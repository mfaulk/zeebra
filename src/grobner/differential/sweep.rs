//! A run of many generated systems through the oracle, and the shrinking of whatever fails.
//!
//! The sweep's coverage is deliberate rather than random: it walks the cross product of variable
//! counts and characteristics in a fixed order, so asking for 24 systems over four variable counts
//! and six primes gives one of each, and asking for 500 gives about 21 of each. A uniformly random
//! choice would leave the small characteristics — where an implementation that assumed `2` is
//! invertible goes wrong — to chance.

use std::time::{Duration, Instant};

use crate::grobner::{f4::F4Options, fglm::FglmOptions};

use super::{
    check::{check_generated, SystemOutcome},
    comparison::{Check, DifferentialCase, Disagreement},
    generator::{GeneratedSystem, SystemShape},
    singular::Oracle,
};

/// What to sweep.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SweepOptions {
    /// The base seed. System `i` is generated from `seed + i`, so a report naming a seed is enough
    /// to reproduce one system without rerunning the sweep.
    pub seed: u64,

    /// How many systems to check.
    pub systems: usize,

    /// Variable counts to cycle through.
    pub variables: Vec<usize>,

    /// Characteristics to cycle through.
    pub characteristics: Vec<u64>,

    /// The largest total degree of a generated term.
    pub max_degree: u32,

    /// The most terms a generated polynomial may have.
    pub max_terms: usize,

    /// Shrink attempts allowed per failing system. Zero disables minimization.
    pub minimize_attempts: usize,

    /// Wall-clock allowed for shrinking one failing system.
    pub minimize_budget: Duration,

    /// The options every quotient algebra and conversion in the sweep is built with.
    ///
    /// This is how a workstream points the oracle at a strategy under development: the sweep's
    /// 500 random systems over six fields are then checking *that* strategy, not the default one.
    pub fglm: FglmOptions,

    /// The options every Gröbner basis in the sweep is computed with.
    ///
    /// The same facility one level down, and M22 is what it is for: every strategy that milestone
    /// added — pair schedule, Hilbert-driven cap, certification — is asserted to return the
    /// baseline's basis on a fixed corpus, and this is how the *same* claim gets checked against an
    /// external oracle on hundreds of random systems instead.
    pub f4: F4Options,
}

impl SweepOptions {
    /// The shape and field of system `index`.
    ///
    /// Variable count cycles fastest, so a short sweep covers every variable count before
    /// repeating a characteristic.
    fn system(&self, index: usize) -> GeneratedSystem {
        let variables = self.variables[index % self.variables.len()];
        let characteristic =
            self.characteristics[(index / self.variables.len()) % self.characteristics.len()];
        GeneratedSystem::generate(
            self.seed.wrapping_add(index as u64),
            SystemShape {
                variables,
                max_degree: self.max_degree,
                max_terms: self.max_terms,
            },
            characteristic,
        )
    }
}

/// A system Zeebra and the oracle disagreed about.
#[derive(Clone, Debug)]
pub struct Failure {
    /// The system as generated. **Always retained**, minimized or not: the seed and the original
    /// input are the only things that reproduce the run that found this.
    pub original: GeneratedSystem,

    /// The smallest system found that still fails the same check. Equal to `original` when
    /// minimization was disabled or found nothing smaller.
    pub minimized: GeneratedSystem,

    /// Shrink steps that were accepted.
    pub shrinks: usize,

    /// Shrink candidates that were tried, accepted or not. Bounded by the sweep's budget.
    pub attempts: usize,

    /// The disagreement, as it stands for `minimized`.
    pub disagreement: Disagreement,

    /// The oracle's answers for `minimized`, for the fixture a failure should become.
    pub case: DifferentialCase,
}

/// What a sweep found.
#[derive(Clone, Debug, Default)]
pub struct SweepReport {
    /// Systems the sweep attempted.
    pub attempted: usize,

    /// Systems where Zeebra and the oracle agreed.
    pub agreed: usize,

    /// Of the agreements, those over a zero-dimensional ideal with a nonzero quotient.
    pub zero_dimensional: usize,

    /// Of the agreements, those over the unit ideal.
    pub unit_ideals: usize,

    /// Of the agreements, those both sides rejected as positive-dimensional.
    pub positive_dimensional: usize,

    /// Disagreements, minimized.
    pub failures: Vec<Failure>,

    /// Systems the oracle could not answer about. **Not agreement.**
    pub oracle_failures: Vec<(String, String)>,

    /// Systems Zeebra could not get far enough on to be compared.
    pub zeebra_failures: Vec<(String, String)>,

    /// Systems skipped because their shape is not instantiated.
    pub unsupported: Vec<String>,

    /// The oracle's answers for every agreeing system, for emitting fixtures.
    pub agreed_cases: Vec<DifferentialCase>,
}

impl SweepReport {
    /// Whether every attempted system either agreed or was explicitly skipped.
    ///
    /// An oracle failure makes this false. A sweep that could not consult its oracle has not
    /// validated anything, and reporting it as a pass is the failure mode §4.5 of the milestone
    /// document exists to prevent.
    pub fn clean(&self) -> bool {
        self.failures.is_empty()
            && self.oracle_failures.is_empty()
            && self.zeebra_failures.is_empty()
    }
}

/// Run a sweep, reporting each system to `observe` as it completes.
///
/// `observe` is called once per system with its index, the system, and the outcome, so a caller can
/// stream progress rather than wait for the whole run.
pub fn run_sweep(
    options: &SweepOptions,
    oracle: &mut impl Oracle,
    observe: &mut dyn FnMut(usize, &GeneratedSystem, &SystemOutcome),
) -> SweepReport {
    assert!(
        !options.variables.is_empty() && !options.characteristics.is_empty(),
        "a sweep needs at least one variable count and one characteristic"
    );

    let mut report = SweepReport::default();

    for index in 0..options.systems {
        let system = options.system(index);
        let outcome = check_generated(&system, oracle, &options.fglm, &options.f4);
        observe(index, &system, &outcome);
        report.attempted += 1;

        match outcome {
            SystemOutcome::Agreed { case, agreement } => {
                report.agreed += 1;
                match agreement.quotient_dimension {
                    None => report.positive_dimensional += 1,
                    Some(0) => report.unit_ideals += 1,
                    Some(_) => report.zero_dimensional += 1,
                }
                report.agreed_cases.push(case);
            }
            SystemOutcome::Disagreed { case, disagreement } => {
                report
                    .failures
                    .push(minimize(&system, case, disagreement, options, oracle));
            }
            SystemOutcome::OracleFailed { error } => {
                report
                    .oracle_failures
                    .push((system.name(), error.to_string()));
            }
            SystemOutcome::ZeebraFailed { detail } => {
                report.zeebra_failures.push((system.name(), detail));
            }
            SystemOutcome::Unsupported { detail } => {
                report
                    .unsupported
                    .push(format!("{}: {}", system.name(), detail));
            }
        }
    }

    report
}

/// Shrink a failing system while it keeps failing the same check.
///
/// Four reductions, in order of how much they remove: drop a generator, drop a term, flatten a
/// coefficient to one, lower an exponent. The first candidate that still fails is accepted and the
/// search restarts from the smaller system, which is a greedy descent and not a minimum.
///
/// **Bounded on purpose.** Each candidate costs an oracle invocation, so an unbounded search on a
/// large failing system can take longer than the sweep that found it. The original is always kept.
fn minimize(
    original: &GeneratedSystem,
    case: DifferentialCase,
    disagreement: Disagreement,
    options: &SweepOptions,
    oracle: &mut impl Oracle,
) -> Failure {
    let mut best = original.clone();
    let mut best_case = case;
    let mut best_disagreement = disagreement;
    let mut shrinks = 0usize;
    let mut attempts = 0usize;
    let deadline = Instant::now() + options.minimize_budget;

    'descent: while attempts < options.minimize_attempts && Instant::now() < deadline {
        for candidate in shrinks_of(&best) {
            if attempts >= options.minimize_attempts || Instant::now() >= deadline {
                break 'descent;
            }
            attempts += 1;

            // Only a disagreement on the *same* check counts. A candidate that fails a different
            // check is a different bug, and following it would walk the search away from the one
            // the sweep found.
            if let SystemOutcome::Disagreed {
                case,
                disagreement: found,
            } = check_generated(&candidate, oracle, &options.fglm, &options.f4)
            {
                if found.check == best_disagreement.check {
                    best = candidate;
                    best_case = case;
                    best_disagreement = found;
                    shrinks += 1;
                    continue 'descent;
                }
            }
        }
        break;
    }

    Failure {
        original: original.clone(),
        minimized: best,
        shrinks,
        attempts,
        disagreement: best_disagreement,
        case: best_case,
    }
}

/// Smaller systems to try, largest reduction first.
///
/// The seed and the characteristic are carried through unchanged: a shrunk system is no longer what
/// the seed generates, and saying so is the point of [`Failure::original`].
fn shrinks_of(system: &GeneratedSystem) -> Vec<GeneratedSystem> {
    let mut candidates: Vec<GeneratedSystem> = Vec::new();

    // Drop a generator. A one-generator system is left alone: dropping its only generator gives
    // the zero ideal, which is a different question rather than a smaller version of this one.
    if system.polynomials.len() > 1 {
        for i in 0..system.polynomials.len() {
            let mut candidate = system.clone();
            candidate.polynomials.remove(i);
            candidates.push(candidate);
        }
    }

    // Drop a term.
    for (i, polynomial) in system.polynomials.iter().enumerate() {
        for j in 0..polynomial.len() {
            let mut candidate = system.clone();
            candidate.polynomials[i].remove(j);
            candidates.push(candidate);
        }
    }

    // Flatten a coefficient to one.
    for (i, polynomial) in system.polynomials.iter().enumerate() {
        for (j, term) in polynomial.iter().enumerate() {
            if term.coefficient == 1 {
                continue;
            }
            let mut candidate = system.clone();
            candidate.polynomials[i][j].coefficient = 1;
            candidates.push(candidate);
        }
    }

    // Lower an exponent.
    for (i, polynomial) in system.polynomials.iter().enumerate() {
        for (j, term) in polynomial.iter().enumerate() {
            for (k, exponent) in term.exponents.iter().enumerate() {
                if *exponent == 0 {
                    continue;
                }
                let mut candidate = system.clone();
                candidate.polynomials[i][j].exponents[k] -= 1;
                candidates.push(candidate);
            }
        }
    }

    candidates
}

/// Whether a check is one the harness can reach at all, for a report's own sanity.
///
/// [`Check::Parse`] and [`Check::Field`] are defects in a case rather than findings about Zeebra,
/// so a sweep reporting one of them means the harness is miswired.
pub fn is_finding(check: Check) -> bool {
    !matches!(check, Check::Parse | Check::Field)
}

#[cfg(test)]
mod tests {
    use super::{shrinks_of, SweepOptions};
    use crate::grobner::f4::F4Options;
    use crate::grobner::{
        differential::generator::{GeneratedSystem, SystemShape},
        fglm::FglmOptions,
    };
    use std::time::Duration;

    const SHAPE: SystemShape = SystemShape {
        variables: 3,
        max_degree: 3,
        max_terms: 4,
    };

    fn options() -> SweepOptions {
        SweepOptions {
            seed: 100,
            systems: 24,
            variables: vec![2, 3, 4, 5],
            characteristics: vec![2, 3, 7, 13, 65537, 2147483647],
            max_degree: 3,
            max_terms: 4,
            minimize_attempts: 0,
            minimize_budget: Duration::from_secs(0),
            fglm: FglmOptions::unbounded(),
            f4: F4Options::default(),
        }
    }

    /// The first `v * c` systems cover every variable count and characteristic exactly once.
    #[test]
    fn test_a_sweep_covers_the_cross_product() {
        let options = options();
        let combinations: Vec<(usize, u64)> = (0..24)
            .map(|i| {
                let system = options.system(i);
                (system.variables.len(), system.characteristic)
            })
            .collect();

        let distinct: std::collections::HashSet<(usize, u64)> =
            combinations.iter().copied().collect();
        assert_eq!(
            distinct.len(),
            24,
            "the first 24 systems do not cover the 4 x 6 cross product: {:?}",
            combinations
        );
    }

    /// Variable count cycles fastest, so a four-system sweep still sees every variable count.
    #[test]
    fn test_the_variable_count_cycles_fastest() {
        let options = options();
        let counts: Vec<usize> = (0..4).map(|i| options.system(i).variables.len()).collect();
        assert_eq!(counts, vec![2, 3, 4, 5]);
    }

    /// Each system has its own seed, so two systems of the same shape are not the same system.
    #[test]
    fn test_each_system_has_its_own_seed() {
        let options = options();
        assert_eq!(options.system(0).seed, 100);
        assert_eq!(options.system(7).seed, 107);
    }

    /// Every shrink is strictly smaller than what it came from, so the descent terminates.
    #[test]
    fn test_every_shrink_is_strictly_smaller() {
        let system = GeneratedSystem::generate(5, SHAPE, 13);
        let size = |s: &GeneratedSystem| -> (usize, usize, u64, u32) {
            (
                s.polynomials.len(),
                s.terms(),
                s.polynomials.iter().flatten().map(|t| t.coefficient).sum(),
                s.polynomials
                    .iter()
                    .flatten()
                    .map(|t| t.exponents.iter().sum::<u32>())
                    .sum(),
            )
        };

        let before = size(&system);
        for candidate in shrinks_of(&system) {
            let after = size(&candidate);
            assert!(
                after.0 <= before.0
                    && after.1 <= before.1
                    && after.2 <= before.2
                    && after.3 <= before.3
                    && after != before,
                "a shrink was not smaller: {:?} from {:?}",
                after,
                before
            );
        }
    }

    /// Shrinking offers every kind of reduction the minimizer claims to make.
    #[test]
    fn test_shrinking_offers_every_reduction() {
        let system = GeneratedSystem::generate(5, SHAPE, 65537);
        let candidates = shrinks_of(&system);

        assert!(
            candidates
                .iter()
                .any(|c| c.polynomials.len() < system.polynomials.len()),
            "no candidate dropped a generator"
        );
        assert!(
            candidates
                .iter()
                .any(|c| c.polynomials.len() == system.polynomials.len()
                    && c.terms() < system.terms()),
            "no candidate dropped a term"
        );
        // Total degree over every term, not the maximum: lowering one exponent of a term that was
        // not the highest-degree one leaves the maximum where it was.
        let total = |s: &GeneratedSystem| -> u32 {
            s.polynomials
                .iter()
                .flatten()
                .map(|t| t.exponents.iter().sum::<u32>())
                .sum()
        };
        assert!(
            candidates
                .iter()
                .any(|c| c.terms() == system.terms() && total(c) < total(&system)),
            "no candidate lowered an exponent"
        );
        assert!(
            candidates.iter().any(|c| c.terms() == system.terms()
                && c.polynomials
                    .iter()
                    .flatten()
                    .map(|t| t.coefficient)
                    .sum::<u64>()
                    < system
                        .polynomials
                        .iter()
                        .flatten()
                        .map(|t| t.coefficient)
                        .sum::<u64>()),
            "no candidate flattened a coefficient"
        );
    }

    /// Shrinking a one-generator system does not offer to delete its only generator.
    #[test]
    fn test_shrinking_keeps_at_least_one_generator() {
        let mut system = GeneratedSystem::generate(5, SHAPE, 13);
        system.polynomials.truncate(1);
        for candidate in shrinks_of(&system) {
            assert_eq!(
                candidate.polynomials.len(),
                1,
                "a candidate removed the only generator"
            );
        }
    }

    /// A shrink keeps the seed and the characteristic, since the original is reported beside it.
    #[test]
    fn test_a_shrink_keeps_its_provenance() {
        let system = GeneratedSystem::generate(42, SHAPE, 7);
        for candidate in shrinks_of(&system) {
            assert_eq!(candidate.seed, 42);
            assert_eq!(candidate.characteristic, 7);
            assert_eq!(candidate.variables, system.variables);
        }
    }
}
