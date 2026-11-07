//! A run of many generated systems through the oracle, and the shrinking of whatever fails.
//!
//! The sweep's coverage is deliberate rather than random: it walks the cross product of variable
//! counts and fields in a fixed order, so asking for 24 systems over four variable counts and six
//! fields gives one of each, and asking for 500 gives about 21 of each. A uniformly random choice
//! would leave the small fields — where an implementation that assumed `2` is invertible goes
//! wrong — to chance.

use std::{
    collections::BTreeMap,
    sync::{
        atomic::{AtomicUsize, Ordering},
        mpsc,
    },
    time::{Duration, Instant},
};

use crate::grobner::{f4::F4Options, fglm::FglmOptions};

use super::{
    check::{check_generated, SystemOutcome},
    comparison::{Check, DifferentialCase, Disagreement},
    field::CaseField,
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

    /// Fields to cycle through, each naming its modulus where it has one.
    pub fields: Vec<CaseField>,

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

    /// How many systems to check at once. One by default.
    ///
    /// The systems are independent — `system(index)` is a pure function of `(seed, index)` and no
    /// iteration reads another's result — so this is purely how much of the machine the sweep is
    /// allowed to use. It does not change the report: see [`run_sweep`].
    pub jobs: usize,

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
    /// repeating a field.
    fn system(&self, index: usize) -> GeneratedSystem {
        let variables = self.variables[index % self.variables.len()];
        let field = self.fields[(index / self.variables.len()) % self.fields.len()];
        GeneratedSystem::generate(
            self.seed.wrapping_add(index as u64),
            SystemShape {
                variables,
                max_degree: self.max_degree,
                max_terms: self.max_terms,
            },
            field,
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

/// Run a sweep, reporting each system to `observe` in index order.
///
/// `oracles` holds exactly one oracle per job. A worker cannot share one: [`Oracle::interrogate`]
/// takes `&mut self`, and [`SingularOracle`](super::singular::SingularOracle) names its scratch
/// files from a per-oracle run counter, so two workers behind one oracle would overwrite each
/// other's script and read each other's output.
/// [`SingularOracle::fleet`](super::singular::SingularOracle::fleet) builds a conforming set.
///
/// **The report is assembled in index order and not in completion order.** A seeded differential
/// sweep whose failure list depended on which worker finished first could not be reproduced, which
/// would defeat the point of seeding it — so each system's contribution is held against its index
/// and absorbed in order. `observe` is called from the calling thread, in index order, for the
/// same reason: a worker that ran ahead has its progress line held until its predecessors' are
/// emitted. At more than one job a failing system's progress line therefore appears only after its
/// shrink has finished, since that is where the worker's result becomes available.
pub fn run_sweep<O: Oracle + Send>(
    options: &SweepOptions,
    oracles: &mut [O],
    observe: &mut dyn FnMut(usize, &GeneratedSystem, &SystemOutcome),
) -> SweepReport {
    assert!(
        !options.variables.is_empty() && !options.fields.is_empty(),
        "a sweep needs at least one variable count and one field"
    );
    assert!(options.jobs >= 1, "a sweep needs at least one job");
    assert_eq!(
        oracles.len(),
        options.jobs,
        "a sweep of {} jobs needs one oracle each",
        options.jobs
    );

    if options.jobs == 1 {
        return run_sequentially(options, &mut oracles[0], observe);
    }
    run_concurrently(options, oracles, observe)
}

/// The one-job sweep, with no channel and no threads.
///
/// Kept as its own path rather than as the degenerate case of the fan-out so that `--jobs 1` is
/// the sequential sweep every recorded report was produced by, down to the order in which a
/// progress line and a shrink happen.
fn run_sequentially<O: Oracle>(
    options: &SweepOptions,
    oracle: &mut O,
    observe: &mut dyn FnMut(usize, &GeneratedSystem, &SystemOutcome),
) -> SweepReport {
    let mut report = SweepReport::default();
    for index in 0..options.systems {
        let system = options.system(index);
        let outcome = check_generated(&system, oracle, &options.fglm, &options.f4);
        observe(index, &system, &outcome);
        report.attempted += 1;
        absorb(&mut report, resolve(&system, outcome, options, oracle));
    }
    report
}

/// The same sweep over `oracles.len()` workers, assembled in index order.
fn run_concurrently<O: Oracle + Send>(
    options: &SweepOptions,
    oracles: &mut [O],
    observe: &mut dyn FnMut(usize, &GeneratedSystem, &SystemOutcome),
) -> SweepReport {
    // Indices are handed out one at a time rather than in blocks. A system's cost spans orders of
    // magnitude with its variable count, and the variable count cycles fastest (see
    // `SweepOptions::system`), so any static split gives one worker every cheap system and
    // another every expensive one.
    let next = AtomicUsize::new(0);
    let (sender, receiver) = mpsc::channel();
    let mut report = SweepReport::default();

    std::thread::scope(|scope| {
        for oracle in oracles.iter_mut() {
            let sender = sender.clone();
            let next = &next;
            scope.spawn(move || loop {
                let index = next.fetch_add(1, Ordering::Relaxed);
                if index >= options.systems {
                    return;
                }
                let system = options.system(index);
                let outcome = check_generated(&system, oracle, &options.fglm, &options.f4);
                // The worker finishes everything that needs its oracle — including the shrink of a
                // failure, which is a loop of oracle calls — before giving up the index.
                let observed = outcome.clone();
                let contribution = resolve(&system, outcome, options, oracle);
                if sender
                    .send((index, system, observed, contribution))
                    .is_err()
                {
                    return;
                }
            });
        }
        // The calling thread's own clone, dropped so the receive loop ends when the workers do.
        drop(sender);

        let mut held: BTreeMap<usize, (GeneratedSystem, SystemOutcome, Contribution)> =
            BTreeMap::new();
        let mut emitted = 0usize;
        for (index, system, outcome, contribution) in receiver {
            held.insert(index, (system, outcome, contribution));
            while let Some((system, outcome, contribution)) = held.remove(&emitted) {
                observe(emitted, &system, &outcome);
                report.attempted += 1;
                absorb(&mut report, contribution);
                emitted += 1;
            }
        }
    });

    report
}

/// What one system owes the report, once its worker is done with its oracle.
///
/// Exists so that the oracle work and the report assembly can happen in different orders: a worker
/// produces this as soon as it can, and [`absorb`] folds it in when the system's index comes up.
enum Contribution {
    Agreed {
        case: DifferentialCase,
        quotient_dimension: Option<usize>,
    },
    Failed(Box<Failure>),
    OracleFailed {
        name: String,
        error: String,
    },
    ZeebraFailed {
        name: String,
        detail: String,
    },
    Unsupported {
        line: String,
    },
}

/// Finish one system's oracle work, shrinking it if it disagreed.
fn resolve<O: Oracle>(
    system: &GeneratedSystem,
    outcome: SystemOutcome,
    options: &SweepOptions,
    oracle: &mut O,
) -> Contribution {
    match outcome {
        SystemOutcome::Agreed { case, agreement } => Contribution::Agreed {
            case,
            quotient_dimension: agreement.quotient_dimension,
        },
        SystemOutcome::Disagreed { case, disagreement } => Contribution::Failed(Box::new(
            minimize(system, case, disagreement, options, oracle),
        )),
        SystemOutcome::OracleFailed { error } => Contribution::OracleFailed {
            name: system.name(),
            error: error.to_string(),
        },
        SystemOutcome::ZeebraFailed { detail } => Contribution::ZeebraFailed {
            name: system.name(),
            detail,
        },
        SystemOutcome::Unsupported { detail } => Contribution::Unsupported {
            line: format!("{}: {}", system.name(), detail),
        },
    }
}

/// Fold one system's contribution into the report. Called in index order, always.
fn absorb(report: &mut SweepReport, contribution: Contribution) {
    match contribution {
        Contribution::Agreed {
            case,
            quotient_dimension,
        } => {
            report.agreed += 1;
            match quotient_dimension {
                None => report.positive_dimensional += 1,
                Some(0) => report.unit_ideals += 1,
                Some(_) => report.zero_dimensional += 1,
            }
            report.agreed_cases.push(case);
        }
        Contribution::Failed(failure) => report.failures.push(*failure),
        Contribution::OracleFailed { name, error } => report.oracle_failures.push((name, error)),
        Contribution::ZeebraFailed { name, detail } => report.zeebra_failures.push((name, detail)),
        Contribution::Unsupported { line } => report.unsupported.push(line),
    }
}

/// Shrink a failing system while it keeps failing the same check.
///
/// Four reductions, in order of how much they remove: drop a generator, drop a term, flatten a
/// coefficient to one, lower an exponent. The first candidate that still fails is accepted and the
/// search restarts from the smaller system, which is a greedy descent and not a minimum.
///
/// **Bounded on purpose.** Each candidate costs an oracle invocation, so an unbounded search on a
/// large failing system can take longer than the sweep that found it. The original is always kept.
fn minimize<O: Oracle>(
    original: &GeneratedSystem,
    case: DifferentialCase,
    disagreement: Disagreement,
    options: &SweepOptions,
    oracle: &mut O,
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
/// The seed and the field are carried through unchanged: a shrunk system is no longer what the
/// seed generates, and saying so is the point of [`Failure::original`].
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
    use super::{run_sweep, shrinks_of, CaseField, SweepOptions, SweepReport};
    use crate::grobner::f4::F4Options;
    use crate::grobner::{
        differential::{
            comparison::DifferentialCase,
            generator::{GeneratedSystem, SystemShape},
            singular::{Oracle, OracleError, OracleQuery},
        },
        fglm::FglmOptions,
    };
    use std::{
        sync::{
            atomic::{AtomicUsize, Ordering},
            Arc,
        },
        time::Duration,
    };

    const SHAPE: SystemShape = SystemShape {
        variables: 3,
        max_degree: 3,
        max_terms: 4,
    };

    /// The six primes and one binary extension these tests cycle through.
    const FIELDS: [CaseField; 7] = [
        CaseField::prime(2),
        CaseField::prime(3),
        CaseField::prime(7),
        CaseField::prime(13),
        CaseField::prime(65537),
        CaseField::prime(2147483647),
        CaseField::binary(0x11B),
    ];

    fn options() -> SweepOptions {
        SweepOptions {
            seed: 100,
            systems: 24,
            variables: vec![2, 3, 4, 5],
            fields: FIELDS.to_vec(),
            max_degree: 3,
            max_terms: 4,
            minimize_attempts: 0,
            minimize_budget: Duration::from_secs(0),
            jobs: 1,
            fglm: FglmOptions::unbounded(),
            f4: F4Options::default(),
        }
    }

    /// The first `v * f` systems cover every variable count and field exactly once.
    #[test]
    fn test_a_sweep_covers_the_cross_product() {
        let options = options();
        let combinations: Vec<(usize, CaseField)> = (0..28)
            .map(|i| {
                let system = options.system(i);
                (system.variables.len(), system.field)
            })
            .collect();

        let distinct: std::collections::HashSet<(usize, CaseField)> =
            combinations.iter().copied().collect();
        assert_eq!(
            distinct.len(),
            28,
            "the first 28 systems do not cover the 4 x 7 cross product: {:?}",
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
        let system = GeneratedSystem::generate(5, SHAPE, CaseField::prime(13));
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
        let system = GeneratedSystem::generate(5, SHAPE, CaseField::prime(65537));
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
        let mut system = GeneratedSystem::generate(5, SHAPE, CaseField::prime(13));
        system.polynomials.truncate(1);
        for candidate in shrinks_of(&system) {
            assert_eq!(
                candidate.polynomials.len(),
                1,
                "a candidate removed the only generator"
            );
        }
    }

    /// A shrink keeps the seed and the field, since the original is reported beside it.
    #[test]
    fn test_a_shrink_keeps_its_provenance() {
        let system = GeneratedSystem::generate(42, SHAPE, CaseField::prime(7));
        for candidate in shrinks_of(&system) {
            assert_eq!(candidate.seed, 42);
            assert_eq!(candidate.field, CaseField::prime(7));
            assert_eq!(candidate.variables, system.variables);
        }
    }

    /// An oracle whose answer is a pure function of its query, with no subprocess.
    ///
    /// Not right about anything: it claims a one-dimensional quotient with a basis of `1` for
    /// every ideal and refuses GF(3) outright, so most of what it produces is a disagreement. That
    /// is deliberate — the failure list is the part of a report whose order a fan-out could
    /// disturb, and a sweep where everything agreed would not exercise it. Being a pure function
    /// of the query is what makes the report independent of which worker asked.
    struct SyntheticOracle {
        /// How long each answer takes. Non-zero widens the window in which workers overlap.
        dwell: Duration,

        /// Answers in flight, and the most there have ever been, shared across the fleet.
        concurrency: Arc<(AtomicUsize, AtomicUsize)>,
    }

    impl Oracle for SyntheticOracle {
        fn interrogate(
            &mut self,
            query: &OracleQuery<'_>,
        ) -> Result<DifferentialCase, OracleError> {
            let (live, peak) = &*self.concurrency;
            let now = live.fetch_add(1, Ordering::SeqCst) + 1;
            peak.fetch_max(now, Ordering::SeqCst);
            std::thread::sleep(self.dwell);
            live.fetch_sub(1, Ordering::SeqCst);

            if query.field == CaseField::prime(3) {
                return Err(OracleError::Incomplete);
            }
            Ok(DifferentialCase {
                name: query.name.clone(),
                field: query.field,
                variables: query.variables.iter().map(|v| v.to_string()).collect(),
                system: query.system.to_vec(),
                // Echoed exactly, so the oracle-input check passes and the comparison gets as far
                // as the mathematics before it disagrees.
                oracle_system: Some(query.system.to_vec()),
                quotient_dimension: Some(1),
                grevlex_basis: vec!["1".to_string()],
                standard_monomials: vec!["1".to_string()],
                border_normal_forms: query
                    .border_monomials
                    .iter()
                    .map(|monomial| (monomial.clone(), "0".to_string()))
                    .collect(),
                lex_basis: Some(vec!["1".to_string()]),
            })
        }
    }

    /// The sweep the concurrency tests run, at `jobs` workers.
    ///
    /// Five variable counts of which one is unsupported, a field the oracle refuses, and a
    /// quotient-dimension cap low enough that some systems trip it: every list in the report is
    /// populated, which `test_the_synthetic_sweep_populates_every_list` asserts.
    ///
    /// `minimize_budget` is ten minutes on purpose. It is a *wall-clock* bound, so a shrink cut
    /// short by it would make the report depend on how fast the machine was and on how contended
    /// it was; the attempt count has to be what binds for a sweep to be reproducible at all.
    fn concurrent_options(jobs: usize) -> SweepOptions {
        SweepOptions {
            seed: 4_400,
            systems: 40,
            variables: vec![2, 3, 4, 5, 6],
            fields: FIELDS.to_vec(),
            max_degree: 3,
            max_terms: 4,
            minimize_attempts: 3,
            minimize_budget: Duration::from_secs(600),
            jobs,
            fglm: FglmOptions {
                max_quotient_dimension: 2,
                ..FglmOptions::unbounded()
            },
            f4: F4Options::default(),
        }
    }

    /// Run that sweep, returning the report, what `observe` saw, and the peak overlap.
    ///
    /// The observations are `(index, seed)` and not just the index: an index argument that merely
    /// counts the calls would look ordered while naming the wrong system, which is the mistake the
    /// pairing catches.
    fn synthetic_sweep(jobs: usize, dwell: Duration) -> (SweepReport, Vec<(usize, u64)>, usize) {
        let concurrency = Arc::new((AtomicUsize::new(0), AtomicUsize::new(0)));
        let mut oracles: Vec<SyntheticOracle> = (0..jobs)
            .map(|_| SyntheticOracle {
                dwell,
                concurrency: Arc::clone(&concurrency),
            })
            .collect();
        let mut observed: Vec<(usize, u64)> = Vec::new();
        let report = run_sweep(
            &concurrent_options(jobs),
            &mut oracles,
            &mut |index, system, _| observed.push((index, system.seed)),
        );
        let peak = concurrency.1.load(Ordering::SeqCst);
        (report, observed, peak)
    }

    /// The seed in a `seed-<n>-p<p>-n<v>` name, which ascends with the sweep index.
    fn seed_of(name: &str) -> u64 {
        let rest = name.strip_prefix("seed-").expect("a generated name");
        rest.split_once("-p")
            .expect("a generated name")
            .0
            .parse()
            .expect("a numeric seed")
    }

    /// Whatever each list holds, it holds in ascending index order.
    fn assert_ascending(seeds: Vec<u64>, what: &str) {
        assert!(
            seeds.windows(2).all(|pair| pair[0] < pair[1]),
            "{} is not in index order: {:?}",
            what,
            seeds
        );
    }

    /// The sweep the concurrency tests use populates every list a report assembles in order.
    #[test]
    fn test_the_synthetic_sweep_populates_every_list() {
        let (report, _, _) = synthetic_sweep(1, Duration::ZERO);
        assert_eq!(report.attempted, 40);
        assert!(!report.failures.is_empty(), "no disagreement");
        assert!(!report.oracle_failures.is_empty(), "no oracle failure");
        assert!(!report.zeebra_failures.is_empty(), "no Zeebra failure");
        assert!(!report.unsupported.is_empty(), "nothing skipped");
        assert!(
            report.failures.iter().any(|failure| failure.shrinks > 0),
            "nothing was shrunk, so the minimizer never ran inside a worker"
        );
    }

    /// A sweep's report does not depend on how many workers produced it.
    ///
    /// The criterion the fan-out turns on. Rendered in full, so the failure list, the shrink
    /// counts and every recorded case are compared and not only the tallies.
    #[test]
    fn test_concurrency_does_not_change_the_report() {
        let sequential = format!("{:#?}", synthetic_sweep(1, Duration::ZERO).0);
        for jobs in [2, 4, 8] {
            assert_eq!(
                format!("{:#?}", synthetic_sweep(jobs, Duration::ZERO).0),
                sequential,
                "the report at {} jobs is not the sequential report",
                jobs
            );
        }
    }

    /// Every list in a concurrent report is in index order rather than completion order.
    #[test]
    fn test_a_concurrent_report_is_assembled_in_index_order() {
        let (report, _, peak) = synthetic_sweep(8, Duration::from_millis(3));
        assert!(peak >= 2, "the workers never overlapped");

        assert_ascending(
            report
                .failures
                .iter()
                .map(|failure| failure.original.seed)
                .collect(),
            "the failure list",
        );
        assert_ascending(
            report
                .oracle_failures
                .iter()
                .map(|(name, _)| seed_of(name))
                .collect(),
            "the oracle-failure list",
        );
        assert_ascending(
            report
                .zeebra_failures
                .iter()
                .map(|(name, _)| seed_of(name))
                .collect(),
            "the Zeebra-failure list",
        );
        assert_ascending(
            report
                .unsupported
                .iter()
                .map(|line| seed_of(line.split(':').next().expect("a name")))
                .collect(),
            "the unsupported list",
        );
        assert_ascending(
            report
                .agreed_cases
                .iter()
                .map(|case| seed_of(&case.name))
                .collect(),
            "the agreed cases",
        );
    }

    /// The progress callback sees each index once, in order, beside its own system.
    #[test]
    fn test_progress_is_observed_in_index_order() {
        let options = concurrent_options(8);
        let (report, observed, peak) = synthetic_sweep(options.jobs, Duration::from_millis(3));
        assert!(
            peak >= 2,
            "the workers never overlapped, so the ordering proves nothing"
        );
        let expected: Vec<(usize, u64)> = (0..report.attempted)
            .map(|index| (index, options.seed + index as u64))
            .collect();
        assert_eq!(
            observed, expected,
            "the progress callback was not called once per index, in index order, with that \
             index's system"
        );
    }

    /// A sweep given fewer oracles than jobs is a programming error and not a quieter sweep.
    #[test]
    #[should_panic(expected = "one oracle each")]
    fn test_a_sweep_needs_one_oracle_per_job() {
        let concurrency = Arc::new((AtomicUsize::new(0), AtomicUsize::new(0)));
        let mut oracles = vec![SyntheticOracle {
            dwell: Duration::ZERO,
            concurrency,
        }];
        let mut options = concurrent_options(4);
        options.systems = 1;
        run_sweep(&options, &mut oracles, &mut |_, _, _| {});
    }
}
