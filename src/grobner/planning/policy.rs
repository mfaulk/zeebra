//! Choosing a route, on stated grounds, with one bounded fallback.
//!
//! Opt-in. [`SolvePolicy::Explicit`] is what `solve_one_with_options` already does, and the
//! explicit entry points are untouched; nothing here changes their behaviour.
//!
//! # The policy, and the measurement behind it
//!
//! The conservative opening is **grevlex-then-FGLM**, which contradicts
//! [`SolveStrategy::DirectLexF4`] being the `#[default]` described as "the conservative choice".
//! The argument is not that conversion usually wins — it does not, losing on the whole planted
//! family — but that **its refusals are cheap by construction**:
//!
//! | | binding budget | checked | cost of a refusal |
//! |---|---|---|---|
//! | direct lex F4 | live matrix entries | after every row operation | the whole elimination so far, plus a grevlex basis to say what it means |
//! | grevlex + FGLM | the span's `2D² + D(D+1)/2` cells | from `D`, before allocating | one quotient-basis enumeration |
//!
//! Measured on the corpus: katsura-7's direct attempt burns 28.3 s and 1.3 GB before refusing,
//! planted-12's conversion refuses after 36 ms. Direct-first costs 28.3 s on katsura-7;
//! grevlex-first costs 37 ms on planted-12 and 47 ms on katsura-7. The conservative question is
//! not "which route usually wins" but **"which route's failure is affordable"**.
//!
//! Ten systems from two synthetic families are not evidence about cryptographic instances, and
//! M21-I re-measures this before the order is called settled. §4.3 of
//! `docs/MILESTONE-RESOURCE-AWARE-CRYPTANALYSIS.md` says so at length.
//!
//! # What the planner may know, and when
//!
//! Two phases, with the knowledge boundary explicit. Before a Gröbner basis it knows only
//! [`SystemShape`] — counts and structure, **no dimension claim**, because cyclic-4 is four
//! equations in four variables and positive-dimensional. After a basis it can classify the ideal
//! and *count* `D`, and only then is the conversion's feasibility a fact rather than a guess. The
//! planner contains no cost model, no learned predictor, and no benchmark names.

use std::time::{Duration, Instant};

use rand::{CryptoRng, RngCore};

use crate::{
    grobner::{
        f4_reported,
        fglm::{classify_ideal, fglm_to_lex_with_options, FglmMemory, QuotientBasis},
        planning::{
            analyze,
            report::{Attempt, Choice, OutcomeClass, SolvePlan},
        },
        solve_from_lex_basis,
        solve_zero_dimensional::explain_lex_failure,
        SolveError, SolveOptions, SolveOutcome, SolveStrategy,
    },
    KnownOrder, MonomialOrder, MultivariatePolynomial,
};

/// How much freedom the planner has.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum SolvePolicy {
    /// Exactly the named route. The behaviour `solve_one_with_options` already has, and the
    /// default, so that opting into a plan is always deliberate.
    Explicit(SolveStrategy),

    /// One route, chosen on the grounds in the module docs. No second attempt.
    ///
    /// A conversion ruled out by a counted `D` is reported as
    /// [`SolveError::ConversionInfeasible`] rather than silently switching: under this policy
    /// "choose one route and stand by it" is the contract.
    #[default]
    ConservativeAuto,

    /// As [`Self::ConservativeAuto`], plus one alternative attempt from the shared budget.
    AutoWithFallback,
}

/// What the whole plan may spend, across every attempt.
///
/// **Shared, not per attempt.** A per-attempt budget lets a fallback burn 28 s and then succeed in
/// 47 ms and report the 47 ms, which measures the algorithm and not the policy.
///
/// # Only cumulative quantities can be shared
/// Batches and seconds are *spent*: they add across attempts. A peak — live entries, live bytes —
/// is not spent, so "sharing" one would be meaningless, and those stay in
/// [`SolveOptions::f4`] where they bound each attempt individually. Confusing the two is how a
/// shared budget comes to mean nothing.
///
/// # The two budgets are enforced differently, and the difference is not cosmetic
///
/// `max_total_batches` is **enforced inside each attempt**: the remaining allowance becomes that
/// attempt's [`F4Options::max_batches`](crate::grobner::F4Options::max_batches), tightened by
/// whatever per-attempt limit the caller set. So `Some(0)` really does permit no batch, and a
/// fallback starting with one batch left can spend one. F4 already counts batches and refuses at a
/// limit; the budget rides that mechanism rather than inventing a second one.
///
/// `max_elapsed` **gates attempts and does not interrupt one**, because F4 has no cooperative time
/// check to ride. So it bounds whether a *second* route starts, not how long the first runs —
/// which is the protection katsura-7 needs, and is not a wall-clock guarantee.
///
/// The asymmetry is a property of what the solver can be told, not a design preference, and it is
/// stated here rather than left for a caller to discover.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct PlanBudget {
    /// Wall clock across every attempt, checked **between** them. `None` for no limit.
    pub max_elapsed: Option<Duration>,

    /// F4 batches summed over every attempt, discarded work included. `None` for no limit.
    ///
    /// Enforced during each attempt, not merely before the second. See the type's docs.
    pub max_total_batches: Option<usize>,
}

impl PlanBudget {
    /// The batches one attempt may spend, given `spent` already consumed.
    ///
    /// The smaller of what the shared budget has left and what the caller's per-attempt
    /// `F4Options::max_batches` allows — so neither can be escaped by the other, and a plan with
    /// no shared budget behaves exactly as the per-attempt limit alone did.
    ///
    /// Saturating: a `spent` beyond the limit gives zero rather than wrapping, and zero is a
    /// satisfiable instruction to F4 — it refuses before building a matrix.
    pub fn batches_for_attempt(&self, spent: usize, per_attempt: Option<usize>) -> Option<usize> {
        let remaining = self.max_total_batches.map(|l| l.saturating_sub(spent));
        match (remaining, per_attempt) {
            (Some(shared), Some(each)) => Some(shared.min(each)),
            (Some(shared), None) => Some(shared),
            (None, each) => each,
        }
    }
}

/// Policy, shared budget, and the per-attempt budgets each route runs under.
#[derive(Clone, Debug, Default)]
pub struct PlannedSolveOptions {
    /// How much freedom the planner has.
    pub policy: SolvePolicy,

    /// What the whole plan may spend.
    pub budget: PlanBudget,

    /// The per-attempt budgets. [`SolveOptions::strategy`] is **ignored** — the policy decides it,
    /// and leaving the field to be silently overridden would be worse than saying so.
    pub attempt: SolveOptions,
}

impl PlannedSolveOptions {
    /// The named policy, with every budget at its default.
    pub fn with_policy(policy: SolvePolicy) -> Self {
        Self {
            policy,
            ..Self::default()
        }
    }
}

/// One point of `system`, by a route the policy chooses, with the decision log beside it.
///
/// The outcome is in the `Result`, so an exhausted plan has no [`SolveOutcome`] to be mistaken for
/// one: an `Err` here means **inconclusive**, never "no solution". The three `Ok` variants are the
/// three answers, exactly as in [`solve_one_with_outcome`](crate::grobner::solve_one_with_outcome).
///
/// `plan` carries every attempt, failed ones included, with what each spent. Quote
/// [`SolvePlan::total_elapsed`] as the policy's cost, not the winning attempt's.
///
/// ```
/// use rand::{prelude::StdRng, SeedableRng};
/// use zeebra::{
///     fields::Zp2147483647,
///     grobner::{
///         benchmark_systems::katsura, solve_one_planned, PlannedSolveOptions, SolvePolicy,
///     },
/// };
///
/// let options = PlannedSolveOptions::with_policy(SolvePolicy::AutoWithFallback);
/// let (outcome, plan) = solve_one_planned(
///     &katsura::<5, Zp2147483647>(),
///     &mut StdRng::seed_from_u64(1),
///     &options,
/// );
/// assert!(outcome.is_ok());
/// // Every decision is recorded, with its reason.
/// assert!(!plan.attempts.is_empty());
/// println!("{}", plan);
/// ```
#[allow(clippy::type_complexity)]
pub fn solve_one_planned<const N: usize, F: KnownOrder, R: RngCore + CryptoRng>(
    system: &[MultivariatePolynomial<N, F>],
    rng: &mut R,
    options: &PlannedSolveOptions,
) -> (Result<SolveOutcome<N, F>, SolveError>, SolvePlan) {
    let mut plan = SolvePlan {
        shape: analyze(system),
        attempts: Vec::new(),
        declined: None,
        preflight: None,
    };

    // Step 1. The only conclusion the input's shape licenses, and it costs nothing: a nonzero
    // constant generator is a unit, so the ideal is the whole ring. No basis, no attempt — and
    // recorded in `preflight`, because a plan with no attempts still reached a conclusive answer
    // and `SolvePlan::outcome` reads the last attempt.
    if plan.shape.constant_contradiction {
        plan.preflight = Some(OutcomeClass::Inconsistent);
        return (Ok(SolveOutcome::Inconsistent), plan);
    }

    let started = Instant::now();
    let (first, second) = match options.policy {
        SolvePolicy::Explicit(strategy) => (strategy, None),
        // Step 2. Grevlex opens, for the reason in the module docs.
        SolvePolicy::ConservativeAuto => (SolveStrategy::GrevlexF4ThenFglm, None),
        SolvePolicy::AutoWithFallback => (
            SolveStrategy::GrevlexF4ThenFglm,
            Some(SolveStrategy::DirectLexF4),
        ),
    };
    let opening = match options.policy {
        SolvePolicy::Explicit(_) => Choice::Explicit,
        _ => Choice::ConservativeOpening,
    };

    let outcome = run(system, first, opening, rng, options, &mut plan);
    let Err(error) = outcome else {
        return (outcome, plan);
    };

    // A failure that is a property of the ideal — positive-dimensional, unsatisfiable options —
    // would be refused identically by the other route, so trying it is pure waste. A *predicted*
    // infeasibility is handled below instead, because it names which route to switch to.
    let ruled_out = match error {
        SolveError::ConversionInfeasible {
            dimension,
            needed,
            budget,
            ..
        } => Some(Choice::ConversionRuledOut {
            dimension,
            needed,
            budget,
        }),
        _ if error.is_resource_failure() => Some(Choice::FallbackAfterResourceLimit),
        _ => None,
    };

    let (Some(alternative), Some(choice)) = (second, ruled_out) else {
        return (Err(error), plan);
    };

    // Step 6. The shared budget decides whether a second attempt starts at all.
    if let Some(limit) = options.budget.max_elapsed {
        if started.elapsed() >= limit {
            plan.declined = Some((alternative, "the shared time budget was already spent"));
            return (Err(error), plan);
        }
    }
    if let Some(limit) = options.budget.max_total_batches {
        if plan.total_batches() >= limit {
            plan.declined = Some((alternative, "the shared batch budget was already spent"));
            return (Err(error), plan);
        }
    }

    let outcome = run(system, alternative, choice, rng, options, &mut plan);
    (outcome, plan)
}

/// Run one route, recording the attempt whether it succeeds or not.
fn run<const N: usize, F: KnownOrder, R: RngCore + CryptoRng>(
    system: &[MultivariatePolynomial<N, F>],
    strategy: SolveStrategy,
    choice: Choice,
    rng: &mut R,
    options: &PlannedSolveOptions,
    plan: &mut SolvePlan,
) -> Result<SolveOutcome<N, F>, SolveError> {
    // The shared batch allowance, minus what earlier attempts spent. Computed here rather than
    // inside `attempt`, which has no view of the plan.
    let batches = options
        .budget
        .batches_for_attempt(plan.total_batches(), options.attempt.f4.max_batches);

    // Whether a crossed lex budget is worth diagnosing, which it is not once some attempt has
    // already computed — or failed to compute — a grevlex basis of the same system.
    let diagnose = !plan
        .attempts
        .iter()
        .any(|a| a.strategy == SolveStrategy::GrevlexF4ThenFglm);

    let at = Instant::now();
    let (outcome, statistics) = attempt(system, strategy, batches, diagnose, rng, options);
    plan.attempts.push(Attempt {
        strategy,
        choice,
        statistics,
        elapsed: at.elapsed(),
        result: outcome.as_ref().map(class).map_err(|e| *e),
    });
    outcome
}

/// The class of an outcome, for the type-parameter-free plan.
fn class<const N: usize, F: KnownOrder>(outcome: &SolveOutcome<N, F>) -> OutcomeClass {
    match outcome {
        SolveOutcome::Point(_) => OutcomeClass::Point,
        SolveOutcome::NoBaseFieldPoint => OutcomeClass::NoBaseFieldPoint,
        SolveOutcome::Inconsistent => OutcomeClass::Inconsistent,
    }
}

/// One route, composed from the stages rather than reimplemented.
///
/// The grevlex route is driven stage by stage here, which the explicit entry point cannot do: the
/// feasibility decision of step 5 has to happen *between* the source basis and the conversion, and
/// nothing else in the crate needs to interleave them. Every stage is the same public function the
/// explicit route calls, so there is no second implementation to diverge.
fn attempt<const N: usize, F: KnownOrder, R: RngCore + CryptoRng>(
    system: &[MultivariatePolynomial<N, F>],
    strategy: SolveStrategy,
    batches: Option<usize>,
    diagnose: bool,
    rng: &mut R,
    options: &PlannedSolveOptions,
) -> (
    Result<SolveOutcome<N, F>, SolveError>,
    crate::grobner::SolveStatistics,
) {
    let mut per_attempt = SolveOptions {
        strategy,
        ..options.attempt.clone()
    };
    // What the shared budget has left for this attempt, which is how `max_total_batches` is
    // enforced rather than merely checked between attempts.
    per_attempt.f4.max_batches = batches;
    let mut statistics = crate::grobner::SolveStatistics::default();

    let order = match strategy {
        SolveStrategy::DirectLexF4 => MonomialOrder::Lexicographic,
        SolveStrategy::GrevlexF4ThenFglm => MonomialOrder::GradedReverseLexicographic,
    };

    // The source basis. Reported, so a crossed budget still says how far it got.
    let (basis, f4) = f4_reported(system, order, &per_attempt.f4);
    statistics.f4 = Some(f4);
    let basis = match basis {
        Ok(basis) => basis,
        Err(e) => {
            // A crossed lex budget leaves nothing to classify, so #376's misdiagnosis is reachable
            // from here too. `diagnose` is false once a grevlex attempt has run in this plan: its
            // basis either classified or was itself out of budget, so recomputing it would answer
            // a question already answered.
            let diagnose = diagnose && strategy == SolveStrategy::DirectLexF4;
            let (error, diagnosis) = explain_lex_failure(system, e, &per_attempt.f4, diagnose);
            statistics.diagnosis = diagnosis;
            return (Err(error), statistics);
        }
    };

    // Step 3. Classification is a question about leading monomials and costs the same under any
    // order, so it is asked of whichever basis this route computed.
    if !classify_ideal(&basis, order).is_finite_dimensional() {
        return (Err(SolveError::PositiveDimensional), statistics);
    }

    let lex = match strategy {
        SolveStrategy::DirectLexF4 => basis,
        SolveStrategy::GrevlexF4ThenFglm => {
            // Steps 4 and 5. `D` is *counted* here, not estimated, and the conversion's dense
            // blocks are a function of it alone — so whether the conversion fits is a fact before
            // a single operator column is built. This is the one decision in the policy that rests
            // on a measurement rather than a guess, and it is the decision planted-12 needs.
            let quotient =
                match QuotientBasis::new(&basis, order, per_attempt.fglm.max_quotient_dimension) {
                    Ok(quotient) => quotient,
                    Err(e) => return (Err(SolveError::Fglm(e)), statistics),
                };
            let dimension = quotient.dimension();

            match FglmMemory::dense_blocks_for::<F>(dimension) {
                // Not representable at all: the cell count overflows a `usize`, so no budget could
                // admit it. Reported with the limit it could not meet rather than as an overflow.
                None => {
                    return (
                        Err(SolveError::ConversionInfeasible {
                            dimension,
                            needed: usize::MAX,
                            limit: per_attempt.fglm.max_span_bytes,
                            budget: "span bytes",
                        }),
                        statistics,
                    )
                }
                Some((span_cells, accepted_cells, bytes)) => {
                    let cells = span_cells.saturating_add(accepted_cells);
                    // Checked in the order the budgets are documented in, and reported in the
                    // unit of whichever bound — the two differ by `size_of::<F>()`, so quoting
                    // one budget's limit against the other's requirement would be wrong by a
                    // factor of 4 over BN254.
                    if cells > per_attempt.fglm.max_span_entries {
                        return (
                            Err(SolveError::ConversionInfeasible {
                                dimension,
                                needed: cells,
                                limit: per_attempt.fglm.max_span_entries,
                                budget: "span cells",
                            }),
                            statistics,
                        );
                    }
                    if bytes > per_attempt.fglm.max_span_bytes {
                        return (
                            Err(SolveError::ConversionInfeasible {
                                dimension,
                                needed: bytes,
                                limit: per_attempt.fglm.max_span_bytes,
                                budget: "span bytes",
                            }),
                            statistics,
                        );
                    }
                }
            }

            match fglm_to_lex_with_options(&basis, order, &per_attempt.fglm) {
                Ok((lex, fglm)) => {
                    statistics.fglm = Some(fglm);
                    lex
                }
                Err(e) => return (Err(SolveError::Fglm(e)), statistics),
            }
        }
    };

    // The search, which is the same function the explicit route runs.
    match solve_from_lex_basis(&lex, system, &per_attempt, rng) {
        Ok((outcome, search)) => {
            statistics.lex_basis_elements = search.lex_basis_elements;
            statistics.branches = search.branches;
            statistics.solutions = search.solutions;
            statistics.inconsistent = search.inconsistent;
            (Ok(outcome), statistics)
        }
        Err(e) => (Err(e), statistics),
    }
}

#[cfg(test)]
mod tests {
    use std::time::Duration;

    use rand::{prelude::StdRng, SeedableRng};

    use super::{solve_one_planned, PlanBudget, PlannedSolveOptions, SolvePolicy};
    use crate::{
        fields::Zp2147483647,
        grobner::{
            benchmark_systems::{cyclic, katsura, planted},
            planning::report::{Choice, OutcomeClass},
            F4Options, FglmOptions, SolveError, SolveOptions, SolveOutcome, SolveStrategy,
        },
        FiniteField, MultivariatePolynomial, Zero,
    };

    type F = Zp2147483647;

    fn parse<const N: usize>(
        strings: &[&str],
        vars: [&str; N],
    ) -> Vec<MultivariatePolynomial<N, F>> {
        strings
            .iter()
            .map(|s| MultivariatePolynomial::parse(s, vars).expect("parses"))
            .collect()
    }

    fn point(n: usize) -> Vec<F> {
        (0..n).map(|i| F::new(2 * i as u64 + 3)).collect()
    }

    /// One policy and one budget solve both ends of the corpus. M21-D's acceptance criterion.
    ///
    /// katsura-7 is solvable only by conversion — its lex basis crosses F4's entry budget after
    /// 28 seconds — and planted-12 only directly, its quotient dimension of 4096 being past what
    /// the span budget admits. Neither is named anywhere in the planner.
    #[test]
    fn test_one_policy_solves_both_ends_of_the_corpus() {
        let options = PlannedSolveOptions::with_policy(SolvePolicy::AutoWithFallback);

        // katsura-7: the opening route works, so there is no second attempt.
        let (outcome, plan) =
            solve_one_planned(&katsura::<7, F>(), &mut StdRng::seed_from_u64(1), &options);
        assert!(matches!(outcome, Ok(SolveOutcome::Point(_))));
        assert_eq!(plan.attempts.len(), 1, "no fallback should be needed");
        assert_eq!(plan.attempts[0].strategy, SolveStrategy::GrevlexF4ThenFglm);
        assert_eq!(plan.attempts[0].choice, Choice::ConservativeOpening);
        assert_eq!(plan.outcome(), Some(OutcomeClass::Point));
        assert_eq!(plan.discarded_elapsed(), Duration::ZERO);

        // planted-12: the conversion is ruled out from a counted D, and direct lex finishes.
        let system = planted::<12, F>(&point(12));
        let (outcome, plan) = solve_one_planned(&system, &mut StdRng::seed_from_u64(2), &options);
        let found = match outcome {
            Ok(SolveOutcome::Point(p)) => p,
            other => panic!("expected a point, got {:?}", other),
        };
        for p in &system {
            assert!(p.eval(&found).is_zero(), "{} is not satisfied", p);
        }
        assert_eq!(plan.attempts.len(), 2);
        assert!(matches!(
            plan.attempts[1].choice,
            Choice::ConversionRuledOut {
                dimension: 4096,
                ..
            }
        ));
        assert_eq!(plan.attempts[1].strategy, SolveStrategy::DirectLexF4);
        // The discarded first attempt is charged, not hidden.
        assert!(plan.attempts[0].statistics.f4.is_some());
        assert!(plan.total_elapsed() > plan.attempts[1].elapsed);
    }

    /// A conversion ruled out from a counted `D` is not a conversion that ran and failed.
    ///
    /// The distinction matters because the two cost different amounts: nothing was spent on the
    /// conversion here, and reporting `SpanStorageExceeded` would claim otherwise.
    #[test]
    fn test_a_ruled_out_conversion_is_not_a_crossed_budget() {
        let system = planted::<12, F>(&point(12));
        let (outcome, plan) = solve_one_planned(
            &system,
            &mut StdRng::seed_from_u64(3),
            &PlannedSolveOptions::with_policy(SolvePolicy::ConservativeAuto),
        );

        // Conservative policy stands by its one route, so this is where it stops.
        match outcome {
            Err(SolveError::ConversionInfeasible {
                dimension,
                needed,
                limit,
                budget,
            }) => {
                assert_eq!(dimension, 4096);
                assert!(needed > limit);
                // At D = 4096 the dense blocks are 33,558,528 cells, so over GF(2^31 - 1) the
                // *cell* budget binds first and the error must say so rather than quoting the
                // byte limit against a cell requirement.
                assert_eq!(budget, "span cells");
                // `D^2 + D (D + 1)`: the span's two triangular blocks — its rows' coordinates are
                // stored from their pivots on — and the accepted quotient vectors.
                assert_eq!(needed, 4096 * 4096 + 4096 * 4097);
                assert_eq!(needed, 33_558_528);
            }
            other => panic!("expected an infeasible conversion, got {:?}", other),
        }
        assert_eq!(plan.attempts.len(), 1);
        assert!(plan.is_inconclusive());
        // The source basis was computed and is reported; the conversion never ran.
        assert!(plan.attempts[0].statistics.f4.is_some());
        assert_eq!(plan.attempts[0].statistics.fglm, None);
    }

    /// A positive-dimensional ideal is never sent through FGLM, and never falls back.
    ///
    /// Both routes would refuse it identically, so a second attempt is pure waste.
    #[test]
    fn test_a_positive_dimensional_ideal_is_refused_without_a_fallback() {
        for policy in [SolvePolicy::ConservativeAuto, SolvePolicy::AutoWithFallback] {
            let (outcome, plan) = solve_one_planned(
                &cyclic::<4, F>(),
                &mut StdRng::seed_from_u64(4),
                &PlannedSolveOptions::with_policy(policy),
            );
            assert_eq!(
                outcome,
                Err(SolveError::PositiveDimensional),
                "{:?}",
                policy
            );
            assert_eq!(plan.attempts.len(), 1, "{:?}: no fallback", policy);
            assert_eq!(plan.declined, None);
            // And the basis behind the refusal is still reported, so it does not look free.
            let f4 = plan.attempts[0]
                .statistics
                .f4
                .as_ref()
                .expect("a basis was computed");
            assert!(f4.batches > 0);
        }
    }

    /// An explicit direct-lex plan diagnoses a crossed budget, and charges the plan for doing so.
    ///
    /// The planner composes the stages itself, so #376's misdiagnosis was reachable through
    /// `Explicit(DirectLexF4)` as well as through `solve_one_with_options`.
    #[test]
    fn test_an_explicit_direct_lex_plan_diagnoses_a_positive_dimensional_ideal() {
        let mut system = katsura::<6, F>();
        system.pop();
        let options = PlannedSolveOptions {
            attempt: SolveOptions {
                f4: F4Options {
                    max_matrix_rows: 1000,
                    max_matrix_columns: 1000,
                    ..Default::default()
                },
                ..Default::default()
            },
            ..PlannedSolveOptions::with_policy(SolvePolicy::Explicit(SolveStrategy::DirectLexF4))
        };

        let (outcome, plan) = solve_one_planned(&system, &mut StdRng::seed_from_u64(44), &options);
        assert_eq!(outcome, Err(SolveError::PositiveDimensional));

        let statistics = &plan.attempts[0].statistics;
        let diagnosis = statistics
            .diagnosis
            .as_ref()
            .expect("the crossed lex budget was diagnosed");
        assert_eq!(
            plan.total_batches(),
            statistics.f4.as_ref().expect("a lex attempt").batches + diagnosis.batches,
            "the diagnosis is work the shared budget must see"
        );
    }

    /// A plan that already ran grevlex does not recompute it to diagnose the fallback.
    ///
    /// Its outcome is known: either the basis classified, or it was itself out of budget. cyclic-7
    /// is out of budget under both orders here, so the fallback fails with nothing new to learn.
    #[test]
    fn test_a_fallback_after_grevlex_is_not_diagnosed_again() {
        let options = PlannedSolveOptions {
            attempt: SolveOptions {
                f4: F4Options {
                    max_matrix_rows: 1000,
                    max_matrix_columns: 1000,
                    ..Default::default()
                },
                ..Default::default()
            },
            ..PlannedSolveOptions::with_policy(SolvePolicy::AutoWithFallback)
        };

        let (outcome, plan) =
            solve_one_planned(&cyclic::<7, F>(), &mut StdRng::seed_from_u64(45), &options);
        assert!(outcome.unwrap_err().is_resource_failure());
        assert_eq!(plan.attempts.len(), 2);
        assert!(plan
            .attempts
            .iter()
            .all(|a| a.statistics.diagnosis.is_none()));
    }

    /// An inconsistent system is settled by the structural pass, with no attempt at all.
    #[test]
    fn test_a_constant_generator_needs_no_attempt() {
        let (outcome, plan) = solve_one_planned(
            &parse(&["x^2 - y", "1"], ["x", "y"]),
            &mut StdRng::seed_from_u64(5),
            &PlannedSolveOptions::with_policy(SolvePolicy::AutoWithFallback),
        );
        assert_eq!(outcome, Ok(SolveOutcome::Inconsistent));
        assert!(plan.attempts.is_empty());
        assert_eq!(plan.total_elapsed(), Duration::ZERO);
        // A conclusive answer with no attempt is still reported as one: `outcome()` reads the last
        // attempt, so without `preflight` it would say `None` about a decided question.
        assert_eq!(plan.preflight, Some(OutcomeClass::Inconsistent));
        assert_eq!(plan.outcome(), Some(OutcomeClass::Inconsistent));
        assert!(
            !plan.is_inconclusive(),
            "the structural pass settled it, which is not inconclusive"
        );
        assert!(plan.to_string().contains("the structure settled it"));

        // An inconsistency that is *not* visible in the generators still reaches the same answer,
        // by computing a basis — which is the case the structural pass cannot shortcut.
        let (outcome, plan) = solve_one_planned(
            &parse(&["x - 1", "x - 2"], ["x", "y"]),
            &mut StdRng::seed_from_u64(5),
            &PlannedSolveOptions::with_policy(SolvePolicy::AutoWithFallback),
        );
        assert_eq!(outcome, Ok(SolveOutcome::Inconsistent));
        assert_eq!(plan.attempts.len(), 1);
        // Reached by computing a basis, so there is no preflight conclusion to report.
        assert_eq!(plan.preflight, None);
        assert_eq!(plan.outcome(), Some(OutcomeClass::Inconsistent));
    }

    /// A zero-dimensional ideal with no base-field point is an answer, not a fallback trigger.
    #[test]
    fn test_no_base_field_point_is_an_answer() {
        // 2^31 - 1 is 3 mod 4, so -1 is not a square.
        let (outcome, plan) = solve_one_planned(
            &parse(&["x^2 + 1", "y"], ["x", "y"]),
            &mut StdRng::seed_from_u64(6),
            &PlannedSolveOptions::with_policy(SolvePolicy::AutoWithFallback),
        );
        assert_eq!(outcome, Ok(SolveOutcome::NoBaseFieldPoint));
        assert_eq!(plan.attempts.len(), 1, "an answer needs no second route");
        assert!(!plan.is_inconclusive());
    }

    /// Every permitted route exhausting its budget is inconclusive, not "no solution".
    #[test]
    fn test_every_route_exhausted_is_inconclusive() {
        let system = planted::<6, F>(&point(6));
        let (outcome, plan) = solve_one_planned(
            &system,
            &mut StdRng::seed_from_u64(7),
            &PlannedSolveOptions {
                policy: SolvePolicy::AutoWithFallback,
                budget: PlanBudget::default(),
                attempt: SolveOptions {
                    f4: F4Options {
                        max_matrix_rows: 1,
                        ..F4Options::default()
                    },
                    ..SolveOptions::default()
                },
            },
        );
        assert!(outcome.is_err());
        assert!(plan.is_inconclusive());
        assert_eq!(plan.attempts.len(), 2, "both routes were tried");
        assert_eq!(plan.attempts[1].choice, Choice::FallbackAfterResourceLimit);
        // Not an answer: nothing here says the system has no point, and it does have one.
        assert!(outcome.is_err());
    }

    /// A shared budget cannot be reset by a fallback: a spent plan declines the second route.
    ///
    /// `max_batches` rather than `max_matrix_rows` for the per-attempt limit, because the row
    /// budget is crossed during symbolic preprocessing — *before* the first batch is recorded — so
    /// an attempt refused that way has spent zero batches and the shared budget is untouched. That
    /// is correct, and it is also why this test has to pick a limit the first attempt can actually
    /// spend against.
    #[test]
    fn test_a_fallback_cannot_reset_the_shared_budget() {
        let system = katsura::<6, F>();
        let (outcome, plan) = solve_one_planned(
            &system,
            &mut StdRng::seed_from_u64(8),
            &PlannedSolveOptions {
                policy: SolvePolicy::AutoWithFallback,
                // One batch is all the plan may spend, and the first attempt spends it.
                budget: PlanBudget {
                    max_total_batches: Some(1),
                    ..PlanBudget::default()
                },
                attempt: SolveOptions {
                    f4: F4Options {
                        max_batches: Some(1),
                        ..F4Options::default()
                    },
                    ..SolveOptions::default()
                },
            },
        );
        assert_eq!(plan.total_batches(), 1, "the first attempt spent its batch");
        assert!(outcome.is_err());
        assert_eq!(plan.attempts.len(), 1, "the fallback must not have started");
        assert_eq!(
            plan.declined,
            Some((
                SolveStrategy::DirectLexF4,
                "the shared batch budget was already spent"
            ))
        );
    }

    /// The shared batch budget bounds what each attempt spends, not just whether one starts.
    ///
    /// The gap a reviewer found: the budget was only consulted *between* attempts, so
    /// `max_total_batches: Some(0)` did not stop the first attempt from running batches, and a
    /// fallback with one batch left could spend many. Both halves are pinned here.
    #[test]
    fn test_the_shared_batch_budget_is_enforced_during_each_attempt() {
        // katsura-6 needs several batches by either route, so a small allowance must bite.
        let system = katsura::<6, F>();

        // Zero batches permitted: the *first* attempt must not run one.
        let (outcome, plan) = solve_one_planned(
            &system,
            &mut StdRng::seed_from_u64(20),
            &PlannedSolveOptions {
                policy: SolvePolicy::AutoWithFallback,
                budget: PlanBudget {
                    max_total_batches: Some(0),
                    ..PlanBudget::default()
                },
                attempt: SolveOptions::default(),
            },
        );
        assert!(outcome.is_err());
        assert_eq!(
            plan.total_batches(),
            0,
            "a zero batch budget must permit no batch at all"
        );

        // A positive allowance is spent across attempts and never exceeded.
        for limit in 1..=4usize {
            let (_, plan) = solve_one_planned(
                &system,
                &mut StdRng::seed_from_u64(21),
                &PlannedSolveOptions {
                    policy: SolvePolicy::AutoWithFallback,
                    budget: PlanBudget {
                        max_total_batches: Some(limit),
                        ..PlanBudget::default()
                    },
                    attempt: SolveOptions::default(),
                },
            );
            assert!(
                plan.total_batches() <= limit,
                "a limit of {} was exceeded: {} batches over {} attempts",
                limit,
                plan.total_batches(),
                plan.attempts.len()
            );
        }
    }

    /// A tighter per-attempt limit still applies, and neither budget escapes the other.
    #[test]
    fn test_the_two_batch_limits_compose() {
        let budget = PlanBudget {
            max_total_batches: Some(10),
            ..PlanBudget::default()
        };
        // The shared allowance shrinks as batches are spent.
        assert_eq!(budget.batches_for_attempt(0, None), Some(10));
        assert_eq!(budget.batches_for_attempt(4, None), Some(6));
        // Saturating rather than wrapping, and zero is a satisfiable instruction.
        assert_eq!(budget.batches_for_attempt(99, None), Some(0));
        // The tighter of the two wins, in both directions.
        assert_eq!(budget.batches_for_attempt(0, Some(3)), Some(3));
        assert_eq!(budget.batches_for_attempt(8, Some(3)), Some(2));
        // With no shared budget, the per-attempt limit is untouched — so a plan without one
        // behaves exactly as the explicit route did.
        let none = PlanBudget::default();
        assert_eq!(none.batches_for_attempt(0, Some(7)), Some(7));
        assert_eq!(none.batches_for_attempt(100, None), None);

        // And end to end: the per-attempt limit binds when it is the smaller.
        let system = katsura::<6, F>();
        let (_, plan) = solve_one_planned(
            &system,
            &mut StdRng::seed_from_u64(22),
            &PlannedSolveOptions {
                policy: SolvePolicy::AutoWithFallback,
                budget: PlanBudget {
                    max_total_batches: Some(100),
                    ..PlanBudget::default()
                },
                attempt: SolveOptions {
                    f4: F4Options {
                        max_batches: Some(1),
                        ..F4Options::default()
                    },
                    ..SolveOptions::default()
                },
            },
        );
        // Two attempts, one batch each: the per-attempt cap, not the shared one.
        assert_eq!(plan.total_batches(), plan.attempts.len());
        assert!(plan.attempts.len() <= 2);
    }

    /// A zero time budget declines the fallback outright, which is what the 28-second case needs.
    #[test]
    fn test_a_spent_time_budget_declines_the_fallback() {
        let system = planted::<6, F>(&point(6));
        let (_, plan) = solve_one_planned(
            &system,
            &mut StdRng::seed_from_u64(9),
            &PlannedSolveOptions {
                policy: SolvePolicy::AutoWithFallback,
                budget: PlanBudget {
                    max_elapsed: Some(Duration::ZERO),
                    ..PlanBudget::default()
                },
                attempt: SolveOptions {
                    f4: F4Options {
                        max_matrix_rows: 1,
                        ..F4Options::default()
                    },
                    ..SolveOptions::default()
                },
            },
        );
        assert_eq!(plan.attempts.len(), 1);
        assert_eq!(
            plan.declined.map(|(_, why)| why),
            Some("the shared time budget was already spent")
        );
    }

    /// `Explicit` is the explicit route and nothing more: one attempt, no fallback, no switching.
    #[test]
    fn test_the_explicit_policy_does_not_plan() {
        let system = planted::<12, F>(&point(12));
        // The route the planner would have ruled out. Asked for explicitly, it is attempted.
        let (outcome, plan) = solve_one_planned(
            &system,
            &mut StdRng::seed_from_u64(10),
            &PlannedSolveOptions::with_policy(SolvePolicy::Explicit(
                SolveStrategy::GrevlexF4ThenFglm,
            )),
        );
        assert!(outcome.is_err());
        assert_eq!(plan.attempts.len(), 1);
        assert_eq!(plan.attempts[0].choice, Choice::Explicit);
        assert_eq!(plan.declined, None);
    }

    /// The default policy is conservative and automatic, not explicit.
    #[test]
    fn test_the_default_policy() {
        assert_eq!(SolvePolicy::default(), SolvePolicy::ConservativeAuto);
        let options = PlannedSolveOptions::default();
        assert_eq!(options.policy, SolvePolicy::ConservativeAuto);
        assert_eq!(options.budget, PlanBudget::default());
        assert_eq!(options.budget.max_elapsed, None);
        assert_eq!(options.budget.max_total_batches, None);
    }

    /// Peaks are maxed across attempts and batches are summed, because only one of them is spent.
    #[test]
    fn test_the_plan_adds_what_is_spent_and_maxes_what_is_not() {
        let system = planted::<12, F>(&point(12));
        let (_, plan) = solve_one_planned(
            &system,
            &mut StdRng::seed_from_u64(11),
            &PlannedSolveOptions::with_policy(SolvePolicy::AutoWithFallback),
        );
        assert_eq!(plan.attempts.len(), 2);

        let batches: Vec<usize> = plan
            .attempts
            .iter()
            .map(|a| a.statistics.f4.as_ref().map_or(0, |f| f.batches))
            .collect();
        assert_eq!(plan.total_batches(), batches.iter().sum::<usize>());

        let peaks: Vec<usize> = plan
            .attempts
            .iter()
            .map(|a| a.statistics.estimated_peak_bytes())
            .collect();
        assert_eq!(
            plan.peak_estimated_bytes(),
            *peaks.iter().max().expect("two attempts")
        );
    }

    /// The decision log names every route, its reason, and what it cost.
    #[test]
    fn test_the_plan_explains_itself() {
        let system = planted::<12, F>(&point(12));
        let (_, plan) = solve_one_planned(
            &system,
            &mut StdRng::seed_from_u64(12),
            &PlannedSolveOptions::with_policy(SolvePolicy::AutoWithFallback),
        );
        let log = plan.to_string();
        assert!(log.contains("Attempt 1: GrevlexF4ThenFglm"), "{}", log);
        assert!(log.contains("Attempt 2: DirectLexF4"), "{}", log);
        assert!(
            log.contains("conversion ruled out from a counted D = 4096"),
            "{}",
            log
        );
        assert!(log.contains("Result: Point"), "{}", log);
        assert!(log.contains("discarded"), "{}", log);
    }

    /// The planner's answer is the explicit route's answer wherever an explicit route works.
    ///
    /// A policy may choose differently; it may not *answer* differently.
    #[test]
    fn test_the_planner_agrees_with_whichever_explicit_route_works() {
        agree(&katsura::<5, F>());
        agree(&katsura::<6, F>());
        agree(&cyclic::<5, F>());
        agree(&planted::<8, F>(&point(8)));
    }

    fn agree<const N: usize>(system: &[MultivariatePolynomial<N, F>]) {
        use crate::grobner::solve_one_with_outcome;

        let (planned, _) = solve_one_planned(
            system,
            &mut StdRng::seed_from_u64(13),
            &PlannedSolveOptions::with_policy(SolvePolicy::AutoWithFallback),
        );
        for strategy in [SolveStrategy::DirectLexF4, SolveStrategy::GrevlexF4ThenFglm] {
            let explicit = solve_one_with_outcome(
                system,
                &mut StdRng::seed_from_u64(13),
                &SolveOptions::with_strategy(strategy),
            );
            if let Ok((outcome, _)) = explicit {
                // The *class* must agree. Which point comes back depends on the lex basis the
                // route produced and on the RNG the search consumed, and both differ by route.
                let planned = planned.as_ref().expect("the planner found an answer too");
                assert_eq!(
                    super::class(planned),
                    super::class(&outcome),
                    "{:?} disagrees with the plan",
                    strategy
                );
            }
        }
    }

    /// A planner that special-cased its benchmarks would pass the tests above and fail this one.
    ///
    /// Renaming nothing and changing nothing but the coefficients, a relabelled planted system
    /// must get the same treatment. The planner sees only polynomials, and this is what says so.
    #[test]
    fn test_the_planner_has_no_knowledge_of_the_corpus() {
        let shifted: Vec<F> = (0..12).map(|i| F::new(1_000_003 + i as u64)).collect();
        let system = planted::<12, F>(&shifted);
        let (outcome, plan) = solve_one_planned(
            &system,
            &mut StdRng::seed_from_u64(14),
            &PlannedSolveOptions::with_policy(SolvePolicy::AutoWithFallback),
        );
        assert!(matches!(outcome, Ok(SolveOutcome::Point(_))));
        assert_eq!(plan.attempts.len(), 2);
        assert!(matches!(
            plan.attempts[1].choice,
            Choice::ConversionRuledOut {
                dimension: 4096,
                ..
            }
        ));
    }

    /// An unsatisfiable `F4Options` is a caller error, so the other route is not tried.
    #[test]
    fn test_an_unsatisfiable_option_does_not_trigger_a_fallback() {
        let (outcome, plan) = solve_one_planned(
            &katsura::<5, F>(),
            &mut StdRng::seed_from_u64(15),
            &PlannedSolveOptions {
                policy: SolvePolicy::AutoWithFallback,
                budget: PlanBudget::default(),
                attempt: SolveOptions {
                    f4: F4Options {
                        max_pairs_per_batch: Some(0),
                        ..F4Options::default()
                    },
                    fglm: FglmOptions::default(),
                    ..SolveOptions::default()
                },
            },
        );
        assert!(outcome.is_err());
        assert_eq!(
            plan.attempts.len(),
            1,
            "the same options would fail the same way on the other route"
        );
    }
}
