//! A cooperative wall deadline and cancellation for one FGLM conversion (#1167).
//!
//! **Cooperative, not preemptive.** The conversion polls its control at safe points and stops at
//! the first one that finds the deadline passed or the cancellation set. Nothing interrupts an
//! operation between safe points, so the overrun past a deadline is bounded by the largest
//! indivisible unit of the stage that was running; [`FglmStage`] names each stage's unit.

use std::{
    fmt::{Display, Formatter},
    sync::{
        atomic::{AtomicBool, Ordering},
        OnceLock,
    },
    time::{Duration, Instant},
};

use super::FglmError;

/// The stage of a conversion a safe point belongs to, and so where a stopped conversion stopped.
///
/// Each variant's documentation names the indivisible unit between its safe points, which is what
/// bounds the overrun of a deadline that passes inside it.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum FglmStage {
    /// Enumerating the standard monomials. Polled every [`SAFE_POINT_STRIDE`] frontier pops, so
    /// the unit is that many divisibility tests against the source's leading monomials, plus the
    /// final sort of the `D` monomials, which is not interrupted.
    QuotientEnumeration,

    /// Classifying every `x_i b_j` as standard or border. Polled once on entry: the unit is the
    /// whole classification, `N * D` monomial multiplies and lookups with no field arithmetic.
    BorderClassification,

    /// Building the multiplication operators. Polled per border normal form (scalar strategies),
    /// per batch (batched strategy, on every worker before it claims a batch), and every
    /// [`SAFE_POINT_STRIDE`] columns while columns are assembled. The unit is one border normal
    /// form or one batch's symbolic closure and reduction, whichever the strategy performs.
    OperatorConstruction,

    /// A scalar Wiedemann attempt. Polled before each attempt, every [`SAFE_POINT_STRIDE`] Krylov
    /// steps, before the Berlekamp–Massey reconstruction, and every [`SAFE_POINT_STRIDE`] powers
    /// during certification. The unit is a Berlekamp–Massey run on `2D` terms (`O(D^2)`) or the
    /// numerator inversion and per-variable reductions (`O(N D^2)` schoolbook), which are not
    /// interrupted.
    Wiedemann,

    /// The classical lex walk. Polled on entry and every [`SAFE_POINT_STRIDE`] candidates; the unit
    /// is that many operator applications and dependence tests (`O(D)` and `O(D^2)` each).
    ClassicalWalk,
}

impl Display for FglmStage {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::QuotientEnumeration => "quotient enumeration",
            Self::BorderClassification => "border classification",
            Self::OperatorConstruction => "operator construction",
            Self::Wiedemann => "a Wiedemann attempt",
            Self::ClassicalWalk => "the classical walk",
        })
    }
}

/// Loop iterations between polls in the stages that poll inside a loop.
///
/// A poll with neither a deadline nor a cancellation is two `None` tests; with a deadline it is one
/// `Instant::now()`. Striding keeps either from being paid per candidate or per frontier pop, where
/// the work between polls can be a handful of nanoseconds.
pub const SAFE_POINT_STRIDE: usize = 64;

/// Why a controlled conversion stopped.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum StopReason {
    Deadline,
    Cancelled,
}

/// A test-only safe-point observer: called with each safe point's stage, it may order a stop.
#[cfg(test)]
pub(crate) type SafePointHook<'a> = &'a (dyn Fn(FglmStage) -> Option<StopReason> + Sync);

/// A wall deadline and a cancellation flag for one conversion.
///
/// Passed to [`fglm_to_lex_with_control`](super::fglm_to_lex_with_control). One control governs
/// every stage of the conversion it is passed to: a Wiedemann attempt that declines or fails does
/// **not** give the classical fallback a fresh allowance, because the fallback polls the same
/// deadline.
///
/// The first stop observed is latched, so every later safe point — on any worker — reports the same
/// reason and stage, and the error names the stage where the conversion first stopped.
///
/// [`FglmControl::unlimited`] stops nothing and produces outputs and statistics identical to
/// [`fglm_to_lex_with_options`](super::fglm_to_lex_with_options).
#[derive(Debug)]
pub struct FglmControl<'a> {
    deadline: Option<Instant>,
    cancel: Option<&'a AtomicBool>,
    stopped: OnceLock<(StopReason, FglmStage)>,
    #[cfg(test)]
    hook: Option<HookCell<'a>>,
}

/// `Debug` for the test hook, which a `dyn Fn` does not implement.
#[cfg(test)]
#[derive(Clone, Copy)]
pub(crate) struct HookCell<'a>(pub(crate) SafePointHook<'a>);

#[cfg(test)]
impl std::fmt::Debug for HookCell<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_str("SafePointHook")
    }
}

impl Default for FglmControl<'_> {
    fn default() -> Self {
        Self::unlimited()
    }
}

impl<'a> FglmControl<'a> {
    /// No deadline and no cancellation.
    pub fn unlimited() -> Self {
        Self {
            deadline: None,
            cancel: None,
            stopped: OnceLock::new(),
            #[cfg(test)]
            hook: None,
        }
    }

    /// Stop at the first safe point at or after `deadline`.
    pub fn with_deadline(mut self, deadline: Instant) -> Self {
        self.deadline = Some(deadline);
        self
    }

    /// Stop at the first safe point at least `budget` after now.
    ///
    /// A budget too large to represent as an `Instant` is no deadline at all.
    pub fn with_time_limit(self, budget: Duration) -> Self {
        match Instant::now().checked_add(budget) {
            Some(deadline) => self.with_deadline(deadline),
            None => self,
        }
    }

    /// Stop at the first safe point that observes `cancel` set.
    ///
    /// Read with `Relaxed` ordering: the flag carries no data, and a poll that misses a store made
    /// an instant earlier sees it at the next safe point.
    pub fn with_cancellation(mut self, cancel: &'a AtomicBool) -> Self {
        self.cancel = Some(cancel);
        self
    }

    /// The deadline, if any.
    pub fn deadline(&self) -> Option<Instant> {
        self.deadline
    }

    /// The stage and outcome of the stop this control has latched, if it has stopped.
    pub fn stopped(&self) -> Option<FglmError> {
        self.stopped
            .get()
            .map(|&(reason, stage)| error(reason, stage))
    }

    #[cfg(test)]
    pub(crate) fn with_hook(mut self, hook: SafePointHook<'a>) -> Self {
        self.hook = Some(HookCell(hook));
        self
    }

    /// A safe point in `stage`: `Err` if the conversion must stop here.
    ///
    /// The cancellation is tested before the deadline, so a conversion both cancelled and late
    /// reports the cancellation, which is the caller's explicit act.
    pub(crate) fn poll(&self, stage: FglmStage) -> Result<(), FglmError> {
        if let Some(&(reason, stage)) = self.stopped.get() {
            return Err(error(reason, stage));
        }
        let reason = if self.cancel.is_some_and(|c| c.load(Ordering::Relaxed)) {
            Some(StopReason::Cancelled)
        } else if self.deadline.is_some_and(|d| Instant::now() >= d) {
            Some(StopReason::Deadline)
        } else {
            self.hooked(stage)
        };
        match reason {
            None => Ok(()),
            Some(reason) => {
                let &(reason, stage) = self.stopped.get_or_init(|| (reason, stage));
                Err(error(reason, stage))
            }
        }
    }

    #[cfg(test)]
    fn hooked(&self, stage: FglmStage) -> Option<StopReason> {
        self.hook.and_then(|HookCell(hook)| hook(stage))
    }

    #[cfg(not(test))]
    fn hooked(&self, _stage: FglmStage) -> Option<StopReason> {
        None
    }
}

fn error(reason: StopReason, stage: FglmStage) -> FglmError {
    match reason {
        StopReason::Deadline => FglmError::DeadlineExceeded { stage },
        StopReason::Cancelled => FglmError::Cancelled { stage },
    }
}

#[cfg(test)]
mod tests {
    use super::{FglmControl, FglmStage, StopReason};
    use crate::{
        fields::Zp2147483647 as F,
        grobner::{
            benchmark_systems::katsura,
            f4,
            fglm::{
                fglm_to_lex_with_control, fglm_to_lex_with_options, BorderBatch, BorderBatchSize,
                ConversionRoute, ConversionStrategy, FglmError, FglmOptions, FglmStatistics,
                OperatorConstruction, WiedemannFallback,
            },
        },
        MonomialOrder, MultivariatePolynomial,
    };
    use std::{
        sync::{
            atomic::{AtomicBool, AtomicUsize, Ordering},
            Mutex,
        },
        time::{Duration, Instant},
    };

    const GREVLEX: MonomialOrder = MonomialOrder::GradedReverseLexicographic;

    /// A grevlex Gröbner basis of `system` over two variables.
    fn source2(system: &[&str]) -> Vec<MultivariatePolynomial<2, F>> {
        let generators: Vec<_> = system
            .iter()
            .map(|s| MultivariatePolynomial::parse(s, ["x", "y"]).unwrap())
            .collect();
        f4(&generators, GREVLEX).unwrap()
    }

    /// Katsura-5's grevlex basis: `D = 16`, with a border large enough to batch.
    fn katsura5() -> Vec<MultivariatePolynomial<5, F>> {
        f4(&katsura::<5, F>(), GREVLEX).unwrap()
    }

    /// The stages an unstopped conversion polls, in order.
    fn safe_points<const N: usize>(
        source: &[MultivariatePolynomial<N, F>],
        options: &FglmOptions,
    ) -> Vec<FglmStage> {
        let seen = Mutex::new(Vec::new());
        let hook = |stage| {
            seen.lock().unwrap().push(stage);
            None
        };
        let control = FglmControl::unlimited().with_hook(&hook);
        let (result, _) = fglm_to_lex_with_control(source, GREVLEX, options, &control);
        result.expect("an observing hook stops nothing");
        seen.into_inner().unwrap()
    }

    /// A conversion stopped at the `k`-th safe point (0-based) by a simulated clock that ticks once
    /// per poll across the whole conversion.
    fn stopped_at_tick<const N: usize>(
        source: &[MultivariatePolynomial<N, F>],
        options: &FglmOptions,
        k: usize,
    ) -> (
        Result<Vec<MultivariatePolynomial<N, F>>, FglmError>,
        FglmStatistics,
    ) {
        let ticks = AtomicUsize::new(0);
        let hook = |_| (ticks.fetch_add(1, Ordering::Relaxed) >= k).then_some(StopReason::Deadline);
        let control = FglmControl::unlimited().with_hook(&hook);
        fglm_to_lex_with_control(source, GREVLEX, options, &control)
    }

    // A stop in quotient enumeration leaves every later stage's figures at zero.
    #[test]
    fn test_a_stop_during_quotient_enumeration() {
        let (result, statistics) = stopped_at_tick(&katsura5(), &FglmOptions::recommended(), 0);
        assert_eq!(
            result,
            Err(FglmError::DeadlineExceeded {
                stage: FglmStage::QuotientEnumeration
            })
        );
        assert_eq!(statistics.stopped_at, Some(FglmStage::QuotientEnumeration));
        assert_eq!(
            statistics.quotient_dimension, 0,
            "enumeration did not finish"
        );
        assert_eq!(
            statistics.border.operator_columns, 0,
            "classification never ran"
        );
        assert_eq!(statistics.candidates_considered, 0, "the walk never ran");
        assert!(statistics.source_basis_elements > 0);
    }

    // A real deadline already passed stops at the first safe point, not after the conversion.
    #[test]
    fn test_a_passed_wall_deadline_stops_the_conversion() {
        let control = FglmControl::unlimited().with_deadline(Instant::now());
        let (result, statistics) =
            fglm_to_lex_with_control(&katsura5(), GREVLEX, &FglmOptions::recommended(), &control);
        assert!(matches!(result, Err(FglmError::DeadlineExceeded { .. })));
        assert!(result.unwrap_err().is_stop());
        assert_eq!(statistics.target_basis_elements, 0);
    }

    // Every construction strategy stops in operator construction, the parallel batches included,
    // and returns only after its workers are joined.
    #[test]
    fn test_a_stop_during_operator_construction() {
        let source = katsura5();
        let parallel = BorderBatch {
            size: BorderBatchSize::Fixed(1),
            workers: 4,
            ..BorderBatch::recommended()
        };
        for options in [
            FglmOptions::recommended().with_operator_construction(OperatorConstruction::PerColumn),
            FglmOptions::recommended()
                .with_operator_construction(OperatorConstruction::DeduplicatedBorder),
            FglmOptions::recommended()
                .with_operator_construction(OperatorConstruction::BatchedBorder)
                .with_border_batch(parallel),
        ] {
            let points = safe_points(&source, &options);
            let k = points
                .iter()
                .position(|s| *s == FglmStage::OperatorConstruction)
                .expect("construction polls")
                + 1;
            // Counts every poll, including any a worker makes after the stop has latched.
            let polls = AtomicUsize::new(0);
            let hook =
                |_| (polls.fetch_add(1, Ordering::SeqCst) >= k).then_some(StopReason::Cancelled);
            let control = FglmControl::unlimited().with_hook(&hook);
            let (result, statistics) =
                fglm_to_lex_with_control(&source, GREVLEX, &options, &control);
            let after_return = polls.load(Ordering::SeqCst);
            assert_eq!(
                result,
                Err(FglmError::Cancelled {
                    stage: FglmStage::OperatorConstruction
                }),
                "{:?}",
                options.operator_construction
            );
            assert_eq!(statistics.stopped_at, Some(FglmStage::OperatorConstruction));
            assert!(statistics.border.operator_columns > 0, "classification ran");
            assert_eq!(
                statistics.quotient_dimension, 0,
                "the algebra was never completed"
            );
            assert_eq!(statistics.operator_entries, 0);
            // The stop came at the first batch claim, so no batch was accounted for: a worker
            // that ignored the control would have reduced and recorded every batch first.
            assert_eq!(statistics.batches.batches, 0);
            // Joined: no worker is left to poll once the conversion has returned.
            std::thread::sleep(Duration::from_millis(20));
            assert_eq!(polls.load(Ordering::SeqCst), after_return);
        }
    }

    // A stop inside a Wiedemann attempt is reported as such, with the attempt counted.
    #[test]
    fn test_a_stop_during_a_wiedemann_attempt() {
        let source = katsura5();
        let options = forced_wiedemann();
        let points = safe_points(&source, &options);
        assert!(
            !points.contains(&FglmStage::ClassicalWalk),
            "Wiedemann converts katsura-5"
        );
        // The second Wiedemann safe point is inside the first attempt's Krylov loop.
        let k = points
            .iter()
            .position(|s| *s == FglmStage::Wiedemann)
            .expect("Wiedemann polls")
            + 1;
        let (result, statistics) = stopped_at_tick(&source, &options, k);
        assert_eq!(
            result,
            Err(FglmError::DeadlineExceeded {
                stage: FglmStage::Wiedemann
            })
        );
        assert_eq!(statistics.wiedemann_attempts, 1);
        assert_eq!(statistics.quotient_dimension, 16, "construction completed");
        assert_eq!(
            statistics.conversion_route,
            ConversionRoute::Classical,
            "no route returned a basis"
        );
        assert_eq!(statistics.target_basis_elements, 0);
    }

    /// `y` has a degree-2 minimal polynomial on a 4-dimensional quotient, so every projection is
    /// non-cyclic and forced Wiedemann falls back to the classical walk.
    const NON_SEPARATING: [&str; 2] = ["x^2 - 1", "y^2 - 1"];

    fn forced_wiedemann() -> FglmOptions {
        FglmOptions {
            conversion_strategy: ConversionStrategy::Wiedemann,
            ..FglmOptions::recommended()
        }
    }

    // A failed Wiedemann attempt leaves the fallback the remainder of the same deadline: a clock
    // that runs out exactly as the attempts end stops the fallback at its first safe point.
    #[test]
    fn test_the_fallback_inherits_the_remaining_deadline() {
        let source = source2(&NON_SEPARATING);
        let options = forced_wiedemann();
        let points = safe_points(&source, &options);
        let first_walk = points
            .iter()
            .position(|s| *s == FglmStage::ClassicalWalk)
            .expect("the fallback ran");
        assert!(points[..first_walk].contains(&FglmStage::Wiedemann));

        // A fresh allowance for the fallback would let this complete.
        let (result, statistics) = stopped_at_tick(&source, &options, first_walk);
        assert_eq!(
            result,
            Err(FglmError::DeadlineExceeded {
                stage: FglmStage::ClassicalWalk
            })
        );
        assert_eq!(statistics.wiedemann_attempts, 3);
        assert_eq!(
            statistics.wiedemann_fallback,
            Some(WiedemannFallback::NonCyclicProjection)
        );
        assert_eq!(
            statistics.candidates_considered, 0,
            "the walk never started"
        );

        // A clock long enough for every safe point completes, so the stop above was the deadline.
        let (result, _) = stopped_at_tick(&source, &options, points.len());
        assert!(result.is_ok());
    }

    // A cancellation set after the last Wiedemann safe point keeps the fallback from starting: it
    // stops at the fallback's first safe point, completing the deferred operators (#1233).
    #[test]
    fn test_cancellation_before_the_fallback_prevents_it() {
        let source = source2(&NON_SEPARATING);
        let options = forced_wiedemann();
        let points = safe_points(&source, &options);
        let last_wiedemann = points
            .iter()
            .rposition(|s| *s == FglmStage::Wiedemann)
            .expect("Wiedemann polls");

        let cancel = AtomicBool::new(false);
        let polls = AtomicUsize::new(0);
        let hook = |_| {
            if polls.fetch_add(1, Ordering::Relaxed) == last_wiedemann {
                cancel.store(true, Ordering::Relaxed);
            }
            None
        };
        let control = FglmControl::unlimited()
            .with_cancellation(&cancel)
            .with_hook(&hook);
        let (result, statistics) = fglm_to_lex_with_control(&source, GREVLEX, &options, &control);
        assert_eq!(
            result,
            Err(FglmError::Cancelled {
                stage: FglmStage::OperatorConstruction
            })
        );
        assert_eq!(statistics.candidates_considered, 0);
        assert_eq!(statistics.stopped_at, Some(FglmStage::OperatorConstruction));
        assert_eq!(statistics.operators_built, 1);
    }

    // A stop inside the classical walk keeps the counters of the candidates it had considered.
    #[test]
    fn test_a_stop_inside_the_classical_walk_keeps_partial_counters() {
        let source = katsura5();
        let options = FglmOptions {
            conversion_strategy: ConversionStrategy::Classical,
            ..FglmOptions::recommended()
        };
        let points = safe_points(&source, &options);
        let walk: Vec<usize> = points
            .iter()
            .enumerate()
            .filter(|(_, s)| **s == FglmStage::ClassicalWalk)
            .map(|(i, _)| i)
            .collect();
        assert!(
            walk.len() >= 2,
            "katsura-5's walk passes a strided safe point"
        );
        let (result, statistics) = stopped_at_tick(&source, &options, walk[1]);
        assert_eq!(
            result,
            Err(FglmError::DeadlineExceeded {
                stage: FglmStage::ClassicalWalk
            })
        );
        assert_eq!(
            statistics.candidates_considered,
            super::SAFE_POINT_STRIDE - 1
        );
        assert_eq!(
            statistics.candidates_considered,
            statistics.candidates_pruned
                + statistics.candidates_independent
                + statistics.candidates_dependent
        );
        assert_eq!(
            statistics.target_basis_elements, 0,
            "no basis was presented"
        );
    }

    // An unlimited control, or one that never fires, gives the same basis and statistics as no
    // control, on every strategy.
    #[test]
    fn test_an_unlimited_control_changes_nothing() {
        let cancel = AtomicBool::new(false);
        let far = FglmControl::unlimited()
            .with_time_limit(Duration::from_secs(3_600))
            .with_cancellation(&cancel);
        let systems: [&[&str]; 4] = [
            &NON_SEPARATING,
            &["x^2 - y", "y^3 - 1"],
            &["x^5 - 1", "y^3 - x"],
            &["x^2 + y^2 - 1", "x - y"],
        ];
        for strategy in [
            ConversionStrategy::Classical,
            ConversionStrategy::Adaptive,
            ConversionStrategy::Wiedemann,
        ] {
            let options = FglmOptions {
                conversion_strategy: strategy,
                ..FglmOptions::recommended()
            };
            for system in systems {
                let source = source2(system);
                let expected = fglm_to_lex_with_options(&source, GREVLEX, &options).unwrap();
                for control in [&FglmControl::unlimited(), &far] {
                    let (result, statistics) =
                        fglm_to_lex_with_control(&source, GREVLEX, &options, control);
                    assert_eq!((result.unwrap(), statistics), expected, "{:?}", system);
                }
            }
            let source = katsura5();
            let expected = fglm_to_lex_with_options(&source, GREVLEX, &options).unwrap();
            let (result, statistics) = fglm_to_lex_with_control(&source, GREVLEX, &options, &far);
            assert_eq!((result.unwrap(), statistics), expected);
        }
    }

    // A storage refusal under a control is still the storage refusal, not a stop.
    #[test]
    fn test_a_resource_refusal_is_not_a_stop() {
        let options = FglmOptions {
            max_operator_entries: 4,
            ..FglmOptions::recommended()
        };
        let control = FglmControl::unlimited().with_time_limit(Duration::from_secs(3_600));
        let (result, statistics) =
            fglm_to_lex_with_control(&katsura5(), GREVLEX, &options, &control);
        let error = result.unwrap_err();
        assert!(matches!(error, FglmError::OperatorStorageExceeded { .. }));
        assert!(!error.is_stop());
        assert_eq!(statistics.stopped_at, None);
    }

    // An unlimited control never stops and says so.
    #[test]
    fn test_an_unlimited_control_never_stops() {
        let control = FglmControl::unlimited();
        for _ in 0..1_000 {
            assert_eq!(control.poll(FglmStage::ClassicalWalk), Ok(()));
        }
        assert_eq!(control.stopped(), None);
    }

    // A deadline already passed stops the first safe point, naming its stage.
    #[test]
    fn test_a_passed_deadline_stops_the_first_safe_point() {
        let control = FglmControl::unlimited().with_deadline(Instant::now());
        assert_eq!(
            control.poll(FglmStage::QuotientEnumeration),
            Err(FglmError::DeadlineExceeded {
                stage: FglmStage::QuotientEnumeration
            })
        );
    }

    // The first stop is latched: a later safe point in another stage reports the first one.
    #[test]
    fn test_the_first_stop_is_latched() {
        let cancel = AtomicBool::new(false);
        let control = FglmControl::unlimited().with_cancellation(&cancel);
        assert_eq!(control.poll(FglmStage::Wiedemann), Ok(()));
        cancel.store(true, Ordering::Relaxed);
        let first = control.poll(FglmStage::Wiedemann);
        cancel.store(false, Ordering::Relaxed);
        assert_eq!(control.poll(FglmStage::ClassicalWalk), first);
        assert_eq!(
            control.stopped(),
            Some(FglmError::Cancelled {
                stage: FglmStage::Wiedemann
            })
        );
    }

    // Cancellation wins over a passed deadline, because it is the caller's explicit act.
    #[test]
    fn test_cancellation_is_reported_over_a_passed_deadline() {
        let cancel = AtomicBool::new(true);
        let control = FglmControl::unlimited()
            .with_deadline(Instant::now())
            .with_cancellation(&cancel);
        assert!(matches!(
            control.poll(FglmStage::ClassicalWalk),
            Err(FglmError::Cancelled { .. })
        ));
    }

    // An unrepresentable time limit is no deadline rather than a panic.
    #[test]
    fn test_an_unrepresentable_time_limit_is_no_deadline() {
        let control = FglmControl::unlimited().with_time_limit(Duration::MAX);
        assert_eq!(control.deadline(), None);
    }

    // The test hook can order a stop.
    #[test]
    fn test_the_hook_orders_a_stop() {
        let hook = |stage| (stage == FglmStage::ClassicalWalk).then_some(StopReason::Deadline);
        let control = FglmControl::unlimited().with_hook(&hook);
        assert_eq!(control.poll(FglmStage::Wiedemann), Ok(()));
        assert_eq!(
            control.poll(FglmStage::ClassicalWalk),
            Err(FglmError::DeadlineExceeded {
                stage: FglmStage::ClassicalWalk
            })
        );
    }
}
