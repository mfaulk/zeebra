//! #974 M33-Q safety suite (plan §12.1): every budget M33 relies on, tripped on purpose through the
//! public entry points at one worker and at sixteen, on rows where the budget is what stops the
//! solve. Thread high-water is in `m33_thread_cap.rs`, alone in its binary so no other test's
//! workers are counted. How each test was shown to fail with its budget disabled is in the PR body.

use std::time::{Duration, Instant};
use zeebra::{
    fields::{PrimeFieldElement64, Zp2147483647},
    grobner::{
        benchmark_systems::katsura, f4::symbolic::MonicBasis, f4_observed_reported, f4_reported,
        f4_signature_reported, BatchObserver, Cascade, CriticalPair, F4Error, F4Options,
        ParallelForward, ParallelSymbolic, ShippingReason, SigF4Error, SignatureRoute,
    },
    FiniteField, MonomialOrder, MultivariatePolynomial,
};

/// A few batches of katsura-11 at most, on any team and build, so the wall budget is what stops the
/// solve: release at 16 workers needs about fifty times this for the whole basis.
const WALL_BUDGET_MILLIS: u64 = 5;
/// 2⁶⁴−353, Track G's field.
type Wide = PrimeFieldElement64<18446744073709551263>;
const GREVLEX: MonomialOrder = MonomialOrder::GradedReverseLexicographic;
/// The longest a cooperative stop may take past its budget here: one batch or one interreduction
/// element of katsura-11 in a debug build, with room for a loaded CI runner.
const OVERSHOOT: Duration = Duration::from_secs(20);

/// The options the M33 harness gives a `workers`-worker call (`examples/m33_qualify.rs`).
fn at(workers: usize) -> F4Options {
    F4Options {
        parallel_forward: if workers == 1 {
            ParallelForward::Serial
        } else {
            ParallelForward::Auto {
                max_workers: workers,
            }
        },
        parallel_symbolic: if workers == 1 {
            ParallelSymbolic::Serial
        } else {
            ParallelSymbolic::Auto {
                max_workers: workers,
            }
        },
        ..F4Options::default()
    }
}

/// Katsura-11 is on the signature route at both counts: eleven variables are past the small-team
/// and worker-crossover bands, so 16 workers get a 16-worker parallel cascade.
fn signature_row<F: FiniteField>() -> Vec<MultivariatePolynomial<11, F>> {
    katsura::<11, F>()
}

/// Runs the entry point, asserting it took the signature engine on the expected team first.
fn entry<const N: usize, F: FiniteField>(
    system: &[MultivariatePolynomial<N, F>],
    options: &F4Options,
    workers: usize,
) -> (
    Result<Vec<MultivariatePolynomial<N, F>>, SigF4Error>,
    SignatureRoute,
    Duration,
) {
    let clock = Instant::now();
    let (result, report) = f4_signature_reported(system, GREVLEX, options);
    let elapsed = clock.elapsed();
    assert_eq!(report.workers, workers, "team");
    let cascade = if workers == 1 {
        Cascade::Serial
    } else {
        Cascade::Parallel
    };
    assert_eq!(report.cascade, Some(cascade));
    (result, report.route, elapsed)
}

/// A wall budget shorter than the solve stops it typed at both counts (as a time stop, not a size
/// fallback), within one batch of the budget, on the signature route Track G times.
///
/// The budget must stay far below the solve at every worker count and build profile: at 300 ms,
/// 16 workers in release finished katsura-11 inside it and returned a basis (#1119).
#[test]
fn test_wall_budget_stops_the_signature_route_typed_at_1_and_16_workers() {
    let system = signature_row::<Wide>();
    for workers in [1, 16] {
        let budget = Duration::from_millis(WALL_BUDGET_MILLIS);
        let options = F4Options {
            max_wall_time: Some(budget),
            ..at(workers)
        };
        let (result, route, elapsed) = entry(&system, &options, workers);
        assert_eq!(route, SignatureRoute::Signature, "{workers} workers");
        match result {
            Err(SigF4Error::Budget(F4Error::TimeBudgetExceeded { budget_millis, .. }))
            | Err(SigF4Error::Budget(F4Error::InterreductionTimeBudgetExceeded {
                budget_millis,
                ..
            })) => assert_eq!(budget_millis, WALL_BUDGET_MILLIS),
            other => panic!("{workers} workers: expected a typed time stop, got {other:?}"),
        }
        assert!(
            elapsed < budget + OVERSHOOT,
            "{workers} workers: {elapsed:?}"
        );
    }
}

/// A matrix-row cap the signature engine crosses falls back to the shipping F4 under the same cap,
/// whose own typed refusal is returned, at both counts and at a 31-bit field. The signature engine
/// reads the cap scaled by its default over F4's, 10× (#1186), so 20 rows is 200 there.
#[test]
fn test_matrix_row_budget_falls_back_typed_at_1_and_16_workers() {
    fn check<F: FiniteField>() {
        let system = signature_row::<F>();
        for workers in [1, 16] {
            let options = F4Options {
                max_matrix_rows: 20,
                ..at(workers)
            };
            let (result, route, _) = entry(&system, &options, workers);
            assert!(
                matches!(
                    route,
                    SignatureRoute::Shipping(ShippingReason::Fallback(F4Error::TooManyRows {
                        limit: 200
                    }))
                ),
                "{workers} workers: {route:?}"
            );
            let shipping = f4_reported(&system, GREVLEX, &options).0;
            assert!(matches!(shipping, Err(F4Error::TooManyRows { limit: 20 })));
            assert_eq!(result, shipping.map_err(SigF4Error::Budget));
        }
    }
    check::<Wide>();
    check::<Zp2147483647>();
}

/// A live-byte budget binds on the signature route at one worker (the serial cascade, #962) and at
/// sixteen (the parallel cascade), on 2⁶⁴−353 and 2³¹−1: the route reports the typed fallback and
/// the call returns what the shipping F4 returns under the same budget.
#[test]
fn test_live_byte_budget_binds_on_the_signature_route_at_1_and_16_workers() {
    fn check<F: FiniteField>() {
        let system = signature_row::<F>();
        for workers in [1, 16] {
            let options = F4Options {
                max_live_bytes: 1 << 16,
                ..at(workers)
            };
            let (result, route, _) = entry(&system, &options, workers);
            assert!(
                matches!(
                    route,
                    SignatureRoute::Shipping(ShippingReason::Fallback(F4Error::TooManyLiveBytes {
                        limit: 65536,
                        ..
                    }))
                ),
                "{workers} workers: {route:?}"
            );
            let shipping = f4_reported(&system, GREVLEX, &options).0;
            assert!(matches!(shipping, Err(F4Error::TooManyLiveBytes { .. })));
            assert_eq!(result, shipping.map_err(SigF4Error::Budget));
        }
    }
    check::<Wide>();
    check::<Zp2147483647>();
}

/// Stops after a fixed number of batches.
struct StopAfter(usize);

impl<const N: usize, F: FiniteField> BatchObserver<N, F> for StopAfter {
    fn batch(&mut self, _: &MonicBasis<N, F>, _: &[CriticalPair<N>]) {
        self.0 = self.0.saturating_sub(1);
    }
    fn should_stop(&self) -> bool {
        self.0 == 0
    }
}

/// A caller's stop cancels the shipping F4 mid-solve with the typed error at both counts, after
/// exactly the batches it allowed, and the counters of the work done survive the stop.
#[test]
fn test_cancellation_stops_the_shipping_f4_typed_at_1_and_16_workers() {
    let system = katsura::<9, Wide>();
    for workers in [1, 16] {
        let (result, statistics) =
            f4_observed_reported(&system, GREVLEX, &at(workers), &mut StopAfter(3));
        assert_eq!(result, Err(F4Error::StoppedByObserver), "{workers} workers");
        assert_eq!(statistics.batches, 2, "{workers} workers");
        assert!(statistics.pairs_reduced > 0);
    }
}
