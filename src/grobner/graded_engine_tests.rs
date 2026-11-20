use std::time::Duration;

use rand::{prelude::StdRng, SeedableRng};

use crate::{
    fields::{PrimeFieldElement64, Zp2147483647, Zp32003},
    grobner::{
        benchmark_systems::{cyclic, eco, katsura},
        f4,
        f4::observer,
        f4_observed_reported, f4_reported, f4_with_options, signature_route,
        solve_zero_dimensional_with_options, F4Error, F4Options, F4Statistics, GradedEngine,
        ParallelForward, ParallelSymbolic, ShippingReason, SignatureRoute, SolveOptions,
        SolveStrategy, StopKind,
    },
    poly::{BlockOrder, BlockOrderKind, MonomialOrder, WeightedTieBreak},
    FiniteField, MultivariatePolynomial,
};

type Goldilocks = PrimeFieldElement64<18446744069414584321>;
type Wide = PrimeFieldElement64<18446744073709551263>;
const GREVLEX: MonomialOrder = MonomialOrder::GradedReverseLexicographic;
const GRADED: [MonomialOrder; 2] = [
    MonomialOrder::GradedReverseLexicographic,
    MonomialOrder::GradedLexicographic,
];

fn options(engine: GradedEngine, count: usize) -> F4Options {
    F4Options {
        graded_engine: engine,
        parallel_forward: ParallelForward::Forced { workers: count },
        parallel_symbolic: if count == 1 {
            ParallelSymbolic::Serial
        } else {
            ParallelSymbolic::Auto { max_workers: count }
        },
        ..F4Options::default()
    }
}

fn adaptive(count: usize) -> F4Options {
    options(GradedEngine::Adaptive, count)
}

fn non_graded<const N: usize>() -> Vec<MonomialOrder> {
    vec![
        MonomialOrder::Lexicographic,
        MonomialOrder::weighted(&[1; N], WeightedTieBreak::ReverseLexicographic)
            .expect("positive weights"),
        MonomialOrder::Block(
            BlockOrder::checked(
                N,
                N / 2,
                BlockOrderKind::GradedReverseLexicographic,
                BlockOrderKind::GradedReverseLexicographic,
            )
            .expect("two blocks"),
        ),
    ]
}

/// Both graded orders at 1 and 4 workers: the adaptive option returns the conventional basis and
/// reports the decision `signature_route` takes; returns the 1-worker grevlex route.
fn agrees<const N: usize, F: FiniteField>(
    system: &[MultivariatePolynomial<N, F>],
) -> SignatureRoute {
    for order in GRADED {
        for count in [1, 4] {
            let conventional =
                f4_with_options(system, order, &options(GradedEngine::Conventional, count))
                    .expect("conventional F4 finishes");
            assert_eq!(conventional.1.graded_route, None);
            let (basis, statistics) =
                f4_with_options(system, order, &adaptive(count)).expect("adaptive finishes");
            assert_eq!(basis, conventional.0, "{order:?}, {count} workers");
            let route = statistics.graded_route.expect("a graded order is routed");
            let expected = signature_route(system, order, &adaptive(count)).expect("graded");
            assert_eq!(route.route, expected.route);
            assert_eq!(route.workers, expected.workers);
            assert!(route.workers <= count);
        }
    }
    signature_route(system, GREVLEX, &adaptive(1))
        .expect("graded")
        .route
}

/// The option is off in every preset, so no default changes.
#[test]
fn test_graded_engine_is_conventional_by_default() {
    assert_eq!(GradedEngine::default(), GradedEngine::Conventional);
    assert_eq!(
        F4Options::default().graded_engine,
        GradedEngine::Conventional
    );
    assert_eq!(
        F4Options::recommended().graded_engine,
        GradedEngine::Conventional
    );
    assert_eq!(
        F4Options::baseline().graded_engine,
        GradedEngine::Conventional
    );
    let (_, statistics) =
        f4_with_options(&katsura::<6, Zp32003>(), GREVLEX, &F4Options::default()).unwrap();
    assert_eq!(statistics.graded_route, None);
}

/// Every dispatch route (small, spread degrees, signature) at four fields returns the conventional
/// basis under both graded orders.
#[test]
fn test_adaptive_option_equals_conventional_f4_on_every_route() {
    assert_eq!(
        agrees(&katsura::<4, Zp32003>()),
        SignatureRoute::Shipping(ShippingReason::Small)
    );
    assert_eq!(
        agrees(&cyclic::<6, Goldilocks>()),
        SignatureRoute::Shipping(ShippingReason::DegreeSpread)
    );
    assert_eq!(
        agrees(&katsura::<6, Zp2147483647>()),
        SignatureRoute::Signature
    );
    assert_eq!(agrees(&eco::<6, Wide>()), SignatureRoute::Signature);
}

/// Lex, `Weighted` and `Block` ignore the option: the conventional algorithm, its statistics, and
/// no route.
#[test]
fn test_non_graded_orders_keep_conventional_f4() {
    let system = katsura::<4, Zp32003>();
    for order in non_graded::<4>() {
        for count in [1, 4] {
            let expected =
                f4_with_options(&system, order, &options(GradedEngine::Conventional, count))
                    .expect("conventional F4 finishes");
            let actual = f4_with_options(&system, order, &adaptive(count)).expect("finishes");
            assert_eq!(actual.0, expected.0, "{order:?}");
            assert_eq!(actual.1.graded_route, None, "{order:?}");
            assert_eq!(actual.1.batches, expected.1.batches, "{order:?}");
        }
    }
    let system = katsura::<4, Goldilocks>();
    for order in non_graded::<4>() {
        let actual = f4_reported(&system, order, &adaptive(1));
        assert_eq!(actual.1.graded_route, None);
        assert_eq!(actual.0, f4(&system, order));
    }
}

/// A route that chooses conventional F4 keeps conventional F4's full statistics.
#[test]
fn test_shipping_route_keeps_conventional_statistics() {
    let system = katsura::<4, Goldilocks>();
    let (basis, statistics) = f4_with_options(&system, GREVLEX, &adaptive(1)).unwrap();
    assert_eq!(basis, f4(&system, GREVLEX).unwrap());
    let route = statistics.graded_route.expect("routed");
    assert_eq!(route.route, SignatureRoute::Shipping(ShippingReason::Small));
    assert!(statistics.batches > 0);
    assert!(statistics.max_matrix_rows > 0);
}

/// The signature route reports its batches and matrix sizes in `F4Statistics`.
#[test]
fn test_signature_route_reports_its_work() {
    for count in [1, 4] {
        let (_, statistics) =
            f4_with_options(&katsura::<7, Zp32003>(), GREVLEX, &adaptive(count)).unwrap();
        let route = statistics.graded_route.expect("routed");
        assert_eq!(route.route, SignatureRoute::Signature);
        assert!(route.workers <= count);
        assert!(statistics.batches > 0);
        assert!(statistics.max_matrix_rows > 0 && statistics.max_matrix_columns > 0);
        assert!(statistics.elements_added > 0);
        assert_eq!(statistics.bytes_per_entry, 16);
    }
}

/// `f4_reported`, the entry point the solvers use, routes too; `f4` and `f4_observed_reported`
/// do not, because they take no option or promise per-batch observation of conventional F4.
#[test]
fn test_reported_entry_point_routes_and_observed_does_not() {
    let system = katsura::<7, Goldilocks>();
    let (basis, statistics) = f4_reported(&system, GREVLEX, &adaptive(2));
    assert_eq!(basis, f4(&system, GREVLEX));
    assert_eq!(
        statistics.graded_route.expect("routed").route,
        SignatureRoute::Signature
    );
    let (observed, statistics) =
        f4_observed_reported(&system, GREVLEX, &adaptive(2), &mut observer::Ignore);
    assert_eq!(observed, f4(&system, GREVLEX));
    assert_eq!(statistics.graded_route, None);
}

/// A crossed wall budget on the signature route is the conventional typed time stop, not a
/// fallback, with the route still reported.
#[test]
fn test_wall_budget_is_typed_on_the_adaptive_route() {
    for count in [1, 4] {
        let options = F4Options {
            max_wall_time: Some(Duration::ZERO),
            ..adaptive(count)
        };
        let (result, statistics) = f4_reported(&katsura::<7, Zp32003>(), GREVLEX, &options);
        let error = result.expect_err("no time to finish");
        assert!(
            matches!(error, F4Error::TimeBudgetExceeded { .. }),
            "{error:?}"
        );
        assert_eq!(error.stop_kind(), StopKind::Time);
        assert_eq!(
            statistics.graded_route.expect("routed").route,
            SignatureRoute::Signature
        );
    }
}

/// A certification budget on the signature route stops typed, never as a failed certificate.
#[test]
fn test_certification_budget_is_typed_on_the_adaptive_route() {
    let options = F4Options {
        certify: true,
        max_certify_time: Some(Duration::ZERO),
        ..adaptive(2)
    };
    let error = f4_with_options(&katsura::<7, Goldilocks>(), GREVLEX, &options).expect_err("stop");
    assert!(matches!(
        error,
        F4Error::CertificationTimeBudgetExceeded { .. }
    ));
    let certified = F4Options {
        certify: true,
        max_certify_time: Some(Duration::from_secs(600)),
        ..adaptive(2)
    };
    assert!(f4_with_options(&katsura::<7, Goldilocks>(), GREVLEX, &certified).is_ok());
}

/// A signature size refusal falls back to conventional F4 once, reports the crossed limit, and
/// returns conventional F4's own typed result.
#[test]
fn test_size_limit_falls_back_once_and_stays_typed() {
    let system = katsura::<7, Zp32003>();
    let tight = |engine| F4Options {
        max_matrix_rows: 1,
        ..options(engine, 1)
    };
    let (result, statistics) = f4_reported(&system, GREVLEX, &tight(GradedEngine::Adaptive));
    assert!(matches!(
        statistics.graded_route.expect("routed").route,
        SignatureRoute::Shipping(ShippingReason::Fallback(F4Error::TooManyRows { .. }))
    ));
    assert_eq!(
        result,
        f4_reported(&system, GREVLEX, &tight(GradedEngine::Conventional)).0
    );
    // The statistics are conventional F4's own, as the plain call reports them, plus the route.
    let plain = f4_reported(&system, GREVLEX, &tight(GradedEngine::Conventional)).1;
    assert_eq!(
        F4Statistics {
            graded_route: None,
            ..statistics
        },
        plain
    );
}

/// One basis for every worker count and repetition under the adaptive option.
#[test]
fn test_adaptive_option_is_deterministic_across_workers() {
    let system = katsura::<6, Zp2147483647>();
    let expected = f4(&system, GREVLEX).unwrap();
    for count in [1, 2, 4, 8, 16] {
        for _ in 0..2 {
            assert_eq!(
                f4_with_options(&system, GREVLEX, &adaptive(count))
                    .unwrap()
                    .0,
                expected,
                "{count} workers"
            );
        }
    }
}

/// A solver built on `f4_reported` runs its grevlex source basis through the option and returns the
/// same solutions; its default lex route is untouched.
#[test]
fn test_solver_routes_its_graded_basis_through_the_option() {
    let system = katsura::<6, Zp32003>();
    let solve = |strategy, f4| {
        let options = SolveOptions {
            strategy,
            f4,
            ..SolveOptions::default()
        };
        solve_zero_dimensional_with_options(&system, &mut StdRng::seed_from_u64(7), &options)
            .expect("katsura-6 is zero-dimensional")
    };
    let grevlex = SolveStrategy::GrevlexF4ThenFglm;
    let (expected, _) = solve(grevlex, F4Options::default());
    let (actual, statistics) = solve(grevlex, adaptive(2));
    assert_eq!(actual, expected);
    let f4 = statistics.f4.expect("a source basis was computed");
    assert_eq!(
        f4.graded_route.expect("routed").route,
        SignatureRoute::Signature
    );

    let (lex, statistics) = solve(SolveStrategy::DirectLexF4, adaptive(2));
    assert_eq!(
        lex,
        solve(SolveStrategy::DirectLexF4, F4Options::default()).0
    );
    assert_eq!(statistics.f4.expect("computed").graded_route, None);
}
