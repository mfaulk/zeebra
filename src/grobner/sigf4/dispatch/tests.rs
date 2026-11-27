use std::time::Duration;

use super::{
    f4_signature, f4_signature_reported, signature_options, signature_route, Cascade,
    ShippingReason, SignatureDispatch, SignatureRoute, SIGNATURE_CROSSOVER_VARIABLES,
    SIGNATURE_CROSSOVER_WORKERS, SIGNATURE_MIN_VARIABLES, SIGNATURE_SMALL_TEAM,
    SIGNATURE_SMALL_TEAM_VARIABLES,
};
use crate::{
    fields::{PrimeFieldElement64, Zp2147483647, Zp32003},
    grobner::{
        benchmark_systems::{cyclic, eco, katsura, noon},
        f4::{
            certify_f4_output, f4_with_options, F4Error, F4Options, ParallelForward,
            ParallelSymbolic,
        },
        sigf4::{SigF4Error, SigF4Options},
    },
    poly::{BlockOrder, BlockOrderKind, MonomialOrder, WeightedTieBreak},
    FiniteField, MultivariatePolynomial,
};

type Goldilocks = PrimeFieldElement64<18446744069414584321>;
const GREVLEX: MonomialOrder = MonomialOrder::GradedReverseLexicographic;
const GRADED: [MonomialOrder; 2] = [
    MonomialOrder::GradedReverseLexicographic,
    MonomialOrder::GradedLexicographic,
];

fn route<const N: usize, F: FiniteField>(
    system: &[MultivariatePolynomial<N, F>],
) -> SignatureRoute {
    signature_route(system, GREVLEX, &workers(1))
        .expect("graded")
        .route
}

/// The dispatch decision at `count` workers.
fn decide<const N: usize, F: FiniteField>(
    system: &[MultivariatePolynomial<N, F>],
    count: usize,
) -> SignatureDispatch {
    signature_route(system, GREVLEX, &workers(count)).expect("graded")
}

/// `N` generators, each with every monomial of degree at most two and a nonzero pseudorandom
/// coefficient: the dense MQ shape.
fn dense_quadratic<const N: usize, F: FiniteField>(seed: u64) -> Vec<MultivariatePolynomial<N, F>> {
    let mut state = seed;
    let mut monomials = vec![[0u32; N]];
    for i in 0..N {
        let mut e = [0; N];
        e[i] = 1;
        monomials.push(e);
        for j in i..N {
            let mut e = [0; N];
            e[i] += 1;
            e[j] += 1;
            monomials.push(e);
        }
    }
    (0..N)
        .map(|_| {
            let terms: Vec<_> = monomials
                .iter()
                .map(|e| {
                    state = state
                        .wrapping_mul(6364136223846793005)
                        .wrapping_add(1442695040888963407);
                    (crate::Monomial::new(e), F::new(1 + (state >> 33) % 30000))
                })
                .collect();
            MultivariatePolynomial::new(&terms)
        })
        .collect()
}

/// Options capping both the forward and the symbolic team at `count`.
fn workers(count: usize) -> F4Options {
    F4Options {
        parallel_forward: ParallelForward::Forced { workers: count },
        parallel_symbolic: if count == 1 {
            ParallelSymbolic::Serial
        } else {
            ParallelSymbolic::Auto { max_workers: count }
        },
        ..F4Options::default()
    }
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

/// The entry point's basis equals the shipping F4's under the same options, and certifies.
fn agrees<const N: usize, F: FiniteField>(system: &[MultivariatePolynomial<N, F>]) {
    for order in GRADED {
        for count in [1, 4] {
            let options = F4Options {
                certify: true,
                max_certify_time: Some(Duration::from_secs(600)),
                ..workers(count)
            };
            let expected = f4_with_options(system, order, &workers(count))
                .expect("shipping F4 finishes")
                .0;
            let (actual, report) = f4_signature_reported(system, order, &options);
            let actual = actual.expect("entry point finishes");
            assert_eq!(
                actual, expected,
                "{order:?}, {count} workers, {:?}",
                report.route
            );
            assert!(certify_f4_output(system, &actual, order).checks_passed());
        }
    }
}

/// Lex, `Weighted` and `Block` are refused with `Unsupported` before either engine runs, whichever
/// route the input would take, at two fields.
#[test]
fn test_every_non_graded_order_is_unsupported_on_every_route() {
    fn refused<const N: usize, F: FiniteField>(system: &[MultivariatePolynomial<N, F>]) {
        for order in non_graded::<N>() {
            let (result, report) = f4_signature_reported(system, order, &F4Options::default());
            assert!(
                matches!(result, Err(SigF4Error::Unsupported { .. })),
                "{order:?}"
            );
            assert_eq!(report.features.generators, 0, "no feature was read");
            assert!(matches!(
                signature_route(system, order, &F4Options::default()),
                Err(SigF4Error::Unsupported { .. })
            ));
        }
    }
    refused(&katsura::<4, Zp32003>());
    refused(&katsura::<7, Zp32003>());
    refused(&cyclic::<6, Goldilocks>());
    refused(&katsura::<7, Goldilocks>());
}

/// Cyclic-n's nonlinear degrees run 2..n, so from six variables up it goes to the shipping F4.
#[test]
fn test_spread_degrees_route_to_shipping() {
    let expected = SignatureRoute::Shipping(ShippingReason::DegreeSpread);
    assert_eq!(route(&cyclic::<6, Zp32003>()), expected);
    assert_eq!(route(&cyclic::<7, Goldilocks>()), expected);
}

/// Inputs in fewer than six variables go to the shipping F4, counting only variables that appear.
#[test]
fn test_small_inputs_route_to_shipping() {
    let small = SignatureRoute::Shipping(ShippingReason::Small);
    assert_eq!(route(&katsura::<4, Zp32003>()), small);
    assert_eq!(route(&cyclic::<5, Goldilocks>()), small);
    let embedded: Vec<MultivariatePolynomial<8, Zp32003>> = katsura::<4, Zp32003>()
        .iter()
        .map(|p| {
            MultivariatePolynomial::new(
                &p.terms()
                    .iter()
                    .map(|(m, c)| {
                        let mut e = [0; 8];
                        e[..4].copy_from_slice(m.exponents());
                        (crate::Monomial::new(&e), *c)
                    })
                    .collect::<Vec<_>>(),
            )
        })
        .collect();
    assert_eq!(route(&embedded), small);
    assert_eq!(SIGNATURE_MIN_VARIABLES, 6);
}

/// A linear system has no signature work to save and goes to the shipping F4.
#[test]
fn test_linear_inputs_route_to_shipping() {
    let linear: Vec<_> = katsura::<7, Zp32003>()
        .into_iter()
        .filter(|p| p.degree() == 1)
        .collect();
    assert_eq!(
        route(&linear),
        SignatureRoute::Shipping(ShippingReason::Linear)
    );
}

/// Katsura (degree 2), Eco (degrees 2 and 3) and Noon (degree 3) take the signature engine.
#[test]
fn test_near_uniform_degrees_route_to_signature() {
    assert_eq!(route(&katsura::<7, Zp32003>()), SignatureRoute::Signature);
    assert_eq!(route(&eco::<7, Goldilocks>()), SignatureRoute::Signature);
    assert_eq!(route(&noon::<6, Zp32003>()), SignatureRoute::Signature);
    let features = decide(&eco::<7, Goldilocks>(), 1).features;
    assert_eq!((features.min_nonlinear_degree, features.max_degree), (2, 3));
}

/// On every route, at one and four workers and both graded orders, the entry point returns the
/// shipping F4's reduced basis and it certifies.
#[test]
fn test_entry_point_equals_shipping_f4_on_every_route() {
    agrees(&katsura::<4, Zp32003>());
    agrees(&cyclic::<6, Goldilocks>());
    agrees(&katsura::<6, Zp32003>());
    agrees(&eco::<6, Goldilocks>());
    agrees(&noon::<6, Goldilocks>());
}

/// A zero wall budget on the signature route is the shipping F4's typed time stop.
#[test]
fn test_wall_budget_is_a_typed_error() {
    for count in [1, 4] {
        let options = F4Options {
            max_wall_time: Some(Duration::ZERO),
            ..workers(count)
        };
        let (result, report) = f4_signature_reported(&katsura::<7, Zp32003>(), GREVLEX, &options);
        assert_eq!(report.route, SignatureRoute::Signature);
        assert!(matches!(
            result,
            Err(SigF4Error::Budget(F4Error::TimeBudgetExceeded { .. }))
        ));
    }
}

/// The signature route's certificate runs under `max_certify_time`, and its stop is typed and not a
/// rejection (#912).
#[test]
fn test_certification_budget_is_a_typed_stop() {
    let options = F4Options {
        certify: true,
        max_certify_time: Some(Duration::ZERO),
        ..workers(2)
    };
    let (result, report) = f4_signature_reported(&katsura::<7, Goldilocks>(), GREVLEX, &options);
    assert_eq!(report.route, SignatureRoute::Signature);
    let Err(SigF4Error::Budget(error)) = result else {
        panic!("expected a stop, got {result:?}");
    };
    assert!(matches!(
        error,
        F4Error::CertificationTimeBudgetExceeded { .. }
    ));
    assert_eq!(error.limit_name(), "max_certify_time");
}

/// A signature-engine size refusal reruns the shipping F4 with the caller's options and reports the
/// limit that was crossed; the shipping F4's own refusal comes back typed.
#[test]
fn test_signature_size_limit_falls_back_to_shipping() {
    let system = katsura::<7, Zp32003>();
    let options = F4Options {
        max_matrix_rows: 1,
        ..F4Options::default()
    };
    let (result, report) = f4_signature_reported(&system, GREVLEX, &options);
    assert!(matches!(
        report.route,
        SignatureRoute::Shipping(ShippingReason::Fallback(F4Error::TooManyRows { .. }))
    ));
    assert_eq!(
        result,
        f4_with_options(&system, GREVLEX, &options)
            .map(|(basis, _)| basis)
            .map_err(SigF4Error::Budget)
    );
}

/// The dispatch reads features only: computing them takes well under a millisecond on Katsura-7.
#[test]
fn test_dispatch_is_cheap_and_recorded() {
    let (result, report) =
        f4_signature_reported(&katsura::<7, Zp32003>(), GREVLEX, &F4Options::default());
    assert!(result.is_ok());
    assert_eq!(report.features.generators, 7);
    assert_eq!(report.features.variables, 7);
    assert!(
        report.dispatch < Duration::from_millis(50),
        "{:?}",
        report.dispatch
    );
    assert_eq!(
        f4_signature(&katsura::<7, Zp32003>(), GREVLEX, &F4Options::default()),
        result
    );
}

/// `system` with every term `x_k^2` removed: no top form has a pure power of `x_k`, so the
/// coordinate point `e_k` is a zero of every top form.
fn without_square<const N: usize, F: FiniteField>(
    system: &[MultivariatePolynomial<N, F>],
    k: usize,
) -> Vec<MultivariatePolynomial<N, F>> {
    system
        .iter()
        .map(|p| {
            let terms: Vec<_> = p
                .terms()
                .iter()
                .filter(|(m, _)| m.exponents()[k] != 2)
                .map(|(m, c)| (*m, *c))
                .collect();
            MultivariatePolynomial::new(&terms)
        })
        .collect()
}

/// A quadratic input in the crossover band whose top forms share a coordinate zero takes the
/// signature engine below `SIGNATURE_CROSSOVER_WORKERS` workers and the shipping F4 from there up,
/// at three fields. Quadratics just outside the band, and dense quadratics inside it (every top
/// form has every square, so there is no witness), keep the signature engine at every worker
/// count (#978: mq-random-10 / Goldilocks is the dense shape).
#[test]
fn test_quadratic_in_the_band_crosses_to_shipping_at_the_worker_threshold() {
    fn crosses<const N: usize, F: FiniteField>() {
        let dense = dense_quadratic::<N, F>(N as u64);
        let witnessed = without_square(&dense, N / 2);
        assert_eq!(decide(&dense, 16).features.infinity_witness, None);
        assert_eq!(
            decide(&witnessed, 16).features.infinity_witness,
            Some(N / 2)
        );
        for count in 1..=16 {
            let report = decide(&dense, count);
            assert_eq!(
                report.route,
                SignatureRoute::Signature,
                "dense, {N} variables, {count} workers"
            );
            assert_eq!(report.features.workers, count);
            let report = decide(&witnessed, count);
            let expected = if SIGNATURE_CROSSOVER_VARIABLES.contains(&N)
                && count >= SIGNATURE_CROSSOVER_WORKERS
            {
                SignatureRoute::Shipping(ShippingReason::WorkerCrossover)
            } else {
                SignatureRoute::Signature
            };
            assert_eq!(
                report.route, expected,
                "witnessed, {N} variables, {count} workers"
            );
        }
    }
    assert_eq!(SIGNATURE_CROSSOVER_WORKERS, 4);
    assert_eq!(SIGNATURE_CROSSOVER_VARIABLES, 10..=10);
    crosses::<10, Zp32003>();
    crosses::<10, Zp2147483647>();
    crosses::<10, Goldilocks>();
    crosses::<9, Zp32003>();
    crosses::<11, Goldilocks>();
}

/// MQ10 from the published ladder, the development row the crossover exists for, crosses at four
/// workers at both of its fields and keeps the signature engine below that.
#[cfg(feature = "external-runners")]
#[test]
fn test_mq10_crosses_at_four_workers_at_both_fields() {
    fn mq10<F: FiniteField>(modulus: u64) {
        let instance = crate::grobner::external::corpus::instance("mq-random-10", modulus, GREVLEX)
            .expect("ladder row");
        let names: [&str; 10] = std::array::from_fn(|i| instance.variables[i].as_str());
        let system: Vec<MultivariatePolynomial<10, F>> = instance
            .system
            .iter()
            .map(|s| MultivariatePolynomial::parse(s, names).expect("parses"))
            .collect();
        for count in [1, 2, 3, 4, 8, 16] {
            let report = decide(&system, count);
            assert!(report.features.infinity_witness.is_some());
            let crossed = report.route == SignatureRoute::Shipping(ShippingReason::WorkerCrossover);
            assert_eq!(
                crossed,
                count >= SIGNATURE_CROSSOVER_WORKERS,
                "{count} workers, {:?}",
                report.features
            );
        }
    }
    mq10::<Zp32003>(32003);
    mq10::<Zp2147483647>(2147483647);
}

/// Katsura-10 is quadratic in ten variables, but each of its quadratics carries `x_k^2` for some
/// `k` and together they carry every square, so it has no coordinate zero at infinity and keeps
/// the signature engine at every worker count. At GF(2³¹−1) and 16 workers that engine is 0.601×
/// conventional F4 (#978).
#[test]
fn test_katsura10_keeps_the_signature_engine_at_every_worker_count() {
    fn keeps<F: FiniteField>() {
        let system = katsura::<10, F>();
        for count in [1, 2, 4, 8, 16] {
            let report = decide(&system, count);
            assert_eq!(report.features.variables, 10);
            assert_eq!(report.features.infinity_witness, None);
            assert_eq!(report.route, SignatureRoute::Signature, "{count} workers");
        }
    }
    keeps::<Zp32003>();
    keeps::<Zp2147483647>();
}

/// The witness reads each generator's top form only: a pure power of `x_k` below the generator's
/// degree does not cover `x_k`, a linear generator covers the variables it contains, a nonzero
/// constant covers every variable, and a variable that appears nowhere is never a witness.
#[test]
fn test_infinity_witness_reads_pure_powers_in_the_top_forms() {
    type F = Zp32003;
    let m = |e: [u32; 3]| crate::Monomial::new(&e);
    let poly = |terms: &[([u32; 3], u64)]| {
        let terms: Vec<_> = terms.iter().map(|&(e, c)| (m(e), F::new(c))).collect();
        MultivariatePolynomial::<3, F>::new(&terms)
    };
    let witness = |system: &[MultivariatePolynomial<3, F>]| {
        signature_route(system, GREVLEX, &workers(1))
            .expect("graded")
            .features
            .infinity_witness
    };
    // x0^2 + x1*x2, x1^2 + x0 (x0 below the top degree), x2^2: e_0 zeros every top form.
    let system = [
        poly(&[([2, 0, 0], 1), ([0, 1, 1], 1)]),
        poly(&[([0, 2, 0], 1), ([1, 0, 0], 1)]),
        poly(&[([0, 0, 2], 1)]),
    ];
    assert_eq!(witness(&system[1..]), Some(0));
    assert_eq!(witness(&system), None);
    // x0*x1 + x2^2 and the linear x0 + x2: x1 has no pure power, x0 and x2 do.
    let system = [
        poly(&[([1, 1, 0], 1), ([0, 0, 2], 1)]),
        poly(&[([1, 0, 0], 1), ([0, 0, 1], 1)]),
    ];
    assert_eq!(witness(&system), Some(1));
    // A nonzero constant generator covers every variable.
    let system = [
        poly(&[([1, 1, 0], 1), ([0, 0, 2], 1)]),
        poly(&[([0, 0, 0], 5)]),
    ];
    assert_eq!(witness(&system), None);
    // Only x0 and x2 appear, and both have pure powers: the absent x1 is not a witness.
    let system = [
        poly(&[([2, 0, 0], 1)]),
        poly(&[([0, 0, 2], 1), ([1, 0, 1], 1)]),
    ];
    assert_eq!(witness(&system), None);
}

/// Every #961 row shape goes to the shipping F4 under graded-lex at every worker count and two
/// fields, with no cascade; grevlex never reports the `Order` reason.
#[test]
fn test_graded_lex_routes_to_shipping_on_every_961_row() {
    fn rule<const N: usize, F: FiniteField>(system: &[MultivariatePolynomial<N, F>]) {
        for count in [1, 4, 8, 16] {
            let options = workers(count);
            let grlex = signature_route(system, MonomialOrder::GradedLexicographic, &options)
                .expect("graded");
            assert_eq!(
                grlex.route,
                SignatureRoute::Shipping(ShippingReason::Order),
                "{N} variables, {count} workers"
            );
            assert_eq!(grlex.cascade, None);
            assert_eq!(grlex.workers, count);
            let grevlex = signature_route(system, GREVLEX, &options).expect("graded");
            assert_ne!(
                grevlex.route,
                SignatureRoute::Shipping(ShippingReason::Order)
            );
        }
    }
    fn rows<F: FiniteField>() {
        rule(&katsura::<9, F>());
        rule(&katsura::<10, F>());
        rule(&katsura::<11, F>());
        rule(&eco::<11, F>());
        rule(&eco::<12, F>());
        rule(&dense_quadratic::<10, F>(10));
        rule(&dense_quadratic::<11, F>(11));
    }
    rows::<Zp32003>();
    rows::<Goldilocks>();
}

/// Under graded-lex the entry point reports the `Order` route and returns the shipping F4's basis,
/// at one and four workers.
#[test]
fn test_graded_lex_entry_point_runs_the_shipping_f4() {
    let system = katsura::<7, Goldilocks>();
    let order = MonomialOrder::GradedLexicographic;
    for count in [1, 4] {
        let (result, report) = f4_signature_reported(&system, order, &workers(count));
        assert_eq!(
            report.route,
            SignatureRoute::Shipping(ShippingReason::Order)
        );
        assert_eq!(
            result.expect("finishes"),
            f4_with_options(&system, order, &workers(count))
                .expect("shipping F4 finishes")
                .0
        );
    }
}

/// The crossover leaves every other signature input where it was at 16 workers: Katsura-9 and -11
/// on either side of the band, cubics (Noon, Eco), and MQ11's dense shape.
#[test]
fn test_crossover_leaves_other_signature_inputs_alone() {
    let signature = SignatureRoute::Signature;
    assert_eq!(decide(&katsura::<9, Goldilocks>(), 16).route, signature);
    assert_eq!(decide(&katsura::<11, Zp32003>(), 16).route, signature);
    assert_eq!(decide(&noon::<8, Goldilocks>(), 16).route, signature);
    assert_eq!(decide(&eco::<12, Zp32003>(), 16).route, signature);
    let mq11 = dense_quadratic::<11, Goldilocks>(11);
    assert_eq!(decide(&mq11, 16).route, signature);
}

/// The dispatch reports term count, density, the caller's worker cap and the field's width.
#[test]
fn test_dispatch_reports_density_workers_and_field_width() {
    let dense = decide(&dense_quadratic::<6, Zp32003>(6), 3).features;
    assert_eq!(dense.terms, 6 * 28);
    assert_eq!(dense.monomials, 6 * 28);
    assert_eq!(dense.density(), 1.0);
    assert_eq!(dense.workers, 3);
    assert_eq!(dense.field_bits, 32);
    let sparse = decide(&katsura::<9, Goldilocks>(), 1).features;
    assert!(sparse.density() < 0.2, "{}", sparse.density());
    assert_eq!(sparse.field_bits, 64);
}

/// The team never exceeds the caller's cap; the cascade is parallel exactly when the signature
/// route has more than one worker, and absent on the shipping route.
#[test]
fn test_team_never_exceeds_max_workers() {
    fn check<const N: usize, F: FiniteField>(system: &[MultivariatePolynomial<N, F>]) {
        for count in 1..=16 {
            let report = decide(system, count);
            assert!(report.workers >= 1 && report.workers <= count);
            let cascade = match report.route {
                SignatureRoute::Signature if report.workers > 1 => Some(Cascade::Parallel),
                SignatureRoute::Signature => Some(Cascade::Serial),
                SignatureRoute::Shipping(_) => None,
            };
            assert_eq!(report.cascade, cascade, "{count} workers");
        }
    }
    check(&katsura::<4, Zp32003>());
    check(&katsura::<7, Goldilocks>());
    check(&katsura::<11, Zp32003>());
    check(&cyclic::<7, Goldilocks>());
    check(&dense_quadratic::<10, Zp32003>(10));
}

/// Signature inputs in fewer than `SIGNATURE_SMALL_TEAM_VARIABLES` variables run on at most
/// `SIGNATURE_SMALL_TEAM` workers; larger ones and the shipping route keep the caller's cap.
#[test]
fn test_small_signature_inputs_cap_the_team() {
    assert_eq!(
        (SIGNATURE_SMALL_TEAM_VARIABLES, SIGNATURE_SMALL_TEAM),
        (10, 8)
    );
    for count in [1, 2, 4, 8, 16] {
        let small = count.min(SIGNATURE_SMALL_TEAM);
        assert_eq!(decide(&katsura::<9, Goldilocks>(), count).workers, small);
        assert_eq!(decide(&noon::<7, Zp32003>(), count).workers, small);
        assert_eq!(decide(&katsura::<11, Zp32003>(), count).workers, count);
        assert_eq!(decide(&eco::<12, Goldilocks>(), count).workers, count);
        assert_eq!(decide(&cyclic::<7, Goldilocks>(), count).workers, count);
    }
}

/// On the crossover route the entry point returns the shipping F4's basis, which certifies.
#[test]
fn test_entry_point_equals_shipping_f4_on_the_crossover_route() {
    fn squares<F: FiniteField>() -> Vec<MultivariatePolynomial<10, F>> {
        (0..10)
            .map(|i| {
                // x_i^2, except x0*x2 in place of x0^2, so e_0 is a zero of every top form.
                let mut e = [0; 10];
                e[i] = 2;
                if i == 0 {
                    e = [1, 0, 1, 0, 0, 0, 0, 0, 0, 0];
                }
                let mut f = [0; 10];
                f[(i + 1) % 10] = 1;
                MultivariatePolynomial::new(&[
                    (crate::Monomial::new(&e), F::one()),
                    (crate::Monomial::new(&f), F::new(i as u64 + 1)),
                ])
            })
            .collect()
    }
    let system = squares::<Zp32003>();
    assert_eq!(
        decide(&system, 4).route,
        SignatureRoute::Shipping(ShippingReason::WorkerCrossover)
    );
    agrees(&system);
    agrees(&squares::<Goldilocks>());
}

/// #1186, Noon-10 in small: the caller's matrix limits are sized for conventional F4's matrices,
/// and the signature engine reads them in proportion to its own defaults. Noon-6's signature
/// matrices peak at 999 rows and 1,511 columns, conventional F4's at 3,817 and 4,432; at a limit of
/// 1,000 both engines stopped when the signature engine was held to it unscaled, as Noon-10 does at
/// the default 200,000.
#[test]
fn test_noon_completes_on_the_signature_route_under_a_conventional_matrix_limit() {
    let system = noon::<6, Zp2147483647>();
    let tight = F4Options {
        max_matrix_rows: 1_000,
        max_matrix_columns: 1_000,
        ..F4Options::default()
    };
    assert!(matches!(
        f4_with_options(&system, GREVLEX, &tight),
        Err(F4Error::TooManyRows { .. } | F4Error::TooManyColumns { .. })
    ));
    let (result, report) = f4_signature_reported(&system, GREVLEX, &tight);
    assert_eq!(report.route, SignatureRoute::Signature);
    let expected = f4_with_options(&system, GREVLEX, &F4Options::default())
        .unwrap()
        .0;
    assert_eq!(result.unwrap(), expected);
}

/// The signature engine's matrix limits scale with the caller's: the default maps to the
/// signature engine's own default, a tightened limit tightens it, and nothing overflows.
#[test]
fn test_signature_matrix_limits_scale_with_the_callers() {
    let defaults = SigF4Options::default();
    let at_default = signature_options::<Zp32003>(&F4Options::default(), 1);
    assert_eq!(at_default.max_matrix_rows, defaults.max_matrix_rows);
    assert_eq!(at_default.max_matrix_columns, defaults.max_matrix_columns);
    let tight = F4Options {
        max_matrix_rows: 1,
        max_matrix_columns: 20_000,
        ..F4Options::default()
    };
    let scaled = signature_options::<Zp32003>(&tight, 1);
    assert_eq!(scaled.max_matrix_rows, 10);
    assert_eq!(scaled.max_matrix_columns, 200_000);
    let wide = F4Options {
        max_matrix_rows: usize::MAX,
        ..F4Options::default()
    };
    assert_eq!(
        signature_options::<Zp32003>(&wide, 1).max_matrix_rows,
        usize::MAX
    );
}
