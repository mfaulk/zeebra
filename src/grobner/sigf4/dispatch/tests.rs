use std::time::Duration;

use super::{
    f4_signature, f4_signature_reported, signature_route, ShippingReason, SignatureRoute,
    SIGNATURE_MIN_VARIABLES,
};
use crate::{
    fields::{PrimeFieldElement64, Zp32003},
    grobner::{
        benchmark_systems::{cyclic, eco, katsura, noon},
        f4::{certify_f4_output, f4_with_options, F4Error, F4Options, ParallelForward},
        sigf4::SigF4Error,
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
    signature_route(system, GREVLEX).expect("graded").0
}

fn workers(count: usize) -> F4Options {
    F4Options {
        parallel_forward: ParallelForward::Forced { workers: count },
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
                signature_route(system, order),
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
    let (_, features) = signature_route(&eco::<7, Goldilocks>(), GREVLEX).unwrap();
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
