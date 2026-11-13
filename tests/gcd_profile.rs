#![cfg(feature = "research-work")]

use zeebra::{fields::Zp13, gcd_profile, GcdRoute, MultivariatePolynomial};

type Poly = MultivariatePolynomial<2, Zp13>;
fn parse(text: &str) -> Poly {
    Poly::parse(text, ["x", "y"]).unwrap()
}

// Completed pseudo-remainders and normalized PRS entries retain distinct coefficient degrees.
#[test]
fn raw_growth_is_separate_from_prs_entries() {
    let a = parse("y^2+x*y+x^3");
    let b = parse("y+x^2");
    for route in [GcdRoute::PrimitivePrs, GcdRoute::SubresultantPrs] {
        let (actual, profile) = gcd_profile::measure(|| a.gcd_by(&b, route));
        assert_eq!(actual, a.gcd_by(&b, route));
        assert_eq!(profile.prs_entries.max_terms, 3);
        assert_eq!(profile.prs_entries.max_coefficient_degree, 3);
        assert_eq!(profile.raw_remainders.max_coefficient_degree, 4);
        assert!(profile.content_calls > 0);
        assert!(profile.max_recursion_depth > 1);
        assert_eq!(profile.subresultant_bound_violations, 0);
    }
}

// Brown reports image and interpolant sizes without disguising its cleanup PRS as interpolation.
#[test]
fn brown_records_its_own_phases() {
    let a = parse("y^2+x*y+y+x");
    let b = parse("y^2+x*y+2*y+2*x");
    let (result, profile) = gcd_profile::measure(|| a.try_gcd_by(&b, GcdRoute::Brown));
    assert_eq!(result.unwrap(), parse("y+x"));
    assert!(profile.brown_images.observations > 0);
    assert!(profile.brown_interpolants.observations > 0);
    assert_eq!(profile.brown_interpolants.max_terms, 2);
    assert_eq!(profile.brown_interpolants.max_coefficient_degree, 1);
}

// A panic releases the scope, so later captures contain no counters from interrupted work.
#[test]
fn panic_cleans_up_and_nested_capture_is_refused() {
    let failed = std::panic::catch_unwind(|| gcd_profile::measure(|| gcd_profile::measure(|| ())));
    assert!(failed.is_err());
    let (_, profile) = gcd_profile::measure(|| parse("x").gcd(&parse("1")));
    assert!(profile.gcd_calls > 0);
    let (_, empty) = gcd_profile::measure(|| ());
    assert_eq!(empty.gcd_calls, 0);
    assert_eq!(empty.prs_entries.observations, 0);
}
