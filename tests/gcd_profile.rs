#![cfg(feature = "research-work")]

use zeebra::{fields::Zp13, gcd_profile, FiniteField, GcdRoute, MultivariatePolynomial};

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

fn assert_no_multivariate_gcd(profile: gcd_profile::GcdProfile) {
    assert_eq!(profile, gcd_profile::GcdProfile::default());
}

// Every selectable multivariate GCD route activates the observer and returns the planted factor.
#[test]
fn solver_census_positive_controls() {
    let a = parse("y^2+x*y+y+x");
    let b = parse("y^2+x*y+2*y+2*x");
    assert_eq!(GcdRoute::default(), GcdRoute::SubresultantPrs);
    for route in [
        GcdRoute::PrimitivePrs,
        GcdRoute::SubresultantPrs,
        GcdRoute::Brown,
    ] {
        let (result, profile) = gcd_profile::measure(|| a.try_gcd_by(&b, route));
        assert_eq!(result.unwrap(), parse("y+x"));
        assert!(profile.gcd_calls > 0, "observer failed for {route:?}");
        println!(
            "CENSUS positive-control {route:?}: gcd_calls={}",
            profile.gcd_calls
        );
    }
}

// Completed corpus solves through direct lex and grevlex/FGLM make no multivariate GCD calls.
#[test]
fn solver_census_completed_corpus() {
    use rand::{prelude::StdRng, SeedableRng};
    use zeebra::{
        fields::Zp32003,
        grobner::{
            benchmark_systems::{cyclic, eco, katsura, noon, planted, reimer},
            solve_one_with_outcome, SolveOptions, SolveOutcome, SolveStrategy,
        },
        Zero,
    };

    let cases = [
        ("cyclic-3", cyclic::<3, Zp32003>()),
        ("katsura-3", katsura::<3, Zp32003>()),
        ("eco-3", eco::<3, Zp32003>()),
        ("noon-3", noon::<3, Zp32003>()),
        ("reimer-3", reimer::<3, Zp32003>()),
        (
            "planted-3",
            planted::<3, Zp32003>(&[Zp32003::new(3), Zp32003::new(5), Zp32003::new(7)]),
        ),
    ];
    for (name, system) in cases {
        for strategy in [SolveStrategy::DirectLexF4, SolveStrategy::GrevlexF4ThenFglm] {
            let mut rng = StdRng::seed_from_u64(0);
            let (result, profile) = gcd_profile::measure(|| {
                solve_one_with_outcome(&system, &mut rng, &SolveOptions::with_strategy(strategy))
            });
            let (outcome, _) = result.unwrap_or_else(|error| panic!("{name}: {error}"));
            if let Some(point) = outcome.point() {
                assert!(system
                    .iter()
                    .all(|polynomial| polynomial.eval(&point).is_zero()));
            }
            assert_no_multivariate_gcd(profile);
            let label = match outcome {
                SolveOutcome::Point(_) => "point-verified",
                SolveOutcome::NoBaseFieldPoint => "no-base-field-point",
                SolveOutcome::Inconsistent => "inconsistent",
            };
            println!("CENSUS {name} {strategy:?}: {label}; gcd_calls=0");
        }
    }
}

// Planner policies and resultant construction also avoid multivariate GCD, while returning checked answers.
#[test]
fn solver_census_planning_and_resultant() {
    use rand::{prelude::StdRng, SeedableRng};
    use zeebra::{
        grobner::{
            planning::{solve_one_planned, PlannedSolveOptions, SolvePolicy},
            resultant::bivariate_resultant,
        },
        Polynomial, Zero,
    };

    let system = [parse("x+y-3"), parse("x*y-2")];
    for policy in [
        SolvePolicy::ConservativeAuto,
        SolvePolicy::AutoWithFallback,
        SolvePolicy::ClassifyThenDirectLex,
    ] {
        let mut rng = StdRng::seed_from_u64(0);
        let ((result, _), profile) = gcd_profile::measure(|| {
            solve_one_planned(&system, &mut rng, &PlannedSolveOptions::with_policy(policy))
        });
        let point = result.unwrap().point().expect("the system has two points");
        assert!(system
            .iter()
            .all(|polynomial| polynomial.eval(&point).is_zero()));
        assert_no_multivariate_gcd(profile);
        println!("CENSUS planner {policy:?}: verified point; gcd_calls=0");
    }
    let (result, profile) = gcd_profile::measure(|| bivariate_resultant(&system[0], &system[1], 1));
    let resultant = result.unwrap();
    assert_eq!(resultant.degree(), 2);
    assert!(resultant.eval(&Zp13::new(1)).is_zero());
    assert!(resultant.eval(&Zp13::new(2)).is_zero());
    assert_no_multivariate_gcd(profile);
    println!("CENSUS resultant: degree=2, roots=1,2; gcd_calls=0");
}

// The frozen Anemoi CICO input reaches its declared F4 batch stop without multivariate GCD calls.
#[test]
fn solver_census_anemoi_prefix() {
    use zeebra::{
        fields::PrimeFieldElement64,
        grobner::{f4_reported, F4Error, F4Options},
        MonomialOrder,
    };
    type G = PrimeFieldElement64<65537>;
    let text = include_str!("../src/grobner/f4/test-data/anemoi17-cico-n5-fcico.system");
    let mut lines = text.lines();
    let variables: [&str; 10] = lines
        .next()
        .unwrap()
        .split(',')
        .collect::<Vec<_>>()
        .try_into()
        .unwrap();
    assert_eq!(lines.next(), Some("65537"));
    let equations = lines.collect::<Vec<_>>().join("\n");
    let system: Vec<MultivariatePolynomial<10, G>> = equations
        .split(',')
        .map(str::trim)
        .filter(|equation| !equation.is_empty())
        .map(|equation| MultivariatePolynomial::parse(equation, variables).unwrap())
        .collect();
    let options = F4Options {
        max_batches: Some(1),
        ..F4Options::default()
    };
    let ((result, statistics), profile) = gcd_profile::measure(|| {
        f4_reported(&system, MonomialOrder::GradedReverseLexicographic, &options)
    });
    assert!(matches!(result, Err(F4Error::TooManyBatches { limit: 1 })));
    assert_eq!(statistics.batches, 1);
    assert_no_multivariate_gcd(profile);
    println!("CENSUS anemoi17-cico-n5-fcico: batch-limit=1, completed-batches=1; gcd_calls=0");
}
