//! The system transformations, the bivariate resultant and the experiment records, reached only
//! through paths a downstream crate can name.

use rand::{prelude::StdRng, SeedableRng};
use zeebra::{
    fields::Zp2147483647,
    grobner::{
        record::{Environment, ExperimentRecord},
        resultant::bivariate_resultant,
        transform::{
            eliminate_affine, satisfies, solve_slice, specialize, SliceOutcome, Specialization,
            VariableOrder,
        },
        PlannedSolveOptions,
    },
    util::Json,
    FiniteField, MultivariatePolynomial, Polynomial, Zero,
};

type F = Zp2147483647;

fn parse<const N: usize>(text: &str, variables: [&str; N]) -> MultivariatePolynomial<N, F> {
    MultivariatePolynomial::parse(text, variables).expect("a polynomial")
}

/// Eliminating an affine variable and solving the rest reconstructs a point of the original system.
#[test]
fn test_affine_elimination_reconstructs_a_point_of_the_original() {
    let vars = ["x", "y", "z"];
    let system = vec![
        parse("x + y + z - 6", vars),
        parse("y^2 - 4", vars),
        parse("z - 3", vars),
    ];
    let (reduced, elimination) = eliminate_affine(&system);
    // Elimination runs from the last variable: z = 3, then y = 3 - x, leaving (3 - x)^2 - 4 in x.
    assert_eq!(elimination.kept(), vec![0]);
    assert_eq!(reduced.len(), 1);

    // x = 1 solves what is left; the eliminated coordinates are recovered from it.
    let point = elimination.reconstruct(&[F::new(1), F::zero(), F::zero()]);
    assert_eq!(point, [F::new(1), F::new(2), F::new(3)]);
    assert!(satisfies(&system, &point));
}

/// A specialization that meets the variety yields a witness, and one that misses it yields an
/// inconsistent slice, which is not a claim about the original system.
#[test]
fn test_slice_solving_distinguishes_a_witness_from_an_empty_slice() {
    let curve = vec![parse("x*y - 6", ["x", "y"]), parse("y - 3", ["x", "y"])];
    let options = PlannedSolveOptions::default();
    let mut rng = StdRng::seed_from_u64(7);

    let hit = Specialization::new(&[(0, F::new(2))]).expect("one fixed variable");
    let (outcome, _) = solve_slice(&curve, &hit, &options, &mut rng);
    match outcome.expect("solvable") {
        SliceOutcome::Witness(point) => assert!(satisfies(&curve, &point)),
        other => panic!("expected a witness, got {other:?}"),
    }

    let miss = Specialization::new(&[(0, F::new(5))]).expect("one fixed variable");
    assert!(specialize(&curve, &miss).iter().any(|p| !p.is_zero()));
    let (outcome, _) = solve_slice(&curve, &miss, &options, &mut rng);
    let outcome = outcome.expect("solvable");
    assert_eq!(outcome, SliceOutcome::SliceInconsistent);
    assert!(!outcome.is_evidence_about_the_original_system());
}

/// Relabelling variables and recovering a point is the identity on the original coordinates.
#[test]
fn test_a_variable_order_round_trips_a_point() {
    let system = vec![
        parse("x - 1", ["x", "y", "z"]),
        parse("y*z - 6", ["x", "y", "z"]),
    ];
    let order = VariableOrder::<3>::new("rotate", &[2, 0, 1]).expect("a bijection");
    let relabelled = order.apply(&system);
    let original = [F::new(1), F::new(2), F::new(3)];
    let moved = order.forward(&original);
    assert!(satisfies(&relabelled, &moved));
    assert_eq!(order.recover(&moved), original);
}

/// `Res_y(y - x, y - 2)` vanishes at `x = 2` and nowhere else.
#[test]
fn test_the_bivariate_resultant_eliminates_a_variable() {
    let f = parse("y - x", ["x", "y"]);
    let g = parse("y - 2", ["x", "y"]);
    let resultant = bivariate_resultant(&f, &g, 1).expect("y occurs in both");
    assert!(resultant.eval(&F::new(2)).is_zero());
    assert!(!resultant.eval(&F::new(3)).is_zero());
}

/// An experiment record serializes through `Json` and parses back with its keys intact.
#[test]
fn test_an_experiment_record_round_trips_through_json() {
    let record = ExperimentRecord::new("katsura-4", "baseline");
    let text = record.to_json().to_json();
    let parsed = Json::parse(&text).expect("valid JSON");
    assert_eq!(
        parsed.get("instance").and_then(Json::as_str),
        Some("katsura-4")
    );

    let environment = Environment::from_git();
    assert!(environment.comparable(&environment));
}
