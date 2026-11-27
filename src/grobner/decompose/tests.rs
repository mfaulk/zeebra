use std::sync::atomic::AtomicBool;
use std::time::Duration;

use super::{f4_decomposed, DecomposeRoute};
use crate::{
    fields::{Zp2147483647, Zp31},
    grobner::{benchmark_systems::dense_blocks, buchberger, f4_with_options, F4Error, F4Options},
    poly::{BlockOrder, BlockOrderKind, MonomialOrder},
    FiniteField, MultivariatePolynomial,
};

fn parse<const N: usize, F: FiniteField>(
    vars: [&str; N],
    strings: &[&str],
) -> Vec<MultivariatePolynomial<N, F>> {
    strings
        .iter()
        .map(|s| MultivariatePolynomial::parse(s, vars).unwrap())
        .collect()
}

fn undecomposed<const N: usize, F: FiniteField>(
    system: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
) -> Vec<MultivariatePolynomial<N, F>> {
    f4_with_options(system, order, &F4Options::default())
        .unwrap()
        .0
}

fn decomposed<const N: usize, F: FiniteField>(
    system: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
) -> (Vec<MultivariatePolynomial<N, F>>, super::DecomposeReport) {
    let (basis, report) = f4_decomposed(system, order, &F4Options::default(), None);
    (basis.unwrap(), report)
}

fn block_order(arity: usize, split: usize) -> MonomialOrder {
    MonomialOrder::Block(
        BlockOrder::checked(
            arity,
            split,
            BlockOrderKind::GradedReverseLexicographic,
            BlockOrderKind::Lexicographic,
        )
        .unwrap(),
    )
}

#[test]
fn test_disjoint_blocks_match_undecomposed_and_reference() {
    let orders = [
        MonomialOrder::GradedReverseLexicographic,
        MonomialOrder::Lexicographic,
        block_order(5, 2),
    ];
    for seed in 0..3 {
        let system = dense_blocks::<5, Zp31>(&[2, 3], seed);
        for order in orders {
            let (basis, report) = decomposed(&system, order);
            assert_eq!(report.route, DecomposeRoute::Decomposed, "{order:?}");
            assert_eq!(report.components.len(), 2);
            assert_eq!(basis, undecomposed(&system, order), "seed {seed} {order:?}");
            assert_eq!(basis, buchberger(&system, order), "seed {seed}");
        }
    }
}

#[test]
fn test_three_unequal_blocks_over_a_wide_prime() {
    let system = dense_blocks::<6, Zp2147483647>(&[1, 2, 3], 7);
    for order in [
        MonomialOrder::GradedReverseLexicographic,
        MonomialOrder::Lexicographic,
        block_order(6, 3),
    ] {
        let (basis, report) = decomposed(&system, order);
        assert_eq!(report.components.len(), 3);
        assert_eq!(basis, undecomposed(&system, order), "{order:?}");
    }
}

#[test]
fn test_positive_dimensional_components() {
    // One generator per block: neither component is zero-dimensional.
    let system = parse::<4, Zp31>(["x", "y", "z", "w"], &["x^2*y - y + 3", "z*w^2 - z^2"]);
    for order in [
        MonomialOrder::GradedReverseLexicographic,
        MonomialOrder::Lexicographic,
        block_order(4, 1),
    ] {
        let (basis, report) = decomposed(&system, order);
        assert_eq!(report.route, DecomposeRoute::Decomposed);
        assert_eq!(basis, undecomposed(&system, order), "{order:?}");
    }
}

#[test]
fn test_coupling_without_a_mixed_monomial_does_not_split() {
    // x^2 + y^2 - 1 joins x and y although no monomial contains both.
    let system = parse::<3, Zp31>(["x", "y", "z"], &["x^2 + y^2 - 1", "x^3 - 2", "y*x - z"]);
    let (basis, report) = decomposed(&system, MonomialOrder::GradedReverseLexicographic);
    assert_eq!(report.route, DecomposeRoute::Undivided);
    assert_eq!(report.components.len(), 1);
    assert_eq!(
        basis,
        undecomposed(&system, MonomialOrder::GradedReverseLexicographic)
    );

    let system = parse::<2, Zp31>(["x", "y"], &["x^2 + y^2 - 1", "x^3 - y"]);
    let (_, report) = decomposed(&system, MonomialOrder::Lexicographic);
    assert_eq!(report.route, DecomposeRoute::Undivided);
}

#[test]
fn test_coupled_blocks_do_not_split() {
    let mut system = dense_blocks::<4, Zp31>(&[2, 2], 3);
    // Variables 0 and 1 belong to different blocks; one coupling term joins them.
    system.push(MultivariatePolynomial::parse("x0*x1 + 1", ["x0", "x1", "x2", "x3"]).unwrap());
    let (basis, report) = decomposed(&system, MonomialOrder::GradedReverseLexicographic);
    assert_eq!(report.route, DecomposeRoute::Undivided);
    assert_eq!(
        basis,
        undecomposed(&system, MonomialOrder::GradedReverseLexicographic)
    );
}

#[test]
fn test_unit_component_gives_the_unit_ideal() {
    let system = parse::<4, Zp31>(
        ["x", "y", "z", "w"],
        &["x^2 - 1", "x - 2", "z*w - 1", "z^2 + w"],
    );
    let (basis, report) = decomposed(&system, MonomialOrder::GradedReverseLexicographic);
    assert_eq!(basis, vec![MultivariatePolynomial::one()]);
    assert_eq!(report.route, DecomposeRoute::Unit);
    assert_eq!(
        basis,
        undecomposed(&system, MonomialOrder::GradedReverseLexicographic)
    );
}

#[test]
fn test_nonzero_constant_generator_is_the_unit_ideal() {
    let system = parse::<3, Zp31>(["x", "y", "z"], &["x^2 - 1", "5", "z - 1"]);
    let (basis, report) = decomposed(&system, MonomialOrder::Lexicographic);
    assert_eq!(basis, vec![MultivariatePolynomial::one()]);
    assert_eq!(report.route, DecomposeRoute::Unit);
    assert!(report.components.is_empty());
    assert_eq!(basis, undecomposed(&system, MonomialOrder::Lexicographic));
}

#[test]
fn test_zero_generators_and_unused_variables() {
    let vars = ["x", "y", "z", "w", "u"];
    let system = parse::<5, Zp31>(vars, &["0", "x^2 - 3", "0", "z^3 - z + 1"]);
    let (basis, report) = decomposed(&system, MonomialOrder::GradedReverseLexicographic);
    assert_eq!(report.route, DecomposeRoute::Decomposed);
    assert_eq!(report.unused_variables, vec![1, 3, 4]);
    assert_eq!(report.components.len(), 2);
    assert_eq!(report.components[0].generators, vec![1]);
    assert_eq!(report.components[1].generators, vec![3]);
    assert_eq!(
        basis,
        undecomposed(&system, MonomialOrder::GradedReverseLexicographic)
    );

    let zero = parse::<2, Zp31>(["x", "y"], &["0", "0"]);
    let (basis, report) = decomposed(&zero, MonomialOrder::Lexicographic);
    assert!(basis.is_empty());
    assert_eq!(report.route, DecomposeRoute::Undivided);
    let (basis, _) = decomposed::<2, Zp31>(&[], MonomialOrder::Lexicographic);
    assert!(basis.is_empty());
}

#[test]
fn test_single_component_is_the_plain_route() {
    let system = parse::<3, Zp31>(["x", "y", "z"], &["x*y - z", "y*z - x", "x*z - y^2 + 1"]);
    let order = MonomialOrder::GradedReverseLexicographic;
    let (basis, report) = decomposed(&system, order);
    assert_eq!(report.route, DecomposeRoute::Undivided);
    let (plain, statistics) = f4_with_options(&system, order, &F4Options::default()).unwrap();
    assert_eq!(basis, plain);
    // One run, the caller's: the report's statistics are that run's.
    assert_eq!(report.components[0].statistics.batches, statistics.batches);
    assert_eq!(report.fallback, None);
}

#[test]
fn test_components_shrink_the_matrices() {
    let system = dense_blocks::<6, Zp31>(&[3, 3], 11);
    let order = MonomialOrder::GradedReverseLexicographic;
    let (_, whole) = f4_with_options(&system, order, &F4Options::default()).unwrap();
    let (_, report) = decomposed(&system, order);
    let widest = report
        .components
        .iter()
        .map(|c| c.statistics.max_matrix_columns)
        .max()
        .unwrap();
    assert!(
        widest < whole.max_matrix_columns,
        "{widest} >= {}",
        whole.max_matrix_columns
    );
}

#[test]
fn test_batches_are_one_budget_across_components() {
    let system = dense_blocks::<6, Zp31>(&[3, 3], 5);
    let order = MonomialOrder::GradedReverseLexicographic;
    let (_, report) = decomposed(&system, order);
    let per_component: Vec<usize> = report
        .components
        .iter()
        .map(|c| c.statistics.batches)
        .collect();
    let total: usize = per_component.iter().sum();
    assert!(per_component.iter().all(|&b| b > 0));

    // Enough for either component alone but not both: the second component sees what is left.
    let largest = *per_component.iter().max().unwrap();
    assert!(largest < total);
    let options = F4Options {
        max_batches: Some(largest),
        ..F4Options::default()
    };
    let (basis, report) = f4_decomposed(&system, order, &options, None);
    // A batch refusal is a resource refusal, so the fallback runs, on what remains, and fails.
    assert!(
        matches!(basis, Err(F4Error::TooManyBatches { .. })),
        "{basis:?}"
    );
    let DecomposeRoute::FellBack { refusal, .. } = report.route else {
        panic!("{:?}", report.route)
    };
    assert!(matches!(refusal, F4Error::TooManyBatches { .. }));
    let spent: usize = report
        .components
        .iter()
        .map(|c| c.statistics.batches)
        .sum::<usize>()
        + report.fallback.as_ref().map_or(0, |s| s.batches);
    assert!(spent <= largest, "spent {spent} of {largest}");

    let options = F4Options {
        max_batches: Some(total),
        ..F4Options::default()
    };
    let (basis, _) = f4_decomposed(&system, order, &options, None);
    assert_eq!(basis.unwrap(), undecomposed(&system, order));
}

#[test]
fn test_basis_element_budget_is_shared() {
    let system = dense_blocks::<6, Zp31>(&[3, 3], 5);
    let order = MonomialOrder::GradedReverseLexicographic;
    let (_, report) = decomposed(&system, order);
    let added: Vec<usize> = report
        .components
        .iter()
        .map(|c| c.statistics.elements_added)
        .collect();
    let largest = *added.iter().max().unwrap();
    // The generators count against the limit too, so allow one component's whole demand.
    let limit = largest + 3;
    assert!(limit < added.iter().sum::<usize>() + 3);
    let options = F4Options {
        max_basis_elements: Some(limit),
        ..F4Options::default()
    };
    let (basis, _) = f4_decomposed(&system, order, &options, None);
    assert!(
        matches!(basis, Err(F4Error::TooManyBasisElements { .. })),
        "{basis:?}"
    );
}

#[test]
fn test_retained_outputs_are_charged_to_the_byte_budget() {
    // Interleaved dealing puts variable 0 in the 2-block, so it is component 0 and the 4-block,
    // with the larger matrices, runs second while the first block's basis is retained.
    let system = dense_blocks::<6, Zp31>(&[2, 4], 5);
    let order = MonomialOrder::GradedReverseLexicographic;
    let (_, report) = decomposed(&system, order);
    let entry = F4Options::bytes_per_entry::<Zp31>();
    let need: Vec<usize> = report
        .components
        .iter()
        .map(|c| c.statistics.max_live_nonzeros * entry)
        .collect();
    assert!(need[0] < need[1], "{need:?}");
    assert!(report.peak_retained_bytes > 0);

    // Enough for the second component alone, not with the first one's output still held.
    let options = F4Options {
        max_live_bytes: need[1],
        ..F4Options::default()
    };
    let (basis, report) = f4_decomposed(&system, order, &options, None);
    match report.route {
        DecomposeRoute::FellBack { after, refusal } => {
            assert_eq!(after, 1);
            assert!(
                matches!(refusal, F4Error::TooManyLiveBytes { .. }),
                "{refusal:?}"
            );
        }
        other => panic!("{other:?}"),
    }
    // The fallback holds nothing retained, so it runs on the caller's whole byte allowance.
    let direct = f4_with_options(&system, order, &options).map(|(b, _)| b);
    assert_eq!(basis, direct);
}

#[test]
fn test_cancellation_is_a_caller_stop_without_fallback() {
    let system = dense_blocks::<6, Zp31>(&[3, 3], 5);
    let cancel = AtomicBool::new(true);
    let (basis, report) = f4_decomposed(
        &system,
        MonomialOrder::GradedReverseLexicographic,
        &F4Options::default(),
        Some(&cancel),
    );
    assert_eq!(basis, Err(F4Error::StoppedByObserver));
    assert_eq!(report.fallback, None);
    assert!(!matches!(report.route, DecomposeRoute::FellBack { .. }));
}

#[test]
fn test_spent_wall_time_is_not_refunded() {
    let system = dense_blocks::<6, Zp31>(&[3, 3], 5);
    let options = F4Options {
        max_wall_time: Some(Duration::ZERO),
        ..F4Options::default()
    };
    let (basis, report) = f4_decomposed(
        &system,
        MonomialOrder::GradedReverseLexicographic,
        &options,
        None,
    );
    let error = basis.unwrap_err();
    assert_eq!(
        error.stop_kind(),
        crate::grobner::StopKind::Time,
        "{error:?}"
    );
    assert_eq!(report.fallback, None);
}

#[test]
fn test_adaptive_engine_matches() {
    let system = dense_blocks::<6, Zp31>(&[2, 4], 9);
    let order = MonomialOrder::GradedReverseLexicographic;
    let options = F4Options {
        graded_engine: crate::grobner::GradedEngine::Adaptive,
        ..F4Options::default()
    };
    let (basis, report) = f4_decomposed(&system, order, &options, None);
    assert_eq!(report.route, DecomposeRoute::Decomposed);
    assert_eq!(basis.unwrap(), undecomposed(&system, order));
}
