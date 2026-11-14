#![cfg(feature = "research-work")]

use zeebra::{
    fields::{Bn254Fr, Gf256, Zp13, Zp18446744069414584321, Zp2, Zp2147483647, Zp32003},
    grobner::{
        f4::{
            live_symbolic::{self, Policy},
            symbolic::{
                symbolic_preprocessing, symbolic_preprocessing_within, MonicBasis, RowKind,
            },
        },
        pairs::CriticalPair,
        F4Options,
    },
    BlockOrder, BlockOrderKind, FiniteField, MonomialOrder, MultivariatePolynomial,
    WeightedTieBreak,
};

fn parse<F: FiniteField>(s: &str) -> MultivariatePolynomial<3, F> {
    MultivariatePolynomial::parse(s, ["x", "y", "z"]).unwrap()
}

// Duplicate seed identities are removed while all pair leads and closure columns remain covered.
#[test]
fn duplicate_seeds_preserve_span_and_covered_leads() {
    let order = MonomialOrder::GradedReverseLexicographic;
    let input = [parse::<Zp13>("x^2 + y"), parse("x*y + z"), parse("y^2 + x")];
    let basis = MonicBasis::new(&input, order);
    let a = CriticalPair::new(&input, 0, 1, order);
    let b = CriticalPair::new(&input, 0, 2, order);
    let pairs = [a.clone(), a, b];
    let original = symbolic_preprocessing(&basis, &pairs);
    let selected = live_symbolic::with_policy(
        Policy {
            order_initial: false,
            deduplicate: true,
        },
        input.len(),
        || symbolic_preprocessing(&basis, &pairs),
    );
    assert!(selected.rows.len() < original.rows.len());
    assert_eq!(selected.leading_monomials, original.leading_monomials);
    assert_eq!(selected.monomials, original.monomials);
    for row in &original.rows {
        assert!(selected
            .rows
            .iter()
            .any(|r| r.basis_index == row.basis_index && r.multiplier == row.multiplier));
    }
    assert!(
        selected
            .rows
            .iter()
            .filter(|r| matches!(r.kind, RowKind::PairComponent { .. }))
            .count()
            < 2 * pairs.len()
    );
}

// Deduplicated preprocessing refuses at its own row limit and does not leak policy into a retry.
#[test]
fn exact_row_budget_and_scope_reuse() {
    let order = MonomialOrder::Lexicographic;
    let input = [parse::<Zp13>("x^2 + y"), parse("x*y + z"), parse("y^2 + x")];
    let basis = MonicBasis::new(&input, order);
    let pair = CriticalPair::new(&input, 0, 1, order);
    let pairs = [pair.clone(), pair];
    let original = symbolic_preprocessing(&basis, &pairs);
    live_symbolic::with_policy(
        Policy {
            order_initial: true,
            deduplicate: true,
        },
        input.len(),
        || {
            let needed = symbolic_preprocessing(&basis, &pairs).rows.len();
            assert!(symbolic_preprocessing_within(&basis, &pairs, needed).is_ok());
            assert!(symbolic_preprocessing_within(&basis, &pairs, needed - 1).is_err());
            assert!(symbolic_preprocessing_within(&basis, &[], 0)
                .unwrap()
                .rows
                .is_empty());
        },
    );
    assert_eq!(symbolic_preprocessing(&basis, &pairs), original);
    let _ = std::panic::catch_unwind(|| {
        live_symbolic::with_policy(
            Policy {
                order_initial: true,
                deduplicate: true,
            },
            1,
            || panic!("scope unwind"),
        )
    });
    assert_eq!(symbolic_preprocessing(&basis, &pairs), original);
}

fn complete<F: FiniteField>() {
    for order in [
        MonomialOrder::Lexicographic,
        MonomialOrder::GradedLexicographic,
        MonomialOrder::GradedReverseLexicographic,
        MonomialOrder::weighted(&[1, 2, 3], WeightedTieBreak::Lexicographic).unwrap(),
        MonomialOrder::Block(
            BlockOrder::checked(
                3,
                1,
                BlockOrderKind::Lexicographic,
                BlockOrderKind::GradedReverseLexicographic,
            )
            .unwrap(),
        ),
    ] {
        let mut input = vec![
            parse::<F>("x^2 + y + 1"),
            parse("x*y + z"),
            parse("y^2 + z + 1"),
            parse("z^2 + x"),
        ];
        input.push(input[0].scale(&(F::ONE + F::ONE)));
        input.push(parse("0"));
        let expected = zeebra::grobner::buchberger(&input, order);
        for order_initial in [false, true] {
            for deduplicate in [false, true] {
                let actual = live_symbolic::with_policy(
                    Policy {
                        order_initial,
                        deduplicate,
                    },
                    input.len(),
                    || {
                        zeebra::grobner::f4_with_options(&input, order, &F4Options::default())
                            .unwrap()
                            .0
                    },
                );
                assert_eq!(actual, expected);
            }
        }
    }
}

// All four live policies preserve complete reduced bases with zero/proportional inputs across field widths.
#[test]
fn complete_bases_match_independent_buchberger() {
    complete::<Zp13>();
    complete::<Zp32003>();
    complete::<Zp2147483647>();
    complete::<Zp2>();
    complete::<Gf256>();
    complete::<Zp18446744069414584321>();
    complete::<Bn254Fr>();
}

// Reducer ordering moves only the initial search prefix and never reorders pair seeds or appended elements.
#[test]
fn ordering_preserves_pair_indices_and_appended_prefix_boundary() {
    let order = MonomialOrder::Lexicographic;
    let input = [
        parse::<Zp13>("x^3 + y"),
        parse("x^2 + z"),
        parse("x + 1"),
        parse("x^5 + x^4 + y"),
        parse("x^6 + z"),
    ];
    let basis = MonicBasis::new(&input, order);
    let pairs = [CriticalPair::new(&input, 3, 4, order)];
    let original = symbolic_preprocessing(&basis, &pairs);
    let selected = live_symbolic::with_policy(
        Policy {
            order_initial: true,
            deduplicate: false,
        },
        2,
        || symbolic_preprocessing(&basis, &pairs),
    );
    assert_eq!(&original.rows[..2], &selected.rows[..2]);
    let lead = zeebra::Monomial::new(&[5, 0, 0]);
    let selected_row = selected
        .rows
        .iter()
        .find(|row| {
            row.kind == RowKind::Reducer
                && basis.element(row.basis_index).leading_monomial * row.multiplier == lead
        })
        .unwrap();
    let original_row = original
        .rows
        .iter()
        .find(|row| {
            row.kind == RowKind::Reducer
                && basis.element(row.basis_index).leading_monomial * row.multiplier == lead
        })
        .unwrap();
    assert_eq!(original_row.basis_index, 0);
    assert_eq!(selected_row.basis_index, 1);
}

// Equal leading monomials and proportional generators are never mistaken for a duplicate seed identity.
#[test]
fn distinct_seed_identities_with_equal_leads_are_retained() {
    let order = MonomialOrder::GradedReverseLexicographic;
    let input = [
        parse::<Zp13>("2*x^2 + 2*y"),
        parse("x^2 + y"),
        parse("x^2 + z"),
    ];
    let basis = MonicBasis::new(&input, order);
    let pairs = [
        CriticalPair::new(&input, 0, 1, order),
        CriticalPair::new(&input, 1, 2, order),
    ];
    let selected = live_symbolic::with_policy(
        Policy {
            order_initial: false,
            deduplicate: true,
        },
        input.len(),
        || symbolic_preprocessing(&basis, &pairs),
    );
    let seeds: Vec<_> = selected
        .rows
        .iter()
        .filter(|row| matches!(row.kind, RowKind::PairComponent { .. }))
        .map(|row| row.basis_index)
        .collect();
    assert_eq!(seeds, [0, 1, 2]);
}

// Live F4 freezes the normalized distinct input size before appended basis elements can enter the search.
#[test]
fn normalized_initial_prefix_is_frozen() {
    let order = MonomialOrder::GradedReverseLexicographic;
    let a = parse::<Zp13>("x^2 + y + 1");
    let input = [
        a.clone(),
        a.scale(&Zp13::new(2)),
        parse("0"),
        parse("x*y + z"),
        parse("y^2 + x"),
    ];
    let ((_, stats), report) = live_symbolic::observe(
        Policy {
            order_initial: true,
            deduplicate: true,
        },
        input.len(),
        || zeebra::grobner::f4_with_options(&input, order, &F4Options::default()).unwrap(),
    );
    assert_eq!(report.initial_generators, 3);
    assert!(stats.elements_added > 0);
    assert!(report.batches > 1);
}
