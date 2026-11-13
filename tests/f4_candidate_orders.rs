use zeebra::{
    fields::{Bn254Fr, Gf256, Zp13, Zp18446744069414584321, Zp2, Zp32003},
    grobner::{
        buchberger,
        f4::{
            build_batch_matrix, reduce_batch,
            structured::{eliminate_to, BlockPlan, RowForm},
            symbolic::{MonicBasis, ReducerCache},
        },
        f4_with_options,
        pairs::CriticalPair,
        F4Options, ReductionStrategy,
    },
    linalg::Backend,
    BlockOrder, BlockOrderKind, FiniteField, MonomialOrder, MultivariatePolynomial,
    WeightedTieBreak,
};

fn orders() -> Vec<MonomialOrder> {
    use BlockOrderKind::{GradedLexicographic, GradedReverseLexicographic, Lexicographic};
    let mut orders = Vec::new();
    for split in [1, 2] {
        for prefix in [
            Lexicographic,
            GradedLexicographic,
            GradedReverseLexicographic,
        ] {
            for suffix in [
                Lexicographic,
                GradedLexicographic,
                GradedReverseLexicographic,
            ] {
                orders.push(MonomialOrder::Block(
                    BlockOrder::checked(3, split, prefix, suffix).unwrap(),
                ));
            }
        }
    }
    for tie in [
        WeightedTieBreak::Lexicographic,
        WeightedTieBreak::ReverseLexicographic,
        WeightedTieBreak::LastVariableFirst,
    ] {
        orders.push(MonomialOrder::weighted(&[1, 2, 3], tie).unwrap());
    }
    orders
}

fn check<F: FiniteField>() {
    for order in orders() {
        for backend in [Backend::Sparse, Backend::Dense, Backend::Adaptive] {
            for reduction in [
                ReductionStrategy::Structured,
                ReductionStrategy::Unstructured,
            ] {
                for texts in [
                    vec!["x^2 + y", "x^2 + z", "x^2 + y + z"],
                    vec!["x^3 - y", "x^2 - z", "x - y*z", "y^2 - 1"],
                ] {
                    let system: Vec<_> = texts
                        .iter()
                        .map(|s| MultivariatePolynomial::<3, F>::parse(s, ["x", "y", "z"]).unwrap())
                        .collect();
                    let basis = MonicBasis::new(&system, order);
                    let pairs: Vec<_> = (0..system.len())
                        .flat_map(|left| {
                            let system = &system;
                            (left + 1..system.len())
                                .map(move |right| CriticalPair::new(system, left, right, order))
                        })
                        .collect();
                    let options = F4Options {
                        elimination: backend,
                        reduction,
                        ..Default::default()
                    };
                    let actual = reduce_batch(&basis, &pairs, order, &options).unwrap();
                    let mut full = build_batch_matrix(
                        &basis,
                        &pairs,
                        order,
                        &options,
                        &mut ReducerCache::disabled(),
                    )
                    .unwrap();
                    let plan = if reduction == ReductionStrategy::Structured {
                        BlockPlan::ReducersFirstBlock
                    } else {
                        BlockPlan::Baseline
                    };
                    eliminate_to(
                        plan,
                        RowForm::Reduced,
                        backend,
                        &mut full.matrix,
                        usize::MAX,
                    )
                    .unwrap();
                    let mut expected: Vec<_> = (0..full.matrix.num_rows())
                        .filter_map(|index| {
                            let column = full.matrix.matrix().row(index).leading_column()?;
                            (!full
                                .preprocessed
                                .leading_monomials
                                .contains(&full.matrix.columns()[column]))
                            .then(|| full.matrix.row_polynomial(index))
                        })
                        .collect();
                    expected.sort_by(|a, b| {
                        order.cmp(&b.leading_monomial(order), &a.leading_monomial(order))
                    });
                    assert_eq!(actual.candidates, expected);
                    assert_eq!(
                        actual.statistics.candidate_reduction.targets,
                        expected.len()
                    );
                    let (complete, _) = f4_with_options(&system, order, &options).unwrap();
                    assert_eq!(complete, buchberger(&system, order));
                }
            }
        }
    }
}

// Candidate rows and complete reduced bases match full RREF and Buchberger for weighted and two-block orders.
#[test]
fn candidate_contract_preserves_parameterized_orders() {
    check::<Zp13>();
    check::<Zp32003>();
    check::<Zp2>();
    check::<Gf256>();
    check::<Zp18446744069414584321>();
    check::<Bn254Fr>();
}
