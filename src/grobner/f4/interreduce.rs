//! Final interreduction as one Macaulay matrix, rather than as one division per basis element.
//!
//! # Why this exists
//!
//! `docs/research/groebner-jl-gap.md` §3 measured Zeebra's final interreduction at **13 871x**
//! Groebner.jl's on `mq-random-10`, where the next worst stage is 97.1x. A spread of 8x among the
//! other three stages is an implementation constant; a 1 400x outlier among them is not an
//! implementation of the same thing. §4 says what the difference is:
//!
//! > It is not a faster interreduction. **It is linear algebra where Zeebra does division.**
//!
//! Groebner.jl's `f4_autoreduce!` builds one matrix whose rows are the non-redundant basis
//! elements, lets symbolic preprocessing supply the reducers those rows need, marks every column as
//! an unknown pivot so that all of them are eliminated against, and reduces once —
//! **250 x 604, 1.74 ms, 2.0% of its whole run.** Zeebra's [`reduce_grobner_basis_until`] instead
//! performs one `normal_form` per element, each with its own intermediate growth, and spends four
//! fifths of the computation there.
//!
//! Every component of the replacement already existed: [`MacaulayMatrix`] builds the matrix,
//! [`symbolic`](super::symbolic) finds the reducers, [`reduced_row_echelon`] eliminates, and
//! `minimize_grobner_basis` produces the row set. What was missing was the assembly.
//!
//! # Why the answer cannot change
//!
//! `buchberger.rs` already writes the argument out: a reduced Gröbner basis is **determined by its
//! leading monomials**, so the route to it cannot change it. Concretely, for a minimized basis
//! `g_1..g_n`:
//!
//! - The seed rows have distinct leading monomials, so each is a pivot —
//!   [`interreduction_rows`](super::symbolic::interreduction_rows) proves this from minimality.
//! - The closure gives every *reducible* monomial in the matrix a row that leads with it, so the
//!   pivot columns are exactly the reducible monomials.
//! - Reduced row echelon form leaves one nonzero per pivot column. So the row led by `lm(g_i)` has
//!   no monomial divisible by any `lm(g_j)` — which is the defining property of the reduced basis
//!   element with that leading monomial, and there is only one such polynomial.
//!
//! So this is a different computation of the same unique object, and the test that matters is exact
//! equality against the division route rather than a tolerance.

use crate::{
    grobner::f4::{
        macaulay::{BuildBudgetExceeded, MacaulayMatrix},
        symbolic::{interreduction_rows, MonicBasis, ReducerCache, RowBudgetExceeded},
        ReducerSelection,
    },
    linalg::sparse::reduced_row_echelon,
    poly::MonomialOrder,
    FiniteField, Monomial, MultivariatePolynomial,
};

/// Why a matrix interreduction refused to run.
///
/// The stage is not exempt from the budgets the batch loop obeys. A basis of a few hundred
/// elements whose closure is wide can need a matrix as large as any batch's, and a stage that
/// ignored the budgets would be a way to exceed them by waiting until the end of the computation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum MatrixInterreductionRefused {
    /// The closure needed more rows than allowed.
    Rows { limit: usize },
    /// The matrix needed more distinct monomials than allowed.
    Columns { limit: usize },
    /// The matrix needed more nonzero entries than allowed.
    Nonzeros { nonzeros: usize },
}

/// What a matrix interreduction did, for attribution against the division route.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub(crate) struct MatrixInterreductionReport {
    /// Rows in the matrix: the basis elements plus the reducer multiples the closure added.
    pub rows: usize,
    /// Columns, i.e. distinct monomials in the closure. Groebner.jl's was 604 on `mq-random-10`.
    pub columns: usize,
    /// Nonzero entries at construction.
    pub nonzeros: usize,
    /// Elements in the minimized basis, which is how many rows were seeds rather than reducers.
    pub elements: usize,
}

/// Interreduce a minimized basis through one Macaulay matrix.
///
/// `minimal` must be **minimized** — monic, deduplicated, and with no leading monomial dividing
/// another — which is what `minimize_grobner_basis` produces and what the pivot argument in the
/// module documentation requires. It is also expected sorted ascending by leading monomial, as the
/// division route sorts it; the output is returned descending, matching
/// [`reduce_grobner_basis_until`]'s canonical order.
///
/// # Errors
/// [`MatrixInterreductionRefused`] if any budget would be exceeded. Nothing is partially written:
/// the budgets are checked while the closure and the matrix are built, not after.
pub(crate) fn interreduce_by_matrix<const N: usize, F: FiniteField>(
    minimal: Vec<MultivariatePolynomial<N, F>>,
    order: MonomialOrder,
    max_rows: usize,
    max_columns: usize,
    max_nonzeros: usize,
) -> Result<
    (
        Vec<MultivariatePolynomial<N, F>>,
        MatrixInterreductionReport,
    ),
    MatrixInterreductionRefused,
> {
    // One element is already reduced against the empty rest of the basis, and zero elements have
    // nothing to reduce. Neither needs a matrix, and `MonicBasis::new` would reject a zero
    // element anyway.
    if minimal.len() < 2 {
        let report = MatrixInterreductionReport {
            elements: minimal.len(),
            ..Default::default()
        };
        return Ok((minimal, report));
    }

    let basis = MonicBasis::new(&minimal, order);
    let elements = basis.len();

    // The leading monomials of the seed rows, which is what the extraction below selects on. Taken
    // from the basis rather than recomputed from the polynomials so that it agrees with the set
    // `interreduction_rows` seeded `covered` with, by construction.
    let leading: Vec<Monomial<N>> = (0..elements)
        .map(|index| basis.element(index).leading_monomial)
        .collect();

    let preprocessed = interreduction_rows(
        &basis,
        max_rows,
        ReducerSelection::FirstApplicable,
        &mut ReducerCache::disabled(),
    )
    .map_err(|RowBudgetExceeded { limit }| MatrixInterreductionRefused::Rows { limit })?;

    let mut matrix =
        MacaulayMatrix::build_within(&basis, &preprocessed, order, max_columns, max_nonzeros)
            .map_err(|exceeded| match exceeded {
                BuildBudgetExceeded::Columns { limit } => {
                    MatrixInterreductionRefused::Columns { limit }
                }
                BuildBudgetExceeded::Nonzeros { nonzeros, .. } => {
                    MatrixInterreductionRefused::Nonzeros { nonzeros }
                }
            })?;

    let report = MatrixInterreductionReport {
        rows: matrix.num_rows(),
        columns: matrix.num_columns(),
        nonzeros: matrix.matrix().nonzeros(),
        elements,
    };

    // **Reduced** row echelon and not plain echelon, and this is the whole point. Plain echelon
    // leaves a pivot row carrying other pivots' columns, which is a basis element still divisible
    // by another's leading monomial — i.e. not interreduced. The back-substitution pass is what
    // performs every division the loop this replaces performed, all at once.
    reduced_row_echelon(matrix.matrix_mut());

    // The row led by `lm(g_i)` is the reduced element with that leading monomial. Rows led by
    // anything else are reducer multiples, and rows that cancelled to zero have no leading column.
    let wanted: std::collections::HashSet<Monomial<N>> = leading.into_iter().collect();
    let mut reduced: Vec<MultivariatePolynomial<N, F>> = (0..matrix.num_rows())
        .filter_map(|index| {
            let column = matrix.matrix().row(index).leading_column()?;
            let monomial = matrix.columns()[column];
            if !wanted.contains(&monomial) {
                return None;
            }
            Some(matrix.row_polynomial(index))
        })
        .collect();

    debug_assert_eq!(
        reduced.len(),
        elements,
        "every minimized element's leading monomial is a pivot, so every element is recovered"
    );

    // Descending by leading monomial, which is what `reduce_grobner_basis_until` returns. The
    // leading monomials are distinct, so this is a total order and the sequence is unique.
    reduced.sort_by(|a, b| order.cmp(&b.leading_monomial(order), &a.leading_monomial(order)));
    Ok((reduced, report))
}

#[cfg(test)]
mod tests {
    use super::{interreduce_by_matrix, MatrixInterreductionRefused};
    use crate::{
        fields::{Zp13, Zp2147483647},
        grobner::{
            benchmark_systems::{cyclic, katsura},
            buchberger::{minimal_basis_for_interreduction, reduce_grobner_basis},
            f4::f4_with_options,
            F4Options,
        },
        poly::MonomialOrder,
        FiniteField, MultivariatePolynomial,
    };

    const ORDERS: [MonomialOrder; 3] = [
        MonomialOrder::Lexicographic,
        MonomialOrder::GradedLexicographic,
        MonomialOrder::GradedReverseLexicographic,
    ];

    /// Both routes over the same basis, asserted equal element for element.
    fn assert_routes_agree<const N: usize, F: FiniteField>(
        label: &str,
        system: &[MultivariatePolynomial<N, F>],
        order: MonomialOrder,
    ) {
        // An F4 basis before interreduction, which is the input the stage actually receives.
        let Ok((basis, _)) = f4_with_options(
            system,
            order,
            &F4Options {
                interreduce_by_matrix: false,
                ..F4Options::default()
            },
        ) else {
            return;
        };

        let minimal = minimal_basis_for_interreduction(basis.clone(), order);
        let by_division = reduce_grobner_basis(basis, order);
        let (by_matrix, report) =
            interreduce_by_matrix(minimal, order, usize::MAX, usize::MAX, usize::MAX)
                .expect("an unbounded interreduction cannot be refused");

        assert_eq!(
            by_matrix, by_division,
            "{label} under {order:?}: the matrix route must reproduce the division route exactly"
        );
        assert_eq!(
            report.elements,
            by_division.len(),
            "{label}: every minimized element is recovered"
        );
        if report.elements >= 2 {
            assert!(report.rows >= report.elements, "the seeds are rows too");
            assert!(report.columns > 0);
        }
    }

    /// The two routes agree on the classical families, over three orders and two fields.
    #[test]
    fn test_the_matrix_route_reproduces_the_division_route() {
        for order in ORDERS {
            assert_routes_agree("katsura-4", &katsura::<4, Zp2147483647>(), order);
            assert_routes_agree("katsura-5", &katsura::<5, Zp2147483647>(), order);
            assert_routes_agree("cyclic-4", &cyclic::<4, Zp2147483647>(), order);
            assert_routes_agree("cyclic-5", &cyclic::<5, Zp2147483647>(), order);
            assert_routes_agree("katsura-4/13", &katsura::<4, Zp13>(), order);
        }
    }

    /// A one-element basis is already reduced, and needs no matrix at all.
    #[test]
    fn test_a_single_element_is_returned_unchanged() {
        let order = MonomialOrder::GradedReverseLexicographic;
        let p = MultivariatePolynomial::<2, Zp13>::parse("x^2 + y", ["x", "y"]).expect("parses");
        let (reduced, report) =
            interreduce_by_matrix(vec![p.clone()], order, usize::MAX, usize::MAX, usize::MAX)
                .expect("cannot be refused");
        assert_eq!(reduced, vec![p]);
        assert_eq!(report.elements, 1);
        assert_eq!(report.rows, 0, "no matrix was built");
    }

    /// The budgets are honored, and each names the resource it refused on. A stage that ignored
    /// them would be a way to exceed the computation's budgets by waiting until the end.
    #[test]
    fn test_each_budget_refuses_and_names_itself() {
        let order = MonomialOrder::GradedReverseLexicographic;
        let system = katsura::<5, Zp2147483647>();
        let (basis, _) = f4_with_options(
            &system,
            order,
            &F4Options {
                interreduce_by_matrix: false,
                ..F4Options::default()
            },
        )
        .expect("katsura-5 completes");
        let minimal = minimal_basis_for_interreduction(basis, order);

        assert_eq!(
            interreduce_by_matrix(minimal.clone(), order, 1, usize::MAX, usize::MAX),
            Err(MatrixInterreductionRefused::Rows { limit: 1 })
        );
        assert_eq!(
            interreduce_by_matrix(minimal.clone(), order, usize::MAX, 1, usize::MAX),
            Err(MatrixInterreductionRefused::Columns { limit: 1 })
        );
        match interreduce_by_matrix(minimal, order, usize::MAX, usize::MAX, 1) {
            Err(MatrixInterreductionRefused::Nonzeros { nonzeros }) => {
                assert!(nonzeros > 1, "the refusal reports what was needed")
            }
            other => panic!("expected a nonzero refusal, got {other:?}"),
        }
    }
}
