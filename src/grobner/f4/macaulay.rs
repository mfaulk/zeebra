//! The Macaulay matrix of a preprocessed batch: polynomials as rows, monomials as columns.
//!
//! Columns are the distinct monomials of all rows, sorted **descending under the monomial order
//! being computed** — not under `Monomial`'s derived `Ord`, which is lex whatever order is in
//! force. Column zero is therefore the largest monomial, a row's leading column is its leading
//! monomial, and the leftmost-first pivot rule of [`crate::linalg::sparse::row_echelon`] coincides
//! with the monomial order. Nothing downstream has to translate between the two.

use std::collections::{HashMap, HashSet};

use crate::{
    grobner::f4::symbolic::{MonicBasis, Preprocessed, PreprocessedRow},
    linalg::sparse::{SparseMatrix, SparseRow},
    poly::MonomialOrder,
    FiniteField, Monomial, MultivariatePolynomial,
};

/// Why a Macaulay matrix was not built.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum BuildBudgetExceeded {
    /// The batch's rows held more distinct monomials than the column budget allowed.
    Columns { limit: usize },

    /// The rows held more entries than the entry budget allowed. `nonzeros` is the count when the
    /// limit was crossed, so the overshoot is bounded by one row.
    Nonzeros { nonzeros: usize, limit: usize },
}

/// A sparse matrix whose columns are labelled by monomials and whose rows carry their provenance.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MacaulayMatrix<const N: usize, F: FiniteField> {
    /// The monomial labelling each column, descending under the order.
    columns: Vec<Monomial<N>>,

    /// The coefficients.
    matrix: SparseMatrix<F>,

    /// What each row is a multiple of, parallel to the matrix's rows.
    rows: Vec<PreprocessedRow<N>>,
}

impl<const N: usize, F: FiniteField> MacaulayMatrix<N, F> {
    /// Build the matrix of a preprocessed batch.
    pub fn build(
        basis: &MonicBasis<N, F>,
        preprocessed: &Preprocessed<N>,
        order: MonomialOrder,
    ) -> Self {
        Self::build_within(basis, preprocessed, order, usize::MAX, usize::MAX)
            .expect("an unbounded construction cannot exceed its budget")
    }

    /// As [`MacaulayMatrix::build`], abandoned if the matrix would exceed either budget.
    ///
    /// Both budgets are checked *while* the matrix is assembled, not after. Column collection
    /// stops as soon as too many distinct monomials have been seen, and entry counting stops as
    /// soon as too many entries have been written, so neither the monomial set nor the rows are
    /// fully materialized before the limit is noticed. The point of a budget is to refuse the
    /// allocation, which a check afterwards cannot do.
    ///
    /// Neither error says how large the matrix would have been: establishing that is the work
    /// being refused.
    pub fn build_within(
        basis: &MonicBasis<N, F>,
        preprocessed: &Preprocessed<N>,
        order: MonomialOrder,
        max_columns: usize,
        max_nonzeros: usize,
    ) -> Result<Self, BuildBudgetExceeded> {
        // The distinct monomials of every row, descending.
        let mut columns: Vec<Monomial<N>> = {
            let mut distinct: HashSet<Monomial<N>> = HashSet::new();
            let mut seen: Vec<Monomial<N>> = Vec::new();
            for row in &preprocessed.rows {
                for (monomial, _) in basis.shifted_terms(row.basis_index, &row.multiplier) {
                    if distinct.insert(monomial) {
                        if seen.len() == max_columns {
                            return Err(BuildBudgetExceeded::Columns { limit: max_columns });
                        }
                        seen.push(monomial);
                    }
                }
            }
            seen
        };
        columns.sort_by(|a, b| order.cmp(b, a));

        let column_of: HashMap<Monomial<N>, usize> = columns
            .iter()
            .enumerate()
            .map(|(index, monomial)| (*monomial, index))
            .collect();

        // Entries written so far, so a matrix that is small in each dimension but dense cannot
        // slip past the row and column budgets.
        let mut nonzeros = 0usize;
        let mut sparse_rows: Vec<SparseRow<F>> = Vec::with_capacity(preprocessed.rows.len());
        for row in &preprocessed.rows {
            let terms = basis.element(row.basis_index).terms.len();
            nonzeros += terms;
            if nonzeros > max_nonzeros {
                return Err(BuildBudgetExceeded::Nonzeros {
                    nonzeros,
                    limit: max_nonzeros,
                });
            }
            sparse_rows.push({
                // A row's terms arrive descending by the order and the columns are descending too,
                // so the column indices come out increasing — exactly the order a sparse row
                // stores them in, with no sorting needed. The monomials of a polynomial are
                // distinct and its coefficients nonzero, so the entries are canonical by
                // construction and `from_sorted_unchecked` is the right constructor; a
                // `debug_assert` inside it keeps that reasoning honest.
                let entries: Vec<(usize, F)> = basis
                    .shifted_terms(row.basis_index, &row.multiplier)
                    .map(|(monomial, coefficient)| {
                        let column = *column_of
                            .get(&monomial)
                            .expect("every row monomial is a column");
                        (column, coefficient)
                    })
                    .collect();
                SparseRow::from_sorted_unchecked(entries)
            });
        }

        Ok(Self {
            matrix: SparseMatrix::new(columns.len(), sparse_rows),
            columns,
            rows: preprocessed.rows.clone(),
        })
    }

    /// The monomial labelling each column, descending under the order.
    pub fn columns(&self) -> &[Monomial<N>] {
        &self.columns
    }

    /// The coefficient matrix.
    pub fn matrix(&self) -> &SparseMatrix<F> {
        &self.matrix
    }

    /// The coefficient matrix, mutably, for elimination to work on.
    pub fn matrix_mut(&mut self) -> &mut SparseMatrix<F> {
        &mut self.matrix
    }

    /// What each row is a multiple of. Only meaningful before elimination rewrites the rows.
    pub fn row_origins(&self) -> &[PreprocessedRow<N>] {
        &self.rows
    }

    pub fn num_rows(&self) -> usize {
        self.matrix.num_rows()
    }

    pub fn num_columns(&self) -> usize {
        self.columns.len()
    }

    pub fn nonzeros(&self) -> usize {
        self.matrix.nonzeros()
    }

    /// The polynomial a row of the matrix represents.
    pub fn row_polynomial(&self, index: usize) -> MultivariatePolynomial<N, F> {
        self.sparse_row_polynomial(self.matrix.row(index))
    }

    /// The polynomial a sparse row over these columns represents.
    pub fn sparse_row_polynomial(&self, row: &SparseRow<F>) -> MultivariatePolynomial<N, F> {
        let terms: Vec<(Monomial<N>, F)> = row
            .entries()
            .iter()
            .map(|(column, coefficient)| (self.columns[*column], *coefficient))
            .collect();
        MultivariatePolynomial::new(&terms)
    }
}

#[cfg(test)]
mod tests {
    use super::{BuildBudgetExceeded, MacaulayMatrix};
    use crate::{
        fields::Zp13,
        grobner::{
            f4::symbolic::{symbolic_preprocessing, MonicBasis},
            pairs::CriticalPair,
        },
        poly::MonomialOrder,
        Monomial, MultivariatePolynomial, One,
    };

    type F = Zp13;
    const VARS: [&str; 3] = ["x", "y", "z"];
    const ALL_ORDERS: [MonomialOrder; 3] = [
        MonomialOrder::Lexicographic,
        MonomialOrder::GradedLexicographic,
        MonomialOrder::GradedReverseLexicographic,
    ];

    fn parse(s: &str) -> MultivariatePolynomial<3, F> {
        MultivariatePolynomial::parse(s, VARS).unwrap()
    }

    fn system(strings: &[&str]) -> Vec<MultivariatePolynomial<3, F>> {
        strings.iter().map(|s| parse(s)).collect()
    }

    /// Build the matrix for every pair of a system under one order.
    fn build(
        strings: &[&str],
        order: MonomialOrder,
    ) -> (Vec<MultivariatePolynomial<3, F>>, MacaulayMatrix<3, F>) {
        let polynomials = system(strings);
        let basis = MonicBasis::new(&polynomials, order);
        let mut pairs = Vec::new();
        for left in 0..polynomials.len() {
            for right in (left + 1)..polynomials.len() {
                pairs.push(CriticalPair::new(&polynomials, left, right, order));
            }
        }
        let preprocessed = symbolic_preprocessing(&basis, &pairs);
        let matrix = MacaulayMatrix::build(&basis, &preprocessed, order);
        (polynomials, matrix)
    }

    /// The hand-verifiable case: f = x^2 + y, g = x^2 + z over the columns x^2, y, z.
    ///
    /// Both rows are the generators themselves, column zero is x^2 under every order, and
    /// subtracting the rows gives y - z — the S-polynomial — which is what the matrix is for.
    #[test]
    fn test_hand_verifiable_matrix() {
        for order in ALL_ORDERS {
            let (_, matrix) = build(&["x^2 + y", "x^2 + z"], order);

            assert_eq!(matrix.num_rows(), 2, "{}", order.name());
            assert_eq!(matrix.num_columns(), 3, "{}", order.name());
            assert_eq!(
                matrix.columns()[0],
                Monomial::new(&[2, 0, 0]),
                "{}: column zero should be the largest monomial",
                order.name()
            );

            // The rows round-trip to the generators.
            assert_eq!(
                matrix.row_polynomial(0),
                parse("x^2 + y"),
                "{}",
                order.name()
            );
            assert_eq!(
                matrix.row_polynomial(1),
                parse("x^2 + z"),
                "{}",
                order.name()
            );

            // And one row operation exposes the S-polynomial.
            let mut scratch = Vec::new();
            let pivot = matrix.matrix().row(0).clone();
            let mut second = matrix.matrix().row(1).clone();
            second.subtract_scaled(&pivot, &F::ONE, &mut scratch);
            assert_eq!(
                matrix.sparse_row_polynomial(&second),
                parse("z - y"),
                "{}",
                order.name()
            );
        }
    }

    /// Columns are distinct and strictly descending under the order in force.
    #[test]
    fn test_columns_are_distinct_and_descending() {
        let systems: Vec<Vec<&str>> = vec![
            vec!["x^2 + y", "x^2 + z"],
            vec!["x + y + z", "x*y + x*z + y*z", "x*y*z - 1"],
            vec!["x^3 - y", "x^2 - z", "x - y*z", "y^2 - 1"],
            vec!["x*z - y^2", "x^3 - z^2"],
        ];

        for order in ALL_ORDERS {
            for strings in &systems {
                let (_, matrix) = build(strings, order);
                for window in matrix.columns().windows(2) {
                    assert_eq!(
                        order.cmp(&window[0], &window[1]),
                        std::cmp::Ordering::Greater,
                        "{:?} under {}: columns are not strictly descending",
                        strings,
                        order.name()
                    );
                }
            }
        }
    }

    /// The column order follows the monomial order, not `Monomial`'s derived lex ordering.
    ///
    /// Under grevlex, y^2 outranks x*z; under lex and grlex it does not. A construction that
    /// sorted by the derived `Ord` would put them the same way round under all three.
    #[test]
    fn test_column_order_follows_the_monomial_order() {
        let xz = Monomial::<3>::new(&[1, 0, 1]);
        let y2 = Monomial::<3>::new(&[0, 2, 0]);

        let position = |order: MonomialOrder, target: Monomial<3>| {
            let (_, matrix) = build(&["x*z + y^2 + 1", "x*z - y^2"], order);
            matrix
                .columns()
                .iter()
                .position(|monomial| *monomial == target)
                .unwrap_or_else(|| panic!("{} is not a column", target))
        };

        for order in [
            MonomialOrder::Lexicographic,
            MonomialOrder::GradedLexicographic,
        ] {
            assert!(
                position(order, xz) < position(order, y2),
                "{}: x*z should precede y^2",
                order.name()
            );
        }
        let grevlex = MonomialOrder::GradedReverseLexicographic;
        assert!(
            position(grevlex, y2) < position(grevlex, xz),
            "grevlex: y^2 should precede x*z"
        );
    }

    /// Every row round-trips to the polynomial it was built from, coefficients included.
    #[test]
    fn test_rows_round_trip_to_their_polynomials() {
        let systems: Vec<Vec<&str>> = vec![
            vec!["x^2 + y", "x^2 + z"],
            vec!["3*x^2 + 5*y", "7*x*y + 11*y"],
            vec!["x + y + z", "x*y + x*z + y*z", "x*y*z - 1"],
            vec!["x^3 - y", "x^2 - z", "x - y*z", "y^2 - 1"],
            vec!["x^2 + y + 1", "y^2 + z + 2", "z^2 + x + 3"],
        ];

        for order in ALL_ORDERS {
            for strings in &systems {
                let polynomials = system(strings);
                let basis = MonicBasis::new(&polynomials, order);
                let mut pairs = Vec::new();
                for left in 0..polynomials.len() {
                    for right in (left + 1)..polynomials.len() {
                        pairs.push(CriticalPair::new(&polynomials, left, right, order));
                    }
                }
                let preprocessed = symbolic_preprocessing(&basis, &pairs);
                let matrix = MacaulayMatrix::build(&basis, &preprocessed, order);

                for (index, row) in preprocessed.rows.iter().enumerate() {
                    assert_eq!(
                        matrix.row_polynomial(index),
                        basis.shifted_polynomial(row.basis_index, &row.multiplier),
                        "{:?} under {}: row {} does not round-trip",
                        strings,
                        order.name(),
                        index
                    );
                }
            }
        }
    }

    /// A row's leading column is its leading monomial, which is what pivoting relies on.
    #[test]
    fn test_leading_column_is_the_leading_monomial() {
        for order in ALL_ORDERS {
            let polynomials = system(&["x^3 - y", "x^2 - z", "x - y*z", "y^2 - 1"]);
            let basis = MonicBasis::new(&polynomials, order);
            let mut pairs = Vec::new();
            for left in 0..polynomials.len() {
                for right in (left + 1)..polynomials.len() {
                    pairs.push(CriticalPair::new(&polynomials, left, right, order));
                }
            }
            let preprocessed = symbolic_preprocessing(&basis, &pairs);
            let matrix = MacaulayMatrix::build(&basis, &preprocessed, order);

            for index in 0..matrix.num_rows() {
                let column = matrix
                    .matrix()
                    .row(index)
                    .leading_column()
                    .expect("nonzero");
                assert_eq!(
                    matrix.columns()[column],
                    preprocessed.leading_monomial(&basis, index),
                    "{}: row {}",
                    order.name(),
                    index
                );
            }
        }
    }

    /// Every row is monic, because every basis element was made monic before shifting.
    #[test]
    fn test_rows_are_monic() {
        for order in ALL_ORDERS {
            let (_, matrix) = build(&["3*x^2 + 5*y", "7*x*y + 11*y", "2*y^2 - 1"], order);
            for index in 0..matrix.num_rows() {
                assert_eq!(
                    matrix.matrix().row(index).leading_coefficient(),
                    Some(F::ONE),
                    "{}: row {} is not monic",
                    order.name(),
                    index
                );
            }
        }
    }

    /// Construction is deterministic, columns and rows alike.
    #[test]
    fn test_construction_is_deterministic() {
        for order in ALL_ORDERS {
            let first = build(&["x^2*y + z", "y^2*z + x", "x*z^2 + y", "x*y*z - 1"], order).1;
            for _ in 0..8 {
                assert_eq!(
                    build(&["x^2*y + z", "y^2*z + x", "x*z^2 + y", "x*y*z - 1"], order).1,
                    first,
                    "{}",
                    order.name()
                );
            }
        }
    }

    /// The column and entry budgets are exact at their boundaries, and stop mid-construction.
    ///
    /// Succeeding at exactly what the matrix needs and failing one below it is what shows the
    /// checks happen while the monomial set and the rows are being assembled. A check afterwards
    /// would have to materialize the whole matrix to discover it was not allowed, which is the
    /// allocation the budget exists to refuse.
    #[test]
    fn test_build_budgets_are_exact() {
        for order in ALL_ORDERS {
            let polynomials = system(&["x^3 - y", "x^2 - z", "x - y*z", "y^2 - 1"]);
            let basis = MonicBasis::new(&polynomials, order);
            let mut pairs = Vec::new();
            for left in 0..polynomials.len() {
                for right in (left + 1)..polynomials.len() {
                    pairs.push(CriticalPair::new(&polynomials, left, right, order));
                }
            }
            let preprocessed = symbolic_preprocessing(&basis, &pairs);
            let full = MacaulayMatrix::build(&basis, &preprocessed, order);
            let (columns, nonzeros) = (full.num_columns(), full.nonzeros());

            assert_eq!(
                MacaulayMatrix::build_within(&basis, &preprocessed, order, columns, nonzeros)
                    .expect("budgets of exactly what is needed suffice"),
                full,
                "{}",
                order.name()
            );
            assert_eq!(
                MacaulayMatrix::build_within(&basis, &preprocessed, order, columns - 1, nonzeros),
                Err(BuildBudgetExceeded::Columns { limit: columns - 1 }),
                "{}",
                order.name()
            );

            // The entry budget reports the count that crossed it, which overshoots by at most the
            // entries of a single row.
            match MacaulayMatrix::<3, F>::build_within(
                &basis,
                &preprocessed,
                order,
                columns,
                nonzeros - 1,
            ) {
                Err(BuildBudgetExceeded::Nonzeros {
                    nonzeros: hit,
                    limit,
                }) => {
                    assert_eq!(limit, nonzeros - 1, "{}", order.name());
                    assert!(
                        hit > limit,
                        "{}: {} should exceed {}",
                        order.name(),
                        hit,
                        limit
                    );
                    assert!(
                        hit <= nonzeros,
                        "{}: {} overshot the matrix total {}",
                        order.name(),
                        hit,
                        nonzeros
                    );
                }
                other => panic!(
                    "{}: expected an entry-budget error, got {:?}",
                    order.name(),
                    other
                ),
            }
        }
    }

    /// An empty batch gives a matrix with no rows and no columns.
    #[test]
    fn test_empty_batch_gives_an_empty_matrix() {
        let order = MonomialOrder::Lexicographic;
        let basis = MonicBasis::new(&system(&["x^2 + y"]), order);
        let preprocessed = symbolic_preprocessing(&basis, &[]);
        let matrix = MacaulayMatrix::build(&basis, &preprocessed, order);
        assert_eq!(matrix.num_rows(), 0);
        assert_eq!(matrix.num_columns(), 0);
        assert_eq!(matrix.nonzeros(), 0);
    }
}
