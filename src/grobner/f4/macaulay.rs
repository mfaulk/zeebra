//! The Macaulay matrix of a preprocessed batch: polynomials as rows, monomials as columns.
//!
//! Columns are the distinct monomials of all rows, sorted **descending under the monomial order
//! being computed** — not under `Monomial`'s derived `Ord`, which is lex whatever order is in
//! force. Column zero is therefore the largest monomial, a row's leading column is its leading
//! monomial, and the leftmost-first pivot rule of [`crate::linalg::sparse::row_echelon`] coincides
//! with the monomial order. Nothing downstream has to translate between the two.

use crate::{
    grobner::f4::statistics::{ConstructionTimings, StageClock},
    grobner::f4::symbolic::{MonicBasis, Preprocessed, PreprocessedRow, RowKind},
    linalg::sparse::{SparseMatrix, SparseRow},
    poly::{MonomialMap, MonomialOrder, MonomialSet},
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
    /// #330's pre-handout route: hash every row monomial again here instead of reading the set
    /// symbolic preprocessing interned.
    ///
    /// A reimplementation kept only so the two routes can be measured against each other in **one
    /// process on one build**, which is the only way to keep a compiler difference out of the
    /// ratio for a change that is structural rather than option-gated. Nothing in the shipping
    /// path calls it, and `test_the_two_construction_routes_agree` asserts it returns the same
    /// matrix as [`MacaulayMatrix::build`].
    pub fn build_rehashing_for_benchmark(
        basis: &MonicBasis<N, F>,
        preprocessed: &Preprocessed<N>,
        order: MonomialOrder,
        measure: bool,
    ) -> (Self, ConstructionTimings) {
        let mut clock = StageClock::new(measure);
        let mut timings = ConstructionTimings::default();

        let mut columns: Vec<Monomial<N>> = {
            let mut distinct: MonomialSet<N> = MonomialSet::default();
            let mut seen: Vec<Monomial<N>> = Vec::new();
            for row in &preprocessed.rows {
                for (monomial, _) in basis.shifted_terms(row.basis_index, &row.multiplier) {
                    if distinct.insert(monomial) {
                        seen.push(monomial);
                    }
                }
            }
            seen
        };
        timings.collect = clock.lap();

        columns.sort_by(|a, b| order.cmp(b, a));
        timings.sort = clock.lap();

        let column_of: MonomialMap<N, usize> = columns
            .iter()
            .enumerate()
            .map(|(index, monomial)| (*monomial, index))
            .collect();
        timings.map = clock.lap();

        let mut sparse_rows: Vec<SparseRow<F>> = Vec::with_capacity(preprocessed.rows.len());
        for row in &preprocessed.rows {
            let entries: Vec<(usize, F)> = basis
                .shifted_terms(row.basis_index, &row.multiplier)
                .map(|(monomial, coefficient)| {
                    let column = *column_of
                        .get(&monomial)
                        .expect("every row monomial is a column");
                    (column, coefficient)
                })
                .collect();
            sparse_rows.push(SparseRow::from_sorted_unchecked(entries));
        }
        let built = Self {
            matrix: SparseMatrix::new(columns.len(), sparse_rows),
            columns,
            rows: preprocessed.rows.clone(),
        };
        timings.scatter = clock.lap();

        (built, timings)
    }

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
    /// The entry budget is checked *while* the rows are written, not after: counting stops as soon
    /// as too many entries have been written, so the rows are never fully materialized before the
    /// limit is noticed. The point of a budget is to refuse the allocation, which a check
    /// afterwards cannot do.
    ///
    /// The column budget is a length check rather than an incremental one, and still refuses
    /// before this function allocates anything: the monomial set it reads was interned by symbolic
    /// preprocessing under [`RowBudgetExceeded`](super::symbolic::RowBudgetExceeded)'s own bound,
    /// so there is nothing left here for an incremental check to refuse. Which count crosses the
    /// line is unchanged — the old loop errored exactly when the distinct monomials exceeded
    /// `max_columns`, and so does this.
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
        Self::build_measured(basis, preprocessed, order, max_columns, max_nonzeros, false)
            .map(|(matrix, _)| matrix)
    }

    /// As [`MacaulayMatrix::build_within`], reporting where the time went when `measure` is set.
    ///
    /// The three reported phases partition the call, so their sum is the whole of it. They exist
    /// because #330 asked whether the monomial-to-column map is worth removing, and the only way
    /// to answer that before writing the replacement is to price the map against the scatter it
    /// feeds. `measure` is threaded rather than always on so that the clock reads do not appear in
    /// the instruction stream of the default path at all — see [`StageClock`].
    pub fn build_measured(
        basis: &MonicBasis<N, F>,
        preprocessed: &Preprocessed<N>,
        order: MonomialOrder,
        max_columns: usize,
        max_nonzeros: usize,
        measure: bool,
    ) -> Result<(Self, ConstructionTimings), BuildBudgetExceeded> {
        let mut clock = StageClock::new(measure);
        let mut timings = ConstructionTimings::default();

        // The distinct monomials of every row, taken from the set symbolic preprocessing already
        // interned rather than hashed a second time here (#330). The two sets are equal by
        // construction — see `Preprocessed::monomials` — so this is a copy of `num_columns`
        // monomials in place of one hash insert per row monomial, and row monomials outnumber
        // columns by whatever the matrix's average column density is.
        if preprocessed.monomials.len() > max_columns {
            return Err(BuildBudgetExceeded::Columns { limit: max_columns });
        }
        let mut columns: Vec<Monomial<N>> = preprocessed.monomials.iter().copied().collect();
        timings.collect = clock.lap();

        columns.sort_by(|a, b| order.cmp(b, a));
        timings.sort = clock.lap();

        let column_of: MonomialMap<N, usize> = columns
            .iter()
            .enumerate()
            .map(|(index, monomial)| (*monomial, index))
            .collect();
        timings.map = clock.lap();

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

        let built = Self {
            matrix: SparseMatrix::new(columns.len(), sparse_rows),
            columns,
            rows: preprocessed.rows.clone(),
        };
        timings.scatter = clock.lap();

        Ok((built, timings))
    }

    /// Move the reducer multiples ahead of the pair rows, ascending by leading column, and report
    /// where the pair rows now begin.
    ///
    /// Columns descend under the monomial order, so ascending leading column is descending leading
    /// monomial and the prefix is upper triangular on its own leading columns. The pair rows keep
    /// their arrival order relative to one another, so the arrangement is a function of the batch.
    ///
    /// Both halves of the matrix are permuted together — the coefficients and the provenance — so
    /// [`MacaulayMatrix::row_origins`] still describes row `i`.
    pub fn partition_reducers_first(&mut self) -> usize {
        // A reducer row is nonzero, so `leading_column` is `Some`; the fallback keeps the key
        // total rather than asserting here, which [`super::structured`] does with a better message.
        let mut arrangement: Vec<usize> = (0..self.rows.len()).collect();
        arrangement.sort_by_key(|&index| match self.rows[index].kind {
            RowKind::Reducer => (
                0,
                self.matrix
                    .row(index)
                    .leading_column()
                    .unwrap_or(usize::MAX),
            ),
            RowKind::PairComponent { .. } => (1, index),
        });

        let mut origins: Vec<PreprocessedRow<N>> = Vec::with_capacity(arrangement.len());
        let mut coefficients: Vec<SparseRow<F>> = Vec::with_capacity(arrangement.len());
        let matrix_rows = self.matrix.rows_mut();
        for &index in &arrangement {
            origins.push(self.rows[index]);
            coefficients.push(std::mem::take(&mut matrix_rows[index]));
        }
        *self.matrix.rows_mut() = coefficients;
        self.rows = origins;

        self.rows
            .iter()
            .take_while(|row| row.kind == RowKind::Reducer)
            .count()
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
    use std::time::Duration;

    use super::{BuildBudgetExceeded, ConstructionTimings, MacaulayMatrix};
    use crate::{
        fields::Zp13,
        grobner::{
            f4::symbolic::{symbolic_preprocessing, MonicBasis},
            pairs::CriticalPair,
        },
        poly::{MonomialOrder, MonomialSet},
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

    /// Symbolic preprocessing's monomial set is exactly the matrix's column set.
    ///
    /// This is the invariant #330's column handout rests on: if it holds, construction can take
    /// the set preprocessing already interned instead of hashing every row monomial a second time.
    /// Asserted over every order and over a batch with reducer rows, because the set is grown in
    /// two places — the seed rows' terms and each reducer row's terms as it is admitted — and a
    /// batch with no reducers would exercise only the first.
    #[test]
    fn test_preprocessing_interns_exactly_the_column_set() {
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
            assert!(
                preprocessed
                    .rows
                    .iter()
                    .any(|row| row.kind == crate::grobner::f4::RowKind::Reducer),
                "the batch must have reducer rows for this to mean anything"
            );

            let matrix = MacaulayMatrix::<3, F>::build(&basis, &preprocessed, order);
            let built: MonomialSet<3> = matrix.columns().iter().copied().collect();
            assert_eq!(preprocessed.monomials, built, "{}", order.name());
        }
    }

    /// The handout route and the rehashing route return the identical matrix, columns and all.
    ///
    /// This is what makes the A/B in `examples/f4_profile construction` a measurement of cost
    /// rather than of two different matrices. Equality of the whole `MacaulayMatrix` covers the
    /// column order too, which matters because the handout route sorts a vector drained from a
    /// hash set and the old one sorted a vector in first-appearance order — the monomial order is
    /// total on distinct monomials, so both sorts land in the same place, and this says so.
    #[test]
    fn test_the_two_construction_routes_agree() {
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

            let handout = MacaulayMatrix::<3, F>::build(&basis, &preprocessed, order);
            let (rehashing, _) = MacaulayMatrix::<3, F>::build_rehashing_for_benchmark(
                &basis,
                &preprocessed,
                order,
                false,
            );
            assert_eq!(handout, rehashing, "{}", order.name());
        }
    }

    /// Releasing the interned set empties it and leaves the rest of the batch's data intact.
    #[test]
    fn test_releasing_the_interned_set_keeps_the_rest_of_the_batch() {
        let order = MonomialOrder::GradedReverseLexicographic;
        let polynomials = system(&["x^3 - y", "x^2 - z", "x - y*z", "y^2 - 1"]);
        let basis = MonicBasis::new(&polynomials, order);
        let pairs = vec![CriticalPair::new(&polynomials, 0, 1, order)];
        let mut preprocessed = symbolic_preprocessing(&basis, &pairs);

        let rows = preprocessed.rows.clone();
        let leads = preprocessed.leading_monomials.clone();
        assert!(!preprocessed.monomials.is_empty());

        preprocessed.release_monomials();
        assert!(preprocessed.monomials.is_empty());
        assert_eq!(preprocessed.rows, rows);
        assert_eq!(preprocessed.leading_monomials, leads);
    }

    /// Measuring construction does not change the matrix, and the measured phases are all nonzero.
    #[test]
    fn test_the_construction_phases_partition_a_measured_build() {
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
            let unmeasured = MacaulayMatrix::build(&basis, &preprocessed, order);

            let (measured, split) = MacaulayMatrix::build_measured(
                &basis,
                &preprocessed,
                order,
                usize::MAX,
                usize::MAX,
                true,
            )
            .expect("an unbounded construction cannot exceed its budget");
            assert_eq!(measured, unmeasured, "{}", order.name());
            assert_eq!(
                split.total(),
                split.collect + split.sort + split.map + split.scatter,
                "{}",
                order.name()
            );
            assert_eq!(split.columns(), split.collect + split.sort);
            assert!(split.total() > Duration::ZERO, "{}", order.name());
            assert!(
                (0.0..=1.0).contains(&split.handout_share()),
                "{}",
                order.name()
            );
            assert!(
                split.removable_share() <= split.handout_share(),
                "{}",
                order.name()
            );
        }
    }

    /// A build with measurement off reads no clock, so every phase is zero.
    #[test]
    fn test_an_unmeasured_build_records_no_phase_times() {
        let order = MonomialOrder::GradedReverseLexicographic;
        let polynomials = system(&["x^3 - y", "x^2 - z", "x - y*z", "y^2 - 1"]);
        let basis = MonicBasis::new(&polynomials, order);
        let pairs = vec![CriticalPair::new(&polynomials, 0, 1, order)];
        let preprocessed = symbolic_preprocessing(&basis, &pairs);

        let (_, split) = MacaulayMatrix::build_measured(
            &basis,
            &preprocessed,
            order,
            usize::MAX,
            usize::MAX,
            false,
        )
        .expect("an unbounded construction cannot exceed its budget");
        assert_eq!(split, ConstructionTimings::default());
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
