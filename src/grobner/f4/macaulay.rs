//! The Macaulay matrix of a preprocessed batch: polynomials as rows, monomials as columns.
//!
//! Columns are the distinct monomials of all rows, sorted **descending under the monomial order
//! being computed** — not under `Monomial`'s derived `Ord`, which is lex whatever order is in
//! force. Column zero is therefore the largest monomial, a row's leading column is its leading
//! monomial, and the leftmost-first pivot rule of [`crate::linalg::sparse::row_echelon`] coincides
//! with the monomial order. Nothing downstream has to translate between the two.

use std::{
    hint::black_box,
    time::{Duration, Instant},
};

use crate::{
    grobner::f4::statistics::{ConstructionTimings, StageClock},
    grobner::f4::symbolic::{MonicBasis, MonomialHandle, Preprocessed, PreprocessedRow, RowKind},
    linalg::sparse::{SparseMatrix, SparseRow},
    poly::{MonomialMap, MonomialOrder, MonomialSet},
    FiniteField, Monomial, MultivariatePolynomial,
};

/// Why a Macaulay matrix was not built.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum BuildBudgetExceeded {
    /// The batch's rows held more distinct monomials than the column budget allowed.
    Columns { limit: usize },

    /// The complete construction needs `nonzeros` entries, more than the entry budget allows.
    /// This count is exact; elimination may subsequently need more entries.
    Nonzeros { nonzeros: usize, limit: usize },
}

/// How much of the pre-#621 row scatter's per-term work to do, for #582's nested ablation.
///
/// Each variant is a **prefix** of the next, so the cost of one step is the difference between two
/// adjacent arms. See
/// [`MacaulayMatrix::scatter_prefix_for_benchmark`] for why the split is an ablation rather than
/// another pair of counters.
///
/// These are the steps of the scatter as it was before #621 — shift, hash, write — so the control
/// beside them is [`MacaulayMatrix::build_hashed_scatter_for_benchmark`] and not `build_measured`,
/// whose loop forms no monomial and reads no hash.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ScatterPrefix {
    /// Shift each row's terms by its multiplier, and consume the result.
    Shift,

    /// Shift, then turn each shifted monomial into a column through the map.
    ShiftAndLookup,

    /// Shift, look up, collect the per-row `Vec` and build the `SparseRow`: the whole of the
    /// pre-#621 loop, so this arm doubles as a control against
    /// [`MacaulayMatrix::build_hashed_scatter_for_benchmark`]'s `scatter_rows`.
    Row,
}

/// What one [`ScatterPrefix`] arm cost, and proof it was not optimized away.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ScatterPrefixTiming {
    /// How long the arm took over every row of the batch.
    pub elapsed: Duration,

    /// A quantity derived from the arm's own output, pinned by test to one derived from the
    /// matrix. An arm the optimizer emptied cannot produce it.
    pub checksum: u64,
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

        // The same sort as the shipping route, and it has to stay the same one: `collect` is the
        // only phase this arm is meant to differ in, and the other three are what makes the A/B a
        // control on itself.
        columns.sort_unstable_by(|a, b| order.cmp(b, a));
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
        timings.scatter_rows = clock.lap();

        let built = Self {
            matrix: SparseMatrix::new(columns.len(), sparse_rows),
            columns,
            rows: preprocessed.rows.clone(),
        };
        timings.scatter_assemble = clock.lap();
        timings.scatter = timings.scatter_rows + timings.scatter_assemble;

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
    /// Both budgets are checked before allocating columns or coefficient rows. Symbolic
    /// preprocessing already records every column and one handle per row term, so the complete
    /// construction demand is available without materializing the matrix. This does not predict
    /// fill-in during elimination or bound symbolic preprocessing's own allocations.
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
    /// The four reported phases partition the call, so their sum is the whole of it. They exist
    /// because #330 asked whether the monomial-to-column map is worth removing, and the only way
    /// to answer that before writing the replacement is to price the map against the scatter it
    /// feeds. `measure` is threaded rather than always on so that the clock reads do not appear in
    /// the instruction stream of the default path at all — see [`StageClock`].
    ///
    /// `scatter` is in turn the sum of `scatter_rows` and `scatter_assemble` (#582), which costs
    /// one extra clock read per matrix on the measured path and none on the default one.
    ///
    /// # Panics
    /// If `preprocessed` was not produced from `basis`: the handle run of each row is located by
    /// the term count of the basis element the row names, so a mismatch is caught by the slice
    /// split rather than silently producing a different matrix.
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

        // The distinct monomials of every row, taken from the arena symbolic preprocessing already
        // interned rather than hashed a second time here (#330). The two sets are equal by
        // construction — see `Preprocessed::monomials` — so this is a copy of `num_columns`
        // monomials in place of one hash insert per row monomial, and row monomials outnumber
        // columns by whatever the matrix's average column density is.
        //
        // Each monomial is paired with its handle, which is its index in the arena, so that the
        // sort below carries the handle along to wherever it puts the column. Pairing rather than
        // sorting a permutation of handles separately keeps the comparator reading the monomial
        // directly, which is the sort #583 measured.
        if preprocessed.monomials.len() > max_columns {
            return Err(BuildBudgetExceeded::Columns { limit: max_columns });
        }
        let nonzeros = preprocessed.term_handles.len();
        if nonzeros > max_nonzeros {
            return Err(BuildBudgetExceeded::Nonzeros {
                nonzeros,
                limit: max_nonzeros,
            });
        }
        let mut sorted: Vec<(Monomial<N>, MonomialHandle)> = preprocessed
            .monomials
            .iter()
            .copied()
            .zip(0 as MonomialHandle..)
            .collect();
        timings.collect = clock.lap();

        // Unstable because stability has nothing to decide here: every `MonomialOrder` variant,
        // weighted included, reports `Equal` only for equal monomials, and the columns are
        // distinct — so the descending sequence is unique and there is no tie for either sort to
        // break (`test_the_column_order_does_not_depend_on_the_handout_order`, over the weighted
        // variant too, since a tie-break is where strictness would be lost). It is worth 1.02-1.24x of
        // the sort — pdqsort against an adaptive merge sort with nothing to adapt to, because #330
        // began handing this vector over drained from a hash set instead of in the first-appearance
        // order the old route pushed, and the runs the merge sort exploited went with it (#583).
        //
        // Comparing on the monomial alone and not on the pair: the handles are distinct, so
        // including them would give the comparator a tie-break to apply and make the sort's output
        // depend on it. There is no tie to break, and a comparator that says so is the one the
        // unstable sort is licensed by.
        sorted.sort_unstable_by(|a, b| order.cmp(&b.0, &a.0));
        timings.sort = clock.lap();

        // Handle to column: a flat array, in place of #330's `MonomialMap<N, usize>`. The handle is
        // already the monomial's index, so all this has to record is the permutation the sort
        // applied — four bytes per column against a hash entry per column, and an indexed load per
        // entry against a hash probe per entry, which is #621.
        let mut column_of: Vec<MonomialHandle> = vec![0; sorted.len()];
        let mut columns: Vec<Monomial<N>> = Vec::with_capacity(sorted.len());
        for (column, (monomial, handle)) in sorted.into_iter().enumerate() {
            column_of[handle as usize] = column as MonomialHandle;
            columns.push(monomial);
        }
        timings.map = clock.lap();

        let mut sparse_rows: Vec<SparseRow<F>> = Vec::with_capacity(preprocessed.rows.len());
        let mut handles: &[MonomialHandle] = &preprocessed.term_handles;
        for row in &preprocessed.rows {
            let terms = &basis.element(row.basis_index).terms;
            // A row's handles are the next run of `term_handles`, one per term of the basis
            // element. `split_at` is what asserts the layout: a `Preprocessed` from another basis
            // runs the vector short and panics here instead of building the wrong matrix.
            let (row_handles, rest) = handles.split_at(terms.len());
            handles = rest;
            sparse_rows.push({
                // A row's terms arrive descending by the order and the columns are descending too,
                // so the column indices come out increasing — exactly the order a sparse row
                // stores them in, with no sorting needed. The monomials of a polynomial are
                // distinct and its coefficients nonzero, so the entries are canonical by
                // construction and `from_sorted_unchecked` is the right constructor; a
                // `debug_assert` inside it keeps that reasoning honest.
                //
                // The shifted monomial is never formed. Preprocessing already met it, interned it
                // and recorded the handle, so the multiplier shift is not needed either — only the
                // coefficient, which the multiplier does not touch.
                let entries: Vec<(usize, F)> = row_handles
                    .iter()
                    .zip(terms.iter())
                    .map(|(handle, (_, coefficient))| {
                        (column_of[*handle as usize] as usize, *coefficient)
                    })
                    .collect();
                SparseRow::from_sorted_unchecked(entries)
            });
        }
        timings.scatter_rows = clock.lap();

        let built = Self {
            matrix: SparseMatrix::new(columns.len(), sparse_rows),
            columns,
            rows: preprocessed.rows.clone(),
        };
        timings.scatter_assemble = clock.lap();
        timings.scatter = timings.scatter_rows + timings.scatter_assemble;

        Ok((built, timings))
    }

    /// #621's pre-handle route: rederive each row monomial from its multiplier and read its column
    /// out of a `MonomialMap` built over the sorted columns.
    ///
    /// A reimplementation kept only so the two scatters can be measured against each other in **one
    /// process on one build**, for the same reason
    /// [`MacaulayMatrix::build_rehashing_for_benchmark`] exists. It shares that route's `collect`
    /// and `sort` with nothing but the pairing removed, so the arms differ in `map` and
    /// `scatter_rows` and in nothing else. Nothing in the shipping path calls it, and
    /// `test_the_two_scatter_routes_agree` asserts it returns the same matrix as
    /// [`MacaulayMatrix::build`].
    pub fn build_hashed_scatter_for_benchmark(
        basis: &MonicBasis<N, F>,
        preprocessed: &Preprocessed<N>,
        order: MonomialOrder,
        measure: bool,
    ) -> (Self, ConstructionTimings) {
        let mut clock = StageClock::new(measure);
        let mut timings = ConstructionTimings::default();

        let mut columns: Vec<Monomial<N>> = preprocessed.monomials.to_vec();
        timings.collect = clock.lap();

        columns.sort_unstable_by(|a, b| order.cmp(b, a));
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
        timings.scatter_rows = clock.lap();

        let built = Self {
            matrix: SparseMatrix::new(columns.len(), sparse_rows),
            columns,
            rows: preprocessed.rows.clone(),
        };
        timings.scatter_assemble = clock.lap();
        timings.scatter = timings.scatter_rows + timings.scatter_assemble;

        (built, timings)
    }

    /// Time one prefix of the scatter's per-term work, for #582's ablation.
    ///
    /// The scatter's inner steps are per *term*, and `Instant::now()` costs more than the term's
    /// work does, so a counter around each step would measure the clock. The arms are therefore
    /// **nested prefixes** of the real loop, timed whole and differenced: `ShiftAndLookup` less
    /// `Shift` is the per-term map lookup, `Row` less `ShiftAndLookup` is the per-row `Vec` and
    /// the `SparseRow` build, and `scatter_assemble` is the rest. The loop is
    /// [`MacaulayMatrix::build_hashed_scatter_for_benchmark`]'s, which is what #582 measured; the
    /// shipping scatter has read its columns through handles since #621.
    ///
    /// The columns and the map are built outside the timing, because they are
    /// [`ConstructionTimings`]'s other phases and charging them here would bury the difference.
    ///
    /// The returned checksum is what keeps an arm from being optimized into nothing: the arms
    /// below `Row` discard the entries they compute, so without a consumed result the shift and
    /// the lookup are both dead code.
    /// `test_the_scatter_ablation_arms_do_the_scatters_work` pins each checksum to a quantity
    /// derived from [`MacaulayMatrix::build`]'s matrix.
    pub fn scatter_prefix_for_benchmark(
        basis: &MonicBasis<N, F>,
        preprocessed: &Preprocessed<N>,
        order: MonomialOrder,
        prefix: ScatterPrefix,
    ) -> ScatterPrefixTiming {
        let mut columns: Vec<Monomial<N>> = preprocessed.monomials.to_vec();
        columns.sort_unstable_by(|a, b| order.cmp(b, a));
        let column_of: MonomialMap<N, usize> = columns
            .iter()
            .enumerate()
            .map(|(index, monomial)| (*monomial, index))
            .collect();

        let column = |monomial: &Monomial<N>| {
            *column_of
                .get(monomial)
                .expect("every row monomial is a column")
        };

        let mut checksum = 0u64;
        let mut sparse_rows: Vec<SparseRow<F>> = Vec::new();
        let started = Instant::now();
        match prefix {
            ScatterPrefix::Shift => {
                for row in &preprocessed.rows {
                    for (monomial, coefficient) in
                        basis.shifted_terms(row.basis_index, &row.multiplier)
                    {
                        black_box(coefficient);
                        checksum = checksum.wrapping_add(monomial.degree());
                    }
                }
            }
            ScatterPrefix::ShiftAndLookup => {
                for row in &preprocessed.rows {
                    for (monomial, coefficient) in
                        basis.shifted_terms(row.basis_index, &row.multiplier)
                    {
                        black_box(coefficient);
                        // The degree is added here too, so that differencing the two arms leaves
                        // the map lookup and nothing else.
                        checksum = checksum.wrapping_add(monomial.degree());
                        checksum = checksum.wrapping_add(column(&monomial) as u64);
                    }
                }
            }
            ScatterPrefix::Row => {
                // Byte-for-byte the shipping loop, so this arm is comparable against
                // `build_measured`'s `scatter_rows` on the same build. The checksum is taken
                // afterwards, outside the clock, for the same reason.
                sparse_rows = Vec::with_capacity(preprocessed.rows.len());
                for row in &preprocessed.rows {
                    let entries: Vec<(usize, F)> = basis
                        .shifted_terms(row.basis_index, &row.multiplier)
                        .map(|(monomial, coefficient)| (column(&monomial), coefficient))
                        .collect();
                    sparse_rows.push(SparseRow::from_sorted_unchecked(entries));
                }
                black_box(&sparse_rows);
            }
        }
        let elapsed = started.elapsed();

        if prefix == ScatterPrefix::Row {
            for built in &sparse_rows {
                for (index, _) in built.entries() {
                    checksum = checksum.wrapping_add(*index as u64);
                }
            }
        }

        ScatterPrefixTiming { elapsed, checksum }
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

    use super::{BuildBudgetExceeded, ConstructionTimings, MacaulayMatrix, ScatterPrefix};
    use crate::{
        fields::Zp13,
        grobner::{
            f4::symbolic::{symbolic_preprocessing, MonicBasis, Preprocessed},
            pairs::CriticalPair,
        },
        poly::{MonomialOrder, MonomialSet, WeightedOrder, WeightedTieBreak},
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

    /// The basis and the preprocessed batch of every pair of a system under one order.
    fn batch(strings: &[&str], order: MonomialOrder) -> (MonicBasis<3, F>, Preprocessed<3>) {
        let polynomials = system(strings);
        let basis = MonicBasis::new(&polynomials, order);
        let mut pairs = Vec::new();
        for left in 0..polynomials.len() {
            for right in (left + 1)..polynomials.len() {
                pairs.push(CriticalPair::new(&polynomials, left, right, order));
            }
        }
        let preprocessed = symbolic_preprocessing(&basis, &pairs);
        (basis, preprocessed)
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

    /// The sorted column order is a function of the column *set*, not of the order the monomials
    /// are handed over in.
    ///
    /// This is what licenses the unstable sort in `build_measured` (#583). An unstable sort may
    /// permute elements its comparator calls equal, so it is deterministic here only because the
    /// comparator calls no two distinct columns equal — a monomial order is strict on distinct
    /// monomials. Sorting several permutations of a real column set and demanding the one answer
    /// says so directly: were the order ever made non-strict, or the column set ever to admit a
    /// duplicate, this goes red and the sort's output would depend on the hash set's iteration
    /// order.
    ///
    /// Covers a weighted order as well as the three built-in ones, because `MonomialOrder` is
    /// reachable here in all its variants and a tie-break is exactly where strictness would be
    /// lost. All three tie-breaks, since they differ only on ties.
    #[test]
    fn test_the_column_order_does_not_depend_on_the_handout_order() {
        static WEIGHTED_LEX: WeightedOrder =
            WeightedOrder::new(&[1, 7, 49], WeightedTieBreak::Lexicographic);
        static WEIGHTED_REVLEX: WeightedOrder =
            WeightedOrder::new(&[3, 1, 2], WeightedTieBreak::ReverseLexicographic);
        static WEIGHTED_LAST: WeightedOrder =
            WeightedOrder::new(&[1, 7, 49], WeightedTieBreak::LastVariableFirst);

        let systems: Vec<Vec<&str>> = vec![
            vec!["x + y + z", "x*y + x*z + y*z", "x*y*z - 1"],
            vec!["x^3 - y", "x^2 - z", "x - y*z", "y^2 - 1"],
            vec!["x*z - y^2", "x^3 - z^2"],
        ];
        let orders: Vec<MonomialOrder> = ALL_ORDERS
            .into_iter()
            .chain([
                MonomialOrder::Weighted(&WEIGHTED_LEX),
                MonomialOrder::Weighted(&WEIGHTED_REVLEX),
                MonomialOrder::Weighted(&WEIGHTED_LAST),
            ])
            .collect();

        for order in orders {
            for strings in &systems {
                let (_, matrix) = build(strings, order);
                let sorted = matrix.columns().to_vec();
                assert!(
                    sorted.len() > 2,
                    "{:?}: too few columns to permute",
                    strings
                );

                let half = sorted.len() / 2;
                let mut permutations: Vec<Vec<Monomial<3>>> = Vec::new();
                permutations.push(sorted.iter().rev().copied().collect());
                permutations.push({
                    let mut rotated = sorted.clone();
                    rotated.rotate_left(half);
                    rotated
                });
                permutations.push(
                    sorted[half..]
                        .iter()
                        .zip(&sorted[..half])
                        .flat_map(|(high, low)| [*high, *low])
                        .chain(sorted[2 * half..].iter().copied())
                        .collect(),
                );

                for mut permutation in permutations {
                    assert_eq!(
                        permutation.len(),
                        sorted.len(),
                        "{:?} under {}: the permutation lost a column",
                        strings,
                        order.name()
                    );
                    assert_ne!(
                        permutation,
                        sorted,
                        "{:?} under {}: the permutation is the sorted order already, so it \
                         establishes nothing",
                        strings,
                        order.name()
                    );
                    permutation.sort_unstable_by(|a, b| order.cmp(b, a));
                    assert_eq!(
                        permutation,
                        sorted,
                        "{:?} under {}: the column order depends on the handout order",
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

    /// Symbolic preprocessing's monomial arena is exactly the matrix's column set, with no repeats.
    ///
    /// This is the invariant #330's column handout rests on: if it holds, construction can take
    /// the set preprocessing already interned instead of hashing every row monomial a second time.
    /// Asserted over every order and over a batch with reducer rows, because the arena is grown in
    /// two places — the seed rows' terms and each reducer row's terms as it is admitted — and a
    /// batch with no reducers would exercise only the first.
    ///
    /// Distinctness is asserted and not assumed, because since #621 the arena is a `Vec` whose
    /// indices are the handles the scatter reads columns through: a repeated monomial would give
    /// one column two handles, and the `column_of` array would then disagree with itself.
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
            let interned: MonomialSet<3> = preprocessed.monomials.iter().copied().collect();
            assert_eq!(interned, built, "{}", order.name());
            assert_eq!(
                interned.len(),
                preprocessed.monomials.len(),
                "{}: the arena repeats a monomial",
                order.name()
            );
        }
    }

    /// Every row term's handle names the monomial that term actually becomes, in row-major order.
    ///
    /// The layout `build_measured` reads is implied rather than stored — a row's handles are the
    /// next `terms.len()` of one flat vector — so the thing that can go wrong is an off-by-one that
    /// shifts every later row. Walking the vector independently and comparing against
    /// `shifted_terms` is what catches that; the length check catches a run that is short or long.
    #[test]
    fn test_term_handles_name_every_row_term_in_row_order() {
        for order in ALL_ORDERS {
            let (basis, preprocessed) = batch(&["x^3 - y", "x^2 - z", "x - y*z", "y^2 - 1"], order);

            let mut offset = 0usize;
            for (index, row) in preprocessed.rows.iter().enumerate() {
                for (term, (monomial, _)) in basis
                    .shifted_terms(row.basis_index, &row.multiplier)
                    .enumerate()
                {
                    let handle = preprocessed.term_handles[offset + term];
                    assert_eq!(
                        preprocessed.monomials[handle as usize],
                        monomial,
                        "{}: row {} term {} has the wrong handle",
                        order.name(),
                        index,
                        term
                    );
                }
                offset += basis.element(row.basis_index).terms.len();
            }
            assert_eq!(
                offset,
                preprocessed.term_handles.len(),
                "{}: the handle vector is not one run per row",
                order.name()
            );
        }
    }

    /// The handle scatter and the pre-#621 hashing scatter return the identical matrix.
    ///
    /// This is what makes the A/B in `examples/f4_profile handles` a measurement of cost rather
    /// than of two different matrices, and it is the differential test the restructuring is pinned
    /// by: equality of the whole `MacaulayMatrix` covers the columns, their order, every row's
    /// entries and the row provenance, which is everything elimination and extraction read. Over a
    /// weighted order too, because the handle is carried through the sort by a comparator that
    /// ignores it and #306's variants are where a comparator can stop being strict.
    #[test]
    fn test_the_two_scatter_routes_agree() {
        static WEIGHTED: WeightedOrder =
            WeightedOrder::new(&[1, 7, 49], WeightedTieBreak::Lexicographic);

        let systems: Vec<Vec<&str>> = vec![
            vec!["x^3 - y", "x^2 - z", "x - y*z", "y^2 - 1"],
            vec!["x + y + z", "x*y + x*z + y*z", "x*y*z - 1"],
            vec!["3*x^2 + 5*y", "7*x*y + 11*y", "2*y^2 - 1"],
            vec!["x^2*y + z", "y^2*z + x", "x*z^2 + y", "x*y*z - 1"],
        ];
        let orders: Vec<MonomialOrder> = ALL_ORDERS
            .into_iter()
            .chain([MonomialOrder::Weighted(&WEIGHTED)])
            .collect();

        for order in orders {
            for strings in &systems {
                let (basis, preprocessed) = batch(strings, order);
                let handles = MacaulayMatrix::<3, F>::build(&basis, &preprocessed, order);
                let (hashed, _) = MacaulayMatrix::<3, F>::build_hashed_scatter_for_benchmark(
                    &basis,
                    &preprocessed,
                    order,
                    false,
                );
                assert_eq!(handles, hashed, "{:?} under {}", strings, order.name());
                assert!(
                    handles.nonzeros() > 0,
                    "{:?} under {}: an empty matrix establishes nothing",
                    strings,
                    order.name()
                );
            }
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

    /// Releasing the interning products empties the arena *and* the handles, and leaves the rest
    /// of the batch's data intact.
    ///
    /// The handles are the larger of the two by the column density, so #536's release discipline is
    /// what keeps #621 from trading a hash pass for a working-set increase; a `release_monomials`
    /// that freed only the arena would leave `num_nonzeros` words live through elimination.
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
        assert!(preprocessed.term_handles.len() > preprocessed.monomials.len());

        preprocessed.release_monomials();
        assert!(preprocessed.monomials.is_empty());
        assert!(preprocessed.term_handles.is_empty());
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

    /// The scatter's two clocked halves partition the scatter lap.
    #[test]
    fn test_the_scatter_halves_partition_the_scatter() {
        for order in ALL_ORDERS {
            let (basis, preprocessed) = batch(&["x^3 - y", "x^2 - z", "x - y*z", "y^2 - 1"], order);
            let (_, split) = MacaulayMatrix::<3, F>::build_measured(
                &basis,
                &preprocessed,
                order,
                usize::MAX,
                usize::MAX,
                true,
            )
            .expect("an unbounded construction cannot exceed its budget");

            assert_eq!(
                split.scatter_rows + split.scatter_assemble,
                split.scatter,
                "{}",
                order.name()
            );
            assert!(split.scatter_rows > Duration::ZERO, "{}", order.name());
            assert!(
                (0.0..=1.0).contains(&split.assembly_share()),
                "{}",
                order.name()
            );
        }
    }

    /// Each scatter-ablation prefix does the scatter's real work, not a degenerate stand-in.
    ///
    /// The failure mode of an ablation is an arm the optimizer emptied, which still reports a
    /// plausible time. Each arm's checksum is therefore compared against the same quantity derived
    /// independently from the matrix `build` returns: the shift arm against the summed degrees of
    /// the monomial behind every entry, the two column arms against the summed column indices.
    #[test]
    fn test_the_scatter_ablation_arms_do_the_scatters_work() {
        for order in ALL_ORDERS {
            let (basis, preprocessed) = batch(&["x^3 - y", "x^2 - z", "x - y*z", "y^2 - 1"], order);
            let matrix = MacaulayMatrix::<3, F>::build(&basis, &preprocessed, order);

            let mut degrees = 0u64;
            let mut indices = 0u64;
            for index in 0..matrix.num_rows() {
                for (column, _) in matrix.matrix().row(index).entries() {
                    degrees = degrees.wrapping_add(matrix.columns()[*column].degree());
                    indices = indices.wrapping_add(*column as u64);
                }
            }

            let checksum = |prefix| {
                MacaulayMatrix::<3, F>::scatter_prefix_for_benchmark(
                    &basis,
                    &preprocessed,
                    order,
                    prefix,
                )
                .checksum
            };
            assert_eq!(checksum(ScatterPrefix::Shift), degrees, "{}", order.name());
            assert_eq!(
                checksum(ScatterPrefix::ShiftAndLookup),
                degrees.wrapping_add(indices),
                "{}",
                order.name()
            );
            assert_eq!(checksum(ScatterPrefix::Row), indices, "{}", order.name());
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

    // Construction succeeds at the exact column and entry demand and refuses one below it.
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

            // The construction demand is exact even when the matrix is refused.
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

    // A refused construction reports the full entry demand independently of the entry allowance.
    #[test]
    fn test_refused_construction_reports_full_entry_demand() {
        for order in ALL_ORDERS {
            let (basis, preprocessed) = batch(&["x^3 - y", "x^2 - z", "x - y*z", "y^2 - 1"], order);
            let full = MacaulayMatrix::build(&basis, &preprocessed, order);
            assert!(full.nonzeros() > 4);
            for limit in [0, 1, full.nonzeros() / 2, full.nonzeros() - 1] {
                assert_eq!(
                    MacaulayMatrix::build_within(&basis, &preprocessed, order, usize::MAX, limit),
                    Err(BuildBudgetExceeded::Nonzeros {
                        nonzeros: full.nonzeros(),
                        limit,
                    }),
                    "{} with allowance {limit}",
                    order.name()
                );
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
