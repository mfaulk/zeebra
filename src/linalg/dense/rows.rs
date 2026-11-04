//! A row-major dense matrix, and row echelon over it.
//!
//! Per-row metadata — the first and last column that may hold a nonzero, and the nonzero count —
//! is maintained incrementally, which is what lets the dense path report the same
//! `peak_nonzeros` the sparse path does without rescanning a row after every operation. `lead` is
//! a lower bound on the first nonzero column and `tail` an upper bound on one past the last; both
//! are tightened lazily, because a cancellation inside a row cannot be detected without a scan
//! and the bounds are only used to limit ranges.

use std::collections::HashMap;

use crate::{
    linalg::sparse::{EliminationStatistics, SparseMatrix, SparseRow},
    FiniteField,
};

/// The dense cells a budget of `max_nonzeros` sparse entries licenses, at equal bytes.
///
/// A sparse entry is a column index and a field element; a dense cell is a field element alone.
/// So the same byte budget buys `size_of::<(usize, F)>() / size_of::<F>()` times as many cells —
/// typically three, for a 32-bit field on a 64-bit target.
///
/// This exists because `max_nonzeros` bounds *stored nonzeros*, and a dense representation has no
/// zeros it can decline to store: a matrix that is a fraction of a percent dense satisfies the
/// entry budget comfortably and still needs `rows x columns` field elements. katsura-7 grevlex's
/// largest matrix holds 112 200 entries and would densify to 46.7 million cells — 374 MB — which
/// is what makes the unit conversion necessary rather than pedantic.
///
/// Saturates rather than overflowing: `usize::MAX` entries means unbounded, and converting an
/// unbounded budget into a smaller one would turn "no limit" into "refuse everything".
fn licensed_cells<F: FiniteField>(max_nonzeros: usize) -> usize {
    max_nonzeros.saturating_mul(cells_per_entry::<F>())
}

/// Refuse a densification that would exceed what `max_nonzeros` licenses, before allocating.
///
/// `Err` carries the cell count **converted back into the budget's unit** — sparse entries — so
/// that the count and the limit it is compared against are in the same currency. Reporting raw
/// cells would put a cell count and an entry limit in one error message, which is the very unit
/// confusion this check exists to resolve.
fn check_dense_budget<F: FiniteField>(
    matrix: &SparseMatrix<F>,
    max_nonzeros: usize,
) -> Result<(), usize> {
    // An overflowing cell count cannot be allocated on any machine, so it is refused with the
    // largest count expressible rather than by panicking inside `from_sparse`.
    let cells = matrix
        .num_rows()
        .checked_mul(matrix.num_columns())
        .ok_or(usize::MAX)?;
    if cells <= licensed_cells::<F>(max_nonzeros) {
        return Ok(());
    }

    // Round up, so a matrix needing a fraction over the budget is still reported as over it.
    let per_entry = cells_per_entry::<F>();
    Err(cells / per_entry + usize::from(cells % per_entry != 0))
}

/// Dense cells with the same byte cost as one sparse entry. At least one.
fn cells_per_entry<F: FiniteField>() -> usize {
    let entry = std::mem::size_of::<(usize, F)>();
    let cell = std::mem::size_of::<F>().max(1);
    (entry / cell.min(entry)).max(1)
}

/// A dense matrix of field elements, stored one row after another.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DenseRows<F: FiniteField> {
    num_columns: usize,
    cells: Vec<F>,
    /// A lower bound on each row's first nonzero column; `num_columns` for the zero row.
    lead: Vec<usize>,
    /// An upper bound on one past each row's last nonzero column; `0` for the zero row.
    tail: Vec<usize>,
    /// Each row's exact nonzero count.
    nonzeros: Vec<usize>,
}

impl<F: FiniteField> DenseRows<F> {
    /// Densify a sparse matrix.
    ///
    /// # Panics
    /// If the cell count overflows `usize`.
    pub fn from_sparse(matrix: &SparseMatrix<F>) -> Self {
        let num_columns = matrix.num_columns();
        let num_rows = matrix.num_rows();
        let cell_count = num_rows
            .checked_mul(num_columns)
            .expect("a dense matrix of this shape does not fit in memory");

        let mut cells = vec![F::zero(); cell_count];
        let mut lead = Vec::with_capacity(num_rows);
        let mut tail = Vec::with_capacity(num_rows);
        let mut nonzeros = Vec::with_capacity(num_rows);

        for (index, row) in matrix.rows().iter().enumerate() {
            let base = index * num_columns;
            for (column, coefficient) in row.entries() {
                cells[base + column] = *coefficient;
            }
            lead.push(row.leading_column().unwrap_or(num_columns));
            tail.push(row.trailing_column().map_or(0, |column| column + 1));
            nonzeros.push(row.nonzeros());
        }

        Self {
            num_columns,
            cells,
            lead,
            tail,
            nonzeros,
        }
    }

    /// The sparse equivalent, keeping only the nonzero cells.
    pub fn to_sparse(&self) -> SparseMatrix<F> {
        let rows: Vec<SparseRow<F>> = (0..self.num_rows())
            .map(|index| {
                let base = index * self.num_columns;
                let mut entries: Vec<(usize, F)> = Vec::with_capacity(self.nonzeros[index]);
                for column in self.lead[index]..self.tail[index] {
                    let cell = self.cells[base + column];
                    if !cell.is_zero() {
                        entries.push((column, cell));
                    }
                }
                debug_assert_eq!(entries.len(), self.nonzeros[index]);
                // Columns are visited in increasing order and zeros are skipped, so this is
                // canonical by construction.
                SparseRow::from_sorted_unchecked(entries)
            })
            .collect();
        SparseMatrix::new(self.num_columns, rows)
    }

    pub fn num_rows(&self) -> usize {
        self.nonzeros.len()
    }

    pub fn num_columns(&self) -> usize {
        self.num_columns
    }

    /// The total number of cells that are not zero.
    pub fn nonzeros(&self) -> usize {
        self.nonzeros.iter().sum()
    }

    /// Reduce to row echelon form in place, and report the work done.
    ///
    /// The contract is [`crate::linalg::row_echelon_with`]'s, and the statistics are the sparse
    /// path's statistics: the same pivot rule and the same normalization visit the same entries, so
    /// every counter agrees.
    ///
    /// # Errors
    /// The live nonzero count that crossed `max_nonzeros`.
    pub fn row_echelon_within(
        &mut self,
        max_nonzeros: usize,
    ) -> Result<EliminationStatistics, usize> {
        let initial_nonzeros = self.nonzeros();
        let mut statistics = EliminationStatistics {
            initial_nonzeros,
            peak_nonzeros: initial_nonzeros,
            ..Default::default()
        };
        if initial_nonzeros > max_nonzeros {
            return Err(initial_nonzeros);
        }

        let mut pivot_of_column: HashMap<usize, usize> = HashMap::new();
        let mut resident = initial_nonzeros;
        self.eliminate_from(
            0,
            &mut pivot_of_column,
            &mut statistics,
            &mut resident,
            max_nonzeros,
        )?;
        statistics.final_nonzeros = resident;
        Ok(statistics)
    }

    /// Reduce rows `[split..]` against a pivot map the caller has already validated.
    ///
    /// `statistics` arrives seeded with the input's entry counts and the upper block's rank and
    /// zero-row counts, so that the split and the unsplit paths report the same thing.
    pub(crate) fn reduce_rows_from(
        &mut self,
        split: usize,
        pivot_of_column: &mut HashMap<usize, usize>,
        statistics: &mut EliminationStatistics,
        max_nonzeros: usize,
    ) -> Result<(), usize> {
        let mut resident = statistics.initial_nonzeros;
        self.eliminate_from(
            split,
            pivot_of_column,
            statistics,
            &mut resident,
            max_nonzeros,
        )?;
        statistics.final_nonzeros = resident;
        Ok(())
    }

    /// Rows `[first..]` reduced against `pivot_of_column`, each becoming a pivot if it can.
    ///
    /// `resident` is the nonzero count of every row; the row being worked on is subtracted out of
    /// it and added back, so that the peak is sampled over the same quantity the sparse path
    /// samples.
    fn eliminate_from(
        &mut self,
        first: usize,
        pivot_of_column: &mut HashMap<usize, usize>,
        statistics: &mut EliminationStatistics,
        resident: &mut usize,
        max_nonzeros: usize,
    ) -> Result<(), usize> {
        for index in first..self.num_rows() {
            *resident -= self.nonzeros[index];

            while let Some(column) = self.leading_column(index) {
                match pivot_of_column.get(&column) {
                    Some(&pivot_index) => {
                        // Every pivot's leading coefficient is one, so the factor that clears this
                        // column is this row's own leading coefficient.
                        let factor = self.cells[index * self.num_columns + column];
                        self.subtract_scaled(index, pivot_index, factor);
                        statistics.row_operations += 1;
                        let live = *resident + self.nonzeros[index];
                        statistics.peak_nonzeros = statistics.peak_nonzeros.max(live);
                        if live > max_nonzeros {
                            return Err(live);
                        }
                    }
                    None => {
                        if self.normalize(index) {
                            statistics.pivot_inversions += 1;
                        }
                        pivot_of_column.insert(column, index);
                        statistics.rank += 1;
                        break;
                    }
                }
            }

            if self.nonzeros[index] == 0 {
                statistics.zero_rows += 1;
            }
            *resident += self.nonzeros[index];
            statistics.peak_nonzeros = statistics.peak_nonzeros.max(*resident);
        }
        Ok(())
    }

    /// The row's first nonzero column, tightening the stored lower bound on the way.
    fn leading_column(&mut self, index: usize) -> Option<usize> {
        if self.nonzeros[index] == 0 {
            self.lead[index] = self.num_columns;
            self.tail[index] = 0;
            return None;
        }
        let base = index * self.num_columns;
        let mut column = self.lead[index];
        // `lead` is a lower bound and the row holds a nonzero, so this terminates inside the row.
        while self.cells[base + column].is_zero() {
            column += 1;
        }
        self.lead[index] = column;
        Some(column)
    }

    /// `row[target] -= factor * row[source]`, over the source's span.
    ///
    /// The loop body is branch-free, which is what lets a compiler widen it. Two branches used to
    /// be here and both were removable without changing a single counter:
    ///
    /// An early `continue` skipped a zero `scaled`. Subtracting zero leaves `after == before`, so
    /// the store is a no-op and neither transition below fires — running the body anyway gives the
    /// same cells and the same counts. The branch bought one subtraction and one store on a zero
    /// source cell and cost a mispredictable test on every cell.
    ///
    /// A two-predicate `match` maintained the nonzero count. It is now the same two predicates
    /// combined with `&` rather than `&&`, so neither operand is short-circuited and the
    /// increments are a zero-extension of a flag rather than a jump. The arithmetic is unchanged:
    /// a cell gains a nonzero exactly when it was zero and is not, and loses one exactly when it
    /// was not zero and now is.
    fn subtract_scaled(&mut self, target: usize, source: usize, factor: F) {
        debug_assert_ne!(target, source, "a row cannot be its own pivot");
        let start = self.lead[source];
        let end = self.tail[source];

        let mut gained = 0usize;
        let mut lost = 0usize;
        {
            let (target_cells, source_cells) =
                two_rows_mut(&mut self.cells, self.num_columns, target, source);
            for column in start..end {
                let before = target_cells[column];
                let after = before - factor * source_cells[column];
                target_cells[column] = after;

                let was_zero = before.is_zero();
                let is_zero = after.is_zero();
                gained += usize::from(was_zero & !is_zero);
                lost += usize::from(!was_zero & is_zero);
            }
        }

        self.nonzeros[target] = self.nonzeros[target] + gained - lost;
        self.tail[target] = self.tail[target].max(end);
        self.lead[target] = self.lead[target].min(start);
    }

    /// Scale the row so its leading coefficient is one, reporting whether an inverse was needed.
    ///
    /// One inverse for the row, not one division per cell: `inverse` is a modular exponentiation
    /// of about log2(q) multiplications.
    ///
    /// Scaling is unconditional. Skipping a zero cell was a branch that saved a multiplication and
    /// prevented the loop from being widened; zero times anything is zero, so the test decided
    /// nothing. Scaling cannot change which cells are zero either, since `inverse` is nonzero and
    /// a field has no zero divisors, so no count is affected.
    fn normalize(&mut self, index: usize) -> bool {
        let lead = self.lead[index];
        if lead >= self.num_columns {
            return false;
        }
        let base = index * self.num_columns;
        let coefficient = self.cells[base + lead];
        if coefficient == F::ONE {
            return false;
        }
        let inverse = coefficient.inverse();
        for column in lead..self.tail[index] {
            self.cells[base + column] *= inverse;
        }
        debug_assert_eq!(self.cells[base + lead], F::ONE);
        true
    }
}

/// Two distinct rows of a row-major buffer, one mutable.
///
/// `split_at_mut` rather than index arithmetic, so the disjointness is the borrow checker's
/// conclusion rather than this function's claim.
fn two_rows_mut<F: FiniteField>(
    cells: &mut [F],
    num_columns: usize,
    target: usize,
    source: usize,
) -> (&mut [F], &[F]) {
    assert_ne!(target, source, "rows must be distinct to be borrowed apart");
    if target < source {
        let (upper, lower) = cells.split_at_mut(source * num_columns);
        let base = target * num_columns;
        (&mut upper[base..base + num_columns], &lower[..num_columns])
    } else {
        let (upper, lower) = cells.split_at_mut(target * num_columns);
        let base = source * num_columns;
        (&mut lower[..num_columns], &upper[base..base + num_columns])
    }
}

/// [`crate::linalg::row_echelon_with`] over dense rows.
///
/// Both budgets are tested before the matrix is densified, so a refused elimination does not pay
/// for a representation it is not going to use — and, more to the point, does not allocate a
/// gigabyte in order to discover it was not allowed to. On failure `matrix` is left as it arrived;
/// the contract says the caller must not read it, and this backend has nothing partial to hand
/// back.
pub(crate) fn dense_row_echelon<F: FiniteField>(
    matrix: &mut SparseMatrix<F>,
    max_nonzeros: usize,
) -> Result<EliminationStatistics, usize> {
    let initial_nonzeros = matrix.nonzeros();
    if initial_nonzeros > max_nonzeros {
        return Err(initial_nonzeros);
    }
    check_dense_budget(matrix, max_nonzeros)?;

    let mut dense = DenseRows::from_sparse(matrix);
    let statistics = dense.row_echelon_within(max_nonzeros)?;
    *matrix = dense.to_sparse();

    debug_assert_eq!(statistics.final_nonzeros, matrix.nonzeros());
    debug_assert_eq!(statistics.rank, matrix.nonzero_rows());
    debug_assert_eq!(statistics.rank + statistics.zero_rows, matrix.num_rows());
    Ok(statistics)
}

/// [`crate::linalg::reduce_rows_against_pivots_with`] over dense rows.
pub(crate) fn dense_reduce_rows_against_pivots<F: FiniteField>(
    matrix: &mut SparseMatrix<F>,
    split: usize,
    pivot_of_column: &mut HashMap<usize, usize>,
    statistics: &mut EliminationStatistics,
    max_nonzeros: usize,
) -> Result<(), usize> {
    check_dense_budget(matrix, max_nonzeros)?;
    let mut dense = DenseRows::from_sparse(matrix);
    dense.reduce_rows_from(split, pivot_of_column, statistics, max_nonzeros)?;
    *matrix = dense.to_sparse();
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::{check_dense_budget, licensed_cells};

    use super::DenseRows;
    use crate::{
        fields::Zp13,
        linalg::sparse::{row_echelon, SparseMatrix, SparseRow},
        FiniteField,
    };
    use rand::{prelude::StdRng, Rng, SeedableRng};

    type F = Zp13;

    fn matrix_of(rows: &[&[(usize, u64)]], num_columns: usize) -> SparseMatrix<F> {
        let rows: Vec<SparseRow<F>> = rows
            .iter()
            .map(|entries| {
                SparseRow::new(
                    &entries
                        .iter()
                        .map(|(column, value)| (*column, F::new(*value)))
                        .collect::<Vec<_>>(),
                )
            })
            .collect();
        SparseMatrix::new(num_columns, rows)
    }

    /// Densifying and sparsifying a matrix round-trips, including zero rows and empty columns.
    #[test]
    fn test_sparse_round_trip() {
        let matrix = matrix_of(&[&[(0, 1), (3, 5)], &[], &[(2, 7)]], 4);
        let dense = DenseRows::from_sparse(&matrix);
        assert_eq!(dense.num_rows(), 3);
        assert_eq!(dense.num_columns(), 4);
        assert_eq!(dense.nonzeros(), 3);
        assert_eq!(dense.to_sparse(), matrix);
    }

    /// A matrix with no rows or no columns densifies to nothing and round-trips.
    #[test]
    fn test_degenerate_shapes_round_trip() {
        for (rows, columns) in [(0usize, 0usize), (0, 5), (3, 0)] {
            let matrix = SparseMatrix::<F>::zero(rows, columns);
            let dense = DenseRows::from_sparse(&matrix);
            assert_eq!(dense.nonzeros(), 0, "{}x{}", rows, columns);
            assert_eq!(dense.to_sparse(), matrix, "{}x{}", rows, columns);
        }
    }

    /// The dense echelon produces the sparse echelon's matrix and its statistics, entry for entry.
    #[test]
    fn test_dense_echelon_matches_the_sparse_one() {
        let original = matrix_of(
            &[
                &[(0, 3), (1, 1), (4, 9)],
                &[(0, 3), (1, 1), (4, 9)],
                &[(1, 5), (2, 2)],
                &[(0, 7), (2, 11), (3, 1)],
                &[],
            ],
            5,
        );

        let mut expected = original.clone();
        let reference = row_echelon(&mut expected);

        let mut dense = DenseRows::from_sparse(&original);
        let statistics = dense.row_echelon_within(usize::MAX).expect("unbounded");
        assert_eq!(dense.to_sparse(), expected);
        assert_eq!(statistics, reference);
    }

    /// The dense echelon agrees with the sparse one on random matrices, matrix and statistics both.
    ///
    /// The single hand-written case above does not exercise the counting hard enough. `nonzeros`
    /// is maintained incrementally by `subtract_scaled`, which infers each row's nonzero count
    /// from the transitions it observes rather than recounting, and `peak_nonzeros` is sampled off
    /// that running total. A miscount is invisible in the matrix and shows up only in the
    /// statistics, so both are compared here, against the sparse path as the oracle, over a range
    /// of shapes and densities.
    ///
    /// Low densities matter most: they put long runs of zeros inside a row's `lead..tail` span,
    /// which is the case where an entry contributes nothing and the counting has to agree that it
    /// contributed nothing.
    #[test]
    fn test_dense_echelon_matches_the_sparse_one_on_random_matrices() {
        let mut rng = StdRng::seed_from_u64(0x5EED_1234);

        for &(num_rows, num_columns) in &[(1, 1), (3, 5), (8, 8), (12, 7), (7, 12), (20, 24)] {
            // A density of 1 in 13 leaves wide zero runs; 12 in 13 leaves almost none.
            for &density in &[1u32, 2, 4, 8, 12] {
                for _trial in 0..24 {
                    let rows: Vec<SparseRow<F>> = (0..num_rows)
                        .map(|_| {
                            let mut entries: Vec<(usize, F)> = Vec::new();
                            for column in 0..num_columns {
                                if rng.gen_ratio(density, 13) {
                                    // A zero coefficient would not be stored by a sparse row, so
                                    // the generator must not produce one.
                                    entries.push((column, F::new(rng.gen_range(1..13))));
                                }
                            }
                            SparseRow::new(&entries)
                        })
                        .collect();
                    let original = SparseMatrix::new(num_columns, rows);

                    let mut expected = original.clone();
                    let reference = row_echelon(&mut expected);

                    let mut dense = DenseRows::from_sparse(&original);
                    let statistics = dense.row_echelon_within(usize::MAX).expect("unbounded");

                    assert_eq!(
                        dense.to_sparse(),
                        expected,
                        "matrices disagree at {}x{} density {}/13",
                        num_rows,
                        num_columns,
                        density
                    );
                    assert_eq!(
                        statistics, reference,
                        "statistics disagree at {}x{} density {}/13",
                        num_rows, num_columns, density
                    );
                }
            }
        }
    }

    /// `nonzeros` after a chain of subtractions equals a recount of the row, not an estimate.
    ///
    /// `subtract_scaled` is the only thing that maintains the count, and it is the function this
    /// pins: the invariant it has to preserve is that the stored count equals what counting the
    /// row's nonzero cells would give. `to_sparse` asserts exactly that in a debug build, so
    /// round-tripping is the recount.
    #[test]
    fn test_the_nonzero_count_survives_cancellation() {
        // Row 1 is a multiple of row 0, so eliminating drives it to the zero row — every entry
        // cancels, which is the transition `subtract_scaled` has to count as a loss.
        let original = matrix_of(
            &[
                &[(0, 1), (2, 5), (4, 7)],
                &[(0, 3), (2, 2), (4, 8)],
                &[(0, 1), (1, 1), (2, 5), (3, 1), (4, 7)],
                &[(1, 4), (3, 9)],
            ],
            5,
        );

        let mut expected = original.clone();
        let reference = row_echelon(&mut expected);

        let mut dense = DenseRows::from_sparse(&original);
        let statistics = dense.row_echelon_within(usize::MAX).expect("unbounded");

        // `to_sparse` debug-asserts the stored count against the cells it actually finds.
        assert_eq!(dense.to_sparse(), expected);
        assert_eq!(statistics, reference);
        assert!(
            reference.zero_rows > 0,
            "the fixture should produce a zero row"
        );
    }

    /// A budget below the input count is refused before any cell is touched.
    #[test]
    fn test_budget_below_the_input_is_refused() {
        let original = matrix_of(&[&[(0, 1), (1, 2)], &[(0, 3), (1, 4)]], 2);
        let mut dense = DenseRows::from_sparse(&original);
        assert_eq!(dense.row_echelon_within(3), Err(4));
        assert_eq!(dense.to_sparse(), original, "no work should have been done");
    }

    /// A sparse matrix too wide to densify within the budget is refused before it is allocated.
    ///
    /// The shape here is the pathology the guard exists for: 0.04% dense, comfortably inside an
    /// entry budget, and 4 million cells if densified.
    #[test]
    fn test_a_wide_sparse_matrix_is_refused_before_densifying() {
        let rows: Vec<SparseRow<Zp13>> = (0..2000)
            .map(|i| SparseRow::new(&[(i, Zp13::new(1))]))
            .collect();
        let matrix = SparseMatrix::new(2000, rows);
        assert_eq!(matrix.nonzeros(), 2000);

        // The entry budget is satisfied many times over; the cell count is not.
        assert!(
            licensed_cells::<Zp13>(2000) < 2000 * 2000,
            "the budget should not cover 4M cells"
        );
        // Reported in the budget's unit, not in cells: 4M cells divided by the cells one entry's
        // bytes buy. Whatever the field width, it must exceed the 2000-entry budget.
        let reported = check_dense_budget(&matrix, 2000).expect_err("over budget");
        assert_eq!(reported, 2000 * 2000 / super::cells_per_entry::<Zp13>());
        assert!(
            reported > 2000,
            "the refusal must exceed the limit it names"
        );

        // And the backend refuses rather than allocating it.
        let mut copy = matrix.clone();
        assert_eq!(
            super::dense_row_echelon(&mut copy, 2000),
            Err(reported),
            "the dense path allocated a matrix the budget did not license"
        );
        assert_eq!(
            copy, matrix,
            "a refused elimination must not rewrite the matrix"
        );
    }

    /// The licensed cell count converts the entry budget at equal bytes, not one for one.
    ///
    /// A sparse entry carries a column index as well as a coefficient, so the same bytes buy more
    /// dense cells than sparse entries. Asserted as the ratio rather than a constant, because it
    /// depends on the field's width.
    #[test]
    fn test_licensed_cells_converts_at_equal_bytes() {
        let entry = std::mem::size_of::<(usize, Zp13)>();
        let cell = std::mem::size_of::<Zp13>();
        assert_eq!(licensed_cells::<Zp13>(1_000), 1_000 * (entry / cell));
        assert!(
            licensed_cells::<Zp13>(1_000) >= 1_000,
            "a dense cell is never larger than a sparse entry"
        );
        // An unbounded budget stays unbounded: saturating here rather than overflowing is what
        // keeps `usize::MAX` meaning "no limit" instead of "refuse everything".
        assert_eq!(licensed_cells::<Zp13>(usize::MAX), usize::MAX);
        assert_eq!(
            check_dense_budget(&SparseMatrix::<Zp13>::zero(4, 4), usize::MAX),
            Ok(())
        );
    }

    /// A matrix that fits is accepted, so the guard does not refuse the ordinary case.
    #[test]
    fn test_a_matrix_within_the_budget_is_accepted() {
        let matrix = SparseMatrix::new(
            8,
            (0..8)
                .map(|i| SparseRow::new(&[(i, Zp13::new(1))]))
                .collect(),
        );
        assert_eq!(check_dense_budget(&matrix, 64), Ok(()));
        let mut copy = matrix.clone();
        assert!(super::dense_row_echelon(&mut copy, 64).is_ok());
    }
}
