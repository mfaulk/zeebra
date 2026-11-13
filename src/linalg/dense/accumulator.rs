//! Dense scratch preserves zero cells outside `[lead, tail)`; the matrix and pivots stay sparse.

use crate::{
    linalg::{
        sparse::{EliminationStatistics, SparseMatrix, SparseRow},
        PivotIndex,
    },
    FiniteField,
};

/// A dense row used as the working register of a sparse elimination.
#[derive(Clone, Debug)]
pub struct DenseAccumulator<F: FiniteField> {
    cells: Vec<F>,
    lead: usize,
    tail: usize,
    nonzeros: usize,
}

impl<F: FiniteField> DenseAccumulator<F> {
    /// An accumulator holding the zero row of the given width.
    pub fn new(num_columns: usize) -> Self {
        Self {
            cells: vec![F::zero(); num_columns],
            lead: num_columns,
            tail: 0,
            nonzeros: 0,
        }
    }

    /// The number of cells the accumulator spans.
    pub fn num_columns(&self) -> usize {
        self.cells.len()
    }

    /// The number of cells that are not zero.
    pub fn nonzeros(&self) -> usize {
        self.nonzeros
    }

    /// Scatter a sparse row in.
    ///
    /// # Panics
    /// If the accumulator is not the zero row, which would silently add the two.
    pub fn load(&mut self, row: &SparseRow<F>) {
        assert_eq!(self.nonzeros, 0, "the accumulator still holds a row");
        #[cfg(feature = "research-work")]
        crate::linalg::work::counters(|work| {
            work.rows_loaded += 1;
            work.dense_load_entries += row.nonzeros();
        });
        for (column, coefficient) in row.entries() {
            self.cells[*column] = *coefficient;
        }
        self.lead = row.leading_column().unwrap_or(self.cells.len());
        self.tail = row.trailing_column().map_or(0, |column| column + 1);
        self.nonzeros = row.nonzeros();
    }

    /// Gather the row back out, leaving the accumulator zero.
    pub fn take(&mut self) -> SparseRow<F> {
        #[cfg(feature = "research-work")]
        crate::linalg::work::counters(|work| {
            work.dense_gather_cells += self.tail.saturating_sub(self.lead);
            work.dense_gather_entries += self.nonzeros;
            work.rows_zero += usize::from(self.nonzeros == 0);
        });
        let mut entries: Vec<(usize, F)> = Vec::with_capacity(self.nonzeros);
        for column in self.lead..self.tail {
            let cell = std::mem::replace(&mut self.cells[column], F::zero());
            if !cell.is_zero() {
                entries.push((column, cell));
            }
        }
        debug_assert_eq!(entries.len(), self.nonzeros);
        self.lead = self.cells.len();
        self.tail = 0;
        self.nonzeros = 0;
        // Columns ascend and zeros are skipped, so this is canonical by construction.
        SparseRow::from_sorted_unchecked(entries)
    }

    /// The first nonzero column, tightening the stored lower bound on the way.
    pub fn leading_column(&mut self) -> Option<usize> {
        if self.nonzeros == 0 {
            self.lead = self.cells.len();
            self.tail = 0;
            return None;
        }
        let mut column = self.lead;
        // `lead` is a lower bound and a nonzero exists, so this terminates inside the buffer.
        while self.cells[column].is_zero() {
            column += 1;
        }
        #[cfg(feature = "research-work")]
        crate::linalg::work::counters(|work| work.dense_scan_cells += column - self.lead + 1);
        self.lead = column;
        Some(column)
    }

    /// The coefficient in the first nonzero column, or `None` for the zero row.
    ///
    /// Reads the stored bound rather than scanning, so it is only correct after
    /// [`DenseAccumulator::leading_column`].
    pub fn leading_coefficient(&self) -> Option<F> {
        if self.nonzeros == 0 {
            return None;
        }
        Some(self.cells[self.lead])
    }

    /// `self -= factor * row`, in time proportional to the row's support.
    pub fn subtract_scaled(&mut self, row: &SparseRow<F>, factor: F) {
        if factor.is_zero() || row.is_zero() {
            return;
        }
        #[cfg(feature = "research-work")]
        crate::linalg::work::pivot(row.nonzeros());
        for (column, coefficient) in row.entries() {
            // A field has no zero divisors and a sparse row stores no zero coefficient, so the
            // scaled entry is nonzero and the inner loop needs no test for it.
            debug_assert!(!coefficient.is_zero(), "a stored coefficient is zero");
            let before = self.cells[*column];
            let after = before - factor * *coefficient;
            self.cells[*column] = after;
            self.nonzeros += usize::from(before.is_zero());
            self.nonzeros -= usize::from(after.is_zero());
        }
        if let Some(column) = row.leading_column() {
            self.lead = self.lead.min(column);
        }
        if let Some(column) = row.trailing_column() {
            self.tail = self.tail.max(column + 1);
        }
    }

    /// Scale so the leading coefficient is one, reporting whether an inverse was needed.
    ///
    /// Scaling is unconditional, as in `crate::linalg::dense::rows`: zero times anything is
    /// zero, so testing for a zero cell decided nothing and only kept the loop from being widened.
    /// `inverse` is nonzero and a field has no zero divisors, so scaling cannot change which cells
    /// are zero and `nonzeros` is unaffected.
    pub fn normalize(&mut self) -> bool {
        let Some(coefficient) = self.leading_coefficient() else {
            return false;
        };
        if coefficient == F::ONE {
            return false;
        }
        // One inverse for the row, not one division per cell.
        let inverse = coefficient.inverse();
        #[cfg(feature = "research-work")]
        crate::linalg::work::counters(|work| work.normalized_cells += self.tail - self.lead);
        for column in self.lead..self.tail {
            self.cells[column] *= inverse;
        }
        debug_assert_eq!(self.cells[self.lead], F::ONE);
        true
    }
}

/// [`crate::linalg::row_echelon_with`] with sparse pivots and a dense working row.
pub(crate) fn accumulated_row_echelon<F: FiniteField>(
    matrix: &mut SparseMatrix<F>,
    max_nonzeros: usize,
) -> Result<EliminationStatistics, usize> {
    let initial_nonzeros = matrix.nonzeros();
    let mut statistics = EliminationStatistics {
        initial_nonzeros,
        peak_nonzeros: initial_nonzeros,
        ..Default::default()
    };
    if initial_nonzeros > max_nonzeros {
        return Err(initial_nonzeros);
    }

    let mut pivot_of_column = PivotIndex::new(matrix.num_columns(), matrix.num_rows());
    let mut resident = initial_nonzeros;
    let mut accumulator = DenseAccumulator::new(matrix.num_columns());
    eliminate_from(
        matrix,
        0,
        &mut pivot_of_column,
        &mut statistics,
        &mut resident,
        &mut accumulator,
        max_nonzeros,
    )?;

    statistics.final_nonzeros = resident;
    debug_assert_eq!(statistics.final_nonzeros, matrix.nonzeros());
    debug_assert_eq!(statistics.rank, matrix.nonzero_rows());
    debug_assert_eq!(statistics.rank + statistics.zero_rows, matrix.num_rows());
    Ok(statistics)
}

/// [`crate::linalg::reduce_rows_against_pivots_with`] with sparse pivots and a dense working row.
pub(crate) fn accumulated_reduce_rows_against_pivots<F: FiniteField>(
    matrix: &mut SparseMatrix<F>,
    split: usize,
    pivot_of_column: &mut PivotIndex,
    statistics: &mut EliminationStatistics,
    max_nonzeros: usize,
) -> Result<(), usize> {
    let mut resident = statistics.initial_nonzeros;
    let mut accumulator = DenseAccumulator::new(matrix.num_columns());
    eliminate_from(
        matrix,
        split,
        pivot_of_column,
        statistics,
        &mut resident,
        &mut accumulator,
        max_nonzeros,
    )?;
    statistics.final_nonzeros = resident;
    Ok(())
}

/// Rows `[first..]` reduced through `accumulator` against `pivot_of_column`.
fn eliminate_from<F: FiniteField>(
    matrix: &mut SparseMatrix<F>,
    first: usize,
    pivot_of_column: &mut PivotIndex,
    statistics: &mut EliminationStatistics,
    resident: &mut usize,
    accumulator: &mut DenseAccumulator<F>,
    max_nonzeros: usize,
) -> Result<(), usize> {
    #[cfg(feature = "research-work")]
    let mut allocated = if crate::linalg::work::enabled() {
        matrix.entry_capacity()
    } else {
        0
    };
    #[cfg(feature = "research-work")]
    crate::linalg::work::memory(
        *resident,
        allocated,
        accumulator.cells.capacity() * std::mem::size_of::<F>(),
        0,
        std::mem::size_of::<(usize, F)>(),
    );
    for index in first..matrix.num_rows() {
        #[cfg(feature = "research-work")]
        let _discovery = crate::linalg::work::discovery_row(index);
        // Taken out so the pivot rows, which are still in the matrix, can be read while this one
        // is rewritten. A pivot's index is always one already processed, so never this one.
        let row = std::mem::take(&mut matrix.rows_mut()[index]);
        *resident -= row.nonzeros();
        #[cfg(feature = "research-work")]
        let (original_entries, original_capacity) = (row.nonzeros(), row.capacity());
        #[cfg(feature = "research-work")]
        crate::linalg::work::target(index);
        accumulator.load(&row);

        while let Some(column) = accumulator.leading_column() {
            #[cfg(feature = "research-work")]
            crate::linalg::work::discovery_pivot(
                column,
                pivot_of_column.pivot_of(column),
                first,
                pivot_of_column
                    .pivot_of(column)
                    .map_or(0, |pivot| matrix.row(pivot).nonzeros()),
            );
            match pivot_of_column.pivot_of(column) {
                Some(pivot_index) => {
                    // Every pivot's leading coefficient is one, so the factor that clears this
                    // column is this row's own leading coefficient.
                    let factor = accumulator
                        .leading_coefficient()
                        .expect("a row with a leading column has a leading coefficient");
                    accumulator.subtract_scaled(matrix.row(pivot_index), factor);
                    statistics.row_operations += 1;
                    let live = *resident + accumulator.nonzeros();
                    statistics.peak_nonzeros = statistics.peak_nonzeros.max(live);
                    if live > max_nonzeros {
                        return Err(live);
                    }
                }
                None => {
                    if accumulator.normalize() {
                        statistics.pivot_inversions += 1;
                    }
                    pivot_of_column.insert(column, index);
                    statistics.rank += 1;
                    break;
                }
            }
        }

        let row = accumulator.take();
        #[cfg(feature = "research-work")]
        crate::linalg::work::discovery_finish(row.leading_column());
        #[cfg(feature = "research-work")]
        {
            // The loaded input row still owns its buffer until this iteration ends.
            crate::linalg::work::memory(
                *resident + original_entries + row.nonzeros(),
                allocated + row.capacity(),
                accumulator.cells.capacity() * std::mem::size_of::<F>(),
                0,
                std::mem::size_of::<(usize, F)>(),
            );
            allocated = allocated.saturating_sub(original_capacity) + row.capacity();
        }
        if row.is_zero() {
            statistics.zero_rows += 1;
        }
        *resident += row.nonzeros();
        statistics.peak_nonzeros = statistics.peak_nonzeros.max(*resident);
        matrix.rows_mut()[index] = row;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::DenseAccumulator;
    use crate::{fields::Zp13, linalg::sparse::SparseRow, FiniteField, One};

    type F = Zp13;

    fn row(entries: &[(usize, u64)]) -> SparseRow<F> {
        SparseRow::new(
            &entries
                .iter()
                .map(|(column, value)| (*column, F::new(*value)))
                .collect::<Vec<_>>(),
        )
    }

    /// Loading and taking a row round-trips and leaves the accumulator zero again.
    #[test]
    fn test_load_and_take_round_trip() {
        let mut accumulator = DenseAccumulator::<F>::new(8);
        let original = row(&[(1, 3), (5, 7)]);
        accumulator.load(&original);
        assert_eq!(accumulator.nonzeros(), 2);
        assert_eq!(accumulator.take(), original);
        assert_eq!(accumulator.nonzeros(), 0);
        assert_eq!(accumulator.take(), SparseRow::zero());
    }

    /// Loading over a row that was not taken out is rejected rather than summing the two.
    #[test]
    #[should_panic(expected = "still holds a row")]
    fn test_load_over_a_live_row_panics() {
        let mut accumulator = DenseAccumulator::<F>::new(4);
        accumulator.load(&row(&[(0, 1)]));
        accumulator.load(&row(&[(1, 1)]));
    }

    /// Subtracting a scaled row tracks the leading column and the nonzero count exactly.
    #[test]
    fn test_subtract_scaled_tracks_the_support() {
        let mut accumulator = DenseAccumulator::<F>::new(6);
        accumulator.load(&row(&[(0, 2), (3, 1)]));

        // Clearing column 0 with a pivot that also touches columns 2 and 5.
        accumulator.subtract_scaled(&row(&[(0, 1), (2, 4), (5, 1)]), F::new(2));
        assert_eq!(accumulator.leading_column(), Some(2));
        assert_eq!(accumulator.nonzeros(), 3);
        assert_eq!(accumulator.take(), row(&[(2, 5), (3, 1), (5, 11)]));
    }

    /// Subtracting a row from itself with factor one empties the accumulator.
    #[test]
    fn test_self_subtraction_cancels() {
        let mut accumulator = DenseAccumulator::<F>::new(16);
        let original = row(&[(0, 5), (7, 9), (15, 12)]);
        accumulator.load(&original);
        accumulator.subtract_scaled(&original, F::ONE);
        assert_eq!(accumulator.nonzeros(), 0);
        assert_eq!(accumulator.leading_column(), None);
        assert_eq!(accumulator.take(), SparseRow::zero());
    }

    /// Normalizing divides through by the leading coefficient and reports the inverse it needed.
    #[test]
    fn test_normalize() {
        let mut accumulator = DenseAccumulator::<F>::new(5);
        accumulator.load(&row(&[(1, 5), (3, 2)]));
        assert_eq!(accumulator.leading_column(), Some(1));
        assert!(accumulator.normalize(), "an inverse was required");
        // 5 inverse mod 13 is 8, and 2 * 8 = 3.
        assert_eq!(accumulator.take(), row(&[(1, 1), (3, 3)]));

        let mut monic = DenseAccumulator::<F>::new(5);
        monic.load(&row(&[(1, 1), (3, 7)]));
        assert_eq!(monic.leading_column(), Some(1));
        assert!(!monic.normalize(), "no inverse should have been computed");
        assert_eq!(monic.take(), row(&[(1, 1), (3, 7)]));
    }

    /// A zero-width accumulator holds the zero row and never reports a leading column.
    #[test]
    fn test_zero_width() {
        let mut accumulator = DenseAccumulator::<F>::new(0);
        assert_eq!(accumulator.num_columns(), 0);
        accumulator.load(&SparseRow::zero());
        assert_eq!(accumulator.leading_column(), None);
        assert_eq!(accumulator.take(), SparseRow::zero());
    }
}
