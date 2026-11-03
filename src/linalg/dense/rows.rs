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
                let scaled = factor * source_cells[column];
                if scaled.is_zero() {
                    continue;
                }
                let before = target_cells[column];
                let after = before - scaled;
                target_cells[column] = after;
                match (before.is_zero(), after.is_zero()) {
                    (true, false) => gained += 1,
                    (false, true) => lost += 1,
                    _ => {}
                }
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
            let cell = &mut self.cells[base + column];
            if !cell.is_zero() {
                *cell *= inverse;
            }
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
/// The budget is tested before the matrix is densified, so a refused elimination does not pay for
/// a representation it is not going to use. On failure `matrix` is left as it arrived; the contract
/// says the caller must not read it, and this backend has nothing partial to hand back.
pub(crate) fn dense_row_echelon<F: FiniteField>(
    matrix: &mut SparseMatrix<F>,
    max_nonzeros: usize,
) -> Result<EliminationStatistics, usize> {
    let initial_nonzeros = matrix.nonzeros();
    if initial_nonzeros > max_nonzeros {
        return Err(initial_nonzeros);
    }

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
    let mut dense = DenseRows::from_sparse(matrix);
    dense.reduce_rows_from(split, pivot_of_column, statistics, max_nonzeros)?;
    *matrix = dense.to_sparse();
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::DenseRows;
    use crate::{
        fields::Zp13,
        linalg::sparse::{row_echelon, SparseMatrix, SparseRow},
        FiniteField,
    };

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

    /// A budget below the input count is refused before any cell is touched.
    #[test]
    fn test_budget_below_the_input_is_refused() {
        let original = matrix_of(&[&[(0, 1), (1, 2)], &[(0, 3), (1, 4)]], 2);
        let mut dense = DenseRows::from_sparse(&original);
        assert_eq!(dense.row_echelon_within(3), Err(4));
        assert_eq!(dense.to_sparse(), original, "no work should have been done");
    }
}
