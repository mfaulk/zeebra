//! A sparse matrix over a finite field: a vector of sparse rows plus a column count.
//!
//! Deliberately not CSR. Elimination rewrites rows wholesale and changes their sparsity on every
//! operation, so a single packed array of entries would have to be rebuilt each time; a vector of
//! independently grown rows pays nothing for that.

use crate::{
    linalg::{sparse::row::SparseRow, Matrix},
    FiniteField,
};

/// A sparse matrix with `num_columns` columns and one `SparseRow` per row.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SparseMatrix<F: FiniteField> {
    num_columns: usize,
    rows: Vec<SparseRow<F>>,
}

impl<F: FiniteField> SparseMatrix<F> {
    /// A matrix of the given rows.
    ///
    /// Only the last stored column of each row is range-checked, because a `SparseRow` keeps its
    /// entries strictly increasing by column and so the last one is the largest. That invariant is
    /// enforced by every `SparseRow` constructor in every build — see
    /// [`SparseRow::from_sorted`] — and the `debug_assert` below is what keeps this function's
    /// reliance on it from becoming silent if that ever changes.
    ///
    /// # Panics
    /// If any row holds a column index at or beyond `num_columns`.
    pub fn new(num_columns: usize, rows: Vec<SparseRow<F>>) -> Self {
        for (index, row) in rows.iter().enumerate() {
            debug_assert!(
                row.is_canonical(),
                "row {} is not a canonical sparse row: {:?}",
                index,
                row.entries()
            );
            if let Some(column) = row.trailing_column() {
                assert!(
                    column < num_columns,
                    "row {} holds column {} in a matrix of {} columns",
                    index,
                    column,
                    num_columns
                );
            }
        }
        Self { num_columns, rows }
    }

    /// A matrix of zero rows.
    pub fn zero(num_rows: usize, num_columns: usize) -> Self {
        Self {
            num_columns,
            rows: vec![SparseRow::zero(); num_rows],
        }
    }

    pub fn num_rows(&self) -> usize {
        self.rows.len()
    }

    pub fn num_columns(&self) -> usize {
        self.num_columns
    }

    pub fn rows(&self) -> &[SparseRow<F>] {
        &self.rows
    }

    pub fn row(&self, index: usize) -> &SparseRow<F> {
        &self.rows[index]
    }

    /// The rows, mutably. Used by elimination, which is the only thing that rewrites them.
    pub(crate) fn rows_mut(&mut self) -> &mut Vec<SparseRow<F>> {
        &mut self.rows
    }

    /// The total number of nonzero entries stored.
    pub fn nonzeros(&self) -> usize {
        self.rows.iter().map(|row| row.nonzeros()).sum()
    }

    /// The fraction of entries that are nonzero, or zero for a matrix with no entries at all.
    pub fn density(&self) -> f64 {
        let cells = self.num_rows() * self.num_columns;
        if cells == 0 {
            0.0
        } else {
            self.nonzeros() as f64 / cells as f64
        }
    }

    /// The number of rows that are not the zero row.
    pub fn nonzero_rows(&self) -> usize {
        self.rows.iter().filter(|row| !row.is_zero()).count()
    }

    /// Sort the rows by leading column, ascending, with the zero rows last.
    ///
    /// Elimination leaves every nonzero row with a distinct leading column but in the order the
    /// rows arrived. Sorting turns that into a row echelon form proper, which is what the
    /// comparison against the dense implementation needs. The sort is stable and the leading
    /// columns are distinct, so the result is unique.
    pub fn sort_rows_by_leading_column(&mut self) {
        self.rows.sort_by_key(|row| match row.leading_column() {
            Some(column) => (0, column),
            None => (1, 0),
        });
    }

    /// The dense equivalent of this matrix.
    pub fn to_dense(&self) -> Matrix<F> {
        let mut elements: Vec<F> = Vec::with_capacity(self.num_rows() * self.num_columns);
        for row in &self.rows {
            elements.extend(row.to_dense(self.num_columns));
        }
        Matrix::new(self.num_rows(), self.num_columns, &elements)
    }

    /// The sparse equivalent of a dense matrix, keeping only the nonzero entries.
    pub fn from_dense(matrix: &Matrix<F>) -> Self {
        let rows: Vec<SparseRow<F>> = (0..matrix.num_rows())
            .map(|index| {
                let dense: Vec<F> = matrix.row(index).copied().collect();
                SparseRow::from_dense(&dense)
            })
            .collect();
        Self {
            num_columns: matrix.num_columns(),
            rows,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::SparseMatrix;
    use crate::{fields::Zp13, linalg::sparse::SparseRow, linalg::Matrix, FiniteField, Zero};

    type F = Zp13;

    /// Dimensions, nonzero counts, and density are read off the stored rows.
    #[test]
    fn test_shape_and_density() {
        let matrix = SparseMatrix::new(
            4,
            vec![
                SparseRow::new(&[(0, F::new(1)), (3, F::new(2))]),
                SparseRow::zero(),
                SparseRow::new(&[(1, F::new(5))]),
            ],
        );
        assert_eq!(matrix.num_rows(), 3);
        assert_eq!(matrix.num_columns(), 4);
        assert_eq!(matrix.nonzeros(), 3);
        assert_eq!(matrix.nonzero_rows(), 2);
        assert_eq!(matrix.density(), 3.0 / 12.0);
    }

    /// A matrix with no cells has zero density rather than dividing by zero.
    #[test]
    fn test_empty_matrix_density() {
        assert_eq!(SparseMatrix::<F>::zero(0, 0).density(), 0.0);
        assert_eq!(SparseMatrix::<F>::zero(0, 5).density(), 0.0);
        assert_eq!(SparseMatrix::<F>::zero(5, 0).density(), 0.0);
    }

    /// A row holding a column outside the declared width is rejected at construction.
    #[test]
    #[should_panic(expected = "holds column 7")]
    fn test_column_out_of_range_panics() {
        let _ = SparseMatrix::new(4, vec![SparseRow::new(&[(7, F::new(1))])]);
    }

    /// Dense and sparse representations round-trip, including zero rows and columns.
    #[test]
    fn test_dense_round_trip() {
        let dense: Matrix<F> = Matrix::new(
            3,
            3,
            &[
                F::new(1),
                F::zero(),
                F::new(2),
                F::zero(),
                F::zero(),
                F::zero(),
                F::new(3),
                F::new(4),
                F::zero(),
            ],
        );
        let sparse = SparseMatrix::from_dense(&dense);
        assert_eq!(sparse.nonzeros(), 4);
        assert_eq!(sparse.to_dense(), dense);
    }

    /// Sorting orders the nonzero rows by leading column and sends zero rows to the bottom.
    #[test]
    fn test_sort_rows_by_leading_column() {
        let mut matrix = SparseMatrix::new(
            5,
            vec![
                SparseRow::new(&[(3, F::new(1))]),
                SparseRow::zero(),
                SparseRow::new(&[(0, F::new(1))]),
                SparseRow::new(&[(1, F::new(1))]),
                SparseRow::zero(),
            ],
        );
        matrix.sort_rows_by_leading_column();
        let leading: Vec<Option<usize>> = matrix
            .rows()
            .iter()
            .map(|row| row.leading_column())
            .collect();
        assert_eq!(leading, vec![Some(0), Some(1), Some(3), None, None]);
    }
}
