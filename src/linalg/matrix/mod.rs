//! Dense matrix.

#![allow(non_snake_case)]

use crate::{
    linalg::matrix::iterating::{RowIterator, RowsIterator},
    FiniteField, Ring,
};
use proptest::{
    arbitrary::any,
    collection::vec,
    prelude::{Arbitrary, BoxedStrategy, Strategy},
};
use std::fmt::{Debug, Display, Formatter};
mod arithmetic_ops;
mod error;
mod indexing;
mod iterating;
mod matrix_scalar_ops;
mod matrix_vector_ops;
mod special;

use crate::linalg::{
    crout_lu_pivoting,
    matrix::iterating::{RowIteratorMut, RowsIteratorMut},
};
pub use error::*;
pub use special::*;

/// A Dense matrix.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Matrix<T: Ring> {
    /// Number of rows in the matrix.
    pub num_rows: usize,

    /// Number of columns in the matrix.
    pub num_columns: usize,

    /// Elements of the matrix, in row-major order.
    pub(crate) elements: Vec<T>,
}

impl<T: Ring> Matrix<T> {
    /// Create a new matrix with the given elements.
    ///
    /// # Arguments
    /// * `elements` - The data to initialize the matrix with, in row-major order.
    ///
    /// # Panics
    /// * If the number of elements does not agree with the number of rows and columns.
    pub fn new(num_rows: usize, num_columns: usize, elements: &[T]) -> Self {
        assert_eq!(
            num_rows * num_columns,
            elements.len(),
            "num_rows: {}, num_columns: {}, elements.len(): {}",
            num_rows,
            num_columns,
            elements.len()
        );
        Self {
            num_rows,
            num_columns,
            elements: elements.to_vec(),
        }
    }

    /// A matrix whose elements are all zero.
    pub fn zero(num_rows: usize, num_columns: usize) -> Self {
        Self {
            num_rows,
            num_columns,
            elements: vec![T::ZERO; num_rows * num_columns],
        }
    }

    /// The nxn identity matrix.
    pub fn identity(n: usize) -> Self {
        let mut data = vec![T::ZERO; n * n];
        for i in 0..n {
            data[i * n + i] = T::ONE;
        }
        Self {
            num_rows: n,
            num_columns: n,
            elements: data,
        }
    }

    /// Create a square matrix with the given diagonal elements.
    pub fn from_diag(diag: &[T]) -> Self {
        let num_rows = diag.len();
        let num_columns = num_rows;
        let mut elements = vec![T::ZERO; num_rows * num_columns];
        for i in 0..num_rows {
            elements[i * num_columns + i] = diag[i];
        }
        Self {
            num_rows,
            num_columns,
            elements,
        }
    }

    /// Transpose this matrix.
    pub fn transpose(&self) -> Self {
        let mut elements = vec![T::ZERO; self.num_rows * self.num_columns];
        for i in 0..self.num_rows {
            for j in 0..self.num_columns {
                elements[j * self.num_rows + i] = self.elements[i * self.num_columns + j];
            }
        }
        Self {
            num_rows: self.num_columns,
            num_columns: self.num_rows,
            elements,
        }
    }

    /// The inverse, if any, of this matrix.
    pub fn inverse<R: Ring>(&self) -> Result<Matrix<R>, ()> {
        todo!()
    }

    /// The submatrix of this matrix consisting of the given rows and columns.
    ///
    /// # Arguments
    /// * `rows` - Set of row indices to include. No duplicates, please.
    /// * `columns` - Set of column indices to include. No duplicates, please.
    ///
    /// # Panics
    /// * If any row or column index is out of bounds.
    pub fn submatrix(&self, rows: &[usize], columns: &[usize]) -> Self {
        let num_rows = rows.len();
        let num_columns = columns.len();
        let mut m = Matrix::zero(num_rows, num_columns);
        for (i, row) in rows.iter().enumerate() {
            for (j, column) in columns.iter().enumerate() {
                m[[i, j]] = self[[*row, *column]];
            }
        }
        m
    }

    /// The number of rows and columns in the matrix.
    pub fn shape(&self) -> (usize, usize) {
        (self.num_rows, self.num_columns)
    }

    /// The number of rows in the matrix.
    pub fn num_rows(&self) -> usize {
        self.num_rows
    }

    /// The number of columns in the matrix.
    pub fn num_columns(&self) -> usize {
        self.num_columns
    }

    /// The rank (number of linearly independent columns) of the matrix.
    pub fn rank<R: Ring>(_m: &Matrix<R>) -> usize {
        todo!()
    }

    /// The elements of the matrix, in row-major order.
    pub fn elements(&self) -> &[T] {
        &self.elements
    }

    /// The elements of the given row.
    pub fn row(&self, row_index: usize) -> RowIterator<T> {
        assert!(
            row_index < self.num_rows,
            "row_index: {}, num_rows: {}",
            row_index,
            self.num_rows
        );
        RowIterator::new(self, row_index)
    }

    /// The elements of the given row, as mutable references.
    ///
    /// # Panics
    /// * If the row index is out of bounds.
    pub fn row_mut(&mut self, row_index: usize) -> RowIteratorMut<T> {
        assert!(row_index < self.num_rows, "row_index: {}", row_index);
        RowIteratorMut::new(self, row_index)
    }

    /// Iterate over the rows of the matrix.
    pub fn rows(&self) -> RowsIterator<T> {
        RowsIterator::new(self)
    }

    /// Iterate over the rows of the matrix, as mutable references.
    pub fn rows_mut(&mut self) -> RowsIteratorMut<T> {
        RowsIteratorMut::new(self)
    }

    /// Swap two rows of the matrix.
    ///
    /// # Panics
    /// * If either row index is out of bounds.
    pub fn swap_rows(&mut self, i: usize, j: usize) {
        assert!(i < self.num_rows, "i: {}", i);
        assert!(j < self.num_rows, "j: {}", j);
        for k in 0..self.num_columns {
            let tmp = self[[i, k]];
            self[[i, k]] = self[[j, k]];
            self[[j, k]] = tmp;
        }
    }

    /// Apply a function to each element of the matrix.
    pub fn apply(&self, f: fn(&T) -> T) -> Self {
        let elements = self.elements.iter().map(f).collect();
        Self {
            num_rows: self.num_rows,
            num_columns: self.num_columns,
            elements,
        }
    }

    /// True if the matrix is square.
    pub fn is_square(&self) -> bool {
        self.num_rows == self.num_columns
    }
}

impl<F: FiniteField> Matrix<F> {
    /// The determinant of the matrix.
    pub fn determinant(&self) -> Result<F, ()> {
        if !self.is_square() {
            return Err(());
        }
        let mut det = F::ONE;
        // Compute the determinant via LU decomposition.
        match crout_lu_pivoting(&self) {
            Ok((L, U, _P)) => {
                for i in 0..self.num_rows {
                    det = det * U[[i, i]] * L[[i, i]];
                }
                // TODO: Each row exchange changes the sign of the determinant.
                // Compute the parity of the permutation.
            }
            Err(Error::NotInvertible) => {
                det = F::ZERO;
            }
            _ => {
                return Err(());
            }
        }
        Ok(det)
    }
}

/// Implement Display for Matrix.
impl<T: Ring + 'static> Display for Matrix<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "{}x{} matrix:", self.num_rows, self.num_columns)?;
        // TODO: Do not print all elements of large matrices.

        for row_index in 0..self.num_rows {
            let row = self.row(row_index).collect::<Vec<&T>>();
            let row_str = row
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<String>>()
                .join(", ");
            writeln!(f, "[ {} ]", row_str)?;
        }
        Ok(())
    }
}

/// Implement Arbitrary
impl<T: Ring + 'static> Arbitrary for Matrix<T> {
    type Parameters = (usize, usize); // (num_rows, num_columns)

    fn arbitrary_with(args: Self::Parameters) -> Self::Strategy {
        let (num_rows, num_columns) = args;

        vec(any::<T>(), num_rows * num_columns)
            .prop_map(move |elements| Matrix::new(num_rows, num_columns, &elements))
            .boxed()
    }

    type Strategy = BoxedStrategy<Self>;
}

#[cfg(test)]
mod tests {
    use crate::{
        fields::{Zp1091, Zp541},
        FiniteField,
    };
    use proptest::prelude::*;

    proptest! {
        #[test]
        // (A^T)^T = A
        fn test_transpose_twice_is_identity(m in (1..=10usize, 1..=10usize).prop_flat_map(any_with::<super::Matrix::<Zp541>>))
        {
            let m_t_t = m.transpose().transpose();
            assert_eq!(m, m_t_t);
        }
    }

    #[test]
    // Spot-check that swapping rows works.
    fn test_swap_rows() {
        type F = Zp541;
        let elements: Vec<F> = (1..=9u64).map(|x| F::new(x)).collect();
        let mut m = super::Matrix::new(3, 3, &elements);
        m.swap_rows(0, 1);
        let expected: Vec<F> = vec![
            F::new(4),
            F::new(5),
            F::new(6),
            F::new(1),
            F::new(2),
            F::new(3),
            F::new(7),
            F::new(8),
            F::new(9),
        ];
        assert_eq!(m, super::Matrix::new(3, 3, &expected));
    }

    #[test]
    // Should return a matrix of the selected rows and columns.
    fn test_submatrix() {
        type F = Zp1091;

        let matrix = super::Matrix::new(
            3,
            3,
            &[
                F::new(1),
                F::new(2),
                F::new(3),
                F::new(4),
                F::new(5),
                F::new(6),
                F::new(7),
                F::new(8),
                F::new(9),
            ],
        );

        let submatrix = matrix.submatrix(&[0, 2], &[1, 2]);
        let expected = super::Matrix::new(2, 2, &[F::new(2), F::new(3), F::new(8), F::new(9)]);
        assert_eq!(submatrix, expected);
    }

    #[test]
    fn test_determinant() {
        // sage: A = matrix(GF(541), 3, [1,1,2, 8,4,3, 539,2,540])
        // sage: A.det()
        // 40
        //
        // sage: B = matrix(GF(541), 3, [8,4,3, 1,1,2, 539,2,540])
        // sage: B.det()
        // 501
        //
        // sage: C = matrix(GF(541), 3, [8,4,3, 1,1,2, 8,4,3])
        // sage: C.det()
        // 0

        type F = Zp541;
        let A = super::Matrix::new(
            3,
            3,
            &[
                F::new(1),
                F::new(1),
                F::new(2),
                F::new(8),
                F::new(4),
                F::new(3),
                F::new(539),
                F::new(2),
                F::new(540),
            ],
        );
        assert_eq!(A.determinant(), Ok(F::new(40)));

        let B = super::Matrix::new(
            3,
            3,
            &[
                F::new(8),
                F::new(4),
                F::new(3),
                F::new(1),
                F::new(1),
                F::new(2),
                F::new(539),
                F::new(2),
                F::new(540),
            ],
        );
        assert_eq!(B.determinant(), Ok(F::new(501)));

        let C = super::Matrix::new(
            3,
            3,
            &[
                F::new(8),
                F::new(4),
                F::new(3),
                F::new(1),
                F::new(1),
                F::new(2),
                F::new(8),
                F::new(4),
                F::new(3),
            ],
        );
        assert_eq!(C.determinant(), Ok(F::new(0)));
    }
}
