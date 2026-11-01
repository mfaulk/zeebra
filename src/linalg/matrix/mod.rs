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
    crout_lu_pivoting, gauss_jordan_elimination,
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

    /// The elements of the matrix, in row-major order.
    pub fn elements(&self) -> &[T] {
        &self.elements
    }

    /// The elements of the given row.
    pub fn row(&self, row_index: usize) -> RowIterator<'_, T> {
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
    pub fn row_mut(&mut self, row_index: usize) -> RowIteratorMut<'_, T> {
        assert!(row_index < self.num_rows, "row_index: {}", row_index);
        RowIteratorMut::new(self, row_index)
    }

    /// Iterate over the rows of the matrix.
    pub fn rows(&self) -> RowsIterator<'_, T> {
        RowsIterator::new(self)
    }

    /// Iterate over the rows of the matrix, as mutable references.
    pub fn rows_mut(&mut self) -> RowsIteratorMut<'_, T> {
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
    /// The rank of the matrix: the number of linearly independent rows, equivalently columns.
    pub fn rank(&self) -> usize {
        // Row reduction preserves rank, and in reduced row echelon form every row either holds a
        // pivot or is entirely zero, so the rank is the number of rows that survive.
        let reduced = gauss_jordan_elimination(self);
        (0..reduced.num_rows())
            .filter(|&i| reduced.row(i).any(|x| *x != F::ZERO))
            .count()
    }

    /// The inverse of this matrix.
    ///
    /// # Errors
    /// * `NotSquare` if the matrix is not square.
    /// * `NotInvertible` if the matrix is square but singular.
    pub fn inverse(&self) -> Result<Matrix<F>, Error> {
        if !self.is_square() {
            return Err(Error::NotSquare {
                num_rows: self.num_rows,
                num_columns: self.num_columns,
            });
        }
        let n = self.num_rows;

        // Reduce [A | I]. The row operations that carry A to the identity carry I to A inverse, so
        // the right half of the result is the inverse whenever the left half reduces to I.
        let mut augmented = Matrix::zero(n, 2 * n);
        for i in 0..n {
            for j in 0..n {
                augmented[[i, j]] = self[[i, j]];
            }
            augmented[[i, n + i]] = F::ONE;
        }
        let reduced = gauss_jordan_elimination(&augmented);

        let rows: Vec<usize> = (0..n).collect();
        let left: Vec<usize> = (0..n).collect();
        let right: Vec<usize> = (n..2 * n).collect();

        // A is invertible exactly when its half reduces to the identity; anything else leaves a
        // zero row, meaning the rows were dependent.
        if reduced.submatrix(&rows, &left) != Matrix::identity(n) {
            return Err(Error::NotInvertible);
        }
        Ok(reduced.submatrix(&rows, &right))
    }

    /// The determinant of the matrix.
    // TODO: return `linalg::Error` instead of `()`, which carries no failure detail.
    #[allow(clippy::result_unit_err)]
    pub fn determinant(&self) -> Result<F, ()> {
        if !self.is_square() {
            return Err(());
        }
        let mut det = F::ONE;
        // Compute the determinant via LU decomposition.
        match crout_lu_pivoting(self) {
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
    use super::Matrix;
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
        let elements: Vec<F> = (1..=9u64).map(F::new).collect();
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

    /// The strategy is usable once given dimensions; the default of (0, 0) yields only 0x0.
    #[test]
    fn test_arbitrary_is_not_degenerate() {
        use crate::test_support::{assert_strategy_is_not_degenerate, draw};
        let strategy = (1..=6usize, 1..=6usize).prop_flat_map(any_with::<super::Matrix<Zp541>>);
        assert_strategy_is_not_degenerate(&strategy, "Matrix");
        for m in draw(&strategy, 16) {
            assert!(m.num_rows() > 0 && m.num_columns() > 0);
        }
    }

    /// Rank counts independent rows: zero for the zero matrix, full for the identity, and fewer
    /// than the row count when a row is a combination of the others.
    #[test]
    fn test_rank() {
        type F = Zp541;
        assert_eq!(Matrix::<F>::zero(3, 3).rank(), 0);
        assert_eq!(Matrix::<F>::identity(4).rank(), 4);

        // The second row is twice the first, so only one row is independent.
        let dependent = matrix![F::new(1), F::new(2); F::new(2), F::new(4)];
        assert_eq!(dependent.rank(), 1);

        let full = matrix![F::new(1), F::new(2); F::new(3), F::new(4)];
        assert_eq!(full.rank(), 2);

        // Non-square: rank cannot exceed the smaller dimension.
        let wide = matrix![
            F::new(1), F::new(0), F::new(5);
            F::new(0), F::new(1), F::new(7)
        ];
        assert_eq!(wide.rank(), 2);
        assert_eq!(wide.transpose().rank(), 2);

        // A single zero row drops the rank by one.
        let with_zero_row = matrix![
            F::new(1), F::new(2);
            F::new(0), F::new(0)
        ];
        assert_eq!(with_zero_row.rank(), 1);
    }

    /// A * A^-1 = A^-1 * A = I, and inverting twice returns the original.
    #[test]
    fn test_inverse() {
        type F = Zp541;
        let identity = Matrix::<F>::identity(3);
        assert_eq!(identity.inverse().unwrap(), identity);

        let a = matrix![F::new(1), F::new(2); F::new(3), F::new(4)];
        let a_inverse = a.inverse().unwrap();
        assert_eq!(&a * &a_inverse, Matrix::identity(2));
        assert_eq!(&a_inverse * &a, Matrix::identity(2));
        assert_eq!(a_inverse.inverse().unwrap(), a);

        // A larger case that needs a row swap: the leading entry is zero.
        let needs_pivoting = matrix![
            F::new(0), F::new(1), F::new(0);
            F::new(1), F::new(0), F::new(0);
            F::new(0), F::new(0), F::new(2)
        ];
        let inverse = needs_pivoting.inverse().unwrap();
        assert_eq!(&needs_pivoting * &inverse, Matrix::identity(3));
    }

    /// The computed inverse matches one derived independently over GF(541).
    #[test]
    fn test_inverse_spotcheck() {
        type F = Zp541;
        let a = matrix![
            F::new(2), F::new(1), F::new(1);
            F::new(1), F::new(3), F::new(2);
            F::new(1), F::new(0), F::new(0)
        ];
        let expected = matrix![
            F::new(0),   F::new(0),   F::new(1);
            F::new(539), F::new(1),   F::new(3);
            F::new(3),   F::new(540), F::new(536)
        ];
        assert_eq!(a.inverse().unwrap(), expected);
        assert_eq!(&a * &expected, Matrix::identity(3));
    }

    /// A singular or non-square matrix has no inverse, and says which.
    #[test]
    fn test_inverse_rejects_singular_and_non_square() {
        type F = Zp541;
        let singular = matrix![F::new(1), F::new(2); F::new(2), F::new(4)];
        assert_eq!(singular.rank(), 1);
        assert_eq!(singular.inverse(), Err(super::Error::NotInvertible));

        assert_eq!(
            Matrix::<F>::zero(2, 2).inverse(),
            Err(super::Error::NotInvertible)
        );

        let not_square = matrix![
            F::new(1), F::new(2), F::new(3);
            F::new(4), F::new(5), F::new(6)
        ];
        assert_eq!(
            not_square.inverse(),
            Err(super::Error::NotSquare {
                num_rows: 2,
                num_columns: 3
            })
        );
    }

    proptest! {
        /// Rank is unchanged by transposition and never exceeds either dimension.
        #[test]
        fn test_rank_matches_transpose(
            m in (1..=6usize, 1..=6usize).prop_flat_map(any_with::<super::Matrix<Zp541>>)) {
            let rank = m.rank();
            prop_assert_eq!(rank, m.transpose().rank());
            prop_assert!(rank <= m.num_rows().min(m.num_columns()));
        }

        /// A square matrix is invertible exactly when it has full rank.
        #[test]
        fn test_inverse_exists_iff_full_rank(
            m in (1..=5usize).prop_flat_map(|n| any_with::<super::Matrix<Zp541>>((n, n)))) {
            let n = m.num_rows();
            match m.inverse() {
                Ok(inverse) => {
                    prop_assert_eq!(m.rank(), n);
                    prop_assert_eq!(&m * &inverse, super::Matrix::identity(n));
                }
                Err(e) => {
                    prop_assert_eq!(e, super::Error::NotInvertible);
                    prop_assert!(m.rank() < n);
                }
            }
        }
    }
}
