//! Concatenate matrices into block matrices.

use crate::{
    linalg::matrix::{Error, Matrix},
    Ring,
};

impl<T: Ring> Matrix<T> {
    /// `[self | other]`: this matrix with `other`'s columns appended to the right.
    ///
    /// # Errors
    /// * `IncompatibleShapes` if the two matrices do not have the same number of rows.
    pub fn hconcat(&self, other: &Self) -> Result<Self, Error> {
        if self.num_rows != other.num_rows {
            return Err(Error::IncompatibleShapes {
                left: self.shape(),
                right: other.shape(),
            });
        }

        let num_columns = self.num_columns + other.num_columns;
        let mut elements = Vec::with_capacity(self.num_rows * num_columns);
        // The buffer is row-major, so each output row is one row of `self` followed by the
        // corresponding row of `other`.
        for i in 0..self.num_rows {
            elements.extend_from_slice(&self[i]);
            elements.extend_from_slice(&other[i]);
        }

        Ok(Self {
            num_rows: self.num_rows,
            num_columns,
            elements,
        })
    }

    /// `[self; other]`: this matrix with `other`'s rows appended below.
    ///
    /// # Errors
    /// * `IncompatibleShapes` if the two matrices do not have the same number of columns.
    pub fn vconcat(&self, other: &Self) -> Result<Self, Error> {
        if self.num_columns != other.num_columns {
            return Err(Error::IncompatibleShapes {
                left: self.shape(),
                right: other.shape(),
            });
        }

        // The buffer is row-major, so stacking vertically is concatenating the two buffers.
        let mut elements = Vec::with_capacity(self.elements.len() + other.elements.len());
        elements.extend_from_slice(&self.elements);
        elements.extend_from_slice(&other.elements);

        Ok(Self {
            num_rows: self.num_rows + other.num_rows,
            num_columns: self.num_columns,
            elements,
        })
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        fields::Zp541,
        linalg::{Error, Matrix},
        FiniteField,
    };
    use proptest::prelude::*;

    /// `[A | B]` places B's columns to the right of A's, keeping each row intact.
    #[test]
    fn test_hconcat() {
        type F = Zp541;
        let a = matrix![
            F::new(1), F::new(2);
            F::new(3), F::new(4)
        ];
        let b = matrix![
            F::new(5), F::new(6), F::new(7);
            F::new(8), F::new(9), F::new(10)
        ];
        let expected = matrix![
            F::new(1), F::new(2), F::new(5), F::new(6), F::new(7);
            F::new(3), F::new(4), F::new(8), F::new(9), F::new(10)
        ];
        assert_eq!(a.hconcat(&b).unwrap(), expected);
        assert_eq!(a.hconcat(&b).unwrap().shape(), (2, 5));
    }

    /// `[A; B]` places B's rows below A's, keeping each column intact.
    #[test]
    fn test_vconcat() {
        type F = Zp541;
        let a = matrix![
            F::new(1), F::new(2);
            F::new(3), F::new(4)
        ];
        let b = matrix![F::new(5), F::new(6)];
        let expected = matrix![
            F::new(1), F::new(2);
            F::new(3), F::new(4);
            F::new(5), F::new(6)
        ];
        assert_eq!(a.vconcat(&b).unwrap(), expected);
        assert_eq!(a.vconcat(&b).unwrap().shape(), (3, 2));
    }

    /// Horizontal concatenation needs equal row counts, vertical equal column counts, and each
    /// reports both shapes.
    #[test]
    fn test_concat_rejects_mismatched_shapes() {
        type F = Zp541;
        let a: Matrix<F> = Matrix::zero(2, 3);
        let b: Matrix<F> = Matrix::zero(4, 3);

        assert_eq!(
            a.hconcat(&b),
            Err(Error::IncompatibleShapes {
                left: (2, 3),
                right: (4, 3)
            })
        );
        // The same pair stacks vertically, since the column counts agree.
        assert_eq!(a.vconcat(&b).unwrap().shape(), (6, 3));

        let wide: Matrix<F> = Matrix::zero(2, 5);
        assert_eq!(
            a.vconcat(&wide),
            Err(Error::IncompatibleShapes {
                left: (2, 3),
                right: (2, 5)
            })
        );
        assert_eq!(a.hconcat(&wide).unwrap().shape(), (2, 8));
    }

    /// `[A | I]`, the augmented matrix an inversion reduces, built by concatenation.
    #[test]
    fn test_hconcat_builds_an_augmented_matrix() {
        type F = Zp541;
        let a = matrix![
            F::new(2), F::new(1);
            F::new(1), F::new(3)
        ];
        let augmented = a.hconcat(&Matrix::identity(2)).unwrap();
        let expected = matrix![
            F::new(2), F::new(1), F::new(1), F::new(0);
            F::new(1), F::new(3), F::new(0), F::new(1)
        ];
        assert_eq!(augmented, expected);
    }

    /// Concatenating along one axis is the transpose of concatenating the transposes along the
    /// other.
    #[test]
    fn test_hconcat_is_vconcat_of_transposes() {
        type F = Zp541;
        let a = matrix![
            F::new(1), F::new(2), F::new(3);
            F::new(4), F::new(5), F::new(6)
        ];
        let b = matrix![
            F::new(7), F::new(8);
            F::new(9), F::new(10)
        ];
        let by_column = a.hconcat(&b).unwrap();
        let by_row = a.transpose().vconcat(&b.transpose()).unwrap().transpose();
        assert_eq!(by_column, by_row);
    }

    proptest! {
        /// Each block keeps its elements at the expected offset, and the result has the summed
        /// shape, for arbitrary matrices of compatible dimensions.
        #[test]
        fn test_concat_places_each_block(
            (a, b) in (1..=6usize, 1..=6usize, 1..=6usize).prop_flat_map(|(rows, columns_a, columns_b)| {
                (
                    any_with::<Matrix<Zp541>>((rows, columns_a).into()),
                    any_with::<Matrix<Zp541>>((rows, columns_b).into()),
                )
            })
        ) {
            let (rows, columns_a) = a.shape();
            let columns_b = b.num_columns();

            let side_by_side = a.hconcat(&b).unwrap();
            prop_assert_eq!(side_by_side.shape(), (rows, columns_a + columns_b));
            for i in 0..rows {
                for j in 0..columns_a {
                    prop_assert_eq!(side_by_side[[i, j]], a[[i, j]]);
                }
                for j in 0..columns_b {
                    prop_assert_eq!(side_by_side[[i, columns_a + j]], b[[i, j]]);
                }
            }

            // Vertically, the same two blocks need equal column counts, which the transposes have.
            let stacked = a.transpose().vconcat(&b.transpose()).unwrap();
            prop_assert_eq!(stacked.shape(), (columns_a + columns_b, rows));
            prop_assert_eq!(stacked, side_by_side.transpose());
        }
    }

    /// Concatenation is associative, so a three-block matrix is unambiguous.
    #[test]
    fn test_concat_is_associative() {
        type F = Zp541;
        let a = matrix![F::new(1); F::new(2)];
        let b = matrix![F::new(3); F::new(4)];
        let c = matrix![F::new(5); F::new(6)];

        let left = a.hconcat(&b).unwrap().hconcat(&c).unwrap();
        let right = a.hconcat(&b.hconcat(&c).unwrap()).unwrap();
        assert_eq!(left, right);
        assert_eq!(left.shape(), (2, 3));

        let down = a
            .transpose()
            .vconcat(&b.transpose())
            .unwrap()
            .vconcat(&c.transpose())
            .unwrap();
        assert_eq!(down, left.transpose());
    }
}
