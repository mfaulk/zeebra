//! Index the elements, rows, and columns of a matrix.

use crate::{linalg::matrix::Matrix, Ring};
use std::ops::{Index, IndexMut};

impl<T: Ring> Index<usize> for Matrix<T> {
    type Output = [T];

    fn index(&self, row: usize) -> &Self::Output {
        assert!(
            row < self.num_rows,
            "index = {}, num_rows = {}",
            row,
            self.num_rows
        );
        &self.elements[row * self.num_columns..(row + 1) * self.num_columns]
    }
}

// Index by [row, column].
impl<T: Ring> Index<[usize; 2]> for Matrix<T> {
    type Output = T;

    fn index(&self, index: [usize; 2]) -> &Self::Output {
        assert!(
            index[0] < self.num_rows,
            "index[0] = {}, num_rows = {}",
            index[0],
            self.num_rows
        );
        assert!(
            index[1] < self.num_columns,
            "index[1] = {}, num_columns = {}",
            index[1],
            self.num_columns
        );

        &self.elements[index[0] * self.num_columns + index[1]]
    }
}

impl<T: Ring> IndexMut<usize> for Matrix<T> {
    fn index_mut(&mut self, index: usize) -> &mut [T] {
        assert!(
            index < self.num_rows,
            "index = {}, num_rows = {}",
            index,
            self.num_rows
        );
        &mut self.elements[index * self.num_columns..(index + 1) * self.num_columns]
    }
}

/// Mutably index by [row, column].
impl<T: Ring> IndexMut<[usize; 2]> for Matrix<T> {
    fn index_mut(&mut self, index: [usize; 2]) -> &mut T {
        assert!(
            index[0] < self.num_rows,
            "index[0] = {}, num_rows = {}",
            index[0],
            self.num_rows
        );
        assert!(
            index[1] < self.num_columns,
            "index[1] = {}, num_columns = {}",
            index[1],
            self.num_columns
        );
        &mut self.elements[index[0] * self.num_columns + index[1]]
    }
}

#[cfg(test)]
mod tests {
    use crate::{fields::Zp541, linalg::matrix::Matrix};
    use proptest::prelude::*;

    proptest! {
        #[test]
        fn test_indexing(m in (1..=10usize, 1..=10usize).prop_flat_map(any_with::<Matrix::<Zp541>>)) {
            let num_rows = m.num_rows;
            let num_columns = m.num_columns;
            for i in 0..num_rows {
                for j in 0..num_columns {
                    assert_eq!(m[[i, j]], m.elements[i * num_columns + j]);
                }
            }
        }
    }
}
