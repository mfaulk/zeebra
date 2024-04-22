//! Iterate over the rows and columns of a matrix.
//!
//! Iterate over:
//! * rows of a matrix.
//! * slice of rows of a matrix.
//! * columns of a matrix.
//! * slice of columns of a matrix.
//! * diagonal of a matrix.

use std::marker::PhantomData;

use crate::{linalg::Matrix, Ring};

/// Iterator over the elements of a row.
#[derive(Clone, Copy, Debug)]
pub struct RowIterator<'a, T: Ring> {
    /// Pointer to the current element.
    here: *const T,

    /// Pointer to the first element after the row.
    end: *const T,

    /// Captures the lifetime of the data that the iterator points to.
    marker: PhantomData<&'a T>,
}

impl<'a, T: Ring> RowIterator<'a, T> {
    pub fn new(matrix: &'a Matrix<T>, row_index: usize) -> Self {
        let here = unsafe { matrix.elements.as_ptr().add(row_index * matrix.num_columns) };
        let end = unsafe { here.add(matrix.num_columns) };
        Self {
            here,
            end,
            marker: PhantomData,
        }
    }
}

impl<'a, T: Ring> Iterator for RowIterator<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.here == self.end {
            None
        } else {
            let result = unsafe { &*self.here };
            self.here = unsafe { self.here.add(1) };
            Some(result)
        }
    }
}

/// Mutable iterator over the elements of a row.
/// This is like RowIterator, but it returns mutable references.
pub struct RowIteratorMut<'a, T: Ring> {
    /// Pointer to the current element.
    here: *mut T,

    /// Pointer to the first element after the row.
    end: *mut T,

    /// Captures the lifetime of the data that the iterator points to.
    marker: PhantomData<&'a mut T>,
}

impl<'a, T: Ring> RowIteratorMut<'a, T> {
    pub fn new(matrix: &mut Matrix<T>, row_index: usize) -> Self {
        let here = unsafe {
            matrix
                .elements
                .as_mut_ptr()
                .add(row_index * matrix.num_columns)
        };
        let end = unsafe { here.add(matrix.num_columns) };
        Self {
            here,
            end,
            marker: PhantomData::<&'a mut T>,
        }
    }
}

impl<'a, T: Ring> Iterator for RowIteratorMut<'a, T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.here == self.end {
            None
        } else {
            let result = unsafe { &mut *self.here };
            self.here = unsafe { self.here.add(1) };
            Some(result)
        }
    }
}

/// Iterator over the rows of a matrix.
pub struct RowsIterator<'a, T: Ring> {
    matrix: &'a Matrix<T>,
    row_index: usize,
}

impl<'a, T: Ring> RowsIterator<'a, T> {
    /// Create a new iterator over all rows of a matrix.
    pub fn new(matrix: &'a Matrix<T>) -> Self {
        Self {
            matrix,
            row_index: 0,
        }
    }
}

impl<'a, T: Ring> Iterator for RowsIterator<'a, T> {
    type Item = RowIterator<'a, T>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.row_index == self.matrix.num_rows {
            None
        } else {
            let result = RowIterator::new(self.matrix, self.row_index);
            self.row_index += 1;
            Some(result)
        }
    }
}

/// Mutable iterator over the rows of a matrix.
pub struct RowsIteratorMut<'a, T: Ring> {
    matrix: &'a mut Matrix<T>,
    row_index: usize,
}

impl<'a, T: Ring> RowsIteratorMut<'a, T> {
    /// Create a new iterator over all rows of a matrix.
    pub fn new(matrix: &'a mut Matrix<T>) -> Self {
        Self {
            matrix,
            row_index: 0,
        }
    }
}

impl<'a, T: Ring> Iterator for RowsIteratorMut<'a, T> {
    type Item = RowIteratorMut<'a, T>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.row_index == self.matrix.num_rows {
            None
        } else {
            let result: RowIteratorMut<T> = RowIteratorMut::new(self.matrix, self.row_index);
            self.row_index += 1;
            Some(result)
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{fields::Zp541, linalg::Matrix, FiniteField};

    /// Create a matrix with the given number of rows and columns. Elements are consecutive.
    fn get_matrix<T: FiniteField>(num_rows: usize, num_columns: usize) -> Matrix<T> {
        let mut matrix = Matrix::zero(num_rows, num_columns);
        for i in 0..num_rows {
            for j in 0..num_columns {
                matrix[[i, j]] = T::new((i * num_columns + j) as u64);
            }
        }
        matrix
    }

    #[test]
    // Spot check that a row can be iterated correctly.
    fn test_iterate_row() {
        type F = Zp541;
        let m = get_matrix::<F>(3, 4);
        let row_one_elements: Vec<F> = m.row(1).cloned().collect();
        let expected = vec![F::new(4), F::new(5), F::new(6), F::new(7)];
        assert_eq!(row_one_elements, expected);
    }

    #[test]
    // Spot check that a row can be iterated and mutated correctly.
    fn test_iterate_row_mut() {
        type F = Zp541;
        let mut m = get_matrix::<F>(3, 4);
        for element in m.row_mut(1) {
            *element += F::new(1);
        }
        let row_one_elements: Vec<F> = m.row(1).cloned().collect();
        let expected = vec![F::new(5), F::new(6), F::new(7), F::new(8)];
        assert_eq!(row_one_elements, expected);
    }

    #[test]
    // Spot check that rows can be iterated correctly.
    fn test_iterate_rows() {
        type F = Zp541;
        let m = get_matrix::<F>(3, 4);
        let row_elements: Vec<Vec<F>> = m.rows().map(|row| row.cloned().collect()).collect();
        let expected = vec![
            vec![F::new(0), F::new(1), F::new(2), F::new(3)],
            vec![F::new(4), F::new(5), F::new(6), F::new(7)],
            vec![F::new(8), F::new(9), F::new(10), F::new(11)],
        ];
        assert_eq!(row_elements, expected);
    }

    #[test]
    // Iterate and mutate each row.
    fn test_iterate_rows_mut() {
        type F = Zp541;
        let mut m = get_matrix::<F>(3, 4);
        for row in m.rows_mut() {
            for element in row {
                *element += F::new(1);
            }
        }

        let row_elements: Vec<Vec<F>> = m.rows().map(|row| row.cloned().collect()).collect();
        let expected = vec![
            vec![F::new(1), F::new(2), F::new(3), F::new(4)],
            vec![F::new(5), F::new(6), F::new(7), F::new(8)],
            vec![F::new(9), F::new(10), F::new(11), F::new(12)],
        ];
        assert_eq!(row_elements, expected);
    }
}
