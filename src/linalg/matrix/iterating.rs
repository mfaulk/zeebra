//! Iterate over the rows and columns of a matrix.

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

/// Iterator over the elements of a column.
///
/// The buffer is row-major, so consecutive elements of a column lie `num_columns` apart. The
/// iterator walks that stride, which is why reading a column does not cost a whole `transpose()`.
#[derive(Clone, Copy, Debug)]
pub struct ColumnIterator<'a, T: Ring> {
    /// The matrix's row-major buffer.
    elements: &'a [T],

    /// Index into `elements` of the next element to yield. Only meaningful while `remaining > 0`:
    /// it runs one stride past the end of the buffer after the last element is taken.
    next: usize,

    /// Distance in the buffer between consecutive elements of the column.
    stride: usize,

    /// Number of elements left to yield.
    remaining: usize,
}

impl<'a, T: Ring> ColumnIterator<'a, T> {
    pub fn new(matrix: &'a Matrix<T>, column_index: usize) -> Self {
        Self {
            elements: &matrix.elements,
            next: column_index,
            stride: matrix.num_columns,
            remaining: matrix.num_rows,
        }
    }
}

impl<'a, T: Ring> Iterator for ColumnIterator<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.remaining == 0 {
            return None;
        }
        let element = &self.elements[self.next];
        self.next += self.stride;
        self.remaining -= 1;
        Some(element)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.remaining, Some(self.remaining))
    }
}

impl<T: Ring> ExactSizeIterator for ColumnIterator<'_, T> {}

/// Iterator over the columns of a matrix.
pub struct ColumnsIterator<'a, T: Ring> {
    matrix: &'a Matrix<T>,
    column_index: usize,
}

impl<'a, T: Ring> ColumnsIterator<'a, T> {
    /// Create a new iterator over all columns of a matrix.
    pub fn new(matrix: &'a Matrix<T>) -> Self {
        Self {
            matrix,
            column_index: 0,
        }
    }
}

impl<'a, T: Ring> Iterator for ColumnsIterator<'a, T> {
    type Item = ColumnIterator<'a, T>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.column_index == self.matrix.num_columns {
            None
        } else {
            let result = ColumnIterator::new(self.matrix, self.column_index);
            self.column_index += 1;
            Some(result)
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.matrix.num_columns - self.column_index;
        (remaining, Some(remaining))
    }
}

impl<T: Ring> ExactSizeIterator for ColumnsIterator<'_, T> {}

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
    // Spot check that a column can be iterated correctly.
    fn test_iterate_column() {
        type F = Zp541;
        let m = get_matrix::<F>(3, 4);
        let column_two_elements: Vec<F> = m.column(2).cloned().collect();
        let expected = vec![F::new(2), F::new(6), F::new(10)];
        assert_eq!(column_two_elements, expected);
    }

    #[test]
    // A column iterator knows how many elements remain, before and after advancing.
    fn test_column_iterator_reports_its_length() {
        type F = Zp541;
        let m = get_matrix::<F>(3, 4);
        let mut column = m.column(0);
        assert_eq!(column.len(), 3);
        assert_eq!(column.size_hint(), (3, Some(3)));
        column.next();
        assert_eq!(column.len(), 2);
        assert_eq!(column.count(), 2);
    }

    #[test]
    #[should_panic(expected = "column_index")]
    // Asking for a column past the last one panics rather than reading another row's element.
    fn test_column_out_of_bounds_panics() {
        type F = Zp541;
        let m = get_matrix::<F>(3, 4);
        let _ = m.column(4);
    }

    #[test]
    // Spot check that columns can be iterated correctly.
    fn test_iterate_columns() {
        type F = Zp541;
        let m = get_matrix::<F>(3, 4);
        let column_elements: Vec<Vec<F>> = m
            .columns()
            .map(|column| column.cloned().collect())
            .collect();
        let expected = vec![
            vec![F::new(0), F::new(4), F::new(8)],
            vec![F::new(1), F::new(5), F::new(9)],
            vec![F::new(2), F::new(6), F::new(10)],
            vec![F::new(3), F::new(7), F::new(11)],
        ];
        assert_eq!(column_elements, expected);
    }

    #[test]
    // The columns of a matrix are the rows of its transpose.
    fn test_columns_are_rows_of_the_transpose() {
        type F = Zp541;
        let m = get_matrix::<F>(3, 5);
        let columns: Vec<Vec<F>> = m
            .columns()
            .map(|column| column.cloned().collect())
            .collect();
        let transposed_rows: Vec<Vec<F>> = m
            .transpose()
            .rows()
            .map(|row| row.cloned().collect())
            .collect();
        assert_eq!(columns, transposed_rows);
        assert_eq!(columns.len(), m.num_columns());
    }

    #[test]
    // A matrix with no rows still has its columns, each of them empty.
    fn test_columns_of_a_matrix_with_no_rows() {
        type F = Zp541;
        let m = Matrix::<F>::zero(0, 3);
        assert_eq!(m.columns().count(), 3);
        assert_eq!(m.column(1).count(), 0);
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
