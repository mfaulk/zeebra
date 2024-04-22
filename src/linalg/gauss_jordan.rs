//! Gaussian elimination and Gauss-Jordan elimination.
//!
//! The Gaussian Elimination and Gauss-Jordan Elimination algorithms are used to reduce a
//! system of linear equations to a simpler form, which can be used to find the solutions directly.
//!
//! This module implements Gaussian Elimination with partial pivoting, and is designed for matrices
//! over finite fields, where numerical stability is not a concern.
//!
//! This module also implements Gauss-Jordan elimination for matrices over finite fields, which
//! produces a matrix in reduced row echelon form.

use crate::{linalg::Matrix, FiniteField};

struct Cursor {
    row: usize,
    column: usize,
}

impl Cursor {
    fn new(row: usize, column: usize) -> Self {
        Self { row, column }
    }
}

/// Gaussian Elimination
#[allow(non_snake_case)]
fn gaussian_elimination<T: FiniteField>(matrix: &Matrix<T>) -> Matrix<T> {
    let num_rows = matrix.num_rows();
    let num_columns = matrix.num_columns();
    let mut A = matrix.clone();

    // The algorithm proceeds by iteratively attempting to place a pivot (a non-zero element) at the cursor location.
    // The cursor is initially at the top-left corner of the matrix.
    // Beginning at the cursor position, the algorithm searches for the first nonzero entry at or below the cursor.
    // If a nonzero entry is found, the algorithm swaps the current row with the row containing the nonzero entry.
    // The algorithm then divides the current row by the pivot to make the pivot equal to 1.
    // The algorithm then eliminates the current column by subtracting multiples of the current row from all rows below it.
    // The algorithm then moves the cursor to the next position and repeats the process.
    // The algorithm ends when the cursor exceeds the bounds of the matrix.

    // Initialize the cursor to the top-left corner of the matrix.
    let mut cursor = Cursor::new(0, 0);

    while cursor.row < num_rows && cursor.column < num_columns {
        // Row of the first nonzero entry at or below the cursor, if any.
        let mut pivot_row: Option<usize> = None;
        for i in cursor.row..num_rows {
            if A[[i, cursor.column]] != T::ZERO {
                pivot_row = Some(i);
                break;
            }
        }
        if let Some(pivot_row) = pivot_row {
            if pivot_row != cursor.row {
                // Swap the pivot row with the current row.
                A.swap_rows(cursor.row, pivot_row);
            }
            // The cursor now contains a pivot.
            // Divide the current row by the pivot to make the pivot equal to 1.
            {
                let pivot = A[[cursor.row, cursor.column]];
                for j in cursor.column..num_columns {
                    A[[cursor.row, j]] /= pivot;
                }
            }

            // Eliminate the current column by subtracting multiples of the current row from all rows below it.
            let current_row: Vec<T> = A.row(cursor.row).cloned().collect();
            for i in (cursor.row + 1)..num_rows {
                let factor = A[[i, cursor.column]]; // The pivot is now 1.
                for j in cursor.column..num_columns {
                    A[[i, j]] -= factor * current_row[j]
                }
            }
            cursor.row += 1;
            cursor.column += 1;
        } else {
            // Unable to locate a pivot in this column.
            cursor.column += 1;
        }
    }

    A
}

/// Returns the reduced row echelon form of the given matrix.
#[allow(non_snake_case)]
pub fn gauss_jordan_elimination<T: FiniteField>(matrix: &Matrix<T>) -> Matrix<T> {
    let mut A = gaussian_elimination(matrix);
    let num_rows = A.num_rows();
    let num_columns = A.num_columns();
    for i in (0..num_rows).rev() {
        // Find the first nonzero entry in the row.
        let pivot_column: Option<usize> = A.row(i).position(|&x| x != T::ZERO);

        if let Some(pivot_column) = pivot_column {
            let pivot = A[[i, pivot_column]];
            debug_assert_eq!(pivot, T::ONE, "pivot: {}", pivot);
            let pivot_row: Vec<T> = A.row(i).cloned().collect();

            // Eliminate values above the pivot.
            for k in 0..i {
                let factor = A[[k, pivot_column]] / pivot; // The pivot is now 1.
                for j in 0..num_columns {
                    A[[k, j]] -= factor * pivot_row[j];
                }
            }
        }
    }
    A
}

#[cfg(test)]
mod tests {
    use crate::{
        fields::Zp541,
        linalg::{
            gauss_jordan::{gauss_jordan_elimination, gaussian_elimination},
            is_reduced_row_echelon, Matrix,
        },
        FiniteField,
    };
    use proptest::prelude::*;

    // A pivot is the first nonzero entry of a row.

    #[test]
    // The row echelon form of the identity matrix is the identity matrix.
    fn test_gaussian_elimination_identity_matrix() {
        type F = Zp541;
        let matrix: Matrix<F> = Matrix::identity(3);
        let row_echelon_form = gaussian_elimination(&matrix);
        assert_eq!(row_echelon_form, matrix);
    }

    #[test]
    // Spot-check converting a matrix to RREF using Sage.
    fn test_spotcheck_sage_reduced_row_echelon_form() {
        /*
            Sage's echelon_form() function returns a matrix in reduced row echelon form:

           '''sage
           p = 541
           Fp = GF(p)
           M = Matrix(Fp, [[1, 2, 3], [4, 5, 6], [7, 8, 9]])
           M.echelon_form()
               [  1   0 540]
               [  0   1   2]
               [  0   0   0]

        */

        type F = Zp541;
        let matrix: Matrix<F> = Matrix::new(
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

        let result = gauss_jordan_elimination(&matrix);
        let expected: Matrix<F> = Matrix::new(
            3,
            3,
            &[
                F::new(1),
                F::new(0),
                F::new(540),
                F::new(0),
                F::new(1),
                F::new(2),
                F::new(0),
                F::new(0),
                F::new(0),
            ],
        );
        assert_eq!(result, expected, "{}, {}", result, expected);
    }

    proptest! {
        #[test]
        // Gauss-Jordan elimination should yield a matrix in reduced row echelon form.
        fn test_gauss_jordan_is_rref(m in (1..=10usize, 1..=10usize).prop_flat_map(any_with::<super::Matrix::<Zp541>>))
        {
            let res = gauss_jordan_elimination(&m);
            println!("m: {}", m);
            println!("res: {}", res);
            assert!(is_reduced_row_echelon(&res));
        }
    }

    #[test]
    #[ignore]
    // Does not change a matrix that is already in row echelon form.
    fn test_gaussian_elimination_upper_triangular() {
        type F = Zp541;
        let matrix: Matrix<F> = Matrix::new(
            3,
            3,
            &[
                F::new(1),
                F::new(0),
                F::new(0),
                F::new(0),
                F::new(2),
                F::new(2),
                F::new(0),
                F::new(0),
                F::new(3),
            ],
        );
        let row_echelon_form = gaussian_elimination(&matrix);
        assert_eq!(row_echelon_form, matrix, "{}, {}", row_echelon_form, matrix);
    }

    #[test]
    // ?
    fn test_gaussian_elimination() {
        type F = Zp541;
        let matrix: Matrix<F> = Matrix::new(
            3,
            3,
            &[
                F::new(1),
                F::new(0),
                F::new(0),
                F::new(1),
                F::new(0),
                F::new(1),
                F::new(0),
                F::new(1),
                F::new(1),
            ],
        );
        let row_echelon_form = gaussian_elimination(&matrix);

        let expected: Matrix<F> = Matrix::new(
            3,
            3,
            &[
                F::new(1),
                F::new(0),
                F::new(0),
                //
                F::new(0),
                F::new(1),
                F::new(1),
                //
                F::new(0),
                F::new(0),
                F::new(1),
            ],
        );
        assert_eq!(row_echelon_form, expected);
    }

    #[test]
    #[ignore]
    fn test_gauss_jordan_elimination() {
        todo!()
    }

    // The identity matrix is already in reduced row echelon form.

    // Does not change a matrix that is already in reduced row echelon form.
}
