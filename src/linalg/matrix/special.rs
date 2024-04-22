//! Special types of matrices.

use crate::{linalg::Matrix, FiniteField};

/// A matrix is upper triangular if all elements below the main diagonal are zero. Any number of the
/// elements on the main diagonal can also be zero.
pub fn is_upper_triangular<T: FiniteField>(m: &Matrix<T>) -> bool {
    let num_rows = m.num_rows();
    let num_columns = m.num_columns();
    for i in 0..num_rows {
        for j in 0..num_columns {
            if i > j && m[[i, j]] != T::ZERO {
                return false;
            }
        }
    }
    true
}

/// A matrix is upper unit triangular if all elements below the main diagonal are zero and all
/// elements on the main diagonal are one.
pub fn is_upper_unit_triangular<T: FiniteField>(m: &Matrix<T>) -> bool {
    let num_rows = m.num_rows();
    let num_columns = m.num_columns();
    for i in 0..num_rows {
        for j in 0..num_columns {
            // Elements on the diagonal must be one.
            if i == j {
                if m[[i, j]] != T::ONE {
                    return false;
                }
            }
            // Elements below the diagonal must be zero.
            if i > j && m[[i, j]] != T::ZERO {
                return false;
            }
        }
    }
    true
}

/// A matrix is lower triangular if all elements above the main diagonal are zero. Any number of the
/// elements on the main diagonal can also be zero.
pub fn is_lower_triangular<T: FiniteField>(m: &Matrix<T>) -> bool {
    let num_rows = m.num_rows();
    let num_columns = m.num_columns();
    for i in 0..num_rows {
        for j in 0..num_columns {
            if i < j && m[[i, j]] != T::ZERO {
                return false;
            }
        }
    }
    true
}

/// A matrix is diagonal if all elements not on the main diagonal are zero. Any number of the elements
/// on the main diagonal can also be zero.
pub fn is_diagonal<T: FiniteField>(m: &Matrix<T>) -> bool {
    let num_rows = m.num_rows();
    let num_columns = m.num_columns();
    for i in 0..num_rows {
        for j in 0..num_columns {
            if i != j && m[[i, j]] != T::ZERO {
                return false;
            }
        }
    }
    true
}

/// Returns true if the given matrix is in reduced row echelon form.
///
/// A matrix is in reduced row echelon form if:
/// 1. The first nonzero entry of each row is 1.
/// 2. The first nonzero entry of each row is to the right of the first nonzero entry of the row above.
/// 3. The first nonzero entry of each row is the only nonzero entry in its column.
/// 4. All rows consisting entirely of zeros are at the bottom of the matrix.
pub fn is_reduced_row_echelon<T: FiniteField>(m: &Matrix<T>) -> bool {
    let num_rows = m.num_rows();
    let mut previous_pivot_column: Option<usize> = None;
    // The index of the first row consisting entirely of zeros, if any.
    let mut zero_row: Option<usize> = None;
    for i in 0..num_rows {
        // Column of the first nonzero entry in the row.
        let pivot_column: Option<usize> = m.row(i).position(|&x| x != T::ZERO);

        if let Some(pivot_column) = pivot_column {
            // 1. The first nonzero entry of each row must be 1.
            let pivot = m[[i, pivot_column]];
            if pivot != T::ONE {
                return false;
            }

            // 2. The first nonzero entry of each row must be to the right of the first nonzero entry of the row above.
            if let Some(previous_pivot_column) = previous_pivot_column {
                if pivot_column <= previous_pivot_column {
                    return false;
                }
            }

            // 3. The pivot must be the only nonzero entry in its column.
            for ii in 0..num_rows {
                if ii != i && m[[ii, pivot_column]] != T::ZERO {
                    return false;
                }
            }
            previous_pivot_column = Some(pivot_column);
        } else {
            // The row did not contain any nonzero entries.
            zero_row = Some(i);
            break;
        }
    }

    if let Some(zero_row) = zero_row {
        // 4. All subsequent rows must consist entirely of zeros.
        for i in (zero_row + 1)..num_rows {
            if m.row(i).any(|&x| x != T::ZERO) {
                return false;
            }
        }
    }

    true
}

#[cfg(test)]
mod tests {
    use crate::{
        fields::Zp1091,
        linalg::{
            is_diagonal, is_lower_triangular, is_upper_triangular,
            matrix::special::is_reduced_row_echelon, Matrix,
        },
    };

    #[test]
    #[allow(non_snake_case)]
    fn test_with_zero() {
        type F = Zp1091;
        let O = Matrix::<F>::zero(9, 9);
        assert!(is_diagonal(&O));
        assert!(is_lower_triangular(&O));
        assert!(is_upper_triangular(&O));
        assert!(is_reduced_row_echelon(&O));
    }

    #[test]
    #[allow(non_snake_case)]
    fn test_with_identity() {
        type F = Zp1091;
        let I = Matrix::<F>::identity(9);
        assert!(is_diagonal(&I));
        assert!(is_lower_triangular(&I));
        assert!(is_upper_triangular(&I));
        assert!(is_reduced_row_echelon(&I));
    }

    #[test]
    #[ignore]
    fn test_is_upper_triangular() {
        todo!()
    }

    #[test]
    #[ignore]
    fn test_is_lower_triangular() {
        todo!()
    }

    #[test]
    #[ignore]
    fn test_is_diagonal() {
        todo!()
    }

    #[test]
    #[ignore]
    fn test_is_reduced_row_echelon() {
        // type F = Zp1091;
        // let m = Matrix::<F>::identity(9);
        // assert!(is_reduced_row_echelon(&m));
    }
}
