//! Crout's method for LU Decomposition
//!
//! Crout's method decomposes a non-singular nxn matrix A into a lower triangular matrix L and a
//! unit upper triangular matrix U such that A = LU.
//!
//! The algorithm proceeds as:
//! 0. Initialize L to the zero matrix and U to the identity matrix.
//! 1. Set the first column of L is the first column of A.
//! 2. The first row of U is the first row of A divided by the first entry of L.
//! 3. For each row i, starting with the second row, compute the i^th row of L and then the
//!    i^th row of U using the following formulas:
//!
//! L_{ij} = a_{ij} - \sum_{k=1}^{j-1} L_{ik} U_{kj}
//!
//! U_{ij} = \frac{A_{ij} - \sum_{k=1}^{j-1} L_{ik} U_{kj}}{L_{ii}}
//!
//! Intuitively, if we look at the elements of L and U...
//!
//!      | l_{00}    0       0    |           |   1  u_{01}  u_{02} |
//! L =  | l_{10}  l_{11}    0    |     U =   |   0     1    u_{12} |
//!      | l_{20}  l_{21}  l_{22} |           |   0     0      1    |
//!
//! Then the product A = LU must be
//!
//!      | l_{00}          l_{00}*u_{01}                  l_{00}*u_{02}                          |  
//! A =  | l_{10}          l_{10}*u_{01} + l_{11}         l_{10}*u_{02} + l_{11}*u_{12}          |     
//!      | l_{20}          l_{20}*u_{01} + l_{21}         l_{20}*u_{02} + l_{21}*u_{12} + l_{22} |
//!
//! The algorithm is based on the observation that each expression depends only on the entries of
//! L and U that are above and/or to the left. If solved in the correct order, this gives explicit
//! formulas for each entry of L and U.
//!
//! ## Crout's Method with Partial Pivoting, PA = LU
//! Crout's method fails if computing U_{ij} requires dividing by zero. This can be avoided by
//! permuting (pivoting) the rows and/or columns of A. Crout's method with partial pivoting permutes
//! the rows of A as necessary to avoid division by zero. These permutations are captured by the
//! permutation matrix P.
//!
//! # References
//! * Numerical Recipes in Fortran 77: The Art of Scientific Computing, Section 2.3

#![allow(non_snake_case)]

use crate::{
    linalg::{Error, Matrix},
    FiniteField,
};

/// Crout's A=LU decomposition of a non-singular matrix, without pivoting.
///
/// # Arguments
/// * `matrix` - An nxn non-singular matrix 'A'
///
/// # Returns
/// * `Ok((L, U))` - The LU decomposition of A. L is a lower triangular matrix and U is a unit upper triangular matrix.
/// * `Err(_)` - If the matrix A is not square, is singular, or if pivoting is required.
pub fn crout_lu<T: FiniteField>(A: &Matrix<T>) -> Result<(Matrix<T>, Matrix<T>), Error> {
    if !A.is_square() {
        return Err(Error::NotSquare {
            num_rows: A.num_rows(),
            num_columns: A.num_columns(),
        });
    }
    let n = A.num_rows();

    // Invariants: L is lower triangular, U is unit upper triangular.
    let mut L: Matrix<T> = Matrix::zero(n, n);
    let mut U: Matrix<T> = Matrix::identity(n);

    // The first column of L is the first column of A.
    for i in 0..n {
        L[[i, 0]] = A[[i, 0]];
    }

    if L[[0, 0]] == T::zero() {
        return Err(Error::PivotingRequired);
    }

    // The first row of U is the first row of A divided by the first entry of L.
    for j in 0..n {
        U[[0, j]] = A[[0, j]] / L[[0, 0]];
    }

    // For each remaining row...
    for i in 1..n {
        // Compute the i^th row of L, omitting the first column.
        for j in 1..=i {
            // L_{ij} = a_{ij} - \sum_{k=1}^{j-1} L_{ik} U_{kj}
            let mut sum = T::zero();
            for k in 0..j {
                sum += L[[i, k]] * U[[k, j]];
            }
            L[[i, j]] = A[[i, j]] - sum;
        }

        if L[[i, i]] == T::zero() {
            return Err(Error::PivotingRequired);
        }

        // And then the i^th row of U, omitting the diagonal.
        for j in i + 1..n {
            // U_{ij} = \frac{A_{ij} - \sum_{k=1}^{j-1} L_{ik} U_{kj}}{L_{ii}}
            let mut sum = T::zero();
            for k in 0..j {
                sum += L[[i, k]] * U[[k, j]];
            }
            U[[i, j]] = (A[[i, j]] - sum) / L[[i, i]];
        }
    }

    Ok((L, U))
}

/// Crout's PA=LU decomposition of a non-singular matrix, with partial pivoting.
///
/// # Arguments
/// * `matrix` - An nxn non-singular matrix 'A'
///
/// # Returns
/// * `Ok((L, U, P))` - The LU decomposition of A. L is a lower triangular matrix, U is a unit upper triangular matrix, and P is a perumation matrix.
/// * `Err(_)` - If the matrix A is not square or is singular.
pub fn crout_lu_pivoting<T: FiniteField>(
    A: &Matrix<T>,
) -> Result<(Matrix<T>, Matrix<T>, Matrix<T>), Error> {
    if !A.is_square() {
        return Err(Error::NotSquare {
            num_rows: A.num_rows(),
            num_columns: A.num_columns(),
        });
    }

    let mut A = A.clone();
    let n = A.num_rows();

    // The decomposition is computed in-place. The upper-triangular matrix U is written into
    // the upper-triangular elements of A. The sub-diagonal elements of L are written into the
    // sub-diagonal elements of A. The diagonal elements of L are all 1, so they are not stored.

    // The elements of L are denoted alpha_ij.
    // The elements of U are denoted beta_ij.

    // The permutation matrix.
    let mut P: Matrix<T> = Matrix::identity(n);

    for j in 0..n {
        // i < j
        for i in 0..j {
            // beta_ij = a_ij - \sum_{k=0}^{i-1} alpha_ik beta_kj
            let mut sum = T::zero();
            for k in 0..i {
                sum += A[[i, k]] * A[[k, j]];
            }
            A[[i, j]] = A[[i, j]] - sum;
        }

        // i >= j
        // Compute candidates
        // Choose a non-zero (or largest) candidate to become the pivot.
        // Swap rows of A and L, if necessary.
        // Divide each remaining candidate by the pivot to compute the elements of L below the pivot.

        for i in j..n {
            // beta_ij = a_ij - \sum_{k=0}^{j-1} alpha_ik beta_kj
            let mut sum = T::zero();
            for k in 0..j {
                sum += A[[i, k]] * A[[k, j]];
            }
            A[[i, j]] = A[[i, j]] - sum;
        }

        if let Some(pivot_row) = (j..n).find(|&i| !A[[i, j]].is_zero()) {
            if pivot_row != j {
                // Swap rows
                A.swap_rows(j, pivot_row);
                P.swap_rows(j, pivot_row);
            }

            // Divide each remaining candidate by the pivot to compute the elements of L below the pivot.
            let pivot = A[[j, j]];
            for i in (j + 1)..n {
                A[[i, j]] = A[[i, j]] / pivot;
            }
        } else {
            return Err(Error::NotInvertible);
        }
    }

    // Unpack L and U from A
    let mut L: Matrix<T> = Matrix::zero(n, n);
    let mut U: Matrix<T> = Matrix::zero(n, n);
    for i in 0..n {
        for j in 0..n {
            if i < j {
                U[[i, j]] = A[[i, j]];
            } else if i == j {
                U[[i, j]] = A[[i, j]];
                L[[i, j]] = T::ONE;
            } else {
                L[[i, j]] = A[[i, j]];
            }
        }
    }
    Ok((L, U, P))
}

#[cfg(test)]
mod tests {
    use proptest::prelude::*;

    pub use crate::linalg::matrix::{
        is_lower_triangular, is_upper_triangular, is_upper_unit_triangular,
    };
    use crate::{fields::Zp541, FiniteField, One, Zero};

    #[test]
    #[ignore]
    // Spot-check against Sage.
    fn test_spotcheck_crout_lu() {
        /*
            Sage's echelon_form() function returns a matrix in reduced row echelon form:

           '''sage
           p = 541
           Fp = GF(p)
           M = Matrix(Fp, [[1, 2, 3], [4, 5, 6], [7, 8, 9]])
           TODO
        */
        todo!()
    }

    proptest! {
        #[test]
        fn test_crout_lu_does_not_panic(
            m in (1..=10usize).prop_flat_map(|n| any_with::<super::Matrix::<Zp541>>((n,n)))) {
            let _res = super::crout_lu(&m);
        }
    }

    proptest! {
        #[test]
        fn test_crout_lu_pivoting_does_not_panic(
            m in (1..=10usize).prop_flat_map(|n| any_with::<super::Matrix::<Zp541>>((n,n)))) {
            let _res = super::crout_lu_pivoting(&m);
        }
    }

    #[test]
    #[ignore]
    fn test_crout_lu_rejects_non_square_matrices() {
        todo!()
    }

    #[test]
    #[ignore]
    fn test_crout_lu_rejects_singular_matrices() {
        todo!()
    }

    #[test]
    #[ignore]
    fn test_crout_lu_rejects_matrices_requiring_pivoting() {
        todo!()
    }

    proptest! {
        #[test]
        // If successful, L is lower triangular.
        fn test_crout_lu_returns_L_lower_triangular(
            A in (1..=10usize).prop_flat_map(|n| any_with::<super::Matrix::<Zp541>>((n,n)))) {
            if let Ok((L,_U)) = super::crout_lu(&A) {
                println!("{}", L);
                prop_assert!(is_lower_triangular(&L));
            }
        }
    }

    proptest! {
        #[test]
        // If successful, L is lower triangular.
        fn test_crout_lu_pivoting_returns_L_lower_triangular(
            A in (1..=10usize).prop_flat_map(|n| any_with::<super::Matrix::<Zp541>>((n,n)))) {
            if let Ok((L,_U, _P)) = super::crout_lu_pivoting(&A) {
                println!("{}", L);
                prop_assert!(is_lower_triangular(&L));
            }
        }
    }

    proptest! {
        #[test]
        // If successful, U is upper triangular.
        fn test_crout_lu_returns_U_upper_unit_triangular(
            A in (1..=10usize).prop_flat_map(|n| any_with::<super::Matrix::<Zp541>>((n,n)))) {
            if let Ok((_L,U)) = super::crout_lu(&A) {
                println!("{}", U);
                prop_assert!(is_upper_unit_triangular(&U));

            }
        }
    }

    proptest! {
        #[test]
        // If successful, U is upper triangular.
        fn test_crout_lu_pivoting_returns_U_upper_triangular(
            A in (1..=10usize).prop_flat_map(|n| any_with::<super::Matrix::<Zp541>>((n,n)))) {
            if let Ok((_L,U, _P)) = super::crout_lu_pivoting(&A) {
                println!("{}", U);
                prop_assert!(is_upper_triangular(&U));

            }
        }
    }

    proptest! {
        #[test]
        // If successful, A = LU.
        fn test_crout_lu_decomposes_A_into_LU(
            A in (1..=10usize).prop_flat_map(|n| any_with::<super::Matrix::<Zp541>>((n,n)))) {
            let n = A.num_rows();
            println!("A: {:#?}", A);
            if let Ok((L,U)) = super::crout_lu(&A) {
                prop_assert_eq!(L.num_rows(), n);
                prop_assert_eq!(L.num_columns(), n);
                prop_assert_eq!(U.num_rows(), n);
                prop_assert_eq!(U.num_columns(), n);
                prop_assert_eq!(A, L * U)
            }
        }
    }

    proptest! {
        #[test]
        // If successful, PA = LU.
        fn test_crout_lu_pivoting_decomposes_PA_into_LU(
            A in (1..=10usize).prop_flat_map(|n| any_with::<super::Matrix::<Zp541>>((n,n)))) {
            let n = A.num_rows();
            println!("A: {:#?}", A);
            if let Ok((L,U,P)) = super::crout_lu_pivoting(&A) {
                prop_assert_eq!(L.num_rows(), n);
                prop_assert_eq!(L.num_columns(), n);
                prop_assert_eq!(U.num_rows(), n);
                prop_assert_eq!(U.num_columns(), n);
                prop_assert_eq!(P.num_rows(), n);
                prop_assert_eq!(P.num_columns(), n);
                prop_assert_eq!(P* A, L * U)
            }
        }
    }

    #[test]
    // Compute A from known L and U, and then recover them.
    fn test_crout_lu_pivoting_example_a() {
        type F = Zp541;
        let L = matrix![F::ONE, F::ZERO; F::new(3), F::ONE];
        let U = matrix![F::new(4), F::new(9); F::ZERO, F::new(14)];
        let A = &L * &U;

        let (L2, U2, _P) = super::crout_lu_pivoting(&A).unwrap();
        assert_eq!(L, L2);
        assert_eq!(U, U2);
    }

    #[test]
    // Compute A from known L and U, and then recover them.
    fn test_crout_lu_pivoting_example_b() {
        type F = Zp541;
        let A = matrix![F::ZERO, F::ONE; F::ONE, F::ZERO];
        let (L, U, P) = super::crout_lu_pivoting(&A).unwrap();
        assert_eq!(&P * A, L * U);

        let expected_P = matrix![F::ZERO, F::ONE; F::ONE, F::ZERO];
        assert_eq!(P, expected_P);
    }
}
