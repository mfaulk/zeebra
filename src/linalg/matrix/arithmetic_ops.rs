//! Matrix-Matrix operations.

use crate::{linalg::matrix::Matrix, Ring};
use std::ops::{Add, Mul};
use crate::{impl_add_variants, impl_mul_variants};

/// Matrices of the same size may be added element-wise.
impl<T: Ring> Add for &Matrix<T> {
    type Output = Matrix<T>;

    fn add(self, rhs: Self) -> Self::Output {
        assert_eq!(
            self.num_rows, rhs.num_rows,
            "num_rows: {} != {}",
            self.num_rows, rhs.num_rows
        );
        assert_eq!(
            self.num_columns, rhs.num_columns,
            "num_columns: {} != {}",
            self.num_columns, rhs.num_columns
        );

        let mut sum = vec![T::ZERO; self.num_rows * self.num_columns];
        for i in 0..self.num_rows {
            for j in 0..self.num_columns {
                sum[i * self.num_columns + j] = self[[i, j]] + rhs[[i, j]];
            }
        }
        Self::Output {
            num_rows: self.num_rows,
            num_columns: self.num_columns,
            elements: sum,
        }
    }
}

impl_add_variants!([T: Ring], Matrix<T>);

// Matrix multiplication.
impl<T: Ring> Mul for &Matrix<T> {
    type Output = Matrix<T>;

    fn mul(self, rhs: Self) -> Self::Output {
        assert_eq!(
            self.num_columns, rhs.num_rows,
            "num_columns: {} != {}",
            self.num_columns, rhs.num_rows
        );

        let mut product = vec![T::ZERO; self.num_rows * rhs.num_columns];
        for i in 0..self.num_rows {
            for j in 0..rhs.num_columns {
                for k in 0..self.num_columns {
                    product[i * rhs.num_columns + j] += self[[i, k]] * rhs[[k, j]];
                }
            }
        }
        Self::Output {
            num_rows: self.num_rows,
            num_columns: rhs.num_columns,
            elements: product,
        }
    }
}

impl_mul_variants!([T: Ring], Matrix<T>);

#[cfg(test)]
mod tests {
    use super::Matrix;
    use crate::fields::{Zp541, Zp65537};
    use proptest::prelude::*;

    const MAX_ROWS: usize = 10;
    const MAX_COLS: usize = 10;

    proptest! {
        #[test]
        // The zero matrix is the additive identity: A + 0 = A
        fn test_additive_identity(m in (1..=MAX_ROWS, 1..=MAX_COLS).prop_flat_map(any_with::<Matrix::<Zp541>>))
        {
            let zero = Matrix::<Zp541>::zero(m.num_rows, m.num_columns);
            assert_eq!(zero + &m, m);
        }
    }

    proptest! {
        #[test]
        // Addition is commutative: A + B = B + A
        // Create two arbitrary matrices of the same size. Maybe there's a better way to do this?
        fn test_addition_is_commutative((a,b) in (1..=MAX_ROWS, 1..=MAX_COLS)
                .prop_flat_map(|params| {
            any_with::<Matrix::<Zp541>>(params).prop_flat_map(move |a| {
                any_with::<Matrix::<Zp541>>(params).prop_map( move |b| (a.clone(),b))})})){

            assert_eq!(&a + &b, &b + &a);
        }
    }

    proptest! {
        #[test]
        // The identity matrix is the multiplicative identity.
        fn test_multiplicative_identity(m in (1..=MAX_ROWS, 1..=MAX_COLS).prop_flat_map(any_with::<Matrix::<Zp541>>))
        {
            // The left-multiplicative identity.
            let I_m = Matrix::<Zp541>::identity(m.num_rows);
            assert_eq!(&I_m * &m, m);

            // The right-multiplicative identity.
            let I_n = Matrix::<Zp541>::identity(m.num_columns);
            assert_eq!(&m * &I_n, m);
        }
    }

    // Multiplication is associative: A(BC) = (AB)C

    // Left Distributive: A(B + C) = AB + AC

    // Right Distributive: (A + B)C = AC + BC

    // Scalar multiplication: r(AB) = (rA)B = A(rB)

    // (A^T)^T = A

    proptest! {
        #[test]
        // (A + B)^T = A^T + B^T
        // Create two arbitrary matrices of the same size. Maybe there's a better way to do this?
        fn test_sum_transposed((a,b) in (1..=MAX_ROWS, 1..=MAX_COLS)
                .prop_flat_map(|params| {
            any_with::<Matrix::<Zp541>>(params).prop_flat_map(move |a| {
                any_with::<Matrix::<Zp541>>(params).prop_map( move |b| (a.clone(),b))})})){

            assert_eq!((&a + &b).transpose(), a.transpose() + b.transpose());
        }
    }

    proptest! {
        #[test]
        // (AB)^T = B^T A^T
        fn test_product_transposed(
            (a,b) in (1..=MAX_ROWS, 1..=MAX_COLS, 1..=MAX_COLS)
                .prop_flat_map(|params| {
                let (p,q,r) = params;
                any_with::<Matrix::<Zp65537>>((q,p)).prop_flat_map(move |a| {
                any_with::<Matrix::<Zp65537>>((p,r)).prop_map(move |b| { (a.clone(),b) })})})){

            let ab_transpose = (&a * &b).transpose();
            let a_transpose = a.transpose();
            let b_transpose = b.transpose();
            assert_eq!(ab_transpose, b_transpose * a_transpose);
        }
    }

    // (rA)^T = rA^T
}
