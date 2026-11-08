//! Matrix-Matrix operations.

use crate::{impl_add_variants, impl_mul_variants};
use crate::{linalg::matrix::Matrix, Ring};
use std::ops::{Add, Mul};

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

        let n = rhs.num_columns;
        let depth = self.num_columns;
        let m = self.num_rows;
        let mut product = vec![T::ZERO; m * n];
        // A 2-by-8 register tile over `i` and `j`, accumulated across the whole `k` loop.
        //
        // `ikj` with `k` unrolled four deep reads and writes a whole row of the product per group
        // of four `k`, which is what left it 8% behind `ijk` at square n=128 while being 2x ahead
        // once the right operand passed L3. Tiling `j` as well holds the product entries in the
        // tile until `k` is exhausted, so the product row is stored once per tile; and tiling two
        // rows of the left operand together doubles the arithmetic each span of the right operand
        // is loaded for, which is what pays for reading that operand down a column rather than
        // along a row.
        //
        // The shape is tuned rather than chosen, and the tuning is most of the result. Measured
        // over a 31-bit prime, pinned and interleaved, three reps: 2x8 is faster than `ikj` at
        // every arm of `benches/linear_algebra.rs`, where 2x16 and 2x32 give back 26% and 16% on
        // the 128 MiB arm, and a `j` tile with no `i` tile wins nowhere — widths 4 and 8 are
        // slower at every square size, and 16 reaches parity in cache only to lose 7-11% once the
        // right operand is past L3. Eight elements is also exactly one 64-byte cache line at 8
        // bytes apiece, which is the obvious reading of why the wider tiles fall off, and not one
        // these measurements establish.
        const JT: usize = 8;
        let mut i = 0;
        while i + 2 <= m {
            let a0 = &self.elements[i * depth..][..depth];
            let a1 = &self.elements[(i + 1) * depth..][..depth];
            let mut j0 = 0;
            while j0 + JT <= n {
                let mut acc0 = [T::ZERO; JT];
                let mut acc1 = [T::ZERO; JT];
                for (k, (&x0, &x1)) in a0.iter().zip(a1.iter()).enumerate() {
                    let b = <&[T; JT]>::try_from(&rhs.elements[k * n + j0..][..JT]).unwrap();
                    for ((s0, s1), &b_j) in acc0.iter_mut().zip(acc1.iter_mut()).zip(b.iter()) {
                        *s0 += x0 * b_j;
                        *s1 += x1 * b_j;
                    }
                }
                product[i * n + j0..][..JT].copy_from_slice(&acc0);
                product[(i + 1) * n + j0..][..JT].copy_from_slice(&acc1);
                j0 += JT;
            }
            // The columns past the last whole tile, one at a time, for both rows at once.
            for j in j0..n {
                let mut s0 = T::ZERO;
                let mut s1 = T::ZERO;
                for (k, (&x0, &x1)) in a0.iter().zip(a1.iter()).enumerate() {
                    let b_j = rhs.elements[k * n + j];
                    s0 += x0 * b_j;
                    s1 += x1 * b_j;
                }
                product[i * n + j] = s0;
                product[(i + 1) * n + j] = s1;
            }
            i += 2;
        }
        // An odd final row runs the same tile one row wide.
        while i < m {
            let a_row = &self.elements[i * depth..][..depth];
            let mut j0 = 0;
            while j0 + JT <= n {
                let mut acc = [T::ZERO; JT];
                for (k, &a) in a_row.iter().enumerate() {
                    let b = <&[T; JT]>::try_from(&rhs.elements[k * n + j0..][..JT]).unwrap();
                    for (s, &b_j) in acc.iter_mut().zip(b.iter()) {
                        *s += a * b_j;
                    }
                }
                product[i * n + j0..][..JT].copy_from_slice(&acc);
                j0 += JT;
            }
            for j in j0..n {
                let mut acc = T::ZERO;
                for (k, &a) in a_row.iter().enumerate() {
                    acc += a * rhs.elements[k * n + j];
                }
                product[i * n + j] = acc;
            }
            i += 1;
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
    use crate::identities::Zero;
    use crate::linalg::MatrixParams;
    use crate::FiniteField;
    use proptest::prelude::*;
    use rand::{prelude::StdRng, SeedableRng};

    const MAX_ROWS: usize = 10;
    const MAX_COLS: usize = 10;

    proptest! {
        #[test]
        // The zero matrix is the additive identity: A + 0 = A
        fn test_additive_identity(m in (1..=MAX_ROWS, 1..=MAX_COLS).prop_map(MatrixParams::from).prop_flat_map(any_with::<Matrix::<Zp541>>))
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
            any_with::<Matrix::<Zp541>>(params.into()).prop_flat_map(move |a| {
                any_with::<Matrix::<Zp541>>(params.into()).prop_map( move |b| (a.clone(),b))})})){

            assert_eq!(&a + &b, &b + &a);
        }
    }

    proptest! {
        #[test]
        // The identity matrix is the multiplicative identity.
        fn test_multiplicative_identity(m in (1..=MAX_ROWS, 1..=MAX_COLS).prop_map(MatrixParams::from).prop_flat_map(any_with::<Matrix::<Zp541>>))
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
            any_with::<Matrix::<Zp541>>(params.into()).prop_flat_map(move |a| {
                any_with::<Matrix::<Zp541>>(params.into()).prop_map( move |b| (a.clone(),b))})})){

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
                any_with::<Matrix::<Zp65537>>((q,p).into()).prop_flat_map(move |a| {
                any_with::<Matrix::<Zp65537>>((p,r).into()).prop_map(move |b| { (a.clone(),b) })})})){

            let ab_transpose = (&a * &b).transpose();
            let a_transpose = a.transpose();
            let b_transpose = b.transpose();
            assert_eq!(ab_transpose, b_transpose * a_transpose);
        }
    }

    // (rA)^T = rA^T

    #[test]
    // A 2x3 times 3x4 product matches hand-computed entries: distinct m, k, n and a
    // non-symmetric operand, so a transposed or mis-strided index cannot pass.
    fn test_product_of_distinct_dimensions() {
        let a = Matrix::new(
            2,
            3,
            &[1, 2, 3, 4, 5, 6].map(Zp65537::new), // [[1,2,3],[4,5,6]]
        );
        let b = Matrix::new(
            3,
            4,
            &[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12].map(Zp65537::new),
        );

        let expected = Matrix::new(2, 4, &[38, 44, 50, 56, 83, 98, 113, 128].map(Zp65537::new));

        assert_eq!(&a * &b, expected);
    }

    #[test]
    #[should_panic(expected = "num_columns")]
    // Multiplying when the left operand's column count differs from the right operand's row
    // count panics rather than reading out of bounds.
    fn test_product_of_mismatched_dimensions_panics() {
        let a = Matrix::<Zp65537>::zero(2, 3);
        let b = Matrix::<Zp65537>::zero(4, 5);
        let _ = &a * &b;
    }

    #[test]
    // The product agrees with the textbook `ijk` sum at dimensions that are not multiples of the
    // kernel's blocking factors, so a mishandled `j` or `k` remainder cannot pass: the proptests
    // above reach only 10 columns, where a tiled kernel runs almost entirely in its tail.
    fn test_product_matches_reference_at_blocking_remainders() {
        // 17 and 19 are coprime to every power of two, so each of m, k and n leaves a remainder
        // under tile widths of 2, 4, 8 and 16; 16 and 32 are exact multiples, pinning the case
        // where the tail is empty.
        for (m, depth, n) in [
            (17, 19, 23),
            (1, 17, 1),
            (3, 1, 7),
            (16, 32, 16),
            (17, 32, 33),
            (33, 17, 16),
        ] {
            let a = random_rect::<Zp65537>(m, depth, 101);
            let b = random_rect::<Zp65537>(depth, n, 103);

            let mut expected = Matrix::<Zp65537>::zero(m, n);
            for i in 0..m {
                for j in 0..n {
                    let mut sum = Zp65537::ZERO;
                    for k in 0..depth {
                        sum += a[[i, k]] * b[[k, j]];
                    }
                    expected[[i, j]] = sum;
                }
            }

            assert_eq!(&a * &b, expected, "{m}x{depth} times {depth}x{n}");
        }
    }

    fn random_rect<F: FiniteField>(rows: usize, columns: usize, seed: u64) -> Matrix<F> {
        let mut rng = StdRng::seed_from_u64(seed);
        let elements: Vec<F> = (0..rows * columns).map(|_| F::random(&mut rng)).collect();
        Matrix::new(rows, columns, &elements)
    }
}
