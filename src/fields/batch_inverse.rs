//! Batch inversion by Montgomery's trick.
//!
//! Inverting n elements one at a time costs n inversions. Inverting their product costs one, and
//! the individual inverses fall out of it with three multiplications each:
//!
//! ```text
//! p_j = a_1 a_2 ... a_j            prefix products, j - 1 multiplications
//! t   = p_n^{-1}                   one inversion
//! a_j^{-1} = t * p_{j-1},  t <- t * a_j      two multiplications per element, backwards
//! ```
//!
//! So `1` inversion and `3(n-1)` multiplications replace `n` inversions. Whether that is a win
//! depends on the ratio between the two operations in the field: `montgomery_256` inverts by the
//! binary extended Euclidean algorithm and the narrower fields by exponentiation, so the ratio is
//! large everywhere and largest over the 254-bit fields. `benches/field_arithmetic.rs` reports
//! `isolated/inverse` against `batch/inverse` per field, which is the measurement to quote.
//!
//! The scratch vector of prefix products is the cost: `nonzeros * size_of::<F>()` bytes, held for
//! the duration.

use crate::FiniteField;

/// Replace every element of `xs` by its multiplicative inverse.
///
/// **A zero element is left as zero.** It has no inverse, and panicking would make this unusable
/// where it is most wanted — a batch comes from a container, and a container of field elements may
/// legitimately hold zeros. [`FiniteField::inverse`] keeps its panic because there the caller named
/// the one element it is asking about; here it did not. The behaviour is pinned by
/// `test_zeros_are_left_alone`.
pub fn batch_invert<F: FiniteField>(xs: &mut [F]) {
    // Prefix products of the nonzero elements. Sized to the nonzero count rather than to `xs`,
    // so a mostly-zero batch costs mostly nothing.
    let mut prefixes: Vec<F> = Vec::with_capacity(xs.len());

    let mut running = F::one();
    for x in xs.iter() {
        if x.is_zero() {
            continue;
        }
        prefixes.push(running);
        running *= *x;
    }

    if prefixes.is_empty() {
        // Every element is zero, so there is nothing to invert — and in particular no inversion
        // of the empty product, which would be wasted work rather than wrong.
        return;
    }

    // The one inversion.
    let mut inverse_of_prefix = running.inverse();

    // Backwards, so that `inverse_of_prefix` is always the inverse of the product up to and
    // including the element being written.
    let mut index = prefixes.len();
    for x in xs.iter_mut().rev() {
        if x.is_zero() {
            continue;
        }
        index -= 1;
        let original = *x;
        *x = inverse_of_prefix * prefixes[index];
        inverse_of_prefix *= original;
    }
    debug_assert_eq!(index, 0, "every prefix product must be consumed");
}

/// The multiplicative inverses of `xs`, in order.
///
/// The allocating form of [`batch_invert`], with the same treatment of zero: a zero input yields a
/// zero output.
pub fn batch_inverse<F: FiniteField>(xs: &[F]) -> Vec<F> {
    let mut inverses = xs.to_vec();
    batch_invert(&mut inverses);
    inverses
}

#[cfg(test)]
mod tests {
    use proptest::{collection::vec, prelude::*, proptest};
    use rand::{prelude::StdRng, SeedableRng};

    use super::{batch_inverse, batch_invert};
    use crate::{
        fields::{Bls12_381Fr, Bn254Fr, Proth68Fr, Zp13, Zp2147483647},
        FiniteField, One, Zero,
    };

    /// `n` nonzero elements of F.
    fn nonzero<F: FiniteField>(n: usize, seed: u64) -> Vec<F> {
        let mut rng = StdRng::seed_from_u64(seed);
        let mut values = Vec::with_capacity(n);
        while values.len() < n {
            let candidate = F::random(&mut rng);
            if !candidate.is_zero() {
                values.push(candidate);
            }
        }
        values
    }

    /// The batch agrees with inverting each element on its own, element for element.
    ///
    /// The whole contract. `inverse()` shares no code with the prefix-product walk, so this is an
    /// independent check rather than a restatement.
    fn agrees_with_elementwise_inverse<F: FiniteField>(seed: u64) {
        for n in [1usize, 2, 3, 4, 5, 17, 64, 100] {
            let values = nonzero::<F>(n, seed + n as u64);
            let expected: Vec<F> = values.iter().map(|x| x.inverse()).collect();
            assert_eq!(batch_inverse(&values), expected, "n = {n}");
        }
    }

    /// Batch inversion agrees with elementwise inversion over every prime field in the crate.
    #[test]
    #[allow(deprecated)]
    fn test_agrees_with_elementwise_inverse() {
        agrees_with_elementwise_inverse::<Zp13>(1);
        agrees_with_elementwise_inverse::<Zp2147483647>(2);
        agrees_with_elementwise_inverse::<crate::fields::PrimeFieldElement128<221360928884514619393>>(
            3,
        );
        agrees_with_elementwise_inverse::<Proth68Fr>(6);
        agrees_with_elementwise_inverse::<Bn254Fr>(4);
        agrees_with_elementwise_inverse::<Bls12_381Fr>(5);
    }

    /// Every reported inverse really is one: `x * x^-1 = 1`.
    ///
    /// Stated as the defining property rather than against another implementation, so it would
    /// catch the two being wrong together.
    #[test]
    fn test_each_product_is_one() {
        let values = nonzero::<Bn254Fr>(50, 7);
        for (x, inverse) in values.iter().zip(batch_inverse(&values)) {
            assert!((*x * inverse).is_one(), "{x} * {inverse} != 1");
        }
    }

    /// A zero is left as zero, and the nonzeros around it are still inverted correctly.
    #[test]
    fn test_zeros_are_left_alone() {
        let mut values = nonzero::<Bn254Fr>(9, 11);
        let expected: Vec<Bn254Fr> = values.iter().map(|x| x.inverse()).collect();

        // Zeros at the front, in the middle, and at the back — the three positions the backward
        // walk could index wrongly.
        let mut with_zeros = vec![Bn254Fr::zero()];
        with_zeros.extend_from_slice(&values[..4]);
        with_zeros.push(Bn254Fr::zero());
        with_zeros.push(Bn254Fr::zero());
        with_zeros.extend_from_slice(&values[4..]);
        with_zeros.push(Bn254Fr::zero());

        let inverted = batch_inverse(&with_zeros);
        let mut nonzero_inverses = inverted.iter().filter(|x| !x.is_zero());
        for expected_inverse in &expected {
            assert_eq!(nonzero_inverses.next(), Some(expected_inverse));
        }
        assert_eq!(nonzero_inverses.next(), None);
        // The zeros are still in their original positions.
        for position in [0usize, 5, 6, 12] {
            assert!(inverted[position].is_zero(), "position {position}");
        }

        // And the in-place form does the same to the same input.
        let in_place = {
            values = with_zeros.clone();
            batch_invert(&mut values);
            values
        };
        assert_eq!(in_place, inverted);
    }

    /// An all-zero batch is unchanged, and an empty one is accepted.
    #[test]
    fn test_degenerate_batches() {
        let mut zeros = vec![Zp2147483647::zero(); 5];
        batch_invert(&mut zeros);
        assert_eq!(zeros, vec![Zp2147483647::zero(); 5]);

        let mut empty: Vec<Zp2147483647> = Vec::new();
        batch_invert(&mut empty);
        assert!(empty.is_empty());
    }

    /// Inverting twice is the identity, including across the zeros.
    ///
    /// A property of the map rather than of either direction, so it is insensitive to a consistent
    /// error of sign or order in both.
    #[test]
    fn test_inverting_twice_is_the_identity() {
        let mut values = nonzero::<Bn254Fr>(20, 13);
        values.insert(0, Bn254Fr::zero());
        values.insert(11, Bn254Fr::zero());
        values.push(Bn254Fr::one());

        let round_trip = batch_inverse(&batch_inverse(&values));
        assert_eq!(round_trip, values);
    }

    /// Repeated elements each get their own inverse rather than aliasing.
    #[test]
    fn test_repeated_elements() {
        let a = nonzero::<Bn254Fr>(1, 17)[0];
        let values = vec![a, a, Bn254Fr::one(), a];
        assert_eq!(
            batch_inverse(&values),
            vec![a.inverse(), a.inverse(), Bn254Fr::one(), a.inverse()]
        );
    }

    /// One is its own inverse, so a batch of ones is unchanged.
    #[test]
    fn test_a_batch_of_ones() {
        let mut ones = vec![Bn254Fr::one(); 8];
        batch_invert(&mut ones);
        assert_eq!(ones, vec![Bn254Fr::one(); 8]);
    }

    proptest! {
        /// On an arbitrary batch, every nonzero entry's inverse matches `inverse()` and every
        /// zero entry survives.
        #[test]
        fn test_arbitrary_batches(values in vec(any::<Bn254Fr>(), 0..40)) {
            let inverted = batch_inverse(&values);
            prop_assert_eq!(inverted.len(), values.len());
            for (x, inverse) in values.iter().zip(&inverted) {
                if x.is_zero() {
                    prop_assert!(inverse.is_zero());
                } else {
                    prop_assert_eq!(*inverse, x.inverse());
                }
            }
        }
    }
}
