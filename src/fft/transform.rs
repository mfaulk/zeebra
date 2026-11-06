//! The radix-2 transform kernel shared by `evaluate` and `interpolate`.
//!
//! Two invariants carry the whole implementation.
//!
//! **Bit reversal.** Decimation-in-time Cooley–Tukey consumes its input in bit-reversed index
//! order and produces its output in natural order, so the permutation is applied once up front
//! rather than being paid as an index computation inside every pass.
//!
//! **Twiddle stride.** `domain` *is* the twiddle table. On the pass whose sub-transform length is
//! `m`, the butterfly at offset `j` wants `w^{j * n / m}`, which is `domain[j * (n / m)]` — so the
//! table is read with a stride and nothing is built, split, or allocated per pass. The same
//! identity makes `w^{m/2} = -1`, so one twiddle product serves both outputs of a butterfly:
//! `(n/2) log n` multiplications rather than `n log n`.

use crate::FiniteField;

/// Transform `values` in place over `domain`, which must be `1, w, w^2, ..., w^{n-1}` for a
/// primitive `n`th root of unity `w`.
///
/// `values` holds the coefficients on entry and the evaluations `p(w^0), ..., p(w^{n-1})` on exit.
/// One buffer, no recursion, no allocation: `log n` passes of `n / 2` butterflies each.
///
/// The inverse transform is this same kernel over the inverse domain, scaled by `1/n` afterwards;
/// see [`crate::interpolate`].
pub(crate) fn transform_in_place<F: FiniteField>(values: &mut [F], domain: &[F]) {
    let n = values.len();
    assert_eq!(
        n,
        domain.len(),
        "values and domain must have the same length"
    );
    assert!(n.is_power_of_two(), "n is {} but must be a power of 2", n);

    if n == 1 {
        // The transform of a single coefficient is itself: domain[0] is 1.
        return;
    }

    // The contract, checked in O(1) rather than trusted. `try_from_generator` rejects a
    // non-primitive root (#120), but `FFTDomain::new` takes a vector of powers unchecked and
    // `FFTDomain::split` yields a domain that is not a power sequence at all. Either would give a
    // silently wrong transform.
    assert_eq!(
        domain[n / 2],
        -F::one(),
        "domain must be the powers of a primitive {}th root of unity, so that w^{} is -1",
        n,
        n / 2
    );

    bit_reverse_permute(values);

    let mut m = 2;
    while m <= n {
        let half = m / 2;
        let stride = n / m;
        for block in values.chunks_mut(m) {
            let (even, odd) = block.split_at_mut(half);
            for ((a, b), w) in even
                .iter_mut()
                .zip(odd.iter_mut())
                .zip(domain.iter().step_by(stride))
            {
                let t = *w * *b;
                let u = *a;
                *a = u + t;
                *b = u - t;
            }
        }
        m *= 2;
    }
}

/// Permute `values` into bit-reversed index order, in place.
///
/// `i.reverse_bits() >> (usize::BITS - log n)` is the reversal of `i` within `log n` bits; swapping
/// only when `j > i` applies each transposition once.
fn bit_reverse_permute<F>(values: &mut [F]) {
    let n = values.len();
    debug_assert!(n.is_power_of_two());
    if n <= 1 {
        // `usize::BITS - 0` is not a legal shift amount, and there is nothing to permute.
        return;
    }
    let shift = usize::BITS - n.trailing_zeros();
    for i in 0..n {
        let j = i.reverse_bits() >> shift;
        if j > i {
            values.swap(i, j);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{bit_reverse_permute, transform_in_place};
    use crate::{
        fields::{Bls12_381Fr, Bn254Fr, KoalaBear, Mersenne31, PrimeFieldElement64},
        identities::Zero,
        FFTDomain, FiniteField, KnownOrder,
    };
    use rand::{prelude::StdRng, SeedableRng};

    /// The transform by its definition: the `n x n` Vandermonde matrix applied to the
    /// coefficients, quadratic and sharing no code with the kernel.
    fn reference_dft<F: FiniteField>(coefficients: &[F], domain: &[F]) -> Vec<F> {
        let n = domain.len();
        (0..n)
            .map(|i| {
                let mut accumulator = F::zero();
                for (j, c) in coefficients.iter().enumerate() {
                    accumulator += *c * domain[(i * j) % n];
                }
                accumulator
            })
            .collect()
    }

    /// Bit reversal is an involution and sends index `i` to the reversal of `i` in `log n` bits.
    #[test]
    fn test_bit_reverse_permute() {
        for log_n in 1..=10u32 {
            let n = 1usize << log_n;
            let mut values: Vec<usize> = (0..n).collect();
            bit_reverse_permute(&mut values);
            for (i, value) in values.iter().enumerate() {
                let expected = i.reverse_bits() >> (usize::BITS - log_n);
                assert_eq!(*value, expected, "log_n = {log_n}, index {i}");
            }
            bit_reverse_permute(&mut values);
            assert_eq!(values, (0..n).collect::<Vec<_>>(), "log_n = {log_n}");
        }
    }

    /// The kernel agrees with the quadratic Vandermonde definition over a 254-bit field.
    #[test]
    fn test_kernel_agrees_with_the_definition_over_bn254() {
        let mut rng = StdRng::seed_from_u64(0x161);
        for log_n in 0..=7u32 {
            let n = 1usize << log_n;
            let w = Bn254Fr::two_adic_root_of_unity(log_n, &mut rng);
            let domain = FFTDomain::from_generator(w, n);
            let coefficients: Vec<Bn254Fr> = (0..n).map(|_| Bn254Fr::random(&mut rng)).collect();

            let expected = reference_dft(&coefficients, domain.powers());
            let mut values = coefficients;
            transform_in_place(&mut values, domain.powers());
            assert_eq!(values, expected, "n = {n}");
        }
    }

    /// The kernel agrees with the definition over the narrow fields, including at a size the
    /// quadratic reference can still reach.
    #[test]
    fn test_kernel_agrees_with_the_definition_over_the_narrow_fields() {
        fn check<F: KnownOrder>(seed: u64) {
            let mut rng = StdRng::seed_from_u64(seed);
            let highest = F::two_adicity().min(8);
            for log_n in 0..=highest {
                let n = 1usize << log_n;
                let w = F::two_adic_root_of_unity(log_n, &mut rng);
                let domain = FFTDomain::from_generator(w, n);
                let coefficients: Vec<F> = (0..n).map(|_| F::random(&mut rng)).collect();

                let expected = reference_dft(&coefficients, domain.powers());
                let mut values = coefficients;
                transform_in_place(&mut values, domain.powers());
                assert_eq!(values, expected, "n = {n}");
            }
        }

        check::<KoalaBear>(11);
        check::<PrimeFieldElement64<2_130_706_433>>(12);
        check::<PrimeFieldElement64<18_446_744_069_414_584_321>>(13);
        check::<Bls12_381Fr>(14);
        // Mersenne-31 has two-adicity 1, so this reaches only size 2. That is the point of
        // deriving the bound from the field rather than fixing it.
        check::<Mersenne31>(15);
    }

    /// A zero input transforms to zero at every size.
    #[test]
    fn test_kernel_of_zero_is_zero() {
        type F = PrimeFieldElement64<97>;
        let mut rng = StdRng::seed_from_u64(97);
        for log_n in 0..=5u32 {
            let n = 1usize << log_n;
            let w = F::two_adic_root_of_unity(log_n, &mut rng);
            let domain = FFTDomain::from_generator(w, n);
            let mut values = vec![F::zero(); n];
            transform_in_place(&mut values, domain.powers());
            assert_eq!(values, vec![F::zero(); n], "n = {n}");
        }
    }

    /// A domain that is not the powers of a primitive nth root of unity is rejected, rather than
    /// producing a silently wrong transform.
    #[test]
    #[should_panic(expected = "primitive")]
    fn test_kernel_rejects_a_non_primitive_domain() {
        type F = PrimeFieldElement64<97>;
        let mut rng = StdRng::seed_from_u64(4919);
        // A primitive 4th root of unity, used to build a size-8 domain: w^8 = 1 holds, but w^4 is
        // 1 rather than -1, so the domain repeats and the transform would be wrong.
        let w = F::two_adic_root_of_unity(2, &mut rng);
        let domain = FFTDomain::new(crate::powers_of(&w, 8));
        let mut values = vec![F::new(1); 8];
        transform_in_place(&mut values, domain.powers());
    }

    /// The odd half of a split domain is rejected: it is not a power sequence from one.
    #[test]
    #[should_panic(expected = "primitive")]
    fn test_kernel_rejects_a_split_domain() {
        type F = PrimeFieldElement64<97>;
        let mut rng = StdRng::seed_from_u64(7919);
        let w = F::two_adic_root_of_unity(4, &mut rng);
        let domain = FFTDomain::from_generator(w, 16);
        let (_evens, odds) = domain.split();
        let mut values = vec![F::new(1); 8];
        transform_in_place(&mut values, odds.powers());
    }

    /// A length mismatch between the values and the domain is rejected.
    #[test]
    #[should_panic(expected = "same length")]
    fn test_kernel_rejects_a_length_mismatch() {
        type F = PrimeFieldElement64<97>;
        let mut rng = StdRng::seed_from_u64(31);
        let w = F::two_adic_root_of_unity(3, &mut rng);
        let domain = FFTDomain::from_generator(w, 8);
        let mut values = vec![F::new(1); 4];
        transform_in_place(&mut values, domain.powers());
    }
}
