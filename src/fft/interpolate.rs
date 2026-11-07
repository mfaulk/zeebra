//! Inverse Fast Fourier Transform (IFFT).

use crate::{
    fft::{domain::FFTDomain, prime_factor::transform_any},
    FiniteField, UnivariatePolynomial,
};

/// Interpolate the points (w_i, x_i) into a polynomial P.
///
/// # Arguments
/// * `x` - the values P(1), P(w), P(w^2), ... P(w^{n-1}).
/// * `w` - Evaluation domain 1, w, w^2, ...
///
/// n must be a power of 2.
///
/// The same kernel as [`crate::evaluate`], run over the inverse domain and scaled by `1/n`. There
/// is no separate inverse pass: after batch inversion of the domain (#118) the two directions are
/// within a few percent of each other, so a second kernel would be a second place for the
/// butterfly to be wrong.
pub fn interpolate<F: FiniteField>(x: &[F], w: &FFTDomain<F>) -> UnivariatePolynomial<F> {
    assert_eq!(x.len(), w.size());

    // `c / n` would invert n once per coefficient: `Div` on a field element is multiplication by
    // `inverse()`, and nothing memoizes it. One inversion for the whole vector instead.
    //
    // n is invertible whenever the domain exists at all: a primitive nth root of unity requires
    // n | q - 1, so n is coprime to the characteristic. `inverse` still panics if a caller built
    // a domain by hand over a field where it is not.
    let size_inverse = F::new(w.size() as u64).inverse();

    // The inverse domain is built before the coefficient buffer, not after: `batch_inverse` holds
    // a vector of prefix products alongside its result, and that transient is the peak. Taking it
    // while only one n-element vector is live keeps the whole call at two.
    let w_inv = w.inverse();

    let mut coefficients = x.to_vec();
    transform_any(&mut coefficients, w_inv.powers());
    for c in coefficients.iter_mut() {
        *c *= size_inverse;
    }
    UnivariatePolynomial::from_coefficients(coefficients)
}

#[cfg(test)]
mod tests {
    use crate::{
        evaluate,
        fft::{domain::FFTDomain, tests::to_polynomial},
        fields::PrimeFieldElement64,
        interpolate, FiniteField, KnownOrder, Polynomial, UnivariatePolynomial,
    };
    use rand::{prelude::StdRng, SeedableRng};

    #[test]
    // Recover p(x) = 5 + x + 4x^2 + x^3 from its values.
    fn test_interpolate() {
        type F = PrimeFieldElement64<13>;
        let g = F::new(8); // 8 is a 4th root of unity of F.
        let domain = FFTDomain::from_generator(g, 4);
        // Evaluations of p(x) = 5 + x + 4x^2 + x^3 at 1,w,w^2,w^3
        let values = [F::new(11), F::new(1), F::new(7), F::new(1)];
        let p = interpolate(&values, &domain);
        let expected_p = to_polynomial::<F>(&[5, 1, 4, 1]);
        assert_eq!(p, expected_p);
    }

    #[test]
    // Property: Evaluating then interpolating should recover the original polynomial.
    fn test_evaluate_then_interpolate_gf_13() {
        let mut rng = StdRng::seed_from_u64(179922776);
        type F = PrimeFieldElement64<13>;
        for n in [1, 2, 4] {
            for _i in 0..100 {
                let g = F::root_of_unity(n, &mut rng);
                let domain = FFTDomain::from_generator(g, n as usize);
                // n points uniquely determine a polynomial of degree n-1.
                let p = UnivariatePolynomial::<F>::rand(n - 1, &mut rng);
                let evaluations = evaluate(&p, &domain);
                let recovered_p = interpolate(&evaluations, &domain);
                assert_eq!(p, recovered_p);
            }
        }
    }

    /// Evaluating then interpolating recovers the polynomial over both 254-bit scalar fields.
    ///
    /// The first NTT round trip over a field whose order needs four limbs. The domain comes from
    /// the two-adic construction, so this exercises the whole path the wide fields previously had
    /// no access to.
    #[test]
    fn test_evaluate_then_interpolate_over_the_wide_fields() {
        use crate::fields::{Bls12_381Fr, Bn254Fr};

        fn round_trip<F: FiniteField + KnownOrder>(seed: u64) {
            let mut rng = StdRng::seed_from_u64(seed);
            for log_n in 0..=5u32 {
                let n = 1usize << log_n;
                let w = F::two_adic_root_of_unity(log_n, &mut rng);
                let domain = FFTDomain::from_generator(w, n);
                let p = UnivariatePolynomial::<F>::rand(n as u64 - 1, &mut rng);
                let evaluations = evaluate(&p, &domain);
                assert_eq!(interpolate(&evaluations, &domain), p, "n = {n}");
            }
        }

        round_trip::<Bn254Fr>(31);
        round_trip::<Bls12_381Fr>(37);
    }

    /// Interpolation agrees with Horner on the recovered polynomial, over every measured field.
    ///
    /// A round trip alone would pass if the forward and inverse transforms were inverse but both
    /// wrong, so the recovered coefficients are also checked against the values they came from by
    /// direct evaluation at each domain point.
    #[test]
    fn test_interpolate_agrees_with_direct_evaluation_over_every_field() {
        use crate::fields::{Bls12_381Fr, Bn254Fr, KoalaBear, Mersenne31, PrimeFieldElement64};

        fn check<F: KnownOrder>(seed: u64) {
            let mut rng = StdRng::seed_from_u64(seed);
            let highest = F::two_adicity().min(9);
            for log_n in 0..=highest {
                let n = 1usize << log_n;
                let w = F::two_adic_root_of_unity(log_n, &mut rng);
                let domain = FFTDomain::from_generator(w, n);
                let values: Vec<F> = (0..n).map(|_| F::random(&mut rng)).collect();

                let p = interpolate(&values, &domain);
                assert!((p.degree() as usize) < n, "n = {n}");
                for (i, value) in values.iter().enumerate() {
                    assert_eq!(p.eval(&domain[i]), *value, "n = {n}, point {i}");
                }
            }
        }

        check::<KoalaBear>(0x4b11);
        check::<Mersenne31>(0x4d11);
        check::<PrimeFieldElement64<2_130_706_433>>(0x4b12);
        check::<PrimeFieldElement64<18_446_744_069_414_584_321>>(0x6011);
        check::<Bn254Fr>(0xb211);
        check::<Bls12_381Fr>(0xb311);
    }

    /// Evaluating then interpolating recovers the polynomial at sizes that are not powers of two.
    ///
    /// The inverse direction needs nothing new — the same prime-factor decomposition over the
    /// inverse domain, scaled by `1/n` — and this is what says so. `1/n` exists for every size a
    /// domain exists at: a primitive `n`th root of unity requires `n | q - 1`.
    #[test]
    fn test_evaluate_then_interpolate_at_sizes_that_are_not_powers_of_two() {
        // 65520 = 2^4 * 3^2 * 5 * 7 * 13.
        type F = PrimeFieldElement64<65521>;
        let mut rng = StdRng::seed_from_u64(0x125c);
        for n in [3u64, 5, 6, 9, 12, 15, 45, 63, 105, 144, 2520] {
            let g = F::root_of_unity(n, &mut rng);
            let domain = FFTDomain::from_generator(g, n as usize);
            let p = UnivariatePolynomial::<F>::rand(n - 1, &mut rng);
            let evaluations = evaluate(&p, &domain);
            assert_eq!(interpolate(&evaluations, &domain), p, "n = {n}");

            // And the recovered coefficients against the values themselves, so a forward and
            // inverse transform that were inverse but both wrong would still fail.
            let values: Vec<F> = (0..n).map(|_| F::random(&mut rng)).collect();
            let q = interpolate(&values, &domain);
            for (i, value) in values.iter().enumerate() {
                assert_eq!(q.eval(&domain[i]), *value, "n = {n}, point {i}");
            }
        }
    }

    /// A length mismatch between the values and the domain is rejected.
    #[test]
    #[should_panic]
    fn test_interpolate_rejects_a_length_mismatch() {
        type F = PrimeFieldElement64<97>;
        let mut rng = StdRng::seed_from_u64(0x9711);
        let w = F::two_adic_root_of_unity(4, &mut rng);
        let domain = FFTDomain::from_generator(w, 16);
        let _p = interpolate(&[F::new(1), F::new(2)], &domain);
    }

    #[test]
    // Property: Evaluating then interpolating should recover the original polynomial.
    fn test_evaluate_then_interpolate_gf_97() {
        let mut rng = StdRng::seed_from_u64(1790076);
        // 97 = 3*2^5 + 1.
        type F = PrimeFieldElement64<97>;
        // The group order 3*2^5 is a product of small primes, including a good power of 2.
        for n in [1, 2, 4, 8, 16, 32] {
            for _i in 0..100 {
                let g = F::root_of_unity(n, &mut rng);
                let domain = FFTDomain::from_generator(g, n as usize);
                // n points uniquely determine a polynomial of degree n-1.
                let p = UnivariatePolynomial::<F>::rand(n - 1, &mut rng);
                let evaluations = evaluate(&p, &domain);
                let recovered_p = interpolate(&evaluations, &domain);
                assert_eq!(p, recovered_p);
            }
        }
    }
}
