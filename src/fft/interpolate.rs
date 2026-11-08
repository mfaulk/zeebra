//! Inverse Fast Fourier Transform (IFFT).

use std::fmt::{Display, Formatter};

use crate::{
    fft::{domain::FFTDomain, prime_factor::transform_any},
    FiniteField, UnivariatePolynomial,
};

/// Why an inverse transform is not defined over a field and size.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum InterpolateError {
    /// The characteristic divides `size`, so the scalar `size` is zero and `1/size` does not exist.
    SizeNotInvertible { size: usize },
}

impl Display for InterpolateError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::SizeNotInvertible { size } => write!(
                f,
                "a transform of size {size} is not invertible over a field whose characteristic \
                 divides {size}: the scalar {size} is zero there, so 1/{size} does not exist"
            ),
        }
    }
}

impl std::error::Error for InterpolateError {}

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
///
/// # Panics
/// Panics on a length mismatch, and on a size the field's characteristic divides. See
/// [`try_interpolate`], which returns the latter as an [`InterpolateError`].
pub fn interpolate<F: FiniteField>(x: &[F], w: &FFTDomain<F>) -> UnivariatePolynomial<F> {
    try_interpolate(x, w).unwrap_or_else(|e| panic!("{e}"))
}

/// [`interpolate`], returning the ill-posed case rather than panicking on it.
///
/// The only such case is a transform size the characteristic divides, where `1/n` does not exist.
/// A length mismatch stays a panic: that is a caller bug and not a fact about the field.
pub fn try_interpolate<F: FiniteField>(
    x: &[F],
    w: &FFTDomain<F>,
) -> Result<UnivariatePolynomial<F>, InterpolateError> {
    assert_eq!(x.len(), w.size());

    // `c / n` would invert n once per coefficient: `Div` on a field element is multiplication by
    // `inverse()`, and nothing memoizes it. One inversion for the whole vector instead.
    //
    // n is invertible whenever the domain was built from a primitive root: that needs n | q - 1,
    // so n is coprime to the characteristic. The unchecked `FFTDomain::new` is the route that gets
    // here otherwise, and over characteristic two it is every even size — `F::new(n)` is `n mod 2`
    // there, so the scalar is zero and `inverse()` would panic about the zero element rather than
    // about the transform. Refused here instead, where the reason can be stated (#396).
    let size = F::new(w.size() as u64);
    if size.is_zero() {
        return Err(InterpolateError::SizeNotInvertible { size: w.size() });
    }
    let size_inverse = size.inverse();

    // The inverse domain is built before the coefficient buffer, not after: `batch_inverse` holds
    // a vector of prefix products alongside its result, and that transient is the peak. Taking it
    // while only one n-element vector is live keeps the whole call at two.
    let w_inv = w.inverse();

    let mut coefficients = x.to_vec();
    // `w.bluestein_domain()`, not `w_inv`'s: `inverse()` does not carry the prepared capability
    // forward, and it does not need to. The convolution domain depends only on the *size*, which
    // inversion preserves, so the one `w` holds is exactly the one the inverse transform wants.
    transform_any(&mut coefficients, w_inv.powers(), w.bluestein_domain());
    for c in coefficients.iter_mut() {
        *c *= size_inverse;
    }
    Ok(UnivariatePolynomial::from_coefficients(coefficients))
}

#[cfg(test)]
mod tests {
    use crate::{
        evaluate,
        fft::{domain::FFTDomain, tests::to_polynomial},
        fields::{Gf256, PrimeFieldElement64},
        interpolate, try_interpolate, FiniteField, InterpolateError, KnownOrder, One, Polynomial,
        UnivariatePolynomial,
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

    /// A size the characteristic divides is refused by name, not by a panic about a zero inverse.
    #[test]
    fn test_a_size_the_characteristic_divides_is_refused() {
        type F = Gf256;
        // Hand-built, because `try_from_generator` cannot produce this: a primitive n-th root of
        // unity needs n | q - 1, and q - 1 = 255 is odd. The unchecked constructor is the only
        // route to the condition, which is why it is a refusal and not an impossibility.
        let domain = FFTDomain::new(vec![F::one(), F::one()]);
        assert_eq!(
            try_interpolate(&[F::one(), F::one()], &domain),
            Err(InterpolateError::SizeNotInvertible { size: 2 })
        );
    }

    /// A 15-point domain over `Gf256` round-trips: 15 | 255 and 15 is odd, so `1/15` exists.
    #[test]
    fn test_evaluate_then_interpolate_gf_256() {
        type F = Gf256;
        let mut rng = StdRng::seed_from_u64(0x396);
        // 255 = 3 * 5 * 17, so the multiplicative group has elements of order 15 and no element
        // of any even order at all.
        let g = F::root_of_unity(15, &mut rng);
        let domain = FFTDomain::from_generator(g, 15);
        for _ in 0..16 {
            let p = UnivariatePolynomial::<F>::rand(14, &mut rng);
            let evaluations = evaluate(&p, &domain);
            assert_eq!(interpolate(&evaluations, &domain), p);
        }
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
