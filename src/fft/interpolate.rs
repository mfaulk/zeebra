//! Inverse Fast Fourier Transform (IFFT).

use crate::{
    fft::{domain::FFTDomain, evaluate::evaluate},
    FiniteField, UnivariatePolynomial,
};

/// Interpolate the points (w_i, x_i) into a polynomial P.
///
/// # Arguments
/// * `x` - the values P(1), P(w), P(w^2), ... P(w^{n-1}).
/// * `w` - Evaluation domain 1, w, w^2, ...
///
/// n must be a power of 2.
pub fn interpolate<F: FiniteField>(x: &[F], w: &FFTDomain<F>) -> UnivariatePolynomial<F> {
    assert_eq!(x.len(), w.size());
    let n = F::new(w.size() as u64);
    let w_inv = w.inverse();
    let unscaled_coefficients = evaluate(&UnivariatePolynomial::new(x), &w_inv);
    let coefficients: Vec<_> = unscaled_coefficients.into_iter().map(|c| c / n).collect();
    UnivariatePolynomial::new(&coefficients)
}

#[cfg(test)]
mod tests {
    use crate::{
        evaluate,
        fft::{domain::FFTDomain, tests::to_polynomial},
        fields::PrimeFieldElement64,
        interpolate, FiniteField, Polynomial, UnivariatePolynomial,
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
