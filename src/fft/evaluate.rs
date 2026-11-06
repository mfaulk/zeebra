//! The Finite Field Fast Fourier Transform
//!
//! (See https://www.csee.umbc.edu/~phatak/691a/fft-lnotes/fftnotes.pdf)
//! (See https://www.csa.iisc.ac.in/~chandan/courses/CNT/notes/lec6.pdf)
//!
//! A Fourier Transform is a sequence of n points constituting the evaluation of a polynomial
//! with coefficients {a_0, ..., a_{n-1}} at the points {w^0, ..., w^{n-1}} where w is a primitive
//! nth root of unity.
//!
//! ```text
//! |    A(1)    |             |  1  1  ...  ...                1     |     |   a_0   |
//! |    A(w)    |             |  1  w  w^2  ...             w^{n-1}  |     |   a_1   |
//! |    A(w^2)  |      =      |  1  ...                       ...    |  *  |   a_2   |
//! |     ...    |             |  1  ...                       ...    |     |   ...   |
//! | A(w^{n-1}) |             |  1  w^{n-1} w^2(n-1) ... w^{(n-1)^2} |     | a_{n-1} |
//! ```
//!
//! When n is even, n=2k, we define two polynomials using the even and odd coefficients:
//!
//! ```text
//! A_even(x) = \sum_0^{k-1} a_{2i} * x^i
//!
//! A_odd(x)  = \sum_0^{k-1} a_{2i+1} * x^i
//!
//! A(x) = A_even(x^2) + x*A_odd(x^2)
//! ```
//!
//! That recurrence is what the transform computes, but it is not how: the split is unrolled into
//! `log n` iterative passes over one buffer by [`transform_in_place`](super::transform).
//!

use crate::{
    fft::{domain::FFTDomain, transform::transform_in_place},
    FiniteField, Polynomial,
};

/// Evaluate a polynomial at the points w^0, ..., w^{n-1}, where n is a power of 2.
///
/// # Arguments
/// * `p` - A polynomial of degree less than n with coefficients in a finite field F.
/// * `w` - Powers w^0, ..., w^{n-1} of w, a primitive nth root of unity of F.
///
/// # Zero padding, and what the caller still owes
///
/// **The transform pads internally.** A polynomial of any degree below `n` is extended with zeros
/// to the domain size here, in the one allocation that becomes the result, so a caller never
/// builds a padded coefficient vector of its own. What the caller still chooses is `n`, because
/// the domain is the caller's: a product of two degree-`d` polynomials needs `n > 2d`, and only the
/// caller knows that. This is the division of labour #124 wants — pick a domain size, hand over
/// the unpadded operands.
///
/// # Panics
///
/// Panics if `p` has degree `n` or more. That is a genuinely over-degree input: `n` evaluations
/// cannot determine it, so silently transforming a truncation would be worse than refusing. Also
/// panics if `w` is not the powers of a primitive `n`th root of unity — see
/// [`transform_in_place`].
pub fn evaluate<F: FiniteField>(p: &impl Polynomial<F>, w: &FFTDomain<F>) -> Vec<F> {
    let d = p.degree() as usize;
    let n = w.size();
    assert!(d < n, "p has degree {} but must be less than {}", d, n);

    let coefficients = p.coefficients();
    let mut values = vec![F::zero(); n];
    values[..coefficients.len()].copy_from_slice(coefficients);
    transform_in_place(&mut values, w.powers());
    values
}

#[cfg(test)]
mod tests {
    use crate::{
        fft::{domain::FFTDomain, evaluate::evaluate, tests::to_polynomial},
        fields::PrimeFieldElement64,
        identities::{One, Zero},
        FiniteField, KnownOrder, Polynomial, UnivariatePolynomial,
    };
    use rand::{prelude::StdRng, SeedableRng};

    #[test]
    // Evaluating the zero polynomial should always produce zero.
    fn test_evaluate_zero_polynomial() {
        let mut rng = StdRng::seed_from_u64(13326);
        type F = PrimeFieldElement64<13>;
        let p = to_polynomial::<F>(&[0]);
        let generator = F::root_of_unity(4, &mut rng);
        let w = FFTDomain::from_generator(generator, 4);
        let evaluations = evaluate(&p, &w);
        assert_eq!(evaluations.len(), 4);
        assert_eq!(evaluations, vec!(F::zero(); 4));
    }

    #[test]
    // Evaluating a constant polynomial should always produce a_0.
    fn test_evaluate_constant_polynomial() {
        let mut rng = StdRng::seed_from_u64(17726);
        type F = PrimeFieldElement64<13>;
        let p = to_polynomial::<F>(&[6]);
        let generator = F::root_of_unity(4, &mut rng);
        let w = FFTDomain::from_generator(generator, 4);
        let evaluations = evaluate(&p, &w);
        // let w = F::root_of_unity(4, &mut rng);
        // let w_powers = powers_of(&w, 4);
        // let evaluations = evaluate(&p, &w_powers);
        assert_eq!(evaluations.len(), 4);
        assert_eq!(evaluations, vec!(F::new(6); 4));
    }

    #[test]
    // Evaluate a degree-1 polynomial.
    fn test_evaluate_linear_polynomial() {
        let mut rng = StdRng::seed_from_u64(179026);
        type F = PrimeFieldElement64<13>;
        // p(x) = 6 + x
        let p = to_polynomial::<F>(&[6, 1]);
        let generator = F::root_of_unity(4, &mut rng);
        let w = FFTDomain::from_generator(generator, 4);
        let evaluations = evaluate(&p, &w);
        assert_eq!(evaluations.len(), 4);
        // p(1) = (6 + 1) mod 13
        // p(w) = (6 + w) mod 13
        // p(w^2) = (6 + w^2) mod 13
        // p(w^3) = (6 + w^3) mod 13
        let expected = [
            F::new(7),
            w[1] + F::new(6),
            w[2] + F::new(6),
            w[3] + F::new(6),
        ];
        assert_eq!(evaluations, expected);
    }

    #[test]
    // Evaluate a degree-2 polynomial.
    fn test_evaluate_quadratic_polynomial() {
        let mut rng = StdRng::seed_from_u64(179026);
        type F = PrimeFieldElement64<13>;
        // p(x) = 6 + 4x^2
        let p = to_polynomial::<F>(&[6, 0, 4]);
        let generator = F::root_of_unity(4, &mut rng);
        let w = FFTDomain::from_generator(generator, 4);
        let evaluations = evaluate(&p, &w);
        assert_eq!(evaluations.len(), 4);
        // p(1) = (6 + 4) mod 13
        // p(w) = (6 + 4w^2) mod 13
        // p(w^2) = (6 + 4w^4) mod 13
        // p(w^3) = (6 + 4w^6) mod 13
        let expected = [
            F::new(10),
            F::new(6) + F::new(4) * w[1].pow(2),
            F::new(6) + F::new(4) * w[2].pow(2),
            F::new(6) + F::new(4) * w[3].pow(2),
        ];
        assert_eq!(evaluations, expected);
    }

    #[test]
    // Evaluate a degree-3 polynomial.
    fn test_evaluate_cubic_polynomial() {
        type F = PrimeFieldElement64<13>;
        // p(x) = 5 + x + 4x^2 + x^3
        let p = to_polynomial::<F>(&[5, 1, 4, 1]);
        let generator = F::new(8); // 8 is a 4th root of unity of F.
        let w = FFTDomain::from_generator(generator, 4);
        let evaluations = evaluate(&p, &w);
        assert_eq!(evaluations.len(), 4);

        // sage: R.<x>=GF(13)[]
        // sage: f = 5 + x + 4*x^2 + x^3
        // sage: f(1)
        // 11
        // etc.

        let expected = [F::new(11), F::new(1), F::new(7), F::new(1)];
        assert_eq!(evaluations, expected);
    }

    /// Building a domain from a generator that is not an nth root of unity is rejected.
    #[test]
    #[should_panic(expected = "root of unity")]
    fn test_evaluate_w_not_nth_root_of_unity() {
        type F = PrimeFieldElement64<541>;
        // 2^4 = 16 != 1 in GF(541), so 2 does not generate a domain of size 4.
        let _domain = FFTDomain::<F>::from_generator(F::new(2), 4);
    }

    /// The transform agrees with evaluating the polynomial at each power of w, one at a time.
    ///
    /// Over BN254's scalar field, where there was no transform at all until `root_of_unity`
    /// stopped being `unimplemented!()`. Direct Horner evaluation shares no code with the
    /// recursive split, so this pins the wide-field NTT against an independent computation
    /// rather than against itself.
    #[test]
    fn test_evaluate_agrees_with_direct_evaluation_over_bn254_fr() {
        use crate::{fields::Bn254Fr, KnownOrder};

        let mut rng = StdRng::seed_from_u64(20261105);
        for log_n in 0..=5u32 {
            let n = 1usize << log_n;
            let w = Bn254Fr::two_adic_root_of_unity(log_n, &mut rng);
            let domain = FFTDomain::from_generator(w, n);
            let p = UnivariatePolynomial::<Bn254Fr>::rand(n as u64 - 1, &mut rng);

            let transformed = evaluate(&p, &domain);
            assert_eq!(transformed.len(), n);
            for (i, value) in transformed.iter().enumerate() {
                assert_eq!(*value, p.eval(&domain[i]), "n = {n}, point {i}");
            }
        }
    }

    /// The transform agrees with Horner evaluation point by point over the narrow fields, at a
    /// size well past anything the small hand-checked cases reach.
    ///
    /// The wide-field agreement test above covered BN254 only. These four are the fields
    /// `examples/univariate_scaling.rs` measures, plus BLS12-381; Horner shares no code with the
    /// kernel, so a forward and inverse transform that were inverse but both wrong would fail
    /// here.
    #[test]
    fn test_evaluate_agrees_with_direct_evaluation_over_every_field() {
        use crate::fields::{Bls12_381Fr, KoalaBear};

        fn check<F: KnownOrder>(seed: u64) {
            let mut rng = StdRng::seed_from_u64(seed);
            let highest = F::two_adicity().min(10);
            for log_n in 0..=highest {
                let n = 1usize << log_n;
                let w = F::two_adic_root_of_unity(log_n, &mut rng);
                let domain = FFTDomain::from_generator(w, n);
                let p = UnivariatePolynomial::<F>::rand(n as u64 - 1, &mut rng);

                let transformed = evaluate(&p, &domain);
                assert_eq!(transformed.len(), n);
                for (i, value) in transformed.iter().enumerate() {
                    assert_eq!(*value, p.eval(&domain[i]), "n = {n}, point {i}");
                }
            }
        }

        check::<KoalaBear>(0x4b01);
        check::<PrimeFieldElement64<2_130_706_433>>(0x4b02);
        check::<PrimeFieldElement64<18_446_744_069_414_584_321>>(0x601d);
        check::<Bls12_381Fr>(0xb12);
    }

    /// Mersenne-31 supports a transform of size 1 and 2 and nothing larger: its two-adicity is 1.
    ///
    /// The unsupported case fails as a clear panic from `two_adic_root_of_unity`, which is where
    /// the bound lives, rather than silently producing a wrong transform.
    #[test]
    fn test_mersenne31_supports_only_sizes_one_and_two() {
        use crate::fields::Mersenne31;

        assert_eq!(Mersenne31::two_adicity(), 1);

        let mut rng = StdRng::seed_from_u64(0x4d31);
        for log_n in 0..=1u32 {
            let n = 1usize << log_n;
            let w = Mersenne31::two_adic_root_of_unity(log_n, &mut rng);
            let domain = FFTDomain::from_generator(w, n);
            let p = UnivariatePolynomial::<Mersenne31>::rand(n as u64 - 1, &mut rng);
            let transformed = evaluate(&p, &domain);
            for (i, value) in transformed.iter().enumerate() {
                assert_eq!(*value, p.eval(&domain[i]), "n = {n}, point {i}");
            }
        }

        let attempt = std::panic::catch_unwind(|| {
            let mut rng = StdRng::seed_from_u64(0x4d32);
            Mersenne31::two_adic_root_of_unity(2, &mut rng)
        });
        assert!(
            attempt.is_err(),
            "a primitive 4th root of unity must not be claimed over Mersenne-31"
        );
    }

    /// A polynomial of degree far below n is zero-padded internally: the caller passes it unpadded.
    #[test]
    fn test_evaluate_pads_a_low_degree_polynomial_internally() {
        type F = PrimeFieldElement64<97>;
        let mut rng = StdRng::seed_from_u64(0x9701);
        let n = 32usize;
        let w = F::two_adic_root_of_unity(5, &mut rng);
        let domain = FFTDomain::from_generator(w, n);
        // Degree 2 over a size-32 domain: 29 coefficients the caller never supplied.
        let p = to_polynomial::<F>(&[5, 1, 4]);
        assert_eq!(p.coefficients().len(), 3);

        let transformed = evaluate(&p, &domain);
        assert_eq!(transformed.len(), n);
        for (i, value) in transformed.iter().enumerate() {
            assert_eq!(*value, p.eval(&domain[i]), "point {i}");
        }
    }

    /// Degree exactly n-1 is accepted and degree exactly n is refused: the panic boundary.
    #[test]
    fn test_the_degree_boundary_is_n_minus_one() {
        type F = PrimeFieldElement64<97>;
        let mut rng = StdRng::seed_from_u64(0x9702);
        let n = 16usize;
        let w = F::two_adic_root_of_unity(4, &mut rng);
        let domain = FFTDomain::from_generator(w, n);

        let at_the_boundary = UnivariatePolynomial::<F>::rand(n as u64 - 1, &mut rng);
        assert_eq!(at_the_boundary.degree() as usize, n - 1);
        let transformed = evaluate(&at_the_boundary, &domain);
        for (i, value) in transformed.iter().enumerate() {
            assert_eq!(*value, at_the_boundary.eval(&domain[i]), "point {i}");
        }

        let over_degree = UnivariatePolynomial::<F>::rand(n as u64, &mut rng);
        let refused = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            evaluate(&over_degree, &domain)
        }));
        assert!(refused.is_err(), "degree n must be refused, not truncated");
    }

    /// Size 1 evaluates a constant polynomial to itself, and size 2 to a_0 + a_1 and a_0 - a_1.
    #[test]
    fn test_the_degenerate_sizes() {
        type F = PrimeFieldElement64<97>;
        let mut rng = StdRng::seed_from_u64(0x9703);

        let one = FFTDomain::from_generator(F::two_adic_root_of_unity(0, &mut rng), 1);
        assert_eq!(evaluate(&to_polynomial::<F>(&[7]), &one), vec![F::new(7)]);
        assert_eq!(evaluate(&to_polynomial::<F>(&[0]), &one), vec![F::zero()]);

        let two = FFTDomain::from_generator(F::two_adic_root_of_unity(1, &mut rng), 2);
        assert_eq!(two[1], F::zero() - F::one());
        let p = to_polynomial::<F>(&[7, 3]);
        assert_eq!(evaluate(&p, &two), vec![F::new(10), F::new(4)]);
    }

    #[test]
    #[should_panic]
    // Panics if the degree of p >= n.
    fn test_p_degree_too_high() {
        let mut rng = StdRng::seed_from_u64(17);
        type F = PrimeFieldElement64<97>;
        let n = 16;
        let generator = F::root_of_unity(n, &mut rng);
        let w = FFTDomain::from_generator(generator, n as usize);

        // The degree of p should be less than n.
        let p = UnivariatePolynomial::<F>::rand(n, &mut rng);

        let _evaluations = evaluate(&p, &w);
    }
}
