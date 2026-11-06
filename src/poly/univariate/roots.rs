//! Finding the roots of a univariate polynomial in a finite field.
//!
//! Every element of GF(q) satisfies a^q = a, so
//!
//! ```text
//! x^q - x = product over a in GF(q) of (x - a)
//! ```
//!
//! and `gcd(f, x^q - x)` is therefore exactly the product of `(x - a)` over the *distinct* roots
//! of f that lie in GF(q). One gcd both discards the irreducible factors of higher degree, whose
//! roots live only in an extension, and collapses multiplicities. What remains is a squarefree
//! product of linear factors, which equal-degree splitting breaks apart.
//!
//! This is the degree-one case of [`factorize`](super::factorize), and shares its splitter. It
//! stays separate because it needs only that one degree, where full factorization works through
//! every degree up to that of f.
//!
//! # References
//! * A Computational Introduction to Number Theory and Algebra, 20.2 and 21.3

use rand::{CryptoRng, RngCore};

use crate::{
    poly::univariate::{
        factorize::separate_equal_degree, gcd, pow_mod::pow_mod_limbs, Polynomial,
        UnivariatePolynomial,
    },
    KnownOrder,
};

/// The distinct roots of `f` in F, in unspecified order.
///
/// A root of multiplicity greater than one is reported once. Roots lying only in an extension of
/// F are not reported, since they are not elements of F.
///
/// # Panics
/// Panics if `f` is the zero polynomial, every element of which is a root.
pub fn roots<F: KnownOrder, R: RngCore + CryptoRng>(
    f: &UnivariatePolynomial<F>,
    rng: &mut R,
) -> Vec<F> {
    assert!(
        !f.is_zero(),
        "every element is a root of the zero polynomial"
    );

    // A nonzero constant has no roots.
    if f.degree() == 0 {
        return Vec::new();
    }

    // gcd(f, x^q - x) keeps exactly the distinct roots of f that lie in F. `x^q` is reduced
    // modulo f as it is built, since materializing it would need q coefficients, and the
    // exponent is the order's limbs so that a 254-bit q is no different from a 31-bit one.
    let x = UnivariatePolynomial::new(&[F::zero(), F::one()]);
    let x_to_the_q = pow_mod_limbs(&x, F::order_limbs(), f);
    let linear_part = gcd(f, &(&x_to_the_q - &x));

    // A constant gcd means f shares no linear factor with x^q - x, i.e. has no root in F.
    if linear_part.is_zero() || linear_part.degree() == 0 {
        return Vec::new();
    }

    // Each linear factor is monic after splitting a monic product, so c_1 x + c_0 vanishes at
    // -c_0 / c_1.
    separate_equal_degree(&linear_part, 1, rng)
        .iter()
        .map(|factor| {
            let coefficients = factor.coefficients();
            F::zero() - coefficients[0] / coefficients[1]
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use rand::{prelude::StdRng, SeedableRng};

    use crate::{
        fields::{
            Bls12_381Fr, Bn254Fr, PrimeFieldElement256, PrimeFieldElement64, PrimeModulus256,
        },
        identities::{One, Zero},
        poly::univariate::{roots::roots, Polynomial, UnivariatePolynomial},
        FiniteField, KnownOrder,
    };

    /// Every element of F at which `f` vanishes, found by trying all of them.
    ///
    /// Shares no code with `roots`: no gcd, no modular exponentiation, no splitting.
    fn by_evaluation<const P: u64>(
        f: &UnivariatePolynomial<PrimeFieldElement64<P>>,
    ) -> HashSet<PrimeFieldElement64<P>> {
        (0..P)
            .map(PrimeFieldElement64::<P>::new)
            .filter(|a| f.eval(a).is_zero())
            .collect()
    }

    fn poly<const P: u64>(coefficients: &[u64]) -> UnivariatePolynomial<PrimeFieldElement64<P>> {
        UnivariatePolynomial::new(
            &coefficients
                .iter()
                .map(|c| PrimeFieldElement64::<P>::new(*c))
                .collect::<Vec<_>>(),
        )
    }

    /// `roots` agrees with evaluating at every element of the field.
    #[test]
    fn test_roots_agree_with_evaluation() {
        fn check<const P: u64>(seed: u64) {
            let mut rng = StdRng::seed_from_u64(seed);
            // Coefficients are low-order first.
            let polynomials: Vec<Vec<u64>> = vec![
                vec![1, 1],           // x + 1
                vec![0, 1],           // x
                vec![P - 1, 0, 1],    // x^2 - 1, two roots
                vec![1, 0, 1],        // x^2 + 1, roots only when -1 is a square
                vec![0, 0, 1],        // x^2, a repeated root
                vec![0, 0, 0, 1],     // x^3
                vec![P - 1, 0, 0, 1], // x^3 - 1
                vec![2, 3, 1],        // a generic quadratic
                vec![1, 2, 3, 4],     // a generic cubic
                vec![1],              // a nonzero constant, no roots (5 would vanish in GF(5))
                vec![1, 1, 1, 1, 1],  // a generic quartic
            ];

            for coefficients in &polynomials {
                let f = poly::<P>(coefficients);
                let expected = by_evaluation::<P>(&f);
                let found: HashSet<_> = roots(&f, &mut rng).into_iter().collect();
                assert_eq!(
                    found, expected,
                    "coefficients {:?} over GF({})",
                    coefficients, P
                );

                // Each reported root must genuinely be one, and each must appear once.
                let as_vec = roots(&f, &mut rng);
                assert_eq!(as_vec.len(), found.len(), "duplicate roots reported");
                for a in &as_vec {
                    assert!(f.eval(a).is_zero(), "{} is not a root of {}", a, f);
                }
            }
        }

        // GF(2) exercises the characteristic-two splitter; the rest exercise the odd-q one.
        check::<2>(1);
        check::<3>(2);
        check::<5>(3);
        check::<7>(4);
        check::<13>(5);
        check::<31>(6);
    }

    /// x^q - x splits completely, so every element of the field is a root.
    #[test]
    fn test_roots_of_x_to_the_q_minus_x() {
        const P: u64 = 11;
        let mut rng = StdRng::seed_from_u64(7);
        // x^11 - x
        let mut coefficients = vec![0u64; 12];
        coefficients[11] = 1;
        coefficients[1] = P - 1;
        let f = poly::<P>(&coefficients);

        let found: HashSet<_> = roots(&f, &mut rng).into_iter().collect();
        assert_eq!(found.len(), P as usize);
        assert_eq!(found, by_evaluation::<P>(&f));
    }

    /// The product of (x - a) over the reported roots divides f.
    #[test]
    fn test_root_factors_divide_the_polynomial() {
        const P: u64 = 13;
        let mut rng = StdRng::seed_from_u64(11);
        let polynomials: Vec<Vec<u64>> = vec![
            vec![P - 1, 0, 1],
            vec![0, 0, 1],
            vec![1, 2, 3, 4],
            vec![P - 1, 0, 0, 1],
            vec![1, 1, 1, 1, 1],
        ];

        for coefficients in &polynomials {
            let f = poly::<P>(coefficients);
            let product = roots(&f, &mut rng).into_iter().fold(
                UnivariatePolynomial::<PrimeFieldElement64<P>>::one(),
                |acc, a| {
                    let linear = UnivariatePolynomial::new(&[
                        PrimeFieldElement64::<P>::zero() - a,
                        PrimeFieldElement64::<P>::one(),
                    ]);
                    acc * linear
                },
            );
            assert!(
                (&f % &product).is_zero(),
                "{} does not divide {}",
                product,
                f
            );
        }
    }

    /// A polynomial irreducible over F has no roots in F, though it has them in an extension.
    #[test]
    fn test_no_roots_for_an_irreducible_polynomial() {
        const P: u64 = 7;
        let mut rng = StdRng::seed_from_u64(13);
        // x^2 + 1 over GF(7): the squares are {1, 2, 4}, so -1 = 6 is not among them.
        let f = poly::<P>(&[1, 0, 1]);
        for a in 0..P {
            assert!(!f.eval(&PrimeFieldElement64::<P>::new(a)).is_zero());
        }
        assert!(roots(&f, &mut rng).is_empty());
    }

    /// A repeated root is reported exactly once.
    #[test]
    fn test_repeated_roots_are_reported_once() {
        const P: u64 = 13;
        let mut rng = StdRng::seed_from_u64(17);
        // (x - 3)^4
        let three = PrimeFieldElement64::<P>::new(3);
        let linear = UnivariatePolynomial::new(&[
            PrimeFieldElement64::<P>::zero() - three,
            PrimeFieldElement64::<P>::one(),
        ]);
        let f = linear.pow(4);

        let found = roots(&f, &mut rng);
        assert_eq!(found, vec![three]);
    }

    /// The zero polynomial has no meaningful root set.
    #[test]
    #[should_panic(expected = "every element is a root of the zero polynomial")]
    fn test_roots_of_zero_panics() {
        let mut rng = StdRng::seed_from_u64(19);
        let _ = roots(
            &UnivariatePolynomial::<PrimeFieldElement64<7>>::zero(),
            &mut rng,
        );
    }

    /// Planted roots are recovered over a field whose order needs four limbs.
    ///
    /// This is the test that `x^q` is computed with the real order. A truncated exponent would
    /// compute `x^(q mod 2^128)`, whose gcd with f has no reason to be the product of f's linear
    /// factors, so the roots would simply not be found.
    fn planted_roots_are_found_over<M: PrimeModulus256>(seed: u64, decimals: &[&str]) {
        type Z<M> = PrimeFieldElement256<M>;
        let planted: Vec<Z<M>> = decimals
            .iter()
            .map(|d| <Z<M> as FiniteField>::from_str(d).expect("valid decimal"))
            .collect();

        // f = product of (x - a) over the planted values, so its roots are exactly those.
        let mut f = UnivariatePolynomial::<Z<M>>::one();
        for a in &planted {
            f = &f * &UnivariatePolynomial::new(&[Z::<M>::zero() - *a, Z::<M>::one()]);
        }

        let mut rng = StdRng::seed_from_u64(seed);
        let found: HashSet<Z<M>> = roots(&f, &mut rng).into_iter().collect();
        assert_eq!(
            found,
            planted.iter().copied().collect::<HashSet<_>>(),
            "roots of {f}"
        );

        // Each really is a root, by evaluation rather than by the construction above.
        for a in &found {
            assert!(f.eval(a).is_zero(), "{a} must be a root");
        }
    }

    /// Root finding works over BN254's 254-bit scalar field.
    #[test]
    fn test_roots_over_bn254_fr() {
        planted_roots_are_found_over::<crate::fields::Bn254FrModulus>(
            7,
            &["1", "7", "123456789012345678901234567890123456789"],
        );
    }

    /// Root finding works over BLS12-381's 255-bit scalar field.
    #[test]
    fn test_roots_over_bls12_381_fr() {
        planted_roots_are_found_over::<crate::fields::Bls12_381FrModulus>(
            8,
            &[
                "2",
                "99",
                "52435875175126190479447740508185965837690552500527637822603658699938581184512",
            ],
        );
    }

    /// A polynomial with no root in the base field reports none, rather than reporting a wrong one.
    ///
    /// `x^2 + 1` has roots in the base field exactly when -1 is a square there. Which of the two
    /// target fields that holds in is not assumed: the test asserts only that the answer is
    /// consistent with squaring the reported root back.
    #[test]
    fn test_roots_in_an_extension_only_are_not_reported_over_wide_fields() {
        let mut rng = StdRng::seed_from_u64(9);

        let f = UnivariatePolynomial::<Bn254Fr>::new(&[
            Bn254Fr::one(),
            Bn254Fr::zero(),
            Bn254Fr::one(),
        ]);
        for root in roots(&f, &mut rng) {
            assert_eq!(
                root * root,
                Bn254Fr::zero() - Bn254Fr::one(),
                "a reported root must square to -1"
            );
        }

        let g = UnivariatePolynomial::<Bls12_381Fr>::new(&[
            Bls12_381Fr::one(),
            Bls12_381Fr::zero(),
            Bls12_381Fr::one(),
        ]);
        for root in roots(&g, &mut rng) {
            assert_eq!(root * root, Bls12_381Fr::zero() - Bls12_381Fr::one());
        }
    }

    /// The wide fields really do have orders beyond a `u128`, so the tests above mean what they say.
    #[test]
    fn test_the_wide_fields_under_test_have_no_u128_order() {
        assert_eq!(Bn254Fr::order_u128(), None);
        assert_eq!(Bls12_381Fr::order_u128(), None);
    }
}
