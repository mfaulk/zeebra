//! Root finding by the Graeffe transform.
//!
//! The oracles below come from `docs/research/graeffe-root-finding.md` §6.3 and §10: the order-2
//! transform against directly squared roots at degree 16, [PC] Lemma 2's `GT_2 . GT_2 = GT_4`,
//! [PC] Lemma 1's degree preservation, and planted roots cross-checked against
//! `src/poly/univariate/roots.rs` at every degree it reaches.

use std::time::Duration;

use rand::{CryptoRng, RngCore};

use crate::{
    fields::RootOfUnityError, poly::univariate::UnivariatePolynomial, FFTDomain, FiniteField,
    KnownOrder,
};

/// Why a Graeffe root find could not run.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GraeffeError {
    /// An order-2 step at degree `degree` needs a power-of-two domain of `2^log_n >= degree + 1`
    /// points, and this field has no primitive `2^log_n`-th root of unity.
    DomainTooLarge {
        degree: u32,
        log_n: u32,
        two_adicity: u32,
    },
}

impl std::fmt::Display for GraeffeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}

impl std::error::Error for GraeffeError {}

/// How the roots in the final subgroup were found.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SubgroupRoute {
    Enumerated { points: u64 },
    GcdRootFinder { degree: u32 },
}

/// What one [`graeffe_root`] call cost.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GraeffeStats {
    pub graeffe_steps: u32,
    pub transforms: usize,
    pub max_transform_size: usize,
    pub total_transform_elements: usize,
    pub stored_coefficients: usize,
    pub final_degree: u32,
    pub subgroup_order: u128,
    pub subgroup_route: SubgroupRoute,
    pub candidates: usize,
    pub forward_time: Duration,
    pub subgroup_time: Duration,
    pub descent_time: Duration,
}

/// The order-2 Graeffe transform of `f`, over a domain the caller supplies.
pub fn graeffe_2_over_domain<F: FiniteField>(
    _f: &UnivariatePolynomial<F>,
    _domain: &FFTDomain<F>,
) -> UnivariatePolynomial<F> {
    todo!("(-1)^d (f_e^2 - x f_o^2), by three transforms of size deg f + 1")
}

/// The order-2 Graeffe transform of `f`, over a domain built for the occasion.
pub fn graeffe_2<F: KnownOrder, R: RngCore + CryptoRng>(
    _f: &UnivariatePolynomial<F>,
    _rng: &mut R,
) -> Result<UnivariatePolynomial<F>, GraeffeError> {
    todo!("a domain of deg f + 1 points, then graeffe_2_over_domain")
}

/// The order-`l` Graeffe transform of `f`.
pub fn graeffe_l<F: KnownOrder, R: RngCore + CryptoRng>(
    _f: &UnivariatePolynomial<F>,
    _l: u64,
    _rng: &mut R,
) -> Result<UnivariatePolynomial<F>, RootOfUnityError> {
    todo!("the product of the l scaled copies, by a product tree")
}

/// A root of `f` in F, or `None` if it has none.
pub fn graeffe_root<F: KnownOrder, R: RngCore + CryptoRng>(
    _f: &UnivariatePolynomial<F>,
    _rng: &mut R,
) -> Result<Option<F>, GraeffeError> {
    todo!("Algorithm C's forward phase, the subgroup search, and the gcd descent")
}

/// [`graeffe_root`], with what the run cost.
pub fn graeffe_root_with_stats<F: KnownOrder, R: RngCore + CryptoRng>(
    _f: &UnivariatePolynomial<F>,
    _rng: &mut R,
) -> Result<(Option<F>, GraeffeStats), GraeffeError> {
    todo!("Algorithm C's forward phase, the subgroup search, and the gcd descent")
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use rand::{prelude::StdRng, Rng, SeedableRng};

    use super::{
        graeffe_2, graeffe_2_over_domain, graeffe_l, graeffe_root, graeffe_root_with_stats,
        GraeffeError, SubgroupRoute,
    };
    use crate::{
        fields::{KoalaBear, Mersenne31, Zp18446744069414584321, Zp2147483647, Zp65537},
        poly::univariate::{roots::roots, Polynomial, UnivariatePolynomial},
        FFTDomain, FiniteField, KnownOrder, One, Zero,
    };

    /// KoalaBear in a `u32`, the field the registered 2026 Poseidon challenges are over.
    type Koala = KoalaBear;
    /// Goldilocks, `2^64 - 2^32 + 1`, whose odd part is `2^32 - 1`.
    type Goldilocks = Zp18446744069414584321;

    /// `prod (x - r_i)` from the given roots, and `prod (x - r_i^power)` beside it.
    fn planted<F: FiniteField>(roots: &[F], power: u32) -> UnivariatePolynomial<F> {
        let raised: Vec<F> = roots.iter().map(|r| r.pow(power as u128)).collect();
        UnivariatePolynomial::from_zeros(&raised)
    }

    /// `count` distinct nonzero field elements.
    fn distinct_nonzero<F: FiniteField, R: Rng>(count: usize, rng: &mut R) -> Vec<F> {
        let mut seen: Vec<F> = Vec::with_capacity(count);
        while seen.len() < count {
            let candidate = F::new(rng.gen::<u32>() as u64);
            if !candidate.is_zero() && !seen.contains(&candidate) {
                seen.push(candidate);
            }
        }
        seen
    }

    /// A polynomial of exactly `degree` with the given roots planted and a random cofactor.
    ///
    /// Building `prod (x - r_i)` over `degree` roots would be quadratic and would also measure the
    /// construction rather than the root finder; a handful of planted roots in a random cofactor
    /// is the shape a resultant or an interpolated output coordinate leaves behind.
    fn with_planted_roots<F: FiniteField, R: Rng>(
        degree: usize,
        planted_roots: &[F],
        rng: &mut R,
    ) -> UnivariatePolynomial<F> {
        let cofactor_degree = degree - planted_roots.len();
        let mut coefficients: Vec<F> = (0..=cofactor_degree)
            .map(|_| F::new(rng.gen::<u32>() as u64))
            .collect();
        while coefficients[cofactor_degree].is_zero() {
            coefficients[cofactor_degree] = F::new(rng.gen::<u32>() as u64);
        }
        &UnivariatePolynomial::new(&coefficients) * &UnivariatePolynomial::from_zeros(planted_roots)
    }

    /// `GT_2` on a degree-16 polynomial with known roots is the polynomial of their squares.
    #[test]
    fn test_the_order_two_transform_squares_the_roots() {
        let mut rng = StdRng::seed_from_u64(1);
        let planted_roots = distinct_nonzero::<Zp65537, _>(16, &mut rng);
        let f = UnivariatePolynomial::from_zeros(&planted_roots);
        assert_eq!(f.degree(), 16);
        assert_eq!(
            graeffe_2(&f, &mut rng).expect("65537 has two-adicity 16"),
            planted(&planted_roots, 2)
        );
    }

    /// The same oracle at odd degree, where the `(-1)^d` normalization is the whole difference.
    #[test]
    fn test_the_sign_convention_holds_at_odd_degree() {
        let mut rng = StdRng::seed_from_u64(2);
        let planted_roots = distinct_nonzero::<Koala, _>(15, &mut rng);
        let f = UnivariatePolynomial::from_zeros(&planted_roots);
        assert_eq!(f.degree(), 15);
        let transformed = graeffe_2(&f, &mut rng).expect("KoalaBear has two-adicity 24");
        assert_eq!(transformed, planted(&planted_roots, 2));
        // Without the normalization the result would be the negation, so this is not vacuous.
        assert_ne!(transformed.scale(&-Koala::one()), planted(&planted_roots, 2));
    }

    /// Two order-2 steps are one order-4 step, which is [PC] Lemma 2.
    #[test]
    fn test_two_order_two_steps_are_one_order_four_step() {
        let mut rng = StdRng::seed_from_u64(3);
        for degree in [7usize, 16] {
            let planted_roots = distinct_nonzero::<Zp65537, _>(degree, &mut rng);
            let f = UnivariatePolynomial::from_zeros(&planted_roots);
            let once = graeffe_2(&f, &mut rng).expect("a domain exists");
            let twice = graeffe_2(&once, &mut rng).expect("a domain exists");
            assert_eq!(twice, graeffe_l(&f, 4, &mut rng).expect("4 divides 65536"));
            assert_eq!(twice, planted(&planted_roots, 4), "degree {degree}");
        }
    }

    /// `GT_l` preserves the degree, which is [PC] Lemma 1.
    #[test]
    fn test_the_transform_preserves_the_degree() {
        let mut rng = StdRng::seed_from_u64(4);
        for degree in [1usize, 2, 5, 16, 17, 64] {
            let f = with_planted_roots::<Zp65537, _>(degree, &[Zp65537::one()], &mut rng);
            assert_eq!(f.degree() as usize, degree);
            assert_eq!(
                graeffe_2(&f, &mut rng).expect("a domain exists").degree() as usize,
                degree,
                "GT_2 changed the degree at {degree}"
            );
            assert_eq!(
                graeffe_l(&f, 2, &mut rng).expect("2 divides 65536").degree() as usize,
                degree
            );
        }
    }

    /// The three-NTT form agrees with [PC] Definition 2's product of scaled copies.
    #[test]
    fn test_the_three_transform_form_agrees_with_the_product_definition() {
        let mut rng = StdRng::seed_from_u64(5);
        for degree in [3usize, 8, 9] {
            let f = with_planted_roots::<Zp65537, _>(degree, &[Zp65537::new(3)], &mut rng);
            assert_eq!(
                graeffe_2(&f, &mut rng).expect("a domain exists"),
                graeffe_l(&f, 2, &mut rng).expect("2 divides 65536"),
                "degree {degree}"
            );
        }
    }

    /// An odd-order transform raises the roots to that power and needs no sign correction.
    #[test]
    fn test_an_odd_order_transform_raises_the_roots_to_that_power() {
        let mut rng = StdRng::seed_from_u64(6);
        // 2130706432 = 2^24 * 127, so 127 is the only odd prime order available over KoalaBear.
        for order in [127u64] {
            for degree in [4usize, 7] {
                let planted_roots = distinct_nonzero::<Koala, _>(degree, &mut rng);
                let f = UnivariatePolynomial::from_zeros(&planted_roots);
                assert_eq!(
                    graeffe_l(&f, order, &mut rng).expect("127 divides q - 1"),
                    planted(&planted_roots, order as u32),
                    "order {order} at degree {degree}"
                );
            }
        }
        // 65536 = 2^16 and 18446744069414584320 = 2^32 * 3 * 5 * 17 * 257 * 65537, so the odd
        // orders have to come from Goldilocks.
        for order in [3u64, 5, 17] {
            let planted_roots = distinct_nonzero::<Goldilocks, _>(5, &mut rng);
            let f = UnivariatePolynomial::from_zeros(&planted_roots);
            assert_eq!(
                graeffe_l(&f, order, &mut rng).expect("the order divides q - 1"),
                planted(&planted_roots, order as u32),
                "order {order}"
            );
        }
    }

    /// Lemma 2 across two different odd orders: `GT_3 . GT_5 = GT_15`.
    #[test]
    fn test_odd_orders_compose() {
        let mut rng = StdRng::seed_from_u64(7);
        let planted_roots = distinct_nonzero::<Goldilocks, _>(4, &mut rng);
        let f = UnivariatePolynomial::from_zeros(&planted_roots);
        let composed = graeffe_l(
            &graeffe_l(&f, 3, &mut rng).expect("3 divides q - 1"),
            5,
            &mut rng,
        )
        .expect("5 divides q - 1");
        assert_eq!(composed, graeffe_l(&f, 15, &mut rng).expect("15 divides"));
        assert_eq!(composed, planted(&planted_roots, 15));
    }

    /// An order that does not divide `q - 1` has no root of unity, so the transform is refused.
    #[test]
    fn test_an_order_that_does_not_divide_the_group_order_is_refused() {
        let mut rng = StdRng::seed_from_u64(8);
        let f = UnivariatePolynomial::<Koala>::from_zeros(&[Koala::one(), Koala::new(5)]);
        // q - 1 = 2^24 * 127, so 3 does not divide it.
        assert!(graeffe_l(&f, 3, &mut rng).is_err());
    }

    /// A domain with exactly `deg f + 1` points suffices, so the step is three transforms of that
    /// size rather than of twice it.
    #[test]
    fn test_a_domain_of_one_more_than_the_degree_suffices() {
        let mut rng = StdRng::seed_from_u64(9);
        let planted_roots = distinct_nonzero::<Zp65537, _>(15, &mut rng);
        let f = UnivariatePolynomial::from_zeros(&planted_roots);
        assert_eq!(f.degree(), 15);
        let generator = Zp65537::two_adic_root_of_unity(4, &mut rng);
        let domain = FFTDomain::from_generator(generator, 16);
        assert_eq!(domain.size(), 16);
        assert_eq!(
            graeffe_2_over_domain(&f, &domain),
            planted(&planted_roots, 2)
        );
    }

    /// A domain too small for the degree is a programmer error, since the caller chose it.
    #[test]
    #[should_panic(expected = "needs at least")]
    fn test_a_domain_smaller_than_the_degree_is_refused() {
        let mut rng = StdRng::seed_from_u64(10);
        let f = UnivariatePolynomial::<Zp65537>::from_zeros(&distinct_nonzero(15, &mut rng));
        let generator = Zp65537::two_adic_root_of_unity(3, &mut rng);
        let domain = FFTDomain::from_generator(generator, 8);
        let _ = graeffe_2_over_domain(&f, &domain);
    }

    /// Planted roots are recovered, and the root returned is one `roots` also reports.
    fn planted_roots_are_recovered<F: KnownOrder>(degrees: &[usize], seed: u64) {
        let mut rng = StdRng::seed_from_u64(seed);
        for &degree in degrees {
            let planted_roots = distinct_nonzero::<F, _>(4, &mut rng);
            let f = with_planted_roots::<F, _>(degree, &planted_roots, &mut rng);
            assert_eq!(f.degree() as usize, degree);

            let found = graeffe_root(&f, &mut rng)
                .expect("the field hosts a domain for this degree")
                .unwrap_or_else(|| panic!("degree {degree} has four planted roots"));
            assert!(
                f.eval(&found).is_zero(),
                "degree {degree}: {found} is not a root"
            );
            let expected: HashSet<F> = roots(&f, &mut rng).into_iter().collect();
            assert!(
                expected.contains(&found),
                "degree {degree}: {found} is not among the roots the gcd finder reports"
            );
        }
    }

    /// Over KoalaBear, the registered challenge's field, at the degrees the gcd finder reaches.
    #[test]
    fn test_planted_roots_are_recovered_over_koala_bear() {
        planted_roots_are_recovered::<Koala>(&[256, 512, 1024, 2048, 4096], 11);
    }

    /// Over Goldilocks, where the odd part of `q - 1` is `2^32 - 1` and the subgroup search falls
    /// back to the gcd route.
    #[test]
    fn test_planted_roots_are_recovered_over_goldilocks() {
        planted_roots_are_recovered::<Goldilocks>(&[256, 512], 13);
    }

    /// The same at the degrees a release build reaches, up to `2^16`.
    #[test]
    #[ignore] // Slow: 24 order-2 steps at degree 2^16 and a gcd cross-check at that degree.
    fn test_planted_roots_are_recovered_at_larger_degrees() {
        planted_roots_are_recovered::<Koala>(&[8192, 16384, 32768, 65536], 17);
        planted_roots_are_recovered::<Goldilocks>(&[1024, 2048, 4096], 19);
    }

    /// A polynomial with no base-field root returns none rather than a wrong root.
    #[test]
    fn test_no_base_field_root_returns_none() {
        let mut rng = StdRng::seed_from_u64(23);
        // x^2 - 3 over KoalaBear: 3 is a quadratic non-residue there, checked by the character.
        let f = UnivariatePolynomial::<Koala>::new(&[-Koala::new(3), Koala::zero(), Koala::one()]);
        assert_eq!(crate::fields::legendre_symbol(&Koala::new(3)), -1);
        assert_eq!(graeffe_root(&f, &mut rng), Ok(None));
        assert!(roots(&f, &mut rng).is_empty());
    }

    /// An irreducible factor of high degree with no base-field root also returns none.
    #[test]
    fn test_a_polynomial_whose_roots_lie_only_in_an_extension_returns_none() {
        let mut rng = StdRng::seed_from_u64(29);
        // x^q - x vanishes on every element, so dividing it out of a random polynomial leaves one
        // with no base-field root. Cheaper: search for one, which takes a handful of draws.
        for _ in 0..40 {
            let f = UnivariatePolynomial::<Koala>::new(&[
                Koala::new(rng.gen::<u32>() as u64),
                Koala::new(rng.gen::<u32>() as u64),
                Koala::one(),
            ]);
            if roots(&f, &mut rng).is_empty() {
                assert_eq!(graeffe_root(&f, &mut rng), Ok(None));
                return;
            }
        }
        panic!("no rootless quadratic was drawn");
    }

    /// A repeated root is found, and so is the root of a perfect square.
    #[test]
    fn test_repeated_roots_and_perfect_squares() {
        let mut rng = StdRng::seed_from_u64(31);
        let a = Koala::new(7);
        let linear = UnivariatePolynomial::<Koala>::from_zeros(&[a]);

        // (x - 7)^8, a single root of multiplicity eight.
        let repeated = linear.pow(8);
        assert_eq!(graeffe_root(&repeated, &mut rng), Ok(Some(a)));

        // A perfect square, whose every root is repeated.
        let base = with_planted_roots::<Koala, _>(32, &[a, Koala::new(11)], &mut rng);
        let square = &base * &base;
        let found = graeffe_root(&square, &mut rng)
            .expect("a domain exists")
            .expect("the square of a polynomial with roots has roots");
        assert!(square.eval(&found).is_zero());
        assert!(base.eval(&found).is_zero());

        // x^2 - a^2, where both square roots of the transform's root are roots of the input and
        // the un-squaring hits its degenerate branch.
        let pair = UnivariatePolynomial::<Koala>::from_zeros(&[a, -a]);
        let found = graeffe_root(&pair, &mut rng)
            .expect("a domain exists")
            .expect("x^2 - a^2 has two roots");
        assert!(found == a || found == -a);
    }

    /// Zero is reported when the constant term vanishes, before any transform runs.
    #[test]
    fn test_a_vanishing_constant_term_gives_zero() {
        let mut rng = StdRng::seed_from_u64(37);
        let f = UnivariatePolynomial::<Koala>::new(&[Koala::zero(), Koala::one(), Koala::one()]);
        let (root, stats) = graeffe_root_with_stats(&f, &mut rng).expect("no transform needed");
        assert_eq!(root, Some(Koala::zero()));
        assert_eq!(stats.graeffe_steps, 0);
    }

    /// A nonzero constant has no root.
    #[test]
    fn test_a_nonzero_constant_has_no_root() {
        let mut rng = StdRng::seed_from_u64(41);
        let f = UnivariatePolynomial::<Koala>::new(&[Koala::new(5)]);
        assert_eq!(graeffe_root(&f, &mut rng), Ok(None));
    }

    /// The zero polynomial has no meaningful root set.
    #[test]
    #[should_panic(expected = "every element is a root of the zero polynomial")]
    fn test_the_zero_polynomial_panics() {
        let mut rng = StdRng::seed_from_u64(43);
        let _ = graeffe_root(&UnivariatePolynomial::<Koala>::zero(), &mut rng);
    }

    /// A field whose two-adicity cannot host the domain fails as a typed value, not a wrong root.
    ///
    /// Mersenne-31 is where this bites: `2^31 - 1` is prime so `q - 1 = 2 * (2^30 - 1)` and the
    /// largest power-of-two domain has two points, which carries degree one and nothing above it.
    #[test]
    fn test_a_field_without_the_two_adicity_refuses() {
        let mut rng = StdRng::seed_from_u64(47);
        assert_eq!(Mersenne31::two_adicity(), 1);
        assert_eq!(Zp2147483647::two_adicity(), 1);

        let planted_roots = distinct_nonzero::<Mersenne31, _>(2, &mut rng);
        let f = UnivariatePolynomial::from_zeros(&planted_roots);
        assert_eq!(
            graeffe_root(&f, &mut rng),
            Err(GraeffeError::DomainTooLarge {
                degree: 2,
                log_n: 2,
                two_adicity: 1,
            })
        );
        assert!(graeffe_2(&f, &mut rng).is_err());

        // Degree one still works: one point per coefficient, and a domain of two exists.
        let linear = UnivariatePolynomial::<Mersenne31>::from_zeros(&planted_roots[..1]);
        assert_eq!(graeffe_root(&linear, &mut rng), Ok(Some(planted_roots[0])));
    }

    /// Progressive reduction cuts the transform work, and by exactly the schedule it implies.
    ///
    /// The lever is `beta_i = (q - 1) / 2^i`, so the degree stays full until `2^i` passes
    /// `(q - 1) / d` and halves thereafter. At `d = 4096` over KoalaBear, `(q - 1) / d = 520 192`,
    /// so 19 steps run at 8 192 points and the last five at 4 096, 2 048, 1 024, 512 and 256 —
    /// `3 * 163 584 = 490 752` elements against `3 * 24 * 8 192 = 589 824` with no reduction.
    ///
    /// The exact figure is asserted because the inequality alone is weak: **the saving is a factor
    /// of 1.2 here, not an order**, since `ceil(log2((q - 1) / d)) = 19` of the 24 steps are at
    /// full size. §3.6's "a small constant times the largest one" is that constant, and it is
    /// `ceil(log2((q - 1) / d)) + 2` rather than something near one.
    #[test]
    fn test_progressive_reduction_bounds_the_total_transform_work() {
        let mut rng = StdRng::seed_from_u64(53);
        let degree = 4096;
        let planted_roots = distinct_nonzero::<Koala, _>(2, &mut rng);
        let f = with_planted_roots::<Koala, _>(degree, &planted_roots, &mut rng);
        let (_root, stats) = graeffe_root_with_stats(&f, &mut rng).expect("a domain exists");

        assert_eq!(stats.graeffe_steps, 24);
        assert_eq!(stats.transforms, 72);
        assert_eq!(stats.max_transform_size, 8192);
        assert_eq!(stats.subgroup_order, 127);
        assert_eq!(
            stats.subgroup_route,
            SubgroupRoute::Enumerated { points: 127 }
        );
        assert!(
            stats.final_degree <= 126,
            "the reduction left degree {} above the subgroup order",
            stats.final_degree
        );
        assert_eq!(stats.total_transform_elements, 490_752);
        assert!(
            stats.total_transform_elements
                < 3 * stats.graeffe_steps as usize * stats.max_transform_size,
            "the reduction saved nothing: {} elements against {} with no reduction",
            stats.total_transform_elements,
            3 * stats.graeffe_steps as usize * stats.max_transform_size
        );
    }

    /// Over Goldilocks the reduction never bites, which is why [PC] wrote a second algorithm.
    ///
    /// The odd part of `q - 1` is `2^32 - 1`, above any degree of interest, so every one of the 32
    /// steps runs at the input degree and the subgroup search falls back to the gcd route.
    #[test]
    fn test_the_reduction_does_not_bite_over_goldilocks() {
        let mut rng = StdRng::seed_from_u64(59);
        let degree = 256;
        let f = with_planted_roots::<Goldilocks, _>(degree, &[Goldilocks::one()], &mut rng);
        let (_root, stats) = graeffe_root_with_stats(&f, &mut rng).expect("a domain exists");

        assert_eq!(stats.graeffe_steps, 32);
        assert_eq!(stats.subgroup_order, 4_294_967_295);
        assert_eq!(stats.final_degree as usize, degree);
        assert_eq!(
            stats.subgroup_route,
            SubgroupRoute::GcdRootFinder { degree: 256 }
        );
        assert_eq!(
            stats.total_transform_elements,
            3 * 32 * stats.max_transform_size
        );
    }
}
