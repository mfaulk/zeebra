//! Modular exponentiation of univariate polynomials.
//!
//! `Polynomial::pow` raises a polynomial to a power outright, so its result has degree
//! `n * deg(base)`. That is unusable for the exponents that matter in polynomial factorization:
//! finding the roots of `f` in GF(q) starts from `gcd(f, x^q - x)`, and `x^q` alone would have
//! q coefficients — around 2^61 of them for a 61-bit prime field.
//!
//! Reducing modulo `f` after every squaring keeps the degree below `deg(f)` throughout, so the
//! cost depends on `log(exponent)` rather than on the exponent itself.

use crate::{
    integers::{bit, highest_set_bit},
    poly::univariate::{
        div_with_remainder::{inversion_products, newton_is_cheaper},
        Polynomial, PreparedDivisor, UnivariatePolynomial,
    },
    FiniteField,
};

/// `base^exponent mod modulus`, by square-and-multiply.
///
/// # Panics
/// Panics if `modulus` is the zero polynomial.
pub fn pow_mod<F: FiniteField>(
    base: &UnivariatePolynomial<F>,
    exponent: u128,
    modulus: &UnivariatePolynomial<F>,
) -> UnivariatePolynomial<F> {
    pow_mod_limbs(base, &[exponent as u64, (exponent >> 64) as u64], modulus)
}

/// `base^exponent mod modulus`, with the exponent as little-endian 64-bit limbs.
///
/// The exponents root finding and factorization need are q, `q - 1` and `(q - 1) / 2`, none of
/// which fits in a machine integer for a 254-bit field. Limbs carry all of them, and the cost is
/// unchanged: one squaring per bit of the exponent, so `O(log q)` polynomial multiplications
/// rather than anything proportional to q itself.
///
/// Trailing zero limbs cost nothing — the loop stops at the highest set bit — so a caller may
/// pass a fixed-width order without padding the work.
///
/// # Panics
/// Panics if `modulus` is the zero polynomial.
pub fn pow_mod_limbs<F: FiniteField>(
    base: &UnivariatePolynomial<F>,
    exponent: &[u64],
    modulus: &UnivariatePolynomial<F>,
) -> UnivariatePolynomial<F> {
    pow_mod_limbs_with_route(base, exponent, modulus, PowModRoute::Classical).0
}

/// How [`pow_mod_limbs_with_route`] reduces each product modulo the fixed modulus (#1205).
///
/// A measurement and differential-testing hook, not API. `Classical` is what [`pow_mod_limbs`]
/// ships; `Auto` is the candidate, which stays off the default until the bench host clears the
/// #1205 gate.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PowModRoute {
    /// `p % modulus` per step. On the Newton route that re-inverts `rev(modulus)` every step.
    Classical,
    /// Invert `rev(modulus)` once, then reduce every step by two truncated products
    /// (`powmod_preinv`), at every degree.
    Prepared,
    /// `Prepared` exactly when `%` would take Newton for a full-width product, else `Classical`.
    /// Below the division crossover it is the classical loop step for step.
    Auto,
}

/// What one modular exponentiation spent, counted at the polynomial level.
///
/// Every product is Karatsuba (`Mul` and the division routes call no transform), so a transform
/// count would be identically zero and is not kept.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct PowModStats {
    /// Squarings of the running power.
    pub squarings: usize,
    /// Products of the result by the running power, one per set bit.
    pub multiplications: usize,
    /// Reductions by long division.
    pub long_reductions: usize,
    /// Reductions by Newton division, each inverting `rev(modulus)` afresh.
    pub newton_reductions: usize,
    /// Reductions against the cached inverse.
    pub prepared_reductions: usize,
    /// Newton inversions of `rev(modulus)`, wherever they happened.
    pub inversions: usize,
    /// Every polynomial product, the truncated ones inside reductions and inversions included.
    pub products: usize,
}

/// [`pow_mod_limbs`] on the stated route, with what it spent.
///
/// # Panics
/// Panics if `modulus` is the zero polynomial.
pub fn pow_mod_limbs_with_route<F: FiniteField>(
    base: &UnivariatePolynomial<F>,
    exponent: &[u64],
    modulus: &UnivariatePolynomial<F>,
    route: PowModRoute,
) -> (UnivariatePolynomial<F>, PowModStats) {
    assert!(
        !modulus.is_zero(),
        "the modulus must be a nonzero polynomial"
    );
    let mut stats = PowModStats::default();

    // Reducing the identity is not redundant: modulo a nonzero constant, F[x]/(c) is the zero
    // ring, where 1 and 0 coincide. Starting from an unreduced `one` would wrongly report 1.
    let mut result = reduce_classical(&UnivariatePolynomial::one(), modulus, &mut stats);

    let Some(highest) = highest_set_bit(exponent) else {
        // A zero exponent leaves the identity, reduced.
        return (result, stats);
    };

    // The base is the one dividend of unbounded degree, so it is reduced classically and the
    // prepared precision only has to cover products of two reduced operands.
    let mut square = reduce_classical(base, modulus, &mut stats);
    let reducer = Reducer::new(modulus, route, &mut stats);
    for index in 0..=highest {
        if bit(exponent, index) {
            stats.multiplications += 1;
            stats.products += 1;
            result = reducer.reduce(&(&result * &square), &mut stats);
        }
        // The last squaring would be discarded, and for a wide exponent it is not cheap.
        if index < highest {
            stats.squarings += 1;
            stats.products += 1;
            square = reducer.reduce(&(&square * &square), &mut stats);
        }
    }

    (result, stats)
}

/// The reduction a [`PowModRoute`] resolves to for one modulus.
enum Reducer<'a, F: FiniteField> {
    Classical(&'a UnivariatePolynomial<F>),
    Prepared(PreparedDivisor<F>),
}

impl<'a, F: FiniteField> Reducer<'a, F> {
    fn new(
        modulus: &'a UnivariatePolynomial<F>,
        route: PowModRoute,
        stats: &mut PowModStats,
    ) -> Self {
        let n = modulus.degree() as usize;
        // A product of two operands of degree below n has at most 2n - 1 coefficients, so its
        // quotient by the n + 1 coefficients of the modulus has at most n - 1.
        let quotient_len = n.saturating_sub(1);
        let prepare = match route {
            PowModRoute::Classical => false,
            PowModRoute::Prepared => true,
            PowModRoute::Auto => newton_is_cheaper::<F>(quotient_len, n + 1),
        };
        if !prepare {
            return Reducer::Classical(modulus);
        }
        let precision = quotient_len.max(1);
        stats.inversions += 1;
        stats.products += inversion_products(precision);
        Reducer::Prepared(PreparedDivisor::new(modulus, precision))
    }

    fn reduce(
        &self,
        p: &UnivariatePolynomial<F>,
        stats: &mut PowModStats,
    ) -> UnivariatePolynomial<F> {
        match self {
            Reducer::Classical(modulus) => reduce_classical(p, modulus, stats),
            Reducer::Prepared(divisor) => {
                if !p.is_zero() && p.coefficients().len() >= divisor.divisor_len() {
                    stats.prepared_reductions += 1;
                    // The truncated quotient and the low half of quotient times modulus.
                    stats.products += 2;
                }
                divisor.rem(p)
            }
        }
    }
}

/// `p % modulus`, counted by the route `div_with_remainder` takes for it.
fn reduce_classical<F: FiniteField>(
    p: &UnivariatePolynomial<F>,
    modulus: &UnivariatePolynomial<F>,
    stats: &mut PowModStats,
) -> UnivariatePolynomial<F> {
    if !p.is_zero() && p.degree() >= modulus.degree() {
        let (f, g) = (p.coefficients().len(), modulus.coefficients().len());
        let k = f - g + 1;
        if newton_is_cheaper::<F>(k, g) {
            stats.newton_reductions += 1;
            stats.inversions += 1;
            // The inversion, the truncated quotient and the full product `q * modulus`.
            stats.products += inversion_products(k) + 2;
        } else {
            stats.long_reductions += 1;
        }
    }
    p % modulus
}

#[cfg(test)]
mod tests {
    use crate::{
        fields::PrimeFieldElement64,
        identities::Zero,
        poly::univariate::{
            pow_mod::{pow_mod, pow_mod_limbs},
            Polynomial, UnivariatePolynomial,
        },
        FiniteField,
    };

    type F = PrimeFieldElement64<7>;
    type P = UnivariatePolynomial<F>;

    /// The polynomial with the given coefficients, lowest order first.
    fn poly(coefficients: &[u64]) -> P {
        UnivariatePolynomial::new(&coefficients.iter().map(|c| F::new(*c)).collect::<Vec<_>>())
    }

    /// For exponents small enough to compute both ways, `pow_mod` agrees with `pow` then reduce.
    ///
    /// `pow` is untouched existing code that never reduces, so this is an independent check on
    /// the whole square-and-multiply loop rather than a restatement of it.
    #[test]
    fn test_pow_mod_agrees_with_pow_then_reduce() {
        let moduli = [poly(&[1, 0, 1]), poly(&[6, 1, 1, 1]), poly(&[3, 2])];
        let bases = [poly(&[0, 1]), poly(&[1, 1]), poly(&[2, 0, 3]), poly(&[5])];

        for modulus in &moduli {
            for base in &bases {
                for exponent in 0..=12u32 {
                    let expected = base.pow(exponent) % modulus;
                    assert_eq!(
                        pow_mod(base, exponent as u128, modulus),
                        expected,
                        "base {} exponent {} modulus {}",
                        base,
                        exponent,
                        modulus
                    );
                }
            }
        }
    }

    /// The result always has degree below the modulus, which is what bounds the cost.
    #[test]
    fn test_pow_mod_stays_reduced() {
        let modulus = poly(&[1, 0, 1]); // x^2 + 1
        for exponent in [0u128, 1, 2, 3, 47, 48, 49, 1_000_000] {
            let result = pow_mod(&poly(&[0, 1]), exponent, &modulus);
            assert!(
                result.is_zero() || result.degree() < modulus.degree(),
                "exponent {} left degree {}",
                exponent,
                result.degree()
            );
        }
    }

    /// Exponents are additive: `b^(i+j) = b^i * b^j`.
    #[test]
    fn test_pow_mod_is_multiplicative_in_the_exponent() {
        let modulus = poly(&[6, 1, 1, 1]);
        let base = poly(&[1, 1]);
        for i in 0..8u128 {
            for j in 0..8u128 {
                let combined = pow_mod(&base, i + j, &modulus);
                let separate =
                    &(&pow_mod(&base, i, &modulus) * &pow_mod(&base, j, &modulus)) % &modulus;
                assert_eq!(combined, separate, "i = {}, j = {}", i, j);
            }
        }
    }

    /// With `f` irreducible of degree d over GF(q), the quotient F[x]/(f) is the field GF(q^d),
    /// so every element satisfies a^(q^d) = a.
    ///
    /// A theorem about the quotient ring rather than a property of this implementation, so it
    /// pins the answer independently.
    #[test]
    fn test_pow_mod_satisfies_frobenius() {
        // x^2 + 1 over GF(7): irreducible because it has no root, as asserted below.
        let modulus = poly(&[1, 0, 1]);
        for a in 0..7u64 {
            assert!(
                !modulus.eval(&F::new(a)).is_zero(),
                "{} is a root, so the modulus is not irreducible",
                a
            );
        }

        let q_to_the_d = 49u128; // |GF(7^2)|
        for c0 in 0..7u64 {
            for c1 in 0..7u64 {
                let a = poly(&[c0, c1]);
                assert_eq!(
                    pow_mod(&a, q_to_the_d, &modulus),
                    &a % &modulus,
                    "a = {}",
                    a
                );
            }
        }
    }

    /// An exponent far beyond what `pow` could represent, whose value theory still determines.
    #[test]
    fn test_pow_mod_handles_an_exponent_pow_cannot() {
        let modulus = poly(&[1, 0, 1]); // x^2 + 1 over GF(7), so the quotient is GF(49)
        let x = poly(&[0, 1]);

        // x is a unit: x * (-x) = -x^2 = 1. The multiplicative group of GF(49) has order 48, so
        // the order of x divides 48 and x^(48k) = 1. Computing x^48000000 with `pow` would mean
        // materializing a polynomial of that degree.
        assert!(pow_mod(&x, 48 * 1_000_000, &modulus).is_one());
        assert!(pow_mod(&x, 48, &modulus).is_one());

        // x^(48k + 1) = x.
        assert_eq!(pow_mod(&x, 48 * 1_000_000 + 1, &modulus), x);
    }

    /// Modulo a nonzero constant the quotient ring is trivial, so every power is zero.
    #[test]
    fn test_pow_mod_by_a_constant_is_zero() {
        let modulus = poly(&[5]);
        for exponent in [0u128, 1, 7, 1_000] {
            assert!(pow_mod(&poly(&[1, 1]), exponent, &modulus).is_zero());
        }
    }

    /// The zero polynomial is not a valid modulus.
    #[test]
    #[should_panic(expected = "modulus must be a nonzero polynomial")]
    fn test_pow_mod_by_zero_panics() {
        let _ = pow_mod(&poly(&[1, 1]), 3, &UnivariatePolynomial::zero());
    }

    /// The limb form agrees with the `u128` one, which is the contract the wrapper rests on.
    #[test]
    fn test_pow_mod_limbs_agrees_with_the_u128_exponent() {
        let modulus = poly(&[6, 1, 1, 1]);
        let base = poly(&[2, 3, 1]);
        for exponent in [0u128, 1, 2, 3, 17, 64, 255, 1 << 40, u64::MAX as u128] {
            let limbs = [exponent as u64, (exponent >> 64) as u64];
            assert_eq!(
                pow_mod(&base, exponent, &modulus),
                pow_mod_limbs(&base, &limbs, &modulus),
                "exponent {exponent}"
            );
        }
    }

    /// An exponent above 2^128, which the `u128` form cannot express at all.
    ///
    /// `base^(2^192)` is reached by squaring 192 times, so it is checkable against a loop that
    /// does exactly that without going through the limb bit-walk.
    #[test]
    fn test_pow_mod_limbs_handles_an_exponent_beyond_u128() {
        let modulus = poly(&[6, 1, 1, 1]);
        let base = poly(&[2, 3, 1]);

        // 2^192 as limbs: the fourth limb's lowest bit.
        let exponent = [0u64, 0, 0, 1];

        let mut expected = &base % &modulus;
        for _ in 0..192 {
            expected = &(&expected * &expected) % &modulus;
        }
        assert_eq!(pow_mod_limbs(&base, &exponent, &modulus), expected);
    }

    /// Trailing zero limbs do not change the result, so a fixed-width order needs no trimming.
    #[test]
    fn test_trailing_zero_limbs_are_ignored() {
        let modulus = poly(&[6, 1, 1, 1]);
        let base = poly(&[2, 3, 1]);
        let expected = pow_mod_limbs(&base, &[37], &modulus);
        for padded in [vec![37u64, 0], vec![37, 0, 0], vec![37, 0, 0, 0, 0]] {
            assert_eq!(pow_mod_limbs(&base, &padded, &modulus), expected);
        }
    }

    /// A zero exponent gives the identity, reduced — including modulo a constant.
    #[test]
    fn test_a_zero_exponent_gives_the_reduced_identity() {
        let base = poly(&[2, 3, 1]);
        assert_eq!(
            pow_mod_limbs(&base, &[0, 0, 0, 0], &poly(&[6, 1, 1, 1])),
            UnivariatePolynomial::one()
        );
        // Modulo a nonzero constant the quotient ring is trivial, so 1 and 0 coincide.
        assert!(pow_mod_limbs(&base, &[0], &poly(&[3])).is_zero());
    }

    // === #1205: the cached-inverse route ===

    use crate::{
        fields::{Bn254Fr, Gf13Pow4, Gf256, KoalaBear, Zp18446744069414584321, Zp2},
        poly::univariate::{
            div_with_remainder::newton_is_cheaper,
            pow_mod::{pow_mod_limbs_with_route, PowModRoute, PowModStats},
            roots::roots_with_frobenius_route,
        },
        KnownOrder,
    };
    use rand::{rngs::StdRng, SeedableRng};

    const ROUTES: [PowModRoute; 3] = [
        PowModRoute::Classical,
        PowModRoute::Prepared,
        PowModRoute::Auto,
    ];

    /// A random polynomial of exactly degree `degree`, with a random nonzero, non-one leading
    /// coefficient where the field allows it, so a non-monic modulus is exercised.
    fn random_of_degree<G: FiniteField>(
        degree: usize,
        rng: &mut StdRng,
    ) -> UnivariatePolynomial<G> {
        let mut c: Vec<G> = (0..degree).map(|_| G::random(rng)).collect();
        let mut lead = G::random(rng);
        while lead.is_zero() {
            lead = G::random(rng);
        }
        c.push(lead);
        UnivariatePolynomial::new(&c)
    }

    /// Every route returns the classical answer, for random moduli and bases at small degrees and
    /// exponents both short and as wide as the field's order.
    fn assert_routes_agree<G: FiniteField>(order: &[u64], seed: u64) {
        let mut rng = StdRng::seed_from_u64(seed);
        let x = UnivariatePolynomial::new(&[G::zero(), G::one()]);
        for degree in [0usize, 1, 2, 3, 5, 17, 40] {
            let modulus = random_of_degree::<G>(degree, &mut rng);
            let bases = [
                x.clone(),
                random_of_degree::<G>(degree / 2, &mut rng),
                // Longer than the modulus, so the base reduction is a real one.
                random_of_degree::<G>(2 * degree + 3, &mut rng),
            ];
            let exponents: [&[u64]; 5] = [&[0], &[1], &[2], &[0x1d3f], order];
            for base in &bases {
                for exponent in exponents {
                    let expected = pow_mod_limbs(base, exponent, &modulus);
                    for route in ROUTES {
                        let (got, _) = pow_mod_limbs_with_route(base, exponent, &modulus, route);
                        assert_eq!(
                            got, expected,
                            "{route:?}, degree {degree}, exponent {exponent:?}"
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn test_routes_agree_over_gf7() {
        assert_routes_agree::<F>(F::order_limbs(), 1);
    }

    /// Characteristic two, where `2 - g*h` in the inversion is `g*h` and a sign slip would hide.
    #[test]
    fn test_routes_agree_in_characteristic_two() {
        assert_routes_agree::<Zp2>(Zp2::order_limbs(), 2);
        assert_routes_agree::<Gf256>(Gf256::order_limbs(), 3);
    }

    /// An odd-characteristic extension field: x^(13^4) mod f.
    #[test]
    fn test_routes_agree_over_an_extension_field() {
        assert_routes_agree::<Gf13Pow4>(&[13u64.pow(4)], 4);
    }

    #[test]
    fn test_routes_agree_over_wide_primes() {
        assert_routes_agree::<KoalaBear>(KoalaBear::order_limbs(), 5);
        assert_routes_agree::<Zp18446744069414584321>(Zp18446744069414584321::order_limbs(), 6);
        assert_routes_agree::<Bn254Fr>(Bn254Fr::order_limbs(), 7);
    }

    /// The smallest modulus degree at which `Auto` takes the cached inverse.
    fn auto_threshold<G: FiniteField>() -> usize {
        (2..)
            .find(|&n| newton_is_cheaper::<G>(n - 1, n + 1))
            .expect("Newton wins somewhere")
    }

    /// Below the division crossover `Auto` is the classical loop exactly — the same products, the
    /// same reductions on the same routes — which is the small-degree parity the dispatch owes.
    #[test]
    fn test_auto_is_classical_below_the_crossover() {
        fn check<G: FiniteField>(order: &[u64], seed: u64) {
            let mut rng = StdRng::seed_from_u64(seed);
            let x = UnivariatePolynomial::new(&[G::zero(), G::one()]);
            let below = auto_threshold::<G>() - 1;
            for degree in [1, 8, below / 2, below] {
                let modulus = random_of_degree::<G>(degree, &mut rng);
                let (classical, classical_stats) =
                    pow_mod_limbs_with_route(&x, order, &modulus, PowModRoute::Classical);
                let (auto, auto_stats) =
                    pow_mod_limbs_with_route(&x, order, &modulus, PowModRoute::Auto);
                assert_eq!(auto, classical, "degree {degree}");
                assert_eq!(auto_stats, classical_stats, "degree {degree}");
                assert_eq!(auto_stats.prepared_reductions, 0, "degree {degree}");
            }
        }
        check::<Zp18446744069414584321>(Zp18446744069414584321::order_limbs(), 8);
        check::<Bn254Fr>(&[0xdead_beef_1234_5678], 9);
    }

    /// Above the crossover `Auto` inverts once where the classical loop inverts every step, and
    /// so spends strictly fewer products for the same answer.
    #[test]
    fn test_auto_inverts_once_above_the_crossover() {
        fn check<G: FiniteField>(order: &[u64], seed: u64) -> (PowModStats, PowModStats) {
            let mut rng = StdRng::seed_from_u64(seed);
            let x = UnivariatePolynomial::new(&[G::zero(), G::one()]);
            let degree = auto_threshold::<G>() + 3;
            let modulus = random_of_degree::<G>(degree, &mut rng);
            let (classical, classical_stats) =
                pow_mod_limbs_with_route(&x, order, &modulus, PowModRoute::Classical);
            let (auto, auto_stats) =
                pow_mod_limbs_with_route(&x, order, &modulus, PowModRoute::Auto);
            assert_eq!(auto, classical, "degree {degree}");

            // The same exponent walk on both.
            assert_eq!(auto_stats.squarings, classical_stats.squarings);
            assert_eq!(auto_stats.multiplications, classical_stats.multiplications);
            // One inversion, and no step re-inverts.
            assert_eq!(auto_stats.inversions, 1);
            assert_eq!(auto_stats.newton_reductions, 0);
            assert!(auto_stats.prepared_reductions > 0);
            // The classical loop pays an inversion for each of its Newton reductions.
            assert!(classical_stats.newton_reductions > 0);
            assert_eq!(
                classical_stats.inversions,
                classical_stats.newton_reductions
            );
            assert!(auto_stats.products < classical_stats.products);
            (classical_stats, auto_stats)
        }
        check::<Zp18446744069414584321>(Zp18446744069414584321::order_limbs(), 10);
        // A 254-bit order, so the walk is BN254's own length.
        let (classical, auto) = check::<Bn254Fr>(Bn254Fr::order_limbs(), 11);
        assert!(classical.squarings >= 253);
        // Each classical Newton reduction is an inversion plus two products, each prepared one is
        // two products; the inversion is the whole difference, so more than halving the total.
        assert!(
            2 * auto.products < classical.products,
            "{classical:?} {auto:?}"
        );
    }

    /// `roots` is the same set on every route.
    #[test]
    fn test_roots_agree_on_every_route() {
        fn check<G: KnownOrder>(seed: u64) {
            let mut rng = StdRng::seed_from_u64(seed);
            for degree in [1usize, 4, 30] {
                let planted: Vec<G> = (0..3).map(|_| G::random(&mut rng)).collect();
                let cofactor = random_of_degree::<G>(degree, &mut rng);
                let f = &UnivariatePolynomial::from_zeros(&planted) * &cofactor;
                let mut expected = roots_with_frobenius_route(
                    &f,
                    PowModRoute::Classical,
                    &mut StdRng::seed_from_u64(seed),
                );
                expected.sort_by_key(|a| format!("{a:?}"));
                for route in ROUTES {
                    let mut got =
                        roots_with_frobenius_route(&f, route, &mut StdRng::seed_from_u64(seed));
                    got.sort_by_key(|a| format!("{a:?}"));
                    assert_eq!(got, expected, "{route:?}, degree {degree}");
                    for a in &planted {
                        assert!(got.contains(a), "{route:?} lost planted root {a:?}");
                    }
                }
            }
        }
        check::<Zp2>(12);
        check::<Gf256>(13);
        check::<KoalaBear>(14);
        check::<Bn254Fr>(15);
    }

    /// The prepared route keeps the trivial-ring and zero-exponent conventions.
    #[test]
    fn test_prepared_route_edge_cases() {
        let base = poly(&[2, 3, 1]);
        for route in ROUTES {
            assert!(pow_mod_limbs_with_route(&base, &[5], &poly(&[3]), route)
                .0
                .is_zero());
            assert!(pow_mod_limbs_with_route(&base, &[0], &poly(&[3]), route)
                .0
                .is_zero());
            assert_eq!(
                pow_mod_limbs_with_route(&base, &[0], &poly(&[6, 1, 1, 1]), route).0,
                UnivariatePolynomial::one()
            );
        }
    }
}
