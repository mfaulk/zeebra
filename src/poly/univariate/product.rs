//! The univariate layer's product dispatcher: schoolbook, Karatsuba, then a transform (#1225).
//!
//! `&a * &b` and the Newton division's slice products come here. Below the measured crossovers,
//! and over every field no transform serves, the route is [`multiply_karatsuba`] exactly as before.
//! Above them there are two transforms, the same two `fft::multiply` has:
//!
//! - over a field whose [`FiniteField::transform_root_of_unity`] serves the domain,
//!   [`multiply_over_domain`] in the field itself;
//! - over a word-size prime field without such a root — Mersenne-31, `2^64 - 59` — the
//!   multi-modular product [`try_multiply_multimodular`] (#1226), which transforms over auxiliary
//!   NTT primes and recombines by CRT.
//!
//! Both are `fft`'s own entry points, so an improvement there reaches the operator too.
//!
//! **No `KnownOrder` and no randomness.** `Mul`'s signature carries neither, which is what kept the
//! operator off the transform until now (`docs/research/fast-univariate.md` §4.1). The in-field
//! root comes from the deterministic `FiniteField` hook #783 added for the transform tree, and the
//! multi-modular product reads its modulus off [`FiniteField::word_residue`], so the operator stays
//! bounded on `FiniteField` alone. Fields with neither — the binary fields, the extension fields —
//! keep Karatsuba at every degree.
//!
//! **Bit-identical to Karatsuba everywhere.** Every route computes the product exactly over the
//! field, so the choice changes the work and never the answer.

use crate::{
    fft::{
        fft_multiplication_crossover, multimodular_multiplication_crossover, multiply_over_domain,
        try_multiply_multimodular, FFTDomain,
    },
    poly::univariate::{karatsuba::multiply_karatsuba, Polynomial, UnivariatePolynomial},
    FiniteField,
};

#[cfg(test)]
thread_local! {
    /// How many products this thread has sent through either transform: the tests' proof that a
    /// route was taken, since its output is by design indistinguishable from Karatsuba's.
    static TRANSFORM_PRODUCTS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };

    /// How many of those went through the multi-modular product.
    static MULTIMODULAR_PRODUCTS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };

    /// Set by [`karatsuba_only`]: every product on this thread takes the old route, so a primitive
    /// can be run both ways and its outputs compared.
    static KARATSUBA_ONLY: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// `f` with both transform routes switched off on this thread.
#[cfg(test)]
pub(crate) fn karatsuba_only<T>(f: impl FnOnce() -> T) -> T {
    KARATSUBA_ONLY.with(|flag| flag.set(true));
    let result = f();
    KARATSUBA_ONLY.with(|flag| flag.set(false));
    result
}

/// Products this thread has sent through either transform so far.
#[cfg(test)]
pub(crate) fn transform_products() -> usize {
    TRANSFORM_PRODUCTS.with(std::cell::Cell::get)
}

/// Products this thread has sent through the multi-modular product so far.
#[cfg(test)]
pub(crate) fn multimodular_products() -> usize {
    MULTIMODULAR_PRODUCTS.with(std::cell::Cell::get)
}

/// Which transform a block product goes through.
enum Route<F: FiniteField> {
    InField(FFTDomain<F>),
    Multimodular,
}

/// How a product goes through a transform: the route, and the block length the longer operand is
/// cut into so that every block's product with the shorter one fits one transform size.
struct Plan<F: FiniteField> {
    route: Route<F>,
    block: usize,
}

/// `log2 3`, Karatsuba's exponent.
const KARATSUBA_EXPONENT: f64 = 1.584_962_500_721_156;

/// A transform of `size` points, blocked over the long operand: `blocks * size * log2 size`.
fn transform_cost(short_len: usize, long_len: usize, size: usize) -> f64 {
    let blocks = long_len.div_ceil(size - short_len + 1) as f64;
    blocks * size as f64 * f64::from(size.trailing_zeros())
}

/// Karatsuba's `long * short^(log2 3 - 1)`, on the scale where it equals [`transform_cost`] for two
/// `c / 2` operands on a `c`-point domain: the shape the crossover `c` was measured on.
fn karatsuba_cost(short_len: usize, long_len: usize, crossover: usize) -> f64 {
    let c = crossover as f64;
    let scale = c * c.log2() / (c / 2.0).powf(KARATSUBA_EXPONENT);
    scale * long_len as f64 * (short_len as f64).powf(KARATSUBA_EXPONENT - 1.0)
}

/// Whether a product is past crossover `c` at all: its degree, and the short operand's square's.
fn past(short_len: usize, long_len: usize, crossover: usize) -> bool {
    short_len + long_len - 2 >= crossover && 2 * short_len - 2 >= crossover
}

/// The smallest transform size holding a block of the short operand's length.
fn smallest_size(short_len: usize) -> usize {
    (2 * short_len - 1).next_power_of_two()
}

/// The power of two minimizing [`transform_cost`], from [`smallest_size`] up to the size holding
/// the whole product.
fn cheapest_size(short_len: usize, long_len: usize) -> usize {
    let whole = (short_len + long_len - 1).next_power_of_two();
    let mut size = smallest_size(short_len);
    let mut best = size;
    while size < whole {
        size *= 2;
        if transform_cost(short_len, long_len, size) < transform_cost(short_len, long_len, best) {
            best = size;
        }
    }
    best
}

/// The plan for a product of `short_len` by `long_len` coefficients, or `None` to keep it on
/// Karatsuba.
///
/// A cost comparison anchored at the route's measured crossover `c`:
/// [`fft_multiplication_crossover`] in the field, [`multimodular_multiplication_crossover`] through
/// CRT. Both were measured against Karatsuba on balanced operands of power-of-two length, so on
/// domains the product nearly fills, and [`karatsuba_cost`] is scaled to agree with
/// [`transform_cost`] there.
///
/// That is stricter than `fft::multiply`'s rule, which takes a transform at every product degree
/// from `c`. The difference is padding. A product one coefficient past a power of two pays for a
/// domain twice its length, which the measured points do not show, and over BN254 a 257 x 257
/// product inside Newton division measured 0.85x on the whole division under the plain degree rule.
///
/// The transform is blocked the way Karatsuba is: one domain sized for the whole product would pay
/// `O(n log n)` in the long length where Karatsuba pays `O(n)`. The size is [`cheapest_size`], or
/// smaller if the field's two-adicity runs out first. Only when the two-adicity cannot hold even
/// [`smallest_size`] is the multi-modular product considered, as in `fft::multiply`. Below `c`, and
/// while the short operand's own square is below it, nothing is costed, which keeps `from_zeros`'s
/// `n x 2` fold and every small product on exactly the route they had.
fn plan<F: FiniteField>(short_len: usize, long_len: usize) -> Option<Plan<F>> {
    if short_len == 0 {
        return None;
    }
    #[cfg(test)]
    if KARATSUBA_ONLY.with(std::cell::Cell::get) {
        return None;
    }
    // The multi-modular crossover is never below the in-field one, so a product short of the
    // latter is short of both.
    let in_field = fft_multiplication_crossover::<F>() as usize;
    if !past(short_len, long_len, in_field) {
        return None;
    }

    let smallest = smallest_size(short_len);
    let mut size = cheapest_size(short_len, long_len);
    let root = loop {
        if let Some(root) = F::transform_root_of_unity(size.trailing_zeros()) {
            break Some(root);
        }
        if size == smallest {
            break None;
        }
        size /= 2;
    };
    let plan = match root {
        Some(root) => {
            let karatsuba = karatsuba_cost(short_len, long_len, in_field);
            if transform_cost(short_len, long_len, size) > karatsuba {
                return None;
            }
            Plan {
                // The hook promises a root of order exactly `size`, which is all the domain checks.
                route: Route::InField(FFTDomain::from_generator(root, size)),
                block: size - short_len + 1,
            }
        }
        None => {
            let crossover = multimodular_multiplication_crossover::<F>() as usize;
            if (-F::one()).word_residue().is_none() || !past(short_len, long_len, crossover) {
                return None;
            }
            let size = cheapest_size(short_len, long_len);
            let karatsuba = karatsuba_cost(short_len, long_len, crossover);
            if transform_cost(short_len, long_len, size) > karatsuba {
                return None;
            }
            #[cfg(test)]
            MULTIMODULAR_PRODUCTS.with(|count| count.set(count.get() + 1));
            Plan {
                route: Route::Multimodular,
                block: size - short_len + 1,
            }
        }
    };
    #[cfg(test)]
    TRANSFORM_PRODUCTS.with(|count| count.set(count.get() + 1));
    Some(plan)
}

/// One block product through `route`, both operands nonzero.
fn multiply_routed<F: FiniteField>(
    a: &UnivariatePolynomial<F>,
    b: &UnivariatePolynomial<F>,
    route: &Route<F>,
) -> UnivariatePolynomial<F> {
    match route {
        Route::InField(domain) => multiply_over_domain(a, b, domain),
        // `Err` only past the auxiliary primes' transform length or coefficient bound, which no
        // block reaches; Karatsuba is the same answer if one ever does.
        Route::Multimodular => try_multiply_multimodular(a, b).unwrap_or_else(|_| {
            UnivariatePolynomial::from_coefficients(multiply_karatsuba(
                a.coefficients(),
                b.coefficients(),
            ))
        }),
    }
}

/// `short * long` block by block through `plan`, as `a.len() + b.len() - 1` coefficients.
fn multiply_blocked<F: FiniteField>(short: &[F], long: &[F], plan: &Plan<F>) -> Vec<F> {
    let mut product = vec![F::zero(); short.len() + long.len() - 1];
    let short = UnivariatePolynomial::new(short);
    if short.is_zero() {
        return product;
    }
    for (i, block) in long.chunks(plan.block).enumerate() {
        let block = UnivariatePolynomial::new(block);
        if block.is_zero() {
            continue;
        }
        let piece = multiply_routed(&short, &block, &plan.route);
        for (slot, c) in product[i * plan.block..]
            .iter_mut()
            .zip(piece.coefficients())
        {
            *slot += *c;
        }
    }
    product
}

/// The shorter operand first.
fn by_length<'a, T>(a: &'a [T], b: &'a [T]) -> (&'a [T], &'a [T]) {
    if a.len() <= b.len() {
        (a, b)
    } else {
        (b, a)
    }
}

/// The product of two polynomials, by the faster route the field allows. What `Mul` runs.
pub(crate) fn multiply_polynomials<F: FiniteField>(
    a: &UnivariatePolynomial<F>,
    b: &UnivariatePolynomial<F>,
) -> UnivariatePolynomial<F> {
    let (short, long) = by_length(a.coefficients(), b.coefficients());
    if !a.is_zero() && !b.is_zero() {
        if let Some(plan) = plan::<F>(short.len(), long.len()) {
            if long.len() <= plan.block {
                return multiply_routed(a, b, &plan.route);
            }
            return UnivariatePolynomial::from_coefficients(multiply_blocked(short, long, &plan));
        }
    }
    UnivariatePolynomial::from_coefficients(multiply_karatsuba(short, long))
}

/// [`multiply_polynomials`] on coefficient slices, under [`multiply_karatsuba`]'s contract: exactly
/// `a.len() + b.len() - 1` coefficients, high-order zeros carried rather than trimmed, and an empty
/// `Vec` for an empty operand.
pub(crate) fn multiply_coefficients<F: FiniteField>(a: &[F], b: &[F]) -> Vec<F> {
    let (short, long) = by_length(a, b);
    match plan::<F>(short.len(), long.len()) {
        Some(plan) => multiply_blocked(short, long, &plan),
        None => multiply_karatsuba(a, b),
    }
}

#[cfg(test)]
mod tests {
    use rand::{prelude::StdRng, SeedableRng};

    use super::{karatsuba_only, multimodular_products, multiply_coefficients, transform_products};
    use crate::{
        fft::{fft_multiplication_crossover, multimodular_multiplication_crossover},
        fields::{
            BabyBear, Bn254Fr, Gf13Pow4, Gf256, KoalaBear, Mersenne31, PrimeFieldElement64,
            Zp18446744069414584321 as Goldilocks, Zp18446744073709551557 as P64m59, Zp65537, Zp7,
        },
        identities::Zero,
        poly::univariate::{
            compose_mod, div_with_remainder_long_unstable, gcd, karatsuba::multiply_karatsuba,
            pow_mod::pow_mod_limbs, resultant_half_gcd_unstable, xgcd,
        },
        test_support::schoolbook_product,
        FiniteField, Polynomial, UnivariatePolynomial,
    };

    /// 12289 = 3 * 2^12 + 1: a field whose root runs out at a 4096-point domain, inside the band
    /// the 8-byte crossover opens, so both sides of the two-adicity limit are reachable.
    type Zp12289 = PrimeFieldElement64<12289>;

    /// A polynomial of exactly `degree`: the leading coefficient is redrawn until nonzero.
    fn exact<F: FiniteField>(degree: usize, rng: &mut StdRng) -> UnivariatePolynomial<F> {
        let mut c: Vec<F> = (0..=degree).map(|_| F::random(rng)).collect();
        while c[degree].is_zero() {
            c[degree] = F::random(rng);
        }
        UnivariatePolynomial::new(&c)
    }

    /// `&a * &b` against the definition, and whether it went through the transform.
    fn product_route<F: FiniteField>(da: usize, db: usize, seed: u64) -> bool {
        let mut rng = StdRng::seed_from_u64(seed);
        let (a, b) = (exact::<F>(da, &mut rng), exact::<F>(db, &mut rng));
        let before = transform_products();
        let product = &a * &b;
        let took = transform_products() > before;
        assert_eq!(product, schoolbook_product(&a, &b), "degrees {da} x {db}");
        assert_eq!(product.degree() as usize, da + db, "degrees {da} x {db}");
        assert_eq!(product, &a * &b, "the same product on a second call");
        took
    }

    /// Product shapes either side of the crossover `c`, with whether the transform should take
    /// them: never below `c`, not on a domain the product barely fills, and yes on one it does.
    fn crossover_shapes(c: usize) -> Vec<(usize, usize, bool)> {
        let half = c / 2;
        vec![
            // Product degree c - 1: below the crossover.
            (half, half - 1, false),
            // Degree c, length c + 1: a 2c-point domain about half full.
            (half, half, false),
            // Length 2c - 1 and exactly 2c on a 2c-point domain, balanced and 3:1.
            (c - 1, c - 1, true),
            (2 * c - 1 - half, half, true),
            // One past: 4c points, or two blocks on 2c, and neither beats Karatsuba.
            (2 * c - half, half, false),
        ]
    }

    /// Over every NTT-friendly width the operator takes the transform where the cost model says,
    /// and agrees with the definition on both sides.
    #[test]
    fn test_the_operator_takes_the_transform_past_the_crossover_on_ntt_fields() {
        fn check<F: FiniteField>(label: &str, seed: u64) {
            let crossover = fft_multiplication_crossover::<F>() as usize;
            for (i, (da, db, expected)) in crossover_shapes(crossover).into_iter().enumerate() {
                let took = product_route::<F>(da, db, seed + i as u64);
                assert_eq!(took, expected, "{label}: route at degrees {da} x {db}");
                let took = product_route::<F>(db, da, seed + 100 + i as u64);
                assert_eq!(took, expected, "{label}: route at degrees {db} x {da}");
            }
        }
        check::<Goldilocks>("Goldilocks", 1);
        check::<Zp65537>("Zp65537", 2);
        check::<Bn254Fr>("BN254 Fr", 3);
        check::<KoalaBear>("KoalaBear", 4);
        check::<BabyBear>("BabyBear", 5);
    }

    /// A short operand keeps Karatsuba however long the other is, until its product with itself
    /// reaches the crossover; past that the long operand is cut into blocks, which agree with the
    /// definition at every ratio.
    #[test]
    fn test_an_unbalanced_product_keeps_karatsuba_until_the_short_operand_is_long() {
        let half = fft_multiplication_crossover::<Goldilocks>() as usize / 2;
        for short in [0, 1, 2, half - 1] {
            assert!(!product_route::<Goldilocks>(4000, short, 10 + short as u64));
            assert!(!product_route::<Goldilocks>(short, 4000, 20 + short as u64));
        }
        for (long, seed) in [(700, 31), (4000, 32), (40_000, 33)] {
            assert!(product_route::<Goldilocks>(long, half, seed));
            assert!(product_route::<Goldilocks>(half, long, seed + 100));
        }
        let half = fft_multiplication_crossover::<KoalaBear>() as usize / 2;
        assert!(product_route::<KoalaBear>(20 * half + 17, half, 40));
    }

    /// The block domain stays inside the two-adicity when the whole product's would not.
    #[test]
    fn test_blocks_fit_a_field_whose_root_cannot_hold_the_whole_product() {
        // The whole product needs 16384 points; 12289 holds 4096, enough for 1000-long blocks.
        assert!(product_route::<Zp12289>(9999, 999, 83));
        assert!(product_route::<Zp12289>(999, 9999, 84));
    }

    /// Fields without a usable root keep Karatsuba around the in-field crossover, which is below
    /// the multi-modular one (Mersenne-31, `Zp7`), and at every degree when they have no word
    /// residue either: characteristic two, and an extension field.
    #[test]
    fn test_fields_without_a_usable_root_keep_karatsuba_above_the_crossover() {
        fn check<F: FiniteField>(label: &str, seed: u64) {
            let crossover = fft_multiplication_crossover::<F>() as usize;
            for (i, (da, db, _)) in crossover_shapes(crossover).into_iter().enumerate() {
                let took = product_route::<F>(da, db, seed + i as u64);
                assert!(!took, "{label}: transform at degrees {da} x {db}");
            }
        }
        check::<Mersenne31>("Mersenne-31", 40);
        check::<Zp7>("Zp7", 50);
        check::<Gf256>("GF(2^8)", 60);
        check::<Gf13Pow4>("GF(13^4)", 70);
        // Past the multi-modular crossover too: no word residue, so no CRT route.
        let crossover = multimodular_multiplication_crossover::<Gf256>() as usize;
        assert!(!product_route::<Gf256>(crossover - 1, crossover - 1, 71));
    }

    /// A word-size prime with two-adicity 2 takes the multi-modular product (#1226) where the cost
    /// model says, anchored at its own crossover, and agrees with the definition on both sides.
    #[test]
    fn test_a_low_two_adicity_word_prime_takes_the_multimodular_product() {
        let crossover = multimodular_multiplication_crossover::<P64m59>() as usize;
        for (i, (da, db, expected)) in crossover_shapes(crossover).into_iter().enumerate() {
            let before = multimodular_products();
            let took = product_route::<P64m59>(da, db, 200 + i as u64);
            assert_eq!(took, expected, "2^64 - 59: route at degrees {da} x {db}");
            assert_eq!(
                multimodular_products() > before,
                expected,
                "2^64 - 59: CRT at {da} x {db}"
            );
        }
        // Blocked: a 3000-long operand against a 20 000-long one.
        assert!(product_route::<P64m59>(20_000, 2999, 210));
    }

    /// Mersenne-31 reaches the multi-modular product only at its own, much later, 4-byte crossover.
    /// Checked against Karatsuba, since the definition is too slow at this size.
    #[test]
    fn test_mersenne_31_takes_the_multimodular_product_past_its_crossover() {
        type F = Mersenne31;
        let c = multimodular_multiplication_crossover::<F>() as usize;
        let mut rng = StdRng::seed_from_u64(220);
        let (a, b) = (exact::<F>(c - 1, &mut rng), exact::<F>(c - 1, &mut rng));
        let before = multimodular_products();
        let product = &a * &b;
        assert!(
            multimodular_products() > before,
            "Mersenne-31 did not take CRT"
        );
        let expected = multiply_karatsuba(a.coefficients(), b.coefficients());
        assert_eq!(product, UnivariatePolynomial::new(&expected));
    }

    /// Past the field's two-adicity the operator falls back to Karatsuba rather than failing, and
    /// up to it the transform is taken.
    #[test]
    fn test_a_product_past_the_two_adicity_falls_back_to_karatsuba() {
        // Product length 4096 is the largest domain 12289 holds; 4097 needs 8192 points.
        assert!(product_route::<Zp12289>(2048, 2047, 80));
        assert!(!product_route::<Zp12289>(2048, 2048, 81));
        assert!(!product_route::<Zp12289>(3000, 3000, 82));
    }

    /// The slice form keeps `multiply_karatsuba`'s contract on the transform route: exact length,
    /// high-order zeros carried, an all-zero operand a run of zeros, an empty one an empty product.
    #[test]
    fn test_the_slice_form_keeps_the_karatsuba_contract_on_the_transform_route() {
        type F = Goldilocks;
        let mut rng = StdRng::seed_from_u64(90);
        let mut a: Vec<F> = (0..900).map(|_| F::random(&mut rng)).collect();
        let mut b: Vec<F> = (0..800).map(|_| F::random(&mut rng)).collect();
        a.extend(std::iter::repeat_n(F::zero(), 30));
        b.extend(std::iter::repeat_n(F::zero(), 5));

        let before = transform_products();
        let product = multiply_coefficients(&a, &b);
        assert!(transform_products() > before, "the transform was not taken");
        assert_eq!(product.len(), a.len() + b.len() - 1);
        assert_eq!(product, multiply_karatsuba(&a, &b));

        let zeros = vec![F::zero(); 800];
        assert_eq!(
            multiply_coefficients(&a, &zeros),
            vec![F::zero(); a.len() + 799]
        );
        assert!(multiply_coefficients(&a, &[]).is_empty());
        assert!(multiply_coefficients::<F>(&[], &b).is_empty());
    }

    /// Run `f` on both routes, assert that the transform was reached on the first and that the
    /// two agree.
    fn both_routes<T: PartialEq + std::fmt::Debug>(label: &str, f: impl Fn() -> T) {
        let before = transform_products();
        let fast = f();
        assert!(
            transform_products() > before,
            "{label}: never reached the transform"
        );
        let before = transform_products();
        let old = karatsuba_only(&f);
        assert_eq!(
            transform_products(),
            before,
            "{label}: the control took the transform"
        );
        assert_eq!(fast, old, "{label}: the routes disagree");
    }

    /// Every primitive the issue names is built on these products, and returns the same answer
    /// with them routed as with Karatsuba alone.
    #[test]
    fn test_the_primitives_built_on_the_product_agree_with_the_karatsuba_route() {
        type F = Goldilocks;
        let mut rng = StdRng::seed_from_u64(100);

        // Newton division, checked against long division too, which shares no product.
        let f = exact::<F>(3000, &mut rng);
        let g = exact::<F>(1400, &mut rng);
        both_routes("divrem", || &f % &g);
        both_routes("quotient", || &f / &g);
        assert_eq!((&f / &g, &f % &g), div_with_remainder_long_unstable(&f, &g));

        let h = exact::<F>(1000, &mut rng);
        let base = exact::<F>(999, &mut rng);
        both_routes("pow_mod", || {
            pow_mod_limbs(&base, &[0x1234_5678_9abc_def1, 3], &h)
        });
        let inner = exact::<F>(999, &mut rng);
        let outer = exact::<F>(700, &mut rng);
        both_routes("compose_mod", || compose_mod(&outer, &inner, &h));

        let common = exact::<F>(1000, &mut rng);
        let a = &common * &exact::<F>(2200, &mut rng);
        let b = &common * &exact::<F>(2150, &mut rng);
        both_routes("gcd", || gcd(&a, &b));
        both_routes("xgcd", || xgcd(&a, &b));
        // `resultant` itself is classical Euclid, whose quotients are too short to reach the
        // transform; the half-GCD resultant is the one built on large products.
        let (r, t) = (exact::<F>(2000, &mut rng), exact::<F>(1900, &mut rng));
        both_routes("resultant", || resultant_half_gcd_unstable(&r, &t));

        let points: Vec<F> = (0..1500).map(|_| F::random(&mut rng)).collect();
        // The subproduct tree's node products. `multipoint_evaluate` and `lagrange_interpolate`
        // are not here: over these fields they already take #783's transform tree, not `Mul`.
        both_routes("from_zeros", || UnivariatePolynomial::from_zeros(&points));

        // A word prime without the two-adicity: the same primitives through the CRT product.
        type P = P64m59;
        let f = exact::<P>(12_000, &mut rng);
        let g = exact::<P>(6_000, &mut rng);
        let before = multimodular_products();
        both_routes("divrem over 2^64 - 59", || (&f / &g, &f % &g));
        assert!(multimodular_products() > before, "divrem did not take CRT");
        let h = exact::<P>(4_096, &mut rng);
        let base = exact::<P>(4_095, &mut rng);
        both_routes("pow_mod over 2^64 - 59", || {
            pow_mod_limbs(&base, &[0xffff], &h)
        });
    }
}
