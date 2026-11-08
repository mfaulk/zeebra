//! Transforms of a size that is not a power of two, by the prime-factor (Good–Thomas) algorithm.
//!
//! For `n = n1 * n2` with `gcd(n1, n2) = 1`, re-indexing the input by the Chinese remainder
//! isomorphism `Z/n = Z/n1 x Z/n2` turns the length-`n` DFT into a 2-D transform of `n1`-point and
//! `n2`-point DFTs **with no twiddle factors between the stages** — the whole cost of the
//! decomposition is two permutations. Writing `i = i1 (mod n1)`, `i = i2 (mod n2)` and
//! `k = k1*n2 + k2*n1 (mod n)`:
//!
//! ```text
//! w^(i k) = w^(n2 i k1) * w^(n1 i k2) = w_n1^(i1 k1) * w_n2^(i2 k2),
//! ```
//!
//! because `w_n1 = w^n2` has order `n1`, so its exponent only matters modulo `n1`. That identity is
//! the algorithm: scatter by the CRT map, transform along each axis with the sub-root, gather by
//! the `k1*n2 + k2*n1` map.
//!
//! Which sub-transform runs is decided per factor: a power-of-two factor goes to the radix-2
//! kernel, a composite factor recurses, and an odd prime power — 9, 25, 27 — has no coprime split
//! and falls back to the `O(m^2)` definition. So a size like `2520 = 2^3 * 3^2 * 5 * 7` costs
//! `n log 8` for the 2-adic part plus `n * (9 + 5 + 7)` for the rest, while a large *prime* size is
//! quadratic through this route. [`bluestein`](super::bluestein) removes that case with a
//! convolution rather than a re-indexing, **and since #375 it is dispatched to from here** —
//! above a measured crossover, and only when the caller's domain carries a prepared convolution
//! domain.
//!
//! That proviso is the whole of the bound problem, and it is solved by moving rather than by
//! widening. Building a convolution domain needs a primitive power-of-two root, hence
//! [`KnownOrder`](crate::KnownOrder) and an rng; the transform itself needs neither. Tightening
//! this function's bound would have propagated through `evaluate` and `interpolate` into the
//! polynomial API and ruled the FFT out over every field that is not `KnownOrder`. Instead the
//! convolution domain is attached to the **domain** by
//! [`with_bluestein`](super::with_bluestein), which carries the bound alone, and threaded down
//! this decomposition as an `Option`. `None` is an ordinary state: it means every prime-power
//! factor takes `dft`, exactly as before #375.
//!
//! Threading rather than reading it off an `FFTDomain` at each node is forced by the recursion.
//! [`good_thomas`] builds its sub-domains as strided `Vec<F>` copies, so there is no `FFTDomain`
//! at a recursive site to carry anything — and a nested odd prime power is reached through
//! exactly that path. One prepared domain serves every factor because
//! [`bluestein_convolution_length`](super::bluestein_convolution_length)'s contract admits a
//! larger `L` than a given factor needs.

use crate::{
    fft::{
        bluestein::{bluestein_convolution_length, bluestein_transform},
        domain::FFTDomain,
        transform::transform_in_place,
    },
    integers::mod_inverse_u128,
    FiniteField,
};

/// Prime-power factor size above which Bluestein beats the quadratic definition.
///
/// Measured by `examples/bluestein_crossover.rs`, not derived. `dft` is `O(m^2)` but
/// allocation-free and branch-free — one accumulator and an incremented twiddle index. Bluestein
/// pays three `m`-length chirp passes, two `L`-length forward transforms, an `L`-length pointwise
/// product, an `L`-length inverse transform and a `batch_inverse` of the convolution domain, at
/// `L` up to `4m`, and it rebuilds the chirp tables on every call. So the quadratic route wins
/// below some size and this is where.
///
/// # One constant, not a tier per element width
///
/// `karatsuba_base_case`, #193's `newton_crossover` and #162's `tree_crossover` all carry three
/// tiers because three were *measured*. Here they cannot be, and the reason is a property of the
/// fields rather than of the sweep: a domain of size `m` needs `m | q - 1`, the dispatch is reached
/// only at an odd prime power, and Bluestein needs the two-adicity to cover `log2 L`. What survives
/// all three conditions is
///
/// ```text
///   Goldilocks  (8 bytes)   3, 5, 17, 257
///   KoalaBear   (4 bytes)   127
///   BabyBear    (8 bytes)   3, 5
///   BN254 Fr   (32 bytes)   nothing at all
/// ```
///
/// One field per width, and none at the widest. Splitting that into three constants would be two
/// unmeasured numbers presented as measured ones, so there is one.
///
/// # What the measurement pins
///
/// `dft` wins at `m = 17` over Goldilocks (0.25x) and loses at `m = 257` (3.06x), so that field
/// brackets the crossover to `[17, 257)` — no hostable size lies between. KoalaBear's only size,
/// 127, favours Bluestein by **3.55x**, which caps the constant below 127. BabyBear's 3 and 5 both
/// favour `dft`, which floors it at 5. Intersecting: any constant in **`[17, 127)`** dispatches
/// identically to the measurement on every field that can exercise it, and 64 is the middle of
/// that range.
pub(crate) const BLUESTEIN_CROSSOVER: usize = 64;

/// The measured crossover, the single source of truth for the dispatch.
///
/// Takes `F` so that a future per-width measurement can be dropped in without changing a call
/// site, and so the measurement binary reads the same figure the dispatch does. It does not use
/// `F` today, and the doc on [`BLUESTEIN_CROSSOVER`] says why that is the honest shape.
pub(crate) fn bluestein_crossover<F: FiniteField>() -> usize {
    let _ = std::mem::size_of::<F>();
    BLUESTEIN_CROSSOVER
}

/// Transform `values` in place over `domain`, which must be `1, w, ..., w^{n-1}` for a primitive
/// `n`th root of unity `w`, for any `n`.
///
/// The radix-2 kernel where it applies, Good–Thomas where the size splits into coprime factors,
/// and the quadratic definition for an odd prime power.
/// `convolution` is the domain Bluestein needs, when the caller has one; `None` keeps the
/// pre-#375 behaviour exactly, with every prime-power factor taking `dft`. It is a parameter
/// rather than something read off an [`FFTDomain`] per node because [`good_thomas`] recurses with
/// strided `Vec<F>` sub-domains, so there is no domain object at a recursive site.
pub(crate) fn transform_any<F: FiniteField>(
    values: &mut [F],
    domain: &[F],
    convolution: Option<&FFTDomain<F>>,
) {
    let n = values.len();
    assert_eq!(
        n,
        domain.len(),
        "values and domain must have the same length"
    );

    if n.is_power_of_two() {
        transform_in_place(values, domain);
    } else if let Some((n1, n2)) = coprime_split(n) {
        good_thomas(values, domain, n1, n2, convolution);
    } else {
        prime_power(values, domain, convolution);
    }
}

/// An odd prime-power factor: Bluestein above the measured crossover, the definition below it.
///
/// A convolution domain too short for this factor falls back to `dft` rather than panicking, even
/// though `bluestein_transform` would panic on it. Reached through [`transform_any`] the
/// check cannot fail — the prepared `L` is sized for the whole transform's `n`, every factor `m`
/// divides `n`, and the padded length is monotone in the factor — so this is not a guard against
/// the decomposition. It is a guard against a **hand-built** domain carrying a deliberately small
/// convolution domain, where the choice is between a correct slow answer and a panic, and the
/// slow answer is the better one for a capability that is optional by design.
fn prime_power<F: FiniteField>(values: &mut [F], domain: &[F], convolution: Option<&FFTDomain<F>>) {
    let m = values.len();
    if m > bluestein_crossover::<F>() {
        if let Some(convolution) = convolution {
            if convolution.size() >= bluestein_convolution_length(m) {
                // `bluestein_transform` wants the factor's domain as an `FFTDomain`; the
                // decomposition holds it as a slice, so this is one `m`-element copy against the
                // route's own `O(m log m)`.
                let factor = FFTDomain::new(domain.to_vec());
                bluestein_transform(values, &factor, convolution);
                return;
            }
        }
    }
    dft(values, domain);
}

/// `n` as `n1 * n2` with `gcd(n1, n2) = 1` and both above one, or `None` if `n` is a prime power.
///
/// `n1` is the prime power of the smallest prime factor, which makes the split deterministic and
/// puts the 2-adic factor first for an even `n`. Any coprime split is correct — the algorithm is
/// symmetric in the two factors — so this is a choice about predictability, not about cost.
pub(crate) fn coprime_split(n: usize) -> Option<(usize, usize)> {
    if n < 2 {
        return None;
    }
    let mut smallest_prime_power = 1;
    let mut remaining = n;
    let mut p = 2;
    while p * p <= remaining {
        if remaining.is_multiple_of(p) {
            while remaining.is_multiple_of(p) {
                remaining /= p;
                smallest_prime_power *= p;
            }
            break;
        }
        p += 1;
    }
    if smallest_prime_power == 1 {
        // `n` is prime, or a prime larger than its own square root times anything: either way the
        // loop above found no factor, so `n` itself is the prime power.
        return None;
    }
    if remaining == 1 {
        return None;
    }
    Some((smallest_prime_power, remaining))
}

/// The distinct prime factors of `n`, by trial division.
///
/// Transform sizes are small enough that trial division to `sqrt(n)` is free, and the only caller
/// needs this to decide whether a root of unity has order exactly `n`.
pub(crate) fn distinct_prime_factors(n: usize) -> Vec<usize> {
    let mut factors = Vec::new();
    let mut remaining = n;
    let mut p = 2;
    while p * p <= remaining {
        if remaining.is_multiple_of(p) {
            factors.push(p);
            while remaining.is_multiple_of(p) {
                remaining /= p;
            }
        }
        p += 1;
    }
    if remaining > 1 {
        factors.push(remaining);
    }
    factors
}

/// The prime-factor algorithm for `n = n1 * n2`, `gcd(n1, n2) = 1`.
fn good_thomas<F: FiniteField>(
    values: &mut [F],
    domain: &[F],
    n1: usize,
    n2: usize,
    convolution: Option<&FFTDomain<F>>,
) {
    let n = values.len();
    debug_assert_eq!(n, n1 * n2);

    // The CRT map, as the two coefficients of `i = c1 * i1 + c2 * i2 (mod n)`.
    let c1 = n2
        * (mod_inverse_u128((n2 % n1) as u128, n1 as u128)
            .expect("n1 and n2 are coprime, so n2 is invertible mod n1") as usize);
    let c2 = n1
        * (mod_inverse_u128((n1 % n2) as u128, n2 as u128)
            .expect("n1 and n2 are coprime, so n1 is invertible mod n2") as usize);

    // Row `i1` of `rows` is `A[i1][*]`, so the n2-point transforms run on contiguous memory and
    // the n1-point transforms are the strided direction.
    let mut rows = vec![F::zero(); n];
    for i1 in 0..n1 {
        for i2 in 0..n2 {
            rows[i1 * n2 + i2] = values[(c1 * i1 + c2 * i2) % n];
        }
    }

    // The sub-roots are `w^n2` of order n1 and `w^n1` of order n2. Their power sequences are the
    // strided reads of the full table: `j * n1 < n` for `j < n2`, so no index wraps.
    let domain_n1: Vec<F> = domain.iter().step_by(n2).cloned().collect();
    let domain_n2: Vec<F> = domain.iter().step_by(n1).cloned().collect();
    debug_assert_eq!(domain_n1.len(), n1);
    debug_assert_eq!(domain_n2.len(), n2);

    for row in rows.chunks_mut(n2) {
        transform_any(row, &domain_n2, convolution);
    }

    let mut column = vec![F::zero(); n1];
    for i2 in 0..n2 {
        for (i1, slot) in column.iter_mut().enumerate() {
            *slot = rows[i1 * n2 + i2];
        }
        transform_any(&mut column, &domain_n1, convolution);
        for (i1, slot) in column.iter().enumerate() {
            rows[i1 * n2 + i2] = *slot;
        }
    }

    // X[(k1 * n2 + k2 * n1) mod n] = A[k1][k2].
    for k1 in 0..n1 {
        for k2 in 0..n2 {
            values[(k1 * n2 + k2 * n1) % n] = rows[k1 * n2 + k2];
        }
    }
}

/// The transform by its definition, `O(n^2)`: the base case for an odd prime power.
///
/// The twiddle index is accumulated rather than computed as `j * k % n`, which would overflow
/// `usize` for a large `n` and costs a division per term besides.
fn dft<F: FiniteField>(values: &mut [F], domain: &[F]) {
    let n = values.len();
    let mut out = Vec::with_capacity(n);
    for k in 0..n {
        let mut accumulator = F::zero();
        let mut index = 0;
        for value in values.iter() {
            accumulator += *value * domain[index];
            index += k;
            if index >= n {
                index -= n;
            }
        }
        out.push(accumulator);
    }
    values.copy_from_slice(&out);
}

/// The quadratic definition, reachable from an example binary so the crossover can be swept.
///
/// `bluestein_transform` is already public, so this is the only half of the A/B that needs a hook.
#[doc(hidden)]
pub fn dft_unstable<F: FiniteField>(values: &mut [F], domain: &[F]) {
    dft(values, domain);
}

/// [`bluestein_crossover`], reachable from an example binary.
#[doc(hidden)]
pub fn bluestein_crossover_unstable<F: FiniteField>() -> usize {
    bluestein_crossover::<F>()
}

#[cfg(test)]
mod tests {
    use super::{bluestein_crossover, coprime_split, distinct_prime_factors, transform_any};
    use crate::{
        fields::PrimeFieldElement64, identities::Zero, FFTDomain, FiniteField, KnownOrder,
    };
    use rand::{prelude::StdRng, Rng, SeedableRng};

    /// The transform by its definition, sharing no code with any kernel.
    fn reference_dft<F: FiniteField>(coefficients: &[F], domain: &[F]) -> Vec<F> {
        let n = domain.len();
        (0..n)
            .map(|k| {
                let mut accumulator = F::zero();
                for (j, c) in coefficients.iter().enumerate() {
                    accumulator += *c * domain[(j * k) % n];
                }
                accumulator
            })
            .collect()
    }

    /// `n` splits into the prime power of its smallest prime and the coprime remainder.
    #[test]
    fn test_coprime_split() {
        assert_eq!(coprime_split(12), Some((4, 3)));
        assert_eq!(coprime_split(6), Some((2, 3)));
        assert_eq!(coprime_split(2520), Some((8, 315)));
        assert_eq!(coprime_split(45), Some((9, 5)));
    }

    /// A prime power has no coprime split, which is what selects the quadratic base case.
    #[test]
    fn test_prime_powers_do_not_split() {
        for n in [0, 1, 2, 3, 4, 7, 8, 9, 25, 27, 1024, 65521] {
            assert_eq!(coprime_split(n), None, "coprime_split({n})");
        }
    }

    /// The distinct primes dividing n, with no multiplicities and none missed.
    #[test]
    fn test_distinct_prime_factors() {
        assert_eq!(distinct_prime_factors(1), Vec::<usize>::new());
        assert_eq!(distinct_prime_factors(2), vec![2]);
        assert_eq!(distinct_prime_factors(12), vec![2, 3]);
        assert_eq!(distinct_prime_factors(2520), vec![2, 3, 5, 7]);
        assert_eq!(distinct_prime_factors(65521), vec![65521]);
    }

    /// Every transform size dividing q - 1 agrees with the definition, whatever path it takes.
    #[test]
    fn test_every_size_agrees_with_the_definition() {
        // 65520 = 2^4 * 3^2 * 5 * 7 * 13, so this field offers every shape of size: powers of two,
        // odd prime powers, and products of several coprime factors.
        type F = PrimeFieldElement64<65521>;
        let mut rng = StdRng::seed_from_u64(125);
        for n in [
            1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 15, 16, 18, 20, 21, 35, 36, 45, 63, 65, 105,
            144, 315, 720, 2520,
        ] {
            let g = F::root_of_unity(n as u64, &mut rng);
            let domain =
                FFTDomain::try_from_generator(g, n).unwrap_or_else(|e| panic!("size {n}: {e}"));
            let coefficients: Vec<F> = (0..n).map(|_| F::new(rng.gen_range(0..65521))).collect();
            let mut values = coefficients.clone();
            transform_any(&mut values, domain.powers(), None);
            assert_eq!(
                values,
                reference_dft(&coefficients, domain.powers()),
                "transform of size {n} disagrees with the definition"
            );
        }
    }

    /// A size whose odd part is a prime power reaches the quadratic base case through the
    /// decomposition and still agrees with the definition.
    #[test]
    fn test_an_odd_prime_power_factor() {
        type F = PrimeFieldElement64<65521>;
        let mut rng = StdRng::seed_from_u64(9);
        // 144 = 16 * 9: the 9-point stage has no coprime split of its own.
        let n = 144;
        let g = F::root_of_unity(n as u64, &mut rng);
        let domain = FFTDomain::try_from_generator(g, n).expect("a primitive 144th root");
        let coefficients: Vec<F> = (0..n).map(|i| F::new((i * i + 1) as u64)).collect();
        let mut values = coefficients.clone();
        transform_any(&mut values, domain.powers(), None);
        assert_eq!(values, reference_dft(&coefficients, domain.powers()));
    }

    /// The transform of a single coefficient is itself, at every size: the constant polynomial
    /// takes the same value at every point of the domain.
    #[test]
    fn test_a_constant_transforms_to_itself() {
        type F = PrimeFieldElement64<65521>;
        let mut rng = StdRng::seed_from_u64(3);
        for n in [3, 5, 12, 15, 105] {
            let g = F::root_of_unity(n as u64, &mut rng);
            let domain = FFTDomain::try_from_generator(g, n).expect("a primitive root");
            let mut values = vec![F::zero(); n];
            values[0] = F::new(7);
            transform_any(&mut values, domain.powers(), None);
            assert_eq!(values, vec![F::new(7); n], "size {n}");
        }
    }

    /// Both routes through a prime-power factor agree, on both sides of the crossover.
    ///
    /// This is the test that makes #375's dispatch safe: the two calls below differ only in
    /// whether a convolution domain is passed, so equality says the dispatch changed the cost and
    /// says the dispatch changed the cost and not the answer. Both are also checked against the
    /// definition, so agreeing on a shared mistake cannot pass.
    ///
    /// Goldilocks because of its factorization: `q - 1 = 2^32 * 3 * 5 * 17 * 257 * 65537`, which
    /// is the richest set of odd prime-power domain sizes any field here can host, and a
    /// two-adicity of 32 for the convolution length. The first field tried, BabyBear, has
    /// `q - 1 = 2^27 * 3 * 5` and could reach only two sizes — both below the crossover, so the
    /// test would have passed without ever running Bluestein.
    #[test]
    fn test_the_bluestein_route_agrees_with_the_quadratic_definition() {
        type F = PrimeFieldElement64<18_446_744_069_414_584_321>;
        let mut rng = StdRng::seed_from_u64(0x0375_0001);
        let crossover = bluestein_crossover::<F>();

        let mut below = 0;
        let mut above = 0;
        for m in [3usize, 5, 17, 257] {
            let Ok(root) = F::try_root_of_unity(m as u64, &mut rng) else {
                continue;
            };
            let Ok(domain) = FFTDomain::try_from_generator(root, m) else {
                continue;
            };
            let Ok(prepared) = crate::fft::with_bluestein(domain.clone(), &mut rng) else {
                continue;
            };

            let values: Vec<F> = (0..m).map(|_| F::random(&mut rng)).collect();
            let expected = reference_dft(&values, domain.powers());

            let mut quadratic = values.clone();
            transform_any(&mut quadratic, domain.powers(), None);
            assert_eq!(quadratic, expected, "the definition disagrees at m = {}", m);

            let mut dispatched = values.clone();
            transform_any(
                &mut dispatched,
                prepared.powers(),
                prepared.bluestein_domain(),
            );
            assert_eq!(dispatched, expected, "the dispatch disagrees at m = {}", m);

            if m > crossover {
                above += 1;
            } else {
                below += 1;
            }
        }
        assert!(
            below > 0 && above > 0,
            "the sweep covered {} sizes below the crossover of {} and {} above, so it does not \
             span the dispatch and cannot have exercised both routes",
            below,
            crossover,
            above
        );
    }

    /// A domain with no prepared convolution domain takes the quadratic route, which is the
    /// pre-#375 behaviour and the only behaviour available over a field that cannot host one.
    #[test]
    fn test_an_unprepared_domain_is_unchanged_by_the_dispatch() {
        type F = PrimeFieldElement64<18_446_744_069_414_584_321>;
        let mut rng = StdRng::seed_from_u64(0x0375_0002);
        for m in [17usize, 257] {
            let root = F::try_root_of_unity(m as u64, &mut rng).expect("m divides q - 1");
            let domain = FFTDomain::from_generator(root, m);
            assert!(domain.bluestein_domain().is_none());
            let values: Vec<F> = (0..m).map(|_| F::random(&mut rng)).collect();
            let mut actual = values.clone();
            transform_any(&mut actual, domain.powers(), None);
            assert_eq!(actual, reference_dft(&values, domain.powers()), "m = {}", m);
        }
    }

    /// A composite size whose prime-power factor is reached through the Good-Thomas recursion
    /// still takes Bluestein, which is what threading the option down the decomposition is for.
    ///
    /// `2056 = 2^3 * 257`: the 2-adic part takes the radix-2 kernel and 257 — above the
    /// crossover — is the nested factor, reached only through `good_thomas`.
    #[test]
    fn test_a_nested_prime_power_factor_reaches_the_dispatch() {
        type F = PrimeFieldElement64<18_446_744_069_414_584_321>;
        let mut rng = StdRng::seed_from_u64(0x0375_0003);
        let n = 8 * 257;
        let root = F::try_root_of_unity(n as u64, &mut rng).expect("n divides q - 1");
        let domain = FFTDomain::from_generator(root, n);
        let prepared = crate::fft::with_bluestein(domain.clone(), &mut rng)
            .expect("this field hosts the convolution length");

        let values: Vec<F> = (0..n).map(|_| F::random(&mut rng)).collect();
        let expected = reference_dft(&values, domain.powers());

        let mut dispatched = values.clone();
        transform_any(
            &mut dispatched,
            prepared.powers(),
            prepared.bluestein_domain(),
        );
        assert_eq!(dispatched, expected);

        let mut quadratic = values.clone();
        transform_any(&mut quadratic, domain.powers(), None);
        assert_eq!(dispatched, quadratic);
    }

    /// A convolution domain too short for a factor falls back to the definition rather than
    /// panicking, which is what keeps a hand-built domain correct rather than fatal.
    #[test]
    fn test_a_convolution_domain_too_short_falls_back() {
        type F = PrimeFieldElement64<18_446_744_069_414_584_321>;
        let mut rng = StdRng::seed_from_u64(0x0375_0004);
        let m = 257;
        let root = F::try_root_of_unity(m as u64, &mut rng).expect("m divides q - 1");
        let domain = FFTDomain::from_generator(root, m);
        let small = crate::fft::bluestein_convolution_domain::<F, _>(8, &mut rng)
            .expect("a tiny convolution length is hostable");
        let prepared = domain.clone().with_bluestein_domain(small);

        let values: Vec<F> = (0..m).map(|_| F::random(&mut rng)).collect();
        let mut actual = values.clone();
        transform_any(&mut actual, prepared.powers(), prepared.bluestein_domain());
        assert_eq!(actual, reference_dft(&values, domain.powers()));
    }

    /// Preparing a domain does not change what it is equal to.
    ///
    /// The derived `PartialEq` would have made a domain stop being equal to itself after
    /// preparation, silently changing every existing assertion over domains; `FFTDomain`'s
    /// `PartialEq` is hand-written to compare points alone, and this pins that.
    #[test]
    fn test_preparing_a_domain_does_not_change_its_equality() {
        type F = PrimeFieldElement64<18_446_744_069_414_584_321>;
        let mut rng = StdRng::seed_from_u64(0x0375_0005);
        let root = F::try_root_of_unity(257, &mut rng).expect("257 divides q - 1");
        let domain = FFTDomain::from_generator(root, 257);
        let prepared = crate::fft::with_bluestein(domain.clone(), &mut rng)
            .expect("this field hosts the convolution length");
        assert_eq!(prepared, domain);
        assert_eq!(domain, prepared);
        assert!(prepared.bluestein_domain().is_some());
        assert!(domain.bluestein_domain().is_none());
    }
}
