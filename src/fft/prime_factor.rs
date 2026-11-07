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
//! convolution rather than a re-indexing, but is not dispatched to from here: it needs a
//! power-of-two root of unity for the convolution length, which `KnownOrder` can supply and the
//! `FiniteField` bound on this function cannot, and the crossover against `dft` is unmeasured
//! (#357).

use crate::{fft::transform::transform_in_place, integers::mod_inverse_u128, FiniteField};

/// Transform `values` in place over `domain`, which must be `1, w, ..., w^{n-1}` for a primitive
/// `n`th root of unity `w`, for any `n`.
///
/// The radix-2 kernel where it applies, Good–Thomas where the size splits into coprime factors,
/// and the quadratic definition for an odd prime power.
pub(crate) fn transform_any<F: FiniteField>(values: &mut [F], domain: &[F]) {
    let n = values.len();
    assert_eq!(
        n,
        domain.len(),
        "values and domain must have the same length"
    );

    if n.is_power_of_two() {
        transform_in_place(values, domain);
    } else if let Some((n1, n2)) = coprime_split(n) {
        good_thomas(values, domain, n1, n2);
    } else {
        dft(values, domain);
    }
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
fn good_thomas<F: FiniteField>(values: &mut [F], domain: &[F], n1: usize, n2: usize) {
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
        transform_any(row, &domain_n2);
    }

    let mut column = vec![F::zero(); n1];
    for i2 in 0..n2 {
        for (i1, slot) in column.iter_mut().enumerate() {
            *slot = rows[i1 * n2 + i2];
        }
        transform_any(&mut column, &domain_n1);
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

#[cfg(test)]
mod tests {
    use super::{coprime_split, distinct_prime_factors, transform_any};
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
            transform_any(&mut values, domain.powers());
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
        transform_any(&mut values, domain.powers());
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
            transform_any(&mut values, domain.powers());
            assert_eq!(values, vec![F::new(7); n], "size {n}");
        }
    }
}
