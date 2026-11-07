//! Bluestein's algorithm: a transform of any length as a convolution at a power-of-two length.
//!
//! The prime-factor decomposition in [`prime_factor`](super::prime_factor) bottoms out at the
//! `O(m^2)` definition for a prime power, so a large prime size is quadratic. Bluestein removes
//! that case by rewriting the transform as a convolution, which the radix-2 kernel can do at a
//! padded power-of-two length.
//!
//! The usual statement of the identity is `jk = (j^2 + k^2 - (k - j)^2) / 2`, whose halved squares
//! need a `2n`-th root of unity to express. This uses the triangular numbers `T(m) = m(m-1)/2`
//! instead, which are integers outright:
//!
//! ```text
//! T(j) + T(k) - T(k - j) = jk - j,   so   jk = T(j) + j + T(k) - T(k - j),
//! ```
//!
//! and therefore
//!
//! ```text
//! X_k = w^T(k) * sum_j (x_j w^(T(j) + j)) * w^(-T(k - j)).
//! ```
//!
//! Every exponent is an integer and every factor is a power of the `n`th root the caller already
//! holds, so no `2n`-th root is ever constructed or required — see
//! [`bluestein_convolution_domain`] for why that requirement would have been redundant anyway.
//!
//! The sum is a linear convolution of an `n`-term sequence with a `(2n - 1)`-term one, taken as a
//! cyclic convolution at any power-of-two length `L >= 2n - 1` so that nothing wraps onto itself.
//! That length is the algorithm's one demand on the field: a primitive `L`-th root of unity, hence
//! two-adicity at least `log2 L`.

use rand::{CryptoRng, RngCore};

use crate::{
    fft::{domain::FFTDomain, transform::transform_in_place},
    fields::RootOfUnityError,
    FiniteField, KnownOrder,
};

/// The convolution length Bluestein needs for a transform of `size` points: the least power of
/// two at least `2 * size - 1`.
///
/// Below `2 * size - 1` the cyclic convolution would alias the two ends of the chirp onto each
/// other. Any power of two at or above it works, and this is the smallest.
pub fn bluestein_convolution_length(size: usize) -> usize {
    if size == 0 {
        return 1;
    }
    (2 * size - 1).next_power_of_two()
}

/// A domain for [`bluestein_transform`]'s convolution, for a transform of `size` points.
///
/// The one thing Bluestein asks of the field beyond the `size`-th root of unity the caller already
/// has: a primitive [`bluestein_convolution_length(size)`](bluestein_convolution_length)-th root.
/// Whether the field holds one is a fact about the field, so it is a [`RootOfUnityError`] rather
/// than a panic — `TwoAdicityExceeded` names the two-adicity that fell short.
///
/// This subsumes the `2n`-th root the halved-squares form of the identity would have needed. A
/// `2n`-th root exists whenever `2n | q - 1`; for odd `n` that follows from `n | q - 1` alone, and
/// for even `n` it needs two-adicity at least `v2(n) + 1`, which never exceeds the `log2(n) + 1`
/// this asks for — `2n - 1` is odd and above one, so it is not itself a power of two and `L >= 2n`.
/// So a field that can host the convolution can always host the `2n`-th root, and this is the only
/// condition worth checking.
pub fn bluestein_convolution_domain<F: KnownOrder, R: RngCore + CryptoRng>(
    size: usize,
    rng: &mut R,
) -> Result<FFTDomain<F>, RootOfUnityError> {
    if size == 0 {
        return Err(RootOfUnityError::OrderDoesNotDivide { n: 0 });
    }
    let length = bluestein_convolution_length(size);
    let root = F::try_two_adic_root_of_unity(length.trailing_zeros(), rng)?;
    Ok(FFTDomain::from_generator(root, length))
}

/// Transform `values` in place over `domain`, by Bluestein's algorithm.
///
/// `domain` must be `1, w, ..., w^{n-1}` for a primitive `n`th root of unity `w`, for any `n`, and
/// `convolution_domain` the powers of a primitive `L`-th root for a power of two
/// `L >= bluestein_convolution_length(n)` — [`bluestein_convolution_domain`] builds one, or
/// reports that the field cannot.
///
/// Three `n`-length chirp passes and a padded convolution of length up to `4n`, so `O(n log n)` at
/// any size, prime included.
///
/// # Panics
/// Panics if `values` and `domain` differ in length, or if `convolution_domain` is not a power of
/// two at least `bluestein_convolution_length(n)` — a caller holding both already knows the sizes,
/// so these are programmer errors rather than facts about the field.
pub fn bluestein_transform<F: FiniteField>(
    values: &mut [F],
    domain: &FFTDomain<F>,
    convolution_domain: &FFTDomain<F>,
) {
    let n = values.len();
    assert_eq!(
        n,
        domain.size(),
        "values and domain must have the same length"
    );
    let length = convolution_domain.size();
    assert!(
        length.is_power_of_two(),
        "the convolution length is {length} but must be a power of two"
    );
    assert!(
        length >= bluestein_convolution_length(n),
        "a transform of {n} points needs a convolution length of at least {}, not {length}",
        bluestein_convolution_length(n)
    );

    if n == 1 {
        // The transform of a single coefficient is itself: domain[0] is 1.
        return;
    }

    let w = domain.powers();

    // `t[m]` is `T(m) mod n` for m in 0..=n, accumulated as `T(m + 1) = T(m) + m` rather than
    // formed as `m * (m - 1) / 2`, which would overflow `usize` at a large n.
    let mut t = Vec::with_capacity(n + 1);
    let mut accumulator = 0usize;
    for m in 0..=n {
        t.push(accumulator);
        accumulator = (accumulator + m) % n;
    }

    // The chirped input, zero-padded to the convolution length.
    let mut chirped = vec![F::zero(); length];
    for (j, x) in values.iter().enumerate() {
        chirped[j] = *x * w[(t[j] + j) % n];
    }

    // The conjugate chirp `w^(-T(m))`, laid out so that index `m mod length` holds the term for a
    // displacement of `m` in `-(n-1)..(n-1)`. `T(-m) = T(m + 1)`, which is why the table runs to
    // `n` rather than `n - 1`. The two ranges are disjoint exactly because `length >= 2n - 1`.
    let mut kernel = vec![F::zero(); length];
    for (m, slot) in kernel[..n].iter_mut().enumerate() {
        *slot = w[(n - t[m]) % n];
    }
    for m in 1..n {
        kernel[length - m] = w[(n - t[m + 1]) % n];
    }

    // The cyclic convolution, through the radix-2 kernel: transform both, multiply pointwise,
    // transform back over the inverse domain and scale by `1 / length`.
    transform_in_place(&mut chirped, convolution_domain.powers());
    transform_in_place(&mut kernel, convolution_domain.powers());
    for (a, b) in chirped.iter_mut().zip(kernel.iter()) {
        *a *= *b;
    }
    transform_in_place(&mut chirped, convolution_domain.inverse().powers());
    let length_inverse = F::new(length as u64).inverse();

    for (k, slot) in values.iter_mut().enumerate() {
        *slot = chirped[k] * length_inverse * w[t[k]];
    }
}

#[cfg(test)]
mod tests {
    use super::{bluestein_convolution_domain, bluestein_convolution_length, bluestein_transform};
    use crate::{
        fft::prime_factor::transform_any,
        fields::{Bn254Fr, KoalaBear, Mersenne31, PrimeFieldElement64, RootOfUnityError},
        identities::{One, Zero},
        FFTDomain, FiniteField, KnownOrder,
    };
    use rand::{prelude::StdRng, Rng, SeedableRng};

    /// Goldilocks, `2^64 - 2^32 + 1`: `q - 1 = 2^32 * 3 * 5 * 17 * 257 * 65537`, so it hosts prime
    /// sizes 17 and 257 alongside a two-adicity deep enough for their convolutions.
    type Goldilocks = PrimeFieldElement64<18_446_744_069_414_584_321>;

    /// The transform by its definition: the Vandermonde matrix applied to the coefficients,
    /// sharing no code with any kernel. The same oracle `prime_factor`'s tests use.
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

    /// Bluestein at `size` over F agrees with the definition on a pseudorandom input.
    fn agrees_with_the_definition<F: KnownOrder>(size: usize, seed: u64) {
        let mut rng = StdRng::seed_from_u64(seed);
        let w = F::root_of_unity(size as u64, &mut rng);
        let domain =
            FFTDomain::try_from_generator(w, size).unwrap_or_else(|e| panic!("size {size}: {e}"));
        let convolution_domain = bluestein_convolution_domain::<F, _>(size, &mut rng)
            .unwrap_or_else(|e| panic!("size {size}: {e}"));

        let coefficients: Vec<F> = (0..size).map(|_| F::random(&mut rng)).collect();
        let mut values = coefficients.clone();
        bluestein_transform(&mut values, &domain, &convolution_domain);
        assert_eq!(
            values,
            reference_dft(&coefficients, domain.powers()),
            "Bluestein at size {size} disagrees with the definition"
        );
    }

    /// The padded convolution length is the least power of two at least `2n - 1`.
    #[test]
    fn test_convolution_length_is_the_least_padded_power_of_two() {
        assert_eq!(bluestein_convolution_length(1), 1);
        assert_eq!(bluestein_convolution_length(2), 4);
        assert_eq!(bluestein_convolution_length(3), 8);
        assert_eq!(bluestein_convolution_length(5), 16);
        assert_eq!(bluestein_convolution_length(7), 16);
        assert_eq!(bluestein_convolution_length(9), 32);
        assert_eq!(bluestein_convolution_length(127), 256);
        // A power of two n needs 2n: `2n - 1` is one short of `2n` and never a power of two itself.
        assert_eq!(bluestein_convolution_length(16), 32);
    }

    /// Bluestein agrees with the definition at a prime size, the case the quadratic fallback
    /// exists for.
    #[test]
    fn test_a_prime_size_agrees_with_the_definition() {
        // 65520 = 2^4 * 3^2 * 5 * 7 * 13, and two-adicity 4 caps the convolution at 16, so 5 and 7
        // are the prime sizes this field can host.
        for size in [5, 7] {
            agrees_with_the_definition::<PrimeFieldElement64<65521>>(size, 357 + size as u64);
        }
        // q - 1 = 2^32 * 3 * 5 * 17 * 257 * 65537: two-adicity 32 leaves room for much more.
        for size in [17, 257] {
            agrees_with_the_definition::<Goldilocks>(size, 1_000 + size as u64);
        }
    }

    /// Bluestein agrees with the definition at a large prime size, where the quadratic route is
    /// 16129 multiplications and this one is a length-256 convolution.
    #[test]
    fn test_a_large_prime_size_agrees_with_the_definition() {
        // KoalaBear: q - 1 = 2^24 * 127, so 127 is the only odd prime order available and the
        // two-adicity is far more than the 8 its convolution needs.
        agrees_with_the_definition::<KoalaBear>(127, 127);
    }

    /// Bluestein agrees with the definition at an odd prime power, the other size the
    /// prime-factor decomposition has no coprime split for.
    #[test]
    fn test_an_odd_prime_power_size_agrees_with_the_definition() {
        // 576 = 2^6 * 3^2, so this field has a primitive 9th root and a 32nd root for size 9's
        // convolution.
        agrees_with_the_definition::<PrimeFieldElement64<577>>(9, 9);
        // 3456 = 2^7 * 3^3, likewise for 27 and its length-64 convolution.
        agrees_with_the_definition::<PrimeFieldElement64<3457>>(27, 27);
    }

    /// Bluestein is correct at every size the field can host a convolution for, not only the
    /// sizes the dispatcher would choose it at.
    #[test]
    fn test_every_size_within_the_two_adicity_agrees_with_the_definition() {
        // Two-adicity 4 caps the convolution at 16, so sizes up to 8 that divide 65520.
        for size in [1, 2, 3, 4, 5, 6, 7, 8] {
            agrees_with_the_definition::<PrimeFieldElement64<65521>>(size, size as u64);
        }
    }

    /// The length-one transform is the identity: the constant polynomial takes its own value at
    /// the single point 1.
    #[test]
    fn test_the_length_one_transform_is_the_identity() {
        type F = PrimeFieldElement64<65521>;
        let mut rng = StdRng::seed_from_u64(1);
        let domain = FFTDomain::from_generator(F::one(), 1);
        let convolution_domain = bluestein_convolution_domain::<F, _>(1, &mut rng)
            .expect("a first root of unity exists in every field");
        assert_eq!(convolution_domain.size(), 1);
        let mut values = [F::new(7)];
        bluestein_transform(&mut values, &domain, &convolution_domain);
        assert_eq!(values, [F::new(7)]);
    }

    /// Bluestein over the inverse domain, scaled by `1/n`, undoes Bluestein over the domain.
    #[test]
    fn test_round_trip_through_the_inverse_domain() {
        type F = KoalaBear;
        let size = 127;
        let mut rng = StdRng::seed_from_u64(31);
        let w = F::root_of_unity(size as u64, &mut rng);
        let domain = FFTDomain::from_generator(w, size);
        let convolution_domain =
            bluestein_convolution_domain::<F, _>(size, &mut rng).expect("two-adicity 24");

        let coefficients: Vec<F> = (0..size).map(|_| F::random(&mut rng)).collect();
        let mut values = coefficients.clone();
        bluestein_transform(&mut values, &domain, &convolution_domain);
        assert_ne!(
            values, coefficients,
            "the transform is not the identity here"
        );

        bluestein_transform(&mut values, &domain.inverse(), &convolution_domain);
        let size_inverse = F::new(size as u64).inverse();
        let recovered: Vec<F> = values.iter().map(|v| *v * size_inverse).collect();
        assert_eq!(recovered, coefficients);
    }

    /// A constant transforms to itself at every point, at a prime size.
    #[test]
    fn test_a_constant_transforms_to_itself() {
        type F = Goldilocks;
        let size = 17;
        let mut rng = StdRng::seed_from_u64(17);
        let w = F::root_of_unity(size as u64, &mut rng);
        let domain = FFTDomain::from_generator(w, size);
        let convolution_domain =
            bluestein_convolution_domain::<F, _>(size, &mut rng).expect("two-adicity 32");

        let mut values = vec![F::zero(); size];
        values[0] = F::new(7);
        bluestein_transform(&mut values, &domain, &convolution_domain);
        assert_eq!(values, vec![F::new(7); size]);
    }

    /// Bluestein agrees with the prime-factor route at a composite size, where both apply.
    #[test]
    fn test_a_composite_size_agrees_with_the_prime_factor_route() {
        type F = PrimeFieldElement64<65521>;
        let size = 6;
        let mut rng = StdRng::seed_from_u64(6);
        let w = F::root_of_unity(size as u64, &mut rng);
        let domain = FFTDomain::from_generator(w, size);
        let convolution_domain =
            bluestein_convolution_domain::<F, _>(size, &mut rng).expect("two-adicity 4");

        let coefficients: Vec<F> = (0..size).map(|_| F::new(rng.gen_range(0..65521))).collect();
        let mut by_bluestein = coefficients.clone();
        bluestein_transform(&mut by_bluestein, &domain, &convolution_domain);
        let mut by_prime_factor = coefficients;
        transform_any(&mut by_prime_factor, domain.powers());
        assert_eq!(by_bluestein, by_prime_factor);
    }

    /// Bluestein works over a 256-bit field, where the only reachable root of unity is two-adic.
    #[test]
    fn test_a_wide_field() {
        let mut rng = StdRng::seed_from_u64(254);
        let size = 8;
        let w = Bn254Fr::two_adic_root_of_unity(3, &mut rng);
        let domain = FFTDomain::from_generator(w, size);
        let convolution_domain =
            bluestein_convolution_domain::<Bn254Fr, _>(size, &mut rng).expect("two-adicity 28");

        let coefficients: Vec<Bn254Fr> = (0..size).map(|_| Bn254Fr::random(&mut rng)).collect();
        let mut values = coefficients.clone();
        bluestein_transform(&mut values, &domain, &convolution_domain);
        assert_eq!(values, reference_dft(&coefficients, domain.powers()));
    }

    /// A field whose two-adicity cannot reach the convolution length is an error value naming
    /// that shortfall, not a panic and not a wrong transform.
    #[test]
    fn test_a_two_adicity_too_small_for_the_convolution_is_an_error() {
        let mut rng = StdRng::seed_from_u64(2);
        // Mersenne-31: q - 1 = 2 * (2^30 - 1), so there is no transform here beyond size two and
        // size 5's length-16 convolution is out of reach.
        assert_eq!(
            bluestein_convolution_domain::<Mersenne31, _>(5, &mut rng),
            Err(RootOfUnityError::TwoAdicityExceeded {
                log_n: 4,
                two_adicity: 1
            })
        );
        // 12 = 2^2 * 3: this field has a primitive 4th root of unity but no 8th one, so size 4's
        // length-8 convolution is one doubling too deep.
        assert_eq!(
            bluestein_convolution_domain::<PrimeFieldElement64<13>, _>(4, &mut rng),
            Err(RootOfUnityError::TwoAdicityExceeded {
                log_n: 3,
                two_adicity: 2
            })
        );
    }

    /// A size of zero has no transform, and is an error rather than an underflow in the padding.
    #[test]
    fn test_a_size_of_zero_is_an_error() {
        let mut rng = StdRng::seed_from_u64(0);
        assert_eq!(
            bluestein_convolution_domain::<PrimeFieldElement64<65521>, _>(0, &mut rng),
            Err(RootOfUnityError::OrderDoesNotDivide { n: 0 })
        );
    }

    /// A convolution domain shorter than `2n - 1` is refused: the cyclic convolution would alias
    /// the chirp onto itself and the transform would be silently wrong.
    #[test]
    #[should_panic(expected = "needs a convolution length of at least 16")]
    fn test_a_convolution_domain_that_is_too_short_is_refused() {
        type F = PrimeFieldElement64<65521>;
        let mut rng = StdRng::seed_from_u64(5);
        let w = F::root_of_unity(5, &mut rng);
        let domain = FFTDomain::from_generator(w, 5);
        // Size 5 needs 16; 8 is a power of two and still one doubling short.
        let too_short = bluestein_convolution_domain::<F, _>(3, &mut rng).expect("length 8");
        assert_eq!(too_short.size(), 8);
        let mut values = vec![F::new(1); 5];
        bluestein_transform(&mut values, &domain, &too_short);
    }

    /// A convolution domain whose size is not a power of two is refused: the radix-2 kernel
    /// cannot run over it.
    #[test]
    #[should_panic(expected = "must be a power of two")]
    fn test_a_convolution_domain_that_is_not_a_power_of_two_is_refused() {
        type F = PrimeFieldElement64<65521>;
        let mut rng = StdRng::seed_from_u64(12);
        let w = F::root_of_unity(5, &mut rng);
        let domain = FFTDomain::from_generator(w, 5);
        let g = F::root_of_unity(20, &mut rng);
        let not_a_power_of_two = FFTDomain::from_generator(g, 20);
        let mut values = vec![F::new(1); 5];
        bluestein_transform(&mut values, &domain, &not_a_power_of_two);
    }

    /// A length mismatch between the values and the domain is refused.
    #[test]
    #[should_panic(expected = "same length")]
    fn test_a_length_mismatch_is_refused() {
        type F = PrimeFieldElement64<65521>;
        let mut rng = StdRng::seed_from_u64(7);
        let w = F::root_of_unity(7, &mut rng);
        let domain = FFTDomain::from_generator(w, 7);
        let convolution_domain = bluestein_convolution_domain::<F, _>(7, &mut rng).expect("16");
        let mut values = vec![F::new(1); 5];
        bluestein_transform(&mut values, &domain, &convolution_domain);
    }
}
