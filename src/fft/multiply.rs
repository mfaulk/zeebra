//! Polynomial multiplication through the transform, and the dispatcher that chooses it.
//!
//! Evaluate both operands on a domain large enough to hold the product, multiply pointwise, and
//! interpolate: `O(n log n)` against the schoolbook `O(d^2)` of `Mul`.
//!
//! [`multiply`] dispatches over **three** routes by measured threshold — schoolbook, Karatsuba,
//! then the transform. The first two are [`multiply_dense`]'s own choice on its base case; this
//! module chooses between that and the transform on [`fft_multiplication_crossover`]. #185 is where
//! the three were joined, and its finding is that the threshold has to be measured against
//! Karatsuba rather than inherited from the schoolbook-versus-transform figure.
//!
//! `Mul` itself stays schoolbook, and not by oversight — see `karatsuba::multiply_dense` for why
//! the operator is a separate decision from this dispatcher, and §4.1.2 of
//! `docs/research/fast-univariate.md` for the measurement behind leaving it alone. Finding a domain
//! needs a primitive `2^k`-th root of unity, which needs [`KnownOrder`] and a source of randomness
//! — neither of which `Mul`'s signature can carry, and the first of which the Gröbner core
//! deliberately does not require of a coefficient type
//! (`test_the_grobner_stack_needs_no_field_cardinality` fails to compile if it starts to). So the
//! transform is reached through the functions here, of which [`multiply`] is the one to call when
//! the degree is not known in advance.

use rand::{CryptoRng, RngCore};

use crate::{
    evaluate, fft::domain::FFTDomain, fields::RootOfUnityError, interpolate, poly::multiply_dense,
    FiniteField, KnownOrder, Polynomial, UnivariatePolynomial,
};

/// The product degree at and above which the transform beats [`multiply_dense`], measured per
/// element width.
///
/// **The comparand is Karatsuba, not schoolbook** (#185). That is the whole content of these
/// numbers and the reason they are not the ones #124 and #161 measured: the dispatcher's question
/// is which of the two routes it actually has is faster, and below this threshold that route is
/// `multiply_dense`, which is Karatsuba above its own base case. Since Karatsuba is 10.7x–22.9x
/// schoolbook at degree `2^14` (#165), a threshold calibrated against schoolbook is calibrated
/// against a route the dispatcher never takes.
///
/// `examples/multiplication_dispatch.rs` is the instrument — three arms in one process, interleaved
/// and `taskset`-pinned, agreement checked outside the timing. Measured crossings, as the bracket
/// between the two adjacent doublings that straddle them:
///
/// | field | element | Karatsuba-vs-transform crossing | threshold |
/// |---|---|---|---|
/// | KoalaBear | 4 bytes | (2046, 4094] | **4096** |
/// | Zp65537 | 8 bytes | (126, 254] | 256 |
/// | Goldilocks | 8 bytes | (254, 510] | **512** |
/// | BN254 `Fr` | 32 bytes | (254, 510] | **512** |
///
/// Rounded **up** to the next power of two, and for the 8-byte tier up to the later of the two
/// fields measured, so the dispatcher errs toward the route that is cheaper at small sizes and
/// never pays the transform's fixed cost on a product too small to amortize it. The cost of erring
/// that way is bounded and small — on Zp65537 between 256 and 512 the transform is at most 1.60x
/// ahead — where erring the other way pays the transform's setup on every product in the band.
///
/// How these differ from the figures they replace, and why the direction is not uniform:
///
/// | element | #124 | #161's schoolbook-vs-transform | **this** |
/// |---|---:|---:|---:|
/// | 4 bytes | 16384 | not measurable from `univariate_scaling` | **4096** |
/// | 8 bytes | 2048 | 512 | **512** |
/// | 32 bytes | 512 | 256 | **512** |
///
/// The 4-byte row falls 4x because 16384 was never measured against anything — at product degree
/// 32766 the transform is 2.98x ahead of Karatsuba there, so the old threshold gave that up. The
/// 32-byte row does **not** fall to 256: Karatsuba is still 1.18x ahead at product degree 254 over
/// BN254, so taking #161's schoolbook crossing would have moved the threshold the wrong way. Both
/// corrections come from measuring the route the dispatcher has rather than the one it had.
///
/// # The 4-byte row is contingent, and the other two are not
///
/// Only the 4-byte tier's schoolbook loop autovectorizes — a 64-bit Montgomery reduction is
/// 128-bit arithmetic LLVM does not vectorize and a 32-bit one is 64-bit arithmetic it does, which
/// is `docs/MILESTONE-SIMD-PARALLELISM.md` §8.3's finding. So only the 4-byte tier's threshold
/// depends on whether that vectorization happened, and **under this crate's `lto = "fat"` with
/// `codegen-units = 1` it is not stable against things that are not the source.** The same source
/// at the same commit, built two ways:
///
/// | build | `vpmuludq` in the artifact | schoolbook at operand 1024 | Karatsuba | crossing |
/// |---|---:|---:|---:|---|
/// | `cargo build --release --examples` | 91 | 295.4 µs | 81.5 µs | (2046, 4094] → 4096 |
/// | `cargo build --release --example multiplication_dispatch` | **0** | 527.2 µs | 141.0 µs | (510, 1022] → 1024 |
///
/// Both scalar routes lose 1.74x–1.77x together and the transform does not move at all (98.1 µs
/// against 100.6), which is what identifies the cause as the 4-byte inner loop rather than
/// anything in the dispatch. The 8- and 32-byte crossings are **identical in both artifacts**, as
/// the paragraph above predicts they must be.
///
/// **4096 is the vectorized figure, and it is shipped because that is the state the library is
/// normally in**: `univariate_scaling`, `karatsuba_crossover`, `field_width` and
/// `cryptanalysis_ladder` all carry `vpmuludq` at this commit. A consumer whose own binary loses
/// the vectorization will see the transform win from product degree 1024 rather than 4096, and
/// Karatsuba at most 2.00x behind it in between. `multiply_above` takes an explicit threshold for
/// exactly this kind of caller. Tracked as #244.
pub fn fft_multiplication_crossover<F: FiniteField>() -> u32 {
    match std::mem::size_of::<F>() {
        0..=4 => 4096,
        // The 8-byte and wider tiers coincide at this measurement. Kept as separate arms rather
        // than collapsed: they are separate because the cost of one field multiplication differs
        // by 11x across them, and a re-measurement is as likely to separate them again as not.
        5..=8 => 512,
        _ => 512,
    }
}

/// The product of `a` and `b`, evaluated and interpolated over `domain`.
///
/// The domain is a parameter because one domain serves any number of products that fit in it, and
/// building it is the expensive part: a root of unity costs a rejection sample and an
/// exponentiation, against `n` multiplications for the powers.
///
/// Bounded on [`FiniteField`] alone, so the core that has no field cardinality can still use it
/// with a domain from elsewhere. The domain must be the powers of a root of unity starting at one
/// — what [`FFTDomain::try_from_generator`] builds — and not, say, the odd half that
/// [`FFTDomain::split`] returns, which is a point set the transform does not invert over.
///
/// # Panics
/// Panics if the domain holds fewer than `deg a + deg b + 1` points, where the product would wrap
/// around rather than be recovered. That is a choice the caller made, unlike the field's
/// two-adicity.
pub fn multiply_over_domain<F: FiniteField>(
    a: &UnivariatePolynomial<F>,
    b: &UnivariatePolynomial<F>,
    domain: &FFTDomain<F>,
) -> UnivariatePolynomial<F> {
    if a.is_zero() || b.is_zero() {
        return UnivariatePolynomial::zero();
    }

    let points = product_degree(a, b) as usize + 1;
    assert!(
        domain.size() >= points,
        "a product of degree {} needs a domain of at least {points} points, not {}",
        points - 1,
        domain.size()
    );

    let a_values = evaluate(a, domain);
    let b_values = evaluate(b, domain);
    let products: Vec<F> = a_values
        .iter()
        .zip(b_values.iter())
        .map(|(x, y)| *x * *y)
        .collect();

    interpolate(&products, domain)
}

/// The product of `a` and `b` through a domain built for the occasion.
///
/// Fails if the field's two-adicity is below `log2` of the points the product needs, where no
/// power-of-two domain of that size exists — a fact about the field, so a value rather than a
/// panic. [`multiply`] falls back to [`multiply_dense`] on exactly that failure.
pub fn try_multiply_via_fft<F: KnownOrder, R: RngCore + CryptoRng>(
    a: &UnivariatePolynomial<F>,
    b: &UnivariatePolynomial<F>,
    rng: &mut R,
) -> Result<UnivariatePolynomial<F>, RootOfUnityError> {
    if a.is_zero() || b.is_zero() {
        return Ok(UnivariatePolynomial::zero());
    }

    let points = product_degree(a, b) as usize + 1;
    let size = points.next_power_of_two();
    let generator = F::try_two_adic_root_of_unity(size.trailing_zeros(), rng)?;
    // Infallible: `size` is a power of two and the root above has order exactly `size`, which are
    // the only two things the domain checks.
    let domain = FFTDomain::from_generator(generator, size);

    Ok(multiply_over_domain(a, b, &domain))
}

/// The product of `a` and `b`, by whichever route is faster for their degree.
///
/// Three routes, by measured threshold: schoolbook, then Karatsuba, then the transform. The first
/// two are [`multiply_dense`]'s own choice on `karatsuba_base_case`; this function chooses between
/// that and the transform on [`fft_multiplication_crossover`]. A field that cannot host a domain
/// that large falls back to `multiply_dense` rather than to schoolbook. Always returns the same
/// polynomial as `a * b`.
pub fn multiply<F: KnownOrder, R: RngCore + CryptoRng>(
    a: &UnivariatePolynomial<F>,
    b: &UnivariatePolynomial<F>,
    rng: &mut R,
) -> UnivariatePolynomial<F> {
    multiply_above(a, b, fft_multiplication_crossover::<F>(), rng)
}

/// [`multiply`] with the crossover stated rather than taken from the measurement.
///
/// For a caller who has measured their own field, or whose polynomials are sparse enough that the
/// schoolbook loop skips most of its work and the default threshold is too low.
pub fn multiply_above<F: KnownOrder, R: RngCore + CryptoRng>(
    a: &UnivariatePolynomial<F>,
    b: &UnivariatePolynomial<F>,
    crossover: u32,
    rng: &mut R,
) -> UnivariatePolynomial<F> {
    if a.is_zero() || b.is_zero() {
        return UnivariatePolynomial::zero();
    }

    if product_degree(a, b) < crossover {
        return multiply_dense(a, b);
    }

    // The fallback is `multiply_dense`, not schoolbook. This arm is not a rare corner: a field
    // whose two-adicity cannot host the domain takes it at *every* degree above the crossover, and
    // Mersenne-31 — two-adicity 1 — is one such field, so this is where its large products land.
    try_multiply_via_fft(a, b, rng).unwrap_or_else(|_| multiply_dense(a, b))
}

/// The degree of the product, which over a field is the sum of the degrees.
///
/// Both operands are nonzero at every call site, so no leading coefficient is zero and the
/// leading terms cannot cancel.
fn product_degree<F: FiniteField>(a: &UnivariatePolynomial<F>, b: &UnivariatePolynomial<F>) -> u32 {
    a.degree() + b.degree()
}

#[cfg(test)]
mod tests {
    use rand::{prelude::StdRng, Rng, SeedableRng};

    use crate::{
        fft::multiply::{
            fft_multiplication_crossover, multiply, multiply_above, multiply_over_domain,
            try_multiply_via_fft,
        },
        fields::{
            BabyBear, Bn254Fr, KoalaBear, Mersenne31, RootOfUnityError, Zp18446744069414584321,
            Zp65537,
        },
        karatsuba_base_case_unstable,
        test_support::schoolbook_product,
        FFTDomain, FiniteField, KnownOrder, Polynomial, UnivariatePolynomial,
    };

    /// A polynomial of exactly the given degree: the leading coefficient is never zero.
    fn random_polynomial<F: FiniteField, R: Rng>(
        degree: usize,
        rng: &mut R,
    ) -> UnivariatePolynomial<F> {
        let mut coefficients: Vec<F> = (0..=degree)
            .map(|_| F::new(rng.gen::<u32>() as u64))
            .collect();
        while coefficients[degree].is_zero() {
            coefficients[degree] = F::new(rng.gen::<u32>() as u64);
        }
        UnivariatePolynomial::new(&coefficients)
    }

    /// The transform agrees with the schoolbook product it replaces, over one field.
    fn agrees_with_schoolbook<F: KnownOrder>(seed: u64, degrees: &[(usize, usize)]) {
        let mut rng = StdRng::seed_from_u64(seed);
        for &(da, db) in degrees {
            let a = random_polynomial::<F, _>(da, &mut rng);
            let b = random_polynomial::<F, _>(db, &mut rng);
            let expected = schoolbook_product(&a, &b);
            let product = try_multiply_via_fft(&a, &b, &mut rng)
                .expect("the field has the two-adicity for this degree");
            assert_eq!(product, expected, "degrees {da} and {db}");
            assert_eq!(product.degree() as usize, da + db);
        }
    }

    /// The transform's product is the schoolbook product, over every field with an NTT domain.
    ///
    /// The degree pairs include the boundary where `da + db + 1` is exactly a power of two, which
    /// is where an off-by-one in the domain size would wrap the product around.
    #[test]
    fn test_the_transform_agrees_with_schoolbook() {
        let degrees = [
            (0, 0),
            (1, 0),
            (1, 1),
            (3, 4),
            (4, 3),
            (7, 8),
            (15, 16),
            (31, 32),
        ];
        agrees_with_schoolbook::<Zp65537>(1, &degrees);
        agrees_with_schoolbook::<KoalaBear>(2, &degrees);
        agrees_with_schoolbook::<BabyBear>(3, &degrees);
        agrees_with_schoolbook::<Zp18446744069414584321>(4, &degrees);
        agrees_with_schoolbook::<Bn254Fr>(5, &degrees);
    }

    /// A degree whose domain would exceed the field's two-adicity is an error, not a wrong product.
    ///
    /// `2^31 - 1` is a Mersenne prime, so `q - 1 = 2 * (2^30 - 1)` and the largest power-of-two
    /// domain has two points. A product of degree 2 needs four.
    #[test]
    fn test_a_field_without_the_two_adicity_refuses() {
        let mut rng = StdRng::seed_from_u64(7);
        let a = random_polynomial::<Mersenne31, _>(1, &mut rng);
        let b = random_polynomial::<Mersenne31, _>(1, &mut rng);
        assert_eq!(
            try_multiply_via_fft(&a, &b, &mut rng),
            Err(RootOfUnityError::TwoAdicityExceeded {
                log_n: 2,
                two_adicity: 1,
            })
        );
    }

    /// The dispatcher falls back to `multiply_dense` rather than failing on such a field.
    ///
    /// The last two degrees put the product above the 4-byte transform threshold of 4096, so they
    /// reach the `unwrap_or_else` arm — the one a field of two-adicity 1 takes at *every* degree
    /// above the crossover — rather than only the below-crossover branch. Both are asserted equal
    /// to schoolbook, so the fallback is exercised and not merely entered.
    #[test]
    fn test_the_dispatcher_falls_back_when_the_field_cannot_host_a_domain() {
        let mut rng = StdRng::seed_from_u64(11);
        assert_eq!(Mersenne31::two_adicity(), 1);
        for degree in [1, 8, 64, 2049, 3000] {
            let a = random_polynomial::<Mersenne31, _>(degree, &mut rng);
            let b = random_polynomial::<Mersenne31, _>(degree, &mut rng);
            let product = multiply(&a, &b, &mut rng);
            assert_eq!(product, schoolbook_product(&a, &b), "degree {degree}");
            assert_eq!(product.degree() as usize, 2 * degree, "degree {degree}");
        }
    }

    /// The fallback arm is reached, not merely reachable: a product degree above the crossover over
    /// a field of two-adicity 1 has no domain, which `try_multiply_via_fft` must report as the
    /// error `multiply_above` catches.
    #[test]
    fn test_the_fallback_arm_is_the_one_a_low_two_adicity_field_takes() {
        let mut rng = StdRng::seed_from_u64(1_111);
        let degree = 2_049;
        assert!(2 * degree >= fft_multiplication_crossover::<Mersenne31>() as usize);
        let a = random_polynomial::<Mersenne31, _>(degree, &mut rng);
        let b = random_polynomial::<Mersenne31, _>(degree, &mut rng);
        assert!(
            try_multiply_via_fft(&a, &b, &mut rng).is_err(),
            "a two-adicity of 1 cannot host this domain, so the dispatcher's fallback is live"
        );
        assert_eq!(multiply(&a, &b, &mut rng), schoolbook_product(&a, &b));
    }

    /// The dispatcher agrees with schoolbook across all three routes' thresholds.
    ///
    /// Over an 8-byte field the Karatsuba base case is 16 coefficients and the transform threshold
    /// is a product degree of 512, so these operand degrees land on every route: 1 and 4 schoolbook
    /// inside `multiply_dense`, 16 through 300 Karatsuba, 600 and 1100 the transform.
    #[test]
    fn test_the_dispatcher_agrees_with_schoolbook_on_every_route() {
        let mut rng = StdRng::seed_from_u64(13);
        assert_eq!(fft_multiplication_crossover::<Zp65537>(), 512);
        assert_eq!(karatsuba_base_case_unstable::<Zp65537>(), 16);
        for degree in [1, 4, 16, 64, 300, 600, 1100] {
            let a = random_polynomial::<Zp65537, _>(degree, &mut rng);
            let b = random_polynomial::<Zp65537, _>(degree, &mut rng);
            assert_eq!(
                multiply(&a, &b, &mut rng),
                schoolbook_product(&a, &b),
                "degree {degree}"
            );
        }
    }

    /// Every degree from zero to past twice the widest Karatsuba base case agrees with schoolbook,
    /// which pins the schoolbook/Karatsuba boundary inside `multiply_dense` rather than sampling
    /// around it.
    ///
    /// Over a 4-byte field, where the base case is 48 — the largest of the three tiers, so this
    /// also covers the 16 and 4 of the others.
    #[test]
    fn test_every_small_degree_agrees_with_schoolbook() {
        let mut rng = StdRng::seed_from_u64(1_185);
        for degree in 0..=100 {
            let a = random_polynomial::<KoalaBear, _>(degree, &mut rng);
            let b = random_polynomial::<KoalaBear, _>(degree, &mut rng);
            let expected = schoolbook_product(&a, &b);
            let dispatched = multiply(&a, &b, &mut rng);
            assert_eq!(dispatched, expected, "degree {degree}");
            assert_eq!(dispatched.degree(), expected.degree(), "degree {degree}");
        }
    }

    /// The crossover is indexed by element width, which is what the measurement varies with.
    ///
    /// The figures are #185's, measured against Karatsuba rather than against schoolbook; see
    /// `fft_multiplication_crossover`'s doc comment for the table and for why the 4-byte tier fell
    /// 4x while the 32-byte tier did not move.
    #[test]
    fn test_the_crossover_follows_the_element_width() {
        assert_eq!(std::mem::size_of::<KoalaBear>(), 4);
        assert_eq!(fft_multiplication_crossover::<KoalaBear>(), 4096);
        assert_eq!(std::mem::size_of::<Zp18446744069414584321>(), 8);
        assert_eq!(
            fft_multiplication_crossover::<Zp18446744069414584321>(),
            512
        );
        assert_eq!(std::mem::size_of::<Bn254Fr>(), 32);
        assert_eq!(fft_multiplication_crossover::<Bn254Fr>(), 512);
    }

    /// Every threshold is at or above the Karatsuba base case for the same width, so the three
    /// routes are ordered and no band is skipped.
    ///
    /// This is the invariant that would break silently if one of the two constants were
    /// re-measured without the other: a transform threshold below the base case would leave
    /// Karatsuba unreachable through `multiply`.
    #[test]
    fn test_the_three_routes_are_ordered_at_every_width() {
        fn ordered<F: FiniteField>() {
            let base_case = karatsuba_base_case_unstable::<F>() as u32;
            let crossover = fft_multiplication_crossover::<F>();
            assert!(
                base_case <= crossover,
                "base case {base_case} is above the transform crossover {crossover} for a {}-byte element",
                std::mem::size_of::<F>()
            );
        }
        ordered::<KoalaBear>();
        ordered::<Mersenne31>();
        ordered::<Zp65537>();
        ordered::<Zp18446744069414584321>();
        ordered::<Bn254Fr>();
    }

    /// An explicit crossover overrides the measured one, in both directions.
    #[test]
    fn test_an_explicit_crossover_chooses_the_route() {
        let mut rng = StdRng::seed_from_u64(29);
        let a = random_polynomial::<Zp65537, _>(8, &mut rng);
        let b = random_polynomial::<Zp65537, _>(8, &mut rng);
        let expected = schoolbook_product(&a, &b);
        // Degree 16 is below the default, so force the transform with a crossover of zero.
        assert_eq!(multiply_above(&a, &b, 0, &mut rng), expected);
        assert_eq!(multiply_above(&a, &b, u32::MAX, &mut rng), expected);
    }

    /// Multiplying by the zero polynomial gives zero, which has no degree to transform.
    #[test]
    fn test_a_zero_operand_gives_zero() {
        let mut rng = StdRng::seed_from_u64(17);
        let a = random_polynomial::<Zp65537, _>(5, &mut rng);
        let zero = UnivariatePolynomial::<Zp65537>::zero();
        assert!(try_multiply_via_fft(&a, &zero, &mut rng).unwrap().is_zero());
        assert!(try_multiply_via_fft(&zero, &a, &mut rng).unwrap().is_zero());
        assert!(multiply(&zero, &zero, &mut rng).is_zero());
    }

    /// One domain serves many products, which is why the domain is a parameter.
    #[test]
    fn test_one_domain_serves_several_products() {
        let mut rng = StdRng::seed_from_u64(19);
        let n = 32;
        let w = Zp65537::root_of_unity(n as u64, &mut rng);
        let domain = FFTDomain::from_generator(w, n);

        for _ in 0..5 {
            let a = random_polynomial::<Zp65537, _>(10, &mut rng);
            let b = random_polynomial::<Zp65537, _>(10, &mut rng);
            assert_eq!(
                multiply_over_domain(&a, &b, &domain),
                schoolbook_product(&a, &b)
            );
        }
    }

    /// A domain too small for the product is a programmer error, since the caller chose it.
    #[test]
    #[should_panic(expected = "needs a domain of at least")]
    fn test_a_domain_too_small_for_the_product_is_refused() {
        let mut rng = StdRng::seed_from_u64(23);
        let w = Zp65537::root_of_unity(8, &mut rng);
        let domain = FFTDomain::from_generator(w, 8);
        let a = random_polynomial::<Zp65537, _>(5, &mut rng);
        let b = random_polynomial::<Zp65537, _>(5, &mut rng);
        // The product has degree 10, so it needs 11 points.
        let _ = multiply_over_domain(&a, &b, &domain);
    }
}
