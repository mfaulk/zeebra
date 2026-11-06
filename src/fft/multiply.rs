//! Polynomial multiplication through the transform.
//!
//! Evaluate both operands on a domain large enough to hold the product, multiply pointwise, and
//! interpolate: `O(n log n)` against the schoolbook `O(d^2)` of `Mul`.
//!
//! `Mul` itself stays schoolbook, and not by oversight. Finding a domain needs a primitive
//! `2^k`-th root of unity, which needs [`KnownOrder`] and a source of randomness — neither of
//! which `Mul`'s signature can carry, and the first of which the Gröbner core deliberately does
//! not require of a coefficient type (`test_the_grobner_stack_needs_no_field_cardinality` fails to
//! compile if it starts to). So the transform is reached through the functions here, of which
//! [`multiply`] is the one to call when the degree is not known in advance.

use rand::{CryptoRng, RngCore};

use crate::{
    evaluate, fft::domain::FFTDomain, fields::RootOfUnityError, interpolate, FiniteField,
    KnownOrder, Polynomial, UnivariatePolynomial,
};

/// The product degree at and above which the transform beats schoolbook, measured per element
/// width.
///
/// `examples/univariate_scaling.rs`'s **mul** and **fftmul** rows are the sweep this comes from;
/// the README's "What the univariate stages cost" records the numbers. The crossover is very late
/// and it is **not** one number:
///
/// | field | element | schoolbook wins until | transform's advantage at degree 16384 |
/// |---|---|---|---|
/// | KoalaBear | 4 bytes | degree ~12000 | 1.3x |
/// | Zp65537, Goldilocks | 8 bytes | degree ~1500 | 10-12x |
/// | BN254, BLS12-381 Fr | 32 bytes | degree ~460 | 24x |
///
/// The lever is the cost of one coefficient multiplication against the transform's per-element
/// bookkeeping, not the asymptotics: at degree 16384 the transform takes the same 13 ms over
/// KoalaBear, Zp65537 and Goldilocks — three fields whose schoolbook times differ by 9x — which
/// says this NTT is bound by allocation and recursion rather than by field arithmetic. Hence a
/// width-indexed threshold: a 32-byte element makes schoolbook dearer while leaving the transform
/// where it was.
///
/// Rounded **up** to the next power of two from the measured crossing, so the dispatcher never
/// picks the slower route on a field measured here.
pub fn fft_multiplication_crossover<F: FiniteField>() -> u32 {
    match std::mem::size_of::<F>() {
        0..=4 => 16384,
        5..=8 => 2048,
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
/// panic. [`multiply`] falls back to schoolbook on exactly that failure.
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
/// Schoolbook below [`fft_multiplication_crossover`], the transform at or above it, and schoolbook
/// again if the field cannot host a domain that large. Always returns the same polynomial as
/// `a * b`.
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
        return a * b;
    }

    try_multiply_via_fft(a, b, rng).unwrap_or_else(|_| a * b)
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
            let expected = &a * &b;
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

    /// The dispatcher falls back to schoolbook rather than failing on such a field.
    #[test]
    fn test_the_dispatcher_falls_back_when_the_field_cannot_host_a_domain() {
        let mut rng = StdRng::seed_from_u64(11);
        for degree in [1, 8, 64] {
            let a = random_polynomial::<Mersenne31, _>(degree, &mut rng);
            let b = random_polynomial::<Mersenne31, _>(degree, &mut rng);
            assert_eq!(multiply(&a, &b, &mut rng), &a * &b, "degree {degree}");
        }
    }

    /// The dispatcher agrees with schoolbook on both sides of the crossover.
    ///
    /// The threshold is a product degree of 2048 over an 8-byte field, so the last pair here takes
    /// the transform and the rest take the schoolbook loop.
    #[test]
    fn test_the_dispatcher_agrees_with_schoolbook_either_side_of_the_crossover() {
        let mut rng = StdRng::seed_from_u64(13);
        assert_eq!(fft_multiplication_crossover::<Zp65537>(), 2048);
        for degree in [1, 4, 16, 64, 300, 1100] {
            let a = random_polynomial::<Zp65537, _>(degree, &mut rng);
            let b = random_polynomial::<Zp65537, _>(degree, &mut rng);
            assert_eq!(multiply(&a, &b, &mut rng), &a * &b, "degree {degree}");
        }
    }

    /// The crossover is indexed by element width, which is what the measurement varies with.
    #[test]
    fn test_the_crossover_follows_the_element_width() {
        assert_eq!(std::mem::size_of::<KoalaBear>(), 4);
        assert_eq!(fft_multiplication_crossover::<KoalaBear>(), 16384);
        assert_eq!(std::mem::size_of::<Zp18446744069414584321>(), 8);
        assert_eq!(
            fft_multiplication_crossover::<Zp18446744069414584321>(),
            2048
        );
        assert_eq!(std::mem::size_of::<Bn254Fr>(), 32);
        assert_eq!(fft_multiplication_crossover::<Bn254Fr>(), 512);
    }

    /// An explicit crossover overrides the measured one, in both directions.
    #[test]
    fn test_an_explicit_crossover_chooses_the_route() {
        let mut rng = StdRng::seed_from_u64(29);
        let a = random_polynomial::<Zp65537, _>(8, &mut rng);
        let b = random_polynomial::<Zp65537, _>(8, &mut rng);
        let expected = &a * &b;
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
            assert_eq!(multiply_over_domain(&a, &b, &domain), &a * &b);
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
