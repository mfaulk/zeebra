//! Dense bivariate multiplication by Kronecker substitution through the NTT (#944).
//!
//! Substitute `y → x^K`, with `K` one more than the product's degree in `x`, multiply the two
//! univariate images through the transform, and unpack. No `x`-exponent of the product reaches
//! `K`, so no two product monomials share an image and the unpacking is exact. The cost is three
//! transforms of length about `(deg_y(a·b) + 1) · K`, `O(D² log D)` for a dense product of total
//! degree `D`, against the `Θ(D⁴)` coefficient products of the dense triangle.
//!
//! The route needs a power-of-two domain, so [`KnownOrder`] and a source of randomness, which
//! `Mul` cannot carry for the reason `fft::multiply` records. [`multiply_bivariate`] is the
//! dispatcher a caller with both reaches for.

use rand::{CryptoRng, RngCore};

use crate::{
    fft::multiply::try_multiply_via_fft,
    fields::RootOfUnityError,
    poly::multivariate::{
        monomial_hash::{BuildMonomialHasher, MonomialMap},
        sparse_multivariate_multiply::{multiply, variable_degrees},
        sparse_multivariate_polynomial::SparseMultiPoly,
    },
    KnownOrder, Monomial, Polynomial, UnivariatePolynomial,
};

/// The product total degree at and above which [`multiply_bivariate`] takes the Kronecker route
/// over the dense triangle, for a dense pair.
///
/// Measured with `examples/bivariate_kronecker.rs` over KoalaBear on an Apple M4 Pro, one thread,
/// unpinned, best of five, at `0cabbad2` plus this change. Dense operands of total degree `d`:
///
/// | product degree | step | triangle | Kronecker | ratio |
/// |---:|---|---:|---:|---:|
/// | 30 | `p²`, `d = 15` | 0.034 ms | 0.034 ms | 0.98x |
/// | 45 | `p²·p`, `d = 15` | 0.119 ms | 0.141 ms | 0.85x |
/// | 54 | `p²`, `d = 27` | 0.288 ms | 0.142 ms | 2.03x |
/// | 81 | `p²·p`, `d = 27` | 1.084 ms | 0.302 ms | 3.59x |
/// | 486 | `p²`, `d = 243` | 1 814.5 ms | 14.9 ms | 121.6x |
/// | 729 | `p²·p`, `d = 243` | 6 483.9 ms | 65.5 ms | 98.9x |
///
/// The crossing is in `(45, 54]`, and the threshold is the upper end, so the dispatcher never
/// takes the transform below a measured win. The bench host has not re-measured it; the
/// transform's fixed cost is small enough that the crossing moves the threshold by a few degrees,
/// not the conclusion.
pub const KRONECKER_CROSSOVER: u64 = 54;

/// How many packed coefficients may be allocated per operand-term product before the pair counts
/// as too sparse for the route.
///
/// The test of `DENSE_TRIANGLE_SLOT_RATIO`, for the same reason: the product has at most `|a|·|b|`
/// monomials, so a packing within a constant factor of that is within the factor of the output.
/// A dense pair of total degree `d` each has about `d⁴ / 4` products against a packing of about
/// `4d²`, so it clears this by orders of magnitude; `(x^20000 + 1)(y^20000 + 1)` has four
/// products against a packing of `4·10⁸` and is refused.
const KRONECKER_SLOT_RATIO: u64 = 4;

/// Bytes one transform-sized buffer may reach before the dispatcher refuses the route.
///
/// A bound on the worst case, not a performance threshold: the transform holds about three
/// buffers of this size at once.
const KRONECKER_BYTE_CAP: u64 = 256 * 1024 * 1024;

/// The substitution for a pair: `K`, the stride `y` is packed at, and an upper bound on the packed
/// product's length, `K · (deg_y(a·b) + 1)`. `None` if that length overflows a `u64`.
fn packing<F: KnownOrder>(
    a: &SparseMultiPoly<2, F>,
    b: &SparseMultiPoly<2, F>,
) -> Option<(u64, u64)> {
    let [ax, ay] = variable_degrees(a);
    let [bx, by] = variable_degrees(b);
    let stride = ax as u64 + bx as u64 + 1;
    let rows = ay as u64 + by as u64 + 1;
    Some((stride, stride.checked_mul(rows)?))
}

/// The univariate image of `p` under `y → x^stride`.
fn pack<F: KnownOrder>(p: &SparseMultiPoly<2, F>, stride: usize) -> UnivariatePolynomial<F> {
    let [x, y] = variable_degrees(p);
    let mut coefficients = vec![F::zero(); x as usize + stride * y as usize + 1];
    for (monomial, coefficient) in p.terms.iter() {
        let [i, j] = monomial.exponents;
        // Distinct monomials of one operand have distinct images, since `i < stride`.
        coefficients[i as usize + stride * j as usize] = *coefficient;
    }
    UnivariatePolynomial::from_coefficients(coefficients)
}

/// The product of two bivariate polynomials by Kronecker substitution, `y → x^K`.
///
/// Fails, as [`try_multiply_via_fft`] does, when the field's two-adicity cannot host a domain of
/// the packed product's length. Memory is `O((deg_y(a·b) + 1) · K)` field elements whatever the
/// operands' density, so a sparse pair such as `(x^20000 + 1)(y^20000 + 1)` is expensive here;
/// [`multiply_bivariate`] only routes dense pairs to it.
///
/// # Panics
/// Panics if the packed length does not fit in memory's address space, which no field's
/// two-adicity would host anyway.
pub fn try_multiply_kronecker<F: KnownOrder, R: RngCore + CryptoRng>(
    a: &SparseMultiPoly<2, F>,
    b: &SparseMultiPoly<2, F>,
    rng: &mut R,
) -> Result<SparseMultiPoly<2, F>, RootOfUnityError> {
    if a.terms.is_empty() || b.terms.is_empty() {
        return Ok(SparseMultiPoly::zero());
    }
    let (stride, _) = packing(a, b).expect("the packed length fits in a u64");
    let stride = usize::try_from(stride).expect("the stride fits in a usize");
    let product = try_multiply_via_fft(&pack(a, stride), &pack(b, stride), rng)?;

    let coefficients = product.coefficients();
    let occupied = coefficients.iter().filter(|c| !c.is_zero()).count();
    let mut terms: MonomialMap<2, F> =
        MonomialMap::with_capacity_and_hasher(occupied, BuildMonomialHasher);
    for (index, coefficient) in coefficients.iter().enumerate() {
        // Drop-on-cancel, as every multiply route does.
        if coefficient.is_zero() {
            continue;
        }
        let (x, y) = (index % stride, index / stride);
        terms.insert(Monomial::new(&[x as u32, y as u32]), *coefficient);
    }
    Ok(SparseMultiPoly { terms })
}

/// The product of two bivariate polynomials, by whichever route suits the pair.
///
/// Kronecker substitution where [`kronecker_selected`] says so, otherwise the route `a * b` takes.
/// Always the same polynomial as `a * b`.
pub fn multiply_bivariate<F: KnownOrder, R: RngCore + CryptoRng>(
    a: &SparseMultiPoly<2, F>,
    b: &SparseMultiPoly<2, F>,
    rng: &mut R,
) -> SparseMultiPoly<2, F> {
    if kronecker_selected(a, b) {
        if let Ok(product) = try_multiply_kronecker(a, b, rng) {
            return product;
        }
    }
    multiply(a, b)
}

/// Whether [`multiply_bivariate`] takes the Kronecker route for this pair.
///
/// Four conditions: the product's total degree is at least [`KRONECKER_CROSSOVER`]; the packing is
/// within `KRONECKER_SLOT_RATIO` (4) of the product count, so the pair is dense; the transform's
/// buffer fits under `KRONECKER_BYTE_CAP` (256 MiB); and the field's two-adicity hosts a domain
/// that long.
pub fn kronecker_selected<F: KnownOrder>(
    a: &SparseMultiPoly<2, F>,
    b: &SparseMultiPoly<2, F>,
) -> bool {
    if a.terms.is_empty() || b.terms.is_empty() {
        return false;
    }
    if a.degree().saturating_add(b.degree()) < KRONECKER_CROSSOVER {
        return false;
    }
    let Some((_, length)) = packing(a, b) else {
        return false;
    };
    let products = (a.terms.len() as u64).saturating_mul(b.terms.len() as u64);
    if length > products.saturating_mul(KRONECKER_SLOT_RATIO) {
        return false;
    }
    let Some(domain) = length.checked_next_power_of_two() else {
        return false;
    };
    if domain.saturating_mul(std::mem::size_of::<F>() as u64) > KRONECKER_BYTE_CAP {
        return false;
    }
    domain.trailing_zeros() <= F::two_adicity()
}

#[cfg(test)]
mod tests {
    use rand::{prelude::StdRng, Rng, SeedableRng};

    use super::{kronecker_selected, multiply_bivariate, try_multiply_kronecker};
    use crate::{
        fields::{BabyBear, KoalaBear, Mersenne31, RootOfUnityError, Zp18446744069414584321},
        poly::multivariate::sparse_multivariate_multiply::{multiply_by, MultiplyRoute},
        FiniteField, KnownOrder, Monomial, MultivariatePolynomial, One,
    };

    /// Dense of total degree `d`: every monomial `x^a y^b` with `a + b <= d`, every coefficient
    /// nonzero. The issue's reproducer.
    fn dense<F: FiniteField, R: Rng>(d: u32, rng: &mut R) -> MultivariatePolynomial<2, F> {
        let mut terms = Vec::new();
        for total in 0..=d {
            for a in 0..=total {
                terms.push((Monomial::<2>::new(&[a, total - a]), nonzero(rng)));
            }
        }
        MultivariatePolynomial::new(&terms)
    }

    /// `count` random terms with exponents up to `max` in each variable.
    fn sparse<F: FiniteField, R: Rng>(
        count: usize,
        max: u32,
        rng: &mut R,
    ) -> MultivariatePolynomial<2, F> {
        let terms: Vec<_> = (0..count)
            .map(|_| {
                let e = [rng.gen_range(0..=max), rng.gen_range(0..=max)];
                (Monomial::<2>::new(&e), nonzero::<F, _>(rng))
            })
            .collect();
        MultivariatePolynomial::new(&terms)
    }

    fn nonzero<F: FiniteField, R: Rng>(rng: &mut R) -> F {
        loop {
            let c = F::new(rng.gen::<u32>() as u64);
            if !c.is_zero() {
                return c;
            }
        }
    }

    /// The independent reference: every product materialised, then collected.
    fn reference<F: FiniteField>(
        a: &MultivariatePolynomial<2, F>,
        b: &MultivariatePolynomial<2, F>,
    ) -> MultivariatePolynomial<2, F> {
        multiply_by(a, b, MultiplyRoute::Materialize)
    }

    fn agrees<F: KnownOrder>(seed: u64) {
        let mut rng = StdRng::seed_from_u64(seed);
        let one = MultivariatePolynomial::<2, F>::one();
        let x = MultivariatePolynomial::new(&[(Monomial::<2>::new(&[1, 0]), F::one())]);
        let y = MultivariatePolynomial::new(&[(Monomial::<2>::new(&[0, 1]), F::one())]);
        let x_only = MultivariatePolynomial::new(
            &(0..=9u32)
                .map(|i| (Monomial::<2>::new(&[i, 0]), nonzero::<F, _>(&mut rng)))
                .collect::<Vec<_>>(),
        );
        let y_only = MultivariatePolynomial::new(
            &(0..=7u32)
                .map(|i| (Monomial::<2>::new(&[0, i]), nonzero::<F, _>(&mut rng)))
                .collect::<Vec<_>>(),
        );
        let constant = MultivariatePolynomial::new(&[(
            Monomial::<2>::new(&[0, 0]),
            nonzero::<F, _>(&mut rng),
        )]);
        let mut pairs = vec![
            (one.clone(), one.clone()),
            (x.clone(), y.clone()),
            (y.clone(), x.clone()),
            (constant.clone(), dense(5, &mut rng)),
            (dense(4, &mut rng), constant),
            (x_only.clone(), y_only.clone()),
            (x_only.clone(), x_only),
            (y_only.clone(), y_only),
            (sparse(12, 40, &mut rng), sparse(9, 30, &mut rng)),
            (sparse(30, 6, &mut rng), dense(6, &mut rng)),
        ];
        for d in [3, 27, 81] {
            pairs.push((dense(d, &mut rng), dense(d, &mut rng)));
        }
        // Unequal degrees in each variable, so `K` is not symmetric in the operands.
        pairs.push((dense(27, &mut rng), dense(3, &mut rng)));
        for (a, b) in pairs {
            let expected = reference(&a, &b);
            let got = try_multiply_kronecker(&a, &b, &mut rng)
                .expect("the field hosts the domain at these degrees");
            assert_eq!(got, expected, "degrees {} and {}", a.degree(), b.degree());
            assert_eq!(multiply_bivariate(&a, &b, &mut rng), expected);
        }
    }

    #[test]
    fn test_kronecker_agrees_with_the_materialising_reference() {
        agrees::<KoalaBear>(1);
        agrees::<BabyBear>(2);
        agrees::<Zp18446744069414584321>(3);
    }

    /// A cube at degree 243, `p² · p`: the issue's headline case, at a size the reference can
    /// check because only the dense triangle (not materialisation) is run against it.
    #[test]
    fn test_kronecker_agrees_with_the_triangle_on_a_cube() {
        let mut rng = StdRng::seed_from_u64(9);
        let p = dense::<KoalaBear, _>(81, &mut rng);
        let square = try_multiply_kronecker(&p, &p, &mut rng).unwrap();
        assert_eq!(square, multiply_by(&p, &p, MultiplyRoute::DenseTriangle));
        let cube = try_multiply_kronecker(&square, &p, &mut rng).unwrap();
        assert_eq!(cube, multiply_by(&square, &p, MultiplyRoute::DenseTriangle));
        assert_eq!(cube.degree(), 243);
    }

    #[test]
    fn test_zero_operands_give_zero() {
        let mut rng = StdRng::seed_from_u64(4);
        let p = dense::<KoalaBear, _>(5, &mut rng);
        let zero = MultivariatePolynomial::<2, KoalaBear>::zero();
        assert!(try_multiply_kronecker(&p, &zero, &mut rng)
            .unwrap()
            .is_zero());
        assert!(try_multiply_kronecker(&zero, &p, &mut rng)
            .unwrap()
            .is_zero());
        assert!(multiply_bivariate(&zero, &p, &mut rng).is_zero());
    }

    /// Coefficients that cancel leave no zero term behind: `(x + y)(x - y) = x² - y²`.
    #[test]
    fn test_cancelled_terms_are_dropped() {
        let mut rng = StdRng::seed_from_u64(5);
        let one = KoalaBear::one();
        let a = MultivariatePolynomial::new(&[
            (Monomial::<2>::new(&[1, 0]), one),
            (Monomial::<2>::new(&[0, 1]), one),
        ]);
        let b = MultivariatePolynomial::new(&[
            (Monomial::<2>::new(&[1, 0]), one),
            (Monomial::<2>::new(&[0, 1]), -one),
        ]);
        let product = try_multiply_kronecker(&a, &b, &mut rng).unwrap();
        assert_eq!(product.terms().len(), 2);
        assert_eq!(product, reference(&a, &b));
    }

    /// Mersenne-31 has two-adicity 1: the route refuses, and the dispatcher still answers.
    #[test]
    fn test_a_field_without_the_two_adicity_falls_back() {
        let mut rng = StdRng::seed_from_u64(6);
        let p = dense::<Mersenne31, _>(81, &mut rng);
        assert!(matches!(
            try_multiply_kronecker(&p, &p, &mut rng),
            Err(RootOfUnityError::TwoAdicityExceeded { .. })
        ));
        assert!(!kronecker_selected(&p, &p));
        assert_eq!(multiply_bivariate(&p, &p, &mut rng), reference(&p, &p));
    }

    /// Dense pairs above the crossover are routed to Kronecker; sparse ones never are, because
    /// the packed length is quadratic in the degree whatever the term count.
    #[test]
    fn test_the_dispatcher_routes_by_density_and_degree() {
        let mut rng = StdRng::seed_from_u64(8);
        let p = dense::<KoalaBear, _>(243, &mut rng);
        assert!(kronecker_selected(&p, &p));
        let small = dense::<KoalaBear, _>(1, &mut rng);
        assert!(!kronecker_selected(&small, &small));
        let spread = MultivariatePolynomial::<2, KoalaBear>::new(&[
            (Monomial::<2>::new(&[20000, 0]), KoalaBear::one()),
            (Monomial::<2>::new(&[0, 0]), KoalaBear::one()),
        ]);
        let other = MultivariatePolynomial::<2, KoalaBear>::new(&[
            (Monomial::<2>::new(&[0, 20000]), KoalaBear::one()),
            (Monomial::<2>::new(&[0, 0]), KoalaBear::one()),
        ]);
        assert!(!kronecker_selected(&spread, &other));
        assert_eq!(
            multiply_bivariate(&spread, &other, &mut rng),
            reference(&spread, &other)
        );
    }
}
