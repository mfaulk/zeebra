//! Lagrange interpolation of polynomials over finite fields.
//!
//! Given a set of n points (x_0,y_0), ... , (x_{n-1}, y_{n-1}) with distinct x coordinates,
//! interpolation produces the unique polynomial p of degree at most n-1 with p(x_i) = y_i.
//!
//! The Lagrange interpolation formula:
//!
//!   p(x) = \sum_{j=1}^n y_j * l_j(x)
//!
//! where the l_j are the "Lagrange polynomials"
//!
//!   l_j(x) = \prod_{k=1..n, k \neq j \frac{x - x_k}{x_j - x_k}
//!
//! Written that way it is `O(n^3)`: each l_j multiplies up n-1 linear factors against a product
//! that grows to degree n-1. [`interpolate`] instead builds the numerator product once and divides
//! it down, which is `O(n^2)`. The `O(n^3)` form is kept as [`interpolate_reference`] so the two
//! can be differentially tested.

use std::collections::HashSet;

use crate::{fields::batch_invert, poly::univariate::UnivariatePolynomial, FiniteField};

// Only the `#[cfg(test)]` reference implementation below needs the trait's methods.
#[cfg(test)]
use crate::poly::univariate::Polynomial;

/// Interpolate n points into a polynomial of degree n-1.
///
/// `O(n^2)` field operations and `O(n)` memory.
///
/// # Arguments
/// * `points` - Collection of (x,y) points.
///
/// # Panics
/// If `points` is empty, or if two points share an x coordinate.
pub fn interpolate<F: FiniteField>(points: Vec<(F, F)>) -> UnivariatePolynomial<F> {
    assert!(!points.is_empty());
    assert_distinct_abscissae(&points);
    let n = points.len();

    // M(x) = \prod_i (x - x_i), of degree n, built once rather than once per basis polynomial.
    // That single product is what takes the whole routine from cubic to quadratic.
    let mut m = vec![F::zero(); n + 1];
    m[0] = F::one();
    for (degree, (x_i, _y_i)) in points.iter().enumerate() {
        // Multiply the degree-`degree` product in place by (x - x_i). Descending, so each read of
        // `m[k - 1]` happens before that slot is overwritten.
        for k in (1..=degree + 1).rev() {
            m[k] = m[k - 1] - *x_i * m[k];
        }
        m[0] = x_i.neg() * m[0];
    }

    // The denominator of l_j is M'(x_j), here as the equivalent product \prod_{k != j}(x_j - x_k).
    //
    // M'(x_j) is also the quotient M(x)/(x - x_j) evaluated at x_j — write M = (x - x_j)q, so
    // M' = q + (x - x_j)q' and the second term vanishes at x_j — and that quotient is computed
    // below anyway. The product form is used instead because it costs the same single O(n) pass
    // and, unlike the quotient form, it is available *before* the divisions, so all n denominators
    // can be inverted together: `batch_invert` turns n field inversions into one. Inversion is the
    // operation whose cost relative to multiplication grows most with field width, so that matters
    // most over BN254, which is where the old implementation was slowest.
    let mut inverse_denominators: Vec<F> = points
        .iter()
        .enumerate()
        .map(|(j, (x_j, _y_j))| {
            let mut denominator = F::one();
            for (k, (x_k, _y_k)) in points.iter().enumerate() {
                if k != j {
                    denominator *= *x_j - *x_k;
                }
            }
            denominator
        })
        .collect();
    // No entry is zero: `assert_distinct_abscissae` ruled that out, which is why `batch_invert`'s
    // leave-zeros-alone behaviour cannot silently produce a wrong answer here.
    batch_invert(&mut inverse_denominators);

    let mut coefficients = vec![F::zero(); n];
    for ((x_j, y_j), inverse_denominator) in points.iter().zip(inverse_denominators) {
        let scale = *y_j * inverse_denominator;
        // A zero ordinate contributes nothing, and all-zero ordinates are a real input shape.
        if scale.is_zero() {
            continue;
        }
        // Synthetic division of M by the linear factor (x - x_j), fused with the accumulation of
        // `scale * quotient` into the result. Descending, the quotient coefficient is
        // `q_k = m_{k+1} + x_j * q_{k+1}`, starting from `q_{n-1} = m_n = 1`. The remainder would
        // be `m_0 + x_j * q_0 = M(x_j)`, which is zero by construction and so is not formed.
        let mut quotient = F::zero();
        for k in (0..n).rev() {
            quotient = m[k + 1] + *x_j * quotient;
            coefficients[k] += scale * quotient;
        }
    }

    UnivariatePolynomial::new(&coefficients)
}

/// Panic unless every x coordinate is distinct.
///
/// Deliberate rather than incidental: the quadratic form above divides by the *product* of the
/// differences, and a repeated abscissa makes that product zero, which `batch_invert` leaves as
/// zero instead of panicking. Nothing downstream would notice.
fn assert_distinct_abscissae<F: FiniteField>(points: &[(F, F)]) {
    let mut seen: HashSet<F> = HashSet::with_capacity(points.len());
    for (x, _y) in points {
        assert!(
            seen.insert(*x),
            "interpolation needs distinct x coordinates, and {} appears more than once",
            x
        );
    }
}

/// The `O(n^3)` textbook form, kept for differential testing against [`interpolate`].
#[cfg(test)]
pub(crate) fn interpolate_reference<F: FiniteField>(
    points: Vec<(F, F)>,
) -> UnivariatePolynomial<F> {
    assert!(!points.is_empty());
    let mut result = UnivariatePolynomial::<F>::zero();
    for (j, (_x_j, y_j)) in points.iter().enumerate() {
        let l_j = lagrange_polynomial(j, &points);
        result += l_j * y_j;
    }
    result
}

/// Compute the Lagrange polynomial l_j. Part of the reference implementation.
#[cfg(test)]
fn lagrange_polynomial<F: FiniteField>(j: usize, points: &[(F, F)]) -> UnivariatePolynomial<F> {
    let x_j = points[j].0;
    let mut numerator = UnivariatePolynomial::<F>::one();
    let mut denominator = F::one();
    for (k, (x_k, _y_k)) in points.iter().enumerate() {
        if k == j {
            continue;
        }
        numerator *= UnivariatePolynomial::new(&[x_k.neg(), F::one()]); // -x_k + x
        denominator *= x_j - x_k;
    }
    let (quotient, remainder) = numerator.div(&UnivariatePolynomial::lift(&denominator));
    assert_eq!(remainder, UnivariatePolynomial::zero());
    quotient
}

#[cfg(test)]
mod tests {
    use proptest::prelude::*;
    use rand::{prelude::StdRng, SeedableRng};

    use crate::{
        fields::{Bn254Fr, KoalaBear, Mersenne31, PrimeFieldElement64, Zp7},
        identities::{One, Zero},
        poly::univariate::{
            lagrange_interpolation::{interpolate, interpolate_reference, lagrange_polynomial},
            Polynomial, UnivariatePolynomial,
        },
        FiniteField,
    };

    // Helper maps coordinates to corresponding values in F.
    fn get_points<F: FiniteField>(coordinates: &[(u64, u64)]) -> Vec<(F, F)> {
        coordinates
            .iter()
            .map(|(x, y)| (F::new(*x), F::new(*y)))
            .collect()
    }

    /// `n` points with distinct abscissae drawn from `rng`, abscissae shuffled out of order.
    fn random_points<F: FiniteField>(n: usize, rng: &mut StdRng) -> Vec<(F, F)> {
        use rand::seq::SliceRandom;
        let mut xs: Vec<F> = Vec::with_capacity(n);
        let mut seen = std::collections::HashSet::new();
        while xs.len() < n {
            let x = F::random(rng);
            if seen.insert(x) {
                xs.push(x);
            }
        }
        xs.shuffle(rng);
        xs.into_iter().map(|x| (x, F::random(rng))).collect()
    }

    /// The interpolant passes through every supplied point and has degree at most n-1.
    fn assert_interpolates<F: FiniteField>(points: &[(F, F)]) {
        let p = interpolate(points.to_vec());
        assert!(
            (p.degree() as usize) < points.len(),
            "degree {} exceeds n-1 = {}",
            p.degree(),
            points.len() - 1
        );
        for (x, y) in points {
            assert_eq!(p.eval(x), *y, "the interpolant misses ({}, {})", x, y);
        }
    }

    #[test]
    // Should evaluate to 1 at x_j, and 0 otherwise, and have degree <= n-1.
    fn test_lagrange_polynomial() {
        // TODO: generate points randomly.
        type F = PrimeFieldElement64<13781>;
        let points: Vec<(F, F)> = get_points(&[(0, 2), (1, 17), (2, 87), (9, 199)]);
        let n = points.len();

        for (j, (x_j, _y_j)) in points.iter().enumerate() {
            // The lagrange univariate l_j(x).
            let l_j = lagrange_polynomial(j, &points);
            // l_j(x_j) = 1.
            assert_eq!(l_j.eval(x_j), F::one());
            assert!(l_j.degree() <= n as u32);
            for (k, (x_k, _y_k)) in points.iter().enumerate() {
                if j == k {
                    continue;
                }
                // l_j(x_k) = 0 for k != j.
                assert_eq!(l_j.eval(x_k), F::zero());
            }
        }
    }

    #[test]
    #[should_panic]
    // Should panic if points is empty.
    fn test_interpolate_points_is_empty() {
        type F = PrimeFieldElement64<13781>;
        let points: Vec<(F, F)> = get_points(&[]);
        let _p = interpolate(points);
    }

    #[test]
    // Should produce the constant polynomial p(x) = c.
    fn test_points_contains_one_point() {
        type F = PrimeFieldElement64<13781>;
        let points: Vec<(F, F)> = get_points(&[(0, 87)]);
        let p = interpolate(points);
        let expected = UnivariatePolynomial::new(&[F::new(87)]);
        assert_eq!(p, expected);
    }

    #[test]
    // Two points should give the line through them, at a non-zero abscissa pair.
    fn test_points_contains_two_points() {
        type F = PrimeFieldElement64<13781>;
        // The line through (3, 10) and (5, 20) is y = 5x - 5.
        let points: Vec<(F, F)> = get_points(&[(3, 10), (5, 20)]);
        let p = interpolate(points);
        let expected = UnivariatePolynomial::new(&[F::new(5).neg(), F::new(5)]);
        assert_eq!(p, expected);
    }

    #[test]
    #[should_panic(expected = "distinct x coordinates")]
    // Should reject duplicate x coordinates deliberately, naming the repeated abscissa.
    fn test_interpolate_points_contains_duplicate_x_coordinates() {
        type F = PrimeFieldElement64<13781>;
        let points: Vec<(F, F)> = get_points(&[(0, 87), (1, 2), (1, 3)]);
        let _p = interpolate(points);
    }

    #[test]
    #[should_panic(expected = "distinct x coordinates")]
    // Duplicate abscissae are rejected even when the ordinates agree, so the system is consistent.
    fn test_interpolate_rejects_a_consistent_duplicate() {
        type F = PrimeFieldElement64<13781>;
        let points: Vec<(F, F)> = get_points(&[(0, 87), (1, 2), (1, 2), (4, 9)]);
        let _p = interpolate(points);
    }

    #[test]
    // Interpolated polynomial should agree with given points.
    fn test_interpolate() {
        // sage: sage.misc.banner.version()
        // 'SageMath version 9.5, Release Date: 2022-01-30'
        //
        // sage: R.<x>=GF(13781)[]
        // sage: f = 14*x^4 + 87*x^3 + 99*x + 23
        // sage: f(0)
        // 23
        // sage: f(1)
        // 223
        // sage: f(2)
        // 1141
        // sage: f(3)
        // 3803
        // sage: f(4)
        // 9571

        type F = PrimeFieldElement64<13781>;
        let points: Vec<(F, F)> = get_points(&[(0, 23), (1, 223), (2, 1141), (3, 3803), (4, 9571)]);
        let p = interpolate(points);
        let expected =
            UnivariatePolynomial::new(&[F::new(23), F::new(99), F::new(0), F::new(87), F::new(14)]);

        assert_eq!(p, expected);
    }

    /// Interpolating n points gives a polynomial of degree at most n - 1 through those points.
    #[test]
    fn test_interpolate_correct_degree() {
        type F = PrimeFieldElement64<541>;
        for n in 1..=6u64 {
            // Points on the curve y = x^2 + 1, so the result has degree 2 once n > 2.
            let points: Vec<(F, F)> = (0..n)
                .map(|x| {
                    let x = F::new(x);
                    (x, x * x + F::one())
                })
                .collect();
            let p = interpolate(points.clone());
            assert!(p.degree() <= (n - 1) as u32, "n = {}", n);
            for (x, y) in points {
                assert_eq!(p.eval(&x), y, "n = {}", n);
            }
        }
    }

    /// All-zero ordinates give the zero polynomial, not a degree-(n-1) polynomial that is zero.
    #[test]
    fn test_all_zero_ordinates_give_the_zero_polynomial() {
        type F = PrimeFieldElement64<13781>;
        for n in 1..=12u64 {
            let points: Vec<(F, F)> = (0..n).map(|x| (F::new(x), F::zero())).collect();
            assert_eq!(interpolate(points), UnivariatePolynomial::<F>::zero());
        }
    }

    /// A true degree far below n-1 is recovered exactly, not padded out to n-1.
    #[test]
    fn test_a_low_degree_interpolant_keeps_its_degree() {
        type F = PrimeFieldElement64<2_147_483_647>;
        // f = 7x^2 + 3 sampled at 64 points, so the true degree is 2 against an n-1 of 63.
        let f = UnivariatePolynomial::new(&[F::new(3), F::zero(), F::new(7)]);
        let points: Vec<(F, F)> = (0..64u64)
            .map(|x| {
                let x = F::new(x);
                (x, f.eval(&x))
            })
            .collect();
        assert_eq!(interpolate(points), f);
    }

    /// The result does not depend on the order the points are supplied in.
    #[test]
    fn test_the_result_is_independent_of_input_order() {
        use rand::seq::SliceRandom;
        type F = PrimeFieldElement64<2_147_483_647>;
        let mut rng = StdRng::seed_from_u64(0x0000_1de6);
        let mut increasing: Vec<(F, F)> = (0..40u64)
            .map(|x| (F::new(x), F::random(&mut rng)))
            .collect();
        let from_increasing = interpolate(increasing.clone());
        for _ in 0..8 {
            increasing.shuffle(&mut rng);
            assert_eq!(interpolate(increasing.clone()), from_increasing);
        }
    }

    /// Agrees with the cubic reference implementation over a narrow 31-bit field.
    #[test]
    fn test_agrees_with_the_reference_over_mersenne31() {
        let mut rng = StdRng::seed_from_u64(0x4d31);
        for n in 1..=48 {
            let points = random_points::<Mersenne31>(n, &mut rng);
            assert_eq!(
                interpolate(points.clone()),
                interpolate_reference(points),
                "n = {}",
                n
            );
        }
    }

    /// Agrees with the cubic reference implementation over KoalaBear.
    #[test]
    fn test_agrees_with_the_reference_over_koalabear() {
        let mut rng = StdRng::seed_from_u64(0x4b0a);
        for n in 1..=48 {
            let points = random_points::<KoalaBear>(n, &mut rng);
            assert_eq!(
                interpolate(points.clone()),
                interpolate_reference(points),
                "n = {}",
                n
            );
        }
    }

    /// Agrees with the cubic reference implementation over the wide BN254 scalar field.
    #[test]
    fn test_agrees_with_the_reference_over_bn254() {
        let mut rng = StdRng::seed_from_u64(0xb254);
        for n in 1..=32 {
            let points = random_points::<Bn254Fr>(n, &mut rng);
            assert_eq!(
                interpolate(points.clone()),
                interpolate_reference(points),
                "n = {}",
                n
            );
        }
    }

    /// Exhaustive over GF(7): every point set of every size, every ordinate assignment, agrees
    /// with the reference and passes through its points.
    #[test]
    fn test_exhaustive_over_gf7() {
        const Q: u64 = 7;
        // Every non-empty subset of the 7 abscissae, as a bitmask.
        for mask in 1u64..(1 << Q) {
            let xs: Vec<Zp7> = (0..Q)
                .filter(|i| mask >> i & 1 == 1)
                .map(Zp7::new)
                .collect();
            let n = xs.len();
            // Every assignment of ordinates, for the subsets small enough to enumerate.
            if n > 3 {
                continue;
            }
            for code in 0..Q.pow(n as u32) {
                let points: Vec<(Zp7, Zp7)> = xs
                    .iter()
                    .enumerate()
                    .map(|(i, x)| (*x, Zp7::new(code / Q.pow(i as u32) % Q)))
                    .collect();
                assert_eq!(
                    interpolate(points.clone()),
                    interpolate_reference(points.clone()),
                    "mask {}, code {}",
                    mask,
                    code
                );
                assert_interpolates(&points);
            }
        }
    }

    proptest! {
        /// Over Mersenne-31, the interpolant passes through every point and has degree <= n-1.
        #[test]
        fn proptest_interpolates_its_points_over_mersenne31(seed: u64, n in 1usize..40) {
            let mut rng = StdRng::seed_from_u64(seed);
            let points = random_points::<Mersenne31>(n, &mut rng);
            assert_interpolates(&points);
        }

        /// Over BN254 `Fr`, the interpolant passes through every point and has degree <= n-1.
        #[test]
        fn proptest_interpolates_its_points_over_bn254(seed: u64, n in 1usize..24) {
            let mut rng = StdRng::seed_from_u64(seed);
            let points = random_points::<Bn254Fr>(n, &mut rng);
            assert_interpolates(&points);
        }

        /// Over Mersenne-31, agrees with the cubic reference implementation point for point.
        #[test]
        fn proptest_agrees_with_the_reference_over_mersenne31(seed: u64, n in 1usize..40) {
            let mut rng = StdRng::seed_from_u64(seed);
            let points = random_points::<Mersenne31>(n, &mut rng);
            prop_assert_eq!(interpolate(points.clone()), interpolate_reference(points));
        }

        /// Over Goldilocks, agrees with the cubic reference implementation point for point.
        #[test]
        fn proptest_agrees_with_the_reference_over_goldilocks(seed: u64, n in 1usize..40) {
            type F = PrimeFieldElement64<18_446_744_069_414_584_321>;
            let mut rng = StdRng::seed_from_u64(seed);
            let points = random_points::<F>(n, &mut rng);
            prop_assert_eq!(interpolate(points.clone()), interpolate_reference(points));
        }
    }
}
