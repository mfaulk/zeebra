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

use crate::{
    poly::univariate::{Polynomial, UnivariatePolynomial},
    FiniteField,
};

/// Interpolate n points into a polynomial of degree n-1.
///
/// # Arguments
/// * `points` - Collection of (x,y) points.
pub fn interpolate<F: FiniteField>(points: Vec<(F, F)>) -> UnivariatePolynomial<F> {
    assert!(!points.is_empty());
    let mut result = UnivariatePolynomial::<F>::zero();
    for (j, (_x_j, y_j)) in points.iter().enumerate() {
        let l_j = lagrange_polynomial(j, &points);
        result = result + l_j * y_j;
    }
    result
}

/// Compute the Lagrange polynomial l_j.
fn lagrange_polynomial<F: FiniteField>(j: usize, points: &[(F, F)]) -> UnivariatePolynomial<F> {
    let x_j = points[j].0;
    let mut numerator = UnivariatePolynomial::<F>::one();
    let mut denominator = F::one();
    for (k, (x_k, _y_k)) in points.iter().enumerate() {
        if k == j {
            continue;
        }
        numerator = numerator * UnivariatePolynomial::new(&[x_k.neg(), F::one()]); // -x_k + x
        denominator = denominator * (x_j - x_k);
    }
    let (quotient, remainder) = numerator.div(&UnivariatePolynomial::lift(&denominator));
    assert_eq!(remainder, UnivariatePolynomial::zero());
    quotient
}

#[cfg(test)]
mod tests {
    use crate::{
        fields::PrimeFieldElement64,
        identities::{One, Zero},
        poly::univariate::{
            lagrange_interpolation::{interpolate, lagrange_polynomial},
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
    #[should_panic]
    // Should panic if points contains points with duplicate x coordinate.
    fn test_interpolate_points_contains_duplicate_x_coordinates() {
        type F = PrimeFieldElement64<13781>;
        let points: Vec<(F, F)> = get_points(&[(0, 87), (1, 2), (1, 3)]);
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

    #[test]
    #[ignore]
    // Should produce a polynomial of the correct degree <= n-1.
    fn test_interpolate_correct_degree() {
        todo!()
    }
}
