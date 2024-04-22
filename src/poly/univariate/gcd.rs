//! Greatest common divisor of two univariate polynomials over a field F.
//!
//! The greatest common divisor of two polynomials f(x) and g(x) over a field F, denoted gcd(f, g),
//! is a highest-degree polynomial d(x) that divides both f(x) and g(x). The gcd is unique up to
//! multiplication by a nonzero constant in F. Typically, gcd(f, g) is defined to be the unique
//! monic polynomial d(x) such that d(x) divides both f(x) and g(x).

use crate::{FiniteField, Polynomial, UnivariatePolynomial};

/// The monic greatest common divisor of two polynomials.
pub fn gcd<F: FiniteField>(
    a: &UnivariatePolynomial<F>,
    b: &UnivariatePolynomial<F>,
) -> UnivariatePolynomial<F> {
    let mut f = a.clone();
    let mut g = b.clone();

    // Euclidean algorithm
    while !g.is_zero() {
        let (_q, remainder) = f.div(&g);
        f = g;
        g = remainder;
    }

    // "The" GCD is chosen to be monic (i.e. the leading coefficient is 1).
    make_monic(&f)
}

/// Scale a polynomial to be monic.
fn make_monic<F: FiniteField>(f: &UnivariatePolynomial<F>) -> UnivariatePolynomial<F> {
    let leading_coefficient = f.coefficients().last().unwrap();
    if !leading_coefficient.is_zero() && !leading_coefficient.is_one() {
        f.scale(&leading_coefficient.inverse())
    } else {
        f.clone()
    }
}

#[cfg(test)]
mod tests {
    use proptest::{prelude::*, proptest};

    use crate::{
        fields::Zp1091,
        poly::univariate::gcd::{gcd, make_monic},
        One, Polynomial, UnivariatePolynomial,
    };

    #[test]
    /// gcd(0, 0) = 0
    fn test_gcd_of_zero_and_zero() {
        let zero = UnivariatePolynomial::<Zp1091>::zero();
        assert_eq!(gcd(&zero, &zero), zero);
    }

    proptest! {

        #[test]
        /// gcd(a,b) is a monic polynomial (i.e. the leading coefficient is 1).
        fn test_gcd_is_monic(
            a in ((0..=100usize).prop_flat_map(|d| any_with::<UnivariatePolynomial<Zp1091>>(d))),
            b in ((0..=100usize).prop_flat_map(|d| any_with::<UnivariatePolynomial<Zp1091>>(d)))) {
            let gcd = gcd(&a, &b);
            prop_assert_eq!(gcd.coefficients().last().unwrap(), &Zp1091::one());
        }

        #[test]
        /// gcd(a, b) divides a and b.
        fn test_gcd_divides_a_and_b(
            a in ((0..=100usize).prop_flat_map(|d| any_with::<UnivariatePolynomial<Zp1091>>(d))),
            b in ((0..=100usize).prop_flat_map(|d| any_with::<UnivariatePolynomial<Zp1091>>(d)))) {
            let gcd = gcd(&a, &b);
            prop_assert_eq!(a.div(&gcd).1, UnivariatePolynomial::<Zp1091>::zero());
            prop_assert_eq!(b.div(&gcd).1, UnivariatePolynomial::<Zp1091>::zero());
        }

        #[test]
        /// gcd(0, a) = gcd(a, 0) = a, up to a constant factor.
        fn test_gcd_with_zero(
            a in ((0..=100usize).prop_flat_map(|d| any_with::<UnivariatePolynomial<Zp1091>>(d)))) {
            let zero = UnivariatePolynomial::<Zp1091>::zero();
            let a_monic = make_monic(&a);
            prop_assert_eq!(gcd(&zero, &a), a_monic.clone());
            prop_assert_eq!(gcd(&a, &zero), a_monic.clone());
        }

        #[test]
        /// gcd(1, a) = gcd(a, 1) = 1
        fn test_gcd_with_one(a: UnivariatePolynomial<Zp1091>) {
            let one = UnivariatePolynomial::<Zp1091>::one();
            prop_assert_eq!(gcd(&one, &a), one.clone());
            prop_assert_eq!(gcd(&a, &one), one);
        }

        #[test]
        /// gcd(a, b) = gcd(b, a)
        fn test_gcd_is_symmetric(
            a in ((0..=100usize).prop_flat_map(|d| any_with::<UnivariatePolynomial<Zp1091>>(d))),
            b in ((0..=100usize).prop_flat_map(|d| any_with::<UnivariatePolynomial<Zp1091>>(d)))) {
            prop_assert_eq!(gcd(&a, &b), gcd(&b, &a));
        }

        #[test]
        // gcd(a,b)= gcd(a,b+ra) for any polynomial r.
        fn test_gcd_is_linear_combination(
            a in ((0..=100usize).prop_flat_map(|d| any_with::<UnivariatePolynomial<Zp1091>>(d))),
            b in ((0..=100usize).prop_flat_map(|d| any_with::<UnivariatePolynomial<Zp1091>>(d))),
            r in ((0..=100usize).prop_flat_map(|d| any_with::<UnivariatePolynomial<Zp1091>>(d)))) {
            let gcd_ab = gcd(&a, &b);
            let gcd_a_b_plus_ra = gcd(&a, &(b + &a * &r));
            prop_assert_eq!(gcd_ab, gcd_a_b_plus_ra);
        }
    }
}
