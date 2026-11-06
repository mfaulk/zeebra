//! Greatest common divisor and least common multiple of two univariate polynomials over a field F.
//!
//! The greatest common divisor of two polynomials f(x) and g(x) over a field F, denoted gcd(f, g),
//! is a highest-degree polynomial d(x) that divides both f(x) and g(x). The gcd is unique up to
//! multiplication by a nonzero constant in F. Typically, gcd(f, g) is defined to be the unique
//! monic polynomial d(x) such that d(x) divides both f(x) and g(x). The least common multiple is
//! normalized the same way, and is `f * g / gcd(f, g)`.
//!
//! The Euclidean algorithm below is classical, so it is `O(d^2)` in the division it drives.
//! Half-GCD would be `O(M(d) log d)` and is not written: `M` at the `Mul` operator is still
//! schoolbook, which makes the recursive algorithm the slower one. See §4.5 of
//! `docs/research/fast-univariate.md`.

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
        let remainder = &f % &g;
        f = g;
        g = remainder;
    }

    // "The" GCD is chosen to be monic (i.e. the leading coefficient is 1).
    make_monic(&f)
}

/// The monic least common multiple of two polynomials, or zero if either is zero.
///
/// `a * b / gcd(a, b)`, dividing before the normalization so that the product is formed once.
pub fn lcm<F: FiniteField>(
    a: &UnivariatePolynomial<F>,
    b: &UnivariatePolynomial<F>,
) -> UnivariatePolynomial<F> {
    // gcd(0, b) is b, so the quotient below would be well defined and equal to zero — but only
    // when b is nonzero too, and gcd(0, 0) is the zero polynomial the division would panic on.
    if a.is_zero() || b.is_zero() {
        return UnivariatePolynomial::zero();
    }

    make_monic(&(&(a * b) / &gcd(a, b)))
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
    use crate::poly::univariate::PolynomialParams;
    use proptest::{prelude::*, proptest};

    use crate::{
        fields::Zp1091,
        poly::univariate::gcd::{gcd, lcm, make_monic},
        One, Polynomial, UnivariatePolynomial,
    };

    #[test]
    /// gcd(0, 0) = 0
    fn test_gcd_of_zero_and_zero() {
        let zero = UnivariatePolynomial::<Zp1091>::zero();
        assert_eq!(gcd(&zero, &zero), zero);
    }

    #[test]
    /// lcm(0, 0) = 0
    fn test_lcm_of_zero_and_zero() {
        let zero = UnivariatePolynomial::<Zp1091>::zero();
        assert_eq!(lcm(&zero, &zero), zero);
    }

    proptest! {

        #[test]
        /// gcd(a,b) is a monic polynomial (i.e. the leading coefficient is 1).
        fn test_gcd_is_monic(
            a in ((0..=100usize).prop_map(PolynomialParams::from).prop_flat_map(any_with::<UnivariatePolynomial<Zp1091>>)),
            b in ((0..=100usize).prop_map(PolynomialParams::from).prop_flat_map(any_with::<UnivariatePolynomial<Zp1091>>))) {
            let gcd = gcd(&a, &b);
            prop_assert_eq!(gcd.coefficients().last().unwrap(), &Zp1091::one());
        }

        #[test]
        /// gcd(a, b) divides a and b.
        fn test_gcd_divides_a_and_b(
            a in ((0..=100usize).prop_map(PolynomialParams::from).prop_flat_map(any_with::<UnivariatePolynomial<Zp1091>>)),
            b in ((0..=100usize).prop_map(PolynomialParams::from).prop_flat_map(any_with::<UnivariatePolynomial<Zp1091>>))) {
            let gcd = gcd(&a, &b);
            prop_assert_eq!(&a % &gcd, UnivariatePolynomial::<Zp1091>::zero());
            prop_assert_eq!(&b % &gcd, UnivariatePolynomial::<Zp1091>::zero());
        }

        #[test]
        /// gcd(0, a) = gcd(a, 0) = a, up to a constant factor.
        fn test_gcd_with_zero(
            a in ((0..=100usize).prop_map(PolynomialParams::from).prop_flat_map(any_with::<UnivariatePolynomial<Zp1091>>))) {
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
            a in ((0..=100usize).prop_map(PolynomialParams::from).prop_flat_map(any_with::<UnivariatePolynomial<Zp1091>>)),
            b in ((0..=100usize).prop_map(PolynomialParams::from).prop_flat_map(any_with::<UnivariatePolynomial<Zp1091>>))) {
            prop_assert_eq!(gcd(&a, &b), gcd(&b, &a));
        }

        #[test]
        /// lcm(a, b) is monic whenever it is nonzero.
        fn test_lcm_is_monic(
            a in ((0..=50usize).prop_map(PolynomialParams::from).prop_flat_map(any_with::<UnivariatePolynomial<Zp1091>>)),
            b in ((0..=50usize).prop_map(PolynomialParams::from).prop_flat_map(any_with::<UnivariatePolynomial<Zp1091>>))) {
            let lcm = lcm(&a, &b);
            if !lcm.is_zero() {
                prop_assert_eq!(lcm.coefficients().last().unwrap(), &Zp1091::one());
            }
        }

        #[test]
        /// a and b both divide lcm(a, b).
        fn test_lcm_is_divisible_by_a_and_b(
            a in ((1..=50usize).prop_map(PolynomialParams::from).prop_flat_map(any_with::<UnivariatePolynomial<Zp1091>>)),
            b in ((1..=50usize).prop_map(PolynomialParams::from).prop_flat_map(any_with::<UnivariatePolynomial<Zp1091>>))) {
            if a.is_zero() || b.is_zero() {
                return Ok(());
            }
            let lcm = lcm(&a, &b);
            prop_assert!((&lcm % &a).is_zero());
            prop_assert!((&lcm % &b).is_zero());
        }

        #[test]
        /// lcm(a, b) * gcd(a, b) = a * b, up to the monic normalization of each side.
        fn test_lcm_times_gcd_is_the_product(
            a in ((1..=50usize).prop_map(PolynomialParams::from).prop_flat_map(any_with::<UnivariatePolynomial<Zp1091>>)),
            b in ((1..=50usize).prop_map(PolynomialParams::from).prop_flat_map(any_with::<UnivariatePolynomial<Zp1091>>))) {
            if a.is_zero() || b.is_zero() {
                return Ok(());
            }
            prop_assert_eq!(&lcm(&a, &b) * &gcd(&a, &b), make_monic(&(&a * &b)));
        }

        #[test]
        /// lcm(a, a) = a, up to a constant factor.
        fn test_lcm_of_a_with_itself(
            a in ((1..=50usize).prop_map(PolynomialParams::from).prop_flat_map(any_with::<UnivariatePolynomial<Zp1091>>))) {
            if a.is_zero() {
                return Ok(());
            }
            prop_assert_eq!(lcm(&a, &a), make_monic(&a));
        }

        #[test]
        /// lcm(1, a) = lcm(a, 1) = a, up to a constant factor.
        fn test_lcm_with_one(
            a in ((1..=50usize).prop_map(PolynomialParams::from).prop_flat_map(any_with::<UnivariatePolynomial<Zp1091>>))) {
            if a.is_zero() {
                return Ok(());
            }
            let one = UnivariatePolynomial::<Zp1091>::one();
            let a_monic = make_monic(&a);
            prop_assert_eq!(lcm(&one, &a), a_monic.clone());
            prop_assert_eq!(lcm(&a, &one), a_monic);
        }

        #[test]
        /// lcm(0, a) = lcm(a, 0) = 0: zero has no nonzero multiple in common with anything.
        fn test_lcm_with_zero(
            a in ((0..=50usize).prop_map(PolynomialParams::from).prop_flat_map(any_with::<UnivariatePolynomial<Zp1091>>))) {
            let zero = UnivariatePolynomial::<Zp1091>::zero();
            prop_assert_eq!(lcm(&zero, &a), zero.clone());
            prop_assert_eq!(lcm(&a, &zero), zero);
        }

        #[test]
        // gcd(a,b)= gcd(a,b+ra) for any polynomial r.
        fn test_gcd_is_linear_combination(
            a in ((0..=100usize).prop_map(PolynomialParams::from).prop_flat_map(any_with::<UnivariatePolynomial<Zp1091>>)),
            b in ((0..=100usize).prop_map(PolynomialParams::from).prop_flat_map(any_with::<UnivariatePolynomial<Zp1091>>)),
            r in ((0..=100usize).prop_map(PolynomialParams::from).prop_flat_map(any_with::<UnivariatePolynomial<Zp1091>>))) {
            let gcd_ab = gcd(&a, &b);
            let gcd_a_b_plus_ra = gcd(&a, &(b + &a * &r));
            prop_assert_eq!(gcd_ab, gcd_a_b_plus_ra);
        }
    }
}
