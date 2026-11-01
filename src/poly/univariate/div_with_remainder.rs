//! Polynomial division with remainder.

use crate::{
    poly::univariate::{Polynomial, UnivariatePolynomial},
    FiniteField,
};

/// Computes dividend = quotient * divisor + remainder.
pub fn div_with_remainder<F: FiniteField>(
    dividend: &UnivariatePolynomial<F>,
    divisor: &UnivariatePolynomial<F>,
) -> (UnivariatePolynomial<F>, UnivariatePolynomial<F>) {
    // TODO: return a Result instead of panicking.
    assert!(
        !divisor.is_zero(),
        "Divisor must not be zero: {:?}",
        divisor
    );
    let mut quotient_coefficients = vec![F::zero(); (dividend.degree() + 1) as usize];
    let mut remainder = dividend.clone();

    // Reduce the remainder until it has degree less than the divisor.
    while !remainder.is_zero() && remainder.degree() >= divisor.degree() {
        let exponent = (remainder.degree() - divisor.degree()) as usize;
        let c: F = leading_coefficient(&remainder) / &leading_coefficient(divisor);
        // The next term of the quotient is c*x^exponent.
        quotient_coefficients[exponent] = c;

        // 0 + 0x + ... + c*x^exponent
        let mut coefficients = vec![F::zero(); exponent + 1];
        coefficients[exponent] = c;
        remainder -= UnivariatePolynomial::new(&coefficients) * divisor;
    }

    (UnivariatePolynomial::new(&quotient_coefficients), remainder)
}

// Coefficient of highest-order term.
fn leading_coefficient<F: FiniteField>(p: &UnivariatePolynomial<F>) -> F {
    *p.coefficients().last().unwrap_or(&F::zero())
}

#[cfg(test)]
mod tests {
    use crate::poly::univariate::PolynomialParams;
    use proptest::prelude::*;

    use crate::{
        fields::{PrimeFieldElement64, Zp7},
        identities::{One, Zero},
        poly::univariate::{
            dense_polynomial::DensePolynomial, div_with_remainder::div_with_remainder, Polynomial,
            UnivariatePolynomial,
        },
        FiniteField,
    };

    #[test]
    #[should_panic]
    fn divide_by_zero_should_panic() {
        type F = PrimeFieldElement64<541>;
        type P = DensePolynomial<F>;
        let p = P::try_from("x^2 + 1").unwrap();
        let (_q, _r) = div_with_remainder(&p, &P::zero());
    }

    proptest! {
        #[test]
        // Dividing by 1 should return the dividend with remainder zero.
        fn test_divide_by_1(
            p in ((0..=100usize).prop_map(PolynomialParams::from).prop_flat_map(any_with::<DensePolynomial<Zp7>>))) {
            let one = DensePolynomial::<Zp7>::one();
            let (q, r) = div_with_remainder(&p, &one);
            assert_eq!(q, p);
            assert_eq!(r, DensePolynomial::<Zp7>::zero());
        }
    }

    #[test]
    // For f = g*q + r, if deg(f) < deg(g), then q = 0 and r = f.
    fn test_divide_quotient_is_zero() {
        type F = PrimeFieldElement64<7>;
        let zero = UnivariatePolynomial::zero();

        // 1 + x
        let dividend = UnivariatePolynomial::new(&[F::one(), F::one()]);

        // x^2
        let divisor = UnivariatePolynomial::new(&[F::zero(), F::zero(), F::one()]);
        let (quotient, remainder) = div_with_remainder(&dividend, &divisor);
        assert_eq!(quotient, zero);
        assert_eq!(remainder, dividend);
    }

    /// For f = g*q + r with deg(f) >= deg(g), the quotient has degree deg(f) - deg(g).
    #[test]
    fn test_degree_of_quotient() {
        type F = Zp7;
        type P = DensePolynomial<F>;

        let dividend = P::new(&[F::new(1), F::new(2), F::new(3), F::new(4), F::new(5)]);
        for divisor in [
            P::new(&[F::new(3)]),                       // degree 0
            P::new(&[F::new(1), F::new(1)]),            // degree 1
            P::new(&[F::new(2), F::new(0), F::new(6)]), // degree 2
        ] {
            let (quotient, remainder) = div_with_remainder(&dividend, &divisor);
            assert_eq!(
                quotient.degree(),
                dividend.degree() - divisor.degree(),
                "divisor {:?}",
                divisor
            );
            // The remainder's degree stays strictly below the divisor's, unless it is zero.
            if !remainder.is_zero() {
                assert!(remainder.degree() < divisor.degree() || divisor.degree() == 0);
            }
            assert_eq!(&(&quotient * &divisor) + &remainder, dividend);
        }
    }

    proptest! {
        #[test]
        fn test_recover_dividend(
            p in ((0..=100usize).prop_map(PolynomialParams::from).prop_flat_map(any_with::<DensePolynomial<Zp7>>)),
            q in ((0..=100usize).prop_map(PolynomialParams::from).prop_flat_map(any_with::<DensePolynomial<Zp7>>)),
        ) {
            if q.is_zero() {
                return Ok(())
            }
            let (quotient, remainder) = div_with_remainder(&p, &q);
            let recovered = (quotient * q) + remainder;
            prop_assert_eq!(p, recovered)
        }
    }
}
