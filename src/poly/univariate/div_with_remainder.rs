//! Polynomial division with remainder.
//!
//! Both `Div` and `Rem` on `DensePolynomial` are one call to this and a projection, so a caller
//! that wants the quotient *and* the remainder must come here rather than write `f / g` and
//! `f % g`, which would run the division twice.
//!
//! Long division over a coefficient array. Each step subtracts `c * x^e * divisor` from the
//! working remainder in place, which is `deg(divisor) + 1` multiplications, so dividing degree
//! `2d` by degree `d` costs `d^2` of them.
//!
//! It is written out rather than expressed with the polynomial operators because doing the latter
//! made it **cubic**. Forming `c * x^e` as a polynomial and multiplying by the divisor ran the
//! schoolbook product over all `e + 1` coefficients of a term that has one, so a step cost
//! `(e + 1) * (deg(divisor) + 1)` rather than `deg(divisor) + 1`, and the sum over e was
//! `d^3 / 2`. Measured at exponent 2.99 by `examples/univariate_scaling.rs` against a predicted
//! 2, which is how it was found: every caller of `pow_mod_limbs` reduces once per squaring, so
//! root finding over a 254-bit field paid `254 * d^3 / 2`.

use crate::{
    poly::univariate::{Polynomial, UnivariatePolynomial},
    FiniteField,
};

/// Computes dividend = quotient * divisor + remainder.
///
/// # Panics
/// Panics if `divisor` is the zero polynomial.
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

    let divisor_degree = divisor.degree() as usize;
    if dividend.is_zero() || (dividend.degree() as usize) < divisor_degree {
        // Nothing to reduce: the dividend is already the remainder.
        return (UnivariatePolynomial::zero(), dividend.clone());
    }

    // One inversion for the whole division rather than one division per step.
    let divisor_coefficients = divisor.coefficients();
    let leading_inverse = divisor_coefficients[divisor_degree].inverse();

    let mut remainder = dividend.coefficients().to_vec();
    let mut quotient = vec![F::zero(); remainder.len() - divisor_degree];

    // High-order term first. After each step `remainder[exponent + divisor_degree]` is exactly
    // zero, so the next leading coefficient is the next one down.
    for exponent in (0..quotient.len()).rev() {
        let c = remainder[exponent + divisor_degree] * leading_inverse;
        if c.is_zero() {
            continue;
        }
        quotient[exponent] = c;
        for (i, b) in divisor_coefficients.iter().enumerate() {
            remainder[exponent + i] -= c * *b;
        }
    }

    (
        UnivariatePolynomial::new(&quotient),
        UnivariatePolynomial::new(&remainder),
    )
}

#[cfg(test)]
mod tests {
    use crate::poly::univariate::PolynomialParams;
    use proptest::prelude::*;
    use rand::SeedableRng;

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

    /// Division at a degree the cubic implementation could not reach.
    ///
    /// The regression guard for the cost of this function, and the closest practical one: the
    /// quantity that changed is the number of field multiplications, which nothing here can
    /// count, and a wall-clock assertion in the test suite would be flaky. What makes this a
    /// guard is the size. Long division of degree 2d by degree d is `d^2` multiplications; the
    /// implementation this replaced was `d^3 / 2`, which at d = 3000 is 1.35e10 and does not
    /// finish in a test run. The measured exponent column of
    /// `cargo run --release --example univariate_scaling` is the direct evidence.
    #[test]
    fn test_division_at_a_degree_the_cubic_implementation_could_not_reach() {
        type F = Zp7;
        type P = DensePolynomial<F>;
        let mut rng = rand::rngs::StdRng::seed_from_u64(20261105);

        let divisor = P::rand(3_000, &mut rng);
        let dividend = P::rand(6_000, &mut rng);
        let (quotient, remainder) = div_with_remainder(&dividend, &divisor);

        assert_eq!(quotient.degree(), 3_000);
        assert!(remainder.is_zero() || remainder.degree() < divisor.degree());
        assert_eq!(&(&quotient * &divisor) + &remainder, dividend);
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
