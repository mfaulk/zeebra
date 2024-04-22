//! Arithmetic operations for sparse multivariate polynomials.

use std::{ops, ops::Neg};

use crate::{impl_add_variants, impl_mul_variants, impl_sub_variants};

use crate::{
    poly::{multivariate::sparse_multivariate_polynomial::SparseMultiPoly, MonomialOrder},
    FiniteField, Monomial,
};

/// Neg: -p
impl<const N: usize, F: FiniteField> Neg for SparseMultiPoly<N, F> {
    type Output = SparseMultiPoly<N, F>;

    fn neg(self) -> Self::Output {
        let terms: Vec<(Monomial<N>, F)> = self
            .terms
            .iter()
            .map(|(monomial, c)| (*monomial, c.neg()))
            .collect();

        SparseMultiPoly::new(&terms)
    }
}

/// Add: &p + &q
impl<const N: usize, F: FiniteField> ops::Add<&SparseMultiPoly<N, F>> for &SparseMultiPoly<N, F> {
    type Output = SparseMultiPoly<N, F>;

    fn add(self, other: &SparseMultiPoly<N, F>) -> Self::Output {
        let terms: Vec<(Monomial<N>, F)> = self
            .terms
            .iter()
            .chain(other.terms.iter())
            .map(|(monomial, c)| (*monomial, *c))
            .collect();

        SparseMultiPoly::new(&terms)
    }
}

impl_add_variants!([const N: usize, F: FiniteField], SparseMultiPoly<N, F>);

/// Mul: &p * &q
impl<const N: usize, F: FiniteField> ops::Mul<&SparseMultiPoly<N, F>> for &SparseMultiPoly<N, F> {
    type Output = SparseMultiPoly<N, F>;

    fn mul(self, other: &SparseMultiPoly<N, F>) -> Self::Output {
        let mut terms: Vec<(Monomial<N>, F)> = Default::default();
        for (monomial_a, coefficient_a) in self.terms.iter() {
            for (monomial_b, coefficient_b) in &other.terms {
                terms.push((monomial_a * monomial_b, *coefficient_a * *coefficient_b));
            }
        }

        SparseMultiPoly::new(&terms)
    }
}

impl_mul_variants!([const N: usize, F: FiniteField], SparseMultiPoly<N, F>);

/// Sub: &p - &q
impl<const N: usize, F: FiniteField> ops::Sub<&SparseMultiPoly<N, F>> for &SparseMultiPoly<N, F> {
    type Output = SparseMultiPoly<N, F>;

    fn sub(self, other: &SparseMultiPoly<N, F>) -> Self::Output {
        let terms: Vec<(Monomial<N>, F)> = self
            .terms
            .iter()
            .map(|(monomial, c)| (*monomial, *c))
            .chain(other.terms.iter().map(|(monomial, c)| (*monomial, c.neg())))
            .collect();

        SparseMultiPoly::new(&terms)
    }
}

impl_sub_variants!([const N: usize, F: FiniteField], SparseMultiPoly<N, F>);

impl<const N: usize, F: FiniteField> SparseMultiPoly<N, F> {
    /// Divides `self` by `divisor` and returns the quotient and remainder.
    pub fn div_rem(&self, divisor: &Self, order: MonomialOrder) -> (Self, Self) {
        let mut remainder = self.clone();
        let mut quotient = SparseMultiPoly::zero();
        while !remainder.terms.is_empty() {
            let lead_term = remainder.leading_term(order);
            match lead_term.checked_div(&divisor.leading_term(order)) {
                Some(q) => {
                    let q: SparseMultiPoly<N, F> = q.into();
                    remainder -= &q * divisor;
                    quotient += q;
                }
                None => {
                    return (quotient, remainder);
                }
            }
        }
        (quotient, remainder)
    }

    /// Divides `self` by each of the `divisors` and returns the quotients and remainder.
    ///
    /// # Arguments
    /// * `divisors` - Nonzero divisors f_0, f_1, ..., f_{k-1}.
    /// * `order` - The monomial order.
    ///
    /// # Returns
    ///  f = q_0 * f_0 + q_1 * f_1 + ... + q_{k-1} * f_{k-1} + r, such that no monomial in r
    /// is divisible by the leading term of any divisor. The result is not necessarily unique,
    /// and may depend on the order of the divisors.
    pub fn multi_div_rem(&self, divisors: &[Self], order: MonomialOrder) -> (Vec<Self>, Self) {
        assert!(!divisors.is_empty());
        assert!(divisors.iter().any(|d| !d.is_zero()));

        // Working copy of self.
        let mut p = self.clone();

        // Remainder
        let mut r = SparseMultiPoly::zero();

        // Quotients q_0, q_1, ..., q_{k-1}
        let mut quotients = vec![SparseMultiPoly::zero(); divisors.len()];

        while !p.is_zero() {
            // True if the leading term of p is divisible by the leading term of some divisor[i].
            let mut divisor_found = false;
            for (i, divisor) in divisors.iter().enumerate() {
                // x = lt(p) / lt(divisor_i)
                if let Some(x) = p
                    .leading_term(order)
                    .checked_div(&divisor.leading_term(order))
                {
                    quotients[i] += SparseMultiPoly::from(&x);
                    p -= &x.into() * divisor;
                    divisor_found = true;
                    break;
                }
            }
            if !divisor_found {
                r += SparseMultiPoly::from(p.leading_term(order));
                p -= SparseMultiPoly::from(p.leading_term(order));
            }
        }

        (quotients, r)
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        fields::PrimeFieldElement64,
        poly::{multivariate::sparse_multivariate_polynomial::SparseMultiPoly, MonomialOrder},
        FiniteField, Monomial,
    };

    // TODO: Proptest that Zero is the additive identity.

    // TODO: test Neg

    #[test]
    // Zero is the additive identity.
    fn test_add_zero_is_additive_identity() {
        type F = PrimeFieldElement64<337>;

        // 3xy + 14x^3
        let terms: Vec<_> = vec![
            (Monomial::<2>::new(&[1, 1]), F::new(3)),
            (Monomial::<2>::new(&[3, 0]), F::new(14)),
        ];
        let p = SparseMultiPoly::new(&terms);
        let zero = SparseMultiPoly::zero();

        assert_eq!(&p + &zero, p);
        assert_eq!(&zero + &p, p);
    }

    #[test]
    fn test_add() {
        type F = PrimeFieldElement64<337>;

        // 3xy + 14x^3 + 5x^11*y^2
        let a = SparseMultiPoly::new(&[
            (Monomial::<2>::new(&[1, 1]), F::new(3)),
            (Monomial::<2>::new(&[3, 0]), F::new(14)),
            (Monomial::<2>::new(&[11, 2]), F::new(5)),
        ]);

        // 4 + x + y + 22xy
        let b = SparseMultiPoly::new(&[
            (Monomial::<2>::new(&[0, 0]), F::new(4)),
            (Monomial::<2>::new(&[1, 0]), F::new(1)),
            (Monomial::<2>::new(&[0, 1]), F::new(1)),
            (Monomial::<2>::new(&[1, 1]), F::new(22)),
        ]);

        // 4 + x + y + 25xy + 14x^3 + 5x^11*y^2
        let expected = SparseMultiPoly::new(&[
            (Monomial::<2>::new(&[0, 0]), F::new(4)),
            (Monomial::<2>::new(&[1, 0]), F::new(1)),
            (Monomial::<2>::new(&[0, 1]), F::new(1)),
            (Monomial::<2>::new(&[1, 1]), F::new(25)),
            (Monomial::<2>::new(&[3, 0]), F::new(14)),
            (Monomial::<2>::new(&[11, 2]), F::new(5)),
        ]);

        assert_eq!(&a + &b, expected);
        assert_eq!(&b + &a, expected);
    }

    #[test]
    #[ignore]
    // a + b = b + a
    fn test_add_is_commutative() {
        todo!()
    }

    #[test]
    #[ignore]
    fn test_sub() {
        todo!()
    }

    #[test]
    #[ignore]
    // a - a = 0
    fn test_sub_is_additive_inverse() {
        todo!()
    }

    #[test]
    // Test a few things against Sage.
    fn test_mul_spot_check() {
        type F = PrimeFieldElement64<541>;

        // 3*x*y + 14*x^3 + 5*x^11*y^2
        let p = SparseMultiPoly::new(&[
            (Monomial::<2>::new(&[1, 1]), F::new(3)),
            (Monomial::<2>::new(&[3, 0]), F::new(14)),
            (Monomial::<2>::new(&[11, 2]), F::new(5)),
        ]);

        // 4 + x + y + 22*x*y
        let q = SparseMultiPoly::new(&[
            (Monomial::<2>::new(&[0, 0]), F::new(4)),
            (Monomial::<2>::new(&[1, 0]), F::new(1)),
            (Monomial::<2>::new(&[0, 1]), F::new(1)),
            (Monomial::<2>::new(&[1, 1]), F::new(22)),
        ]);

        // sage: sage.misc.banner.version()
        // 'SageMath version 9.5, Release Date: 2022-01-30'
        // sage: P.<x,y,z> = PolynomialRing(GF(541), 3, order='lex')
        // sage: p = 3*x*y + 14*x^3 + 5*x^11*y^2
        // sage: q = 4 + x + y + 22*x*y
        // sage: p * q
        // 110*x^12*y^3 + 5*x^12*y^2 + 5*x^11*y^3 + 20*x^11*y^2 - 233*x^4*y + 14*x^4 + 14*x^3*y + 56*x^3 + 66*x^2*y^2 + 3*x^2*y + 3*x*y^2 + 12*x*y

        let expected = SparseMultiPoly::new(&[
            (Monomial::<2>::new(&[12, 3]), F::new(110)),
            (Monomial::<2>::new(&[12, 2]), F::new(5)),
            (Monomial::<2>::new(&[11, 3]), F::new(5)),
            (Monomial::<2>::new(&[11, 2]), F::new(20)),
            (Monomial::<2>::new(&[4, 1]), F::new(233).neg()),
            (Monomial::<2>::new(&[4, 0]), F::new(14)),
            (Monomial::<2>::new(&[3, 1]), F::new(14)),
            (Monomial::<2>::new(&[3, 0]), F::new(56)),
            (Monomial::<2>::new(&[2, 2]), F::new(66)),
            (Monomial::<2>::new(&[2, 1]), F::new(3)),
            (Monomial::<2>::new(&[1, 2]), F::new(3)),
            (Monomial::<2>::new(&[1, 1]), F::new(12)),
        ]);

        assert_eq!(&p * &q, expected);
    }

    #[test]
    #[ignore]
    // a * 1 = a
    fn test_mul_one_is_identity() {
        todo!()
    }

    #[test]
    #[ignore]
    //
    fn test_mul_is_commutative() {
        todo!()
    }

    #[test]
    fn test_div_rem() {
        type F = PrimeFieldElement64<541>;
        let vars = ["x", "y"];

        let p: SparseMultiPoly<2, F> =
            SparseMultiPoly::parse("5*x^11*y^2  + 14*x^3 + 3*x*y", vars).unwrap();

        {
            // p / 1 = p
            let (q, r) = p.div_rem(&SparseMultiPoly::one(), MonomialOrder::Lexicographic);
            assert_eq!(q, p);
            assert_eq!(r, SparseMultiPoly::zero());
        }

        {
            // p / p = 1
            let (q, r) = p.div_rem(&p, MonomialOrder::Lexicographic);
            assert_eq!(q, SparseMultiPoly::one());
            assert_eq!(r, SparseMultiPoly::zero());
        }

        {
            // p / x = 5*x^10*y^2 + 14*x^2 + 3*y
            let (q, r) = p.div_rem(
                &SparseMultiPoly::parse("x", vars).unwrap(),
                MonomialOrder::Lexicographic,
            );
            assert_eq!(
                q,
                SparseMultiPoly::parse("3*y + 14*x^2 + 5*x^10*y^2", vars).unwrap()
            );
            assert_eq!(r, SparseMultiPoly::zero());
        }

        {
            // p / y = (5*x^11*y) * y + 14*x^3 + 3*x*y
            let (q, r) = p.div_rem(
                &SparseMultiPoly::parse("y", vars).unwrap(),
                MonomialOrder::Lexicographic,
            );
            assert_eq!(q, SparseMultiPoly::parse("5*x^11*y", vars).unwrap());
            assert_eq!(r, SparseMultiPoly::parse("14*x^3 + 3*x*y", vars).unwrap());
        }
    }

    #[test]
    fn test_multi_div_rem() {
        type F = PrimeFieldElement64<541>;
        let vars = ["x", "y"];
        let order = MonomialOrder::Lexicographic;

        let p: SparseMultiPoly<2, F> =
            SparseMultiPoly::parse("5*x^11*y^2  + 14*x^3 + 3*x*y", vars).unwrap();
        let divisors = [
            SparseMultiPoly::parse("x", vars).unwrap(),
            SparseMultiPoly::parse("x*y", vars).unwrap(),
            SparseMultiPoly::parse("y", vars).unwrap(),
        ];

        let (quotients, remainder) = p.multi_div_rem(&divisors, order);

        assert_eq!(quotients.len(), divisors.len());

        // no monomial in r is divisible by the leading term of any divisor.
        for divisor in &divisors {
            for (monomial, _) in &remainder.terms {
                assert_eq!(
                    None,
                    monomial.checked_div(&divisor.leading_term(order).monomial)
                );
            }
        }

        // p = q_0 * f_0 + q_1 * f_1 + ... + q_{k-1} * f_{k-1} + r
        let mut p_recovered = remainder.clone();
        for (i, divisor) in divisors.iter().enumerate() {
            p_recovered += &quotients[i] * divisor;
        }
        assert_eq!(p, p_recovered);
    }
}
