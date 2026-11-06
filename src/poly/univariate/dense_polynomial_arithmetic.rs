//! Arithmetic operations for dense univariate polynomials.

use crate::{impl_add_variants, impl_div_variants, impl_mul_variants, impl_rem_variants};
use crate::{impl_sub_variants, poly::univariate::div_with_remainder::div_with_remainder};
use crate::{poly::univariate::dense_polynomial::DensePolynomial, FiniteField, Polynomial};
use std::{cmp::max, ops};

// Borrowed + Borrowed
impl<F: FiniteField> ops::Add<&DensePolynomial<F>> for &DensePolynomial<F> {
    type Output = DensePolynomial<F>;

    fn add(self, rhs: &DensePolynomial<F>) -> Self::Output {
        let (longer, shorter) = {
            if self.degree() > rhs.degree() {
                (self, rhs)
            } else {
                (rhs, self)
            }
        };

        let mut sum: Vec<F> = longer.coefficients.clone();
        for i in 0..shorter.coefficients.len() {
            sum[i] += shorter.coefficients[i];
        }

        DensePolynomial::<F>::new(&sum)
    }
}

impl_add_variants!([F: FiniteField], DensePolynomial<F>);

// Borrowed - Borrowed
impl<F: FiniteField> ops::Sub<&DensePolynomial<F>> for &DensePolynomial<F> {
    type Output = DensePolynomial<F>;

    fn sub(self, rhs: &DensePolynomial<F>) -> Self::Output {
        let result_len = max(self.coefficients.len(), rhs.coefficients.len());
        let mut result = vec![F::zero(); result_len];
        for i in 0..result_len {
            result[i] = *self.coefficients.get(i).unwrap_or(&F::zero())
                - *rhs.coefficients.get(i).unwrap_or(&F::zero());
        }

        Self::Output::new(&result)
    }
}

impl_sub_variants!([F: FiniteField], DensePolynomial<F>);

// -Borrowed
impl<F: FiniteField> ops::Neg for &DensePolynomial<F> {
    type Output = DensePolynomial<F>;

    fn neg(self) -> Self::Output {
        let mut result = self.clone();
        for coeff in result.coefficients.iter_mut() {
            *coeff = -*coeff;
        }
        result
    }
}

// -Owned
impl<F: FiniteField> ops::Neg for DensePolynomial<F> {
    type Output = DensePolynomial<F>;

    fn neg(self) -> Self::Output {
        (&self).neg()
    }
}

// Borrowed * Borrowed
impl<F: FiniteField> ops::Mul<&DensePolynomial<F>> for &DensePolynomial<F> {
    type Output = DensePolynomial<F>;

    fn mul(self, rhs: &DensePolynomial<F>) -> Self::Output {
        let prod_degree = self.degree() + rhs.degree();
        let mut product = vec![F::zero(); (prod_degree + 1) as usize];
        for (i, a) in self.coefficients.iter().enumerate() {
            for (j, b) in rhs.coefficients.iter().enumerate() {
                // ax^i * bx^j = abx^{i+j}
                let degree = i + j;
                product[degree] += *a * *b;
            }
        }
        DensePolynomial::<F>::new(&product)
    }
}

impl_mul_variants!([F: FiniteField], DensePolynomial<F>);

// Borrowed / Borrowed. The quotient half of division with remainder; `%` is the other half, and a
// caller that wants both should call `div_with_remainder` rather than pay for the division twice.
impl<F: FiniteField> ops::Div<&DensePolynomial<F>> for &DensePolynomial<F> {
    type Output = DensePolynomial<F>;

    fn div(self, rhs: &DensePolynomial<F>) -> Self::Output {
        div_with_remainder(self, rhs).0
    }
}

impl_div_variants!([F: FiniteField], DensePolynomial<F>);

// Borrowed % Borrowed
impl<F: FiniteField> ops::Rem<&DensePolynomial<F>> for &DensePolynomial<F> {
    type Output = DensePolynomial<F>;

    fn rem(self, rhs: &DensePolynomial<F>) -> Self::Output {
        div_with_remainder(self, rhs).1
    }
}

impl_rem_variants!([F: FiniteField], DensePolynomial<F>);

// &DensePolynomial * &F
impl<F: FiniteField> ops::Mul<&F> for &DensePolynomial<F> {
    type Output = DensePolynomial<F>;

    fn mul(self, rhs: &F) -> Self::Output {
        self.scale(rhs)
    }
}

// &DensePolynomial * F
impl<F: FiniteField> ops::Mul<F> for &DensePolynomial<F> {
    type Output = DensePolynomial<F>;

    fn mul(self, rhs: F) -> Self::Output {
        self * &rhs
    }
}

// DensePolynomial * &F
impl<F: FiniteField> ops::Mul<&F> for DensePolynomial<F> {
    type Output = DensePolynomial<F>;

    fn mul(self, rhs: &F) -> Self::Output {
        &self * rhs
    }
}

// DensePolynomial * F
impl<F: FiniteField> ops::Mul<F> for DensePolynomial<F> {
    type Output = DensePolynomial<F>;

    fn mul(self, rhs: F) -> Self::Output {
        &self * &rhs
    }
}

#[cfg(test)]
mod tests {
    use crate::poly::univariate::PolynomialParams;
    use crate::{
        fields::{PrimeFieldElement64, Zp7},
        poly::univariate::dense_polynomial::DensePolynomial,
        FiniteField, Polynomial,
    };
    use proptest::prelude::*;

    fn get_elements(values: Vec<u64>) -> Vec<PrimeFieldElement64<13>> {
        values
            .iter()
            .map(|v| PrimeFieldElement64::new(*v))
            .collect()
    }

    #[test]
    // Adding polynomials of equal degree with coefficients in GF(p) produces correct sum.
    fn test_add_polynomials_over_fp_equal_degrees() {
        type F = PrimeFieldElement64<13>;
        type P = DensePolynomial<F>;

        // 1 + 2x + 3x^2 + 4x^3
        let a_coefficients = get_elements(vec![1, 2, 3, 4]);
        let a = P::new(&a_coefficients);

        // 8 + 3x + 10x^2 + 11x^3
        let b_coefficients = get_elements(vec![8, 3, 10, 11]);
        let b = P::new(&b_coefficients);

        // (9 + 5x + 13x^2 + 15x^3) mod 13
        let expected_coefficients = get_elements(vec![9, 5, 0, 2]);
        let expected_sum = P::new(&expected_coefficients);

        assert_eq!(a + b, expected_sum);
    }

    #[test]
    // Add polynomials of unequal degree with coefficients in GF(p)  produces correct sum.
    fn test_add_polynomials_over_fp_unequal_degrees() {
        // 1 + 2x + 3x^2 + 4x^3 + 5x^4 + 6x^5
        let a_coefficients = get_elements(vec![1, 2, 3, 4, 5, 6]);
        let a = DensePolynomial::new(&a_coefficients);

        // 8 + 3x + 10x^2 + 11x^3
        let b_coefficients = get_elements(vec![8, 3, 10, 11]);
        let b = DensePolynomial::new(&b_coefficients);

        // (9 + 5x + 13x^2 + 15x^3 + 5x^4 + 6x^5) mod 13
        let expected_coefficients = get_elements(vec![9, 5, 0, 2, 5, 6]);
        let expected_sum = DensePolynomial::new(&expected_coefficients);

        assert_eq!(a + b, expected_sum);
    }

    fn addition_is_commutative<F: FiniteField>(p: &DensePolynomial<F>, q: &DensePolynomial<F>) {
        assert_eq!(p + q, q + p);
    }

    proptest! {
        #[test]
        fn test_addition_is_commutative(
            p in ((0..=100usize).prop_map(PolynomialParams::from).prop_flat_map(any_with::<DensePolynomial<Zp7>>)),
            q in ((0..=100usize).prop_map(PolynomialParams::from).prop_flat_map(any_with::<DensePolynomial<Zp7>>))) {
            addition_is_commutative(&p, &q);
        }
    }

    #[test]
    // Sum should not produce a highest-degree term with zero coefficient.
    fn test_add_removes_high_zeros() {
        type F = PrimeFieldElement64<13>;
        type P = DensePolynomial<F>;

        let a = P::try_from("1 + 2x").unwrap();
        let b = P::try_from("11x").unwrap();
        let sum = a + b;

        assert_eq!(sum.coefficients.len(), 1);
        assert_eq!(sum, P::one());
    }

    #[test]
    // Subtract polynomials of unequal degree with coefficients in GF(p).
    fn test_sub_polynomials_over_fp_unequal_degrees() {
        // 1 + 2x + 3x^2 + 4x^3 + 5x^4 + 6x^5
        let a_coefficients = get_elements(vec![1, 2, 3, 4, 5, 6]);
        let a = DensePolynomial::new(&a_coefficients);

        // 8 + 3x + 10x^2 + 11x^3
        let b_coefficients = get_elements(vec![8, 3, 10, 11]);
        let b = DensePolynomial::new(&b_coefficients);

        // 6 + 12x + 6x^2 + 6x^3 + 5x^4 + 6x^5
        let expected_coefficients = get_elements(vec![6, 12, 6, 6, 5, 6]);
        let expected = DensePolynomial::new(&expected_coefficients);

        assert_eq!(a - b, expected);
    }

    #[test]
    // Subtracting should not produce a highest-degree term with zero coefficient.
    fn test_sub_removes_high_zeros() {
        type F = PrimeFieldElement64<541>;
        type P = DensePolynomial<F>;
        let p1 = P::try_from("3 + 16x^2 + 44x^3").unwrap();
        let p2 = P::try_from("16x^2 + 44x^3").unwrap();
        let diff = p1 - p2; // 3
        assert_eq!(diff.coefficients.len(), 1, "diff: {:?}", diff);
    }

    #[test]
    fn test_mul_by_zero() {
        let zero = DensePolynomial::new(&get_elements(vec![0]));
        // 1 + 2x + 3x^2 + 4x^3 + 5x^4 + 6x^5
        let a_coefficients = get_elements(vec![1, 2, 3, 4, 5, 6]);
        let a = DensePolynomial::new(&a_coefficients);
        assert_eq!(a * &zero, zero);
    }

    #[test]
    fn test_mul_by_one() {
        let one = DensePolynomial::new(&get_elements(vec![1]));
        // 1 + 2x + 3x^2 + 4x^3 + 5x^4 + 6x^5
        let a_coefficients = get_elements(vec![1, 2, 3, 4, 5, 6]);
        let a = DensePolynomial::new(&a_coefficients);
        assert_eq!(&a * one, a);
    }

    fn multiplication_is_commutative<F: FiniteField>(
        p: &DensePolynomial<F>,
        q: &DensePolynomial<F>,
    ) {
        assert_eq!(p * q, q * p);
    }

    proptest! {
        #[test]
        fn test_multiplication_is_commutative(
            p in ((0..=100usize).prop_map(PolynomialParams::from).prop_flat_map(any_with::<DensePolynomial<Zp7>>)),
            q in ((0..=100usize).prop_map(PolynomialParams::from).prop_flat_map(any_with::<DensePolynomial<Zp7>>))) {
            multiplication_is_commutative(&p, &q);
        }
    }

    #[test]
    fn test_mul_spot_check() {
        // 1 + 2x + 3x^2 + 4x^3 + 5x^4 + 6x^5
        let a_coefficients = get_elements(vec![1, 2, 3, 4, 5, 6]);
        let a = DensePolynomial::new(&a_coefficients);

        // 8 + 3x + 10x^2 + 11x^3
        let b_coefficients = get_elements(vec![8, 3, 10, 11]);
        let b = DensePolynomial::new(&b_coefficients);

        // 8 + 6x + x^2 + 7x^3 + 0x^4 + 6x^5 + 8x^6 + 11x^7 + x^8
        let expected = DensePolynomial::new(&get_elements(vec![8, 6, 1, 7, 0, 6, 8, 11, 1]));
        assert_eq!(a * b, expected);
    }

    #[test]
    // `/` returns the quotient and `%` the remainder of `div_with_remainder`.
    fn test_div_and_rem_agree_with_div_with_remainder() {
        type F = Zp7;
        type P = DensePolynomial<F>;

        let f = P::try_from("1 + 2x + 3x^2 + 4x^3").unwrap();
        let g = P::try_from("2 + x^2").unwrap();
        let (quotient, remainder) = f.div_with_remainder(&g);

        assert_eq!(&f / &g, quotient);
        assert_eq!(&f % &g, remainder);
    }

    #[test]
    // All four owned/borrowed operand combinations, plus `/=` and `%=`, are available.
    fn test_div_and_rem_operand_variants() {
        type F = Zp7;
        type P = DensePolynomial<F>;

        let f = P::try_from("1 + x + x^3").unwrap();
        let g = P::try_from("3 + x").unwrap();
        let quotient = &f / &g;
        let remainder = &f % &g;

        assert_eq!(f.clone() / &g, quotient);
        assert_eq!(&f / g.clone(), quotient);
        assert_eq!(f.clone() / g.clone(), quotient);
        assert_eq!(f.clone() % &g, remainder);
        assert_eq!(&f % g.clone(), remainder);
        assert_eq!(f.clone() % g.clone(), remainder);

        let mut quotient_assign = f.clone();
        quotient_assign /= g.clone();
        assert_eq!(quotient_assign, quotient);

        let mut remainder_assign = f.clone();
        remainder_assign %= g.clone();
        assert_eq!(remainder_assign, remainder);
    }

    #[test]
    // `%` by a zero divisor panics, as `div_with_remainder` does.
    #[should_panic]
    fn test_rem_by_zero_should_panic() {
        type F = Zp7;
        type P = DensePolynomial<F>;
        let _ = P::try_from("1 + x").unwrap() % P::zero();
    }

    #[test]
    // `/` by a zero divisor panics, as `div_with_remainder` does.
    #[should_panic]
    fn test_div_by_zero_should_panic() {
        type F = Zp7;
        type P = DensePolynomial<F>;
        let _ = P::try_from("1 + x").unwrap() / P::zero();
    }

    proptest! {
        #[test]
        // f = (f / g) * g + f % g for every nonzero divisor g.
        fn test_div_and_rem_recover_the_dividend(
            f in ((0..=50usize).prop_map(PolynomialParams::from).prop_flat_map(any_with::<DensePolynomial<Zp7>>)),
            g in ((0..=50usize).prop_map(PolynomialParams::from).prop_flat_map(any_with::<DensePolynomial<Zp7>>))) {
            if g.is_zero() {
                return Ok(());
            }
            prop_assert_eq!(&(&(&f / &g) * &g) + &(&f % &g), f);
        }
    }
}
