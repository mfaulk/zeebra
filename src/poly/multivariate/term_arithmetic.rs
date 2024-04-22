//! Arithmetic operations for multivariate terms.

use std::ops;
use crate::impl_mul_variants;
use crate::FiniteField;
use crate::poly::multivariate::term::Term;

/// &Term * &Term
impl<const N: usize, F: FiniteField> ops::Mul<&Term<N,F>> for &Term<N,F> {
    type Output = Term<N,F>;

    fn mul(self, rhs: &Term<N,F>) -> Self::Output {
        let coefficient = self.coefficient * rhs.coefficient;
        let monomial = &self.monomial * &rhs.monomial;
        Term { coefficient, monomial }
    }
}

impl_mul_variants!([const N: usize, F: FiniteField], Term<N, F>);

impl<const N: usize, F: FiniteField> Term<N,F> {

    pub fn checked_div(&self, rhs: &Self) -> Option<Self> {
        let coefficient = self.coefficient.checked_div(&rhs.coefficient)?;
        let monomial = self.monomial.checked_div(&rhs.monomial)?;
        Some(Term { coefficient, monomial })
    }

}