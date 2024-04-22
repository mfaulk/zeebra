//! Convert between sparse multivariate polynomials and other representations.

use crate::{
    poly::multivariate::{sparse_multivariate_polynomial::SparseMultiPoly, term::Term},
    FiniteField, Monomial,
};

/// From<FiniteField>
impl<const N: usize, F: FiniteField> From<F> for SparseMultiPoly<N, F> {
    fn from(f: F) -> Self {
        Self::new(&[Term::new(f, Monomial::one())])
    }
}

/// From<Monomial>
impl<const N: usize, F: FiniteField> From<Monomial<N>> for SparseMultiPoly<N, F> {
    fn from(monomial: Monomial<N>) -> Self {
        Self {
            terms: vec![(monomial, F::one())].into_iter().collect(),
        }
    }
}

/// From<&Monomial>
impl<const N: usize, F: FiniteField> From<&Monomial<N>> for SparseMultiPoly<N, F> {
    fn from(monomial: &Monomial<N>) -> Self {
        Self {
            terms: vec![(*monomial, F::one())].into_iter().collect(),
        }
    }
}

/// From<Term>
impl<const N: usize, F: FiniteField> From<Term<N, F>> for SparseMultiPoly<N, F> {
    fn from(term: Term<N, F>) -> Self {
        Self::new(&[term])
    }
}

/// From<&Term>
impl<const N: usize, F: FiniteField> From<&Term<N, F>> for SparseMultiPoly<N, F> {
    fn from(term: &Term<N, F>) -> Self {
        Self::new(&[*term])
    }
}

#[cfg(test)]
mod tests {

    #[test]
    #[ignore]
    // From<FiniteField> should be equivalent to new(&[Term::new(f, Monomial::one())])
    fn test_from_constant() {
        todo!()
    }

    #[test]
    #[ignore]
    // From<Monomial> should be equivalent to new(&[Term::new(monomial, F::one())])
    fn test_from_monomial() {
        todo!()
    }

    #[test]
    #[ignore]
    // From<Term> should be equivalent to new(&[term])
    fn test_from_term() {
        todo!()
    }
}
