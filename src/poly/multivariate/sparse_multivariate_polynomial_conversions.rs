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
    use crate::{
        fields::Zp541,
        poly::multivariate::{
            sparse_multivariate_polynomial::SparseMultiPoly, term::Term, Monomial,
        },
        FiniteField, One, Zero,
    };

    const N: usize = 3;
    type F = Zp541;
    type Poly = SparseMultiPoly<N, F>;

    /// `From<F>` lifts a field element to the constant polynomial.
    #[test]
    fn test_from_constant() {
        let c = F::new(7);
        assert_eq!(
            Poly::from(c),
            Poly::new(&[Term::new(c, Monomial::<N>::one())])
        );
        // A zero constant is the zero polynomial, which holds no terms.
        assert_eq!(Poly::from(F::zero()), Poly::zero());
    }

    /// `From<Monomial>` gives the monomial a coefficient of one.
    #[test]
    fn test_from_monomial() {
        let monomial = Monomial::<N>::new(&[1, 0, 2]);
        assert_eq!(
            Poly::from(monomial),
            Poly::new(&[Term::new(F::one(), monomial)])
        );
        // The borrowed conversion agrees with the owned one.
        assert_eq!(Poly::from(&monomial), Poly::from(monomial));
    }

    /// `From<Term>` wraps a single term.
    #[test]
    fn test_from_term() {
        let term = Term::new(F::new(5), Monomial::<N>::new(&[2, 1, 0]));
        assert_eq!(Poly::from(term), Poly::new(&[term]));
        assert_eq!(Poly::from(&term), Poly::from(term));
    }
}
