//! Multivariate polynomial represented as a sparse collection of terms.

use crate::{
    poly::{
        multivariate::{
            monomial_order::MonomialOrder,
            multi_poly_parser::{parse_multivariate_polynomial, Rule},
            term::Term,
        },
        Monomial,
    },
    FiniteField,
};
use pest::error::Error;
use proptest::{
    arbitrary::any,
    collection::vec,
    prelude::{Arbitrary, BoxedStrategy, Strategy},
};
use serde::{Deserialize, Serialize};
use std::{
    collections::HashMap,
    fmt::{Display, Formatter},
    hash::{Hash, Hasher},
};

/// Multivariate polynomial over N variables.
#[derive(Clone, Eq, PartialEq, Debug, Default, Deserialize, Serialize)]
pub struct SparseMultiPoly<const N: usize, F: FiniteField> {
    /// Terms stored as the mapping monomial --> coefficient
    /// The zero polynomial may be represented as an empty set of terms, or by the single
    /// term 0 * Monomial:one(). Otherwise, terms should not contain any monomials with zero coefficient.  
    #[serde(bound = "F: FiniteField")]
    pub(crate) terms: HashMap<Monomial<N>, F>,
}

impl<const N: usize, F: FiniteField> SparseMultiPoly<N, F> {
    /// Create a new polynomial from a list of terms.
    ///
    /// # Arguments
    /// * `terms` - A list of terms (monomial, coefficient).
    ///
    /// The zero polynomial may be represented as an empty set of terms, or by the single
    /// term 0 * Monomial:one().
    pub fn new<T>(terms: &[T]) -> Self
    where
        T: Into<Term<N, F>> + Clone,
    {
        let mut terms_map: HashMap<Monomial<N>, F> = HashMap::default();
        for term in terms.iter() {
            let term: Term<N, F> = term.clone().into();
            // Omit terms with zero coefficient.
            if term.is_zero() {
                continue;
            }

            match terms_map.get_mut(term.monomial()) {
                None => {
                    terms_map.insert(*term.monomial(), *term.coefficient());
                }
                Some(c) => {
                    // Merge terms with equal monomials.
                    *c += *term.coefficient();
                }
            }
        }

        Self { terms: terms_map }
    }

    /// Parse a Sage-style string.
    ///
    /// # Arguments
    /// * `value` - A Sage-style string, e.g. "2*x^3 + 1".
    /// * `variables` - The expected variable names.
    pub fn parse(value: &str, variables: [&str; N]) -> Result<Self, Error<Rule>> {
        parse_multivariate_polynomial(value, variables)
    }

    /// The zero polynomial.
    pub fn zero() -> Self {
        Self {
            terms: Default::default(),
        }
    }

    /// The constant polynomial 1.
    pub fn one() -> Self {
        Self {
            terms: vec![(Monomial::one(), F::one())].into_iter().collect(),
        }
    }

    /// Returns true if the polynomial is the zero polynomial.
    pub fn is_zero(&self) -> bool {
        // terms must be empty or only contain 0 * (x^0*y*0...z^0)
        match self.terms.get(&Monomial::one()) {
            Some(c) => c.is_zero() && (self.terms.len() == 1),
            None => self.terms.is_empty(),
        }
    }

    pub fn is_one(&self) -> bool {
        // Must only contain a single term 1*x^0*y*0...z^0
        match self.terms.get(&Monomial::one()) {
            Some(c) => c.is_one() && (self.terms.len() == 1),
            None => false,
        }
    }

    /// Total degree of the polynomial.
    pub fn degree(&self) -> u64 {
        self.terms
            .keys()
            .map(|term| term.degree())
            .max()
            .unwrap_or(0)
    }

    /// Evaluate the polynomial at the vector x.
    pub fn eval(&self, x: &[F]) -> F {
        assert_eq!(x.len(), N, "The point x has the wrong length.");

        self.terms
            .iter()
            .fold(F::zero(), |acc, (term, c): (&Monomial<N>, &F)| {
                acc + *c * term.eval(x)
            })
    }

    pub fn terms(&self) -> &HashMap<Monomial<N>, F> {
        &self.terms
    }

    /// The leading term w.r.t. the given monomial order.
    pub fn leading_term(&self, order: MonomialOrder) -> Term<N, F> {
        self.terms
            .iter()
            .max_by(|a, b| order.cmp(a.0, b.0))
            .map(|(monom, coefficient)| Term::new(coefficient.clone(), monom.clone()))
            .unwrap_or(Term::zero())
    }

    /// The leading monomial w.r.t. the given monomial order.
    pub fn leading_monomial(&self, order: MonomialOrder) -> Monomial<N> {
        let term = self.leading_term(order);
        term.monomial().clone()
    }

    /// The leading coefficient w.r.t. the given monomial order.
    pub fn leading_coefficient(&self, order: MonomialOrder) -> F {
        let term = self.leading_term(order);
        term.coefficient.clone()
    }

    /// The multidegree of the polynomial w.r.t. the given monomial order.
    pub fn multidegree(&self, order: MonomialOrder) -> [u32; N] {
        let term = self.leading_term(order);
        let mut degrees = [0; N];
        degrees.copy_from_slice(term.monomial.exponents());
        degrees
    }

    /// Scale the polynomial by a constant factor.
    pub fn scale(&self, scale_factor: &F) -> Self {
        let terms: Vec<_> = self
            .terms
            .iter()
            .map(|(monomial, c)| (*monomial, *c * scale_factor))
            .collect();
        Self::new(&terms)
    }
}

/// Display the polynomial in Sage-style.
impl<const N: usize, F: FiniteField> Display for SparseMultiPoly<N, F> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        // TODO: handle the zero polynomial.

        let mut terms: Vec<_> = self.terms.iter().collect();
        let order = MonomialOrder::GradedLexicographic;
        terms.sort_by(|(a, _), (b, _)| order.cmp(a, b).reverse());

        let mut first = true;
        for (monomial, c) in terms {
            if first {
                first = false;
            } else {
                write!(f, " + ")?;
            }
            if c.is_one() && monomial.is_one() {
                write!(f, "1")?;
                continue;
            }
            if !c.is_one() {
                write!(f, "{}*", c)?;
            }
            write!(f, "{}", monomial)?;
        }
        Ok(())
    }
}

/// Hash
impl<const N: usize, F: FiniteField> Hash for SparseMultiPoly<N, F> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        // Terms must be hashed in a canonical order.
        let order = MonomialOrder::Lexicographic;
        let mut terms: Vec<_> = self.terms.iter().collect();
        terms.sort_by(|(a, _), (b, _)| order.cmp(a, b).reverse());
        terms.hash(state);
    }
}

#[derive(Debug, Clone, Default)]
pub struct ArbParams {
    num_terms: usize,
}

/// Arbitrary
impl<const N: usize, F: FiniteField + 'static> Arbitrary for SparseMultiPoly<N, F> {
    type Parameters = ArbParams;

    fn arbitrary_with(args: Self::Parameters) -> Self::Strategy {
        (
            vec(any::<Monomial<N>>(), args.num_terms),
            vec(any::<F>(), args.num_terms),
        )
            .prop_map(|(monomials, coefficients)| {
                // Collecting into an array so that the size is known at compile time.
                let mut terms: Vec<Term<N, F>> = vec![];
                for (i, (m, c)) in monomials.into_iter().zip(coefficients).enumerate() {
                    terms[i] = (c, m).into();
                }
                Self::new(&terms)
            })
            .boxed()
    }

    type Strategy = BoxedStrategy<Self>;
}

#[cfg(test)]
mod tests {
    use crate::{
        fields::{PrimeFieldElement64, Zp65537},
        identities::Zero,
        poly::{
            multivariate::{sparse_multivariate_polynomial::SparseMultiPoly, term::Term},
            Monomial,
        },
        FiniteField,
    };

    #[test]
    // Should omit terms with zero coefficient.
    fn test_new_omits_zeros() {
        type F = PrimeFieldElement64<337>;
        let terms: Vec<_> = vec![
            (Monomial::<2>::new(&[1, 1]), F::new(3)),
            (Monomial::<2>::new(&[3, 0]), F::new(0)), // This should be omitted.
            (Monomial::<2>::new(&[3, 1]), F::new(3)),
        ];
        let p = SparseMultiPoly::new(&terms);

        assert_eq!(p.terms.len(), 2);
    }

    #[test]
    // Should merge terms with same powers.
    fn test_new_should_merge_terms() {
        type F = PrimeFieldElement64<337>;
        // 3xy + xy + 8xy
        let p = SparseMultiPoly::new(&[
            (Monomial::<2>::new(&[1, 1]), F::new(3)),
            (Monomial::<2>::new(&[1, 1]), F::new(1)), // This should be omitted.
            (Monomial::<2>::new(&[1, 1]), F::new(8)),
        ]);

        let expected = SparseMultiPoly::new(&[(Monomial::<2>::new(&[1, 1]), F::new(12))]);
        assert_eq!(p, expected)
    }

    #[test]
    #[ignore]
    // Order of terms should not matter.
    fn test_new_term_order_is_irrelevant() {
        todo!()
    }

    #[test]
    // zero() should produce a polynomial with empty set of terms.
    fn test_zero() {
        type F = PrimeFieldElement64<337>;
        const N: usize = 5;
        let p = SparseMultiPoly::<N, F>::zero();
        assert_eq!(p.terms.len(), 0);
    }

    #[test]
    // is_zero() should accept the empty set of terms, or the degree-zero monomial with zero coefficient.
    fn test_is_zero() {
        type F = Zp65537;
        const N: usize = 5;
        let terms: Vec<Term<N, F>> = vec![];
        assert!(SparseMultiPoly::<N, F>::new(&terms).is_zero());
        assert!(SparseMultiPoly::<N, F>::new(&[(Monomial::new(&[0u32; 5]), F::zero())]).is_zero());
        assert!(SparseMultiPoly::<N, F>::new(&[(Monomial::new(&[1u32; 5]), F::zero())]).is_zero());
    }

    #[test]
    // constant(0) should be equivalent to zero().
    fn test_constant_zero() {
        type F = PrimeFieldElement64<337>;
        const N: usize = 5;
        type P = SparseMultiPoly<N, F>;
        assert_eq!(P::from(F::zero()), P::zero());
    }

    #[test]
    // Should correctly merge terms, e.g. 1 + xy + xy --> 1 + 2xy.
    fn test_new_merges_terms() {
        type F = PrimeFieldElement64<337>;
        // 3xy + 7xy
        let terms: Vec<_> = vec![
            (Monomial::<2>::new(&[1, 1]), F::new(3)),
            (Monomial::<2>::new(&[1, 1]), F::new(7)),
        ];

        let p_1 = SparseMultiPoly::new(&terms);

        let terms_merged: Vec<_> = vec![(Monomial::<2>::new(&[1, 1]), F::new(10))];
        let p_2 = SparseMultiPoly::new(&terms_merged);

        assert_eq!(p_1, p_2);
    }

    #[test]
    fn test_display() {
        type F = PrimeFieldElement64<337>;
        // 3xy + 14x^3 + 18x^3y
        let terms: Vec<_> = vec![
            (Monomial::<2>::new(&[1, 1]), F::new(3)),
            (Monomial::<2>::new(&[3, 1]), F::new(1)),
            (Monomial::<2>::new(&[3, 0]), F::new(14)),
        ];
        let p = SparseMultiPoly::new(&terms);
        assert_eq!(format!("{}", p), "x_0^3*x_1 + 14*x_0^3 + 3*x_0*x_1");
    }

    #[test]
    // Should return total degree of the polynomial.
    fn test_degree() {
        type F = PrimeFieldElement64<337>;
        // 3xy + 14x^3 + 18x^3y
        let terms: Vec<_> = vec![
            (Monomial::<2>::new(&[1, 1]), F::new(3)),  // 3xy
            (Monomial::<2>::new(&[3, 1]), F::new(18)), // 18x^3y
            (Monomial::<2>::new(&[3, 0]), F::new(14)), // 14x^3
        ];
        let p = SparseMultiPoly::new(&terms);
        assert_eq!(p.degree(), 4);
    }

    #[test]
    // Should correctly evaluate the polynomial.
    fn test_evaluate() {
        type F = PrimeFieldElement64<337>;
        // 3xy + xy^3
        let terms: Vec<_> = vec![
            (Monomial::<2>::new(&[1, 1]), F::new(3)),
            (Monomial::<2>::new(&[1, 3]), F::new(1)),
        ];

        let p = SparseMultiPoly::new(&terms);

        assert_eq!(p.eval(&[F::new(1), F::new(1)]), F::new(4));
        assert_eq!(p.eval(&[F::new(0), F::new(1)]), F::new(0));
        assert_eq!(p.eval(&[F::new(1), F::new(2)]), F::new(14));
    }

    #[test]
    #[should_panic]
    // Should panic if the point x has the wrong length.
    fn test_evaluate_panics_wrong_length() {
        type F = PrimeFieldElement64<337>;
        // 3xy + xy^3
        let terms: Vec<_> = vec![
            (Monomial::<2>::new(&[1, 1]), F::new(3)),
            (Monomial::<2>::new(&[1, 3]), F::new(1)),
        ];

        let p = SparseMultiPoly::new(&terms);
        // p is a polynomial in 2 variables, but 3 are given.
        let _x = p.eval(&[F::new(1), F::new(1), F::new(1)]);
    }

    // Operations should not produce unnecessary terms with zero coefficient.
}
