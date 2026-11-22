//! Multivariate polynomial represented as a sparse collection of terms.

use crate::{
    poly::{
        multivariate::{
            monomial_hash::MonomialMap,
            monomial_order::MonomialOrder,
            multi_poly_parser::{parse_multivariate_polynomial, Rule},
            term::Term,
        },
        Monomial,
    },
    FiniteField,
};
use pest::error::Error;
#[cfg(any(test, feature = "proptest"))]
use proptest::{
    arbitrary::any,
    collection::vec,
    prelude::{Arbitrary, BoxedStrategy, Strategy},
};
use serde::{ser::SerializeStruct, Deserialize, Serialize, Serializer};
use std::{
    fmt::{Debug, Display, Formatter},
    hash::{Hash, Hasher},
};

/// Multivariate polynomial over N variables.
///
/// `Serialize`, `Debug` and `Hash` write the terms in descending lexicographic order, so equal
/// polynomials produce equal output however their terms were inserted.
#[derive(Clone, Eq, PartialEq, Default, Deserialize)]
pub struct SparseMultiPoly<const N: usize, F: FiniteField> {
    /// Terms stored as the mapping monomial --> coefficient
    /// The zero polynomial may be represented as an empty set of terms, or by the single
    /// term 0 * Monomial:one(). Otherwise, terms should not contain any monomials with zero coefficient.  
    #[serde(bound = "F: FiniteField")]
    pub(crate) terms: MonomialMap<N, F>,
}

impl<const N: usize, F: FiniteField> SparseMultiPoly<N, F> {
    /// Create a new polynomial from a list of terms.
    ///
    /// # Arguments
    /// * `terms` - A list of terms (monomial, coefficient).
    ///
    /// Terms whose coefficient is zero are omitted, including terms that cancel when merged, so
    /// the zero polynomial is always the empty set of terms. `PartialEq` is derived over that set
    /// and `Hash` is written over it, so a surviving zero term would make a polynomial unequal to
    /// its own canonical form.
    pub fn new<T>(terms: &[T]) -> Self
    where
        T: Into<Term<N, F>> + Clone,
    {
        let mut terms_map: MonomialMap<N, F> = MonomialMap::default();
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

        // Merging can cancel a monomial out entirely; such a term is not part of the polynomial.
        terms_map.retain(|_monomial, c| !c.is_zero());

        Self { terms: terms_map }
    }

    /// Parse a Sage-style string.
    ///
    /// # Arguments
    /// * `value` - A Sage-style string, e.g. "2*x^3 + 1".
    /// * `variables` - The expected variable names.
    pub fn parse(value: &str, variables: [&str; N]) -> Result<Self, Box<Error<Rule>>> {
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

    /// The polynomial that results from fixing variable `index` to `value`.
    ///
    /// The named variable disappears, so the result lies in the polynomial ring over the
    /// remaining variables, carried here as a zero exponent in that position.
    ///
    /// # Panics
    /// Panics if `index` is not a variable of this ring.
    pub fn substitute(&self, index: usize, value: F) -> Self {
        assert!(
            index < N,
            "index {} is not one of the {} variables",
            index,
            N
        );
        let substituted: Vec<(Monomial<N>, F)> = self
            .terms
            .iter()
            .map(|(monomial, coefficient)| {
                let exponent = monomial.exponents()[index];
                let mut exponents = [0u32; N];
                exponents.copy_from_slice(monomial.exponents());
                exponents[index] = 0;
                (
                    Monomial::new(&exponents),
                    *coefficient * value.pow(exponent as u128),
                )
            })
            .collect();
        // Through `new`, which merges monomials that have become equal once the variable is gone
        // and drops any term whose coefficient cancelled to zero.
        Self::new(&substituted)
    }

    /// True if the polynomial has no variables, i.e. is an element of the base field.
    pub fn is_constant(&self) -> bool {
        self.terms.keys().all(|monomial| monomial.is_one())
    }

    pub fn terms(&self) -> &MonomialMap<N, F> {
        &self.terms
    }

    /// The leading term w.r.t. the given monomial order.
    pub fn leading_term(&self, order: MonomialOrder) -> Term<N, F> {
        self.terms
            .iter()
            .max_by(|a, b| order.cmp(a.0, b.0))
            .map(|(monom, coefficient)| Term::new(*coefficient, *monom))
            .unwrap_or(Term::zero())
    }

    /// The leading monomial w.r.t. the given monomial order.
    pub fn leading_monomial(&self, order: MonomialOrder) -> Monomial<N> {
        let term = self.leading_term(order);
        *term.monomial()
    }

    /// The leading coefficient w.r.t. the given monomial order.
    pub fn leading_coefficient(&self, order: MonomialOrder) -> F {
        let term = self.leading_term(order);
        term.coefficient
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
        let mut scaled = self.clone();
        scaled.scale_assign(scale_factor);
        scaled
    }

    /// Scale every coefficient by `factor`, in the polynomial's own map.
    ///
    /// The form the MDS fold of a symbolic permutation wants: `scale` built a `Vec` of the scaled
    /// terms and then rehashed every one of them into a fresh map, so scaling a 266 815-term state
    /// word allocated it twice over to change only its values.
    ///
    /// One pass, because `retain` holds each coefficient by mutable reference: scaling and dropping
    /// the terms that went to zero — every term, when `factor` is zero — happen together.
    pub fn scale_assign(&mut self, factor: &F) {
        self.terms.retain(|_monomial, c| {
            *c *= *factor;
            !c.is_zero()
        });
    }
}

/// Display the polynomial in Sage-style.
impl<const N: usize, F: FiniteField> Display for SparseMultiPoly<N, F> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        // The zero polynomial has no terms, and an empty string is not a reading of it. Every
        // other polynomial has at least one term, so this is the only case needing a constant.
        if self.is_zero() {
            return write!(f, "0");
        }

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

            // A constant term is its coefficient and nothing else. `Monomial::one` displays as
            // the empty string — there are no variables to name — so writing the coefficient with
            // a trailing `*` would leave a dangling operator.
            if monomial.is_one() {
                write!(f, "{}", c)?;
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

impl<const N: usize, F: FiniteField> SparseMultiPoly<N, F> {
    /// The terms in descending lexicographic order: the canonical order for anything that writes
    /// them out, since the map's own iteration order depends on its capacity and insertion history.
    fn canonical_terms(&self) -> Vec<(&Monomial<N>, &F)> {
        let order = MonomialOrder::Lexicographic;
        let mut terms: Vec<_> = self.terms.iter().collect();
        terms.sort_unstable_by(|(a, _), (b, _)| order.cmp(a, b).reverse());
        terms
    }
}

/// Hash
impl<const N: usize, F: FiniteField> Hash for SparseMultiPoly<N, F> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.canonical_terms().hash(state);
    }
}

/// The terms as a map in canonical order. This is the wire shape the derived impl wrote, so data
/// serialized before #920 still deserializes and `Deserialize` stays derived.
struct CanonicalTerms<'a, const N: usize, F: FiniteField>(&'a SparseMultiPoly<N, F>);

impl<const N: usize, F: FiniteField> Serialize for CanonicalTerms<'_, N, F> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.collect_map(self.0.canonical_terms())
    }
}

impl<const N: usize, F: FiniteField> Serialize for SparseMultiPoly<N, F> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut state = serializer.serialize_struct("SparseMultiPoly", 1)?;
        state.serialize_field("terms", &CanonicalTerms(self))?;
        state.end()
    }
}

/// The derived shape, `SparseMultiPoly { terms: {..} }`, with the terms in canonical order.
impl<const N: usize, F: FiniteField> Debug for SparseMultiPoly<N, F> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        struct Terms<'a, const N: usize, F: FiniteField>(&'a SparseMultiPoly<N, F>);
        impl<const N: usize, F: FiniteField> Debug for Terms<'_, N, F> {
            fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
                f.debug_map().entries(self.0.canonical_terms()).finish()
            }
        }
        f.debug_struct("SparseMultiPoly")
            .field("terms", &Terms(self))
            .finish()
    }
}

#[cfg(any(test, feature = "proptest"))]
#[derive(Debug, Clone)]
pub struct ArbParams {
    /// How many (monomial, coefficient) pairs to draw. Duplicate monomials are combined and zero
    /// coefficients dropped, so the generated polynomial may end up with fewer terms than this.
    pub num_terms: usize,
}

#[cfg(any(test, feature = "proptest"))]
impl Default for ArbParams {
    fn default() -> Self {
        // Must be nonzero: drawing no pairs would make `any::<SparseMultiPoly>()` generate
        // nothing but the zero polynomial, and every property over it would hold vacuously.
        Self { num_terms: 4 }
    }
}

#[cfg(any(test, feature = "proptest"))]
impl<const N: usize, F: FiniteField + Arbitrary + 'static> Arbitrary for SparseMultiPoly<N, F> {
    type Parameters = ArbParams;

    fn arbitrary_with(args: Self::Parameters) -> Self::Strategy {
        (
            vec(any::<Monomial<N>>(), args.num_terms),
            vec(any::<F>(), args.num_terms),
        )
            .prop_map(|(monomials, coefficients)| {
                // Collecting into an array so that the size is known at compile time.
                let mut terms: Vec<Term<N, F>> = vec![];
                for (m, c) in monomials.into_iter().zip(coefficients) {
                    terms.push((c, m).into());
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
        identities::{One, Zero},
        poly::{
            multivariate::{sparse_multivariate_polynomial::SparseMultiPoly, term::Term},
            Monomial,
        },
        FiniteField,
    };

    /// A constant term displays as its coefficient, with no dangling multiplication sign.
    ///
    /// `Monomial::one` displays as the empty string, since it names no variables, so a constant
    /// term written as `coefficient * monomial` used to come out as `7*` — which is not a
    /// polynomial, and appeared in every example's output and every assertion message.
    #[test]
    fn test_display_of_a_constant_term() {
        type F = PrimeFieldElement64<337>;

        let seven: SparseMultiPoly<2, F> = SparseMultiPoly::new(&[(Monomial::one(), F::new(7))]);
        assert_eq!(seven.to_string(), "7");

        // The coefficient one is the one case that was already right.
        let one: SparseMultiPoly<2, F> = SparseMultiPoly::one();
        assert_eq!(one.to_string(), "1");

        // And beside a non-constant term.
        let shifted: SparseMultiPoly<2, F> = SparseMultiPoly::new(&[
            (Monomial::new(&[2, 0]), F::one()),
            (Monomial::one(), F::new(336)),
        ]);
        assert_eq!(shifted.to_string(), "x_0^2 + 336");
    }

    /// The zero polynomial displays as `0`, not as nothing at all.
    #[test]
    fn test_display_of_the_zero_polynomial() {
        type F = PrimeFieldElement64<337>;
        let zero: SparseMultiPoly<3, F> = SparseMultiPoly::zero();
        assert_eq!(zero.to_string(), "0");
    }

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

    /// `new` collects terms into a map, so the order they are supplied in does not matter.
    #[test]
    fn test_new_term_order_is_irrelevant() {
        type F = PrimeFieldElement64<337>;
        let x2y = (Monomial::<2>::new(&[2, 1]), F::new(5));
        let x = (Monomial::<2>::new(&[1, 0]), F::new(3));
        let one = (Monomial::<2>::new(&[0, 0]), F::new(7));

        let ascending = SparseMultiPoly::new(&[one, x, x2y]);
        let descending = SparseMultiPoly::new(&[x2y, x, one]);
        let shuffled = SparseMultiPoly::new(&[x, x2y, one]);

        assert_eq!(ascending, descending);
        assert_eq!(ascending, shuffled);
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

    /// The strategy is usable, equal polynomials hash equally, and no zero terms are retained.
    #[test]
    fn test_arbitrary_and_representation_are_sound() {
        use crate::test_support::{
            assert_hash_agrees_with_eq, assert_strategy_is_not_degenerate, draw,
        };
        use proptest::arbitrary::Arbitrary;
        type F = PrimeFieldElement64<541>;
        type Poly = SparseMultiPoly<2, F>;
        let strategy = Poly::arbitrary();
        assert_strategy_is_not_degenerate(&strategy, "SparseMultiPoly");

        let mut values = draw(&strategy, 32);
        // Every spelling of zero, including one built from terms that cancel.
        let x = Monomial::<2>::new(&[1, 0]);
        values.extend([
            Poly::zero(),
            Poly::default(),
            Poly::new(&[(x, F::zero())]),
            Poly::new(&[(x, F::new(3)), (x, F::new(538))]),
        ]);
        assert_hash_agrees_with_eq(&values, "SparseMultiPoly");

        for p in &values {
            for (monomial, coefficient) in p.terms.iter() {
                assert!(
                    !coefficient.is_zero(),
                    "{:?} retained a zero coefficient for {:?}",
                    p,
                    monomial
                );
            }
        }
    }

    /// Substituting a value for one variable removes it and leaves the rest untouched.
    #[test]
    fn test_substitute() {
        type F = PrimeFieldElement64<13>;
        let vars = ["x", "y"];
        let p: SparseMultiPoly<2, F> =
            SparseMultiPoly::parse("x^2*y + 3*x + 2*y + 5", vars).unwrap();

        // x = 2: 4y + 6 + 2y + 5 = 6y + 11
        let expected: SparseMultiPoly<2, F> = SparseMultiPoly::parse("6*y + 11", vars).unwrap();
        assert_eq!(p.substitute(0, F::new(2)), expected);

        // y = 1: x^2 + 3x + 2 + 5 = x^2 + 3x + 7
        let expected: SparseMultiPoly<2, F> =
            SparseMultiPoly::parse("x^2 + 3*x + 7", vars).unwrap();
        assert_eq!(p.substitute(1, F::new(1)), expected);

        // Substituting every variable leaves a constant equal to the full evaluation.
        let both = p.substitute(0, F::new(2)).substitute(1, F::new(1));
        assert!(both.is_constant());
        assert_eq!(
            both.eval(&[F::new(2), F::new(1)]),
            p.eval(&[F::new(2), F::new(1)])
        );
    }

    /// Substituting agrees with evaluating, for every point of a small field.
    #[test]
    fn test_substitute_agrees_with_eval() {
        type F = PrimeFieldElement64<7>;
        let vars = ["x", "y"];
        let p: SparseMultiPoly<2, F> =
            SparseMultiPoly::parse("x^2*y + 3*x*y^2 + 2*y + 5", vars).unwrap();

        for a in 0..7u64 {
            for b in 0..7u64 {
                let (x, y) = (F::new(a), F::new(b));
                // Substituting one variable then the other must match evaluating at once.
                let by_substitution = p.substitute(0, x).substitute(1, y);
                assert!(by_substitution.is_constant());
                assert_eq!(
                    by_substitution.eval(&[F::zero(), F::zero()]),
                    p.eval(&[x, y]),
                    "at ({}, {})",
                    a,
                    b
                );
            }
        }
    }

    /// Terms that cancel after substitution are dropped, not kept with a zero coefficient.
    #[test]
    fn test_substitute_drops_cancelled_terms() {
        type F = PrimeFieldElement64<13>;
        let vars = ["x", "y"];
        // At x = 1 this is y - y = 0.
        let p: SparseMultiPoly<2, F> = SparseMultiPoly::parse("x*y - y", vars).unwrap();
        let at_one = p.substitute(0, F::new(1));
        assert!(at_one.is_zero(), "expected zero, got {}", at_one);
        assert!(at_one.terms().is_empty());
    }

    /// The terms of `p`, all present, in an insertion history chosen to iterate differently.
    ///
    /// The same entries go into a map of far larger capacity, in the reverse of `p`'s iteration
    /// order. The two polynomials are equal; only the hash map's layout differs.
    fn rebuilt_in_another_layout<const N: usize, F: FiniteField>(
        p: &SparseMultiPoly<N, F>,
    ) -> SparseMultiPoly<N, F> {
        use crate::poly::multivariate::monomial_hash::MonomialMap;
        let mut terms: MonomialMap<N, F> =
            MonomialMap::with_capacity_and_hasher(4096, Default::default());
        let mut entries: Vec<_> = p.terms.iter().map(|(m, c)| (*m, *c)).collect();
        entries.reverse();
        terms.extend(entries);
        SparseMultiPoly { terms }
    }

    /// A polynomial whose two layouts in [`rebuilt_in_another_layout`] iterate differently.
    fn polynomial_with_two_layouts() -> (
        SparseMultiPoly<3, PrimeFieldElement64<541>>,
        SparseMultiPoly<3, PrimeFieldElement64<541>>,
    ) {
        type F = PrimeFieldElement64<541>;
        let terms: Vec<_> = (0..40u32)
            .map(|i| {
                (
                    Monomial::<3>::new(&[i % 5, i / 5, i % 3]),
                    F::new(u64::from(i) + 1),
                )
            })
            .collect();
        let a = SparseMultiPoly::new(&terms);
        let b = rebuilt_in_another_layout(&a);
        assert_eq!(a, b);
        // Without this the tests below could pass because the layouts happened to agree.
        let order = |p: &SparseMultiPoly<3, F>| p.terms.keys().copied().collect::<Vec<_>>();
        assert_ne!(
            order(&a),
            order(&b),
            "the two layouts must iterate differently"
        );
        (a, b)
    }

    /// Equal polynomials serialize to the same bytes, however their terms were inserted (#920).
    #[test]
    fn test_serialize_is_independent_of_insertion_history() {
        let (a, b) = polynomial_with_two_layouts();
        assert_eq!(
            bincode::serialize(&a).unwrap(),
            bincode::serialize(&b).unwrap()
        );
    }

    /// Equal polynomials print the same `Debug`, so test-failure output is stable too.
    #[test]
    fn test_debug_is_independent_of_insertion_history() {
        let (a, b) = polynomial_with_two_layouts();
        assert_eq!(format!("{:?}", a), format!("{:?}", b));
    }

    /// Terms are written in descending lexicographic order, the order `Hash` uses.
    #[test]
    fn test_serialize_and_debug_order_terms_lexicographically() {
        type F = PrimeFieldElement64<337>;
        let (x2, xy, y, one) = (
            Monomial::<2>::new(&[2, 0]),
            Monomial::<2>::new(&[1, 1]),
            Monomial::<2>::new(&[0, 1]),
            Monomial::<2>::one(),
        );
        let p: SparseMultiPoly<2, F> = SparseMultiPoly::new(&[
            (y, F::new(3)),
            (one, F::new(4)),
            (x2, F::new(1)),
            (xy, F::new(2)),
        ]);
        let sorted = [
            (x2, F::new(1)),
            (xy, F::new(2)),
            (y, F::new(3)),
            (one, F::new(4)),
        ];

        // bincode writes a map as its length followed by each key and value, exactly as it
        // writes a sequence of pairs, so the sorted pairs spell out the expected bytes.
        assert_eq!(
            bincode::serialize(&p).unwrap(),
            bincode::serialize(&sorted.to_vec()).unwrap()
        );

        let entries: Vec<String> = sorted
            .iter()
            .map(|(m, c)| format!("{:?}: {:?}", m, c))
            .collect();
        assert_eq!(
            format!("{:?}", p),
            format!("SparseMultiPoly {{ terms: {{{}}} }}", entries.join(", "))
        );
    }

    /// The shape the derived `Serialize` wrote before #920, kept to test compatibility against.
    #[derive(serde::Serialize, serde::Deserialize)]
    #[serde(rename = "SparseMultiPoly")]
    struct DerivedSparseMultiPoly<const N: usize, F: FiniteField> {
        #[serde(bound = "F: FiniteField")]
        terms: crate::poly::multivariate::monomial_hash::MonomialMap<N, F>,
    }

    /// Serialization round-trips, and its wire shape is the one the derived impl wrote: old data
    /// still deserializes, and new data still reads as the old shape.
    #[test]
    fn test_serde_round_trip_and_wire_compatibility() {
        use crate::test_support::draw;
        use proptest::arbitrary::Arbitrary;
        type Poly = SparseMultiPoly<3, PrimeFieldElement64<541>>;

        let mut values = draw(
            &Poly::arbitrary_with(super::ArbParams { num_terms: 12 }),
            64,
        );
        values.push(Poly::zero());
        values.push(polynomial_with_two_layouts().0);

        for p in &values {
            let bytes = bincode::serialize(p).unwrap();
            let recovered: Poly = bincode::deserialize(&bytes).unwrap();
            assert_eq!(&recovered, p);

            let legacy = DerivedSparseMultiPoly {
                terms: p.terms.clone(),
            };
            let legacy_bytes = bincode::serialize(&legacy).unwrap();
            let from_legacy: Poly = bincode::deserialize(&legacy_bytes).unwrap();
            assert_eq!(&from_legacy, p);

            let as_legacy: DerivedSparseMultiPoly<3, PrimeFieldElement64<541>> =
                bincode::deserialize(&bytes).unwrap();
            assert_eq!(as_legacy.terms, p.terms);
            // The same entries, so the same length: only their order may differ.
            assert_eq!(bytes.len(), legacy_bytes.len());
        }
    }
}
