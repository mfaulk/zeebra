//! Greatest common divisor, content, and squarefree decomposition of sparse multivariate
//! polynomials.
//!
//! `F[x_0, ..., x_{N-1}]` is not Euclidean, so the GCD is recursive: read the polynomials as
//! univariate in their highest occurring variable, with coefficients in the polynomial ring over
//! the remaining ones. That coefficient ring is a UFD but not a field, so the Euclidean step is
//! *pseudo*-division — scale the dividend by a power of the divisor's leading coefficient so the
//! division goes through — and the content is removed from every remainder to keep the
//! coefficients from growing. This is the classical primitive PRS.
//!
//! The recursion terminates because the main variable strictly decreases: the coefficients of a
//! polynomial read in `x_v` do not involve `x_v`, so the GCDs that compute a content are taken in
//! a smaller ring.
//!
//! Faster routes exist and are not taken here. The subresultant PRS replaces the per-step content
//! GCD with one exact division, and over a prime field Brown's modular algorithm evaluates the
//! problem down to univariate GCDs and lifts. Both are follow-ons; this is the form whose
//! coefficient growth is bounded by construction rather than by an argument.

use crate::{
    poly::{multivariate::sparse_multivariate_polynomial::SparseMultiPoly, MonomialOrder},
    FiniteField, KnownOrder, Monomial,
};

/// Why a squarefree decomposition could not be computed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SquarefreeError {
    /// The zero polynomial has no squarefree decomposition: it is divisible by every square.
    Zero,
    /// The method separates a factor of multiplicity `e` by differentiating, which multiplies the
    /// factor by `e` — and in characteristic `p` that is zero whenever `p` divides `e`. Refused
    /// rather than answered, because the wrong answer here is a *plausible* one.
    ///
    /// The guard is `characteristic > total degree`, which is sufficient: it bounds every
    /// multiplicity away from the characteristic and makes every irreducible factor separable in
    /// some variable, so `gcd(f, all partials)` is exactly `∏ g_i^(e_i - 1)`.
    CharacteristicTooSmall { characteristic: u128, degree: u64 },
}

impl std::fmt::Display for SquarefreeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Zero => write!(f, "the zero polynomial has no squarefree decomposition"),
            Self::CharacteristicTooSmall {
                characteristic,
                degree,
            } => write!(
                f,
                "a squarefree decomposition by differentiation needs a characteristic above the \
                 total degree {degree}, and this field's is {characteristic}"
            ),
        }
    }
}

impl std::error::Error for SquarefreeError {}

/// The image of the integer `n` in `F`, as `n` copies of one.
///
/// Built by double-and-add rather than through `F::new`, which takes an integer the prime fields
/// interpret as a residue but the binary and extension fields do not implement.
fn integer_in_field<F: FiniteField>(n: u32) -> F {
    let mut total = F::zero();
    let mut addend = F::one();
    let mut n = n;
    while n > 0 {
        if n & 1 == 1 {
            total += addend;
        }
        addend = addend + addend;
        n >>= 1;
    }
    total
}

impl<const N: usize, F: FiniteField> SparseMultiPoly<N, F> {
    /// The highest exponent of variable `index`, or zero if the variable does not occur.
    ///
    /// The zero polynomial reports zero, as [`Self::degree`] does — the degree of zero is
    /// undefined, and every caller here guards on [`Self::is_zero`] first.
    ///
    /// # Panics
    /// Panics if `index` is not a variable of this ring.
    pub fn degree_in(&self, index: usize) -> u32 {
        assert!(
            index < N,
            "index {} is not one of the {} variables",
            index,
            N
        );
        self.terms
            .keys()
            .map(|monomial| monomial.exponents()[index])
            .max()
            .unwrap_or(0)
    }

    /// The coefficients of `self` read as a polynomial in variable `index`.
    ///
    /// `result[e]` is the coefficient of `x_index^e`, a polynomial that does not involve
    /// `x_index`. The result has `degree_in(index) + 1` entries, and is empty for the zero
    /// polynomial.
    ///
    /// # Panics
    /// Panics if `index` is not a variable of this ring.
    pub fn coefficients_in(&self, index: usize) -> Vec<Self> {
        if self.is_zero() {
            return vec![];
        }
        let degree = self.degree_in(index);
        let mut buckets: Vec<Vec<(Monomial<N>, F)>> = vec![vec![]; degree as usize + 1];
        for (monomial, coefficient) in self.terms.iter() {
            let exponent = monomial.exponents()[index];
            let mut exponents = [0u32; N];
            exponents.copy_from_slice(monomial.exponents());
            exponents[index] = 0;
            buckets[exponent as usize].push((Monomial::new(&exponents), *coefficient));
        }
        buckets.iter().map(|terms| Self::new(terms)).collect()
    }

    /// The coefficient of `x_index^exponent`, as a polynomial not involving `x_index`.
    fn coefficient_in(&self, index: usize, exponent: u32) -> Self {
        let terms: Vec<(Monomial<N>, F)> = self
            .terms
            .iter()
            .filter(|(monomial, _)| monomial.exponents()[index] == exponent)
            .map(|(monomial, coefficient)| {
                let mut exponents = [0u32; N];
                exponents.copy_from_slice(monomial.exponents());
                exponents[index] = 0;
                (Monomial::new(&exponents), *coefficient)
            })
            .collect();
        Self::new(&terms)
    }

    /// The quotient `self / divisor`, or `None` if the division leaves a remainder.
    ///
    /// Division by a single polynomial is division by a Gröbner basis of the principal ideal it
    /// generates, so the remainder is zero exactly when the divisor divides — which makes this a
    /// decision procedure for divisibility and not merely a division that might work.
    pub fn exact_div(&self, divisor: &Self) -> Option<Self> {
        if divisor.is_zero() {
            return None;
        }
        let (quotient, remainder) = self.div_rem(divisor, MonomialOrder::Lexicographic);
        remainder.is_zero().then_some(quotient)
    }

    /// The formal partial derivative with respect to variable `index`.
    ///
    /// In characteristic `p` a term `x^e` whose exponent is divisible by `p` differentiates to
    /// zero, because `e` does: the integer exponent enters as a field element. That is correct
    /// and is what makes `squarefree_part` need a characteristic guard.
    ///
    /// # Panics
    /// Panics if `index` is not a variable of this ring.
    pub fn derivative(&self, index: usize) -> Self {
        assert!(
            index < N,
            "index {} is not one of the {} variables",
            index,
            N
        );
        let terms: Vec<(Monomial<N>, F)> = self
            .terms
            .iter()
            .filter(|(monomial, _)| monomial.exponents()[index] > 0)
            .map(|(monomial, coefficient)| {
                let exponent = monomial.exponents()[index];
                let mut exponents = [0u32; N];
                exponents.copy_from_slice(monomial.exponents());
                exponents[index] = exponent - 1;
                (
                    Monomial::new(&exponents),
                    *coefficient * integer_in_field::<F>(exponent),
                )
            })
            .collect();
        // Through `new`, which drops the terms whose exponent vanished in the characteristic.
        Self::new(&terms)
    }

    /// The content of `self` read as a polynomial in variable `index`: the GCD of its
    /// coefficients.
    ///
    /// A polynomial in the remaining variables, normalized as [`Self::gcd`] normalizes. Zero for
    /// the zero polynomial. Note that a common *numeric* factor is a unit and so contributes only
    /// the normalization, not a factor.
    ///
    /// # Panics
    /// Panics if `index` is not a variable of this ring.
    pub fn content(&self, index: usize) -> Self {
        let mut content = Self::zero();
        for coefficient in self.coefficients_in(index) {
            content = content.gcd(&coefficient);
            // Nothing below one is reachable, so the remaining coefficients cannot change it.
            if content.is_one() {
                break;
            }
        }
        content
    }

    /// `self` divided by its content in variable `index`.
    ///
    /// # Panics
    /// Panics if `index` is not a variable of this ring.
    pub fn primitive_part(&self, index: usize) -> Self {
        if self.is_zero() {
            return Self::zero();
        }
        let content = self.content(index);
        self.exact_div(&content)
            .expect("the content divides every coefficient")
    }

    /// The pseudo-remainder of `self` by `divisor`, both read as polynomials in variable `index`.
    ///
    /// The coefficient ring is not a field, so a division step cannot divide by the divisor's
    /// leading coefficient — it multiplies the dividend by it instead. The result therefore
    /// satisfies `lc^k * self = quotient * divisor + remainder` for some `k`, with
    /// `degree_in(index)` of the remainder below the divisor's. The power of `lc` is why the
    /// caller must take primitive parts: it is the coefficient growth the pseudo-division trades
    /// for exactness.
    ///
    /// Zero when the divisor has degree zero in `index`, since then the scaling alone clears the
    /// division.
    ///
    /// # Panics
    /// Panics if `divisor` is zero, or if `index` is not a variable of this ring.
    fn pseudo_remainder(&self, divisor: &Self, index: usize) -> Self {
        assert!(
            !divisor.is_zero(),
            "cannot pseudo-divide by the zero polynomial"
        );
        let divisor_degree = divisor.degree_in(index);
        if divisor_degree == 0 {
            return Self::zero();
        }
        let leading = divisor.coefficient_in(index, divisor_degree);

        let mut remainder = self.clone();
        while !remainder.is_zero() && remainder.degree_in(index) >= divisor_degree {
            let degree = remainder.degree_in(index);
            let shift: Self = Monomial::univariate(index, degree - divisor_degree).into();
            let top = remainder.coefficient_in(index, degree);
            // The two `x_index^degree` terms are both `leading * top * x^degree`, so the leading
            // term cancels and the loop strictly decreases the degree in `index`.
            remainder = &(&leading * &remainder) - &(&(&top * &shift) * divisor);
        }
        remainder
    }

    /// The greatest common divisor of `self` and `other`.
    ///
    /// Normalized so that the leading coefficient under [`MonomialOrder::Lexicographic`] is one,
    /// which pins down the unit the GCD is otherwise only defined up to. `gcd(0, f)` is `f`
    /// normalized and `gcd(0, 0)` is zero; the GCD of anything with a nonzero constant is one,
    /// since a nonzero constant is a unit.
    ///
    /// Recursive primitive PRS — see the module documentation for the shape and for the faster
    /// routes not taken.
    pub fn gcd(&self, other: &Self) -> Self {
        if self.is_zero() {
            return other.normalized();
        }
        if other.is_zero() {
            return self.normalized();
        }

        // The main variable: the highest in which either operand is not constant. Taking the
        // highest rather than the lowest is not required for correctness, only for determinism.
        let main = (0..N)
            .rev()
            .find(|&i| self.degree_in(i) > 0 || other.degree_in(i) > 0);
        let Some(variable) = main else {
            // Both are nonzero constants, hence units.
            return Self::one();
        };

        let self_content = self.content(variable);
        let other_content = other.content(variable);
        // One ring down: the contents do not involve `variable`.
        let content = self_content.gcd(&other_content);

        let mut a = self
            .exact_div(&self_content)
            .expect("the content divides every coefficient");
        let mut b = other
            .exact_div(&other_content)
            .expect("the content divides every coefficient");

        // Euclid on the primitive parts. Each remainder is made primitive before the next step,
        // which is what keeps the pseudo-division's powers of the leading coefficient from
        // accumulating.
        while !b.is_zero() {
            let remainder = a.pseudo_remainder(&b, variable);
            a = b;
            b = if remainder.is_zero() {
                Self::zero()
            } else {
                remainder.primitive_part(variable)
            };
        }

        (&content * &a).normalized()
    }

    /// Scaled so the leading coefficient under [`MonomialOrder::Lexicographic`] is one.
    ///
    /// The zero polynomial is returned unchanged: it has no leading coefficient to normalize.
    fn normalized(&self) -> Self {
        let leading = self.leading_coefficient(MonomialOrder::Lexicographic);
        if leading.is_zero() || leading.is_one() {
            self.clone()
        } else {
            self.scale(&leading.inverse())
        }
    }
}

impl<const N: usize, F: KnownOrder> SparseMultiPoly<N, F> {
    /// The squarefree part of `self`: the product of its distinct irreducible factors.
    ///
    /// `self / gcd(self, ∂self/∂x_0, ..., ∂self/∂x_{N-1})`, normalized. For
    /// `self = ∏ g_i^(e_i)` that GCD is `∏ g_i^(e_i - 1)`, so the quotient is `∏ g_i` — the
    /// radical. A nonzero constant is a unit and has squarefree part one.
    ///
    /// # Errors
    /// Refuses when the field's characteristic does not exceed the total degree, where
    /// differentiation can annihilate a repeated factor and the answer would be wrong rather than
    /// absent. See [`SquarefreeError`].
    pub fn squarefree_part(&self) -> Result<Self, SquarefreeError> {
        if self.is_zero() {
            return Err(SquarefreeError::Zero);
        }
        self.check_characteristic()?;

        let mut repeated = self.clone();
        for index in 0..N {
            repeated = repeated.gcd(&self.derivative(index));
            if repeated.is_one() {
                break;
            }
        }
        Ok(self
            .exact_div(&repeated)
            .expect("the repeated part divides")
            .normalized())
    }

    /// The squarefree decomposition of `self`, as `(factor, multiplicity)` pairs.
    ///
    /// The factors are squarefree, pairwise coprime, normalized, and listed at most once per
    /// multiplicity; their product with multiplicity is `self` up to that normalization. A unit
    /// decomposes into nothing.
    ///
    /// Built from repeated radicals rather than by Yun's algorithm: with
    /// `f_1 = self`, `r_i = radical(f_i)` and `f_{i+1} = f_i / r_i`, the radical `r_i` is the
    /// product of the factors of multiplicity at least `i`, so `r_i / r_{i+1}` is exactly the
    /// factor of multiplicity `i`. That costs one radical — `N + 1` GCDs — per distinct
    /// multiplicity, where Yun's costs one GCD; it is the cheaper thing to get right, and the
    /// faster form is a follow-on.
    ///
    /// # Errors
    /// As [`Self::squarefree_part`].
    pub fn squarefree_decomposition(&self) -> Result<Vec<(Self, u32)>, SquarefreeError> {
        if self.is_zero() {
            return Err(SquarefreeError::Zero);
        }

        // radicals[i] is the product of the factors of multiplicity at least i + 1. The sequence
        // ends at one, since each step strictly drops the degree while the radical is not one.
        let mut radicals: Vec<Self> = vec![];
        let mut remaining = self.normalized();
        loop {
            let radical = remaining.squarefree_part()?;
            let done = radical.is_one();
            radicals.push(radical.clone());
            if done {
                break;
            }
            remaining = remaining
                .exact_div(&radical)
                .expect("the radical divides its own polynomial");
        }

        let mut decomposition = vec![];
        for (i, window) in radicals.windows(2).enumerate() {
            let factor = window[0]
                .exact_div(&window[1])
                .expect("each radical divides the one before it");
            if !factor.is_one() {
                decomposition.push((factor.normalized(), i as u32 + 1));
            }
        }
        Ok(decomposition)
    }

    /// The characteristic guard [`Self::squarefree_part`] documents.
    fn check_characteristic(&self) -> Result<(), SquarefreeError> {
        let degree = self.degree();
        match F::characteristic_u128() {
            // A characteristic that does not fit in a `u128` exceeds any representable degree.
            None => Ok(()),
            Some(characteristic) if characteristic > degree as u128 => Ok(()),
            Some(characteristic) => Err(SquarefreeError::CharacteristicTooSmall {
                characteristic,
                degree,
            }),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        fields::{PrimeFieldElement64, Zp13},
        poly::{
            multivariate::{
                multivariate_gcd::SquarefreeError, sparse_multivariate_polynomial::SparseMultiPoly,
            },
            MonomialOrder,
        },
        FiniteField, Monomial, One, Zero,
    };

    type F = Zp13;
    type Poly = SparseMultiPoly<2, F>;

    const VARS: [&str; 2] = ["x", "y"];

    fn parse(s: &str) -> Poly {
        SparseMultiPoly::parse(s, VARS).unwrap()
    }

    /// Scale so the lexicographic leading coefficient is one, as the GCD's own normalization does.
    fn monic(p: &Poly) -> Poly {
        let lc = p.leading_coefficient(MonomialOrder::Lexicographic);
        if lc.is_zero() {
            p.clone()
        } else {
            p.scale(&lc.inverse())
        }
    }

    /// The GCD of two products sharing one factor is that factor.
    #[test]
    fn test_gcd_of_a_product_with_a_shared_factor() {
        let w = parse("x + y");
        let u = parse("x - y");
        let v = parse("x*y + 1");
        let f = &u * &w;
        let g = &v * &w;
        assert_eq!(f.gcd(&g), monic(&w));
        // And with the shared factor itself, the GCD is the whole of it.
        assert_eq!(f.gcd(&w), monic(&w));
    }

    /// Coprime inputs have GCD one.
    #[test]
    fn test_gcd_of_coprime_inputs_is_one() {
        let f = parse("x + 1");
        let g = parse("y + 1");
        assert!(f.gcd(&g).is_one());
        // A pair that shares no factor but is not linear either.
        assert!(parse("x^2 + 1").gcd(&parse("x^2 + x + 1")).is_one());
    }

    /// Zero is the GCD identity: `gcd(0, f)` is `f` normalized, and `gcd(0, 0)` is zero.
    #[test]
    fn test_gcd_with_zero() {
        let f = parse("3*x^2*y + 6*y");
        let zero = Poly::zero();
        assert_eq!(zero.gcd(&f), monic(&f));
        assert_eq!(f.gcd(&zero), monic(&f));
        assert!(zero.gcd(&zero).is_zero());
    }

    /// A nonzero constant is a unit, so its GCD with anything is one.
    #[test]
    fn test_gcd_with_a_constant_is_one() {
        let f = parse("x^2*y + x");
        assert!(f.gcd(&Poly::one()).is_one());
        assert!(f.gcd(&Poly::from(F::new(7))).is_one());
    }

    /// The GCD is symmetric, and the GCD of a polynomial with itself is itself up to a unit.
    #[test]
    fn test_gcd_is_symmetric_and_idempotent() {
        let f = parse("x^2*y + x*y + 2*x + 2");
        let g = parse("x*y + 2");
        assert_eq!(f.gcd(&g), g.gcd(&f));
        assert_eq!(f.gcd(&f), monic(&f));
    }

    /// `degree_in` reports the highest exponent of one variable, and zero when it is absent.
    #[test]
    fn test_degree_in() {
        let f = parse("x^3*y + x*y^4 + 7");
        assert_eq!(f.degree_in(0), 3);
        assert_eq!(f.degree_in(1), 4);
        assert_eq!(parse("x^2 + 1").degree_in(1), 0);
        assert_eq!(Poly::zero().degree_in(0), 0);
    }

    /// `coefficients_in` splits a polynomial into its coefficients as a polynomial in one variable.
    #[test]
    fn test_coefficients_in() {
        // Read in y: (x + 1) + (x^2)*y^2.
        let f = parse("x^2*y^2 + x + 1");
        let coefficients = f.coefficients_in(1);
        assert_eq!(coefficients.len(), 3);
        assert_eq!(coefficients[0], parse("x + 1"));
        assert!(coefficients[1].is_zero());
        assert_eq!(coefficients[2], parse("x^2"));
    }

    /// Content is the GCD of the coefficients in one variable; the primitive part is the quotient.
    #[test]
    fn test_content_and_primitive_part() {
        // Read in y: x*(y^2 + 1), so the content is x and the primitive part y^2 + 1.
        let f = parse("x*y^2 + x");
        assert_eq!(f.content(1), monic(&parse("x")));
        assert_eq!(f.primitive_part(1), parse("y^2 + 1"));

        // A numeric common factor is a unit, so it belongs to the content only as a scale.
        let g = parse("2*x*y + 4*x");
        assert_eq!(g.content(1), monic(&parse("x")));
        assert_eq!(&g.content(1) * &g.primitive_part(1), g);

        // Already primitive in y: the content is one.
        assert!(parse("x*y + 1").content(1).is_one());

        // The content of the zero polynomial is zero.
        assert!(Poly::zero().content(0).is_zero());
    }

    /// `exact_div` returns the quotient only when the division leaves no remainder.
    #[test]
    fn test_exact_div() {
        let f = parse("x^2 - y^2");
        let g = parse("x + y");
        assert_eq!(f.exact_div(&g), Some(parse("x - y")));
        assert_eq!(f.exact_div(&parse("x + 1")), None);
        // Nothing divides by zero, and zero is divisible by everything.
        assert_eq!(f.exact_div(&Poly::zero()), None);
        assert_eq!(Poly::zero().exact_div(&g), Some(Poly::zero()));
    }

    /// The formal partial derivative differentiates one variable and holds the others fixed.
    #[test]
    fn test_derivative() {
        let f = parse("x^3*y^2 + 5*x*y + 7*y + 2");
        assert_eq!(f.derivative(0), parse("3*x^2*y^2 + 5*y"));
        assert_eq!(f.derivative(1), parse("2*x^3*y + 5*x + 7"));
        // A variable the polynomial does not use differentiates to zero.
        assert!(parse("x^2 + 1").derivative(1).is_zero());
        // So does a constant.
        assert!(Poly::from(F::new(9)).derivative(0).is_zero());
    }

    /// In characteristic p the derivative of `x^p` vanishes, because the exponent does.
    #[test]
    fn test_derivative_vanishes_in_small_characteristic() {
        type Small = PrimeFieldElement64<3>;
        let f: SparseMultiPoly<2, Small> =
            SparseMultiPoly::new(&[(Monomial::new(&[3, 0]), Small::one())]);
        assert!(f.derivative(0).is_zero());
    }

    /// The squarefree part is the product of the distinct irreducible factors.
    #[test]
    fn test_squarefree_part() {
        let repeated = parse("x + y");
        let other = parse("x*y + 1");
        let f = &(&repeated * &repeated) * &other;
        let expected = monic(&(&repeated * &other));
        assert_eq!(f.squarefree_part().unwrap(), expected);

        // A squarefree polynomial is its own squarefree part, up to the normalization.
        assert_eq!(other.squarefree_part().unwrap(), monic(&other));
        // A unit has squarefree part one, and so does any nonzero constant.
        assert!(Poly::from(F::new(5)).squarefree_part().unwrap().is_one());
        // Zero has none.
        assert_eq!(Poly::zero().squarefree_part(), Err(SquarefreeError::Zero));
    }

    /// The squarefree decomposition recovers each distinct factor with its multiplicity.
    #[test]
    fn test_squarefree_decomposition() {
        let g1 = parse("x + 1");
        let g2 = parse("y + 1");
        let g3 = parse("x + y");
        // g1 * g2^2 * g3^3, of total degree 6 — below the characteristic, so the guard passes.
        let f = &(&g1 * &(&g2 * &g2)) * &(&g3 * &(&g3 * &g3));
        let mut decomposition = f.squarefree_decomposition().unwrap();
        decomposition.sort_by_key(|(_, multiplicity)| *multiplicity);

        assert_eq!(
            decomposition,
            vec![(monic(&g1), 1), (monic(&g2), 2), (monic(&g3), 3),]
        );

        // The decomposition multiplies back to the input, up to the leading normalization.
        let product = decomposition
            .iter()
            .fold(Poly::one(), |acc, (factor, multiplicity)| {
                (0..*multiplicity).fold(acc, |acc, _| &acc * factor)
            });
        assert_eq!(product, monic(&f));
    }

    /// A squarefree input decomposes into itself with multiplicity one.
    #[test]
    fn test_squarefree_decomposition_of_a_squarefree_polynomial() {
        let f = parse("x^2 - y^2");
        assert_eq!(f.squarefree_decomposition().unwrap(), vec![(monic(&f), 1)]);
        // A unit has no factors at all.
        assert!(Poly::one().squarefree_decomposition().unwrap().is_empty());
        assert_eq!(
            Poly::zero().squarefree_decomposition(),
            Err(SquarefreeError::Zero)
        );
    }

    /// Squarefree decomposition is refused, not guessed, when the characteristic is too small.
    #[test]
    fn test_squarefree_part_is_refused_in_small_characteristic() {
        type Small = PrimeFieldElement64<3>;
        // (x + y)^3 has total degree 3, which the characteristic does not exceed.
        let factor: SparseMultiPoly<2, Small> = SparseMultiPoly::new(&[
            (Monomial::new(&[1, 0]), Small::one()),
            (Monomial::new(&[0, 1]), Small::one()),
        ]);
        let cube = &(&factor * &factor) * &factor;
        assert_eq!(
            cube.squarefree_part(),
            Err(SquarefreeError::CharacteristicTooSmall {
                characteristic: 3,
                degree: 3,
            })
        );
    }

    /// The GCD of three variables' worth of input still finds a shared factor.
    #[test]
    fn test_gcd_in_three_variables() {
        let vars = ["x", "y", "z"];
        let w: SparseMultiPoly<3, F> = SparseMultiPoly::parse("x*z + y", vars).unwrap();
        let u: SparseMultiPoly<3, F> = SparseMultiPoly::parse("y*z + 1", vars).unwrap();
        let v: SparseMultiPoly<3, F> = SparseMultiPoly::parse("x + z^2", vars).unwrap();
        let f = &u * &w;
        let g = &v * &w;
        let d = f.gcd(&g);
        assert_eq!(d.exact_div(&w).map(|q| q.is_one()), Some(true));
        assert!(f.exact_div(&d).is_some());
        assert!(g.exact_div(&d).is_some());
    }

    mod brute_force {
        use super::*;

        type Small = PrimeFieldElement64<3>;
        type SmallPoly = SparseMultiPoly<2, Small>;

        /// Every monomial in two variables of total degree at most `max`.
        fn monomials(max: u32) -> Vec<Monomial<2>> {
            (0..=max)
                .flat_map(|d| (0..=d).map(move |i| Monomial::new(&[i, d - i])))
                .collect()
        }

        /// Every polynomial over `F` supported on `monomials`.
        fn all_polynomials(monomials: &[Monomial<2>]) -> Vec<SmallPoly> {
            let elements = [Small::new(0), Small::new(1), Small::new(2)];
            let mut polynomials = vec![];
            let count = elements.len().pow(monomials.len() as u32);
            for code in 0..count {
                let mut digits = code;
                let terms: Vec<(Monomial<2>, Small)> = monomials
                    .iter()
                    .map(|monomial| {
                        let coefficient = elements[digits % elements.len()];
                        digits /= elements.len();
                        (*monomial, coefficient)
                    })
                    .collect();
                polynomials.push(SmallPoly::new(&terms));
            }
            polynomials
        }

        /// `gcd` satisfies the defining property against an exhaustive search over a small field.
        ///
        /// Not "the same answer as the brute force", which is not well defined — a GCD is only
        /// unique up to a unit, and several candidates share the maximal degree. The property
        /// checked is the one that characterizes it: the result divides both inputs, and every
        /// common divisor divides the result.
        #[test]
        fn test_gcd_has_the_universal_property_over_a_small_field() {
            let linear = all_polynomials(&monomials(1));
            // Inputs are products of two linear factors, so every common divisor of a pair has
            // total degree at most two and the candidate set below is exhaustive.
            let candidates = all_polynomials(&monomials(2));

            let mut checked = 0;
            for (i, w) in linear.iter().enumerate() {
                if w.is_zero() || w.is_constant() {
                    continue;
                }
                let u = &linear[(i * 7 + 3) % linear.len()];
                let v = &linear[(i * 11 + 5) % linear.len()];
                let f = u * w;
                let g = v * w;
                let d = f.gcd(&g);

                assert!(f.exact_div(&d).is_some(), "gcd {d} does not divide {f}");
                assert!(g.exact_div(&d).is_some(), "gcd {d} does not divide {g}");

                for candidate in &candidates {
                    if candidate.is_zero() {
                        continue;
                    }
                    if f.exact_div(candidate).is_some() && g.exact_div(candidate).is_some() {
                        assert!(
                            d.exact_div(candidate).is_some(),
                            "the common divisor {candidate} of {f} and {g} does not divide \
                             the gcd {d}"
                        );
                    }
                }
                checked += 1;
            }
            assert!(checked > 0, "the brute force checked nothing");
        }
    }

    mod over_every_field {
        use crate::{
            poly::{multivariate::sparse_multivariate_polynomial::SparseMultiPoly, MonomialOrder},
            FiniteField, Monomial,
        };
        use rand::{prelude::StdRng, Rng, SeedableRng};

        /// A polynomial with `num_terms` drawn monomials of exponent at most one per variable.
        ///
        /// Written out rather than reached through `Arbitrary`, whose strategy is boxed and so
        /// requires `F: 'static` — a bound the generic body `for_each_field!` writes cannot state.
        fn random_poly<const N: usize, F: FiniteField, R: Rng + rand::CryptoRng>(
            num_terms: usize,
            rng: &mut R,
        ) -> SparseMultiPoly<N, F> {
            let terms: Vec<(Monomial<N>, F)> = (0..num_terms)
                .map(|_| {
                    let mut exponents = [0u32; N];
                    for e in exponents.iter_mut() {
                        *e = rng.gen_range(0..2);
                    }
                    (Monomial::new(&exponents), F::random(rng))
                })
                .collect();
            SparseMultiPoly::new(&terms)
        }

        /// The GCD divides both inputs, is symmetric, and is normalized to a monic leading term.
        pub(super) fn assert_gcd_contract_holds<const N: usize, F: FiniteField>() {
            let mut rng = StdRng::seed_from_u64(0x9cd0_1234);
            let mut nontrivial = 0;
            for _ in 0..12 {
                let u = random_poly::<N, F, _>(3, &mut rng);
                let v = random_poly::<N, F, _>(3, &mut rng);
                let w = random_poly::<N, F, _>(3, &mut rng);
                if u.is_zero() || v.is_zero() || w.is_zero() {
                    continue;
                }
                let f = &u * &w;
                let g = &v * &w;
                let d = f.gcd(&g);

                // The GCD divides both inputs.
                assert!(f.exact_div(&d).is_some(), "gcd does not divide f");
                assert!(g.exact_div(&d).is_some(), "gcd does not divide g");
                // The shared factor divides the GCD, so nothing of it was lost.
                assert!(d.exact_div(&w).is_some(), "the shared factor was lost");
                // Symmetric, and normalized.
                assert_eq!(d, g.gcd(&f));
                assert!(d.leading_coefficient(MonomialOrder::Lexicographic).is_one());
                // No operation may leave a zero coefficient in the map.
                assert!(d.terms().values().all(|c| !c.is_zero()));
                nontrivial += 1;
            }
            assert!(nontrivial > 0, "every drawn case was degenerate");
        }
    }

    // The GCD contract holds over every field, at two arities.
    for_each_field!(
        fn the_gcd_contract_holds<F>() {
            over_every_field::assert_gcd_contract_holds::<2, F>();
            over_every_field::assert_gcd_contract_holds::<3, F>();
        }
    );
}
