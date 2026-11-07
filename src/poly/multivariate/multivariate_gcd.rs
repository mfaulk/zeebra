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
//! Two routes do that Euclidean step, and [`GcdRoute`] chooses. The **primitive PRS** removes the
//! content from every pseudo-remainder — nothing can grow, so the coefficient bound is by
//! construction, and a content is itself a recursive GCD so it pays one per step. **Collins'
//! subresultant PRS** divides each pseudo-remainder by `g * h^delta` instead, which the
//! fundamental theorem of subresultants makes exact: one division per step and three content GCDs
//! for the whole computation. Coefficients can then grow, but by a bound rather than unboundedly,
//! since the sequence's entries are subresultants and so determinants of submatrices of the
//! inputs' Sylvester matrix.
//!
//! The subresultant route is the default, on correctness evidence — the two are asserted to return
//! the same value exhaustively and over every field — and **not on a measurement**. The operation
//! count is asserted (`test_the_subresultant_route_takes_fewer_content_gcds`); the wall clock is
//! not, and #407 is where that belongs.
//!
//! Brown's modular algorithm, which evaluates the problem down to univariate GCDs over a prime
//! field and lifts, is the route that changes the asymptotics and is not here.

use crate::{
    poly::{multivariate::sparse_multivariate_polynomial::SparseMultiPoly, MonomialOrder},
    FiniteField, KnownOrder, Monomial,
};

/// Which polynomial-remainder sequence [`SparseMultiPoly::gcd`] runs.
///
/// Both routes are the same recursion — read the operands as univariate in their highest occurring
/// variable, over the polynomial ring in the rest — and differ only in what they do to a
/// pseudo-remainder before the next Euclidean step. The GCD they return is the same value; a
/// reduced GCD is unique once normalized.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub enum GcdRoute {
    /// Take the primitive part of every pseudo-remainder.
    ///
    /// #128's route. Nothing can grow, because a content is divided out at every step — so the
    /// coefficient bound is by construction. A content is itself a recursive GCD in a smaller
    /// ring, so this pays one such GCD per Euclidean step, which is the cost
    /// [`Self::SubresultantPrs`] removes. Kept as the reference the other is differentially tested
    /// against.
    PrimitivePrs,

    /// Divide every pseudo-remainder by `g * h^delta`, carrying `g` and `h` across steps.
    ///
    /// Collins' subresultant PRS, and the default. One *exact division* per step instead of a
    /// recursive GCD: three content GCDs for the whole computation rather than one per step.
    /// Coefficients can grow, but by a bound rather than unboundedly — the sequence's entries are
    /// subresultants, determinants of submatrices of the inputs' Sylvester matrix, so Hadamard's
    /// inequality bounds them in terms of the inputs alone.
    ///
    /// **Default on correctness evidence, not on a measurement.** The two routes are asserted to
    /// return the same value by the exhaustive brute force, by `for_each_field!` at two arities,
    /// and case by case; whether it is faster in wall clock on any particular machine is
    /// unmeasured, and #407 is where that measurement belongs.
    #[default]
    SubresultantPrs,
}

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
        self.content_by(index, GcdRoute::default())
    }

    /// [`Self::content`] with the GCD route chosen, since a content *is* a GCD.
    ///
    /// # Panics
    /// As [`Self::content`].
    pub fn content_by(&self, index: usize, route: GcdRoute) -> Self {
        #[cfg(test)]
        content_calls::record();
        let mut content = Self::zero();
        for coefficient in self.coefficients_in(index) {
            content = content.gcd_by(&coefficient, route);
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
        self.primitive_part_by(index, GcdRoute::default())
    }

    /// [`Self::primitive_part`] with the GCD route chosen.
    ///
    /// # Panics
    /// As [`Self::primitive_part`].
    pub fn primitive_part_by(&self, index: usize, route: GcdRoute) -> Self {
        if self.is_zero() {
            return Self::zero();
        }
        let content = self.content_by(index, route);
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
    /// **`k` is the number of division steps and not `delta + 1`**, which is fine for the
    /// primitive PRS — it divides the content out of every remainder, so the power is irrelevant —
    /// and is exactly what the subresultant PRS cannot use. See
    /// [`Self::pseudo_remainder_scaled`].
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

    /// The pseudo-remainder with **exactly** `delta + 1` powers of the divisor's leading
    /// coefficient, where `delta` is the difference of the two degrees in `index`.
    ///
    /// `lc(divisor)^(delta + 1) * self = quotient * divisor + remainder`, with the remainder's
    /// degree in `index` below the divisor's. That identity, not merely "some power", is what the
    /// subresultant divisibility theorem is stated over — so [`Self::pseudo_remainder`] cannot be
    /// used in its place: it multiplies once per division *step*, and a step that skips a degree
    /// leaves the power short. A gapped dividend such as `x^6 + 1` against `x^2 + 1` takes three
    /// steps where `delta + 1` is five.
    ///
    /// The shortfall is made up at the end rather than inside the loop, which is both cheaper and
    /// the standard statement: each skipped degree contributes one unused factor of `lc`.
    ///
    /// # Panics
    /// Panics if `divisor` is zero, if `index` is not a variable of this ring, or if the divisor
    /// is constant in `index` while `self` is not — a caller in that position has no `delta` to
    /// speak of and wants [`Self::pseudo_remainder`].
    fn pseudo_remainder_scaled(&self, divisor: &Self, index: usize) -> Self {
        assert!(
            !divisor.is_zero(),
            "cannot pseudo-divide by the zero polynomial"
        );
        let divisor_degree = divisor.degree_in(index);
        assert!(
            divisor_degree > 0,
            "a divisor constant in x_{index} has no degree difference to scale by"
        );
        if self.is_zero() || self.degree_in(index) < divisor_degree {
            return self.clone();
        }

        let leading = divisor.coefficient_in(index, divisor_degree);
        let mut unused = self.degree_in(index) - divisor_degree + 1;
        let mut remainder = self.clone();
        while !remainder.is_zero() && remainder.degree_in(index) >= divisor_degree {
            let degree = remainder.degree_in(index);
            let shift: Self = Monomial::univariate(index, degree - divisor_degree).into();
            let top = remainder.coefficient_in(index, degree);
            remainder = &(&leading * &remainder) - &(&(&top * &shift) * divisor);
            unused -= 1;
        }
        // One factor of `lc` per degree the loop skipped, so the identity holds with `delta + 1`
        // exactly and not with however many steps the degrees happened to take.
        (0..unused).fold(remainder, |remainder, _| &leading * &remainder)
    }

    /// The greatest common divisor of `self` and `other`.
    ///
    /// Normalized so that the leading coefficient under [`MonomialOrder::Lexicographic`] is one,
    /// which pins down the unit the GCD is otherwise only defined up to. `gcd(0, f)` is `f`
    /// normalized and `gcd(0, 0)` is zero; the GCD of anything with a nonzero constant is one,
    /// since a nonzero constant is a unit.
    ///
    /// [`GcdRoute::default`] — Collins' subresultant PRS. [`Self::gcd_by`] chooses.
    pub fn gcd(&self, other: &Self) -> Self {
        self.gcd_by(other, GcdRoute::default())
    }

    /// [`Self::gcd`] by a chosen route.
    ///
    /// Both routes are recursive in the same way and differ only in what they do to a
    /// pseudo-remainder before the next Euclidean step: see [`GcdRoute`].
    pub fn gcd_by(&self, other: &Self, route: GcdRoute) -> Self {
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

        let self_content = self.content_by(variable, route);
        let other_content = other.content_by(variable, route);
        // One ring down: the contents do not involve `variable`.
        let content = self_content.gcd_by(&other_content, route);

        let mut a = self
            .exact_div(&self_content)
            .expect("the content divides every coefficient");
        let mut b = other
            .exact_div(&other_content)
            .expect("the content divides every coefficient");
        if a.degree_in(variable) < b.degree_in(variable) {
            std::mem::swap(&mut a, &mut b);
        }

        let primitive = match route {
            GcdRoute::PrimitivePrs => Self::primitive_prs(a, b, variable),
            GcdRoute::SubresultantPrs => Self::subresultant_prs(a, b, variable),
        };
        (&content * &primitive).normalized()
    }

    /// Euclid on the primitive parts, with the primitive part taken of every pseudo-remainder.
    ///
    /// #128's route, kept as the reference the subresultant one is differentially tested against.
    /// `a` and `b` are primitive in `variable`; the result is their GCD, primitive in `variable`.
    ///
    /// Taking a primitive part is what keeps the pseudo-division's powers of the leading
    /// coefficient from accumulating — and a content is itself a recursive GCD in a smaller ring,
    /// so this pays one such GCD **per Euclidean step**. That is the cost the subresultant route
    /// exists to remove.
    ///
    /// The inner content GCDs recurse through this same route explicitly rather than through the
    /// default: a reference implementation that followed whatever the default happened to be would
    /// stop being a reference the moment the default changed.
    fn primitive_prs(mut a: Self, mut b: Self, variable: usize) -> Self {
        while !b.is_zero() {
            let remainder = a.pseudo_remainder(&b, variable);
            a = b;
            b = if remainder.is_zero() {
                Self::zero()
            } else {
                remainder.primitive_part_by(variable, GcdRoute::PrimitivePrs)
            };
        }
        a
    }

    /// Collins' subresultant PRS: one exact division per step where the primitive PRS takes a
    /// content.
    ///
    /// `a` and `b` are primitive in `variable`, nonzero, with `deg_v(a) >= deg_v(b)`; the result is
    /// their GCD, primitive in `variable`.
    ///
    /// Carries `g = lc(a)` and `h` across steps, and divides each pseudo-remainder by
    /// `g * h^delta` instead of by its content. The fundamental theorem of subresultants is what
    /// makes that division exact, and it is also what bounds the coefficients: the entries of the
    /// sequence *are* subresultants, which are determinants of submatrices of the Sylvester matrix
    /// of the inputs, so their size is bounded by Hadamard's inequality on the inputs alone. The
    /// primitive PRS bounds them by construction — nothing can grow, since every remainder is made
    /// primitive — and pays a recursive GCD per step for it; this bounds them by a theorem and pays
    /// one exact division. **Which is faster here is unmeasured**; what is structural is the GCD
    /// count: `3` recursive GCDs in a smaller ring in total, against one per Euclidean step.
    ///
    /// # Panics
    /// Panics if either division the subresultant theorem makes exact is not — which would be a
    /// defect in this function or in `exact_div`, not an input it cannot handle.
    fn subresultant_prs(mut a: Self, mut b: Self, variable: usize) -> Self {
        // `b` is primitive and constant in `variable`, so its content is one and it is a unit.
        if b.degree_in(variable) == 0 {
            return Self::one();
        }

        let mut g = Self::one();
        let mut h = Self::one();
        loop {
            let delta = a.degree_in(variable) - b.degree_in(variable);
            let remainder = a.pseudo_remainder_scaled(&b, variable);
            if remainder.is_zero() {
                // `b` divides `a` up to content, and `b` is not primitive — the route does not
                // make it so — which is why the primitive part is taken here and not at the top.
                return b.primitive_part_by(variable, GcdRoute::SubresultantPrs);
            }
            if remainder.degree_in(variable) == 0 {
                // A nonzero remainder of degree zero in `variable`. The GCD divides it and is
                // primitive, so it has degree zero and content one: a unit. The primitive parts
                // are coprime, and the whole GCD is the content the caller already has.
                return Self::one();
            }

            let divisor = &g * &Self::power(&h, delta);
            let next = remainder
                .exact_div(&divisor)
                .expect("the subresultant divisibility theorem makes this division exact");
            a = b;
            b = next;
            g = a.coefficient_in(variable, a.degree_in(variable));
            // `h <- h^(1 - delta) * g^delta`, which for `delta = 0` leaves `h` alone and otherwise
            // is the exact division below. Written this way because a negative exponent is not a
            // thing a polynomial ring has.
            if delta > 0 {
                h = Self::power(&g, delta)
                    .exact_div(&Self::power(&h, delta - 1))
                    .expect("the subresultant h-update is an exact division");
            }
        }
    }

    /// `base^exponent`, by repeated multiplication. `base^0` is one.
    fn power(base: &Self, exponent: u32) -> Self {
        (0..exponent).fold(Self::one(), |product, _| &product * base)
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
    /// The radical, normalized. A nonzero constant is a unit and has squarefree part one.
    ///
    /// `self / gcd(self, ∂self/∂x_0, ..., ∂self/∂x_{N-1})` where the characteristic exceeds the
    /// total degree, which is `∏ g_i` for `self = ∏ g_i^(e_i)` and costs `N + 1` GCDs. Otherwise
    /// that quotient is only *part* of the radical — see [`Self::squarefree_decomposition`] — and
    /// the radical comes from the decomposition instead.
    ///
    /// # Errors
    /// [`SquarefreeError::Zero`] only. Before #408 this also refused in small characteristic.
    pub fn squarefree_part(&self) -> Result<Self, SquarefreeError> {
        match self.gradient_radical() {
            Ok(radical) => Ok(radical),
            Err(SquarefreeError::Zero) => Err(SquarefreeError::Zero),
            // The characteristic divides some multiplicity, or might: the gradient alone cannot
            // see every factor, so the radical is assembled from the decomposition, which can.
            Err(SquarefreeError::CharacteristicTooSmall { .. }) => Ok(self
                .squarefree_decomposition()?
                .into_iter()
                .fold(Self::one(), |product, (factor, _)| &product * &factor)
                .normalized()),
        }
    }

    /// The squarefree decomposition of `self`, as `(factor, multiplicity)` pairs.
    ///
    /// The factors are squarefree, pairwise coprime, normalized, and listed at most once per
    /// multiplicity; their product with multiplicity is `self` up to that normalization. A unit
    /// decomposes into nothing. **Defined in every characteristic**, including the one where the
    /// derivative is blind.
    ///
    /// # Why the derivative is not enough
    /// For `self = ∏ g_i^(e_i)`, `gcd(self, ∇self)` is
    /// `∏_{p | e_i} g_i^(e_i) * ∏_{p ∤ e_i} g_i^(e_i - 1)`: a factor whose multiplicity the
    /// characteristic divides contributes *all* of itself, because `e_i` enters each derivative as
    /// a field element and vanishes. So `self / gcd(self, ∇self)` is the product of the distinct
    /// factors whose multiplicity `p` does not divide — the **visible** ones — and over GF(2) every
    /// even multiplicity is invisible. #128 refused rather than answer here, and that refusal was a
    /// fact about the method and not about the problem.
    ///
    /// # The two halves
    /// *The visible half* is resolved by a ladder: with `P_1` the visible part and `Q_1 = f / P_1`,
    /// `P_{j+1} = gcd(P_j, Q_j)` and `Q_{j+1} = Q_j / P_{j+1}`. `P_j` is the product of the visible
    /// factors of multiplicity at least `j`, so `P_j / P_{j+1}` is the one of multiplicity exactly
    /// `j`. That is **one GCD per multiplicity**, between a squarefree `P_j` that only shrinks,
    /// where [`Self::squarefree_decomposition_by_radicals`] pays a whole radical — `N + 1` GCDs
    /// over operands that stay large — for each.
    ///
    /// *The invisible half* is whatever the ladder leaves, which is `∏_{p | e_i} g_i^(e_i)`: every
    /// multiplicity is a multiple of `p`, so it is a `p`-th power, and [`Self::pth_root`] takes the
    /// root exactly. Recursing on the root gives those factors with multiplicities divided by `p`,
    /// and multiplying each by `p` puts them back. Each level divides the degree by at least `p`,
    /// so the recursion is at most `log_p(degree)` deep.
    ///
    /// # Not Yun's algorithm, and why
    /// #408 asked for Yun's. Yun's recurrence is univariate: it carries `b_i` and `c_i` and forms
    /// `d_i = b_i' - c_i`, one derivative and one GCD per multiplicity. Generalized to `N`
    /// variables honestly it carries a `d_i` per variable and needs `gcd(b_i, d_i^(0), …,
    /// d_i^(N-1))` — `N` GCDs per multiplicity, which is *worse* than the ladder above and no
    /// better than the radicals it was meant to replace. The ladder achieves the cost Yun's is
    /// wanted for, one GCD per multiplicity, with the gradient taken once rather than once per
    /// level. Stated here rather than in a commit message because the issue names the other
    /// algorithm.
    ///
    /// # Errors
    /// [`SquarefreeError::Zero`] only.
    pub fn squarefree_decomposition(&self) -> Result<Vec<(Self, u32)>, SquarefreeError> {
        if self.is_zero() {
            return Err(SquarefreeError::Zero);
        }
        let mut decomposition = Vec::new();
        self.normalized().collect_squarefree(1, &mut decomposition);
        Ok(decomposition)
    }

    /// Append `self`'s decomposition to `out`, with every multiplicity scaled by `scale`.
    ///
    /// `self` must be nonzero and normalized. `scale` is the power of the characteristic this
    /// level was reached through: a factor of multiplicity `j` here had multiplicity `j * scale` in
    /// the polynomial the recursion started from.
    fn collect_squarefree(&self, scale: u32, out: &mut Vec<(Self, u32)>) {
        if self.is_one() {
            return;
        }

        let visible = match self.gradient_radical_unguarded() {
            Some(visible) => visible,
            // A unit, which `is_one` above has already excluded after normalization.
            None => return,
        };

        let mut level = visible;
        let mut rest = self
            .exact_div(&level)
            .expect("the visible part divides its own polynomial");
        let mut multiplicity = 1u32;
        while !level.is_one() {
            let next = level.gcd(&rest);
            rest = rest
                .exact_div(&next)
                .expect("a visible factor of the next level occurs again in the remainder");
            let factor = level
                .exact_div(&next)
                .expect("the next level divides this one")
                .normalized();
            if !factor.is_one() {
                out.push((factor, multiplicity * scale));
            }
            level = next;
            multiplicity += 1;
        }

        // What the ladder left is `∏_{p | e_i} g_i^(e_i)`, a `p`-th power.
        let rest = rest.normalized();
        if rest.is_one() {
            return;
        }
        let characteristic = F::characteristic_u128()
            .and_then(|characteristic| u32::try_from(characteristic).ok())
            // A characteristic that divides a multiplicity of a nonzero polynomial is at most its
            // total degree, which a `Monomial`'s exponents hold in a `u32`.
            .expect("a characteristic that divides a multiplicity fits the degree it divides");
        let root = rest
            .pth_root()
            .expect("what the ladder leaves has every multiplicity divisible by p");
        root.collect_squarefree(scale * characteristic, out);
    }

    /// The `p`-th root of `self`, or `None` if `self` is not a `p`-th power.
    ///
    /// In characteristic `p` the Frobenius map `c -> c^p` is a ring homomorphism, so
    /// `(Σ d_α x^α)^p = Σ d_α^p x^(pα)`: a `p`-th power is exactly a polynomial every one of whose
    /// exponents `p` divides, and its root divides the exponents and takes the `p`-th root of each
    /// coefficient. Every finite field is perfect, so each coefficient has one and it is unique.
    ///
    /// The coefficient root is `c^(q/p)`, since `(c^(q/p))^p = c^q = c`. The exponent is formed on
    /// the order's limbs rather than on a machine integer, so nothing here caps the field's size;
    /// over a prime field `q/p` is one and the root is the identity, which is correct because
    /// Frobenius is the identity on GF(p).
    ///
    /// `None` also for a field whose characteristic exceeds a `u32`, which divides no nonzero
    /// exponent this ring can hold — so no non-constant polynomial over it is a `p`-th power.
    pub fn pth_root(&self) -> Option<Self> {
        if self.is_zero() {
            return Some(Self::zero());
        }
        let characteristic = match F::characteristic_limbs() {
            [characteristic] => u32::try_from(*characteristic).ok()?,
            _ => return None,
        };
        let exponent = divide_limbs(F::order_limbs(), u64::from(characteristic));

        let mut terms: Vec<(Monomial<N>, F)> = Vec::with_capacity(self.terms.len());
        for (monomial, coefficient) in self.terms.iter() {
            let mut exponents = [0u32; N];
            for (root, exponent) in exponents.iter_mut().zip(monomial.exponents()) {
                if !exponent.is_multiple_of(characteristic) {
                    return None;
                }
                *root = exponent / characteristic;
            }
            terms.push((Monomial::new(&exponents), coefficient.pow_limbs(&exponent)));
        }
        Some(Self::new(&terms))
    }

    /// The squarefree decomposition built from repeated radicals: the reference implementation.
    ///
    /// #128's form, kept as the thing [`Self::squarefree_decomposition`] is differentially tested
    /// against rather than deleted. With `f_1 = self`, `r_i = radical(f_i)` and
    /// `f_{i+1} = f_i / r_i`, the radical `r_i` is the product of the factors of multiplicity at
    /// least `i`, so `r_i / r_{i+1}` is the factor of multiplicity exactly `i`. Simple enough to be
    /// obviously correct, and that is its whole job.
    ///
    /// It is a reference and not the implementation for two reasons: it costs a radical — `N + 1`
    /// GCDs over operands that do not shrink — per distinct multiplicity, and it is **only valid
    /// where differentiation sees every factor**, so it still refuses in small characteristic.
    /// That refusal is a true statement about this method.
    ///
    /// # Errors
    /// [`SquarefreeError::Zero`], and [`SquarefreeError::CharacteristicTooSmall`] when the
    /// characteristic does not exceed the total degree.
    pub fn squarefree_decomposition_by_radicals(
        &self,
    ) -> Result<Vec<(Self, u32)>, SquarefreeError> {
        if self.is_zero() {
            return Err(SquarefreeError::Zero);
        }

        // radicals[i] is the product of the factors of multiplicity at least i + 1. The sequence
        // ends at one, since each step strictly drops the degree while the radical is not one.
        let mut radicals: Vec<Self> = vec![];
        let mut remaining = self.normalized();
        loop {
            let radical = remaining.gradient_radical()?;
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

    /// `self / gcd(self, ∇self)`, refused where differentiation can be blind to a factor.
    ///
    /// The shape [`Self::squarefree_part`] had before #408, kept because
    /// [`Self::squarefree_decomposition_by_radicals`] is built from it: a reference implementation
    /// has to be what it was, not a wrapper over the implementation it is meant to check.
    ///
    /// # Errors
    /// As [`Self::squarefree_decomposition_by_radicals`].
    fn gradient_radical(&self) -> Result<Self, SquarefreeError> {
        if self.is_zero() {
            return Err(SquarefreeError::Zero);
        }
        self.check_characteristic()?;
        Ok(self
            .gradient_radical_unguarded()
            .expect("a nonzero polynomial has a gradient radical"))
    }

    /// `self / gcd(self, ∇self)`, normalized, with no characteristic guard.
    ///
    /// The product of the distinct irreducible factors whose multiplicity the characteristic does
    /// **not** divide — the whole radical only where it divides none of them. `None` for the zero
    /// polynomial, which has no radical.
    fn gradient_radical_unguarded(&self) -> Option<Self> {
        if self.is_zero() {
            return None;
        }
        let mut repeated = self.clone();
        for index in 0..N {
            repeated = repeated.gcd(&self.derivative(index));
            if repeated.is_one() {
                break;
            }
        }
        Some(
            self.exact_div(&repeated)
                .expect("the repeated part divides")
                .normalized(),
        )
    }

    /// The characteristic guard [`Self::squarefree_decomposition_by_radicals`] documents.
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

/// A count of the recursive content GCDs a computation performed, for the test that asserts the
/// subresultant route takes fewer of them.
///
/// `#[cfg(test)]` and thread-local: the claim it supports is **structural**, so it is asserted as a
/// count of operations and not as a duration — a duration would be a measurement, which #407 still
/// owes. Thread-local rather than global because `cargo test` runs tests in threads of one process.
#[cfg(test)]
pub(crate) mod content_calls {
    use std::cell::Cell;

    thread_local! {
        static CALLS: Cell<usize> = const { Cell::new(0) };
    }

    /// Note one call to `content_by`.
    pub(crate) fn record() {
        CALLS.with(|calls| calls.set(calls.get() + 1));
    }

    /// Run `body` and report how many content GCDs it took.
    pub(crate) fn counting<T>(body: impl FnOnce() -> T) -> (T, usize) {
        CALLS.with(|calls| calls.set(0));
        let value = body();
        (value, CALLS.with(Cell::get))
    }
}

/// `limbs / divisor`, little-endian, for a divisor that fits a `u64`.
///
/// Exact at its one call site, where the divisor is the characteristic and the dividend the order
/// `q = p^k`. Written out rather than taken from an integer type so that
/// [`SparseMultiPoly::pth_root`] does not cap the field's order at the width of a `u128` — the
/// orders in this crate reach 255 bits.
fn divide_limbs(limbs: &[u64], divisor: u64) -> Vec<u64> {
    let divisor = u128::from(divisor);
    let mut quotient = vec![0u64; limbs.len()];
    let mut remainder = 0u128;
    for index in (0..limbs.len()).rev() {
        let current = (remainder << 64) | u128::from(limbs[index]);
        quotient[index] = (current / divisor) as u64;
        remainder = current % divisor;
    }
    quotient
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

    /// The refusal in small characteristic moved to the reference route, which still earns it.
    ///
    /// `(x + y)^3` over GF(3) is the case #128 refused: the whole gradient vanishes, so the
    /// repeated-radical form cannot see the factor and says so. `squarefree_part` now answers it
    /// through the Frobenius route instead — asserted in `characteristic_p` — so the refusal is a
    /// statement about one method and no longer about the crate.
    #[test]
    fn test_the_reference_route_still_refuses_in_small_characteristic() {
        type Small = PrimeFieldElement64<3>;
        // (x + y)^3 has total degree 3, which the characteristic does not exceed.
        let factor: SparseMultiPoly<2, Small> = SparseMultiPoly::new(&[
            (Monomial::new(&[1, 0]), Small::one()),
            (Monomial::new(&[0, 1]), Small::one()),
        ]);
        let cube = &(&factor * &factor) * &factor;
        assert_eq!(
            cube.squarefree_decomposition_by_radicals(),
            Err(SquarefreeError::CharacteristicTooSmall {
                characteristic: 3,
                degree: 3,
            })
        );
        // And the implementation answers the same input.
        assert_eq!(cube.squarefree_part().unwrap(), factor);
    }

    mod characteristic_p {
        use super::*;
        use crate::fields::{Gf256, Zp2};

        /// GF(3), where a cube is what the derivative cannot see.
        type Zp3 = PrimeFieldElement64<3>;

        /// `(factor, multiplicity)` pairs sorted by multiplicity, for a stable comparison.
        fn sorted<const N: usize, G: crate::KnownOrder>(
            mut decomposition: Vec<(SparseMultiPoly<N, G>, u32)>,
        ) -> Vec<(SparseMultiPoly<N, G>, u32)> {
            decomposition.sort_by_key(|(_, multiplicity)| *multiplicity);
            decomposition
        }

        /// `∏ factor^multiplicity`, to check a decomposition against what it decomposed.
        fn product<const N: usize, G: crate::KnownOrder>(
            decomposition: &[(SparseMultiPoly<N, G>, u32)],
        ) -> SparseMultiPoly<N, G> {
            decomposition
                .iter()
                .fold(SparseMultiPoly::one(), |acc, (factor, multiplicity)| {
                    (0..*multiplicity).fold(acc, |acc, _| &acc * factor)
                })
        }

        /// Over GF(2) a factor of even multiplicity is recovered, which the derivative cannot see.
        ///
        /// `x^2` differentiates to zero: the exponent `2` enters as a field element and vanishes.
        /// So this is exactly the case #128's guard refused, and the whole point of #408.
        #[test]
        fn test_an_even_multiplicity_is_recovered_over_gf2() {
            type P = SparseMultiPoly<2, Zp2>;
            let x: P = SparseMultiPoly::parse("x", VARS).unwrap();
            let square = &x * &x;
            assert!(
                square.derivative(0).is_zero() && square.derivative(1).is_zero(),
                "the whole gradient must vanish, or this proves nothing"
            );
            assert_eq!(
                square.squarefree_decomposition().unwrap(),
                vec![(x.clone(), 2)]
            );
            assert_eq!(square.squarefree_part().unwrap(), x);
        }

        /// A multiplicity divisible by the characteristic twice over needs two Frobenius steps.
        #[test]
        fn test_a_fourth_power_is_recovered_over_gf2() {
            type P = SparseMultiPoly<2, Zp2>;
            let x: P = SparseMultiPoly::parse("x", VARS).unwrap();
            let fourth = &(&x * &x) * &(&x * &x);
            assert_eq!(fourth.squarefree_decomposition().unwrap(), vec![(x, 4)]);
        }

        /// A visible and an invisible multiplicity in one polynomial are both recovered.
        ///
        /// `x^2 * (x + 1)^3` over GF(2): the gradient sees `(x + 1)^3` and is blind to `x^2`, so
        /// the two halves have to be found by different means and recombined.
        #[test]
        fn test_a_visible_and_an_invisible_factor_together_over_gf2() {
            type P = SparseMultiPoly<2, Zp2>;
            let x: P = SparseMultiPoly::parse("x", VARS).unwrap();
            let shifted: P = SparseMultiPoly::parse("x + 1", VARS).unwrap();
            let f = &(&x * &x) * &(&shifted * &(&shifted * &shifted));

            let decomposition = sorted(f.squarefree_decomposition().unwrap());
            assert_eq!(
                decomposition,
                vec![(x.clone(), 2), (shifted.clone(), 3)],
                "the gradient-blind factor and the visible one must both appear"
            );
            assert_eq!(product(&decomposition), f);
            assert_eq!(f.squarefree_part().unwrap(), &x * &shifted);
        }

        /// Over GF(2^8) a factor of even multiplicity with extension coefficients is recovered.
        ///
        /// The coefficients are past the prime subfield, so this also exercises the `p`-th root:
        /// over GF(2^8) it is `c^128`, not the identity it is over GF(2).
        #[test]
        fn test_an_even_multiplicity_is_recovered_over_gf256() {
            type P = SparseMultiPoly<2, Gf256>;
            let parse = |s| P::parse(s, VARS).unwrap();
            // 87 and 131 are 0x57 and 0x83, the pair whose product distinguishes the two GF(2^8)
            // moduli; nothing here depends on that, they are simply not in GF(2).
            let a = parse("87*x + 131");
            let b = parse("200*y + 57");
            let f = &(&a * &a) * &b;

            let decomposition = sorted(f.squarefree_decomposition().unwrap());
            assert_eq!(decomposition.len(), 2);
            assert_eq!(decomposition[0].1, 1);
            assert_eq!(decomposition[1].1, 2);
            assert_eq!(product(&decomposition), f.normalized());
        }

        /// The `p`-th root inverts the `p`-th power, over a field where Frobenius is not identity.
        #[test]
        fn test_the_pth_root_inverts_the_pth_power() {
            type P = SparseMultiPoly<2, Gf256>;
            let f = P::parse("87*x*y + 131*x + 200", VARS).unwrap();
            let square = &f * &f;
            assert_eq!(square.pth_root(), Some(f));
            // A polynomial that is not a `p`-th power has none.
            assert_eq!(P::parse("x", VARS).unwrap().pth_root(), None);
        }

        /// A multiplicity of `p` in odd characteristic is recovered too, so nothing is special
        /// about two.
        #[test]
        fn test_a_cube_is_recovered_over_gf3() {
            type P = SparseMultiPoly<2, Zp3>;
            let factor: P = SparseMultiPoly::parse("x + y", VARS).unwrap();
            let cube = &(&factor * &factor) * &factor;
            assert!(
                cube.derivative(0).is_zero() && cube.derivative(1).is_zero(),
                "the gradient must vanish, or this is not the characteristic case"
            );
            assert_eq!(
                cube.squarefree_decomposition().unwrap(),
                vec![(factor.clone(), 3)]
            );
            assert_eq!(cube.squarefree_part().unwrap(), factor);
        }

        /// The only remaining refusal is the zero polynomial.
        ///
        /// `SquarefreeError::CharacteristicTooSmall` is still reachable, but only from the
        /// repeated-radical reference route, which keeps the guard because the guard is a true
        /// statement about *that* method.
        #[test]
        fn test_the_only_refusal_left_is_zero() {
            type P = SparseMultiPoly<2, Zp2>;
            let factor: P = SparseMultiPoly::parse("x + y", VARS).unwrap();
            let fourth = &(&factor * &factor) * &(&factor * &factor);
            assert!(fourth.squarefree_decomposition().is_ok());
            assert!(fourth.squarefree_part().is_ok());
            assert_eq!(
                P::zero().squarefree_decomposition(),
                Err(SquarefreeError::Zero)
            );
            assert_eq!(P::zero().squarefree_part(), Err(SquarefreeError::Zero));

            // The reference route still refuses this, which is why it is a reference and not the
            // implementation.
            assert!(matches!(
                fourth.squarefree_decomposition_by_radicals(),
                Err(SquarefreeError::CharacteristicTooSmall { .. })
            ));
        }

        /// The two routes agree wherever the reference route can answer at all.
        ///
        /// The differential test #408 asks for: the repeated-radical form becomes the reference,
        /// and where its characteristic guard passes it must give exactly what the new route
        /// gives. Over GF(13) with total degree below 13 that is every case here.
        #[test]
        fn test_the_two_routes_agree_where_the_reference_applies() {
            let g1 = parse("x + 1");
            let g2 = parse("y + 1");
            let g3 = parse("x + y");
            let cases = [
                g1.clone(),
                &g1 * &g1,
                &(&g1 * &g1) * &g2,
                &(&(&g1 * &g1) * &(&g2 * &g2)) * &g3,
                &(&g3 * &(&g3 * &g3)) * &g2,
                parse("x^2 - y^2"),
                Poly::one(),
            ];
            for f in cases {
                let reference = sorted(f.squarefree_decomposition_by_radicals().unwrap());
                let computed = sorted(f.squarefree_decomposition().unwrap());
                assert_eq!(reference, computed, "the two routes disagree about {f}");
            }
        }
    }

    mod subresultant {
        use super::*;
        use crate::{fields::Gf256, poly::multivariate::multivariate_gcd::GcdRoute};

        /// The two routes give the same GCD, which is an equality and not a containment test.
        ///
        /// A reduced GCD is unique once normalized, and both routes normalize the same way, so
        /// "the same answer" is the right assertion rather than "each divides the other".
        #[test]
        fn test_the_two_routes_agree_on_shared_factors() {
            let w = parse("x + y");
            let u = parse("x - y");
            let v = parse("x*y + 1");
            let cases = [
                (&u * &w, &v * &w),
                (&(&u * &w) * &w, &(&v * &w) * &w),
                (parse("x^2 - y^2"), parse("x^3 + y^3")),
                (parse("x^4*y^2 + x^2"), parse("x^3*y^3 + x^3")),
                (parse("x + 1"), parse("y + 1")),
                (Poly::zero(), &u * &w),
                (Poly::one(), &u * &w),
            ];
            for (f, g) in cases {
                assert_eq!(
                    f.gcd_by(&g, GcdRoute::SubresultantPrs),
                    f.gcd_by(&g, GcdRoute::PrimitivePrs),
                    "the two routes disagree about gcd({f}, {g})"
                );
            }
        }

        /// A degree gap of more than one is handled: that is where the subresultant scaling bites.
        ///
        /// `pseudo_remainder` as the primitive PRS uses it multiplies by the leading coefficient
        /// once per *step*, which can be fewer times than `delta + 1` when a degree is skipped. The
        /// subresultant divisibility theorem needs exactly `delta + 1`, so the two pseudo-remainders
        /// are not interchangeable and a gap is the case that tells them apart.
        #[test]
        fn test_a_degree_gap_is_handled() {
            // Read in x, `x^5 + 1` has nothing at x^4, x^3, x^2 or x^1.
            let gapped = parse("x^5*y + x^5 + y^2 + 1");
            let other = parse("x^2*y + x^2 + y + 1");
            assert_eq!(
                gapped.gcd_by(&other, GcdRoute::SubresultantPrs),
                gapped.gcd_by(&other, GcdRoute::PrimitivePrs)
            );

            let f = parse("x^6 + 1");
            let g = parse("x^2 + 1");
            assert_eq!(
                f.gcd_by(&g, GcdRoute::SubresultantPrs),
                f.gcd_by(&g, GcdRoute::PrimitivePrs)
            );
        }

        /// The scaled pseudo-remainder uses exactly `delta + 1` powers of the leading coefficient.
        ///
        /// The identity the subresultant route rests on: `lc(b)^(delta+1) * a = q*b + r`. Checked
        /// by dividing, since the quotient has to come out exactly.
        #[test]
        fn test_the_scaled_pseudo_remainder_satisfies_its_identity() {
            let cases = [
                (parse("x^5*y + x^2 + 1"), parse("x^2*y + x + 3")),
                (parse("x^6 + 1"), parse("x^2 + 1")),
                (parse("x^3*y^2 + x"), parse("x*y + 1")),
            ];
            for (a, b) in cases {
                let delta = a.degree_in(0) - b.degree_in(0);
                let remainder = a.pseudo_remainder_scaled(&b, 0);
                let leading = b.coefficient_in(0, b.degree_in(0));
                let scale = (0..=delta).fold(Poly::one(), |acc, _| &acc * &leading);
                let scaled = &scale * &a;
                let difference = &scaled - &remainder;
                assert!(
                    difference.exact_div(&b).is_some(),
                    "lc(b)^{} * a - r is not a multiple of b, for a = {a}, b = {b}",
                    delta + 1
                );
                assert!(
                    remainder.is_zero() || remainder.degree_in(0) < b.degree_in(0),
                    "the remainder {remainder} did not reduce the degree"
                );
            }
        }

        /// The two routes agree over GF(2^8), where the coefficients are not integers.
        #[test]
        fn test_the_two_routes_agree_over_gf256() {
            type P = SparseMultiPoly<2, Gf256>;
            let p = |s| P::parse(s, VARS).unwrap();
            let w = p("87*x + 131*y + 200");
            let u = p("57*x*y + 3");
            let f = &u * &w;
            let g = &p("200*x + 1") * &w;
            assert_eq!(
                f.gcd_by(&g, GcdRoute::SubresultantPrs),
                f.gcd_by(&g, GcdRoute::PrimitivePrs)
            );
            assert!(f.gcd(&g).exact_div(&w.normalized()).is_some());
        }

        /// `gcd` without a route is the subresultant one, so the default is what everything uses.
        #[test]
        fn test_the_default_route_is_the_subresultant_one() {
            assert_eq!(GcdRoute::default(), GcdRoute::SubresultantPrs);
            let f = parse("x^2 - y^2");
            let g = parse("x^3 + y^3");
            assert_eq!(f.gcd(&g), f.gcd_by(&g, GcdRoute::SubresultantPrs));
        }

        /// The subresultant route takes strictly fewer recursive content GCDs.
        ///
        /// The structural claim #407 rests on, asserted as a **count of operations** and not as a
        /// duration: the primitive PRS divides the content out of every pseudo-remainder, and a
        /// content is itself a recursive GCD, so it pays one per Euclidean step; the subresultant
        /// route pays one exact division per step and takes contents only at the top and at the
        /// end. Whether that is faster in wall clock on any machine is **unmeasured**, and this
        /// test deliberately does not pretend otherwise.
        #[test]
        fn test_the_subresultant_route_takes_fewer_content_gcds() {
            use crate::poly::multivariate::multivariate_gcd::content_calls;

            // Enough Euclidean steps for the per-step cost to show: degree five against degree
            // two in the main variable, with coefficients that are not constants.
            let f = parse("x^5*y^2 + x^3*y + x^2 + y^3 + 1");
            let g = parse("x^2*y + x*y^2 + x + 2");

            let (primitive, primitive_calls) =
                content_calls::counting(|| f.gcd_by(&g, GcdRoute::PrimitivePrs));
            let (subresultant, subresultant_calls) =
                content_calls::counting(|| f.gcd_by(&g, GcdRoute::SubresultantPrs));

            assert_eq!(
                primitive, subresultant,
                "the comparison is only meaningful if the two agree"
            );
            assert!(
                subresultant_calls < primitive_calls,
                "the subresultant route took {subresultant_calls} content GCDs and the primitive \
                 one took {primitive_calls}, so the per-step cost is not being removed"
            );
            assert!(
                primitive_calls > 0,
                "the counter recorded nothing, so this test is vacuous"
            );
            // Printed rather than pinned to exact numbers, which would turn a counting assertion
            // into a snapshot of an implementation detail.
            println!(
                "content GCDs: primitive {primitive_calls}, subresultant {subresultant_calls}"
            );
        }

        /// Three variables, where the recursion that computes a content is itself a GCD.
        #[test]
        fn test_the_two_routes_agree_in_three_variables() {
            let vars = ["x", "y", "z"];
            let p = |s| SparseMultiPoly::<3, F>::parse(s, vars).unwrap();
            let w = p("x*z + y");
            let f = &p("y*z + 1") * &w;
            let g = &p("x + z^2") * &w;
            assert_eq!(
                f.gcd_by(&g, GcdRoute::SubresultantPrs),
                f.gcd_by(&g, GcdRoute::PrimitivePrs)
            );
        }
    }

    mod squarefree_contract {
        use crate::{
            fields::{Gf256, Zp2},
            poly::multivariate::sparse_multivariate_polynomial::SparseMultiPoly,
            FiniteField, KnownOrder, Monomial,
        };
        use rand::{prelude::StdRng, Rng, SeedableRng};

        /// Everything a squarefree decomposition must satisfy, asserted against `f` itself.
        ///
        /// Checked as a contract rather than against an expected answer, so it can be applied to
        /// inputs nobody factored by hand: the factors multiply back to `f`, each is squarefree,
        /// they are pairwise coprime, their multiplicities are distinct, and none is a unit. A
        /// decomposition that is silently wrong fails at least one of these.
        pub(super) fn assert_contract<const N: usize, G: KnownOrder>(
            f: &SparseMultiPoly<N, G>,
        ) -> Vec<(SparseMultiPoly<N, G>, u32)> {
            let decomposition = f
                .squarefree_decomposition()
                .unwrap_or_else(|e| panic!("{f} has no decomposition: {e}"));

            let product = decomposition
                .iter()
                .fold(SparseMultiPoly::one(), |acc, (factor, multiplicity)| {
                    (0..*multiplicity).fold(acc, |acc, _| &acc * factor)
                });
            // `f` up to the unit the factors are normalized by, which is what `normalized` pins.
            assert_eq!(
                product,
                normalized(f),
                "the decomposition {decomposition:?} does not multiply back to {f}"
            );

            let mut multiplicities: Vec<u32> = decomposition.iter().map(|(_, m)| *m).collect();
            multiplicities.sort_unstable();
            let distinct = {
                let mut unique = multiplicities.clone();
                unique.dedup();
                unique.len()
            };
            assert_eq!(
                distinct,
                multiplicities.len(),
                "{f} lists a multiplicity twice: {multiplicities:?}"
            );
            assert!(
                multiplicities.iter().all(|m| *m >= 1),
                "{f} has a factor of multiplicity zero"
            );

            for (i, (factor, _)) in decomposition.iter().enumerate() {
                assert!(!factor.is_one(), "{f} lists a unit as a factor");
                // Squarefree: its own decomposition is itself, once.
                assert_eq!(
                    factor.squarefree_decomposition().unwrap(),
                    vec![(normalized(factor), 1)],
                    "the factor {factor} of {f} is not squarefree"
                );
                for (other, _) in decomposition.iter().skip(i + 1) {
                    assert!(
                        factor.gcd(other).is_one(),
                        "the factors {factor} and {other} of {f} share a divisor"
                    );
                }
            }
            // The radical is the product of the distinct factors, which is the same list.
            let radical = decomposition
                .iter()
                .fold(SparseMultiPoly::one(), |acc, (factor, _)| &acc * factor);
            assert_eq!(
                f.squarefree_part().unwrap(),
                normalized(&radical),
                "the squarefree part of {f} is not the product of its distinct factors"
            );
            decomposition
        }

        /// Scaled so the lexicographic leading coefficient is one, as the decomposition is.
        fn normalized<const N: usize, G: FiniteField>(
            p: &SparseMultiPoly<N, G>,
        ) -> SparseMultiPoly<N, G> {
            let leading = p.leading_coefficient(crate::poly::MonomialOrder::Lexicographic);
            if leading.is_zero() || leading.is_one() {
                p.clone()
            } else {
                p.scale(&leading.inverse())
            }
        }

        /// The eight polynomials over GF(2) in two variables of total degree at most one.
        fn linear_over_gf2() -> Vec<SparseMultiPoly<2, Zp2>> {
            let monomials = [
                Monomial::new(&[0, 0]),
                Monomial::new(&[1, 0]),
                Monomial::new(&[0, 1]),
            ];
            (0..8usize)
                .map(|code| {
                    let terms: Vec<(Monomial<2>, Zp2)> = monomials
                        .iter()
                        .enumerate()
                        .map(|(bit, monomial)| (*monomial, Zp2::new(((code >> bit) & 1) as u64)))
                        .collect();
                    SparseMultiPoly::new(&terms)
                })
                .collect()
        }

        /// Every planted `u^a * v^b` over GF(2) decomposes to exactly `u` and `v`.
        ///
        /// Exhaustive over the distinct non-constant linear factors — all irreducible, and
        /// pairwise coprime because they are distinct and of degree one — and over multiplicities
        /// one to four. Half of the `(a, b)` pairs have at least one even multiplicity, which is
        /// precisely what the derivative cannot see over GF(2).
        #[test]
        fn test_every_planted_product_over_gf2_is_recovered() {
            let linear: Vec<SparseMultiPoly<2, Zp2>> = linear_over_gf2()
                .into_iter()
                .filter(|p| !p.is_zero() && !p.is_constant())
                .collect();
            assert_eq!(linear.len(), 6, "GF(2) has six non-constant linear forms");

            let mut even_multiplicities = 0;
            for (i, u) in linear.iter().enumerate() {
                for v in linear.iter().skip(i + 1) {
                    for a in 1..=4u32 {
                        for b in 1..=4u32 {
                            let f = (0..a).fold(SparseMultiPoly::one(), |acc, _| &acc * u);
                            let f = (0..b).fold(f, |acc, _| &acc * v);
                            let decomposition = assert_contract(&f);

                            // The expected answer, grouped: two factors of the same multiplicity
                            // are reported once, as their product.
                            let mut expected: Vec<(SparseMultiPoly<2, Zp2>, u32)> = if a == b {
                                vec![(normalized(&(u * v)), a)]
                            } else {
                                vec![(normalized(u), a), (normalized(v), b)]
                            };
                            expected.sort_by_key(|(_, m)| *m);
                            let mut found = decomposition;
                            found.sort_by_key(|(_, m)| *m);
                            assert_eq!(found, expected, "u = {u}, v = {v}, a = {a}, b = {b}");

                            if a % 2 == 0 || b % 2 == 0 {
                                even_multiplicities += 1;
                            }
                        }
                    }
                }
            }
            assert!(
                even_multiplicities >= 100,
                "only {even_multiplicities} cases had an even multiplicity, which is the case \
                 the derivative cannot see"
            );
        }

        /// Every polynomial over GF(2) on the degree-two monomials satisfies the contract.
        ///
        /// 64 inputs nobody chose, including the ones that are squares and the ones that are not,
        /// checked against the contract rather than against an expected factorization — which is
        /// the only way to cover inputs whose factorization is not known in advance.
        #[test]
        fn test_the_contract_holds_over_every_small_polynomial_over_gf2() {
            let monomials: Vec<Monomial<2>> = (0..=2u32)
                .flat_map(|d| (0..=d).map(move |i| Monomial::new(&[i, d - i])))
                .collect();
            assert_eq!(monomials.len(), 6);

            let mut checked = 0;
            for code in 0..(1u32 << monomials.len()) {
                let terms: Vec<(Monomial<2>, Zp2)> = monomials
                    .iter()
                    .enumerate()
                    .map(|(bit, monomial)| (*monomial, Zp2::new(u64::from((code >> bit) & 1))))
                    .collect();
                let f: SparseMultiPoly<2, Zp2> = SparseMultiPoly::new(&terms);
                if f.is_zero() {
                    continue;
                }
                assert_contract(&f);
                checked += 1;
            }
            assert_eq!(checked, 63, "the sweep did not cover every nonzero input");
        }

        /// A planted product over GF(2^8) with extension coefficients satisfies the contract.
        ///
        /// Over GF(2) the `p`-th root of a coefficient is the identity, so GF(2) alone would not
        /// exercise the inverse Frobenius at all. Here it is `c^128`.
        #[test]
        fn test_the_contract_holds_over_gf256_with_extension_coefficients() {
            type P = SparseMultiPoly<2, Gf256>;
            let parse = |s| P::parse(s, ["x", "y"]).unwrap();
            let u = parse("87*x + 131*y + 200");
            let v = parse("57*x*y + 3");
            for (a, b) in [(2u32, 1u32), (4, 1), (2, 2), (1, 2), (6, 3), (2, 3)] {
                let f = (0..a).fold(P::one(), |acc, _| &acc * &u);
                let f = (0..b).fold(f, |acc, _| &acc * &v);
                let decomposition = assert_contract(&f);
                assert!(
                    decomposition.iter().any(|(_, m)| *m == a || *m == b),
                    "a = {a}, b = {b} produced {decomposition:?}"
                );
            }
        }

        /// A random product satisfies the contract, over every field `for_each_field!` covers.
        pub(super) fn assert_random_products_satisfy_the_contract<const N: usize, G: KnownOrder>() {
            let mut rng = StdRng::seed_from_u64(0x0408_5f5e);
            let mut nontrivial = 0;
            for _ in 0..8 {
                let draw = |rng: &mut StdRng| -> SparseMultiPoly<N, G> {
                    let terms: Vec<(Monomial<N>, G)> = (0..3)
                        .map(|_| {
                            let mut exponents = [0u32; N];
                            for e in exponents.iter_mut() {
                                *e = rng.gen_range(0..2);
                            }
                            (Monomial::new(&exponents), G::random(rng))
                        })
                        .collect();
                    SparseMultiPoly::new(&terms)
                };
                let u = draw(&mut rng);
                let v = draw(&mut rng);
                if u.is_zero() || v.is_zero() {
                    continue;
                }
                // `u^2 * v` plants a multiplicity the derivative cannot see in characteristic two
                // and can in every other field here, so one body covers both cases.
                let f = &(&u * &u) * &v;
                assert_contract(&f);
                nontrivial += 1;
            }
            assert!(nontrivial > 0, "every drawn case was degenerate");
        }
    }

    // The squarefree-decomposition contract holds over every field, at two arities.
    for_each_field!(
        fn the_squarefree_contract_holds<F>() {
            squarefree_contract::assert_random_products_satisfy_the_contract::<2, F>();
            squarefree_contract::assert_random_products_satisfy_the_contract::<3, F>();
        }
    );

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
        use crate::poly::multivariate::multivariate_gcd::GcdRoute;

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
        ///
        /// Run against the **default** route, as #407 asks, and against each route by name beside
        /// it — so neither route can pass by being the one nothing exercises.
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
                // The default route, which is what every caller gets, and both routes against each
                // other: a reduced GCD is unique once normalized, so that is an equality.
                let d = f.gcd(&g);
                assert_eq!(
                    d,
                    f.gcd_by(&g, GcdRoute::PrimitivePrs),
                    "the two routes disagree about gcd({f}, {g})"
                );
                assert_eq!(d, f.gcd_by(&g, GcdRoute::SubresultantPrs));

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
            poly::{
                multivariate::{
                    multivariate_gcd::GcdRoute, sparse_multivariate_polynomial::SparseMultiPoly,
                },
                MonomialOrder,
            },
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

                // The two routes return the same value, over this field and at this arity.
                assert_eq!(
                    d,
                    f.gcd_by(&g, GcdRoute::PrimitivePrs),
                    "the two GCD routes disagree"
                );
                assert_eq!(d, f.gcd_by(&g, GcdRoute::SubresultantPrs));

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
