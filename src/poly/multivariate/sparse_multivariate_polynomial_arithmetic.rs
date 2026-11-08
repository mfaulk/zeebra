//! Arithmetic operations for sparse multivariate polynomials.
//!
//! `Add`, `Sub` and `Neg` collect into one of their operands' maps rather than materialising a
//! `Vec` of `|a| + |b|` terms and rebuilding a third map through [`SparseMultiPoly::new`] — the
//! same change #243 made to `Mul`, one operator over. #243 left `Add` as the binding term in the
//! six-round `cico_bivariate` build, whose MDS layer folds sixteen 266 815-term state words
//! through it once per round and so allocated the sum two to three times over.
//!
//! Which map is merged into is chosen per ownership spelling, and that is the whole of the
//! optimisation: an owned operand is mutated, so `p + q` and `p += &q` allocate nothing beyond the
//! growth the sum's own support needs. Addition being commutative, the borrowed/borrowed spelling
//! clones the *larger* side and hashes the smaller.

use std::{cmp::Ordering, collections::HashMap, ops, ops::Neg};

use crate::impl_mul_variants;

use crate::{
    poly::{
        multivariate::{
            sparse_multivariate_multiply, sparse_multivariate_polynomial::SparseMultiPoly,
        },
        MonomialOrder,
    },
    FiniteField, Monomial,
};

/// Merge `terms` into `accumulator`, dropping any monomial whose coefficient cancels to zero.
///
/// The canonical invariant is maintained entry by entry rather than by a `retain` pass afterwards.
/// A `retain` is linear in the accumulator, which would make `div_rem`'s `quotient += q` — one
/// term against the quotient built so far — linear in the quotient on every reduction step.
///
/// # Why there is no `reserve`
///
/// `|a| + |b|` is an upper bound on the sum's support and pre-sizing to it would save a handful of
/// rehashes, but it is the *wrong* bound to allocate: it is exactly the quantity the materialising
/// form was criticised for holding. Measured on the cancelling shape in
/// `tests/multivariate_add_memory.rs` — two 11 476-term triangles summing to one term — a
/// `reserve(|b|)` grew the accumulator's table to hold 22 952 entries and peaked at **426 KB** to
/// produce one term, against **594 KB** for materialising: a 1.4x improvement and no bound at all.
/// Letting the table grow geometrically instead only ever grows it when it is full of *live*
/// entries, so the live set is bounded by the output; the same case then peaks at under a
/// kilobyte. The amortised insert cost is unchanged, which is why this is not a trade.
fn merge_terms<const N: usize, F: FiniteField>(
    accumulator: &mut HashMap<Monomial<N>, F>,
    terms: impl Iterator<Item = (Monomial<N>, F)>,
) {
    for (monomial, coefficient) in terms {
        let cancelled = match accumulator.get_mut(&monomial) {
            Some(c) => {
                *c += coefficient;
                c.is_zero()
            }
            None => {
                // A zero coefficient is not a term of the polynomial, so it is never inserted.
                if !coefficient.is_zero() {
                    accumulator.insert(monomial, coefficient);
                }
                false
            }
        };
        if cancelled {
            accumulator.remove(&monomial);
        }
    }
}

/// Neg: -p
impl<const N: usize, F: FiniteField> Neg for SparseMultiPoly<N, F> {
    type Output = SparseMultiPoly<N, F>;

    fn neg(mut self) -> Self::Output {
        // One pass: `retain`'s closure holds the coefficient by mutable reference, so negating and
        // dropping the zeros happen together. The drop is not dead — `terms` admits the
        // non-canonical `0 * 1` spelling of the zero polynomial, and `-p` has always returned the
        // canonical form of it.
        self.terms.retain(|_monomial, c| {
            *c = -*c;
            !c.is_zero()
        });
        self
    }
}

/// Add: &p + &q
impl<const N: usize, F: FiniteField> ops::Add<&SparseMultiPoly<N, F>> for &SparseMultiPoly<N, F> {
    type Output = SparseMultiPoly<N, F>;

    fn add(self, other: &SparseMultiPoly<N, F>) -> Self::Output {
        // Clone the larger operand and merge the smaller into it. Addition is commutative, so the
        // choice is free, and it is the cheaper split: the clone copies a map, while the merge
        // hashes once per term of whichever side is merged.
        let (mut sum, addend) = if self.terms.len() >= other.terms.len() {
            (self.clone(), other)
        } else {
            (other.clone(), self)
        };
        sum += addend;
        sum
    }
}

/// Add: p + &q, accumulated into `p`'s map.
impl<const N: usize, F: FiniteField> ops::Add<&SparseMultiPoly<N, F>> for SparseMultiPoly<N, F> {
    type Output = SparseMultiPoly<N, F>;

    fn add(mut self, other: &SparseMultiPoly<N, F>) -> Self::Output {
        self += other;
        self
    }
}

/// Add: &p + q, accumulated into `q`'s map — equivalent, since addition commutes.
impl<const N: usize, F: FiniteField> ops::Add<SparseMultiPoly<N, F>> for &SparseMultiPoly<N, F> {
    type Output = SparseMultiPoly<N, F>;

    fn add(self, mut other: SparseMultiPoly<N, F>) -> Self::Output {
        other += self;
        other
    }
}

/// Add: p + q, accumulated into whichever map is larger.
impl<const N: usize, F: FiniteField> ops::Add for SparseMultiPoly<N, F> {
    type Output = SparseMultiPoly<N, F>;

    fn add(self, other: Self) -> Self::Output {
        let (mut sum, addend) = if self.terms.len() >= other.terms.len() {
            (self, other)
        } else {
            (other, self)
        };
        sum += addend;
        sum
    }
}

/// Add: &mut p + &mut q
impl<const N: usize, F: FiniteField> ops::Add<&mut SparseMultiPoly<N, F>>
    for &mut SparseMultiPoly<N, F>
{
    type Output = SparseMultiPoly<N, F>;

    fn add(self, other: &mut SparseMultiPoly<N, F>) -> Self::Output {
        &*self + &*other
    }
}

/// AddAssign: p += &q, merging `q`'s terms into `p`'s map.
impl<const N: usize, F: FiniteField> ops::AddAssign<&SparseMultiPoly<N, F>>
    for SparseMultiPoly<N, F>
{
    fn add_assign(&mut self, other: &SparseMultiPoly<N, F>) {
        merge_terms(
            &mut self.terms,
            other.terms.iter().map(|(monomial, c)| (*monomial, *c)),
        );
    }
}

/// AddAssign: p += q
impl<const N: usize, F: FiniteField> ops::AddAssign for SparseMultiPoly<N, F> {
    fn add_assign(&mut self, other: Self) {
        // Consuming `other`'s map rather than borrowing it, so its allocation is released here
        // instead of surviving until the end of the statement.
        merge_terms(&mut self.terms, other.terms.into_iter());
    }
}

/// Mul: &p * &q
impl<const N: usize, F: FiniteField> ops::Mul<&SparseMultiPoly<N, F>> for &SparseMultiPoly<N, F> {
    type Output = SparseMultiPoly<N, F>;

    /// Collected as the products are formed, by the route `sparse_multivariate_multiply::route`
    /// selects: see that module for the three routes and the dispatch between them.
    ///
    /// On the operator rather than behind an opt-in, because every form of multiplication in the
    /// crate funnels through here — `impl_mul_variants!`, `MulAssign`, `div_rem`'s `&q * divisor`,
    /// and the repeated-multiplication S-box in `grobner::research::resultant` — so a caller that
    /// had to opt in would be a caller that did not. Bit-identical to the materialising loop it
    /// replaces at every size; below the dispatch threshold it *is* that loop.
    fn mul(self, other: &SparseMultiPoly<N, F>) -> Self::Output {
        sparse_multivariate_multiply::multiply(self, other)
    }
}

impl_mul_variants!([const N: usize, F: FiniteField], SparseMultiPoly<N, F>);

/// Mul by a scalar: `&p * &c`.
///
/// The one definition of what scaling a multivariate polynomial means as an operator; the other
/// three ownership spellings and all four of `c * p` (`impl_left_scalar_mul!`) delegate here, so
/// no spelling can disagree with another. `scale` remains the route for code generic over `F`,
/// which the orphan rule keeps the left-hand operators out of reach of.
impl<const N: usize, F: FiniteField> ops::Mul<&F> for &SparseMultiPoly<N, F> {
    type Output = SparseMultiPoly<N, F>;

    fn mul(self, rhs: &F) -> Self::Output {
        self.scale(rhs)
    }
}

/// Mul by a scalar: `&p * c`.
impl<const N: usize, F: FiniteField> ops::Mul<F> for &SparseMultiPoly<N, F> {
    type Output = SparseMultiPoly<N, F>;

    fn mul(self, rhs: F) -> Self::Output {
        self * &rhs
    }
}

/// Mul by a scalar: `p * &c`. Scales in place, since the polynomial is owned.
impl<const N: usize, F: FiniteField> ops::Mul<&F> for SparseMultiPoly<N, F> {
    type Output = SparseMultiPoly<N, F>;

    fn mul(mut self, rhs: &F) -> Self::Output {
        self.scale_assign(rhs);
        self
    }
}

/// Mul by a scalar: `p * c`.
impl<const N: usize, F: FiniteField> ops::Mul<F> for SparseMultiPoly<N, F> {
    type Output = SparseMultiPoly<N, F>;

    fn mul(self, rhs: F) -> Self::Output {
        self * &rhs
    }
}

/// Sub: &p - &q
impl<const N: usize, F: FiniteField> ops::Sub<&SparseMultiPoly<N, F>> for &SparseMultiPoly<N, F> {
    type Output = SparseMultiPoly<N, F>;

    fn sub(self, other: &SparseMultiPoly<N, F>) -> Self::Output {
        // Subtraction does not commute, so unlike addition this is the one spelling with no owned
        // map to accumulate into and no choice about which side to clone.
        let mut difference = self.clone();
        difference -= other;
        difference
    }
}

/// Sub: p - &q, accumulated into `p`'s map.
impl<const N: usize, F: FiniteField> ops::Sub<&SparseMultiPoly<N, F>> for SparseMultiPoly<N, F> {
    type Output = SparseMultiPoly<N, F>;

    fn sub(mut self, other: &SparseMultiPoly<N, F>) -> Self::Output {
        self -= other;
        self
    }
}

/// Sub: &p - q, as `(-q) + p`, so that `q`'s map is the one accumulated into.
impl<const N: usize, F: FiniteField> ops::Sub<SparseMultiPoly<N, F>> for &SparseMultiPoly<N, F> {
    type Output = SparseMultiPoly<N, F>;

    fn sub(self, other: SparseMultiPoly<N, F>) -> Self::Output {
        let mut difference = -other;
        difference += self;
        difference
    }
}

/// Sub: p - q
impl<const N: usize, F: FiniteField> ops::Sub for SparseMultiPoly<N, F> {
    type Output = SparseMultiPoly<N, F>;

    fn sub(mut self, other: Self) -> Self::Output {
        self -= other;
        self
    }
}

/// Sub: &mut p - &mut q
impl<const N: usize, F: FiniteField> ops::Sub<&mut SparseMultiPoly<N, F>>
    for &mut SparseMultiPoly<N, F>
{
    type Output = SparseMultiPoly<N, F>;

    fn sub(self, other: &mut SparseMultiPoly<N, F>) -> Self::Output {
        &*self - &*other
    }
}

/// SubAssign: p -= &q, merging `q`'s negated terms into `p`'s map.
impl<const N: usize, F: FiniteField> ops::SubAssign<&SparseMultiPoly<N, F>>
    for SparseMultiPoly<N, F>
{
    fn sub_assign(&mut self, other: &SparseMultiPoly<N, F>) {
        merge_terms(
            &mut self.terms,
            other.terms.iter().map(|(monomial, c)| (*monomial, -*c)),
        );
    }
}

/// SubAssign: p -= q
impl<const N: usize, F: FiniteField> ops::SubAssign for SparseMultiPoly<N, F> {
    fn sub_assign(&mut self, other: Self) {
        merge_terms(
            &mut self.terms,
            other.terms.into_iter().map(|(monomial, c)| (monomial, -c)),
        );
    }
}

impl<const N: usize, F: FiniteField> SparseMultiPoly<N, F> {
    /// Divides `self` by `divisor` and returns the quotient and remainder.
    pub fn div_rem(&self, divisor: &Self, order: MonomialOrder) -> (Self, Self) {
        assert!(!divisor.is_zero(), "cannot divide by the zero polynomial");

        // `working` holds what is left to reduce; `remainder` collects the terms that cannot be.
        let mut working = self.clone();
        let mut quotient = SparseMultiPoly::zero();
        let mut remainder = SparseMultiPoly::zero();
        let divisor_lead = divisor.leading_term(order);

        while !working.is_zero() {
            let lead_term = working.leading_term(order);
            match lead_term.checked_div(&divisor_lead) {
                Some(q) => {
                    let q: SparseMultiPoly<N, F> = q.into();
                    working -= &q * divisor;
                    quotient += q;
                }
                None => {
                    // An irreducible leading term does not end the division: lower terms may
                    // still be divisible. Set it aside and carry on, so that no monomial of the
                    // remainder is divisible by the divisor's leading term.
                    let lead: SparseMultiPoly<N, F> = lead_term.into();
                    working -= lead.clone();
                    remainder += lead;
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
    /// Reduce `self` to normal form modulo `divisors`, discarding the quotients.
    ///
    /// Returns the remainder `multi_div_rem` would produce: no monomial of it is divisible by
    /// the leading term of any divisor. As with `multi_div_rem` the result depends on the order
    /// of the divisors, since the first whose leading term divides is the one applied.
    ///
    /// This is the operation Gröbner basis computation spends its time in, so it avoids the
    /// costs `multi_div_rem` pays for the quotients it does not need:
    ///
    /// - Terms are held in a vector sorted by `order`, so the leading term is the last element
    ///   and extracting it is constant time rather than a scan of the whole polynomial.
    /// - Each divisor's leading term and tail are computed once, not once per reduction step.
    /// - Reduction subtracts the divisor's tail by merging two sorted sequences, which is linear
    ///   and allocation-free given a reused buffer, rather than building a polynomial and
    ///   rebuilding a hash map.
    /// - The remainder is appended to, rather than accumulated with `+=`, which rebuilt its map
    ///   on every term.
    ///
    /// Sortedness survives the merge because monomial orders are multiplicative: multiplying a
    /// sorted sequence of terms by a monomial preserves their order.
    pub fn normal_form(&self, divisors: &[Self], order: MonomialOrder) -> Self {
        let mut counts = NormalFormCounts::default();
        self.normal_form_counting::<false>(divisors, order, &mut counts)
    }

    /// [`normal_form`](Self::normal_form), also returning what it cost in operations.
    ///
    /// Same code, same result — the counting is a const-generic parameter, so the uncounted path
    /// compiles the increments away and the counted path cannot drift from it.
    ///
    /// # Why this exists
    ///
    /// `docs/research/groebner-jl-gap.md` §4 attributes final interreduction's 13 871x against
    /// Groebner.jl to intermediate expression swell and then says the attribution is **inferred,
    /// not measured**: nothing counted terms popped or divisor tests. These counters settle it.
    /// `terms_popped` far exceeding the remainder's term count is swell; `terms_popped` close to
    /// it with `divisor_tests` large is scan cost. They point at different fixes.
    pub fn normal_form_counted(
        &self,
        divisors: &[Self],
        order: MonomialOrder,
    ) -> (Self, NormalFormCounts) {
        let mut counts = NormalFormCounts::default();
        let remainder = self.normal_form_counting::<true>(divisors, order, &mut counts);
        (remainder, counts)
    }

    fn normal_form_counting<const COUNT: bool>(
        &self,
        divisors: &[Self],
        order: MonomialOrder,
        counts: &mut NormalFormCounts,
    ) -> Self {
        // A zero divisor can never reduce anything, so drop them here rather than testing in the
        // inner loop. `multi_div_rem` reaches the same conclusion by failing to divide.
        let reducers: Vec<Reducer<N, F>> = divisors
            .iter()
            .filter(|d| !d.is_zero())
            .map(|d| Reducer::new(d, order))
            .collect();

        if reducers.is_empty() {
            return self.clone();
        }

        let mut working = sorted_terms(self, order);
        let mut remainder: Vec<(Monomial<N>, F)> = Vec::new();
        let mut scratch: Vec<(Monomial<N>, F)> = Vec::new();

        if COUNT {
            counts.calls += 1;
            counts.reducers += reducers.len();
            counts.dividend_terms += working.len();
        }

        while let Some((lead_monomial, lead_coefficient)) = working.pop() {
            if COUNT {
                counts.terms_popped += 1;
                counts.max_working_terms = counts.max_working_terms.max(working.len() + 1);
            }
            // The counter increments inside the scan, because a scan that stops early tested
            // fewer reducers than the basis holds and the mean scan length is the thing worth
            // knowing. `COUNT` is a const generic, so the uncounted path compiles this to the
            // bare `find_map` — which it has to, since this closure runs once per reducer per
            // term popped and is the innermost loop in the stage.
            let applicable = reducers.iter().find_map(|reducer| {
                if COUNT {
                    counts.divisor_tests += 1;
                }
                lead_monomial
                    .checked_div(&reducer.lead_monomial)
                    .map(|quotient| (reducer, quotient))
            });

            match applicable {
                Some((reducer, quotient_monomial)) => {
                    // The quotient term times the divisor's leading term is exactly the term just
                    // popped, so only the divisor's tail still has to be subtracted.
                    let quotient_coefficient = match reducer.lead_inverse {
                        Some(inverse) => lead_coefficient * inverse,
                        None => lead_coefficient,
                    };
                    if COUNT {
                        counts.reduction_steps += 1;
                        counts.tail_terms_merged += reducer.tail.len();
                        counts.terms_rewritten += working.len();
                    }
                    subtract_shifted(
                        &mut working,
                        &mut scratch,
                        &reducer.tail,
                        &quotient_monomial,
                        quotient_coefficient,
                        order,
                    );
                }
                None => remainder.push((lead_monomial, lead_coefficient)),
            }
        }

        if COUNT {
            counts.remainder_terms += remainder.len();
        }

        Self::new(&remainder)
    }

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

/// What a [`normal_form`](SparseMultiPoly::normal_form) reduction cost, in operations.
///
/// Durations say a reduction was slow. These say *why*, and the two candidate answers need
/// different fixes:
///
/// - **Swell.** `terms_popped` far exceeding `remainder_terms` means the working polynomial grew
///   through intermediates the answer does not contain. The fix is not a faster inner loop; it is
///   not building the intermediates, which is what a matrix formulation does.
/// - **Scan cost.** `terms_popped` close to `remainder_terms` with `divisor_tests` large means the
///   reducer search dominates. The fix is an index over leading monomials.
/// - **Rewrite cost.** `terms_rewritten` far exceeding `tail_terms_merged` means `subtract_shifted`
///   is copying terms no divisor tail touches, which is what windowing the merge removes.
///
/// Accumulates across calls, so one value can describe a whole interreduction.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct NormalFormCounts {
    /// Reductions performed, i.e. calls that got past the empty-divisor-set shortcut.
    pub calls: usize,
    /// Nonzero divisors seen, summed over calls. Divided by `calls`, the mean basis size reduced
    /// against.
    pub reducers: usize,
    /// Terms in the dividends, summed over calls — the input size, for comparison with
    /// `terms_popped`.
    pub dividend_terms: usize,
    /// Terms taken off the working polynomial. **The swell measure**: every term the reduction
    /// ever had to look at, including ones created by substituting divisor tails.
    pub terms_popped: usize,
    /// `Monomial::checked_div` calls in the reducer search. With a linear scan this is on the
    /// order of `terms_popped` times `reducers / calls`.
    pub divisor_tests: usize,
    /// Terms popped that a divisor applied to, as opposed to being set aside as irreducible.
    pub reduction_steps: usize,
    /// Divisor-tail terms merged in, summed over reduction steps — the work a reduction step
    /// genuinely owes.
    pub tail_terms_merged: usize,
    /// Terms of the working polynomial that `subtract_shifted` rewrote, summed over reduction
    /// steps. Against `tail_terms_merged` this is the ratio #440 is about: the merge is linear in
    /// the whole dividend whether or not the tail touches it.
    pub terms_rewritten: usize,
    /// The largest working polynomial seen, in terms. Swell's peak rather than its total.
    pub max_working_terms: usize,
    /// Terms in the remainders, summed over calls — the answer size.
    pub remainder_terms: usize,
}

impl NormalFormCounts {
    /// Fold another reduction's counts into these.
    pub fn add(&mut self, other: &Self) {
        self.calls += other.calls;
        self.reducers += other.reducers;
        self.dividend_terms += other.dividend_terms;
        self.terms_popped += other.terms_popped;
        self.divisor_tests += other.divisor_tests;
        self.reduction_steps += other.reduction_steps;
        self.tail_terms_merged += other.tail_terms_merged;
        self.terms_rewritten += other.terms_rewritten;
        self.max_working_terms = self.max_working_terms.max(other.max_working_terms);
        self.remainder_terms += other.remainder_terms;
    }

    /// Terms popped per term of the answer.
    ///
    /// The swell factor. One means every term looked at survived; a hundred means the reduction
    /// built and destroyed ninety-nine terms for every one it kept.
    pub fn swell_factor(&self) -> f64 {
        if self.remainder_terms == 0 {
            0.0
        } else {
            self.terms_popped as f64 / self.remainder_terms as f64
        }
    }

    /// Divisor tests per term popped — the mean length of the reducer scan.
    pub fn divisor_tests_per_term(&self) -> f64 {
        if self.terms_popped == 0 {
            0.0
        } else {
            self.divisor_tests as f64 / self.terms_popped as f64
        }
    }

    /// Terms rewritten per divisor-tail term merged.
    ///
    /// One would mean the merge touched only what the tail reached. Large means
    /// `subtract_shifted` is paying for the whole working polynomial on every step, which is the
    /// cost #440's windowed merge removes.
    pub fn rewrite_amplification(&self) -> f64 {
        if self.tail_terms_merged == 0 {
            0.0
        } else {
            self.terms_rewritten as f64 / self.tail_terms_merged as f64
        }
    }
}

/// A divisor with its leading term and tail precomputed, so reduction does not recompute them.
struct Reducer<const N: usize, F: FiniteField> {
    lead_monomial: Monomial<N>,
    /// The inverse of the leading coefficient, or `None` when this reducer is monic.
    ///
    /// Reduction divides the popped coefficient by this one on every step. Division is
    /// multiplication by an inverse, and an inverse is a modular exponentiation of about log2(q)
    /// multiplications, so computing it per step cost more than the term arithmetic it enabled.
    /// Inverting once here turns the inner loop into a single multiply.
    ///
    /// `None` is not merely an optimization of the common case: Buchberger scales every generator
    /// and every new basis element monic, so it is the only case that arises there, and it skips
    /// the multiply entirely.
    lead_inverse: Option<F>,
    /// Every term below the leading one, sorted ascending by the order.
    tail: Vec<(Monomial<N>, F)>,
}

impl<const N: usize, F: FiniteField> Reducer<N, F> {
    fn new(divisor: &SparseMultiPoly<N, F>, order: MonomialOrder) -> Self {
        let (lead_coefficient, lead_monomial): (F, Monomial<N>) =
            divisor.leading_term(order).into();
        let mut tail: Vec<(Monomial<N>, F)> = divisor
            .terms()
            .iter()
            .filter(|(monomial, _)| **monomial != lead_monomial)
            .map(|(monomial, coefficient)| (*monomial, *coefficient))
            .collect();
        tail.sort_by(|a, b| order.cmp(&a.0, &b.0));
        let lead_inverse = if lead_coefficient == F::ONE {
            None
        } else {
            Some(lead_coefficient.inverse())
        };
        Self {
            lead_monomial,
            lead_inverse,
            tail,
        }
    }
}

/// The terms of `p`, sorted ascending by `order`, so the leading term is last.
fn sorted_terms<const N: usize, F: FiniteField>(
    p: &SparseMultiPoly<N, F>,
    order: MonomialOrder,
) -> Vec<(Monomial<N>, F)> {
    let mut terms: Vec<(Monomial<N>, F)> = p
        .terms()
        .iter()
        .map(|(monomial, coefficient)| (*monomial, *coefficient))
        .collect();
    terms.sort_by(|a, b| order.cmp(&a.0, &b.0));
    terms
}

/// `working -= coefficient * monomial * tail`, for sequences sorted ascending by `order`.
///
/// Both inputs are sorted and the shifted tail stays sorted, because monomial orders are
/// multiplicative. So this is a merge: linear in the two lengths, and writing sequentially into a
/// reused buffer rather than allocating.
fn subtract_shifted<const N: usize, F: FiniteField>(
    working: &mut Vec<(Monomial<N>, F)>,
    scratch: &mut Vec<(Monomial<N>, F)>,
    tail: &[(Monomial<N>, F)],
    monomial: &Monomial<N>,
    coefficient: F,
    order: MonomialOrder,
) {
    scratch.clear();
    scratch.reserve(working.len() + tail.len());

    // The window: everything below the smallest shifted tail term is copied wholesale instead of
    // being compared against it.
    //
    // # Why this is safe, and total rather than probabilistic
    //
    // Monomial orders are multiplicative, so `q * tail[0]` is the smallest term the shifted tail
    // has — `tail` is sorted ascending and multiplying by `q` preserves that. No tail term can
    // therefore land at or below any `working` term strictly below it, so no term in the prefix can
    // merge or cancel against the tail. The merge loop would have pushed each of them unchanged;
    // copying them is what it would have done, term for term. The cancellation branch only fires on
    // `Ordering::Equal`, which cannot occur in the prefix.
    //
    // # Why it is worth doing, measured rather than assumed
    //
    // `docs/research/interreduction-cost.md` §3 measured this merge rewriting **1 174 314 651**
    // terms over 534 135 reduction steps on `mq-random-10` — a mean working polynomial of 2 199
    // terms against a mean divisor tail of 34.3, an amplification of **64.2x**. §3.0a then measured
    // the per-term cost at **30.2 ns**, which at 48 bytes a term is 1.59 GB/s and so an order of
    // magnitude under this machine's streaming bandwidth: the cost is not the copying, it is the
    // monomial multiply and `MonomialOrder::cmp` this prefix pays per element. Those are exactly
    // what the window removes.
    //
    // The downside is bounded at one `partition_point` — `O(log W)` — per step, in the case where
    // the tail straddles all of `working` and the prefix is empty.
    let start = if tail.is_empty() {
        0
    } else {
        let shifted_min = &tail[0].0 * monomial;
        let start =
            working.partition_point(|term| order.cmp(&term.0, &shifted_min) == Ordering::Less);
        scratch.extend_from_slice(&working[..start]);
        start
    };

    let mut i = start;
    let mut j = 0;
    while i < working.len() && j < tail.len() {
        let shifted = &tail[j].0 * monomial;
        match order.cmp(&working[i].0, &shifted) {
            Ordering::Less => {
                scratch.push(working[i]);
                i += 1;
            }
            Ordering::Greater => {
                scratch.push((shifted, F::zero() - coefficient * tail[j].1));
                j += 1;
            }
            Ordering::Equal => {
                let merged = working[i].1 - coefficient * tail[j].1;
                // Terms that cancel are dropped, keeping the representation canonical.
                if !merged.is_zero() {
                    scratch.push((working[i].0, merged));
                }
                i += 1;
                j += 1;
            }
        }
    }
    scratch.extend_from_slice(&working[i..]);
    for (tail_monomial, tail_coefficient) in &tail[j..] {
        scratch.push((
            tail_monomial * monomial,
            F::zero() - coefficient * *tail_coefficient,
        ));
    }

    std::mem::swap(working, scratch);
}

#[cfg(test)]
mod tests {
    use crate::{
        fields::PrimeFieldElement64,
        poly::{multivariate::sparse_multivariate_polynomial::SparseMultiPoly, MonomialOrder},
        FiniteField, Monomial, MultivariatePolynomial, One, Zero,
    };
    use proptest::{collection::vec, prelude::*, test_runner::TestRunner};

    /// A strategy for a polynomial of at most `num_terms` distinct monomials over any field.
    ///
    /// Written out rather than reached through `any::<SparseMultiPoly<N, F>>()`, whose `Arbitrary`
    /// impl boxes its strategy and so requires `F: 'static` — a bound the generic body
    /// `for_each_field!` writes cannot state.
    fn poly_strategy<const N: usize, F: FiniteField>(
        num_terms: usize,
    ) -> impl Strategy<Value = SparseMultiPoly<N, F>> {
        (
            vec(any::<Monomial<N>>(), num_terms),
            vec(F::arbitrary(), num_terms),
        )
            .prop_map(|(monomials, coefficients)| {
                let terms: Vec<(Monomial<N>, F)> =
                    monomials.into_iter().zip(coefficients).collect();
                SparseMultiPoly::new(&terms)
            })
    }

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

    /// Subtraction removes exactly what addition contributed.
    #[test]
    fn test_sub() {
        type F = PrimeFieldElement64<541>;
        let vars = ["x", "y"];
        let p: SparseMultiPoly<2, F> = SparseMultiPoly::parse("5*x^2*y + 3*x + 7", vars).unwrap();
        let q: SparseMultiPoly<2, F> = SparseMultiPoly::parse("3*x + 7", vars).unwrap();
        let expected: SparseMultiPoly<2, F> = SparseMultiPoly::parse("5*x^2*y", vars).unwrap();

        assert_eq!(&p - &q, expected);
        // Subtracting in the other order negates the result.
        assert_eq!(&q - &p, -expected.clone());
        // Terms that cancel are dropped rather than kept with a zero coefficient.
        assert_eq!(&q - &q, SparseMultiPoly::zero());
    }

    proptest! {
        /// a + b = b + a
        #[test]
        fn test_add_is_commutative(
            a in any::<SparseMultiPoly<2, PrimeFieldElement64<541>>>(),
            b in any::<SparseMultiPoly<2, PrimeFieldElement64<541>>>()) {
            prop_assert_eq!(&a + &b, &b + &a);
        }

        /// a - a = 0
        #[test]
        fn test_sub_is_additive_inverse(
            a in any::<SparseMultiPoly<2, PrimeFieldElement64<541>>>()) {
            prop_assert_eq!(&a - &a, SparseMultiPoly::zero());
            prop_assert_eq!(&a + &(-a.clone()), SparseMultiPoly::zero());
        }
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

    proptest! {
        /// a * 1 = a
        #[test]
        fn test_mul_one_is_identity(
            a in any::<SparseMultiPoly<2, PrimeFieldElement64<541>>>()) {
            prop_assert_eq!(&a * &SparseMultiPoly::one(), a.clone());
            prop_assert_eq!(&a * &SparseMultiPoly::zero(), SparseMultiPoly::zero());
        }

        /// a * b = b * a
        #[test]
        fn test_mul_is_commutative(
            a in any::<SparseMultiPoly<2, PrimeFieldElement64<541>>>(),
            b in any::<SparseMultiPoly<2, PrimeFieldElement64<541>>>()) {
            prop_assert_eq!(&a * &b, &b * &a);
        }

        /// (a * b) * c = a * (b * c)
        #[test]
        fn test_mul_is_associative(
            a in any::<SparseMultiPoly<2, PrimeFieldElement64<541>>>(),
            b in any::<SparseMultiPoly<2, PrimeFieldElement64<541>>>(),
            c in any::<SparseMultiPoly<2, PrimeFieldElement64<541>>>()) {
            prop_assert_eq!(&(&a * &b) * &c, &a * &(&b * &c));
        }

        /// a * (b + c) = a * b + a * c
        #[test]
        fn test_mul_distributes_over_add(
            a in any::<SparseMultiPoly<2, PrimeFieldElement64<541>>>(),
            b in any::<SparseMultiPoly<2, PrimeFieldElement64<541>>>(),
            c in any::<SparseMultiPoly<2, PrimeFieldElement64<541>>>()) {
            prop_assert_eq!(&a * &(&b + &c), &(&a * &b) + &(&a * &c));
        }
    }

    /// `(a * b) * c = a * (b * c)` over `F` in `N` variables.
    ///
    /// A proptest driven through [`TestRunner`] rather than written with `proptest!`, because the
    /// macro expands to a `#[test]` item and so cannot sit inside `for_each_field!`'s generic body.
    fn assert_mul_associates<const N: usize, F: FiniteField>() {
        let strategy = (
            poly_strategy::<N, F>(4),
            poly_strategy::<N, F>(4),
            poly_strategy::<N, F>(4),
        );
        TestRunner::deterministic()
            .run(&strategy, |(a, b, c)| {
                prop_assert_eq!(&(&a * &b) * &c, &a * &(&b * &c));
                Ok(())
            })
            .unwrap();
    }

    /// `a * (b + c) = a * b + a * c` over `F` in `N` variables.
    fn assert_mul_distributes<const N: usize, F: FiniteField>() {
        let strategy = (
            poly_strategy::<N, F>(4),
            poly_strategy::<N, F>(4),
            poly_strategy::<N, F>(4),
        );
        TestRunner::deterministic()
            .run(&strategy, |(a, b, c)| {
                prop_assert_eq!(&a * &(&b + &c), &(&a * &b) + &(&a * &c));
                Ok(())
            })
            .unwrap();
    }

    // Multiplication associates, over every field and at two arities.
    for_each_field!(
        fn multiplication_associates<F>() {
            assert_mul_associates::<2, F>();
            assert_mul_associates::<3, F>();
        }
    );

    // Multiplication distributes over addition, over every field and at two arities.
    for_each_field!(
        fn multiplication_distributes<F>() {
            assert_mul_distributes::<2, F>();
            assert_mul_distributes::<3, F>();
        }
    );

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
            // p / y = (5*x^11*y + 3*x) * y + 14*x^3
            //
            // Both 5*x^11*y^2 and 3*x*y are divisible by y, so both belong in the quotient. This
            // expectation previously stopped at the first irreducible term and left 3*x*y in the
            // remainder, where it was still divisible by the divisor.
            let (q, r) = p.div_rem(
                &SparseMultiPoly::parse("y", vars).unwrap(),
                MonomialOrder::Lexicographic,
            );
            assert_eq!(q, SparseMultiPoly::parse("5*x^11*y + 3*x", vars).unwrap());
            assert_eq!(r, SparseMultiPoly::parse("14*x^3", vars).unwrap());
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
            for monomial in remainder.terms.keys() {
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

    /// Division leaves a remainder no monomial of which is divisible by the divisor's lead.
    ///
    /// Regression test: `div_rem` used to return as soon as the *leading* term was not
    /// divisible, leaving lower reducible terms behind. The identity f = q*g + r still held, so
    /// only the normal-form property was violated.
    #[test]
    fn test_div_rem_reduces_every_divisible_term() {
        type F = PrimeFieldElement64<13>;
        let vars = ["x", "y", "z"];
        let parse = |s: &str| MultivariatePolynomial::<3, F>::parse(s, vars).unwrap();

        for order in ALL_ORDERS {
            // LT(x^2 + y) is x^2 under every order here, which y does not divide — but the
            // lower term y does.
            let f = parse("x^2 + y");
            let g = parse("y");
            let (q, r) = f.div_rem(&g, order);

            assert_eq!(q, parse("1"), "{}", order.name());
            assert_eq!(r, parse("x^2"), "{}", order.name());
            assert_eq!(&(&q * &g) + &r, f, "{}: f = q*g + r violated", order.name());
            assert!(
                !r.terms()
                    .keys()
                    .any(|m| m.checked_div(&g.leading_monomial(order)).is_some()),
                "{}: remainder still has a term divisible by LT(g)",
                order.name()
            );
        }
    }

    /// `div_rem` agrees with `multi_div_rem` given a single divisor.
    ///
    /// `multi_div_rem` already satisfied the contract, so it serves as the oracle.
    #[test]
    fn test_div_rem_agrees_with_multi_div_rem() {
        type F = PrimeFieldElement64<13>;
        let vars = ["x", "y", "z"];
        let parse = |s: &str| MultivariatePolynomial::<3, F>::parse(s, vars).unwrap();

        let cases = [
            ("x^2 + y", "y"),
            ("x^2*y + x + y + 1", "y"),
            ("x^3 + x^2*y + z", "x^2"),
            ("x*y*z + x + y + z + 1", "z"),
            ("x^2 + 2*x*y + y^2", "x + y"),
            ("x^5 + 1", "x^2 + 1"),
            ("z^4 + y^2 + x", "x"),
        ];

        for order in ALL_ORDERS {
            for (dividend, divisor) in cases {
                let f = parse(dividend);
                let g = parse(divisor);
                let (q, r) = f.div_rem(&g, order);
                let (qs, r_multi) = f.multi_div_rem(std::slice::from_ref(&g), order);
                assert_eq!(
                    (q, r),
                    (qs[0].clone(), r_multi),
                    "{} / {} under {}",
                    dividend,
                    divisor,
                    order.name()
                );
            }
        }
    }

    proptest! {
        /// Over random input, division satisfies both halves of its contract.
        #[test]
        fn test_div_rem_contract(
            f in any::<MultivariatePolynomial<3, PrimeFieldElement64<13>>>(),
            g in any::<MultivariatePolynomial<3, PrimeFieldElement64<13>>>()) {
            prop_assume!(!g.is_zero());
            for order in ALL_ORDERS {
                let (q, r) = f.div_rem(&g, order);
                // f = q*g + r
                prop_assert_eq!(&(&q * &g) + &r, f.clone(), "{}", order.name());
                // and no monomial of r is divisible by LT(g)
                let lead = g.leading_monomial(order);
                for m in r.terms().keys() {
                    prop_assert!(
                        m.checked_div(&lead).is_none(),
                        "{}: {:?} is divisible by LT(g) = {:?}",
                        order.name(), m.exponents(), lead.exponents()
                    );
                }
            }
        }
    }

    /// `normal_form` agrees with `multi_div_rem` on **random** inputs, over several fields,
    /// arities and all three orders.
    ///
    /// The hand-written cases below cover the shapes someone thought of. This covers the one
    /// nobody can enumerate: where the shifted divisor tail lands *inside* the working polynomial,
    /// which is the boundary the windowed merge in `subtract_shifted` computes with
    /// `partition_point`. An off-by-one there would drop or duplicate exactly one term, and
    /// `multi_div_rem` — which reduces by rebuilding polynomials and never calls
    /// `subtract_shifted` — is the independent oracle that would catch it.
    #[test]
    fn test_normal_form_agrees_with_multi_div_rem_on_random_input() {
        fn case<const N: usize, F: FiniteField>() {
            let mut runner = TestRunner::default();
            runner
                .run(
                    &(
                        poly_strategy::<N, F>(12),
                        vec(poly_strategy::<N, F>(5), 1..5),
                    ),
                    |(dividend, divisors)| {
                        let divisors: Vec<_> =
                            divisors.into_iter().filter(|d| !d.is_zero()).collect();
                        if divisors.is_empty() {
                            return Ok(());
                        }
                        for order in [
                            MonomialOrder::Lexicographic,
                            MonomialOrder::GradedLexicographic,
                            MonomialOrder::GradedReverseLexicographic,
                        ] {
                            prop_assert_eq!(
                                dividend.normal_form(&divisors, order),
                                dividend.multi_div_rem(&divisors, order).1
                            );
                        }
                        Ok(())
                    },
                )
                .expect("normal_form agrees with its oracle on random input");
        }
        case::<1, PrimeFieldElement64<13>>();
        case::<2, PrimeFieldElement64<13>>();
        case::<3, PrimeFieldElement64<7>>();
        case::<4, PrimeFieldElement64<2147483647>>();
        case::<6, PrimeFieldElement64<13>>();
    }

    /// The windowed merge's prefix boundary, exercised directly rather than through a reduction.
    ///
    /// `subtract_shifted` binary-searches for the smallest shifted tail term and copies everything
    /// below it. These cases put the boundary at each of the three places it can be: below every
    /// working term, above every working term, and strictly inside.
    #[test]
    fn test_the_merge_window_is_correct_at_each_boundary() {
        type F = PrimeFieldElement64<13>;
        let order = MonomialOrder::Lexicographic;
        let vars = ["x"];
        let parse = |s: &str| MultivariatePolynomial::<1, F>::parse(s, vars).unwrap();

        // Reducing by `x^k - 1` shifts a tail of `{1}` to `{x^{d-k}}`, so the boundary's position
        // inside the working polynomial is controlled by `k` against the dividend's spread.
        let cases: [(&str, &str); 5] = [
            // The tail lands below every surviving term.
            ("x^9 + x^8 + x^7", "x^9 - 1"),
            // The tail lands above every surviving term.
            ("x^9 + x + 1", "x^9 - x^8"),
            // Strictly inside.
            ("x^9 + x^6 + x^3 + 1", "x^9 - x^5"),
            ("x^12 + x^7 + x^2", "x^12 - x^4"),
            // And a case where the merge cancels, which only fires on `Ordering::Equal`.
            ("x^9 + x^4", "x^9 + x^4"),
        ];

        for (dividend, divisor) in cases {
            let f = parse(dividend);
            let d = parse(divisor);
            assert_eq!(
                f.normal_form(std::slice::from_ref(&d), order),
                f.multi_div_rem(std::slice::from_ref(&d), order).1,
                "{dividend} modulo {divisor}"
            );
        }
    }

    /// `normal_form` returns exactly the remainder `multi_div_rem` does.
    ///
    /// `multi_div_rem` is the existing, independently tested implementation, so it is the oracle
    /// for the optimized one. Divisor order matters to both, so the sets are passed in the same
    /// order rather than sorted.
    #[test]
    fn test_normal_form_agrees_with_multi_div_rem() {
        type F = PrimeFieldElement64<13>;
        let vars = ["x", "y", "z"];
        let parse = |s: &str| MultivariatePolynomial::<3, F>::parse(s, vars).unwrap();

        let cases: Vec<(&str, Vec<&str>)> = vec![
            ("x^2 + y", vec!["y"]),
            ("x^2 + y", vec!["x"]),
            ("x^2*y + x + y + 1", vec!["y", "x"]),
            ("x^3 + x^2*y + z", vec!["x^2", "y"]),
            ("x*y*z + x + y + z + 1", vec!["z", "y", "x"]),
            ("x^2 + 2*x*y + y^2", vec!["x + y"]),
            ("x^5 + 1", vec!["x^2 + 1"]),
            ("z^4 + y^2 + x", vec!["x", "y", "z"]),
            // Divisor order changes the remainder, so both must agree on each arrangement.
            ("x^2*y^2 + x*y + 1", vec!["x*y - 1", "y^2 - 1"]),
            ("x^2*y^2 + x*y + 1", vec!["y^2 - 1", "x*y - 1"]),
            // A reducible lower term beneath an irreducible lead.
            ("z^5 + x*y", vec!["x"]),
            // A divisor that cannot reduce anything.
            ("x + y + z", vec!["x^9"]),
            // A zero divisor mixed in must be ignored by both.
            ("x^2 + y", vec!["y", "0"]),
            ("x^2 + y", vec!["0", "y"]),
        ];

        for order in ALL_ORDERS {
            for (dividend, divisors) in &cases {
                let f = parse(dividend);
                let ds: Vec<MultivariatePolynomial<3, F>> =
                    divisors.iter().map(|s| parse(s)).collect();
                assert_eq!(
                    f.normal_form(&ds, order),
                    f.multi_div_rem(&ds, order).1,
                    "{} modulo {:?} under {}",
                    dividend,
                    divisors,
                    order.name()
                );
            }
        }
    }

    proptest! {
        /// Over random input, `normal_form` matches the oracle and satisfies the contract.
        #[test]
        fn test_normal_form_matches_the_oracle(
            f in any::<MultivariatePolynomial<3, PrimeFieldElement64<13>>>(),
            d1 in any::<MultivariatePolynomial<3, PrimeFieldElement64<13>>>(),
            d2 in any::<MultivariatePolynomial<3, PrimeFieldElement64<13>>>()) {
            prop_assume!(!d1.is_zero() || !d2.is_zero());
            let divisors = [d1, d2];
            for order in ALL_ORDERS {
                let normal = f.normal_form(&divisors, order);
                prop_assert_eq!(
                    normal.clone(),
                    f.multi_div_rem(&divisors, order).1,
                    "{}", order.name()
                );
                // And the defining property: nothing left is reducible.
                for m in normal.terms().keys() {
                    for d in divisors.iter().filter(|d| !d.is_zero()) {
                        prop_assert!(
                            m.checked_div(&d.leading_monomial(order)).is_none(),
                            "{}: {:?} is still divisible", order.name(), m.exponents()
                        );
                    }
                }
            }
        }
    }

    /// Reduction by a set containing only zeros leaves the polynomial untouched.
    #[test]
    fn test_normal_form_with_no_usable_divisors() {
        type F = PrimeFieldElement64<13>;
        let vars = ["x", "y", "z"];
        let f = MultivariatePolynomial::<3, F>::parse("x^2 + y", vars).unwrap();
        let zero = MultivariatePolynomial::<3, F>::zero();
        for order in ALL_ORDERS {
            assert_eq!(f.normal_form(&[], order), f, "{}", order.name());
            assert_eq!(
                f.normal_form(std::slice::from_ref(&zero), order),
                f,
                "{}",
                order.name()
            );
        }
    }

    /// Reduction by a non-monic divisor scales by the leading coefficient's inverse.
    ///
    /// Buchberger makes every reducer monic, so the non-monic path is only reachable through the
    /// public API and would otherwise go untested by the Gröbner tests.
    #[test]
    fn test_normal_form_by_a_non_monic_divisor() {
        type F = PrimeFieldElement64<13>;
        let vars = ["x", "y"];
        // 3x - 1 has leading coefficient 3, whose inverse mod 13 is 9.
        let divisor = MultivariatePolynomial::<2, F>::parse("3*x - 1", vars).unwrap();
        let f = MultivariatePolynomial::<2, F>::parse("x^2 + y", vars).unwrap();

        for order in ALL_ORDERS {
            // The quotient is 9x + 3 and (9x + 3)(3x - 1) = 27x^2 - 3 = x^2 - 3 mod 13, so the
            // normal form is y + 3. Note 1/3 = 9 and 9/3 = 3 mod 13.
            let expected = MultivariatePolynomial::<2, F>::parse("y + 3", vars).unwrap();
            assert_eq!(
                f.normal_form(std::slice::from_ref(&divisor), order),
                expected,
                "{}",
                order.name()
            );
            // And it still agrees with the independent oracle.
            assert_eq!(
                f.normal_form(std::slice::from_ref(&divisor), order),
                f.multi_div_rem(std::slice::from_ref(&divisor), order).1,
                "{}",
                order.name()
            );
        }
    }

    const ALL_ORDERS: [MonomialOrder; 3] = [
        MonomialOrder::Lexicographic,
        MonomialOrder::GradedLexicographic,
        MonomialOrder::GradedReverseLexicographic,
    ];

    // === in-place Add, Sub and scale (#361) ===
    //
    // The collecting forms mutate one operand's map instead of building a third, so the risk they
    // carry is not a wrong sum but a wrong *representation*: a coefficient that cancelled and was
    // left in the map, or a term merged into the operand that was supposed to be read-only. Every
    // test below pins one of those.
    //
    // `a += &a` and `a -= &a` are not spellable in safe Rust — `&mut a` and `&a` cannot coexist —
    // so self-assignment is exercised through a clone, which is the aliasing the borrow checker
    // does permit and the one `div_rem`'s `working -= &q * divisor` actually reaches.

    /// Three polynomials with overlapping support, so merging them exercises hit, miss and cancel.
    fn overlapping_triple<const N: usize, F: FiniteField>() -> (
        SparseMultiPoly<N, F>,
        SparseMultiPoly<N, F>,
        SparseMultiPoly<N, F>,
    ) {
        let mut low = [0u32; N];
        low[0] = 1;
        let mut mid = [0u32; N];
        mid[N - 1] = 2;
        let mut high = [1u32; N];

        let a = SparseMultiPoly::new(&[
            (Monomial::new(&low), F::new(3)),
            (Monomial::new(&mid), F::new(5)),
        ]);
        let b = SparseMultiPoly::new(&[
            (Monomial::new(&mid), F::new(7)),
            (Monomial::new(&high), F::new(11)),
        ]);
        high[0] += 1;
        let c = SparseMultiPoly::new(&[(Monomial::new(&high), F::new(13))]);
        (a, b, c)
    }

    /// `a += &b` leaves `a` equal to `&a + &b`, and leaves `b` untouched.
    #[test]
    fn test_add_assign_agrees_with_add_and_does_not_disturb_the_right_operand() {
        type F = PrimeFieldElement64<541>;
        let (a, b, _) = overlapping_triple::<3, F>();
        let expected = &a + &b;
        let b_before = b.clone();

        let mut accumulator = a.clone();
        accumulator += &b;
        assert_eq!(accumulator, expected);
        assert_eq!(b, b_before, "the right operand was mutated");
    }

    /// `a -= &b` leaves `a` equal to `&a - &b`, and leaves `b` untouched.
    #[test]
    fn test_sub_assign_agrees_with_sub_and_does_not_disturb_the_right_operand() {
        type F = PrimeFieldElement64<541>;
        let (a, b, _) = overlapping_triple::<3, F>();
        let expected = &a - &b;
        let b_before = b.clone();

        let mut accumulator = a.clone();
        accumulator -= &b;
        assert_eq!(accumulator, expected);
        assert_eq!(b, b_before, "the right operand was mutated");
    }

    /// Every ownership spelling of `+` and `-` returns the same polynomial.
    #[test]
    fn test_add_and_sub_agree_across_every_ownership_spelling() {
        type F = PrimeFieldElement64<541>;
        let (a, b, _) = overlapping_triple::<2, F>();
        let sum = &a + &b;
        let difference = &a - &b;

        assert_eq!(a.clone() + &b, sum);
        assert_eq!(&a + b.clone(), sum);
        assert_eq!(a.clone() + b.clone(), sum);
        assert_eq!(&mut a.clone() + &mut b.clone(), sum);
        assert_eq!(
            {
                let mut t = a.clone();
                t += b.clone();
                t
            },
            sum
        );
        assert_eq!(
            {
                let mut t = a.clone();
                t += &b;
                t
            },
            sum
        );

        assert_eq!(a.clone() - &b, difference);
        assert_eq!(&a - b.clone(), difference);
        assert_eq!(a.clone() - b.clone(), difference);
        assert_eq!(&mut a.clone() - &mut b.clone(), difference);
        assert_eq!(
            {
                let mut t = a.clone();
                t -= b.clone();
                t
            },
            difference
        );
        assert_eq!(
            {
                let mut t = a.clone();
                t -= &b;
                t
            },
            difference
        );
    }

    /// Adding a clone of a polynomial to itself doubles it rather than aliasing the accumulator.
    #[test]
    fn test_add_assign_of_a_clone_of_self_doubles() {
        type F = PrimeFieldElement64<541>;
        let (a, _, _) = overlapping_triple::<3, F>();
        let doubled = a.scale(&F::new(2));

        let mut owned = a.clone();
        owned += a.clone();
        assert_eq!(owned, doubled);

        let mut borrowed = a.clone();
        borrowed += &a.clone();
        assert_eq!(borrowed, doubled);
        assert_eq!(borrowed.terms().len(), a.terms().len(), "support changed");
    }

    /// Subtracting a clone of a polynomial from itself is the zero polynomial, with no terms left.
    #[test]
    fn test_sub_assign_of_a_clone_of_self_is_the_empty_polynomial() {
        type F = PrimeFieldElement64<541>;
        let (a, _, _) = overlapping_triple::<3, F>();

        let mut owned = a.clone();
        owned -= a.clone();
        assert!(owned.is_zero());
        assert!(
            owned.terms().is_empty(),
            "a cancelled monomial was kept with a zero coefficient: {:?}",
            owned.terms()
        );

        let mut borrowed = a.clone();
        borrowed -= &a.clone();
        assert_eq!(borrowed, SparseMultiPoly::zero());
        assert!(borrowed.terms().is_empty());
    }

    /// `+=` and `-=` drop a monomial whose coefficient cancels rather than storing a zero.
    #[test]
    fn test_in_place_add_and_sub_drop_cancelled_monomials() {
        type F = PrimeFieldElement64<13>;
        let x = Monomial::<2>::new(&[1, 0]);
        let y = Monomial::<2>::new(&[0, 1]);

        // 5x + y plus 8x is y: 5 + 8 = 13 = 0 mod 13.
        let mut p: SparseMultiPoly<2, F> = SparseMultiPoly::new(&[(x, F::new(5)), (y, F::new(1))]);
        p += SparseMultiPoly::new(&[(x, F::new(8))]);
        assert_eq!(p, SparseMultiPoly::new(&[(y, F::new(1))]));
        assert!(!p.terms().contains_key(&x), "x survived its cancellation");
        assert!(p.terms().values().all(|c| !c.is_zero()));

        // And by subtraction, which cancels on equal coefficients.
        let mut q: SparseMultiPoly<2, F> = SparseMultiPoly::new(&[(x, F::new(5)), (y, F::new(1))]);
        q -= SparseMultiPoly::new(&[(x, F::new(5))]);
        assert_eq!(q, SparseMultiPoly::new(&[(y, F::new(1))]));
        assert!(!q.terms().contains_key(&x));
        assert!(q.terms().values().all(|c| !c.is_zero()));
    }

    /// Adding a monomial that cancels and then adding it back restores the term.
    ///
    /// A map entry removed on cancellation must be re-insertable; an implementation that left a
    /// zero behind would pass the first half of this and fail nothing else.
    #[test]
    fn test_a_cancelled_monomial_can_be_added_back() {
        type F = PrimeFieldElement64<13>;
        let x = Monomial::<2>::new(&[1, 0]);
        let p: SparseMultiPoly<2, F> = SparseMultiPoly::new(&[(x, F::new(4))]);

        let mut accumulator = p.clone();
        accumulator -= &p;
        assert!(accumulator.terms().is_empty());
        accumulator += &p;
        assert_eq!(accumulator, p);
    }

    /// `scale_assign` agrees with `scale`, including the zero and one factors.
    #[test]
    fn test_scale_assign_agrees_with_scale() {
        type F = PrimeFieldElement64<541>;
        let (a, _, _) = overlapping_triple::<3, F>();

        for factor in [F::zero(), F::one(), F::new(7), F::new(540)] {
            let mut scaled = a.clone();
            scaled.scale_assign(&factor);
            assert_eq!(scaled, a.scale(&factor), "factor {}", factor);
            assert!(scaled.terms().values().all(|c| !c.is_zero()));
        }

        // Scaling by zero is the zero polynomial held as no terms at all, not as zero coefficients.
        let mut zeroed = a.clone();
        zeroed.scale_assign(&F::zero());
        assert!(zeroed.terms().is_empty());

        // Scaling by one is the identity, on the support as well as on the value.
        let mut unchanged = a.clone();
        unchanged.scale_assign(&F::one());
        assert_eq!(unchanged, a);
    }

    /// Negation is the additive inverse and keeps no zero coefficient.
    #[test]
    fn test_neg_is_the_additive_inverse_in_place() {
        type F = PrimeFieldElement64<541>;
        let (a, _, _) = overlapping_triple::<3, F>();

        let negated = -a.clone();
        assert_eq!(negated.terms().len(), a.terms().len());
        assert!(negated.terms().values().all(|c| !c.is_zero()));
        assert_eq!(&a + &negated, SparseMultiPoly::zero());
        assert_eq!(-negated, a);
    }

    /// `+=` agrees with `+`, `-=` with `-`, and addition associates, over `F` in `N` variables.
    fn assert_in_place_add_agrees<const N: usize, F: FiniteField>() {
        let strategy = (
            poly_strategy::<N, F>(4),
            poly_strategy::<N, F>(4),
            poly_strategy::<N, F>(4),
        );
        TestRunner::deterministic()
            .run(&strategy, |(a, b, c)| {
                let mut accumulated = a.clone();
                accumulated += &b;
                prop_assert_eq!(&accumulated, &(&a + &b));

                let mut subtracted = a.clone();
                subtracted -= &b;
                prop_assert_eq!(&subtracted, &(&a - &b));

                // (a + b) + c = a + (b + c), folded in place on the left as the MDS layer does.
                let mut folded = a.clone();
                folded += &b;
                folded += &c;
                prop_assert_eq!(&folded, &(&a + &(&b + &c)));

                // No operation leaves a zero coefficient in the map.
                for p in [&accumulated, &subtracted, &folded] {
                    prop_assert!(p.terms().values().all(|coefficient| !coefficient.is_zero()));
                }

                // Scaling in place agrees with scaling out of place, including by zero. The third
                // factor is drawn rather than written as `F::new(3)`, which is unimplemented for
                // the binary fields `for_each_field!` covers.
                let drawn = b.leading_coefficient(MonomialOrder::Lexicographic);
                for factor in [F::zero(), F::one(), drawn] {
                    let mut scaled = a.clone();
                    scaled.scale_assign(&factor);
                    prop_assert_eq!(&scaled, &a.scale(&factor));
                }
                Ok(())
            })
            .unwrap();
    }

    // In-place addition, subtraction and scaling agree with the allocating forms, over every field
    // and at three arities.
    for_each_field!(
        fn in_place_arithmetic_agrees<F>() {
            assert_in_place_add_agrees::<1, F>();
            assert_in_place_add_agrees::<2, F>();
            assert_in_place_add_agrees::<3, F>();
        }
    );

    /// Counting cannot change the answer: the two entry points agree on random inputs over
    /// several fields and arities, which is what makes the counted path usable as evidence about
    /// the uncounted one.
    #[test]
    fn test_counting_does_not_change_the_normal_form() {
        fn case<const N: usize, F: FiniteField>() {
            let mut runner = TestRunner::default();
            runner
                .run(
                    &(
                        poly_strategy::<N, F>(8),
                        vec(poly_strategy::<N, F>(4), 1..4),
                    ),
                    |(dividend, divisors)| {
                        let divisors: Vec<_> =
                            divisors.into_iter().filter(|d| !d.is_zero()).collect();
                        if divisors.is_empty() {
                            return Ok(());
                        }
                        for order in [
                            MonomialOrder::Lexicographic,
                            MonomialOrder::GradedLexicographic,
                            MonomialOrder::GradedReverseLexicographic,
                        ] {
                            let plain = dividend.normal_form(&divisors, order);
                            let (counted, _) = dividend.normal_form_counted(&divisors, order);
                            prop_assert_eq!(&plain, &counted);
                        }
                        Ok(())
                    },
                )
                .expect("counted and uncounted normal forms agree");
        }
        case::<2, PrimeFieldElement64<13>>();
        case::<3, PrimeFieldElement64<7>>();
        case::<4, PrimeFieldElement64<2147483647>>();
    }

    /// The counters describe a reduction that does no work: an irreducible dividend pops its own
    /// terms once, keeps all of them, and takes no reduction step.
    #[test]
    fn test_an_irreducible_dividend_shows_no_swell() {
        type F = PrimeFieldElement64<13>;
        let order = MonomialOrder::GradedReverseLexicographic;
        let dividend =
            MultivariatePolynomial::<2, F>::parse("x + y", ["x", "y"]).expect("a polynomial");
        let divisor =
            MultivariatePolynomial::<2, F>::parse("x^5*y^5", ["x", "y"]).expect("a polynomial");

        let (remainder, counts) = dividend.normal_form_counted(&[divisor], order);

        assert_eq!(remainder, dividend, "nothing divides, so nothing reduces");
        assert_eq!(counts.calls, 1);
        assert_eq!(counts.reduction_steps, 0);
        assert_eq!(counts.terms_popped, 2);
        assert_eq!(counts.remainder_terms, 2);
        assert_eq!(counts.terms_rewritten, 0);
        assert_eq!(counts.swell_factor(), 1.0, "every term looked at survived");
        // One divisor, so one test per term popped.
        assert_eq!(counts.divisor_tests, 2);
        assert_eq!(counts.divisor_tests_per_term(), 1.0);
    }

    /// And the counters separate the two costs they exist to separate. Reducing `x^n` by `x - 1`
    /// pops one term per degree step and keeps exactly one, so the swell factor grows with `n`
    /// while the scan length stays at one divisor.
    #[test]
    fn test_the_counters_separate_swell_from_scan_length() {
        type F = PrimeFieldElement64<13>;
        let order = MonomialOrder::Lexicographic;
        let divisor = MultivariatePolynomial::<1, F>::parse("x - 1", ["x"]).expect("a polynomial");

        let mut previous_swell = 0.0;
        for degree in [4u32, 8, 16] {
            let dividend = MultivariatePolynomial::<1, F>::parse(&format!("x^{degree}"), ["x"])
                .expect("a polynomial");
            let (remainder, counts) =
                dividend.normal_form_counted(std::slice::from_ref(&divisor), order);

            assert_eq!(remainder, MultivariatePolynomial::<1, F>::one());
            // `x^d -> x^{d-1} -> ... -> 1`: one reduction step per degree, one surviving term.
            assert_eq!(counts.reduction_steps, degree as usize);
            assert_eq!(counts.remainder_terms, 1);
            assert_eq!(counts.terms_popped, degree as usize + 1);
            // Swell grows with the degree; the scan never does, because there is one divisor.
            assert!(counts.swell_factor() > previous_swell);
            previous_swell = counts.swell_factor();
            assert_eq!(counts.divisor_tests_per_term(), 1.0);
        }
    }

    /// Accumulating counts across reductions adds the totals and takes the maximum of the peak,
    /// which is what lets one value describe a whole interreduction.
    #[test]
    fn test_counts_accumulate_totals_and_peaks() {
        use crate::poly::NormalFormCounts;
        let mut total = NormalFormCounts::default();
        let a = NormalFormCounts {
            calls: 1,
            terms_popped: 10,
            max_working_terms: 7,
            remainder_terms: 2,
            ..Default::default()
        };
        let b = NormalFormCounts {
            calls: 1,
            terms_popped: 30,
            max_working_terms: 4,
            remainder_terms: 3,
            ..Default::default()
        };
        total.add(&a);
        total.add(&b);
        assert_eq!(total.calls, 2);
        assert_eq!(total.terms_popped, 40);
        assert_eq!(total.max_working_terms, 7, "a peak is a maximum, not a sum");
        assert_eq!(total.remainder_terms, 5);
        assert_eq!(total.swell_factor(), 8.0);
    }
}
