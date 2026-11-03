//! Symbolic preprocessing: turning a batch of critical pairs into a set of matrix rows.
//!
//! For a pair `(f, g)` with `m = lcm(LM(f), LM(g))`, F4 puts **both** multiples `(m/LT(f))*f` and
//! `(m/LT(g))*g` into the matrix rather than their difference. Their difference is the
//! S-polynomial, so elimination still recovers it; keeping the halves apart is what lets one
//! matrix cancel across the whole batch instead of once per pair.
//!
//! Reducing those rows needs more rows. Whenever a monomial appearing in some row is divisible by
//! the leading monomial of a basis element, the corresponding multiple of that element has to be
//! present too, or the matrix cannot perform the reduction that polynomial division would. Adding
//! those multiples introduces further monomials, so the process is iterated to a fixed point:
//!
//! > **Closure invariant.** For every row `h` and every monomial `u` in the support of `h`: if `u`
//! > is divisible by `LM(g)` for some basis element `g`, then some row has leading monomial `u`.
//!
//! The pair multiples satisfy it at `u = m` by themselves, since each half has leading monomial
//! `m` — which is why the lcm is seeded as already covered and must not acquire a reducer of its
//! own. Everything else that is reducible gets `(u / LM(g)) * g`, whose leading monomial is `u`.
//!
//! The invariant does not refer to the order monomials are examined in, so any deterministic
//! traversal reaches the same set of rows. Termination does not depend on it either: a row's
//! non-leading monomials are strictly below the monomial that produced it, and a monomial order
//! admits no infinite descending chain.
//!
//! See Faugère (1999), Sec 2.1, where this is `SymbolicPreprocessing`.

use std::collections::{HashMap, HashSet, VecDeque};

use crate::{
    grobner::{f4::options::ReducerSelection, pairs::CriticalPair},
    poly::MonomialOrder,
    FiniteField, Monomial, MultivariatePolynomial,
};

/// What one symbolic preprocessing pass cost.
///
/// The counters exist because the preceding milestone's bottleneck list is a set of hypotheses.
/// "Divisor lookup is a linear scan" predicts [`SymbolicCounts::divisor_scan_steps`] grows with
/// the basis size times [`SymbolicCounts::divisor_queries`]; "reducer multiples are rebuilt every
/// batch" predicts nothing at all about whether the *same* multiple recurs, which is what
/// [`SymbolicCounts::reducer_rows_reused`] is there to find out.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct SymbolicCounts {
    /// Monomials tested for reducibility.
    pub divisor_queries: usize,

    /// Basis elements examined across all those tests.
    pub divisor_scan_steps: usize,

    /// Reducer multiples whose built terms came from the cache rather than being recomputed.
    pub reducer_rows_reused: usize,
}

impl SymbolicCounts {
    /// Fold another pass's counters into these.
    pub fn add(&mut self, other: &Self) {
        self.divisor_queries += other.divisor_queries;
        self.divisor_scan_steps += other.divisor_scan_steps;
        self.reducer_rows_reused += other.reducer_rows_reused;
    }
}

/// What a [`ReducerCache`] does.
///
/// Three modes rather than a flag, because the question "would a cache pay?" has to be answerable
/// *without* building one. [`CacheMode::Count`] answers it: it records which multiples were
/// needed, so the repetition rate across batches is measurable at the cost of one monomial per
/// distinct multiple and with no change whatsoever to what is computed.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum CacheMode {
    /// Remember nothing. The baseline.
    #[default]
    Off,

    /// Remember which multiples were needed, but not their terms.
    ///
    /// The measurement mode. Nothing is served from it, so the computation is bit-identical to
    /// [`CacheMode::Off`]; only the counters differ.
    Count,

    /// Remember the built terms and serve them.
    Store,
}

/// Built reducer multiples, kept between batches.
///
/// Cross-batch state is the one thing in F4 that can make a batch's output depend on what came
/// before it, so it is passed explicitly rather than held anywhere ambient: "the result is a
/// function of the input and the options" stays checkable only if every input appears in a
/// signature.
///
/// What is cacheable is the **shifted terms** of a multiple — the basis element's monomials each
/// multiplied by the multiplier, which is where the monomial arithmetic goes. The built *sparse
/// row* is not: its column indices are relative to the batch's own column set, and no two batches
/// have the same one. An implementation that expected to cache rows would find that out late.
#[derive(Clone, Debug, Default)]
pub struct ReducerCache<const N: usize, F: FiniteField> {
    mode: CacheMode,

    /// Every multiple needed so far, for the repetition measurement. Empty when off.
    seen: HashSet<(usize, Monomial<N>)>,

    /// The built terms, under [`CacheMode::Store`] only.
    terms: HashMap<(usize, Monomial<N>), Vec<(Monomial<N>, F)>>,

    /// Multiples needed that had been needed before.
    repeats: usize,

    /// Multiples needed for the first time.
    firsts: usize,
}

impl<const N: usize, F: FiniteField> ReducerCache<N, F> {
    pub fn new(mode: CacheMode) -> Self {
        Self {
            mode,
            seen: HashSet::new(),
            terms: HashMap::new(),
            repeats: 0,
            firsts: 0,
        }
    }

    /// A cache that remembers nothing, for a caller that does not want one.
    pub fn disabled() -> Self {
        Self::new(CacheMode::Off)
    }

    /// A cache that measures repetition without serving anything.
    pub fn counting() -> Self {
        Self::new(CacheMode::Count)
    }

    pub fn mode(&self) -> CacheMode {
        self.mode
    }

    /// The number of distinct multiples remembered.
    pub fn len(&self) -> usize {
        self.seen.len()
    }

    pub fn is_empty(&self) -> bool {
        self.seen.is_empty()
    }

    /// Note that a multiple is needed, and report whether it has been needed before.
    ///
    /// Always `false` under [`CacheMode::Off`], which records nothing — so the baseline pays a
    /// branch and no allocation.
    pub fn record(&mut self, key: (usize, Monomial<N>)) -> bool {
        if self.mode == CacheMode::Off {
            return false;
        }
        if self.seen.insert(key) {
            self.firsts += 1;
            false
        } else {
            self.repeats += 1;
            true
        }
    }

    /// Multiples needed that had been needed before, and multiples needed for the first time.
    pub fn repeats_and_firsts(&self) -> (usize, usize) {
        (self.repeats, self.firsts)
    }

    /// The share of needed multiples that had been built before.
    ///
    /// **This is the number that decides whether a reducer cache is worth building.** Zero when
    /// nothing was recorded, which is also the answer under [`CacheMode::Off`].
    pub fn repetition_rate(&self) -> f64 {
        let total = self.repeats + self.firsts;
        if total == 0 {
            0.0
        } else {
            self.repeats as f64 / total as f64
        }
    }

    /// The stored terms of a multiple, under [`CacheMode::Store`].
    pub fn terms(&self, key: &(usize, Monomial<N>)) -> Option<&[(Monomial<N>, F)]> {
        self.terms.get(key).map(|terms| terms.as_slice())
    }

    /// Store the built terms of a multiple. Does nothing except under [`CacheMode::Store`].
    pub fn store(&mut self, key: (usize, Monomial<N>), terms: Vec<(Monomial<N>, F)>) {
        if self.mode == CacheMode::Store {
            self.terms.insert(key, terms);
        }
    }

    /// Forget everything, keeping the mode and the counters.
    ///
    /// The bound a cache needs is on memory, and the basis grows throughout a computation, so an
    /// implementation that caps itself has to be able to start over. Discarding the contents
    /// cannot change a result — a miss is always recoverable by recomputing — which is what makes
    /// a bounded cache safe.
    pub fn clear(&mut self) {
        self.seen.clear();
        self.terms.clear();
    }
}

/// A basis element with everything F4 reads repeatedly precomputed.
///
/// `leading_monomial` on a `SparseMultiPoly` is a scan of the whole term map, and F4 asks for it
/// once per monomial tested for divisibility, so it is taken once here instead.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MonicElement<const N: usize, F: FiniteField> {
    /// The leading monomial under the order the basis was built for.
    pub leading_monomial: Monomial<N>,

    /// Every term, sorted descending by that order, scaled so the leading coefficient is one.
    pub terms: Vec<(Monomial<N>, F)>,
}

/// The current basis, made monic and indexed for divisibility queries.
///
/// Scaling to monic up front costs one multiplication per term, once per batch, and removes every
/// later coefficient fixup: a pair multiple is then just a shift of the terms. Scaling changes a
/// generator by a unit, so it generates the same ideal.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MonicBasis<const N: usize, F: FiniteField> {
    elements: Vec<MonicElement<N, F>>,
}

impl<const N: usize, F: FiniteField> MonicBasis<N, F> {
    /// Prepare a basis for F4 under the given order.
    ///
    /// Zero polynomials are not valid basis elements — they have no leading monomial to divide by
    /// — and are rejected rather than silently dropped, which would shift every later index and
    /// invalidate the critical pairs that refer to them.
    ///
    /// # Panics
    /// If any element is the zero polynomial.
    pub fn new(basis: &[MultivariatePolynomial<N, F>], order: MonomialOrder) -> Self {
        let elements = basis
            .iter()
            .enumerate()
            .map(|(index, polynomial)| {
                assert!(
                    !polynomial.is_zero(),
                    "basis element {} is zero and has no leading monomial",
                    index
                );

                let mut terms: Vec<(Monomial<N>, F)> = polynomial
                    .terms()
                    .iter()
                    .map(|(monomial, coefficient)| (*monomial, *coefficient))
                    .collect();
                terms.sort_by(|a, b| order.cmp(&b.0, &a.0));

                let leading_monomial = terms[0].0;
                let leading_coefficient = terms[0].1;
                if leading_coefficient != F::ONE {
                    let inverse = leading_coefficient.inverse();
                    for (_, coefficient) in terms.iter_mut() {
                        *coefficient *= inverse;
                    }
                }

                MonicElement {
                    leading_monomial,
                    terms,
                }
            })
            .collect();

        Self { elements }
    }

    pub fn len(&self) -> usize {
        self.elements.len()
    }

    pub fn is_empty(&self) -> bool {
        self.elements.is_empty()
    }

    pub fn element(&self, index: usize) -> &MonicElement<N, F> {
        &self.elements[index]
    }

    /// Append one element, as [`MonicBasis::new`] would have.
    ///
    /// The main loop grows the basis one element at a time, and rebuilding the whole structure per
    /// batch would re-sort every element's terms for nothing.
    ///
    /// # Panics
    /// If the polynomial is zero.
    pub fn push(&mut self, polynomial: &MultivariatePolynomial<N, F>, order: MonomialOrder) {
        let appended = Self::new(std::slice::from_ref(polynomial), order);
        self.elements.extend(appended.elements);
    }

    /// The leading monomial of each element, in index order.
    pub fn leading_monomials(&self) -> impl Iterator<Item = Monomial<N>> + '_ {
        self.elements.iter().map(|element| element.leading_monomial)
    }

    /// The first element, in index order, whose leading monomial divides `monomial`, with the
    /// quotient.
    ///
    /// First-applicable is a deliberately simple reducer-selection policy. It only has to be
    /// deterministic for the computation to be reproducible; preferring, say, the largest leading
    /// monomial would give smaller multiples and is an optimization for a later milestone.
    pub fn find_divisor(&self, monomial: &Monomial<N>) -> Option<(usize, Monomial<N>)> {
        self.elements
            .iter()
            .enumerate()
            .find_map(|(index, element)| {
                monomial
                    .checked_div(&element.leading_monomial)
                    .map(|quotient| (index, quotient))
            })
    }

    /// As [`MonicBasis::find_divisor`], under the given policy, counting the work.
    ///
    /// The frozen entry point for divisor lookup: an index or a filter goes behind this signature,
    /// and [`MonicBasis::find_divisor`] stays as the linear scan it must agree with. Agreement is
    /// not merely about returning *a* divisor — a different divisor is a different multiplier,
    /// hence a different row, hence a different matrix — so a faster lookup under
    /// [`ReducerSelection::FirstApplicable`] has to return the *same* divisor, and that is what the
    /// differential test checks.
    pub fn find_divisor_with(
        &self,
        monomial: &Monomial<N>,
        selection: ReducerSelection,
        counts: &mut SymbolicCounts,
    ) -> Option<(usize, Monomial<N>)> {
        counts.divisor_queries += 1;

        match selection {
            // The baseline: scan in index order and stop at the first hit. The scan step count is
            // what an index has to beat, so it is counted exactly — elements examined, which is
            // one more than the number rejected when the search succeeds.
            ReducerSelection::FirstApplicable | ReducerSelection::LargestLeadingMonomial => {
                for (index, element) in self.elements.iter().enumerate() {
                    counts.divisor_scan_steps += 1;
                    if let Some(quotient) = monomial.checked_div(&element.leading_monomial) {
                        return Some((index, quotient));
                    }
                }
                None
            }
        }
    }

    /// True if some basis element's leading monomial divides `monomial`.
    pub fn is_top_reducible(&self, monomial: &Monomial<N>) -> bool {
        self.find_divisor(monomial).is_some()
    }

    /// The terms of `multiplier * element(index)`, descending by the monomial order.
    ///
    /// Descending because the terms were sorted that way and a monomial order is multiplicative:
    /// shifting a sorted sequence of monomials by a common factor preserves their order.
    pub fn shifted_terms(
        &self,
        index: usize,
        multiplier: &Monomial<N>,
    ) -> impl Iterator<Item = (Monomial<N>, F)> + '_ {
        let multiplier = *multiplier;
        self.elements[index]
            .terms
            .iter()
            .map(move |(monomial, coefficient)| (monomial * &multiplier, *coefficient))
    }

    /// The polynomial `multiplier * element(index)`.
    ///
    /// Used by the tests, which check rows against polynomial arithmetic performed independently.
    pub fn shifted_polynomial(
        &self,
        index: usize,
        multiplier: &Monomial<N>,
    ) -> MultivariatePolynomial<N, F> {
        let terms: Vec<(Monomial<N>, F)> = self.shifted_terms(index, multiplier).collect();
        MultivariatePolynomial::new(&terms)
    }
}

/// Why a row was added to the matrix.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RowKind {
    /// One half of a critical pair's S-polynomial, identified by the pair's position in the batch.
    PairComponent { pair: usize },

    /// A reducer multiple, added to satisfy the closure invariant.
    Reducer,
}

/// A row of the Macaulay matrix: a basis element times a monomial.
///
/// Stored as the multiplier and the index rather than as an expanded polynomial, so that building
/// the matrix does not allocate and rebuild a term map per row.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct PreprocessedRow<const N: usize> {
    /// The monomial the basis element is multiplied by.
    pub multiplier: Monomial<N>,

    /// Which basis element.
    pub basis_index: usize,

    /// Where the row came from.
    pub kind: RowKind,
}

/// The rows a batch of critical pairs reduces to, and the leading monomials they already cover.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Preprocessed<const N: usize> {
    /// The rows, pair multiples first and then reducer multiples in the order they were needed.
    pub rows: Vec<PreprocessedRow<N>>,

    /// The leading monomials of `rows`.
    ///
    /// This is the set candidate extraction tests against: a pivot whose monomial is in here is a
    /// relation the batch already represented, and only a pivot outside it is new.
    pub leading_monomials: HashSet<Monomial<N>>,

    /// What finding those rows cost.
    pub counts: SymbolicCounts,
}

impl<const N: usize> Preprocessed<N> {
    /// The leading monomial of the row at `index`.
    pub fn leading_monomial<F: FiniteField>(
        &self,
        basis: &MonicBasis<N, F>,
        index: usize,
    ) -> Monomial<N> {
        let row = &self.rows[index];
        &basis.element(row.basis_index).leading_monomial * &row.multiplier
    }
}

/// The rows needed to reduce the S-polynomials of `pairs` by linear algebra alone.
///
/// Satisfies the closure invariant stated in the module documentation, which is what makes the
/// resulting matrix's new pivots genuinely new basis elements rather than relations the basis
/// already implies.
///
/// # Panics
/// If a pair names a basis element whose leading monomial does not divide the pair's lcm, which
/// would mean the pair was built against a different basis or a different monomial order.
pub fn symbolic_preprocessing<const N: usize, F: FiniteField>(
    basis: &MonicBasis<N, F>,
    pairs: &[CriticalPair<N>],
) -> Preprocessed<N> {
    symbolic_preprocessing_within(basis, pairs, usize::MAX)
        .expect("an unbounded preprocessing cannot exceed its budget")
}

/// As [`symbolic_preprocessing`], abandoned once more than `max_rows` rows are needed.
///
/// The closure is discovered a row at a time and there is no way to know in advance how many rows
/// it will take, so a budget has to be checked as rows are added rather than afterwards: a batch
/// that would need millions of reducer multiples must not allocate them all before anyone notices.
/// `Err` means the limit was crossed, and carries nothing about how many rows the batch would
/// really have needed, because the work of finding that out is the work being refused.
pub fn symbolic_preprocessing_within<const N: usize, F: FiniteField>(
    basis: &MonicBasis<N, F>,
    pairs: &[CriticalPair<N>],
    max_rows: usize,
) -> Result<Preprocessed<N>, RowBudgetExceeded> {
    symbolic_preprocessing_with(
        basis,
        pairs,
        max_rows,
        ReducerSelection::FirstApplicable,
        &mut ReducerCache::disabled(),
    )
}

/// As [`symbolic_preprocessing_within`], under the given reducer-selection policy, consulting and
/// populating `cache`.
///
/// The frozen entry point the F4 reduction step calls. `cache` carries whatever a reducer-reuse
/// implementation keeps between batches; a disabled cache stores nothing and misses every lookup,
/// which is also how repetition is *measured* before anything is cached.
///
/// # Errors
/// As [`symbolic_preprocessing_within`].
pub fn symbolic_preprocessing_with<const N: usize, F: FiniteField>(
    basis: &MonicBasis<N, F>,
    pairs: &[CriticalPair<N>],
    max_rows: usize,
    selection: ReducerSelection,
    cache: &mut ReducerCache<N, F>,
) -> Result<Preprocessed<N>, RowBudgetExceeded> {
    let mut counts = SymbolicCounts::default();
    let mut rows: Vec<PreprocessedRow<N>> = Vec::with_capacity(2 * pairs.len());

    // Monomials that are the leading monomial of some row, so the invariant already holds there.
    let mut covered: HashSet<Monomial<N>> = HashSet::new();
    // Monomials already tested for reducibility, so no monomial is handled twice.
    let mut examined: HashSet<Monomial<N>> = HashSet::new();
    let mut pending: VecDeque<Monomial<N>> = VecDeque::new();

    // Both halves of each pair. Their common leading monomial is the lcm, which is therefore
    // covered by the pair itself and must not acquire a reducer multiple of its own: that would
    // add the very row whose cancellation against its partner is the point of the pair.
    for (position, pair) in pairs.iter().enumerate() {
        for basis_index in [pair.left, pair.right] {
            let multiplier = pair
                .lcm
                .checked_div(&basis.element(basis_index).leading_monomial)
                .expect("a pair's lcm is divisible by each of its leading monomials");
            if rows.len() == max_rows {
                return Err(RowBudgetExceeded { limit: max_rows });
            }
            rows.push(PreprocessedRow {
                multiplier,
                basis_index,
                kind: RowKind::PairComponent { pair: position },
            });
        }
        covered.insert(pair.lcm);
    }

    for row in &rows {
        for (monomial, _) in basis.shifted_terms(row.basis_index, &row.multiplier) {
            pending.push_back(monomial);
        }
    }

    while let Some(monomial) = pending.pop_front() {
        if !examined.insert(monomial) {
            continue;
        }
        if covered.contains(&monomial) {
            continue;
        }
        let Some((basis_index, multiplier)) =
            basis.find_divisor_with(&monomial, selection, &mut counts)
        else {
            // Irreducible: nothing in the matrix can reduce it, and nothing needs to.
            continue;
        };

        // Recorded unconditionally, so that the repetition rate of `(basis_index, multiplier)`
        // across batches is measurable in a mode that serves nothing and changes nothing. That
        // measurement is the precondition for building a cache, not a consequence of having
        // built one.
        if cache.record((basis_index, multiplier)) {
            counts.reducer_rows_reused += 1;
        }

        if rows.len() == max_rows {
            return Err(RowBudgetExceeded { limit: max_rows });
        }

        covered.insert(monomial);
        for (shifted, _) in basis.shifted_terms(basis_index, &multiplier) {
            pending.push_back(shifted);
        }
        rows.push(PreprocessedRow {
            multiplier,
            basis_index,
            kind: RowKind::Reducer,
        });
    }

    Ok(Preprocessed {
        rows,
        leading_monomials: covered,
        counts,
    })
}

/// Symbolic preprocessing needed more rows than it was allowed.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct RowBudgetExceeded {
    pub limit: usize,
}

#[cfg(test)]
mod tests {
    use super::{
        symbolic_preprocessing, symbolic_preprocessing_within, MonicBasis, Preprocessed,
        PreprocessedRow, RowBudgetExceeded, RowKind,
    };
    use crate::{
        fields::Zp13,
        grobner::pairs::CriticalPair,
        poly::MonomialOrder,
        util::contains_duplicates,
        {Monomial, MultivariatePolynomial, One},
    };
    use std::collections::HashSet;

    type F = Zp13;
    const VARS: [&str; 3] = ["x", "y", "z"];
    const ALL_ORDERS: [MonomialOrder; 3] = [
        MonomialOrder::Lexicographic,
        MonomialOrder::GradedLexicographic,
        MonomialOrder::GradedReverseLexicographic,
    ];

    fn parse(s: &str) -> MultivariatePolynomial<3, F> {
        MultivariatePolynomial::parse(s, VARS).unwrap()
    }

    fn system(strings: &[&str]) -> Vec<MultivariatePolynomial<3, F>> {
        strings.iter().map(|s| parse(s)).collect()
    }

    /// Preparing a basis makes every element monic without changing the polynomial up to a unit.
    #[test]
    fn test_monic_basis_normalizes() {
        for order in ALL_ORDERS {
            let basis = MonicBasis::new(&system(&["3*x^2 + y", "5*y^2 - z"]), order);
            for index in 0..basis.len() {
                let element = basis.element(index);
                assert_eq!(
                    element.terms[0].1,
                    F::ONE,
                    "{}: element {} is not monic",
                    order.name(),
                    index
                );
                // And the recorded leading monomial is the one the order chooses.
                assert_eq!(
                    element.leading_monomial,
                    basis
                        .shifted_polynomial(index, &Monomial::one())
                        .leading_monomial(order)
                );
            }
        }
    }

    /// Terms are held descending by the order, which is what makes a shifted row sorted too.
    #[test]
    fn test_monic_basis_terms_are_descending() {
        for order in ALL_ORDERS {
            let basis = MonicBasis::new(&system(&["x^2*y + x*z + y^3 + 1"]), order);
            let terms = &basis.element(0).terms;
            for window in terms.windows(2) {
                assert_eq!(
                    order.cmp(&window[0].0, &window[1].0),
                    std::cmp::Ordering::Greater,
                    "{}: terms are not descending",
                    order.name()
                );
            }
            // Shifting by a monomial preserves that, because monomial orders are multiplicative.
            let shifted: Vec<Monomial<3>> = basis
                .shifted_terms(0, &Monomial::new(&[1, 2, 3]))
                .map(|(monomial, _)| monomial)
                .collect();
            for window in shifted.windows(2) {
                assert_eq!(
                    order.cmp(&window[0], &window[1]),
                    std::cmp::Ordering::Greater,
                    "{}: a shifted row is not descending",
                    order.name()
                );
            }
        }
    }

    /// A zero basis element is rejected rather than silently shifting every later index.
    #[test]
    #[should_panic(expected = "is zero and has no leading monomial")]
    fn test_monic_basis_rejects_a_zero_element() {
        let _ = MonicBasis::new(
            &[parse("x + y"), MultivariatePolynomial::zero()],
            MonomialOrder::Lexicographic,
        );
    }

    /// Divisor lookup returns the first applicable element and the quotient.
    #[test]
    fn test_find_divisor() {
        let order = MonomialOrder::Lexicographic;
        let basis = MonicBasis::new(&system(&["x^2 + 1", "x*y + 1", "z^3 + 1"]), order);

        // x^2*y is divisible by x^2 (index 0) and by x*y (index 1); index order picks 0.
        assert_eq!(
            basis.find_divisor(&Monomial::new(&[2, 1, 0])),
            Some((0, Monomial::new(&[0, 1, 0])))
        );
        // x*y*z is only divisible by x*y.
        assert_eq!(
            basis.find_divisor(&Monomial::new(&[1, 1, 1])),
            Some((1, Monomial::new(&[0, 0, 1])))
        );
        // y*z^2 is divisible by nothing here.
        assert_eq!(basis.find_divisor(&Monomial::new(&[0, 1, 2])), None);
        assert!(!basis.is_top_reducible(&Monomial::new(&[0, 1, 2])));
    }

    /// Shifting multiplies the polynomial, which independent polynomial arithmetic confirms.
    #[test]
    fn test_shifted_polynomial_agrees_with_multiplication() {
        for order in ALL_ORDERS {
            let basis = MonicBasis::new(&system(&["x^2*y + 3*z + 1"]), order);
            let multiplier = Monomial::<3>::new(&[1, 0, 2]);
            let expected = &parse("x^2*y + 3*z + 1") * &MultivariatePolynomial::from(multiplier);
            assert_eq!(
                basis.shifted_polynomial(0, &multiplier),
                expected,
                "{}",
                order.name()
            );
        }
    }

    /// Assert the closure invariant: every reducible monomial of every row is some row's lead.
    ///
    /// This is the property the whole of F4's correctness rests on. If it fails, the matrix cannot
    /// perform a reduction that polynomial division would, and a pivot can appear that the basis
    /// already implied.
    fn assert_closure_invariant(
        basis: &MonicBasis<3, F>,
        preprocessed: &Preprocessed<3>,
        context: &str,
    ) {
        // The recorded set really is the set of row leading monomials.
        let leads: HashSet<Monomial<3>> = (0..preprocessed.rows.len())
            .map(|index| preprocessed.leading_monomial(basis, index))
            .collect();
        assert_eq!(
            leads, preprocessed.leading_monomials,
            "{}: the recorded leading monomials are not the rows' leading monomials",
            context
        );

        for row in &preprocessed.rows {
            for (monomial, _) in basis.shifted_terms(row.basis_index, &row.multiplier) {
                if basis.is_top_reducible(&monomial) {
                    assert!(
                        leads.contains(&monomial),
                        "{}: {} is reducible but no row leads with it",
                        context,
                        monomial
                    );
                }
            }
        }
    }

    /// Every pair of a batch contributes exactly two rows, both leading with the lcm.
    #[test]
    fn test_pair_multiples_lead_with_the_lcm() {
        for order in ALL_ORDERS {
            let polynomials = system(&["x^2 + y", "x^2 + z"]);
            let basis = MonicBasis::new(&polynomials, order);
            let pairs = vec![CriticalPair::new(&polynomials, 0, 1, order)];
            let preprocessed = symbolic_preprocessing(&basis, &pairs);

            let components: Vec<&PreprocessedRow<3>> = preprocessed
                .rows
                .iter()
                .filter(|row| matches!(row.kind, RowKind::PairComponent { .. }))
                .collect();
            assert_eq!(components.len(), 2, "{}", order.name());
            for (index, row) in preprocessed.rows.iter().enumerate() {
                if matches!(row.kind, RowKind::PairComponent { pair: 0 }) {
                    assert_eq!(
                        preprocessed.leading_monomial(&basis, index),
                        pairs[0].lcm,
                        "{}",
                        order.name()
                    );
                }
            }
        }
    }

    /// The textbook example: f = x^2 + y and g = x^2 + z, whose S-polynomial is y - z.
    ///
    /// Both leading monomials are x^2, so the lcm is x^2 and each multiplier is one. The two rows
    /// are the generators themselves; y and z are not reducible, so no reducer multiples are
    /// needed and the matrix is exactly two rows over the columns x^2, y, z.
    #[test]
    fn test_hand_verifiable_two_row_matrix() {
        for order in ALL_ORDERS {
            let polynomials = system(&["x^2 + y", "x^2 + z"]);
            let basis = MonicBasis::new(&polynomials, order);
            let pairs = vec![CriticalPair::new(&polynomials, 0, 1, order)];
            let preprocessed = symbolic_preprocessing(&basis, &pairs);

            assert_eq!(preprocessed.rows.len(), 2, "{}", order.name());
            assert!(
                preprocessed
                    .rows
                    .iter()
                    .all(|row| row.multiplier == Monomial::one()),
                "{}: the multipliers should both be one",
                order.name()
            );
            assert_eq!(
                preprocessed.leading_monomials,
                HashSet::from([Monomial::new(&[2, 0, 0])]),
                "{}",
                order.name()
            );
            assert_closure_invariant(&basis, &preprocessed, order.name());
        }
    }

    /// A reducer multiple is added when a row holds a reducible monomial.
    ///
    /// With basis {x*y - 1, y^2 - 1} under lex the pair has lcm x*y^2, and the multiples are
    /// y*(x*y - 1) = x*y^2 - y and x*(y^2 - 1) = x*y^2 - x. Neither y nor x is reducible, so again
    /// no reducers are needed. Adding x^2 - 1 changes that: x becomes irreducible still, but
    /// pairing x*y - 1 with x^2 - 1 gives lcm x^2*y, multiples x*(x*y - 1) = x^2*y - x and
    /// y*(x^2 - 1) = x^2*y - y, and still nothing reducible. The case that does need a reducer is
    /// a basis element whose tail is reducible by another element.
    #[test]
    fn test_reducer_multiples_are_added_when_needed() {
        let order = MonomialOrder::Lexicographic;
        // LM(x^2 + y^2) = x^2 and LM(x*y + y) = x*y, so the pair's lcm is x^2*y. The multiples are
        // y*(x^2 + y^2) = x^2*y + y^3 and x*(x*y + y) = x^2*y + x*y. The monomial x*y is divisible
        // by LM(x*y + y), so a reducer multiple leading with x*y is required.
        let polynomials = system(&["x^2 + y^2", "x*y + y"]);
        let basis = MonicBasis::new(&polynomials, order);
        let pairs = vec![CriticalPair::new(&polynomials, 0, 1, order)];
        let preprocessed = symbolic_preprocessing(&basis, &pairs);

        let reducers = preprocessed
            .rows
            .iter()
            .filter(|row| row.kind == RowKind::Reducer)
            .count();
        assert!(
            reducers >= 1,
            "expected a reducer multiple, got rows {:?}",
            preprocessed.rows
        );
        assert!(preprocessed
            .leading_monomials
            .contains(&Monomial::new(&[1, 1, 0])));
        assert_closure_invariant(&basis, &preprocessed, "lex");
    }

    /// Preprocessing is a fixed point: a reducer that introduces reducible monomials is chased.
    ///
    /// Here the reducer multiples themselves hold reducible monomials, so a single pass over the
    /// pair multiples would not be enough.
    #[test]
    fn test_closure_requires_several_rounds() {
        let order = MonomialOrder::Lexicographic;
        // Chained: x^3's reducer introduces x^2, whose reducer introduces x, and so on.
        let polynomials = system(&["x^3 - y", "x^2 - z", "x - y*z", "y^2 - 1"]);
        let basis = MonicBasis::new(&polynomials, order);
        let pairs = vec![
            CriticalPair::new(&polynomials, 0, 1, order),
            CriticalPair::new(&polynomials, 1, 2, order),
        ];
        let preprocessed = symbolic_preprocessing(&basis, &pairs);

        assert!(
            preprocessed.rows.len() > 2 * pairs.len(),
            "expected reducer multiples beyond the pair halves, got {:?}",
            preprocessed.rows
        );
        assert_closure_invariant(&basis, &preprocessed, "lex");
    }

    /// The closure invariant holds across a range of systems, orders, and batch shapes.
    #[test]
    fn test_closure_invariant_across_systems() {
        let systems: Vec<Vec<&str>> = vec![
            vec!["x^2 + y", "x^2 + z"],
            vec!["x^2 - y", "x*y - 1"],
            vec!["x + y + z", "x*y + x*z + y*z", "x*y*z - 1"],
            vec!["x^2*y + x", "x*y^2 + y"],
            vec!["x^3 - 2*x*y", "x^2*y - 2*y^2 + x"],
            vec!["x*z - y^2", "x^3 - z^2"],
            vec!["x^3 - y", "x^2 - z", "x - y*z", "y^2 - 1"],
            // Homogeneous.
            vec!["x^2 + y^2 + z^2", "x*y + y*z"],
            // Inhomogeneous, with a constant term.
            vec!["x^2 + y + 1", "y^2 + z + 2", "z^2 + x + 3"],
            // Repeated leading monomials, so several pairs share an lcm.
            vec!["x^2 + y", "x^2 + z", "x^2 + y + z"],
        ];

        for order in ALL_ORDERS {
            for strings in &systems {
                let polynomials = system(strings);
                let basis = MonicBasis::new(&polynomials, order);

                // One batch holding every pair of the system, which is the widest batch possible.
                let mut pairs = Vec::new();
                for left in 0..polynomials.len() {
                    for right in (left + 1)..polynomials.len() {
                        pairs.push(CriticalPair::new(&polynomials, left, right, order));
                    }
                }
                let context = format!("{:?} under {}", strings, order.name());
                let preprocessed = symbolic_preprocessing(&basis, &pairs);
                assert_closure_invariant(&basis, &preprocessed, &context);

                // And each pair on its own, which is the narrowest.
                for pair in &pairs {
                    let preprocessed = symbolic_preprocessing(&basis, std::slice::from_ref(pair));
                    assert_closure_invariant(&basis, &preprocessed, &context);
                }
            }
        }
    }

    /// No row is duplicated: the same multiple is never added twice.
    #[test]
    fn test_rows_are_distinct() {
        for order in ALL_ORDERS {
            let polynomials = system(&["x^3 - y", "x^2 - z", "x - y*z", "y^2 - 1"]);
            let basis = MonicBasis::new(&polynomials, order);
            let mut pairs = Vec::new();
            for left in 0..polynomials.len() {
                for right in (left + 1)..polynomials.len() {
                    pairs.push(CriticalPair::new(&polynomials, left, right, order));
                }
            }
            let preprocessed = symbolic_preprocessing(&basis, &pairs);

            // Reducer rows are keyed by the monomial they lead with, so they cannot repeat. Pair
            // halves can coincide with a reducer multiple in principle, so only the reducers are
            // checked for distinctness here.
            let reducers: Vec<(Monomial<3>, usize)> = preprocessed
                .rows
                .iter()
                .filter(|row| row.kind == RowKind::Reducer)
                .map(|row| (row.multiplier, row.basis_index))
                .collect();
            assert!(
                !contains_duplicates(&reducers),
                "{}: a reducer multiple was added twice",
                order.name()
            );
        }
    }

    /// Preprocessing is deterministic: the same batch gives the same rows, in the same order.
    #[test]
    fn test_preprocessing_is_deterministic() {
        for order in ALL_ORDERS {
            let polynomials = system(&["x^2*y + z", "y^2*z + x", "x*z^2 + y", "x*y*z - 1"]);
            let basis = MonicBasis::new(&polynomials, order);
            let mut pairs = Vec::new();
            for left in 0..polynomials.len() {
                for right in (left + 1)..polynomials.len() {
                    pairs.push(CriticalPair::new(&polynomials, left, right, order));
                }
            }

            let first = symbolic_preprocessing(&basis, &pairs);
            for _ in 0..8 {
                assert_eq!(
                    symbolic_preprocessing(&basis, &pairs),
                    first,
                    "{}",
                    order.name()
                );
            }
        }
    }

    /// The row budget is exact at its boundary, and refuses the work rather than reporting it.
    ///
    /// A batch needing `n` rows succeeds at a budget of `n` and fails at `n - 1`. Failing at the
    /// boundary is what shows the check happens as rows are discovered: a check after the fact
    /// would have had to build all `n` first, which for a batch that needs millions is exactly
    /// the allocation the budget exists to prevent.
    #[test]
    fn test_row_budget_is_exact() {
        let order = MonomialOrder::Lexicographic;
        let polynomials = system(&["x^3 - y", "x^2 - z", "x - y*z", "y^2 - 1"]);
        let basis = MonicBasis::new(&polynomials, order);
        let mut pairs = Vec::new();
        for left in 0..polynomials.len() {
            for right in (left + 1)..polynomials.len() {
                pairs.push(CriticalPair::new(&polynomials, left, right, order));
            }
        }

        let needed = symbolic_preprocessing(&basis, &pairs).rows.len();
        assert!(needed > 2 * pairs.len(), "the closure should add reducers");

        assert_eq!(
            symbolic_preprocessing_within(&basis, &pairs, needed)
                .expect("a budget of exactly what is needed suffices")
                .rows
                .len(),
            needed
        );
        assert_eq!(
            symbolic_preprocessing_within(&basis, &pairs, needed - 1),
            Err(RowBudgetExceeded { limit: needed - 1 })
        );

        // A budget too small even for the pair halves fails on the first push.
        assert_eq!(
            symbolic_preprocessing_within(&basis, &pairs, 0),
            Err(RowBudgetExceeded { limit: 0 })
        );
        assert_eq!(
            symbolic_preprocessing_within(&basis, &pairs, 1),
            Err(RowBudgetExceeded { limit: 1 })
        );
    }

    /// An empty batch needs no rows, so any budget covers it, including zero.
    #[test]
    fn test_row_budget_with_an_empty_batch() {
        let order = MonomialOrder::Lexicographic;
        let basis = MonicBasis::new(&system(&["x^2 + y"]), order);
        assert!(symbolic_preprocessing_within(&basis, &[], 0)
            .expect("nothing to build")
            .rows
            .is_empty());
    }

    /// An empty batch produces no rows.
    #[test]
    fn test_empty_batch() {
        let order = MonomialOrder::Lexicographic;
        let basis = MonicBasis::new(&system(&["x^2 + y"]), order);
        let preprocessed = symbolic_preprocessing(&basis, &[]);
        assert!(preprocessed.rows.is_empty());
        assert!(preprocessed.leading_monomials.is_empty());
    }
}
