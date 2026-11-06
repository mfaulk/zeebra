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

use std::{
    cmp::Ordering,
    collections::{HashSet, VecDeque},
    hash::{BuildHasher, Hasher},
};

use crate::{
    grobner::{f4::options::ReducerSelection, pairs::CriticalPair},
    poly::MonomialOrder,
    FiniteField, Monomial, MultivariatePolynomial,
};

/// A set of monomials, hashed the cheap way. See [`MonomialHasher`].
pub type MonomialSet<const N: usize> = HashSet<Monomial<N>, BuildMonomialHasher>;

/// A multiplicative hash over machine words, for keys that are a handful of integers.
///
/// A monomial is `[u32; N]`, and the closure traversal hashes one per monomial it meets — twice,
/// once to decide whether the monomial has been examined and once to ask whether it is already
/// covered. The standard library's `SipHash-1-3` is chosen to withstand adversarially chosen keys,
/// and costs more per key than the work being guarded: the keys here are monomials the computation
/// produced itself, and a caller who can choose them can already choose the ideal.
///
/// The construction is the one `rustc` uses for its own interned-key maps: rotate, xor the next
/// word in, multiply by an odd constant.
#[derive(Clone, Copy, Debug, Default)]
pub struct MonomialHasher {
    hash: u64,
}

/// An odd 64-bit constant with a well-mixed bit pattern, from `rustc`'s `FxHasher`.
const HASH_MULTIPLIER: u64 = 0x517c_c1b7_2722_0a95;

impl MonomialHasher {
    #[inline]
    fn add(&mut self, word: u64) {
        self.hash = (self.hash.rotate_left(5) ^ word).wrapping_mul(HASH_MULTIPLIER);
    }
}

impl Hasher for MonomialHasher {
    /// Eight bytes at a time.
    ///
    /// This is the path a monomial actually takes: `[u32; N]` hashes through the standard library's
    /// `hash_slice` for integers, which hands the whole exponent array over as one byte slice. A
    /// byte-at-a-time loop here turns a 28-byte key into 28 rounds and was measured to be *slower*
    /// than the SipHash it replaced.
    #[inline]
    fn write(&mut self, bytes: &[u8]) {
        // `as_chunks` rather than `chunks_exact`: the chunk size is a constant, so the array
        // length is known to the compiler and `from_le_bytes` needs no fallible conversion.
        let (words, tail) = bytes.as_chunks::<8>();
        for word in words {
            self.add(u64::from_le_bytes(*word));
        }
        if !tail.is_empty() {
            let mut padded = [0u8; 8];
            padded[..tail.len()].copy_from_slice(tail);
            self.add(u64::from_le_bytes(padded));
        }
    }

    #[inline]
    fn write_u8(&mut self, value: u8) {
        self.add(value as u64);
    }

    #[inline]
    fn write_u16(&mut self, value: u16) {
        self.add(value as u64);
    }

    #[inline]
    fn write_u32(&mut self, value: u32) {
        self.add(value as u64);
    }

    #[inline]
    fn write_u64(&mut self, value: u64) {
        self.add(value);
    }

    #[inline]
    fn write_usize(&mut self, value: usize) {
        self.add(value as u64);
    }

    /// The accumulator, with its high entropy folded down.
    ///
    /// The fold is not optional. A multiplicative accumulator leaves the *low* bits of the product
    /// depending only on the low bits of the inputs, and `hashbrown` takes the bucket index from
    /// exactly those bits — so returning the accumulator raw makes small exponent vectors collide
    /// in droves. Measured, it doubled the cost of the stage it was meant to cheapen. The finalizer
    /// is `splitmix64`'s: two shifts and a multiply.
    #[inline]
    fn finish(&self) -> u64 {
        let mut hash = self.hash;
        hash ^= hash >> 32;
        hash = hash.wrapping_mul(0xd6e8_feb8_6659_fd93);
        hash ^= hash >> 32;
        hash
    }
}

/// Builds a [`MonomialHasher`].
#[derive(Clone, Copy, Debug, Default)]
pub struct BuildMonomialHasher;

impl BuildHasher for BuildMonomialHasher {
    type Hasher = MonomialHasher;

    #[inline]
    fn build_hasher(&self) -> MonomialHasher {
        MonomialHasher::default()
    }
}

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

    /// Monomials pushed onto the pending queue, counted **before** the deduplication test.
    ///
    /// Every term of every row is enqueued and only then checked against `examined`, so this is
    /// larger than [`Self::divisor_queries`] by the repetition factor. It is recorded because the
    /// queue is the one structure in this stage that no [`F4Options`](super::F4Options) budget
    /// bounds: the row budget stops the loop, and each surviving iteration has already enqueued a
    /// row's worth of monomials.
    pub monomials_enqueued: usize,

    /// The largest the pending queue grew, in monomials.
    ///
    /// The queue's own high-water mark, which is what its allocation costs:
    /// `size_of::<Monomial<N>>()` each, and a `VecDeque` never shrinks below the capacity its peak
    /// forced. Sampled once per loop iteration rather than once per push, so the measurement is
    /// one comparison against work that already includes a hash insert.
    pub max_pending_monomials: usize,
}

impl SymbolicCounts {
    /// Fold another pass's counters into these.
    ///
    /// Sums the totals and takes the maximum of the high-water marks: two passes' peaks are not
    /// simultaneous, so adding them would describe memory no moment ever held.
    pub fn add(&mut self, other: &Self) {
        self.divisor_queries += other.divisor_queries;
        self.divisor_scan_steps += other.divisor_scan_steps;
        self.reducer_rows_reused += other.reducer_rows_reused;
        self.monomials_enqueued += other.monomials_enqueued;
        self.max_pending_monomials = self.max_pending_monomials.max(other.max_pending_monomials);
    }
}

/// Whether reducer multiples are tracked across batches.
///
/// Two modes, and **neither serves a cached multiple** — which is the measured conclusion rather
/// than an omission. [`CacheMode::Count`] exists because "would a cache pay?" has to be answerable
/// without building one, and the answer turned out to be no: the repetition rate is high (43% to
/// 95% of reducer multiples had been built in an earlier batch, so the recurrence the preceding
/// milestone expected is real) and serving them is still slower, because a multiple's terms are
/// the basis element's monomials each plus the multiplier — one integer addition per variable per
/// term — against a hash of the key and a pointer chase to a heap vector. Implemented and
/// measured, that made symbolic preprocessing 8% to 50% slower on every instance above a
/// millisecond; see §7.2 of `docs/MILESTONE-F4-OPTIMIZATION.md`.
///
/// A `Store` variant existed and was removed: an option named for a behaviour it does not have is
/// worse than no option. The implementation is in this file's history.
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
pub struct ReducerCache<const N: usize> {
    mode: CacheMode,

    /// Every multiple needed so far, for the repetition measurement. Empty when off.
    seen: HashSet<(usize, Monomial<N>), BuildMonomialHasher>,

    /// Multiples needed that had been needed before.
    repeats: usize,

    /// Multiples needed for the first time.
    firsts: usize,
}

impl<const N: usize> ReducerCache<N> {
    pub fn new(mode: CacheMode) -> Self {
        Self {
            mode,
            seen: HashSet::default(),
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

    /// Forget everything, keeping the mode and the counters.
    ///
    /// The bound a cache needs is on memory, and the basis grows throughout a computation, so an
    /// implementation that caps itself has to be able to start over. Discarding the contents
    /// cannot change a result — a miss is always recoverable by recomputing — which is what makes
    /// a bounded cache safe.
    pub fn clear(&mut self) {
        self.seen.clear();
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

    /// The order the leading monomials were taken under.
    ///
    /// Kept because reducer selection compares them: "the largest leading monomial that divides"
    /// is not a question about exponent vectors alone.
    order: MonomialOrder,
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
        let elements: Vec<MonicElement<N, F>> = basis
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

        Self { elements, order }
    }

    /// The order the basis was prepared under.
    pub fn order(&self) -> MonomialOrder {
        self.order
    }

    /// Recompute every derived field and compare it to what is stored.
    ///
    /// The invariants this type's constructors establish are stated in prose on [`MonicElement`]
    /// and on [`MonicBasis::new`], and until this existed nothing checked that they still held
    /// partway through a computation. A wrong cached leading monomial does not fail where it is
    /// written: it selects a different reducer, which produces a different row and a different
    /// matrix, so it surfaces as a wrong answer hundreds of batches later, if at all.
    ///
    /// Modelled on Singular's `kTest` family (`kernel/GBEngine/kutil.cc`, read in
    /// `docs/research/singular-engine-notes.md` §6): recompute rather than trust, and name the
    /// field and the index on failure, because "assertion failed" at a line number in a
    /// four-hundred-batch run is most of the problem.
    ///
    /// # What is deliberately not checked
    ///
    /// That no leading monomial divides another's, and in particular that leads are distinct. Both
    /// are **false** for a basis under construction, and the counterexample was measured rather
    /// than assumed: asserting it fires on `certify`'s own fixtures, where element 0's lead `x_0^2`
    /// is divisible by element 4's lead `x_0` — an input generator divided by a basis element F4
    /// discovered *later*. Nothing removes such an element until the final minimization, and
    /// `docs/research/singular-engine-notes.md` §0.3 measures two of them surviving to the end on
    /// every katsura instance under a graded order, and 200 of 206 under lex. Asserting it here
    /// would fire on correct computations.
    ///
    /// Debug-only, and the call site in [`super::f4_with_options`] is gated the same way, so this
    /// does not exist in a release build. `cargo test --profile ci-release` therefore does **not**
    /// run it — `ci-release` inherits `release`, where `debug-assertions` is off. The default
    /// `cargo test` job does.
    ///
    /// # Panics
    /// If any stored field disagrees with its recomputation.
    #[cfg(debug_assertions)]
    pub(crate) fn check(&self) {
        for (index, element) in self.elements.iter().enumerate() {
            assert!(
                !element.terms.is_empty(),
                "MonicBasis element {index}: terms is empty, so it has no leading monomial"
            );

            // Both halves are checked: equal-to-terms[0] alone would pass on a list sorted the
            // wrong way, and largest-term alone would pass on a list that is merely unsorted.
            assert_eq!(
                element.leading_monomial, element.terms[0].0,
                "MonicBasis element {index}: leading_monomial {} disagrees with terms[0] {}",
                element.leading_monomial, element.terms[0].0
            );
            let largest = element
                .terms
                .iter()
                .map(|(monomial, _)| *monomial)
                .reduce(|a, b| if self.order.cmp(&a, &b).is_ge() { a } else { b })
                .expect("the terms are not empty");
            assert_eq!(
                element.leading_monomial,
                largest,
                "MonicBasis element {index}: leading_monomial {} is not the largest term under \
                 {}, which is {}",
                element.leading_monomial,
                self.order.name(),
                largest
            );

            assert!(
                element.terms[0].1.is_one(),
                "MonicBasis element {index}: leading coefficient is not one, so the element is \
                 not monic and a pair multiple is not a bare shift of its terms"
            );

            for (position, (monomial, coefficient)) in element.terms.iter().enumerate() {
                assert!(
                    !coefficient.is_zero(),
                    "MonicBasis element {index}: terms[{position}] has a zero coefficient at \
                     {monomial}"
                );
                if position > 0 {
                    let previous = element.terms[position - 1].0;
                    assert!(
                        self.order.cmp(&previous, monomial).is_gt(),
                        "MonicBasis element {index}: terms[{}] {previous} does not strictly \
                         precede terms[{position}] {monomial} under {}",
                        position - 1,
                        self.order.name()
                    );
                }
            }
        }
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
    /// If the polynomial is zero, or if `order` is not the order the basis was prepared under —
    /// which would leave the recorded leading monomials disagreeing with each other.
    pub fn push(&mut self, polynomial: &MultivariatePolynomial<N, F>, order: MonomialOrder) {
        assert_eq!(
            order,
            self.order,
            "a basis prepared under {} cannot be extended under {}",
            self.order.name(),
            order.name()
        );
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
    /// The reference scan for [`ReducerSelection::FirstApplicable`], which any faster lookup has to
    /// agree with element for element.
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

    /// The element whose leading monomial divides `monomial` and is largest under the basis's
    /// order, with the quotient.
    ///
    /// The largest divisor gives the smallest multiplier, hence a multiple whose monomials are the
    /// fewest steps above the ones already in the matrix — which is the whole hypothesis. Equal
    /// leading monomials are broken by the smaller basis index, because "largest" alone is not a
    /// total order on the basis and preprocessing has to be deterministic.
    ///
    /// The reference scan for [`ReducerSelection::LargestLeadingMonomial`].
    pub fn find_largest_divisor(&self, monomial: &Monomial<N>) -> Option<(usize, Monomial<N>)> {
        let mut best: Option<(usize, Monomial<N>)> = None;
        for (index, element) in self.elements.iter().enumerate() {
            let Some(quotient) = monomial.checked_div(&element.leading_monomial) else {
                continue;
            };
            let beats_the_best = match best {
                None => true,
                Some((incumbent, _)) => {
                    self.order.cmp(
                        &element.leading_monomial,
                        &self.elements[incumbent].leading_monomial,
                    ) == Ordering::Greater
                }
            };
            if beats_the_best {
                best = Some((index, quotient));
            }
        }
        best
    }

    /// The element with the fewest terms whose leading monomial divides `monomial`, with the
    /// quotient.
    ///
    /// The reference scan for [`ReducerSelection::FewestTerms`]. Ties go to the smaller basis
    /// index, which is what makes "fewest" a total order on the basis.
    pub fn find_sparsest_divisor(&self, monomial: &Monomial<N>) -> Option<(usize, Monomial<N>)> {
        self.best_divisor_by_length(monomial, Ordering::Less)
    }

    /// The element with the most terms whose leading monomial divides `monomial`, with the
    /// quotient.
    ///
    /// The reference scan for [`ReducerSelection::MostTerms`], the control.
    pub fn find_densest_divisor(&self, monomial: &Monomial<N>) -> Option<(usize, Monomial<N>)> {
        self.best_divisor_by_length(monomial, Ordering::Greater)
    }

    /// The divisor whose term count compares `wanted` against the incumbent's, index order
    /// breaking ties.
    ///
    /// One scan for both directions, so the control cannot drift from the policy it controls.
    fn best_divisor_by_length(
        &self,
        monomial: &Monomial<N>,
        wanted: Ordering,
    ) -> Option<(usize, Monomial<N>)> {
        let mut best: Option<(usize, Monomial<N>)> = None;
        for (index, element) in self.elements.iter().enumerate() {
            let Some(quotient) = monomial.checked_div(&element.leading_monomial) else {
                continue;
            };
            let beats_the_best = match best {
                None => true,
                Some((incumbent, _)) => {
                    element
                        .terms
                        .len()
                        .cmp(&self.elements[incumbent].terms.len())
                        == wanted
                }
            };
            if beats_the_best {
                best = Some((index, quotient));
            }
        }
        best
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
            ReducerSelection::FirstApplicable => {
                for (index, element) in self.elements.iter().enumerate() {
                    counts.divisor_scan_steps += 1;
                    if let Some(quotient) = monomial.checked_div(&element.leading_monomial) {
                        return Some((index, quotient));
                    }
                }
                None
            }
            ReducerSelection::LargestLeadingMonomial => {
                counts.divisor_scan_steps += self.elements.len();
                self.find_largest_divisor(monomial)
            }
            ReducerSelection::FewestTerms => {
                counts.divisor_scan_steps += self.elements.len();
                self.find_sparsest_divisor(monomial)
            }
            ReducerSelection::MostTerms => {
                counts.divisor_scan_steps += self.elements.len();
                self.find_densest_divisor(monomial)
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
    pub leading_monomials: MonomialSet<N>,

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
    cache: &mut ReducerCache<N>,
) -> Result<Preprocessed<N>, RowBudgetExceeded> {
    let mut counts = SymbolicCounts::default();
    let mut rows: Vec<PreprocessedRow<N>> = Vec::with_capacity(2 * pairs.len());

    // Monomials that are the leading monomial of some row, so the invariant already holds there.
    let mut covered: MonomialSet<N> = MonomialSet::default();
    // Monomials already tested for reducibility, so no monomial is handled twice.
    let mut examined: MonomialSet<N> = MonomialSet::default();
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
            counts.monomials_enqueued += 1;
        }
    }

    while let Some(monomial) = pending.pop_front() {
        counts.max_pending_monomials = counts.max_pending_monomials.max(pending.len());
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
            counts.monomials_enqueued += 1;
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
        symbolic_preprocessing, symbolic_preprocessing_with, symbolic_preprocessing_within,
        BuildMonomialHasher, CacheMode, MonicBasis, MonomialSet, Preprocessed, PreprocessedRow,
        ReducerCache, RowBudgetExceeded, RowKind, SymbolicCounts,
    };

    /// Three polynomials with tails and distinct leads, for the corruption tests below.
    #[cfg(debug_assertions)]
    fn fixture() -> Vec<MultivariatePolynomial<3, F>> {
        system(&["3*x^2 + y + 3", "x*y + 5*z", "2*y^2 + 11"])
    }

    /// The checker accepts a basis its own constructor built.
    ///
    /// The control for the corruption tests below: without it they would pass against a checker
    /// that rejected everything.
    #[cfg(debug_assertions)]
    #[test]
    fn test_the_checker_accepts_a_well_formed_basis() {
        let basis = MonicBasis::new(&fixture(), MonomialOrder::GradedReverseLexicographic);
        basis.check();
    }

    /// A leading monomial that disagrees with the term list is caught, and named.
    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "leading_monomial")]
    fn test_a_stale_leading_monomial_is_caught() {
        let mut basis = MonicBasis::new(&fixture(), MonomialOrder::GradedReverseLexicographic);
        basis.elements[1].leading_monomial = Monomial::<3>::new(&[9, 0, 0]);
        basis.check();
    }

    /// Two tail terms out of order are caught, with the lead left correct.
    ///
    /// Swapping inside the tail is the case the lead checks cannot see: `terms[0]` is still the
    /// largest and still equals `leading_monomial`, so only the pairwise descent catches it. A
    /// coarser corruption — reversing the whole list — is caught one assertion earlier, by the
    /// largest-term check, and so would not exercise this one.
    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "does not strictly precede")]
    fn test_terms_out_of_order_are_caught() {
        let mut basis = MonicBasis::new(&fixture(), MonomialOrder::GradedReverseLexicographic);
        let element = &mut basis.elements[0];
        assert!(
            element.terms.len() > 2,
            "the fixture needs two tail terms to swap"
        );
        element.terms.swap(1, 2);
        basis.check();
    }

    /// An element that is not monic is caught.
    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "not monic")]
    fn test_a_non_monic_element_is_caught() {
        let mut basis = MonicBasis::new(&fixture(), MonomialOrder::GradedReverseLexicographic);
        basis.elements[0].terms[0].1 = F::new(7);
        basis.check();
    }

    /// A surviving zero coefficient is caught.
    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "zero coefficient")]
    fn test_a_zero_coefficient_is_caught() {
        let mut basis = MonicBasis::new(&fixture(), MonomialOrder::GradedReverseLexicographic);
        let last = basis.elements[0].terms.len() - 1;
        assert!(last > 0, "the fixture needs a tail term to zero");
        basis.elements[0].terms[last].1 = F::new(0);
        basis.check();
    }

    use crate::{
        fields::Zp13,
        grobner::{f4::options::ReducerSelection, pairs::CriticalPair},
        poly::MonomialOrder,
        util::contains_duplicates,
        FiniteField, {Monomial, MultivariatePolynomial, One},
    };
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

    /// Largest-leading-monomial selection picks the biggest divisor, which is the smallest multiple.
    #[test]
    fn test_find_largest_divisor() {
        let order = MonomialOrder::Lexicographic;
        // LM(x*y + 1) = x*y at index 0 and LM(x^2 + 1) = x^2 at index 1, and x^2 > x*y under lex,
        // so the two policies disagree about x^2*y: first-applicable takes index 0.
        let basis = MonicBasis::new(&system(&["x*y + 1", "x^2 + 1"]), order);
        let monomial = Monomial::new(&[2, 1, 0]);

        assert_eq!(
            basis.find_divisor(&monomial),
            Some((0, Monomial::new(&[1, 0, 0])))
        );
        assert_eq!(
            basis.find_largest_divisor(&monomial),
            Some((1, Monomial::new(&[0, 1, 0])))
        );
        // Nothing divides y*z^2, under either policy.
        assert_eq!(basis.find_largest_divisor(&Monomial::new(&[0, 1, 2])), None);
    }

    /// Equal largest leading monomials are broken by the smaller basis index.
    #[test]
    fn test_find_largest_divisor_tiebreak() {
        for order in ALL_ORDERS {
            // Both elements lead with x^2, so the policy has to fall back on the index.
            let basis = MonicBasis::new(&system(&["x^2 + y", "x^2 + z"]), order);
            assert_eq!(
                basis.find_largest_divisor(&Monomial::new(&[2, 1, 0])),
                Some((0, Monomial::new(&[0, 1, 0]))),
                "{}",
                order.name()
            );
        }
    }

    /// Each selection policy routes to its own reference scan, and counts one query per lookup.
    #[test]
    fn test_find_divisor_with_follows_the_policy() {
        let order = MonomialOrder::Lexicographic;
        let basis = MonicBasis::new(&system(&["x*y + 1", "x^2 + 1"]), order);
        let monomial = Monomial::new(&[2, 1, 0]);

        let mut counts = SymbolicCounts::default();
        assert_eq!(
            basis.find_divisor_with(&monomial, ReducerSelection::FirstApplicable, &mut counts),
            basis.find_divisor(&monomial)
        );
        assert_eq!(
            basis.find_divisor_with(
                &monomial,
                ReducerSelection::LargestLeadingMonomial,
                &mut counts
            ),
            basis.find_largest_divisor(&monomial)
        );
        assert_eq!(
            basis.find_divisor_with(&monomial, ReducerSelection::FewestTerms, &mut counts),
            basis.find_sparsest_divisor(&monomial)
        );
        assert_eq!(
            basis.find_divisor_with(&monomial, ReducerSelection::MostTerms, &mut counts),
            basis.find_densest_divisor(&monomial)
        );
        assert_eq!(counts.divisor_queries, 4);
    }

    /// The term-count policies pick the sparsest and the densest divisor respectively.
    #[test]
    fn test_find_divisor_by_term_count() {
        let order = MonomialOrder::Lexicographic;
        // Both lead with x under lex, and x^2*y is divisible by both. The first has two terms, the
        // second four, so the two policies part company — and neither is index order, since
        // `FewestTerms` has to reach past element 1 for element 2.
        let basis = MonicBasis::new(
            &system(&["x + y + z", "x*y + x*z + y*z + 1", "x + 1"]),
            order,
        );
        let monomial = Monomial::new(&[2, 1, 0]);

        assert_eq!(
            basis.find_sparsest_divisor(&monomial),
            Some((2, Monomial::new(&[1, 1, 0])))
        );
        assert_eq!(
            basis.find_densest_divisor(&monomial),
            Some((1, Monomial::new(&[1, 0, 0])))
        );
        // Nothing divides z^3, under either policy.
        assert_eq!(
            basis.find_sparsest_divisor(&Monomial::new(&[0, 0, 3])),
            None
        );
        assert_eq!(basis.find_densest_divisor(&Monomial::new(&[0, 0, 3])), None);
    }

    /// Equal term counts are broken by the smaller basis index, under both directions.
    #[test]
    fn test_find_divisor_by_term_count_tiebreak() {
        for order in ALL_ORDERS {
            // Both elements lead with x^2 and have two terms, so only the index is left.
            let basis = MonicBasis::new(&system(&["x^2 + y", "x^2 + z"]), order);
            let monomial = Monomial::new(&[2, 1, 0]);
            let expected = Some((0, Monomial::new(&[0, 1, 0])));
            assert_eq!(
                basis.find_sparsest_divisor(&monomial),
                expected,
                "{}",
                order.name()
            );
            assert_eq!(
                basis.find_densest_divisor(&monomial),
                expected,
                "{}",
                order.name()
            );
        }
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
        let leads: MonomialSet<3> = (0..preprocessed.rows.len())
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
                MonomialSet::from_iter([Monomial::new(&[2, 0, 0])]),
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

    /// The systems the closure invariant is asserted over, matching the fixed corpus.
    fn closure_corpus() -> Vec<Vec<&'static str>> {
        vec![
            vec!["x^2 + y", "x^2 + z"],
            vec!["x^2 - y", "x*y - 1"],
            vec!["x + y + z", "x*y + x*z + y*z", "x*y*z - 1"],
            vec!["x^2*y + x", "x*y^2 + y"],
            vec!["x^3 - 2*x*y", "x^2*y - 2*y^2 + x"],
            vec!["x*z - y^2", "x^3 - z^2"],
            vec!["x^3 - y", "x^2 - z", "x - y*z", "y^2 - 1"],
            vec!["x^2 + y^2 + z^2", "x*y + y*z"],
            vec!["x^2 + y + 1", "y^2 + z + 2", "z^2 + x + 3"],
            vec!["x^2 + y", "x^2 + z", "x^2 + y + z"],
        ]
    }

    /// Every pair of the system, which is the widest batch a basis admits.
    fn every_pair(
        polynomials: &[MultivariatePolynomial<3, F>],
        order: MonomialOrder,
    ) -> Vec<CriticalPair<3>> {
        let mut pairs = Vec::new();
        for left in 0..polynomials.len() {
            for right in (left + 1)..polynomials.len() {
                pairs.push(CriticalPair::new(polynomials, left, right, order));
            }
        }
        pairs
    }

    /// The closure invariant holds under every selection policy and every cache mode.
    #[test]
    fn test_closure_invariant_under_every_configuration() {
        for order in ALL_ORDERS {
            for strings in &closure_corpus() {
                let polynomials = system(strings);
                let basis = MonicBasis::new(&polynomials, order);
                let pairs = every_pair(&polynomials, order);

                for selection in ReducerSelection::ALL {
                    for mode in [CacheMode::Off, CacheMode::Count] {
                        let mut cache = ReducerCache::new(mode);
                        let context = format!(
                            "{:?} under {} {:?}/{:?}",
                            strings,
                            order.name(),
                            selection,
                            mode
                        );

                        let wide = symbolic_preprocessing_with(
                            &basis,
                            &pairs,
                            usize::MAX,
                            selection,
                            &mut cache,
                        )
                        .expect("unbounded");
                        assert_closure_invariant(&basis, &wide, &context);

                        for pair in &pairs {
                            let narrow = symbolic_preprocessing_with(
                                &basis,
                                std::slice::from_ref(pair),
                                usize::MAX,
                                selection,
                                &mut cache,
                            )
                            .expect("unbounded");
                            assert_closure_invariant(&basis, &narrow, &context);
                        }
                    }
                }
            }
        }
    }

    /// Every row is the polynomial its multiplier and basis index say it is.
    #[test]
    fn test_rows_round_trip_through_polynomial_arithmetic() {
        for order in ALL_ORDERS {
            for strings in &closure_corpus() {
                let polynomials = system(strings);
                let basis = MonicBasis::new(&polynomials, order);
                let pairs = every_pair(&polynomials, order);
                let preprocessed = symbolic_preprocessing(&basis, &pairs);

                for row in &preprocessed.rows {
                    // The basis is monic, so the row is the scaled generator times the multiplier.
                    let scaled = &polynomials[row.basis_index].scale(
                        &polynomials[row.basis_index]
                            .leading_coefficient(order)
                            .inverse(),
                    );
                    let expected = scaled * &MultivariatePolynomial::from(row.multiplier);
                    assert_eq!(
                        basis.shifted_polynomial(row.basis_index, &row.multiplier),
                        expected,
                        "{:?} under {}: row {:?} is not its own polynomial",
                        strings,
                        order.name(),
                        row
                    );
                }
            }
        }
    }

    /// A policy's selected divisor fixes the row set, which does not depend on the cache's contents.
    #[test]
    fn test_clearing_the_cache_does_not_change_the_rows() {
        for order in ALL_ORDERS {
            let polynomials = system(&["x^3 - y", "x^2 - z", "x - y*z", "y^2 - 1"]);
            let basis = MonicBasis::new(&polynomials, order);
            let pairs = every_pair(&polynomials, order);

            for selection in ReducerSelection::ALL {
                let mut warm = ReducerCache::new(CacheMode::Count);
                let expected =
                    symbolic_preprocessing_with(&basis, &pairs, usize::MAX, selection, &mut warm)
                        .expect("unbounded");

                // Run again against a warm cache, then against one cleared mid-flight.
                for _ in 0..3 {
                    let actual = symbolic_preprocessing_with(
                        &basis,
                        &pairs,
                        usize::MAX,
                        selection,
                        &mut warm,
                    )
                    .expect("unbounded");
                    assert_eq!(actual.rows, expected.rows, "{}", order.name());
                }
                warm.clear();
                let after =
                    symbolic_preprocessing_with(&basis, &pairs, usize::MAX, selection, &mut warm)
                        .expect("unbounded");
                assert_eq!(after.rows, expected.rows, "{}", order.name());
            }
        }
    }

    /// Each policy's dispatch returns exactly what its reference scan returns, over random bases.
    ///
    /// The differential test any faster lookup has to pass: agreement is not about returning *a*
    /// divisor but *the* divisor, since a different divisor is a different multiplier and so a
    /// different matrix row.
    #[test]
    fn test_dispatch_agrees_with_the_reference_scans() {
        use rand::{prelude::StdRng, Rng, SeedableRng};

        let mut rng = StdRng::seed_from_u64(20260211);
        for order in ALL_ORDERS {
            for _ in 0..60 {
                // Single-term generators, so the leading monomials are exactly what is drawn, from
                // a small range so that equal leads and the tiebreaker both occur.
                let size = rng.gen_range(1..=12);
                let polynomials: Vec<MultivariatePolynomial<3, F>> = (0..size)
                    .map(|_| {
                        let exponents: Vec<u32> = (0..3).map(|_| rng.gen_range(0..=2)).collect();
                        let mut lead = Monomial::<3>::new(&exponents);
                        if lead.is_one() {
                            lead = Monomial::new(&[1, 0, 0]);
                        }
                        MultivariatePolynomial::from(lead)
                    })
                    .collect();
                let basis = MonicBasis::new(&polynomials, order);

                for _ in 0..40 {
                    let exponents: Vec<u32> = (0..3).map(|_| rng.gen_range(0..=4)).collect();
                    let monomial = Monomial::<3>::new(&exponents);
                    let mut counts = SymbolicCounts::default();
                    assert_eq!(
                        basis.find_divisor_with(
                            &monomial,
                            ReducerSelection::FirstApplicable,
                            &mut counts
                        ),
                        basis.find_divisor(&monomial),
                        "{}: first-applicable disagreed on {}",
                        order.name(),
                        monomial
                    );
                    assert_eq!(
                        basis.find_divisor_with(
                            &monomial,
                            ReducerSelection::LargestLeadingMonomial,
                            &mut counts
                        ),
                        basis.find_largest_divisor(&monomial),
                        "{}: largest-leading-monomial disagreed on {}",
                        order.name(),
                        monomial
                    );
                }
            }
        }
    }

    /// The cheap monomial hasher agrees with equality, and is not degenerate on small exponents.
    #[test]
    fn test_monomial_hasher() {
        use std::collections::hash_map::RandomState;
        use std::hash::BuildHasher;

        fn hash_of(monomial: &Monomial<4>) -> u64 {
            BuildMonomialHasher.hash_one(monomial)
        }

        // Equal monomials hash equally, which is the only thing `Hash` actually requires.
        let monomials: Vec<Monomial<4>> = (0..8)
            .flat_map(|a| (0..8).map(move |b| Monomial::new(&[a, b, (a + b) % 5, 0])))
            .collect();
        for monomial in &monomials {
            assert_eq!(
                hash_of(monomial),
                hash_of(&Monomial::new(monomial.exponents()))
            );
        }

        // And distinctly: the low bits are what `hashbrown` buckets on, and an unfinalized
        // multiplicative hash leaves them barely mixed. Compare bucket spread against the standard
        // hasher on the same keys.
        let mask = 63;
        let mine: std::collections::HashSet<u64> =
            monomials.iter().map(|m| hash_of(m) & mask).collect();
        let standard = RandomState::new();
        let theirs: std::collections::HashSet<u64> = monomials
            .iter()
            .map(|m| standard.hash_one(m) & mask)
            .collect();
        assert!(
            mine.len() * 4 >= theirs.len() * 3,
            "the low bits spread over {} buckets against the standard hasher's {}",
            mine.len(),
            theirs.len()
        );
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
