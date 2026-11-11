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
    collections::{hash_map::Entry, HashSet, VecDeque},
};

use crate::{
    grobner::{
        f4::{divmask::DivmaskCalibration, options::ReducerSelection},
        pairs::CriticalPair,
    },
    poly::{MonomialMap, MonomialOrder},
    FiniteField, Monomial, MultivariatePolynomial,
};

/// The monomial hash lives in the polynomial layer, which also keys its term maps with it.
pub use crate::poly::{BuildMonomialHasher, MonomialHasher, MonomialSet};

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

    /// Monomials *offered* to the pending queue, counted **before** the deduplication test.
    ///
    /// Every term of every row is offered, so this is larger than [`Self::divisor_queries`] by the
    /// repetition factor, and it stays the pre-deduplication total after #305 moved the test from
    /// pop to push — the figures recorded against this counter before that change remain
    /// comparable with the ones taken after it. What changed is how many of these offers are
    /// *admitted*: now only the distinct ones, so [`Self::max_pending_monomials`] is bounded by
    /// the batch's column count rather than by nothing.
    pub monomials_enqueued: usize,

    /// The largest the pending queue grew, in monomials.
    ///
    /// The queue's own high-water mark, which is what its allocation costs:
    /// `size_of::<Monomial<N>>()` each, and a `VecDeque` never shrinks below the capacity its peak
    /// forced. Sampled after each iteration's run of pushes, which is where the queue can only
    /// have grown, so this is the exact maximum rather than an approximation to it.
    pub max_pending_monomials: usize,

    /// Divisibility tests the divmask probe replayed. Zero unless the probe is on.
    ///
    /// Must equal [`Self::divisor_scan_steps`] whenever the probe is on, because the replay walks
    /// the basis exactly as the selection policy does — including stopping at the first hit under
    /// [`ReducerSelection::FirstApplicable`]. That equality is the probe's own correctness check
    /// (`test_the_probe_replays_exactly_the_scan_the_policy_performed`): a replay over a different
    /// set of tests would answer a different question from the one #331 asks.
    pub divmask_tests: usize,

    /// Of [`Self::divmask_tests`], the tests that answered **not divisible**.
    ///
    /// The population a mask can help with. A mask can never shortcut a positive answer — see
    /// [`DivmaskCalibration::rejects`] — so this is the denominator for the probe's hit rate, and
    /// `divmask_tests - divmask_negative` is work no mask could have saved.
    pub divmask_negative: usize,

    /// Of [`Self::divmask_negative`], the tests a 32-bit calibrated mask would have decided.
    ///
    /// The number #331 is for: the fraction of the exponent comparisons that one AND and one
    /// branch would have replaced. Compare against [`Self::divmask_tests`] rather than against
    /// [`Self::divmask_negative`] when asking what a mask saves overall, because the positives are
    /// in the denominator of the stage's cost whether a mask exists or not.
    pub divmask_decided: usize,
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
        self.divmask_tests += other.divmask_tests;
        self.divmask_negative += other.divmask_negative;
        self.divmask_decided += other.divmask_decided;
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

    /// The divmask probe, when one was installed. `None` on every shipping path.
    ///
    /// `MonicBasis::new` cannot build it: the calibration is a function of the *input system*, and
    /// a basis under construction is not that — calibrating off the growing basis would move the
    /// thresholds mid-run and make the counters incomparable between batches. So it is installed
    /// by the caller that read the system; see [`MonicBasis::probe_divmask_from`].
    divmask: Option<DivmaskProbe<N>>,
}

/// A calibration and the mask of each basis element's leading monomial.
///
/// The masks are cached because the scan asks about the same leading monomials once per monomial
/// tested, which is the asymmetry the technique rests on: msolve keeps them in `bs->lm` for
/// exactly this reason (`symbol.c:514`). Recomputing one per test would still give the right
/// counters and would measure a straw man.
#[derive(Clone, Debug, Eq, PartialEq)]
struct DivmaskProbe<const N: usize> {
    calibration: DivmaskCalibration<N>,

    /// `leads[i]` is the mask of element `i`'s leading monomial, maintained by every path that
    /// appends to `elements`.
    leads: Vec<u32>,
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

        Self {
            elements,
            order,
            divmask: None,
        }
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
        self.refresh_divmask_leads();
    }

    /// Install the divmask probe, calibrated from the monomials of `system`.
    ///
    /// Measurement only: nothing the solver returns changes, because
    /// [`MonicBasis::find_divisor_with`] consults the probe *after* answering and only to count
    /// (#331). Calibrated from the system as read, which is msolve's point of calibration
    /// (`engine.c:93`) and the only one at which the thresholds are a property of the input rather
    /// than of how far the run has got.
    pub fn probe_divmask_from<'a>(
        &mut self,
        system: impl IntoIterator<Item = &'a MultivariatePolynomial<N, F>>,
    ) where
        F: 'a,
    {
        let mut monomials: Vec<Monomial<N>> = Vec::new();
        for polynomial in system {
            monomials.extend(polynomial.terms().keys().copied());
        }
        self.divmask = Some(DivmaskProbe {
            calibration: DivmaskCalibration::calibrate(monomials.iter()),
            leads: Vec::new(),
        });
        self.refresh_divmask_leads();
    }

    /// Whether a divmask probe is installed and its calibration can decide anything.
    pub fn divmask_is_informative(&self) -> bool {
        self.divmask
            .as_ref()
            .is_some_and(|probe| probe.calibration.is_informative())
    }

    /// Bring the cached lead masks up to the element count. A no-op with no probe.
    fn refresh_divmask_leads(&mut self) {
        let Some(probe) = self.divmask.as_mut() else {
            return;
        };
        for element in &self.elements[probe.leads.len()..] {
            probe
                .leads
                .push(probe.calibration.mask(&element.leading_monomial));
        }
    }

    /// Replay the scan the policy just performed, counting what a mask would have decided.
    ///
    /// Walks the basis the way the policy does — stopping at the first divisor under
    /// [`ReducerSelection::FirstApplicable`], scanning the whole basis otherwise — so
    /// [`SymbolicCounts::divmask_tests`] is the same population as
    /// [`SymbolicCounts::divisor_scan_steps`]. A separate walk rather than a hook inside the four
    /// scan functions: the probe must not be able to change which divisor is selected, and code
    /// that cannot reach the return value cannot.
    fn replay_divmask(
        &self,
        monomial: &Monomial<N>,
        selection: ReducerSelection,
        counts: &mut SymbolicCounts,
    ) {
        let Some(probe) = self.divmask.as_ref() else {
            return;
        };
        let dividend = probe.calibration.mask(monomial);
        for (index, element) in self.elements.iter().enumerate() {
            counts.divmask_tests += 1;
            if monomial.checked_div(&element.leading_monomial).is_some() {
                if selection == ReducerSelection::FirstApplicable {
                    return;
                }
                continue;
            }
            counts.divmask_negative += 1;
            if probe.calibration.rejects(probe.leads[index], dividend) {
                counts.divmask_decided += 1;
            }
        }
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
        self.replay_divmask(monomial, selection, counts);
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

/// A monomial's position in [`Preprocessed::monomials`].
///
/// `u32` rather than `usize` because there is one of these per matrix *entry* and entries outnumber
/// columns by the average column density — 11.5x to 39.8x on the corpus (#621) — so the width is
/// the dominant term in what the handles cost. A batch with more than `u32::MAX` distinct monomials
/// would need 96 GB for the arena alone, so the narrowing is not a limit anything can reach; the
/// conversion in `enqueue` is checked rather than wrapping all the same, once per column.
pub type MonomialHandle = u32;

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

    /// Every distinct monomial appearing in any row — which is exactly the matrix's column set —
    /// in the order the closure first met it, so a monomial's index is its [`MonomialHandle`].
    ///
    /// Preprocessing has to intern these anyway to deduplicate its own work queue, so handing the
    /// set on saves [`MacaulayMatrix::build`](super::macaulay::MacaulayMatrix::build) hashing
    /// every row monomial a second time. That the two sets coincide is not an accident of the
    /// implementation: the queue is fed from row terms and nothing else, and every row's terms are
    /// fed to it, so the set of monomials examined and the set of columns are the same set.
    /// `macaulay.rs`'s `test_preprocessing_interns_exactly_the_column_set` is what keeps that true.
    pub monomials: Vec<Monomial<N>>,

    /// The handle of every row term: row by row in `rows` order, and within a row in the basis
    /// element's own descending term order.
    ///
    /// This is what #621 is: the column of an entry is discovered here, once, and the scatter reads
    /// it through the handle instead of rederiving `monomial * multiplier` and hashing it again.
    /// A row's terms are a *contiguous* run of this vector, `basis.element(row.basis_index).terms`
    /// long, which is why no per-row offset is stored — the layout is implied by the rows and the
    /// basis, and `MacaulayMatrix::build_measured` walks the two together.
    pub term_handles: Vec<MonomialHandle>,

    /// What finding those rows cost.
    pub counts: SymbolicCounts,
}

impl<const N: usize> Preprocessed<N> {
    /// Drop what interning produced — [`Preprocessed::monomials`] and
    /// [`Preprocessed::term_handles`] — which nothing needs once the matrix has its columns.
    ///
    /// Called by the reduction step the moment construction returns. Without it they would stay
    /// live for the rest of the batch — through elimination, where the dense backend's buffer is —
    /// and the handout would have traded a hash pass for a working-set increase. #536 is the
    /// precedent for not leaving that to be argued about: both are released at the point the
    /// old code freed its own copy, so the peak is no worse than before the handout. The handles
    /// make that discipline matter more, not less: the arena is `num_columns` monomials and the
    /// handles are `num_nonzeros` words, which is the larger of the two by the column density.
    pub fn release_monomials(&mut self) {
        self.monomials = Vec::new();
        self.term_handles = Vec::new();
    }

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
    let counts = SymbolicCounts::default();
    let mut rows: Vec<PreprocessedRow<N>> = Vec::with_capacity(2 * pairs.len());

    // Monomials that are the leading monomial of some row, so the invariant already holds there.
    let mut covered: MonomialSet<N> = MonomialSet::default();

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

    // Deduplication happens on **push**, in `enqueue`, rather than when a monomial is popped.
    // That is the whole of #305. Pushing first and testing later bounds the queue by
    // `max_matrix_rows` times the terms per row — by nothing a caller sets — and on
    // `fukuoka-mq-III-n20-seed0` that reached 162 188 194 monomials, a single `VecDeque` reserve of
    // 2^28 slots and **88.4% of a 13 996 MB peak RSS**; see `docs/research/f4-resource-scaling.md`
    // §9.2. Testing first bounds it by the *distinct* monomials in the closure, which is exactly
    // the matrix's column count and therefore `max_matrix_columns`. The peak is reached before any
    // matrix exists, so no entry or byte budget can see it; this is the only place that can.
    //
    // **Why this is the same algorithm and not merely a cheaper one.** Write `E_pop` for the
    // pop-time `examined` set and `E_push` for this one. A monomial enters `E_push` when it is
    // enqueued but enters `E_pop` only when it is processed, so the two sets differ at every
    // intermediate moment and the claim cannot be that they agree pointwise. What has to be
    // identical is the **sequence of processed monomials**, because everything downstream —
    // `covered`, `rows`, the divisor queries, and where the row budget is crossed — is a function
    // of it alone. It is identical, by induction over processing steps on two invariants:
    //
    // 1. `E_push` = (processed) u (queued). A monomial enters `E_push` exactly when it is enqueued
    //    and leaves the queue exactly when it is processed, and `enqueue` admits it at most once,
    //    so the queue holds precisely the examined-but-not-yet-processed monomials.
    // 2. The push-time queue is the pop-time queue with every already-processed monomial and every
    //    duplicate after the first surviving occurrence deleted.
    //
    // Both queues are FIFO, so under (2) the head of the push-time queue is the first element of
    // the pop-time queue that pop-time deduplication would *not* discard: both algorithms process
    // the same monomial next. They then run the same tests on it against an identical `covered` and
    // an identical basis, so they append the same row and offer the same term sequence; (1) says
    // the predicate `enqueue` filters by is exactly the already-seen predicate that defines (2), so
    // (2) is restored. The base case is the initial fill, where nothing is processed yet and (2) is
    // the definition of `enqueue`.
    //
    // The consequence worth stating, because #305 expected the opposite, is that the **row order
    // does not move**. Deduplicating on push keeps a monomial at its first occurrence's position in
    // the queue, and deduplicating on pop also processes it at its first occurrence's position, so
    // the two agree on order and not merely on membership. At termination both queues are empty and
    // `E_push` = `E_pop`; `rows`, `leading_monomials`, `divisor_queries` and `divisor_scan_steps`
    // are equal element for element, which `test_push_time_deduplication_preserves_the_closure`
    // checks batch by batch against `symbolic_preprocessing_pop_deduplicated`.
    //
    // `monomials_enqueued` still counts *offers* rather than admissions, so the figures recorded
    // against it before this change stay comparable. `max_pending_monomials` is what moves.
    close_over_rows(basis, rows, covered, counts, max_rows, selection, cache)
}

/// The rows of the one Macaulay matrix that interreduces a whole basis.
///
/// # What this is
///
/// Every element of `basis` becomes a row at multiplier **one**, and the closure then supplies a
/// reducer multiple for every reducible monomial those rows contain. Reducing the resulting matrix
/// to *reduced* row echelon form clears every pivot column out of every other row, and the pivot
/// columns are exactly the reducible monomials — so the row led by each element's own leading
/// monomial comes out with no monomial divisible by any other element's leading monomial. That is
/// the definition of the reduced Gröbner basis.
///
/// # Why each element's own leading monomial is seeded into `covered`
///
/// Without it the closure would find that `lm(g_i)` is divisible by `lm(g_i)` and add `1 · g_i` as
/// a *reducer* row — a duplicate of the element row it came from. Seeding is the same device
/// [`symbolic_preprocessing_with`] uses for a pair's lcm, and for the same reason.
///
/// # Why every leading monomial is a pivot, which is what makes the extraction sound
///
/// `basis` must be **minimized**: no element's leading monomial divides another's. Then a reducer
/// row `t · g_j` has leading monomial `t · lm(g_j)`, which equals some `lm(g_i)` only if
/// `lm(g_j)` divides `lm(g_i)` — excluded for `i != j` by minimality, and forcing `t = 1` for
/// `i == j`, which is the element row rather than a reducer. So the input rows have **distinct**
/// leading monomials, every one of them is a pivot, and exactly one row ends up led by each
/// `lm(g_i)`.
///
/// # Errors
/// [`RowBudgetExceeded`] if the closure would need more than `max_rows` rows.
pub(crate) fn interreduction_rows<const N: usize, F: FiniteField>(
    basis: &MonicBasis<N, F>,
    max_rows: usize,
    selection: ReducerSelection,
    cache: &mut ReducerCache<N>,
) -> Result<Preprocessed<N>, RowBudgetExceeded> {
    let counts = SymbolicCounts::default();
    let mut rows: Vec<PreprocessedRow<N>> = Vec::with_capacity(basis.len());
    let mut covered: MonomialSet<N> = MonomialSet::default();

    for basis_index in 0..basis.len() {
        if rows.len() == max_rows {
            return Err(RowBudgetExceeded { limit: max_rows });
        }
        rows.push(PreprocessedRow {
            multiplier: Monomial::one(),
            basis_index,
            // Not `Reducer`: these are the rows being reduced, which is what `PairComponent` means
            // structurally even though no critical pair is involved. The index is the element's,
            // so a row's origin is still recoverable.
            kind: RowKind::PairComponent { pair: basis_index },
        });
        covered.insert(basis.element(basis_index).leading_monomial);
    }

    close_over_rows(basis, rows, covered, counts, max_rows, selection, cache)
}

/// Close a seed row set under divisibility, adding a reducer multiple for every reducible monomial
/// no row already leads with.
///
/// Shared by [`symbolic_preprocessing_with`], whose seed is the two halves of each critical pair,
/// and by final interreduction's matrix route, whose seed is every basis element at multiplier one.
/// Written once because the push-time deduplication discipline below carries a correctness
/// argument, and two copies of an argument is one copy too many.
///
/// `covered` must already hold the leading monomial of every seed row. That is what stops a seed
/// row from acquiring a reducer multiple of itself — for a pair, the lcm whose cancellation is the
/// point of the pair; for an interreduction row, the element's own leading monomial.
///
/// # Errors
/// [`RowBudgetExceeded`] if the closure would need more than `max_rows` rows.
#[allow(clippy::too_many_arguments)]
fn close_over_rows<const N: usize, F: FiniteField>(
    basis: &MonicBasis<N, F>,
    mut rows: Vec<PreprocessedRow<N>>,
    mut covered: MonomialSet<N>,
    mut counts: SymbolicCounts,
    max_rows: usize,
    selection: ReducerSelection,
    cache: &mut ReducerCache<N>,
) -> Result<Preprocessed<N>, RowBudgetExceeded> {
    // The interner the queue deduplicates through. It assigns each distinct monomial a handle as a
    // side effect of the test it was already making, which is the whole of #621: `term_handles`
    // records what the test already found, so the row scatter has a column to read rather than a
    // monomial to rederive and hash again.
    let mut examined: MonomialMap<N, MonomialHandle> = MonomialMap::default();
    let mut monomials: Vec<Monomial<N>> = Vec::new();
    let mut term_handles: Vec<MonomialHandle> = Vec::new();
    let mut pending: VecDeque<Monomial<N>> = VecDeque::new();

    for row in &rows {
        for (monomial, _) in basis.shifted_terms(row.basis_index, &row.multiplier) {
            term_handles.push(enqueue(
                monomial,
                &mut pending,
                &mut examined,
                &mut monomials,
                &mut counts,
            ));
        }
    }
    counts.max_pending_monomials = counts.max_pending_monomials.max(pending.len());

    while let Some(monomial) = pending.pop_front() {
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
        // The handles of this row's terms are appended before the row is, so `term_handles` stays
        // in `rows` order and a row's run of it is found by walking the two together. The row
        // budget was checked above, so there is no path that appends handles for a row that is
        // never pushed.
        for (shifted, _) in basis.shifted_terms(basis_index, &multiplier) {
            term_handles.push(enqueue(
                shifted,
                &mut pending,
                &mut examined,
                &mut monomials,
                &mut counts,
            ));
        }
        // Sampled here rather than after a pop, because the queue grows only in `enqueue` and
        // every push of an iteration happens in the run just above: this is the exact high-water
        // mark rather than a figure one row's terms below it.
        counts.max_pending_monomials = counts.max_pending_monomials.max(pending.len());

        rows.push(PreprocessedRow {
            multiplier,
            basis_index,
            kind: RowKind::Reducer,
        });
    }

    Ok(Preprocessed {
        rows,
        leading_monomials: covered,
        monomials,
        term_handles,
        counts,
    })
}

/// Offer `monomial` to the pending queue, admitting it only if `examined` had not seen it, and
/// return its handle either way.
///
/// Counts the offer either way too, so `monomials_enqueued` keeps the pre-deduplication meaning the
/// recorded memory figures were taken against. See the argument at the call site in
/// [`symbolic_preprocessing_with`] for why admitting here rather than on pop leaves the closure,
/// the rows and their order unchanged.
///
/// The handle costs nothing that the deduplication test was not already paying: one hash of the
/// monomial, one probe. `entry` rather than `insert` only so the occupied case can report the
/// handle it finds.
fn enqueue<const N: usize>(
    monomial: Monomial<N>,
    pending: &mut VecDeque<Monomial<N>>,
    examined: &mut MonomialMap<N, MonomialHandle>,
    monomials: &mut Vec<Monomial<N>>,
    counts: &mut SymbolicCounts,
) -> MonomialHandle {
    counts.monomials_enqueued += 1;
    match examined.entry(monomial) {
        Entry::Occupied(seen) => *seen.get(),
        Entry::Vacant(slot) => {
            // Checked once per *column* rather than per entry, so the cost is nil, and a wrap here
            // would be a silently wrong matrix rather than a refusal.
            let handle = MonomialHandle::try_from(monomials.len())
                .expect("a batch holds fewer distinct monomials than a handle can name");
            monomials.push(monomial);
            slot.insert(handle);
            pending.push_back(monomial);
            handle
        }
    }
}

/// [`symbolic_preprocessing_with`]'s pre-#305 queue discipline: enqueue every term of every row,
/// and deduplicate only when popping.
///
/// A reimplementation kept for one purpose, which is to let the test suite check the two
/// disciplines against each other batch by batch — the empirical half of the closure-equivalence
/// argument at the push site, and the half that matters, because two different closures can reach
/// the same reduced basis by different matrices. A reimplementation rather than a runtime flag,
/// because a flag would let the unbounded discipline reach a caller.
///
/// Pop-time deduplication has no handle to hand out when a term is pushed, so the arena and the
/// per-term handles are recovered in a second pass once the closure is complete. That keeps
/// [`Preprocessed`]'s layout invariant total — a caller could build a matrix from this — at a cost
/// that does not matter in a route only the test suite calls.
#[cfg(test)]
pub(crate) fn symbolic_preprocessing_pop_deduplicated<const N: usize, F: FiniteField>(
    basis: &MonicBasis<N, F>,
    pairs: &[CriticalPair<N>],
    max_rows: usize,
    selection: ReducerSelection,
    cache: &mut ReducerCache<N>,
) -> Result<Preprocessed<N>, RowBudgetExceeded> {
    let mut counts = SymbolicCounts::default();
    let mut rows: Vec<PreprocessedRow<N>> = Vec::with_capacity(2 * pairs.len());
    let mut covered: MonomialSet<N> = MonomialSet::default();
    let mut examined: MonomialSet<N> = MonomialSet::default();
    let mut pending: VecDeque<Monomial<N>> = VecDeque::new();

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
            continue;
        };
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

    // The second pass. It visits the rows in order and each row's terms in order, which is exactly
    // the sequence the push-time discipline interns in, so the arena it builds is the same one.
    let mut handle_of: MonomialMap<N, MonomialHandle> = MonomialMap::default();
    let mut monomials: Vec<Monomial<N>> = Vec::new();
    let mut term_handles: Vec<MonomialHandle> = Vec::new();
    for row in &rows {
        for (monomial, _) in basis.shifted_terms(row.basis_index, &row.multiplier) {
            let next = MonomialHandle::try_from(monomials.len()).expect("a handle names it");
            let handle = *handle_of.entry(monomial).or_insert(next);
            if handle == next {
                monomials.push(monomial);
            }
            term_handles.push(handle);
        }
    }

    Ok(Preprocessed {
        rows,
        leading_monomials: covered,
        monomials,
        term_handles,
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
        CacheMode, MonicBasis, MonomialSet, Preprocessed, PreprocessedRow, ReducerCache,
        RowBudgetExceeded, RowKind, SymbolicCounts,
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

    /// The probe's replay covers exactly the tests the selection policy performed, under each
    /// policy, so its three counters describe the shipping scan and not a second one.
    #[test]
    fn test_the_probe_replays_exactly_the_scan_the_policy_performed() {
        let generators = system(&["x^2 + y", "x*y + z", "y^3 + x", "z^2 + x*y + 1"]);
        for order in ALL_ORDERS {
            for selection in [
                ReducerSelection::FirstApplicable,
                ReducerSelection::LargestLeadingMonomial,
                ReducerSelection::FewestTerms,
                ReducerSelection::MostTerms,
            ] {
                let mut basis = MonicBasis::new(&generators, order);
                basis.probe_divmask_from(generators.iter());
                assert!(basis.divmask_is_informative());

                let mut counts = SymbolicCounts::default();
                for a in 0..4u32 {
                    for b in 0..4u32 {
                        for c in 0..4u32 {
                            basis.find_divisor_with(
                                &Monomial::<3>::new(&[a, b, c]),
                                selection,
                                &mut counts,
                            );
                        }
                    }
                }
                assert_eq!(
                    counts.divmask_tests,
                    counts.divisor_scan_steps,
                    "{} under {:?}: the replay walked a different set of tests",
                    order.name(),
                    selection
                );
                assert!(counts.divmask_negative <= counts.divmask_tests);
                assert!(counts.divmask_decided <= counts.divmask_negative);
                assert!(
                    counts.divmask_decided > 0,
                    "{} under {:?}: the probe decided nothing, so the fixture measures nothing",
                    order.name(),
                    selection
                );
            }
        }
    }

    /// With the probe on, the divisor selected is the same one, element for element.
    ///
    /// The property that makes this measurement-only: a probe that could change which divisor is
    /// returned would change the multiplier, the row, and the matrix — so the counters would be
    /// about a computation nothing else performs.
    #[test]
    fn test_the_probe_does_not_change_the_divisor_selected() {
        let generators = system(&["x^2 + y", "x*y + z", "y^3 + x", "z^2 + x*y + 1"]);
        for order in ALL_ORDERS {
            for selection in [
                ReducerSelection::FirstApplicable,
                ReducerSelection::LargestLeadingMonomial,
                ReducerSelection::FewestTerms,
                ReducerSelection::MostTerms,
            ] {
                let plain = MonicBasis::new(&generators, order);
                let mut probed = MonicBasis::new(&generators, order);
                probed.probe_divmask_from(generators.iter());
                for a in 0..5u32 {
                    for b in 0..5u32 {
                        for c in 0..5u32 {
                            let monomial = Monomial::<3>::new(&[a, b, c]);
                            let mut here = SymbolicCounts::default();
                            let mut there = SymbolicCounts::default();
                            assert_eq!(
                                plain.find_divisor_with(&monomial, selection, &mut here),
                                probed.find_divisor_with(&monomial, selection, &mut there),
                                "{} under {:?}: the probe changed the divisor for {monomial}",
                                order.name(),
                                selection
                            );
                        }
                    }
                }
            }
        }
    }

    /// An element appended after the probe was installed gets a mask, rather than panicking or
    /// being read against a stale one.
    #[test]
    fn test_the_probe_covers_elements_appended_after_it_was_installed() {
        let generators = system(&["x^2 + y", "x*y + z"]);
        let order = MonomialOrder::GradedReverseLexicographic;
        let mut basis = MonicBasis::new(&generators, order);
        basis.probe_divmask_from(generators.iter());
        basis.push(&parse("y^4 + z"), order);

        let mut counts = SymbolicCounts::default();
        basis.find_divisor_with(
            &Monomial::<3>::new(&[1, 1, 1]),
            ReducerSelection::MostTerms,
            &mut counts,
        );
        assert_eq!(counts.divmask_tests, basis.len());
        assert_eq!(counts.divisor_scan_steps, basis.len());
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
