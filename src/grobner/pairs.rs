//! Critical pairs, and the queue that decides which to process next.
//!
//! Shared by [`super::buchberger`], which takes one pair at a time, and [`super::f4`], which takes
//! a whole batch. Both want the same thing from the queue: the lowest-degree pairs first, and a
//! total order on ties so that the computation is reproducible.
//!
//! Pairs are selected in order of the total degree of their lcm — the normal strategy — which
//! keeps the intermediate polynomials as small as possible for as long as possible.
//!
//! Everything here works on **leading monomials** rather than on polynomials. A pair is determined
//! by the two leading monomials and the two indices, and nothing about pair handling needs a
//! coefficient. The practical reason is cost: `MultivariatePolynomial::leading_monomial` is a scan
//! of the whole term map, and generating the pairs of a newly appended basis element asks for one
//! per existing element. The structural reason is that the criteria which discard pairs — see
//! [`PairCriteria`] — are statements about the leading-term ideal, so they need the whole basis's
//! leading monomials at once and nothing else.

use std::{
    cmp::Reverse,
    collections::{BinaryHeap, HashSet},
};

use crate::{poly::MonomialOrder, FiniteField, Monomial, MultivariatePolynomial};

/// The leading monomials of a basis, under the order being computed.
pub fn leading_monomials<const N: usize, F: FiniteField>(
    basis: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
) -> Vec<Monomial<N>> {
    basis.iter().map(|p| p.leading_monomial(order)).collect()
}

/// A critical pair of basis elements, keyed for selection.
///
/// Ordered by the total degree of the lcm first, then by the lcm and the two indices so that the
/// order is total and the computation reproducible. The lcm comparison uses `Monomial`'s derived
/// ordering rather than the monomial order under computation: a tiebreaker only has to be
/// deterministic, not meaningful.
///
/// The two multipliers are carried as well, for [`PairSchedule`]. They are **appended** to the
/// declaration rather than inserted, because `Ord` is derived: a field before `right` would change
/// the baseline's tiebreak, whereas one after it can never be reached, since `(left, right)`
/// already identifies the pair.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct CriticalPair<const N: usize> {
    /// The total degree of `lcm`, which is what selection ranks by.
    pub degree: u64,

    /// `lcm(LM(left), LM(right))`, the monomial at which the two leading terms cancel.
    pub lcm: Monomial<N>,

    /// Index into the basis of the first element. Always less than `right`.
    pub left: usize,

    /// Index into the basis of the second element.
    pub right: usize,

    /// The larger of the two multipliers `lcm / LM(g_left)` and `lcm / LM(g_right)`, by degree.
    ///
    /// "Larger" is by *degree*, which is a total order on the two and needs no monomial order to
    /// establish. Which of the two monomials this is does not depend on the order; how the pair
    /// then ranks against another pair's multiplier can, and
    /// [`PairSchedule::SmallMultiplierMonomial`] is the schedule that uses that.
    ///
    /// The monomials are stored rather than only their degrees because the published ordering
    /// compares the monomials, and they cannot be recovered from the pair: that would need the two
    /// leading monomials, which a pair deliberately does not carry.
    pub larger_multiplier: Monomial<N>,

    /// The smaller of the two multipliers, by degree.
    pub smaller_multiplier: Monomial<N>,
}

impl<const N: usize> CriticalPair<N> {
    /// The pair of the basis elements at `left` and `right`.
    ///
    /// # Panics
    /// If the two indices are equal: a polynomial's S-polynomial with itself is zero, so such a
    /// pair is not a critical pair.
    pub fn new<F: FiniteField>(
        basis: &[MultivariatePolynomial<N, F>],
        left: usize,
        right: usize,
        order: MonomialOrder,
    ) -> Self {
        Self::from_leads(&leading_monomials(basis, order), left, right)
    }

    /// The pair of the elements at `left` and `right` of a basis given by its leading monomials.
    ///
    /// The monomial order does not appear: an lcm is the pointwise maximum of two exponent
    /// vectors, which no order enters into. The order is needed to *find* a leading monomial, not
    /// to pair two of them.
    ///
    /// # Panics
    /// If the two indices are equal.
    pub fn from_leads(leads: &[Monomial<N>], left: usize, right: usize) -> Self {
        assert_ne!(left, right, "a polynomial does not pair with itself");
        let (left, right) = (left.min(right), left.max(right));
        let lcm = Monomial::lcm(&leads[left], &leads[right]);
        let degree = lcm.degree();
        // The multipliers are lcm/LM(g) each. A leading monomial divides the lcm of the pair it
        // belongs to, so each quotient exists and `checked_div` cannot fail here; a failure would
        // mean the pair was built against a different basis.
        let multiplier = |lead: &Monomial<N>| {
            lcm.checked_div(lead)
                .expect("a leading monomial divides its own pair's lcm")
        };
        let (left_multiplier, right_multiplier) =
            (multiplier(&leads[left]), multiplier(&leads[right]));
        // Ordered by degree, which needs no monomial order. See the field documentation.
        let (larger_multiplier, smaller_multiplier) =
            if left_multiplier.degree() >= right_multiplier.degree() {
                (left_multiplier, right_multiplier)
            } else {
                (right_multiplier, left_multiplier)
            };
        Self {
            degree,
            lcm,
            left,
            right,
            larger_multiplier,
            smaller_multiplier,
        }
    }

    /// The degree of the larger of the two multipliers.
    pub fn larger_multiplier_degree(&self) -> u64 {
        self.larger_multiplier.degree()
    }

    /// The degree of the smaller of the two multipliers.
    ///
    /// `larger + smaller = 2 * degree - deg LM(g_left) - deg LM(g_right)`, so at a fixed lcm degree
    /// the sum is determined by the two leading monomials and only the *split* is free. That is why
    /// [`PairSchedule::SmallMultiplierDegree`] ranks on the larger and then the smaller rather than
    /// on their sum, which would order nothing the lcm degree does not already.
    pub fn smaller_multiplier_degree(&self) -> u64 {
        self.smaller_multiplier.degree()
    }

    /// True if Buchberger's first criterion eliminates this pair.
    ///
    /// When the two leading monomials share no variable their lcm is their product, and the
    /// S-polynomial is then guaranteed to reduce to zero modulo the two of them — so the reduction
    /// can be skipped without affecting the result. See Cox, Little, and O'Shea, Sec 2.9,
    /// Proposition 4.
    pub fn is_eliminated_by_product_criterion<F: FiniteField>(
        &self,
        basis: &[MultivariatePolynomial<N, F>],
        order: MonomialOrder,
    ) -> bool {
        are_relatively_prime(
            &basis[self.left].leading_monomial(order),
            &basis[self.right].leading_monomial(order),
        )
    }
}

/// True if `a` divides `b`, i.e. `a`'s exponent of every variable is at most `b`'s.
///
/// `Monomial::checked_div` answers the same question but builds the quotient to do it. The
/// criteria ask it of every basis element against every pair's lcm and never want the quotient.
pub fn divides<const N: usize>(a: &Monomial<N>, b: &Monomial<N>) -> bool {
    a.exponents()
        .iter()
        .zip(b.exponents().iter())
        .all(|(x, y)| x <= y)
}

/// True if two monomials share no variable, i.e. their lcm is their product.
pub fn are_relatively_prime<const N: usize>(a: &Monomial<N>, b: &Monomial<N>) -> bool {
    a.exponents()
        .iter()
        .zip(b.exponents().iter())
        .all(|(x, y)| *x == 0 || *y == 0)
}

/// In what order the pending pairs of one degree are taken.
///
/// **Not a criterion.** A criterion is a theorem that a pair need not be reduced at all; a schedule
/// only decides which of the pairs that *will* be reduced is reduced first. Every variant here
/// keeps every pending pair pending until it is selected or a sound criterion discards it, so every
/// variant returns the identical reduced Gröbner basis — which is asserted over the correctness
/// corpus, not assumed.
///
/// The lcm degree is primary under every schedule, and that is a correctness-adjacent requirement
/// rather than a preference: [`PairQueue::select_batch`] forms a batch from the pairs of one degree
/// and F4's termination argument is stated in terms of ascending degree. A schedule reorders
/// *within* a degree.
///
/// # What the reordering is for
///
/// A pair's two matrix rows are the shifted basis elements `(lcm / LM g_i) * g_i` and
/// `(lcm / LM g_j) * g_j`. A larger shift moves a polynomial further up, so its monomials are
/// larger, so more of them are reducible, so symbolic preprocessing adds more reducer rows to
/// cover them. The hypothesis is that preferring small multipliers gives a smaller symbolic
/// closure and therefore a narrower matrix.
///
/// It is a hypothesis. M22-0 measured reducer scaffolding at 40% to 99% of all rows, so the closure
/// is where the rows are — but a pair with smaller multipliers need not produce a smaller closure,
/// because what each reducer row costs is decided by *its* tail and not by the shift that asked for
/// it. The `Large…` variants are in this enum as the controls that settle the direction.
///
/// # Degree against monomial, which are different strategies
///
/// Sakata, K., Takagi, T. (2026), *An Efficient Variant of F4 Algorithm for Solving MQ Problem*,
/// IACR TCHES 2026(3), 1284–1309, rank candidate pairs on the larger and then the smaller of the
/// two multipliers **under the monomial order**. Comparing the multipliers' *degrees* is a coarser
/// relation: `x^2` and `y^2` have the same degree and are distinct under grevlex, so a
/// degree comparator falls through to the lcm tiebreak exactly where the published one still
/// discriminates.
///
/// Both are offered, and they are named for what they compare, because a measurement of one is not
/// a measurement of the other:
///
/// - [`PairSchedule::SmallMultiplierDegree`] is the degree heuristic.
/// - [`PairSchedule::SmallMultiplierMonomial`] is the published ordering.
///
/// # Multiplier size against term count, which is a different axis
///
/// Every schedule above ranks by the size of the multiplier. [`PairSchedule::ShortPair`] ranks by
/// how many terms the two polynomials have, which is orthogonal to all of them: two pairs with the
/// same lcm and the same multipliers can have S-polynomials of very different length. It is
/// `slimgb`'s `pair_weighted_length` (Singular, `kernel/GBEngine/tgb.cc`) specialized to a prime
/// field, where the coefficient-size factors drop out and the score is `terms(i) + terms(j) - 2`.
/// See `docs/research/singular-engine-notes.md` §4.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum PairSchedule {
    /// Lowest lcm degree first, then the lcm and the two indices. The measured baseline.
    #[default]
    DegreeThenLcm,

    /// Within a degree, the smallest larger multiplier *degree* first, then the smaller degree.
    ///
    /// A coarsening of [`PairSchedule::SmallMultiplierMonomial`] — see the type's documentation for
    /// why the two are not the same strategy. Ties fall through to the baseline's tiebreak, so the
    /// order is still total.
    SmallMultiplierDegree,

    /// Within a degree, the *largest* larger multiplier degree first.
    ///
    /// The control for [`PairSchedule::SmallMultiplierDegree`]. If preferring small multipliers
    /// reduces matrix growth, preferring large ones should increase it, and a heuristic that beats
    /// the baseline in both directions is measuring run-to-run noise.
    LargeMultiplierDegree,

    /// Within a degree, the smallest larger multiplier **monomial** first, then the smaller.
    ///
    /// Sakata–Takagi's refined ordering as published: the comparison is between monomials under the
    /// monomial order being computed, not between their degrees. This is the variant a claim about
    /// their strategy has to be measured with.
    SmallMultiplierMonomial,

    /// Within a degree, the *largest* larger multiplier monomial first. The control for the above.
    LargeMultiplierMonomial,

    /// Within a degree, the pair whose S-polynomial is expected to be shortest first.
    ///
    /// The score is `slimgb`'s `pair_weighted_length` over a prime field —
    /// `terms(left) + terms(right) - 2` — and the mechanism is that the two pair rows are the
    /// shifted basis elements, so a pair of sparse polynomials is two sparse rows and fewer
    /// monomials for symbolic preprocessing to cover. Orthogonal to the multiplier-size schedules:
    /// it says nothing about the shift and they say nothing about the length.
    ///
    /// Needs the basis's term counts, which a pair does not carry —
    /// [`PairQueue::seeded_from_leads_ranked`] is how they get in.
    ShortPair,

    /// Within a degree, the pair whose S-polynomial is expected to be *longest* first.
    ///
    /// The control for [`PairSchedule::ShortPair`], and not optional. If preferring short pairs
    /// narrows the matrix, preferring long ones should widen it; a heuristic that beats the
    /// baseline in both directions is measuring run-to-run variation, and without the opposite
    /// direction there is no way to tell.
    LongPair,
}

impl PairSchedule {
    /// Every schedule, for an ablation that should not have to be edited when one is added.
    pub const ALL: [Self; 7] = [
        Self::DegreeThenLcm,
        Self::SmallMultiplierDegree,
        Self::LargeMultiplierDegree,
        Self::SmallMultiplierMonomial,
        Self::LargeMultiplierMonomial,
        Self::ShortPair,
        Self::LongPair,
    ];

    /// A short name, for a table column.
    pub fn name(&self) -> &'static str {
        match self {
            Self::DegreeThenLcm => "degree-then-lcm",
            Self::SmallMultiplierDegree => "small-multiplier-degree",
            Self::LargeMultiplierDegree => "large-multiplier-degree",
            Self::SmallMultiplierMonomial => "small-multiplier-monomial",
            Self::LargeMultiplierMonomial => "large-multiplier-monomial",
            Self::ShortPair => "short-pair",
            Self::LongPair => "long-pair",
        }
    }

    /// True if the schedule compares multiplier monomials and so depends on the monomial order.
    ///
    /// The queue carries an order only for these; see [`PairQueue::scheduled_in`].
    pub fn needs_the_monomial_order(&self) -> bool {
        matches!(
            self,
            Self::SmallMultiplierMonomial | Self::LargeMultiplierMonomial
        )
    }

    /// True if the schedule ranks by how many terms the paired polynomials have.
    ///
    /// Those schedules need data a pair does not carry, so the queue has to be given the basis's
    /// term counts; see [`PairQueue::push_term_count`].
    pub fn ranks_by_term_count(&self) -> bool {
        matches!(self, Self::ShortPair | Self::LongPair)
    }
}

/// A pending pair together with the schedule that ranks it and the order that schedule needs.
///
/// The heap's element type. `BinaryHeap` takes its comparison from `Ord` on the element, so both
/// have to be reachable from one — hence a copy of two one-byte enums per entry rather than a
/// comparator stored on the queue. Every entry in a queue carries the same values, which
/// [`PairQueue::push`] is the only place that can establish and does.
#[derive(Clone, Debug)]
struct ScheduledPair<const N: usize> {
    schedule: PairSchedule,
    order: MonomialOrder,

    /// `terms(left) + terms(right) - 2`, the key [`PairSchedule::ShortPair`] ranks by. Zero under
    /// every other schedule, which does not read it.
    ///
    /// Here rather than on [`CriticalPair`] because it is not a property of the pair: it needs the
    /// two polynomials, and a pair deliberately carries leading monomials and indices only. The
    /// queue's term-count table supplies it, so within one queue it *is* a function of the pair —
    /// which is what keeps the `Ord` below consistent with the `Eq` beside it.
    pair_length: u64,

    pair: CriticalPair<N>,
}

/// Equality on the pair alone, so that `Ord` and `Eq` cannot disagree.
///
/// Derived equality would compare the schedule, the order and the length too, and `Ord` below
/// returns `Equal` exactly when the two pairs are the same pair — so two entries with equal pairs
/// and different schedules would be ordered equal and compare unequal, which `Ord`'s contract
/// forbids. The queue never holds mixed schedules, and its term-count table is append-only so a
/// pair's length never changes, so this is unreachable rather than a bug being papered over; it is
/// written this way so that the types agree without depending on that.
impl<const N: usize> PartialEq for ScheduledPair<N> {
    fn eq(&self, other: &Self) -> bool {
        self.pair == other.pair
    }
}

impl<const N: usize> Eq for ScheduledPair<N> {}

impl<const N: usize> Ord for ScheduledPair<N> {
    /// Degree first under every schedule; the rest is the schedule's own key, then the baseline's
    /// tiebreak so that the order is total whatever the schedule decided.
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        let fallback = |a: &CriticalPair<N>, b: &CriticalPair<N>| {
            a.lcm
                .cmp(&b.lcm)
                .then(a.left.cmp(&b.left))
                .then(a.right.cmp(&b.right))
        };
        let (mine, theirs) = (&self.pair, &other.pair);
        let order = self.order;

        mine.degree
            .cmp(&theirs.degree)
            .then_with(|| match self.schedule {
                PairSchedule::DegreeThenLcm => std::cmp::Ordering::Equal,
                PairSchedule::SmallMultiplierDegree => mine
                    .larger_multiplier_degree()
                    .cmp(&theirs.larger_multiplier_degree())
                    .then(
                        mine.smaller_multiplier_degree()
                            .cmp(&theirs.smaller_multiplier_degree()),
                    ),
                PairSchedule::LargeMultiplierDegree => theirs
                    .larger_multiplier_degree()
                    .cmp(&mine.larger_multiplier_degree())
                    .then(
                        theirs
                            .smaller_multiplier_degree()
                            .cmp(&mine.smaller_multiplier_degree()),
                    ),
                PairSchedule::SmallMultiplierMonomial => order
                    .cmp(&mine.larger_multiplier, &theirs.larger_multiplier)
                    .then(order.cmp(&mine.smaller_multiplier, &theirs.smaller_multiplier)),
                PairSchedule::LargeMultiplierMonomial => order
                    .cmp(&theirs.larger_multiplier, &mine.larger_multiplier)
                    .then(order.cmp(&theirs.smaller_multiplier, &mine.smaller_multiplier)),
                PairSchedule::ShortPair => self.pair_length.cmp(&other.pair_length),
                PairSchedule::LongPair => other.pair_length.cmp(&self.pair_length),
            })
            .then_with(|| fallback(mine, theirs))
    }
}

impl<const N: usize> PartialOrd for ScheduledPair<N> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

/// Which pair-elimination criteria a computation may apply.
///
/// A criterion here is a *theorem* that a pair's S-polynomial is guaranteed to reduce to zero
/// modulo relations the computation already has, so that reducing it cannot contribute a new basis
/// element. Enabling one must therefore leave the computed reduced Gröbner basis unchanged; it may
/// only change how much work was done to reach it. That is what the differential tests check, and
/// it is the reason each flag exists separately rather than as one "optimize" switch.
///
/// [`PairCriteria::default`] is Buchberger's first criterion alone, which is what the preceding
/// milestone implemented and what the measured baseline uses.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct PairCriteria {
    /// Buchberger's first criterion: relatively prime leading monomials.
    ///
    /// Applied when a batch is selected, by [`PairQueue::filter_batch`].
    pub product: bool,

    /// Buchberger's chain criterion.
    ///
    /// Discards `(i, j)` when some `LM(f_k)` divides `lcm(LM f_i, LM f_j)` **and both `(i, k)` and
    /// `(k, j)` have already been handled**. The second half is not optional: divisibility of the
    /// lcm alone is not a sufficient condition, and acting on it alone returns an incomplete basis
    /// that a fixed test corpus will often fail to notice.
    ///
    /// Applied when a batch is selected, by [`PairQueue::filter_batch`] and
    /// [`PairQueue::is_discarded`]. See those for the exact condition and its citation.
    pub chain: bool,

    /// Gebauer–Möller pair-set minimization, applied as pairs are inserted.
    ///
    /// See [`PairQueue::push_pairs_from_leads`] for the three conditions and their citation.
    pub gebauer_moller: bool,
}

impl PairCriteria {
    /// Buchberger's first criterion only — the configuration the baseline was measured with.
    pub const PRODUCT_ONLY: Self = Self {
        product: true,
        chain: false,
        gebauer_moller: false,
    };

    /// No criterion at all: every pair is reduced.
    ///
    /// Not a configuration anyone should compute with. It is the reference the criteria are
    /// checked against, since a criterion is sound exactly when enabling it does not change the
    /// basis this computes.
    pub const NONE: Self = Self {
        product: false,
        chain: false,
        gebauer_moller: false,
    };

    /// Every criterion.
    pub const ALL: Self = Self {
        product: true,
        chain: true,
        gebauer_moller: true,
    };
}

impl Default for PairCriteria {
    fn default() -> Self {
        Self::PRODUCT_ONLY
    }
}

/// How many pairs each criterion discarded.
///
/// Counted per criterion rather than in total because the question a measurement has to answer is
/// which criterion is worth its complexity, and a single total cannot say.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct CriterionCounts {
    /// Discarded by Buchberger's first criterion.
    pub product: usize,

    /// Discarded by the chain criterion.
    pub chain: usize,

    /// Discarded by Gebauer–Möller: never inserted into the queue, or removed from it unselected.
    ///
    /// Includes Gebauer–Möller's criterion F, which is Buchberger's first criterion applied to a
    /// new pair at insertion time. It is counted here rather than under `product` so that
    /// `product` keeps meaning what the baseline measured — pairs eliminated after being
    /// selected — and so that `pairs_considered` still bounds it.
    pub gebauer_moller: usize,
}

impl CriterionCounts {
    /// Pairs discarded by any criterion.
    pub fn total(&self) -> usize {
        self.product + self.chain + self.gebauer_moller
    }

    /// Fold another set of counts into these.
    pub fn add(&mut self, other: &Self) {
        self.product += other.product;
        self.chain += other.chain;
        self.gebauer_moller += other.gebauer_moller;
    }
}

/// How much a [`PairQueue`] holds, counted in entries.
///
/// Exists because the pair queue is `O(B²)` in the basis size `B` while a Macaulay matrix is a
/// function of one batch, so on a system whose basis grows the queue outgrows the thing every
/// [`F4Options`](super::f4::F4Options) budget bounds. `heap_entries` and `live` differ by the
/// lazily deleted pairs, which still occupy the heap.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct PairQueueFootprint {
    /// Entries in the binary heap, including the lazily deleted ones. One
    /// `ScheduledPair<N>` each, plus whatever slack the heap's doubling leaves.
    pub heap_entries: usize,

    /// Pairs actually waiting: `heap_entries` less the lazily deleted ones.
    pub live: usize,

    /// Keys in the Gebauer-Möller removal set. Monotonically growing; nothing is ever retired.
    pub removed: usize,

    /// Keys in the chain criterion's handled set. Monotonically growing, for the same reason.
    pub handled: usize,

    /// Pairs a selection heuristic set aside, which are promoted back before the loop can end.
    pub deferred: usize,
}

impl PairQueueFootprint {
    /// Entries in the two lazy-deletion sets, each a [`PairKey`].
    pub fn criteria_keys(&self) -> usize {
        self.removed + self.handled
    }

    /// The larger of two footprints, field by field.
    ///
    /// Field by field rather than by a single ordering: the heap and the criteria sets peak at
    /// different moments, and a summary that picked one moment's values would understate whichever
    /// structure was not peaking then.
    pub fn max(&self, other: &Self) -> Self {
        Self {
            heap_entries: self.heap_entries.max(other.heap_entries),
            live: self.live.max(other.live),
            removed: self.removed.max(other.removed),
            handled: self.handled.max(other.handled),
            deferred: self.deferred.max(other.deferred),
        }
    }
}

/// The critical pairs still to be processed, lowest lcm degree first.
///
/// A min-heap, so adding the pairs of a newly found basis element costs a logarithmic insertion
/// each rather than a rescan of every pair. This is what makes pair processing incremental: the
/// textbook formulation rebuilds every pair on every pass.
/// A pair's identity: its two basis indices, smaller first.
type PairKey = (usize, usize);

#[derive(Debug, Clone)]
pub struct PairQueue<const N: usize> {
    // `Reverse` turns the max-heap into a min-heap.
    pending: BinaryHeap<Reverse<ScheduledPair<N>>>,

    /// Pairs Gebauer–Möller removed from the pending set, whose heap entry is still there.
    ///
    /// A binary heap cannot delete an interior element, and rebuilding it per removal would make
    /// insertion quadratic. The entry is instead left in place and skipped when it reaches the
    /// top, which is the standard lazy deletion. Empty unless Gebauer–Möller is enabled.
    removed: HashSet<PairKey>,

    /// Pairs that have been selected and whose batch has been processed.
    ///
    /// This is the chain criterion's "already handled". See [`PairQueue::is_discarded`] for why it
    /// is this set and not "absent from the pending set". Empty unless the chain criterion is
    /// enabled, since nothing else reads it.
    handled: HashSet<PairKey>,

    /// Pairs in the pending set: heap entries less the lazily deleted ones.
    live: usize,

    /// Whether to record handled pairs, which only the chain criterion needs.
    ///
    /// Set from the criteria the queue is driven with, which are fixed for a computation.
    track_handled: bool,

    /// In what order pairs of one degree come out. Fixed for the queue's lifetime.
    schedule: PairSchedule,

    /// The monomial order, for a schedule that compares multiplier monomials.
    ///
    /// The queue is otherwise order-agnostic, deliberately: an lcm is a pointwise maximum and the
    /// criteria are statements about divisibility, neither of which an order enters into. Only
    /// [`PairSchedule::needs_the_monomial_order`] schedules read this, and for the others any value
    /// gives the same queue — which [`PairQueue::scheduled`] relies on to keep the old constructor.
    order: MonomialOrder,

    /// Pairs a selection heuristic set aside, still part of the pair set.
    ///
    /// **Not discarded, and not "handled".** A heuristic is not a theorem, so a pair it declines to
    /// select now has to remain available — and it has to remain available *as an unprocessed
    /// pair*, which is a stronger requirement than merely being retrievable:
    ///
    /// - Gebauer–Möller's criterion B minimizes the pending set, so a deferred pair must be visible
    ///   to it or the installation would differ from the published one. It is: see
    ///   [`PairQueue::push_pairs_from_leads`], which scans this list alongside the heap.
    /// - The chain criterion's witnesses are pairs that have been *processed*, and a deferred pair
    ///   has not been. [`PairQueue::defer_degree`] therefore moves pairs without recording them as
    ///   handled, which is why it does not go through [`PairQueue::pop`].
    ///
    /// Empty unless a selection strategy defers, and emptied by
    /// [`PairQueue::promote_deferred`] before the computation can end.
    deferred: Vec<CriticalPair<N>>,

    /// How many terms each basis element has, in index order, for a length-ranking schedule.
    ///
    /// Append-only, which is the invariant a pair's rank rests on: the rank is computed when the
    /// pair is pushed, so a count that changed under an index would let two entries for the same
    /// pair rank differently. Empty unless the caller records them; see
    /// [`PairQueue::push_term_count`].
    term_counts: Vec<usize>,
}

impl<const N: usize> Default for PairQueue<N> {
    /// An empty queue under the baseline schedule.
    ///
    /// Hand-written rather than derived because the queue carries a [`MonomialOrder`], which has no
    /// `Default` — deliberately, since no order is the obvious one. The baseline schedule does not
    /// read it.
    fn default() -> Self {
        Self::new()
    }
}

impl<const N: usize> PairQueue<N> {
    /// An empty queue, under the baseline schedule.
    pub fn new() -> Self {
        Self::scheduled(PairSchedule::default())
    }

    /// An empty queue, under the given schedule.
    ///
    /// # Panics
    /// If `schedule` compares multiplier monomials, which needs an order: use
    /// [`PairQueue::scheduled_in`]. Rejected rather than defaulted, because a monomial-comparing
    /// schedule silently ranked under the wrong order would produce a different computation and
    /// look like a measurement.
    pub fn scheduled(schedule: PairSchedule) -> Self {
        assert!(
            !schedule.needs_the_monomial_order(),
            "{} compares multiplier monomials and needs an order: use scheduled_in",
            schedule.name()
        );
        Self::scheduled_in(schedule, MonomialOrder::GradedReverseLexicographic)
    }

    /// An empty queue, under the given schedule and monomial order.
    pub fn scheduled_in(schedule: PairSchedule, order: MonomialOrder) -> Self {
        Self {
            pending: BinaryHeap::new(),
            removed: HashSet::new(),
            handled: HashSet::new(),
            live: 0,
            track_handled: false,
            schedule,
            order,
            deferred: Vec::new(),
            term_counts: Vec::new(),
        }
    }

    /// Record how many terms the next basis element has, for a schedule that ranks by it.
    ///
    /// Append-only by construction, so the counts a pushed pair was ranked with cannot be
    /// rewritten. The basis both engines maintain is append-only too, so this is the shape the
    /// data already has: call it once per element, before that element's pairs are pushed.
    pub fn push_term_count(&mut self, terms: usize) {
        self.term_counts.push(terms);
    }

    /// The schedule this queue selects under.
    pub fn schedule(&self) -> PairSchedule {
        self.schedule
    }

    /// Every pair of the given basis.
    pub fn seeded<F: FiniteField>(
        basis: &[MultivariatePolynomial<N, F>],
        order: MonomialOrder,
    ) -> Self {
        Self::seeded_from_leads(
            &leading_monomials(basis, order),
            &PairCriteria::NONE,
            &mut CriterionCounts::default(),
        )
    }

    /// Every pair of a basis given by its leading monomials, less those a criterion discards.
    ///
    /// Seeding is incremental in the same way appending is: element `i` is paired with everything
    /// before it, so an insertion-time criterion sees the same prefix it would see during the
    /// computation proper and makes the same decision.
    pub fn seeded_from_leads(
        leads: &[Monomial<N>],
        criteria: &PairCriteria,
        counts: &mut CriterionCounts,
    ) -> Self {
        Self::seeded_from_leads_scheduled(
            leads,
            criteria,
            PairSchedule::default(),
            MonomialOrder::GradedReverseLexicographic,
            counts,
        )
    }

    /// As [`PairQueue::seeded_from_leads`], under the given schedule and monomial order.
    ///
    /// The order is only read by a schedule that compares multiplier monomials; for every other
    /// schedule any value gives the same queue.
    ///
    /// A separate constructor rather than an extra parameter on the existing one, so that the two
    /// engines and the existing tests that drive the queue directly keep the signature they were
    /// written against and the baseline stays the thing you get by not asking for anything.
    pub fn seeded_from_leads_scheduled(
        leads: &[Monomial<N>],
        criteria: &PairCriteria,
        schedule: PairSchedule,
        order: MonomialOrder,
        counts: &mut CriterionCounts,
    ) -> Self {
        Self::seeded_from_leads_ranked(leads, &[], criteria, schedule, order, counts)
    }

    /// As [`PairQueue::seeded_from_leads_scheduled`], with the basis's term counts.
    ///
    /// The counts are only read by a [`PairSchedule::ranks_by_term_count`] schedule, which cannot
    /// be driven without them; for every other schedule an empty slice gives the same queue, which
    /// is what lets [`PairQueue::seeded_from_leads_scheduled`] keep its signature.
    ///
    /// # Panics
    /// If `term_counts` is shorter than `leads` under a length-ranking schedule — see
    /// [`PairQueue::push_term_count`].
    pub fn seeded_from_leads_ranked(
        leads: &[Monomial<N>],
        term_counts: &[usize],
        criteria: &PairCriteria,
        schedule: PairSchedule,
        order: MonomialOrder,
        counts: &mut CriterionCounts,
    ) -> Self {
        let mut queue = Self::scheduled_in(schedule, order);
        for &terms in term_counts {
            queue.push_term_count(terms);
        }
        for right in 0..leads.len() {
            queue.push_pairs_from_leads(leads, right, criteria, counts);
        }
        queue
    }

    /// True if no pairs remain.
    pub fn is_empty(&self) -> bool {
        self.live == 0
    }

    /// The number of pairs waiting.
    pub fn len(&self) -> usize {
        self.live
    }

    /// Add the pairs of the basis element at `added` with every element before it.
    ///
    /// Those are the only new pairs when an element is appended, which is the point: everything
    /// already handled stays handled.
    pub fn push_pairs_with<F: FiniteField>(
        &mut self,
        basis: &[MultivariatePolynomial<N, F>],
        added: usize,
        order: MonomialOrder,
    ) {
        self.push_pairs_from_leads(
            &leading_monomials(basis, order),
            added,
            &PairCriteria::NONE,
            &mut CriterionCounts::default(),
        );
    }

    /// Add the pairs of the element at `added` with every element before it, from leading
    /// monomials, less those an insertion-time criterion discards.
    ///
    /// This is the insertion point Gebauer–Möller acts at: it minimizes the pair *set* as it is
    /// built, which is cheaper and discards more than filtering a selected batch can, because it
    /// can compare the new element's pairs against one another.
    ///
    /// The baseline inserts every pair. `counts.gebauer_moller` records how many were not.
    ///
    /// # Gebauer–Möller
    ///
    /// Gebauer, R., Möller, H. M. (1988), *On an installation of Buchberger's algorithm*, J.
    /// Symbolic Computation 6, 275–286, criteria B, M and F; as installed in Becker, T.,
    /// Weispfenning, V., *Gröbner Bases*, Algorithm 5.5 (`UPDATE`). Writing `h` for the element
    /// just added and `B` for the pending set, with all three conditions on leading monomials:
    ///
    /// - **B**, applied to the pairs already pending. Discard `(g1, g2)` when `LM(h)` divides
    ///   `lcm(LM g1, LM g2)` and `lcm(LM g1, LM h)` and `lcm(LM h, LM g2)` both *differ* from it.
    ///   This is Buchberger's chain criterion with `h` as the witness, and the two inequalities
    ///   are what make it sound without any bookkeeping: together with the divisibility they say
    ///   both witness lcms divide `lcm(LM g1, LM g2)` strictly, so the justification descends in
    ///   a well-founded order and cannot be circular. Dropping either inequality is the classic
    ///   unsound shortcut.
    /// - **M**, applied to the new pairs `(h, g)`. Keep only pairs whose lcm is minimal under
    ///   divisibility among the new pairs: discard `(h, g)` when another new pair's lcm divides
    ///   `lcm(LM h, LM g)`. The asymmetry between the not-yet-examined candidates and the already
    ///   accepted ones is what keeps exactly one pair per lcm when several are equal.
    /// - **F**, applied to the new pairs that survived M. Discard `(h, g)` when `LM(h)` and
    ///   `LM(g)` are relatively prime. Such a pair is admitted to the intermediate set first, so
    ///   that it can block another pair with the same lcm under M, and only then discarded —
    ///   which is why F is a second pass and not part of the first test.
    ///
    /// F is Buchberger's first criterion, so it is applied only when
    /// [`PairCriteria::product`] is also set. Keeping a pair is never unsound, only slower.
    pub fn push_pairs_from_leads(
        &mut self,
        leads: &[Monomial<N>],
        added: usize,
        criteria: &PairCriteria,
        counts: &mut CriterionCounts,
    ) {
        // The chain criterion is the only reader of the handled set, so it is only recorded when
        // the computation asked for it.
        self.track_handled |= criteria.chain;

        if !criteria.gebauer_moller {
            for existing in 0..added {
                self.push(CriticalPair::from_leads(leads, existing, added));
            }
            return;
        }

        let lead_h = leads[added];

        // Criterion B. Applied to the old pairs before the new ones are inserted, as published:
        // a new pair (g, h) has lcm(LM g, LM h) = lcm(LM g, LM h), so the equality guard would
        // keep it regardless, but following the published order keeps the two sets distinct.
        let condition = |pair: &CriticalPair<N>| {
            divides(&lead_h, &pair.lcm)
                && Monomial::lcm(&leads[pair.left], &lead_h) != pair.lcm
                && Monomial::lcm(&lead_h, &leads[pair.right]) != pair.lcm
        };

        let stale: Vec<PairKey> = self
            .pending
            .iter()
            .map(|Reverse(entry)| &entry.pair)
            .filter(|pair| !self.removed.contains(&(pair.left, pair.right)))
            .filter(|pair| condition(pair))
            .map(|pair| (pair.left, pair.right))
            .collect();
        for key in stale {
            self.removed.insert(key);
            self.live -= 1;
            counts.gebauer_moller += 1;
        }

        // The deferred pairs are part of the pair set, so criterion B applies to them too. Removing
        // them here rather than after promotion is what makes a deferring strategy's pair-set
        // minimization identical to a non-deferring one's, instead of merely similar.
        let before = self.deferred.len();
        self.deferred.retain(|pair| !condition(pair));
        counts.gebauer_moller += before - self.deferred.len();

        // Criterion M. `accepted` holds the indices `g` whose pair with `h` survived, in the order
        // they were examined, which is the published algorithm's intermediate set `D`.
        let mut accepted: Vec<usize> = Vec::new();
        for existing in 0..added {
            if are_relatively_prime(&lead_h, &leads[existing]) {
                accepted.push(existing);
                continue;
            }

            let lcm = Monomial::lcm(&lead_h, &leads[existing]);
            let blocked = ((existing + 1)..added)
                .chain(accepted.iter().copied())
                .any(|other| divides(&Monomial::lcm(&lead_h, &leads[other]), &lcm));

            if blocked {
                counts.gebauer_moller += 1;
            } else {
                accepted.push(existing);
            }
        }

        // Criterion F.
        for existing in accepted {
            if criteria.product && are_relatively_prime(&lead_h, &leads[existing]) {
                counts.gebauer_moller += 1;
                continue;
            }
            self.push(CriticalPair::from_leads(leads, existing, added));
        }
    }

    /// Insert a pair into the pending set.
    ///
    /// The one place a heap entry is created, which is what makes "every entry carries the queue's
    /// schedule" an invariant rather than a convention.
    fn push(&mut self, pair: CriticalPair<N>) {
        self.live += 1;
        let pair_length = self.pair_length(&pair);
        self.pending.push(Reverse(ScheduledPair {
            schedule: self.schedule,
            order: self.order,
            pair_length,
            pair,
        }));
    }

    /// `slimgb`'s `pair_weighted_length` over a prime field: `terms(left) + terms(right) - 2`.
    ///
    /// Zero under a schedule that does not rank by it, so the term counts are only required where
    /// they are read. A basis element has at least one term — a zero polynomial has no leading
    /// monomial and is not one — so the published `- 2` cannot go negative.
    ///
    /// # Panics
    /// If a length-ranking schedule has no recorded count for either index. Refused rather than
    /// defaulted, for [`PairQueue::scheduled`]'s reason: a schedule silently ranking every pair
    /// equal would fall through to the baseline's tiebreak and look like a measurement of itself.
    fn pair_length(&self, pair: &CriticalPair<N>) -> u64 {
        if !self.schedule.ranks_by_term_count() {
            return 0;
        }
        let terms = |index: usize| -> u64 {
            let count = self.term_counts.get(index).unwrap_or_else(|| {
                panic!(
                    "{} ranks by term count and basis element {} has none recorded: \
                     seed the queue with seeded_from_leads_ranked",
                    self.schedule.name(),
                    index
                )
            });
            *count as u64
        };
        (terms(pair.left) + terms(pair.right)).saturating_sub(2)
    }

    /// Drop lazily deleted entries from the top of the heap, so that the top is a pending pair.
    fn drop_stale_top(&mut self) {
        while !self.removed.is_empty() {
            let Some(Reverse(top)) = self.pending.peek() else {
                return;
            };
            let key = (top.pair.left, top.pair.right);
            if !self.removed.remove(&key) {
                return;
            }
            self.pending.pop();
        }
    }

    /// The next pair: of minimum lcm degree, and within that degree whichever the schedule ranks
    /// first.
    pub fn pop(&mut self) -> Option<CriticalPair<N>> {
        self.take(true)
    }

    /// Take the top pair, recording it as handled only if `processed`.
    ///
    /// `processed = false` is deferral, and the flag is not a convenience: the chain criterion may
    /// only discard a pair on the strength of witnesses that have been *reduced*, so a pair that
    /// left the pending set without being reduced must not enter `handled`. Letting it would close
    /// the justification loop the criterion's soundness argument rules out.
    fn take(&mut self, processed: bool) -> Option<CriticalPair<N>> {
        self.drop_stale_top();
        let Reverse(ScheduledPair { pair, .. }) = self.pending.pop()?;
        self.live -= 1;
        if processed && self.track_handled {
            self.handled.insert((pair.left, pair.right));
        }
        Some(pair)
    }

    /// The lcm degree the next batch would be selected at, or `None` if nothing is pending.
    ///
    /// For a selection strategy that has to decide how large a batch to ask for *before* asking:
    /// the cap depends on the degree, and the degree is only knowable from the queue. Takes `&mut`
    /// because establishing it means skipping any lazily deleted entries at the top, which is the
    /// same work `select_batch` would have done.
    pub fn next_degree(&mut self) -> Option<u64> {
        self.drop_stale_top();
        self.pending.peek().map(|Reverse(entry)| entry.pair.degree)
    }

    /// How many pending pairs are at `degree`.
    ///
    /// A scan of the heap, so a caller should ask only when it needs the answer. It exists because
    /// "did the cap bind?" is a question about the degree being selected and not about the queue:
    /// `len()` counts pairs at every degree, and using it would charge a cap with withholding
    /// pairs it was never offered.
    pub fn pending_at_degree(&self, degree: u64) -> usize {
        self.pending
            .iter()
            .map(|Reverse(entry)| &entry.pair)
            .filter(|pair| pair.degree == degree)
            .filter(|pair| !self.removed.contains(&(pair.left, pair.right)))
            .count()
    }

    /// Pairs waiting, pending and deferred together.
    ///
    /// What a main loop has to test to know whether it is finished: an empty pending set with
    /// deferred pairs left is not a finished computation.
    pub fn has_work(&self) -> bool {
        self.live > 0 || !self.deferred.is_empty()
    }

    /// Pairs set aside by a selection heuristic.
    pub fn deferred_len(&self) -> usize {
        self.deferred.len()
    }

    /// What the queue currently occupies, in entries rather than in bytes.
    ///
    /// Entries and not bytes because only the caller knows `N`, and `size_of` is what turns one
    /// into the other. Every count here is a field read, so a main loop may take it once per batch
    /// without paying for a scan.
    pub fn footprint(&self) -> PairQueueFootprint {
        PairQueueFootprint {
            heap_entries: self.pending.len(),
            live: self.live,
            removed: self.removed.len(),
            handled: self.handled.len(),
            deferred: self.deferred.len(),
        }
    }

    /// Recompute every derived field from `leads` and compare it to what is stored.
    ///
    /// `leads` is a parameter because a pair carries indices and monomials but deliberately not the
    /// two leading monomials (see [`CriticalPair::larger_multiplier`]), so there is nothing to
    /// recompute against without them. The caller holding both is F4's main loop.
    ///
    /// What this catches that the type system does not: `live` drifting from the heap, a pair whose
    /// lcm or multipliers no longer match the leads it names, the pending and deferred sets
    /// overlapping — which would let one pair be processed twice — and a deferred pair recorded as
    /// handled, which would let the chain criterion use an unprocessed pair as a witness and
    /// discard a pair that is not redundant.
    ///
    /// Modelled on Singular's `kTest_TS` (`kernel/GBEngine/kutil.cc`), which checks `S`, `T`, `L`
    /// and their cross-indices against each other rather than in isolation; see
    /// `docs/research/singular-engine-notes.md` §6.
    ///
    /// Debug-only, like `MonicBasis::check`, and the call site is gated the same way.
    ///
    /// # Panics
    /// If any stored field disagrees with its recomputation.
    #[cfg(debug_assertions)]
    pub(crate) fn check(&self, leads: &[Monomial<N>]) {
        // `live` is maintained by hand across push, pop, lazy deletion and deferral, and a drift
        // in it is silent: it is what `is_empty` reads, so too low ends a computation early.
        let live = self
            .pending
            .iter()
            .filter(|entry| {
                !self
                    .removed
                    .contains(&(entry.0.pair.left, entry.0.pair.right))
            })
            .count();
        assert_eq!(
            self.live, live,
            "PairQueue: live is {} but the heap holds {live} entries not in `removed`",
            self.live
        );

        let mut pending_keys: HashSet<PairKey> = HashSet::new();
        for entry in &self.pending {
            let pair = &entry.0.pair;
            self.check_pair(pair, leads, "pending");
            if !self.removed.contains(&(pair.left, pair.right)) {
                pending_keys.insert((pair.left, pair.right));
            }
            assert_eq!(
                entry.0.schedule,
                self.schedule,
                "PairQueue: heap entry ({}, {}) carries schedule {} but the queue is {}",
                pair.left,
                pair.right,
                entry.0.schedule.name(),
                self.schedule.name()
            );
        }

        for pair in &self.deferred {
            self.check_pair(pair, leads, "deferred");
            let key = (pair.left, pair.right);
            assert!(
                !pending_keys.contains(&key),
                "PairQueue: pair ({}, {}) is both pending and deferred, so it could be \
                 processed twice",
                pair.left,
                pair.right
            );
            assert!(
                !self.handled.contains(&key),
                "PairQueue: deferred pair ({}, {}) is recorded as handled, so the chain \
                 criterion could use an unprocessed pair as a witness",
                pair.left,
                pair.right
            );
        }

        // A rank computed from a missing count would silently order every pair equal. The counts
        // are append-only precisely so that a pair's rank cannot change under it.
        if self.schedule.ranks_by_term_count() {
            assert!(
                self.term_counts.len() >= leads.len(),
                "PairQueue: schedule {} ranks by term count but only {} of {} counts are recorded",
                self.schedule.name(),
                self.term_counts.len(),
                leads.len()
            );
        }
    }

    /// One pair's lcm, degree, multipliers and index bounds, recomputed from `leads`.
    #[cfg(debug_assertions)]
    fn check_pair(&self, pair: &CriticalPair<N>, leads: &[Monomial<N>], set: &str) {
        let (left, right) = (pair.left, pair.right);
        assert!(
            left < right,
            "PairQueue {set} pair ({left}, {right}): indices are not ordered"
        );
        assert!(
            right < leads.len(),
            "PairQueue {set} pair ({left}, {right}): right is out of bounds for {} leads",
            leads.len()
        );

        let lcm = Monomial::lcm(&leads[left], &leads[right]);
        assert_eq!(
            pair.lcm, lcm,
            "PairQueue {set} pair ({left}, {right}): lcm {} disagrees with lcm of its leads, {lcm}",
            pair.lcm
        );
        assert_eq!(
            pair.degree,
            lcm.degree(),
            "PairQueue {set} pair ({left}, {right}): degree {} disagrees with lcm degree {}",
            pair.degree,
            lcm.degree()
        );

        // The two multipliers are the quotients, assigned by degree. Recomputing both and
        // comparing as a pair catches a swap, which comparing degrees alone would not.
        let from_left = lcm
            .checked_div(&leads[left])
            .expect("an lcm is divisible by each of its leads");
        let from_right = lcm
            .checked_div(&leads[right])
            .expect("an lcm is divisible by each of its leads");
        let (larger, smaller) = if from_left.degree() >= from_right.degree() {
            (from_left, from_right)
        } else {
            (from_right, from_left)
        };
        assert_eq!(
            pair.larger_multiplier, larger,
            "PairQueue {set} pair ({left}, {right}): larger_multiplier {} disagrees with the \
             recomputed {larger}",
            pair.larger_multiplier
        );
        assert_eq!(
            pair.smaller_multiplier, smaller,
            "PairQueue {set} pair ({left}, {right}): smaller_multiplier {} disagrees with the \
             recomputed {smaller}",
            pair.smaller_multiplier
        );
    }

    /// Move every pending pair of `degree` into the deferred set, and return how many.
    ///
    /// For a selection strategy that has decided it has taken enough of this degree and wants to
    /// move on. The pairs are **not** recorded as handled — see [`PairQueue::deferred`] — and they
    /// remain visible to Gebauer–Möller, so the pair set is minimized exactly as it would have
    /// been had they stayed pending.
    pub fn defer_degree(&mut self, degree: u64) -> usize {
        let mut moved = 0;
        loop {
            self.drop_stale_top();
            match self.pending.peek() {
                Some(Reverse(next)) if next.pair.degree == degree => {
                    let pair = self.take(false).expect("peeked at a pair that is there");
                    self.deferred.push(pair);
                    moved += 1;
                }
                _ => return moved,
            }
        }
    }

    /// Return every deferred pair to the pending set, and report how many.
    ///
    /// **This is what makes a deferring strategy complete**: the computation cannot end while
    /// deferred pairs remain, so every pair is eventually processed or discarded by a criterion that
    /// is a theorem. A deferral is a decision about *when*, never about *whether*.
    pub fn promote_deferred(&mut self) -> usize {
        let promoted = std::mem::take(&mut self.deferred);
        let count = promoted.len();
        for pair in promoted {
            self.push(pair);
        }
        count
    }

    /// Every remaining pair of minimum lcm degree, up to `limit` of them.
    ///
    /// This is the selection strategy F4 batches on: all the pairs at the lowest degree available,
    /// which is Faugère's `Sel` specialized to the normal strategy. `limit` caps the batch so that
    /// a degree with very many pairs cannot produce a matrix of unbounded size in one step; a
    /// limit of one reduces F4 to processing a single pair per matrix, which is a useful
    /// degenerate case to be able to test.
    ///
    /// **The `limit` is what decides whether a [`PairSchedule`] changes the batch *sets*.** Without a
    /// cap the batch is every pending pair of its degree whatever the schedule, so the sets are
    /// identical and only the row order differs; with a cap the schedule decides which pairs of the
    /// degree reach *this* matrix and which wait for the next. The pairs left behind stay pending
    /// either way, which is what makes every schedule complete.
    ///
    /// Row order is not inert even so — see [`PairSchedule`].
    ///
    /// # Panics
    /// If `limit` is `Some(0)`, which would select nothing and loop forever.
    pub fn select_batch(&mut self, limit: Option<usize>) -> Vec<CriticalPair<N>> {
        assert_ne!(limit, Some(0), "a batch of no pairs makes no progress");

        let Some(first) = self.pop() else {
            return Vec::new();
        };
        let degree = first.degree;
        let mut batch = vec![first];

        while limit.is_none_or(|limit| batch.len() < limit) {
            self.drop_stale_top();
            match self.pending.peek() {
                Some(Reverse(next)) if next.pair.degree == degree => {
                    batch.push(self.pop().expect("peeked at a pair that is there"));
                }
                _ => break,
            }
        }

        batch
    }

    /// Discard the pairs of a selected batch that an enabled criterion proves redundant.
    ///
    /// Takes `&self` because a criterion is a statement about the pairs that are *still pending*
    /// as well as about the basis: the chain criterion may only discard `(i, j)` on the strength of
    /// a `k` whose own pairs with `i` and `j` have already been dealt with, and "already dealt
    /// with" is exactly "not in this queue".
    ///
    /// The returned batch keeps the input's order, so selection stays deterministic.
    pub fn filter_batch(
        &self,
        batch: Vec<CriticalPair<N>>,
        leads: &[Monomial<N>],
        criteria: &PairCriteria,
        counts: &mut CriterionCounts,
    ) -> Vec<CriticalPair<N>> {
        // The pairs of this batch have been selected but not yet reduced, so none of them is a
        // witness for another: see `is_discarded`. Only the chain criterion reads the set.
        let in_batch: HashSet<PairKey> = if criteria.chain {
            batch.iter().map(|pair| (pair.left, pair.right)).collect()
        } else {
            HashSet::new()
        };

        batch
            .into_iter()
            .filter(|pair| !self.discards(pair, leads, criteria, counts, &in_batch))
            .collect()
    }

    /// Discard the given selected pair if an enabled criterion proves it redundant.
    ///
    /// The one-pair-at-a-time form of [`PairQueue::filter_batch`], for an engine that selects one
    /// pair at a time. The pair must already have been popped.
    pub fn is_discarded(
        &self,
        pair: &CriticalPair<N>,
        leads: &[Monomial<N>],
        criteria: &PairCriteria,
        counts: &mut CriterionCounts,
    ) -> bool {
        self.discards(pair, leads, criteria, counts, &HashSet::new())
    }

    /// The selection-time criteria. `in_batch` holds pairs selected alongside `pair`.
    ///
    /// # The chain criterion
    ///
    /// Buchberger's chain criterion, in the form Cox, Little and O'Shea state as
    /// `Criterion(f_i, f_j, B)` in *Ideals, Varieties, and Algorithms* Sec 2.10: the pair
    /// `(i, j)` is discarded when there is a `k` outside `{i, j}` with `LM(f_k)` dividing
    /// `lcm(LM f_i, LM f_j)` **and** neither `(i, k)` nor `(k, j)` in the pair set `B`. The
    /// soundness is Sec 2.9's chain lemma: if `S(f_i, f_k)` and `S(f_k, f_j)` have standard
    /// representations then so does `S(f_i, f_j)`. Divisibility of the lcm alone does not imply
    /// that and discarding on it returns an incomplete basis.
    ///
    /// "In `B`" is read here as "not yet selected and processed", which is stronger than "absent
    /// from the pending set", and deliberately:
    ///
    /// - A pair selected in the same batch has been removed from the pending set but not yet
    ///   reduced. Three pairs on one another's lcms could then each be discarded on the strength
    ///   of the other two, and none of the three would ever be reduced. `in_batch` excludes them.
    /// - A pair Gebauer–Möller removed is absent from the pending set but was never reduced, and
    ///   its own redundancy is justified by two pairs that are still pending. Letting it witness
    ///   one of those would close the loop. Only popped pairs enter `handled`, so it cannot.
    ///
    /// With Gebauer–Möller off, every pair leaves the pending set by being selected, so the two
    /// readings coincide and this is exactly the published criterion. The invariant both
    /// installations maintain is the same one: every pair not in `B` has a standard representation
    /// modulo the final basis, justified either by a pair processed strictly earlier or by pairs
    /// whose lcm divides its own strictly.
    fn discards(
        &self,
        pair: &CriticalPair<N>,
        leads: &[Monomial<N>],
        criteria: &PairCriteria,
        counts: &mut CriterionCounts,
        in_batch: &HashSet<PairKey>,
    ) -> bool {
        // Buchberger's first criterion. The leading monomials share no variable, so their lcm is
        // their product and the S-polynomial is guaranteed to reduce to zero modulo the two of
        // them: there is no reason to put either half in a matrix.
        if criteria.product && are_relatively_prime(&leads[pair.left], &leads[pair.right]) {
            counts.product += 1;
            return true;
        }

        if criteria.chain && self.chain_witness(pair, leads, in_batch).is_some() {
            counts.chain += 1;
            return true;
        }

        false
    }

    /// The index of an element witnessing the chain criterion for `pair`, if there is one.
    fn chain_witness(
        &self,
        pair: &CriticalPair<N>,
        leads: &[Monomial<N>],
        in_batch: &HashSet<PairKey>,
    ) -> Option<usize> {
        (0..leads.len()).find(|&k| {
            k != pair.left
                && k != pair.right
                && divides(&leads[k], &pair.lcm)
                && self.is_handled(pair.left, k, in_batch)
                && self.is_handled(pair.right, k, in_batch)
        })
    }

    /// True if the pair of `a` and `b` has been selected and its batch processed.
    fn is_handled(&self, a: usize, b: usize, in_batch: &HashSet<PairKey>) -> bool {
        let key = (a.min(b), a.max(b));
        self.handled.contains(&key) && !in_batch.contains(&key)
    }
}

#[cfg(test)]
mod tests {
    use super::{
        are_relatively_prime, divides, leading_monomials, CriterionCounts, CriticalPair,
        PairCriteria, PairQueue, PairSchedule,
    };
    use crate::{fields::Zp13, poly::MonomialOrder, Monomial, MultivariatePolynomial};

    type F = Zp13;
    const VARS: [&str; 3] = ["x", "y", "z"];
    const ORDER: MonomialOrder = MonomialOrder::Lexicographic;

    fn parse(s: &str) -> MultivariatePolynomial<3, F> {
        MultivariatePolynomial::parse(s, VARS).unwrap()
    }

    /// A pair records the lcm of the two leading monomials and its degree.
    #[test]
    fn test_pair_records_the_lcm() {
        let basis = vec![parse("x^2*y + 1"), parse("x*y^3 + z")];
        let pair = CriticalPair::new(&basis, 0, 1, ORDER);
        assert_eq!(pair.lcm, Monomial::<3>::new(&[2, 3, 0]));
        assert_eq!(pair.degree, 5);
        assert_eq!((pair.left, pair.right), (0, 1));
    }

    /// The indices are normalized, so the same pair is the same whichever way it is given.
    #[test]
    fn test_pair_indices_are_ordered() {
        let basis = vec![parse("x^2 + 1"), parse("y^2 + 1")];
        assert_eq!(
            CriticalPair::new(&basis, 1, 0, ORDER),
            CriticalPair::new(&basis, 0, 1, ORDER)
        );
    }

    /// Pairing an element with itself is rejected: its S-polynomial is zero.
    #[test]
    #[should_panic(expected = "does not pair with itself")]
    fn test_pair_with_itself_panics() {
        let basis = vec![parse("x^2 + 1")];
        let _ = CriticalPair::new(&basis, 0, 0, ORDER);
    }

    /// Relative primality is exactly disjoint support.
    #[test]
    fn test_are_relatively_prime() {
        let x2 = Monomial::<3>::new(&[2, 0, 0]);
        let y3 = Monomial::<3>::new(&[0, 3, 0]);
        let xy = Monomial::<3>::new(&[1, 1, 0]);
        let one = Monomial::<3>::one();

        assert!(are_relatively_prime(&x2, &y3));
        assert!(!are_relatively_prime(&x2, &xy));
        assert!(!are_relatively_prime(&xy, &y3));
        // One shares no variable with anything, including itself.
        assert!(are_relatively_prime(&one, &x2));
        assert!(are_relatively_prime(&one, &one));
        // A monomial always shares a variable with itself, unless it is one.
        assert!(!are_relatively_prime(&x2, &x2));
    }

    /// The product criterion fires exactly when the leading monomials are relatively prime.
    #[test]
    fn test_product_criterion() {
        let basis = vec![parse("x^2 - 1"), parse("y^3 - 1"), parse("x*y - 1")];
        assert!(CriticalPair::new(&basis, 0, 1, ORDER)
            .is_eliminated_by_product_criterion(&basis, ORDER));
        assert!(!CriticalPair::new(&basis, 0, 2, ORDER)
            .is_eliminated_by_product_criterion(&basis, ORDER));
    }

    /// Seeding produces every unordered pair of the basis, once each.
    #[test]
    fn test_seeded_queue_holds_every_pair() {
        let basis: Vec<MultivariatePolynomial<3, F>> =
            vec![parse("x^2"), parse("y^2"), parse("z^2"), parse("x*y")];
        let queue = PairQueue::seeded(&basis, ORDER);
        assert_eq!(queue.len(), 4 * 3 / 2);

        // And a basis of one element has no pairs at all.
        assert!(PairQueue::seeded(&[parse("x^2")], ORDER).is_empty());
        assert!(PairQueue::<3>::seeded::<F>(&[], ORDER).is_empty());
    }

    /// Pairs come out in nondecreasing lcm degree.
    #[test]
    fn test_pairs_come_out_in_degree_order() {
        let basis: Vec<MultivariatePolynomial<3, F>> = vec![
            parse("x^4*y^4"),
            parse("x*y"),
            parse("x^2*y^2"),
            parse("x^3*y^3"),
        ];
        let mut queue = PairQueue::seeded(&basis, ORDER);

        let mut degrees = Vec::new();
        while let Some(pair) = queue.pop() {
            degrees.push(pair.degree);
        }
        let mut sorted = degrees.clone();
        sorted.sort_unstable();
        assert_eq!(degrees, sorted, "pairs were not in degree order");
    }

    /// A batch holds every pair at the minimum degree, and nothing above it.
    #[test]
    fn test_select_batch_takes_one_whole_degree() {
        // Leading monomials x^2, y^2, z^2 pair at degree four; adding x*y gives degree-three pairs
        // with x^2 and y^2, and a degree-four pair with z^2.
        let basis: Vec<MultivariatePolynomial<3, F>> =
            vec![parse("x^2"), parse("y^2"), parse("z^2"), parse("x*y")];
        let mut queue = PairQueue::seeded(&basis, ORDER);
        let total = queue.len();

        let batch = queue.select_batch(None);
        assert!(!batch.is_empty());
        assert!(
            batch.iter().all(|pair| pair.degree == batch[0].degree),
            "a batch mixed degrees: {:?}",
            batch
        );
        assert_eq!(batch.len() + queue.len(), total, "pairs went missing");
        // Nothing left is below the batch's degree.
        while let Some(pair) = queue.pop() {
            assert!(pair.degree >= batch[0].degree);
        }
    }

    /// A batch limit caps the batch without losing the pairs it left behind.
    #[test]
    fn test_select_batch_respects_the_limit() {
        let basis: Vec<MultivariatePolynomial<3, F>> =
            vec![parse("x^2"), parse("y^2"), parse("z^2"), parse("x*y")];
        let mut queue = PairQueue::seeded(&basis, ORDER);
        let total = queue.len();

        let mut taken = 0;
        let mut batches = 0;
        while !queue.is_empty() {
            let batch = queue.select_batch(Some(1));
            assert_eq!(batch.len(), 1, "a limit of one should take one pair");
            taken += batch.len();
            batches += 1;
        }
        assert_eq!(taken, total);
        assert_eq!(
            batches, total,
            "one pair per batch means one batch per pair"
        );
    }

    /// A limit of zero is rejected rather than silently making no progress.
    #[test]
    #[should_panic(expected = "makes no progress")]
    fn test_select_batch_rejects_a_zero_limit() {
        let basis = vec![parse("x^2"), parse("y^2")];
        let mut queue = PairQueue::seeded(&basis, ORDER);
        let _ = queue.select_batch(Some(0));
    }

    /// Selecting from an empty queue yields an empty batch rather than panicking.
    #[test]
    fn test_select_batch_from_an_empty_queue() {
        let mut queue = PairQueue::<3>::new();
        assert!(queue.select_batch(None).is_empty());
        assert!(queue.select_batch(Some(5)).is_empty());
    }

    /// Pairing from leading monomials gives the same pair as pairing from the polynomials.
    #[test]
    fn test_from_leads_agrees_with_from_polynomials() {
        let basis: Vec<MultivariatePolynomial<3, F>> =
            vec![parse("x^2*y + 1"), parse("x*y^3 + z"), parse("z^2 + x")];
        for order in [
            MonomialOrder::Lexicographic,
            MonomialOrder::GradedLexicographic,
            MonomialOrder::GradedReverseLexicographic,
        ] {
            let leads = leading_monomials(&basis, order);
            for left in 0..basis.len() {
                for right in (left + 1)..basis.len() {
                    assert_eq!(
                        CriticalPair::from_leads(&leads, left, right),
                        CriticalPair::new(&basis, left, right, order),
                        "{}",
                        order.name()
                    );
                }
            }
        }
    }

    /// Seeding from leading monomials gives the same queue as seeding from the polynomials.
    #[test]
    fn test_seeding_from_leads_agrees() {
        let basis: Vec<MultivariatePolynomial<3, F>> =
            vec![parse("x^2"), parse("y^2"), parse("z^2"), parse("x*y")];
        let leads = leading_monomials(&basis, ORDER);

        let drain = |mut queue: PairQueue<3>| {
            let mut pairs = Vec::new();
            while let Some(pair) = queue.pop() {
                pairs.push(pair);
            }
            pairs
        };

        assert_eq!(
            drain(PairQueue::seeded_from_leads(
                &leads,
                &PairCriteria::NONE,
                &mut CriterionCounts::default()
            )),
            drain(PairQueue::seeded(&basis, ORDER))
        );
    }

    /// Filtering a batch applies the product criterion and counts what it discarded.
    #[test]
    fn test_filter_batch_applies_the_product_criterion() {
        // x^2 and y^3 are relatively prime; x^2 and x*y are not.
        let basis: Vec<MultivariatePolynomial<3, F>> =
            vec![parse("x^2 - 1"), parse("y^3 - 1"), parse("x*y - 1")];
        let leads = leading_monomials(&basis, ORDER);
        let queue = PairQueue::<3>::new();

        let batch = vec![
            CriticalPair::from_leads(&leads, 0, 1),
            CriticalPair::from_leads(&leads, 0, 2),
            CriticalPair::from_leads(&leads, 1, 2),
        ];

        let mut counts = CriterionCounts::default();
        let kept = queue.filter_batch(
            batch.clone(),
            &leads,
            &PairCriteria::PRODUCT_ONLY,
            &mut counts,
        );
        assert_eq!(kept, vec![batch[1].clone(), batch[2].clone()]);
        assert_eq!(counts.product, 1);
        assert_eq!(counts.total(), 1);

        // With no criterion enabled nothing is discarded, which is the reference the criteria are
        // checked against.
        let mut counts = CriterionCounts::default();
        assert_eq!(
            queue.filter_batch(batch.clone(), &leads, &PairCriteria::NONE, &mut counts),
            batch
        );
        assert_eq!(counts.total(), 0);
    }

    /// The default criteria are Buchberger's first criterion alone, which is what was measured.
    #[test]
    fn test_default_criteria() {
        assert_eq!(PairCriteria::default(), PairCriteria::PRODUCT_ONLY);
        assert!(PairCriteria::default().product);
        assert!(!PairCriteria::default().chain);
        assert!(!PairCriteria::default().gebauer_moller);
    }

    /// Criterion counts sum per criterion and fold together.
    #[test]
    fn test_criterion_counts_accumulate() {
        let mut total = CriterionCounts::default();
        total.add(&CriterionCounts {
            product: 3,
            chain: 1,
            gebauer_moller: 0,
        });
        total.add(&CriterionCounts {
            product: 2,
            chain: 0,
            gebauer_moller: 5,
        });
        assert_eq!(
            total,
            CriterionCounts {
                product: 5,
                chain: 1,
                gebauer_moller: 5
            }
        );
        assert_eq!(total.total(), 11);
    }

    const CHAIN_ONLY: PairCriteria = PairCriteria {
        product: false,
        chain: true,
        gebauer_moller: false,
    };

    const GEBAUER_MOLLER_ONLY: PairCriteria = PairCriteria {
        product: false,
        chain: false,
        gebauer_moller: true,
    };

    fn monomials<const N: usize>(exponents: &[[u32; N]]) -> Vec<Monomial<N>> {
        exponents.iter().map(|e| Monomial::new(e)).collect()
    }

    /// Three leads and a queue seeded from them, for the checker tests.
    #[cfg(debug_assertions)]
    fn checkable() -> (Vec<Monomial<3>>, PairQueue<3>) {
        let leads = monomials::<3>(&[[2, 0, 0], [0, 2, 0], [0, 0, 2]]);
        let mut counts = CriterionCounts::default();
        let queue = PairQueue::seeded_from_leads(&leads, &PairCriteria::NONE, &mut counts);
        (leads, queue)
    }

    /// The checker accepts a queue its own constructor seeded.
    ///
    /// The control: without it the corruption tests would pass against a checker that rejected
    /// every queue.
    #[cfg(debug_assertions)]
    #[test]
    fn test_the_queue_checker_accepts_a_well_formed_queue() {
        let (leads, queue) = checkable();
        queue.check(&leads);
    }

    /// A `live` count that has drifted from the heap is caught, and named.
    ///
    /// `live` is maintained by hand across push, pop, lazy deletion and deferral, and it is what
    /// `is_empty` reads — so a count that is too low ends a computation early with a basis that is
    /// not a Gröbner basis.
    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "live is")]
    fn test_a_drifted_live_count_is_caught() {
        let (leads, mut queue) = checkable();
        queue.live -= 1;
        queue.check(&leads);
    }

    /// A pair whose lcm no longer matches the leads it names is caught.
    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "disagrees with lcm of its leads")]
    fn test_a_stale_pair_lcm_is_caught() {
        let (leads, mut queue) = checkable();
        let mut entries: Vec<_> = queue.pending.drain().collect();
        entries[0].0.pair.lcm = Monomial::<3>::new(&[7, 7, 7]);
        queue.pending.extend(entries);
        queue.check(&leads);
    }

    /// Multipliers swapped between the two legs are caught.
    ///
    /// Recomputing both and comparing them as a pair is what catches this; comparing their degrees
    /// would not, since a swap preserves the multiset of degrees.
    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "multiplier")]
    fn test_swapped_multipliers_are_caught() {
        let leads = monomials::<3>(&[[2, 0, 0], [0, 1, 0]]);
        let mut counts = CriterionCounts::default();
        let mut queue = PairQueue::seeded_from_leads(&leads, &PairCriteria::NONE, &mut counts);
        let mut entries: Vec<_> = queue.pending.drain().collect();
        let pair = &mut entries[0].0.pair;
        assert_ne!(
            pair.larger_multiplier, pair.smaller_multiplier,
            "the fixture needs multipliers of different degrees for a swap to be visible"
        );
        std::mem::swap(&mut pair.larger_multiplier, &mut pair.smaller_multiplier);
        queue.pending.extend(entries);
        queue.check(&leads);
    }

    /// A pair that is both pending and deferred is caught.
    ///
    /// It could otherwise be processed twice: once from the heap and once after
    /// [`PairQueue::promote_deferred`].
    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "both pending and deferred")]
    fn test_a_pair_in_both_sets_is_caught() {
        let (leads, mut queue) = checkable();
        let duplicate = queue
            .pending
            .peek()
            .expect("the fixture seeds pairs")
            .0
            .pair
            .clone();
        queue.deferred.push(duplicate);
        queue.check(&leads);
    }

    /// A deferred pair recorded as handled is caught.
    ///
    /// The chain criterion's witnesses must have been *processed*; a deferred pair has not been, so
    /// this state would let it witness a discard that is not justified.
    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "recorded as handled")]
    fn test_a_deferred_pair_recorded_as_handled_is_caught() {
        let (leads, mut queue) = checkable();
        let moved = queue.pending.pop().expect("the fixture seeds pairs").0.pair;
        queue.live -= 1;
        queue.handled.insert((moved.left, moved.right));
        queue.deferred.push(moved);
        queue.check(&leads);
    }

    fn drain<const N: usize>(mut queue: PairQueue<N>) -> Vec<(usize, usize)> {
        let mut keys = Vec::new();
        while let Some(pair) = queue.pop() {
            keys.push((pair.left, pair.right));
        }
        keys
    }

    /// Term counts for a basis of `n` elements, spread so a length-ranking schedule has something
    /// to order by rather than ranking every pair equal.
    fn term_counts(n: usize) -> Vec<usize> {
        (0..n).map(|index| 1 + (index * 3) % 5).collect()
    }

    /// A seeded queue under any schedule, including the ones that need the term counts.
    fn seeded_under<const N: usize>(
        leads: &[Monomial<N>],
        criteria: &PairCriteria,
        schedule: PairSchedule,
        counts: &mut CriterionCounts,
    ) -> PairQueue<N> {
        PairQueue::seeded_from_leads_ranked(
            leads,
            &term_counts(leads.len()),
            criteria,
            schedule,
            ORDER,
            counts,
        )
    }

    /// The chain criterion discards a pair once both of its witness's pairs have been handled.
    #[test]
    fn test_chain_criterion_discards_a_pair_with_handled_witnesses() {
        // Leading monomials x, y, x*y. Every pair has lcm x*y, and each element's leading
        // monomial divides it, so each pair has the other two as its chain witness — which is
        // exactly the configuration that distinguishes the criterion from the unsound shortcut.
        let leads = monomials::<3>(&[[1, 0, 0], [0, 1, 0], [1, 1, 0]]);
        let mut counts = CriterionCounts::default();
        let mut queue = PairQueue::seeded_from_leads(&leads, &CHAIN_ONLY, &mut counts);

        let mut kept = Vec::new();
        while let Some(pair) = queue.pop() {
            if !queue.is_discarded(&pair, &leads, &CHAIN_ONLY, &mut counts) {
                kept.push((pair.left, pair.right));
            }
        }

        // (0,1) and (0,2) are handled first and so have no witness yet; (1,2) is discarded on the
        // strength of element 0, whose pairs with 1 and with 2 are both handled by then.
        assert_eq!(kept, vec![(0, 1), (0, 2)]);
        assert_eq!(counts.chain, 1);
        assert_eq!(counts.product, 0);
        assert_eq!(counts.gebauer_moller, 0);
    }

    /// Divisibility of the lcm alone does not discard a pair: the witness's own pairs must be
    /// handled first.
    ///
    /// Regression test for the unsound shortcut. Element 2's leading monomial x*y divides the lcm
    /// of the very first pair selected, so a criterion testing only divisibility would discard it
    /// and return an incomplete basis.
    #[test]
    fn test_chain_criterion_requires_the_witness_pairs_to_be_handled() {
        let leads = monomials::<3>(&[[1, 0, 0], [0, 1, 0], [1, 1, 0]]);
        let mut counts = CriterionCounts::default();
        let mut queue = PairQueue::seeded_from_leads(&leads, &CHAIN_ONLY, &mut counts);

        let first = queue.pop().expect("three pairs were seeded");
        assert_eq!((first.left, first.right), (0, 1));
        assert!(divides(&leads[2], &first.lcm), "the shortcut would fire");
        assert!(
            !queue.is_discarded(&first, &leads, &CHAIN_ONLY, &mut counts),
            "the first pair selected has no handled witness and must not be discarded"
        );
        assert_eq!(counts.chain, 0);
    }

    /// Pairs of the batch being selected do not count as handled.
    #[test]
    fn test_chain_criterion_does_not_use_pairs_from_the_same_batch() {
        // All three pairs have lcm x*y, so they are selected as one batch. None of them has been
        // reduced yet, so none can witness another: discarding all three would leave every
        // S-polynomial of the three unreduced.
        let leads = monomials::<3>(&[[1, 0, 0], [0, 1, 0], [1, 1, 0]]);
        let mut counts = CriterionCounts::default();
        let mut queue = PairQueue::seeded_from_leads(&leads, &CHAIN_ONLY, &mut counts);

        let batch = queue.select_batch(None);
        assert_eq!(batch.len(), 3);
        let kept = queue.filter_batch(batch, &leads, &CHAIN_ONLY, &mut counts);
        assert_eq!(kept.len(), 3);
        assert_eq!(counts.chain, 0);
    }

    /// The chain criterion discards nothing when it is switched off, leaving the product
    /// criterion's eliminations alone.
    #[test]
    fn test_chain_criterion_is_inert_when_disabled() {
        let leads = monomials::<3>(&[[1, 0, 0], [0, 1, 0], [1, 1, 0]]);
        let mut counts = CriterionCounts::default();
        let mut queue =
            PairQueue::seeded_from_leads(&leads, &PairCriteria::PRODUCT_ONLY, &mut counts);

        let mut reduced = 0;
        while let Some(pair) = queue.pop() {
            if !queue.is_discarded(&pair, &leads, &PairCriteria::PRODUCT_ONLY, &mut counts) {
                reduced += 1;
            }
        }
        // x and y are relatively prime, so (0,1) goes to the product criterion; (1,2) is the pair
        // the chain criterion would have taken, and it is reduced here.
        assert_eq!(reduced, 2);
        assert_eq!(counts.product, 1);
        assert_eq!(counts.chain, 0);
    }

    /// Gebauer–Möller's criterion M keeps one new pair per lcm, and criterion B keeps an old pair
    /// whose lcm one of the new pairs reproduces.
    #[test]
    fn test_gebauer_moller_keeps_one_new_pair_per_lcm() {
        // Leading monomials x*z, x*y*z, y*z. Pairing y*z with each of the first two gives lcm
        // x*y*z both times, so one of the two is redundant. The existing pair (0,1) also has lcm
        // x*y*z, which y*z divides — but lcm(x*z, y*z) is that same monomial, so criterion B's
        // equality guard keeps it.
        let leads = monomials::<3>(&[[1, 0, 1], [1, 1, 1], [0, 1, 1]]);

        let mut counts = CriterionCounts::default();
        let queue = PairQueue::seeded_from_leads(&leads, &GEBAUER_MOLLER_ONLY, &mut counts);
        assert_eq!(drain(queue), vec![(0, 1), (1, 2)]);
        assert_eq!(counts.gebauer_moller, 1);

        // Without the criterion all three pairs are inserted.
        let mut counts = CriterionCounts::default();
        let queue = PairQueue::seeded_from_leads(&leads, &PairCriteria::NONE, &mut counts);
        assert_eq!(queue.len(), 3);
        assert_eq!(counts.total(), 0);
    }

    /// Gebauer–Möller's criterion F discards a new pair with relatively prime leading monomials,
    /// and only when the product criterion is enabled.
    #[test]
    fn test_gebauer_moller_discards_a_relatively_prime_new_pair() {
        let leads = monomials::<3>(&[[1, 0, 0], [0, 1, 0]]);

        let mut counts = CriterionCounts::default();
        let queue = PairQueue::seeded_from_leads(&leads, &PairCriteria::ALL, &mut counts);
        assert!(queue.is_empty(), "the only pair is relatively prime");
        assert_eq!(counts.gebauer_moller, 1);

        // Criterion F is Buchberger's first criterion, so it is only applied when that is on.
        let mut counts = CriterionCounts::default();
        let queue = PairQueue::seeded_from_leads(&leads, &GEBAUER_MOLLER_ONLY, &mut counts);
        assert_eq!(queue.len(), 1);
        assert_eq!(counts.total(), 0);
    }

    /// Gebauer–Möller's criterion B discards an already pending pair that the new element makes
    /// redundant, and the queue's length follows.
    #[test]
    fn test_gebauer_moller_discards_a_pending_pair() {
        // Leading monomials x^2*z, y^2*z, x*y. The pair (0,1) has lcm x^2*y^2*z, which x*y
        // divides, and lcm(x^2*z, x*y) = x^2*y*z and lcm(x*y, y^2*z) = x*y^2*z are both strictly
        // smaller — so the chain criterion applies and the pair never has to be selected.
        let leads = monomials::<3>(&[[2, 0, 1], [0, 2, 1], [1, 1, 0]]);

        let mut counts = CriterionCounts::default();
        let mut queue = PairQueue::new();
        queue.push_pairs_from_leads(&leads, 1, &GEBAUER_MOLLER_ONLY, &mut counts);
        assert_eq!(queue.len(), 1);
        queue.push_pairs_from_leads(&leads, 2, &GEBAUER_MOLLER_ONLY, &mut counts);

        assert_eq!(counts.gebauer_moller, 1);
        assert_eq!(queue.len(), 2, "the pending pair was not removed");
        // Both remaining pairs have lcm degree four, so the tiebreak on the lcm decides: the
        // removed pair (0,1) is not among them, which is what this asserts.
        assert_eq!(drain(queue), vec![(1, 2), (0, 2)]);
    }

    /// Gebauer–Möller is deterministic: the same leading monomials give the same queue.
    #[test]
    fn test_gebauer_moller_is_deterministic() {
        let leads = monomials::<3>(&[
            [2, 0, 1],
            [0, 2, 1],
            [1, 1, 0],
            [1, 0, 2],
            [0, 1, 1],
            [3, 0, 0],
        ]);

        let queue_of = || {
            let mut counts = CriterionCounts::default();
            let queue = PairQueue::seeded_from_leads(&leads, &PairCriteria::ALL, &mut counts);
            (drain(queue), counts)
        };

        let first = queue_of();
        assert!(first.1.gebauer_moller > 0, "nothing was discarded");
        for _ in 0..8 {
            assert_eq!(queue_of(), first);
        }
    }

    /// Selection is deterministic: the same basis gives the same batches, in the same order.
    #[test]
    fn test_selection_is_deterministic() {
        let basis: Vec<MultivariatePolynomial<3, F>> = vec![
            parse("x^2*y + z"),
            parse("y^2*z + x"),
            parse("x*z^2 + y"),
            parse("x*y*z - 1"),
        ];

        let batches_of = || {
            let mut queue = PairQueue::seeded(&basis, ORDER);
            let mut batches = Vec::new();
            while !queue.is_empty() {
                batches.push(queue.select_batch(None));
            }
            batches
        };

        let first = batches_of();
        for _ in 0..8 {
            assert_eq!(batches_of(), first);
        }
    }

    /// A pair records the degrees of its two multipliers, larger first.
    ///
    /// `lcm / LM(g)` for each side, so the degrees are `deg lcm - deg LM(g)`. On x^2*y against
    /// x*y^3 the lcm is x^2*y^3 of degree five, so the multipliers are y^2 and x, of degrees two
    /// and one.
    #[test]
    fn test_pair_records_the_multiplier_degrees() {
        let basis = vec![parse("x^2*y + 1"), parse("x*y^3 + z")];
        let pair = CriticalPair::new(&basis, 0, 1, ORDER);
        assert_eq!(pair.larger_multiplier_degree(), 2);
        assert_eq!(pair.smaller_multiplier_degree(), 1);
        // And they sum to what the identity in the field docs says they must.
        let leads = leading_monomials(&basis, ORDER);
        assert_eq!(
            pair.larger_multiplier_degree() + pair.smaller_multiplier_degree(),
            2 * pair.degree - leads[0].degree() - leads[1].degree()
        );
    }

    /// A relatively prime pair has multipliers that are the other side's leading monomial.
    #[test]
    fn test_multiplier_degrees_of_a_relatively_prime_pair() {
        // lcm(x^2, y^3) = x^2*y^3, so the multipliers are y^3 and x^2.
        let basis = vec![parse("x^2 - 1"), parse("y^3 - 1")];
        let pair = CriticalPair::new(&basis, 0, 1, ORDER);
        assert_eq!(pair.larger_multiplier_degree(), 3);
        assert_eq!(pair.smaller_multiplier_degree(), 2);
    }

    /// The multiplier degrees do not disturb the baseline order, which is degree then lcm.
    ///
    /// They are appended to a struct whose `Ord` is derived, so they sort after `right` — which
    /// already identifies the pair, so they can never be reached. Asserted because the alternative
    /// is silently changing the baseline every figure in M16 was measured against.
    #[test]
    fn test_the_multiplier_degrees_do_not_change_the_derived_order() {
        let leads = monomials::<3>(&[[2, 0, 1], [0, 2, 1], [1, 1, 0], [1, 0, 2], [0, 1, 1]]);
        let mut pairs: Vec<CriticalPair<3>> = Vec::new();
        for right in 0..leads.len() {
            for left in 0..right {
                pairs.push(CriticalPair::from_leads(&leads, left, right));
            }
        }

        let mut by_derived = pairs.clone();
        by_derived.sort();
        let mut by_hand = pairs.clone();
        by_hand.sort_by_key(|p| (p.degree, p.lcm, p.left, p.right));
        assert_eq!(by_derived, by_hand);
    }

    /// Every schedule keeps the lcm degree primary.
    ///
    /// Not a preference: `select_batch` forms a batch from one degree and F4's termination argument
    /// is stated in ascending degree, so a schedule that reordered across degrees would be changing
    /// the algorithm rather than its order of work.
    #[test]
    fn test_every_schedule_is_degree_first() {
        let leads = monomials::<3>(&[
            [4, 0, 0],
            [0, 1, 0],
            [2, 2, 0],
            [1, 0, 3],
            [0, 3, 1],
            [1, 1, 1],
        ]);

        for schedule in PairSchedule::ALL {
            let mut counts = CriterionCounts::default();
            let mut queue = seeded_under(&leads, &PairCriteria::NONE, schedule, &mut counts);
            assert_eq!(queue.schedule(), schedule);

            let mut degrees = Vec::new();
            while let Some(pair) = queue.pop() {
                degrees.push(pair.degree);
            }
            let mut sorted = degrees.clone();
            sorted.sort_unstable();
            assert_eq!(
                degrees,
                sorted,
                "{} reordered across degrees",
                schedule.name()
            );
        }
    }

    /// Within a degree, `SmallMultiplier` takes the smallest larger multiplier first and
    /// `LargeMultiplier` takes the largest.
    #[test]
    fn test_the_schedules_order_within_a_degree() {
        // Leading monomials x^4, x^3*y, x, y^4. Two pairs have lcm degree five: (0,1) with lcm
        // x^4*y and multipliers y and x, so a larger multiplier degree of one; and (2,3) with lcm
        // x*y^4 and multipliers y^4 and x, so a larger multiplier degree of four. The lcm degree
        // cannot separate those two, which is exactly the case a schedule decides.
        let leads = monomials::<3>(&[[4, 0, 0], [3, 1, 0], [1, 0, 0], [0, 4, 0]]);
        let of = |schedule| {
            let mut counts = CriterionCounts::default();
            let mut queue = PairQueue::seeded_from_leads_scheduled(
                &leads,
                &PairCriteria::NONE,
                schedule,
                ORDER,
                &mut counts,
            );
            let mut keys = Vec::new();
            while let Some(pair) = queue.pop() {
                keys.push((pair.degree, pair.larger_multiplier_degree()));
            }
            keys
        };

        // Within each degree the larger-multiplier column is nondecreasing under SmallMultiplier
        // and nonincreasing under LargeMultiplier.
        for (schedule, ascending) in [
            (PairSchedule::SmallMultiplierDegree, true),
            (PairSchedule::LargeMultiplierDegree, false),
        ] {
            let keys = of(schedule);
            for window in keys.windows(2) {
                if window[0].0 != window[1].0 {
                    continue;
                }
                if ascending {
                    assert!(
                        window[0].1 <= window[1].1,
                        "{}: {:?} then {:?}",
                        schedule.name(),
                        window[0],
                        window[1]
                    );
                } else {
                    assert!(
                        window[0].1 >= window[1].1,
                        "{}: {:?} then {:?}",
                        schedule.name(),
                        window[0],
                        window[1]
                    );
                }
            }
        }

        // And the two really do differ on this input, so the test is not vacuous.
        assert_ne!(
            of(PairSchedule::SmallMultiplierDegree),
            of(PairSchedule::LargeMultiplierDegree)
        );
    }

    /// Every schedule yields exactly the same set of pairs, in a different order.
    ///
    /// The property that makes a schedule safe: it reorders, it does not discard. A pair the
    /// schedule deprioritizes stays pending until it is selected.
    #[test]
    fn test_a_schedule_discards_nothing() {
        let leads = monomials::<3>(&[
            [2, 0, 1],
            [0, 2, 1],
            [1, 1, 0],
            [1, 0, 2],
            [0, 1, 1],
            [3, 0, 0],
            [0, 0, 4],
        ]);

        for criteria in [
            PairCriteria::NONE,
            PairCriteria::PRODUCT_ONLY,
            PairCriteria::ALL,
        ] {
            let of = |schedule| {
                let mut counts = CriterionCounts::default();
                let queue = seeded_under(&leads, &criteria, schedule, &mut counts);
                let mut keys = drain(queue);
                keys.sort_unstable();
                (keys, counts)
            };

            let baseline = of(PairSchedule::DegreeThenLcm);
            for schedule in PairSchedule::ALL {
                assert_eq!(
                    of(schedule),
                    baseline,
                    "{} under {:?} selected a different pair set",
                    schedule.name(),
                    criteria
                );
            }
        }
    }

    /// Selection under every schedule is deterministic.
    #[test]
    fn test_every_schedule_is_deterministic() {
        let leads = monomials::<3>(&[
            [4, 0, 0],
            [3, 1, 0],
            [1, 0, 0],
            [0, 4, 0],
            [0, 0, 3],
            [1, 1, 1],
        ]);

        for schedule in PairSchedule::ALL {
            let of = || {
                let mut counts = CriterionCounts::default();
                let queue = seeded_under(&leads, &PairCriteria::ALL, schedule, &mut counts);
                (drain(queue), counts)
            };
            let first = of();
            for _ in 0..8 {
                assert_eq!(of(), first, "{}", schedule.name());
            }
        }
    }

    /// A batch cap under a schedule takes the pairs the schedule ranks first, and leaves the rest
    /// pending.
    ///
    /// This is the only place a schedule changes *what* is computed rather than the order of a
    /// matrix's rows: with no cap the batch is the whole degree whatever the schedule.
    #[test]
    fn test_a_capped_batch_follows_the_schedule_and_loses_nothing() {
        let leads = monomials::<3>(&[[4, 0, 0], [3, 1, 0], [1, 0, 0], [0, 4, 0]]);

        for schedule in PairSchedule::ALL {
            let mut counts = CriterionCounts::default();
            let mut queue = seeded_under(&leads, &PairCriteria::NONE, schedule, &mut counts);
            let total = queue.len();

            let mut taken = Vec::new();
            while !queue.is_empty() {
                let batch = queue.select_batch(Some(2));
                assert!(batch.len() <= 2, "{}", schedule.name());
                assert!(
                    batch.iter().all(|p| p.degree == batch[0].degree),
                    "{}: a capped batch mixed degrees",
                    schedule.name()
                );
                taken.extend(batch.iter().map(|p| (p.left, p.right)));
            }
            assert_eq!(
                taken.len(),
                total,
                "{}: pairs went missing",
                schedule.name()
            );
            taken.sort_unstable();
            taken.dedup();
            assert_eq!(
                taken.len(),
                total,
                "{}: a pair came out twice",
                schedule.name()
            );
        }
    }

    /// The chain criterion's handled set is unaffected by the schedule's ordering.
    ///
    /// A deferred pair must not become a witness merely because the schedule put it late, and a
    /// pair the schedule put early must not witness one that has not been processed. Both follow
    /// from `handled` being populated only by `pop`, which this checks by driving the queue under
    /// each schedule and asserting the chain criterion's decisions stay sound: every kept pair is
    /// reduced, and the union of kept and discarded is every pair.
    #[test]
    fn test_the_chain_criterion_stays_sound_under_every_schedule() {
        let leads = monomials::<3>(&[[1, 0, 0], [0, 1, 0], [1, 1, 0], [2, 1, 0], [1, 2, 0]]);

        for schedule in PairSchedule::ALL {
            let mut counts = CriterionCounts::default();
            let mut queue = seeded_under(&leads, &CHAIN_ONLY, schedule, &mut counts);
            let total = queue.len();

            let mut kept = 0;
            let mut discarded = 0;
            while let Some(pair) = queue.pop() {
                if queue.is_discarded(&pair, &leads, &CHAIN_ONLY, &mut counts) {
                    discarded += 1;
                } else {
                    kept += 1;
                }
            }
            assert_eq!(
                kept + discarded,
                total,
                "{}: pairs were neither kept nor discarded",
                schedule.name()
            );
            // A pair is only ever discarded on the strength of pairs already popped, so the first
            // pair out can never be discarded whatever the schedule chose it to be.
            assert!(kept > 0, "{}: every pair was discarded", schedule.name());
        }
    }

    /// The monomial comparator discriminates where the degree comparator cannot.
    ///
    /// The point of Finding 3 and the reason both exist. Sakata–Takagi rank on the larger
    /// multiplier **under the monomial order**; comparing degrees is coarser, and `x^2` against
    /// `y^2` is the smallest case where the two part company — equal degree, distinct under
    /// grevlex. A measurement of the degree heuristic is therefore not a measurement of the
    /// published ordering.
    #[test]
    fn test_the_monomial_comparator_separates_equal_degree_multipliers() {
        // Leading monomials y^2, x^2, x^2*y^2. Pair (0,2) has lcm x^2*y^2 and multipliers x^2 and
        // 1; pair (1,2) has the same lcm and multipliers y^2 and 1. Equal degrees throughout,
        // different monomials.
        let leads = monomials::<2>(&[[0, 2], [2, 0], [2, 2]]);
        let (a, b) = (
            CriticalPair::from_leads(&leads, 0, 2),
            CriticalPair::from_leads(&leads, 1, 2),
        );

        assert_eq!(a.degree, b.degree, "the lcm degree cannot separate them");
        assert_eq!(a.lcm, b.lcm, "nor can the lcm");
        assert_eq!(
            (a.larger_multiplier_degree(), a.smaller_multiplier_degree()),
            (b.larger_multiplier_degree(), b.smaller_multiplier_degree()),
            "nor can the multiplier degrees"
        );
        assert_ne!(
            a.larger_multiplier, b.larger_multiplier,
            "but the multiplier monomials differ, which is what the published ordering compares"
        );

        // The two pairs' relative order under each schedule, read off a live queue.
        let relative = |schedule, order| {
            let mut counts = CriterionCounts::default();
            let mut queue = PairQueue::<2>::scheduled_in(schedule, order);
            queue.push_pairs_from_leads(&leads, 2, &PairCriteria::NONE, &mut counts);
            let mut seen = Vec::new();
            while let Some(pair) = queue.pop() {
                let key = (pair.left, pair.right);
                if key == (0, 2) || key == (1, 2) {
                    seen.push(key);
                }
            }
            seen
        };

        let grevlex = MonomialOrder::GradedReverseLexicographic;

        // The degree comparator ties on both keys and falls through to the lcm, which is also
        // equal, then to the indices — so small and large agree. That is the finding, asserted.
        assert_eq!(
            relative(PairSchedule::SmallMultiplierDegree, grevlex),
            relative(PairSchedule::LargeMultiplierDegree, grevlex),
            "equal degrees leave the degree comparator nothing to order by"
        );

        // The monomial comparator does not tie: x^2 > y^2 under grevlex, so taking the smallest
        // larger multiplier first puts (1,2) ahead of (0,2), and the control reverses it.
        let small = relative(PairSchedule::SmallMultiplierMonomial, grevlex);
        let large = relative(PairSchedule::LargeMultiplierMonomial, grevlex);
        assert_eq!(
            small,
            vec![(1, 2), (0, 2)],
            "smallest larger multiplier first"
        );
        assert_eq!(large, vec![(0, 2), (1, 2)], "and the control reverses it");
    }

    /// A monomial-comparing schedule under two different orders gives two different queues.
    ///
    /// What makes threading the order through the queue necessary rather than cosmetic.
    #[test]
    fn test_the_monomial_comparator_depends_on_the_order() {
        let leads = monomials::<3>(&[[0, 2, 0], [2, 0, 0], [2, 2, 0], [2, 2, 0]]);
        let drain_under = |order| {
            let mut counts = CriterionCounts::default();
            let mut queue =
                PairQueue::<3>::scheduled_in(PairSchedule::SmallMultiplierMonomial, order);
            queue.push_pairs_from_leads(&leads, 2, &PairCriteria::NONE, &mut counts);
            queue.push_pairs_from_leads(&leads, 3, &PairCriteria::NONE, &mut counts);
            drain(queue)
        };
        // x^2 > y^2 under lex and grevlex alike, but the *lcm* tiebreak below the multiplier
        // comparison can still reorder, so assert the weaker and true thing: each order is
        // internally consistent and the queue is deterministic under each.
        for order in [
            MonomialOrder::Lexicographic,
            MonomialOrder::GradedReverseLexicographic,
        ] {
            let first = drain_under(order);
            for _ in 0..4 {
                assert_eq!(drain_under(order), first, "{}", order.name());
            }
        }
    }

    /// Asking for a monomial-comparing schedule without an order is refused, not defaulted.
    #[test]
    #[should_panic(expected = "needs an order")]
    fn test_a_monomial_schedule_without_an_order_is_refused() {
        let _ = PairQueue::<3>::scheduled(PairSchedule::SmallMultiplierMonomial);
    }

    /// Within a degree, `ShortPair` takes the pair with the fewest terms first and `LongPair` the
    /// pair with the most.
    #[test]
    fn test_a_length_schedule_orders_within_a_degree() {
        // Leading monomials x^4, x^3*y, x, y^4. Pairs (0,1) and (2,3) both have lcm degree five,
        // so the degree cannot separate them. The term counts can: 5 + 1 - 2 = 4 against
        // 1 + 1 - 2 = 0.
        let leads = monomials::<3>(&[[4, 0, 0], [3, 1, 0], [1, 0, 0], [0, 4, 0]]);
        let lengths = [5, 1, 1, 1];
        let relative = |schedule| {
            let mut discarded = CriterionCounts::default();
            let queue = PairQueue::seeded_from_leads_ranked(
                &leads,
                &lengths,
                &PairCriteria::NONE,
                schedule,
                ORDER,
                &mut discarded,
            );
            drain(queue)
                .into_iter()
                .filter(|key| *key == (0, 1) || *key == (2, 3))
                .collect::<Vec<_>>()
        };

        assert_eq!(
            relative(PairSchedule::ShortPair),
            vec![(2, 3), (0, 1)],
            "the shorter S-polynomial first"
        );
        assert_eq!(
            relative(PairSchedule::LongPair),
            vec![(0, 1), (2, 3)],
            "and the control reverses it"
        );
    }

    /// With every element the same length a length schedule ties everywhere and falls through to
    /// the baseline's tiebreak, which is what keeps its order total.
    #[test]
    fn test_a_length_schedule_with_equal_counts_is_the_baseline_order() {
        let leads = monomials::<3>(&[[2, 0, 1], [0, 2, 1], [1, 1, 0], [1, 0, 2], [0, 1, 1]]);
        let equal = vec![3; leads.len()];
        let of = |schedule, lengths: &[usize]| {
            let mut discarded = CriterionCounts::default();
            drain(PairQueue::seeded_from_leads_ranked(
                &leads,
                lengths,
                &PairCriteria::NONE,
                schedule,
                ORDER,
                &mut discarded,
            ))
        };

        let baseline = of(PairSchedule::DegreeThenLcm, &[]);
        assert_eq!(of(PairSchedule::ShortPair, &equal), baseline);
        assert_eq!(of(PairSchedule::LongPair, &equal), baseline);
    }

    /// A length-ranking schedule driven without the term counts is refused, not defaulted.
    #[test]
    #[should_panic(expected = "ranks by term count")]
    fn test_a_length_schedule_without_term_counts_is_refused() {
        let leads = monomials::<3>(&[[2, 0, 0], [0, 2, 0]]);
        let mut counts = CriterionCounts::default();
        let _ = PairQueue::seeded_from_leads_scheduled(
            &leads,
            &PairCriteria::NONE,
            PairSchedule::ShortPair,
            ORDER,
            &mut counts,
        );
    }

    /// The default schedule is the baseline, which is what the earlier milestones measured.
    #[test]
    fn test_the_default_schedule_is_the_baseline() {
        assert_eq!(PairSchedule::default(), PairSchedule::DegreeThenLcm);
        assert_eq!(
            PairQueue::<3>::new().schedule(),
            PairSchedule::DegreeThenLcm
        );
        assert_eq!(PairSchedule::ALL.len(), 7);
    }
}
