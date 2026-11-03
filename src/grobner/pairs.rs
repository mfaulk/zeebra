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
        Self {
            degree: lcm.degree(),
            lcm,
            left,
            right,
        }
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

/// The critical pairs still to be processed, lowest lcm degree first.
///
/// A min-heap, so adding the pairs of a newly found basis element costs a logarithmic insertion
/// each rather than a rescan of every pair. This is what makes pair processing incremental: the
/// textbook formulation rebuilds every pair on every pass.
/// A pair's identity: its two basis indices, smaller first.
type PairKey = (usize, usize);

#[derive(Debug, Clone, Default)]
pub struct PairQueue<const N: usize> {
    // `Reverse` turns the max-heap into a min-heap.
    pending: BinaryHeap<Reverse<CriticalPair<N>>>,

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
}

impl<const N: usize> PairQueue<N> {
    /// An empty queue.
    pub fn new() -> Self {
        Self {
            pending: BinaryHeap::new(),
            removed: HashSet::new(),
            handled: HashSet::new(),
            live: 0,
            track_handled: false,
        }
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
        let mut queue = Self::new();
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
        let stale: Vec<PairKey> = self
            .pending
            .iter()
            .filter(|Reverse(pair)| !self.removed.contains(&(pair.left, pair.right)))
            .filter(|Reverse(pair)| {
                divides(&lead_h, &pair.lcm)
                    && Monomial::lcm(&leads[pair.left], &lead_h) != pair.lcm
                    && Monomial::lcm(&lead_h, &leads[pair.right]) != pair.lcm
            })
            .map(|Reverse(pair)| (pair.left, pair.right))
            .collect();
        for key in stale {
            self.removed.insert(key);
            self.live -= 1;
            counts.gebauer_moller += 1;
        }

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
    fn push(&mut self, pair: CriticalPair<N>) {
        self.live += 1;
        self.pending.push(Reverse(pair));
    }

    /// Drop lazily deleted entries from the top of the heap, so that the top is a pending pair.
    fn drop_stale_top(&mut self) {
        while !self.removed.is_empty() {
            let Some(Reverse(top)) = self.pending.peek() else {
                return;
            };
            let key = (top.left, top.right);
            if !self.removed.remove(&key) {
                return;
            }
            self.pending.pop();
        }
    }

    /// The next pair, of minimum lcm degree.
    pub fn pop(&mut self) -> Option<CriticalPair<N>> {
        self.drop_stale_top();
        let Reverse(pair) = self.pending.pop()?;
        self.live -= 1;
        if self.track_handled {
            self.handled.insert((pair.left, pair.right));
        }
        Some(pair)
    }

    /// Every remaining pair of minimum lcm degree, up to `limit` of them.
    ///
    /// This is the selection strategy F4 batches on: all the pairs at the lowest degree available,
    /// which is Faugère's `Sel` specialized to the normal strategy. `limit` caps the batch so that
    /// a degree with very many pairs cannot produce a matrix of unbounded size in one step; a
    /// limit of one reduces F4 to processing a single pair per matrix, which is a useful
    /// degenerate case to be able to test.
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
                Some(Reverse(next)) if next.degree == degree => {
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
        PairCriteria, PairQueue,
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

    fn drain<const N: usize>(mut queue: PairQueue<N>) -> Vec<(usize, usize)> {
        let mut keys = Vec::new();
        while let Some(pair) = queue.pop() {
            keys.push((pair.left, pair.right));
        }
        keys
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
}
