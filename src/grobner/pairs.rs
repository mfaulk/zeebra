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

use std::{cmp::Reverse, collections::BinaryHeap};

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
    /// Not yet implemented; the flag exists so that the option surface is complete before the
    /// implementation lands. Setting it currently changes nothing.
    pub chain: bool,

    /// Gebauer–Möller pair-set minimization, applied as pairs are inserted.
    ///
    /// Not yet implemented, as [`PairCriteria::chain`].
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

    /// Discarded by Gebauer–Möller, i.e. never inserted into the queue.
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
#[derive(Debug, Clone, Default)]
pub struct PairQueue<const N: usize> {
    // `Reverse` turns the max-heap into a min-heap.
    pending: BinaryHeap<Reverse<CriticalPair<N>>>,
}

impl<const N: usize> PairQueue<N> {
    /// An empty queue.
    pub fn new() -> Self {
        Self {
            pending: BinaryHeap::new(),
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
        self.pending.is_empty()
    }

    /// The number of pairs waiting.
    pub fn len(&self) -> usize {
        self.pending.len()
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
    pub fn push_pairs_from_leads(
        &mut self,
        leads: &[Monomial<N>],
        added: usize,
        criteria: &PairCriteria,
        counts: &mut CriterionCounts,
    ) {
        // Named so that the baseline's "nothing is discarded here" is visible as a decision rather
        // than as an omission, and so that the implementation has a place to go.
        let _ = (criteria, &mut *counts);

        for existing in 0..added {
            self.pending
                .push(Reverse(CriticalPair::from_leads(leads, existing, added)));
        }
    }

    /// The next pair, of minimum lcm degree.
    pub fn pop(&mut self) -> Option<CriticalPair<N>> {
        self.pending.pop().map(|Reverse(pair)| pair)
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
        batch
            .into_iter()
            .filter(|pair| {
                // Buchberger's first criterion. The leading monomials share no variable, so their
                // lcm is their product and the S-polynomial is guaranteed to reduce to zero modulo
                // the two of them: there is no reason to put either half in a matrix.
                if criteria.product && are_relatively_prime(&leads[pair.left], &leads[pair.right]) {
                    counts.product += 1;
                    return false;
                }

                // The chain criterion belongs here, and must test the handled-pairs condition and
                // not only divisibility of the lcm.
                if criteria.chain {
                    // Not yet implemented; the flag changes nothing rather than changing something
                    // unsound.
                }

                true
            })
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::{
        are_relatively_prime, leading_monomials, CriterionCounts, CriticalPair, PairCriteria,
        PairQueue,
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
