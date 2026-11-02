//! Critical pairs, and the queue that decides which to process next.
//!
//! Shared by [`super::buchberger`], which takes one pair at a time, and [`super::f4`], which takes
//! a whole batch. Both want the same thing from the queue: the lowest-degree pairs first, and a
//! total order on ties so that the computation is reproducible.
//!
//! Pairs are selected in order of the total degree of their lcm — the normal strategy — which
//! keeps the intermediate polynomials as small as possible for as long as possible.

use std::{cmp::Reverse, collections::BinaryHeap};

use crate::{poly::MonomialOrder, FiniteField, Monomial, MultivariatePolynomial};

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
        assert_ne!(left, right, "a polynomial does not pair with itself");
        let (left, right) = (left.min(right), left.max(right));
        let lcm = Monomial::lcm(
            &basis[left].leading_monomial(order),
            &basis[right].leading_monomial(order),
        );
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
        let mut queue = Self::new();
        for right in 0..basis.len() {
            queue.push_pairs_with(basis, right, order);
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
        for existing in 0..added {
            self.pending
                .push(Reverse(CriticalPair::new(basis, existing, added, order)));
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
}

#[cfg(test)]
mod tests {
    use super::{are_relatively_prime, CriticalPair, PairQueue};
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
