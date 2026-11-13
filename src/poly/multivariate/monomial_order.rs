//! Orders carry their variable arity when required; comparison rejects a mismatched ring.

use crate::Monomial;
use std::{
    cmp::Ordering,
    fmt::{Display, Formatter},
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MonomialOrder {
    /// Lexicographic order (lex).
    Lexicographic,

    /// Graded lexicographic order (grlex).
    GradedLexicographic,

    /// Graded reverse lexicographic order (grevlex).
    GradedReverseLexicographic,

    /// A weighted order: graded by [`WeightedOrder::weighted_degree`], then by a stated tie-break.
    ///
    /// The payload is a reference so that `MonomialOrder` stays `Copy` and two words wide. It is
    /// threaded by value through the whole Gröbner stack, and an inline weight array would make
    /// every one of those signatures pass an aggregate in memory rather than in registers.
    /// [`MonomialOrder::weighted`] builds one from a runtime weight vector; a weight vector known
    /// at compile time can be a `static` and skip the interning entirely.
    Weighted(&'static WeightedOrder),

    /// A validated product order with a dominant prefix of variables.
    Block(BlockOrder),
}

impl MonomialOrder {
    /// Returns the monomial order's comparison function.
    pub fn cmp<const N: usize>(&self, a: &Monomial<N>, b: &Monomial<N>) -> Ordering {
        match self {
            MonomialOrder::Lexicographic => lex(a, b),
            MonomialOrder::GradedLexicographic => grlex(a, b),
            MonomialOrder::GradedReverseLexicographic => grevlex(a, b),
            MonomialOrder::Weighted(weighted) => weighted.cmp(a, b),
            MonomialOrder::Block(block) => block.cmp(a, b),
        }
    }

    /// A weighted order over `weights`, interned for the process lifetime.
    ///
    /// For a weight vector that is not known until run time — Construction 1 of the FreeLunch
    /// paper derives one from the system it is about to order — there is nowhere to put a
    /// `static`, so the vector is leaked. One small leak per *distinct order*, and orders are
    /// built once per computation rather than once per comparison, so the total is bounded by how
    /// many orders a process constructs. A caller that minds can hold the returned value instead
    /// of rebuilding it.
    ///
    /// # Errors
    /// [`WeightedOrderError`] if the weight vector is empty or has a non-positive weight.
    pub fn weighted(
        weights: &[u32],
        tie_break: WeightedTieBreak,
    ) -> Result<Self, WeightedOrderError> {
        let leaked: &'static [u32] = Box::leak(weights.to_vec().into_boxed_slice());
        let order = WeightedOrder::checked(leaked, tie_break)?;
        Ok(MonomialOrder::Weighted(Box::leak(Box::new(order))))
    }

    /// The required variable arity, or `None` for a built-in order.
    ///
    /// Lets a caller reject an arity mismatch with an error of its own before [`Self::cmp`]
    /// panics on one; see [`WeightedOrder::cmp`] for why that panic is not negotiable.
    pub fn arity(&self) -> Option<usize> {
        match self {
            MonomialOrder::Weighted(weighted) => Some(weighted.weights().len()),
            MonomialOrder::Block(block) => Some(block.arity()),
            _ => None,
        }
    }

    /// The greater of two monomials under this order.
    pub fn max<const N: usize>(&self, a: &Monomial<N>, b: &Monomial<N>) -> Monomial<N> {
        // Defers to `cmp` so the two cannot drift apart, which is how grevlex came to be
        // dispatched two different ways.
        match self.cmp(a, b) {
            Ordering::Greater => *a,
            Ordering::Less => *b,
            Ordering::Equal => *a,
        }
    }

    /// Returns the monomial order's name.
    ///
    /// Not injective: weighted and block orders answer `"weighted"` and `"block"`; the name is
    /// `&'static str` and carries no parameters. Anything that has to *distinguish* orders —
    /// a digest, a record key, a cache — must not key on this.
    pub fn name(&self) -> &'static str {
        match self {
            MonomialOrder::Lexicographic => "lex",
            MonomialOrder::GradedLexicographic => "grlex",
            MonomialOrder::GradedReverseLexicographic => "grevlex",
            MonomialOrder::Weighted(_) => "weighted",
            MonomialOrder::Block(_) => "block",
        }
    }

    /// Returns the monomial order's description.
    pub fn description(&self) -> &'static str {
        match self {
            MonomialOrder::Lexicographic => "lexicographic",
            MonomialOrder::GradedLexicographic => "graded lexicographic",
            MonomialOrder::GradedReverseLexicographic => "graded reverse lexicographic",
            MonomialOrder::Weighted(_) => "weighted graded",
            MonomialOrder::Block(_) => "two-block elimination",
        }
    }
}

/// The admissible order within one contiguous block.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BlockOrderKind {
    /// Compare the first differing exponent, larger first.
    Lexicographic,
    /// Compare total degree, then lexicographically.
    GradedLexicographic,
    /// Compare total degree, then reverse lexicographically.
    GradedReverseLexicographic,
}

impl BlockOrderKind {
    fn cmp(self, a: &[u32], b: &[u32]) -> Ordering {
        if self != Self::Lexicographic {
            // BlockOrder caps arity at u32::MAX, so the sum of u32 exponents fits u64.
            let degree = |xs: &[u32]| xs.iter().map(|&x| u64::from(x)).sum::<u64>();
            let cmp = degree(a).cmp(&degree(b));
            if cmp != Ordering::Equal {
                return cmp;
            }
        }
        if self == Self::GradedReverseLexicographic {
            a.iter().rev().cmp(b.iter().rev()).reverse()
        } else {
            a.cmp(b)
        }
    }

    /// The canonical suborder name used in instance identities.
    pub fn name(self) -> &'static str {
        match self {
            Self::Lexicographic => "lex",
            Self::GradedLexicographic => "grlex",
            Self::GradedReverseLexicographic => "grevlex",
        }
    }
}

/// Product order on `[0, split)` followed by `[split, arity)`.
///
/// Both nonempty blocks use admissible orders. Their lexicographic product is total,
/// multiplicative and a well-order. A nonconstant prefix exceeds the constant prefix,
/// independently of suffix exponents, giving the elimination property.
/// The inline payload preserves the compact `Copy` order API without process-lifetime storage.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BlockOrder {
    arity: u32,
    split: u32,
    prefix: BlockOrderKind,
    suffix: BlockOrderKind,
}

impl BlockOrder {
    /// Construct two nonempty blocks; arities above `u32::MAX` are unsupported.
    pub fn checked(
        arity: usize,
        split: usize,
        prefix: BlockOrderKind,
        suffix: BlockOrderKind,
    ) -> Result<Self, BlockOrderError> {
        let arity = u32::try_from(arity).map_err(|_| BlockOrderError::ArityTooLarge)?;
        if split == 0 || split >= arity as usize {
            return Err(BlockOrderError::EmptyBlock);
        }
        Ok(Self {
            arity,
            split: split as u32,
            prefix,
            suffix,
        })
    }

    /// Number of variables in the ring.
    pub fn arity(self) -> usize {
        self.arity as usize
    }
    /// Number of variables in the dominant eliminated prefix.
    pub fn split(self) -> usize {
        self.split as usize
    }
    /// Order within the prefix.
    pub fn prefix(self) -> BlockOrderKind {
        self.prefix
    }
    /// Order within the retained suffix.
    pub fn suffix(self) -> BlockOrderKind {
        self.suffix
    }

    fn cmp<const N: usize>(self, a: &Monomial<N>, b: &Monomial<N>) -> Ordering {
        assert_eq!(N, self.arity(), "block order arity mismatch");
        let split = self.split();
        self.prefix
            .cmp(&a.exponents()[..split], &b.exponents()[..split])
            .then_with(|| {
                self.suffix
                    .cmp(&a.exponents()[split..], &b.exponents()[split..])
            })
    }
}

/// Invalid boundary or unsupported arity in a two-block order.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BlockOrderError {
    /// The split must lie strictly inside the variable list.
    EmptyBlock,
    /// The compact order representation supports at most `u32::MAX` variables.
    ArityTooLarge,
}
impl Display for BlockOrderError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::EmptyBlock => "both order blocks must be nonempty",
            Self::ArityTooLarge => "block order arity exceeds u32::MAX",
        })
    }
}
impl std::error::Error for BlockOrderError {}

/// How a [`WeightedOrder`] ranks monomials of equal weighted degree.
///
/// Every variant compares exponent vectors position by position, which is what keeps the order
/// multiplicative: multiplying both monomials by a third adds the same exponent to each position
/// and so changes no comparison.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WeightedTieBreak {
    /// Variable 0 first, larger exponent greater. With all weights 1 this is exactly
    /// [`MonomialOrder::GradedLexicographic`].
    Lexicographic,

    /// Last variable first, *smaller* exponent greater. With all weights 1 this is exactly
    /// [`MonomialOrder::GradedReverseLexicographic`].
    ReverseLexicographic,

    /// Last variable first, larger exponent greater.
    ///
    /// Definition 2 of the FreeLunch paper (`docs/research/griffin-freelunch.md` §2.1): ties go to
    /// the monomial with the larger exponent at the highest differing index, i.e.
    /// [`Self::Lexicographic`] on the reversed variable labelling. It is **not**
    /// [`Self::ReverseLexicographic`], which favours the smaller exponent there — the two differ
    /// on every tie, and getting it wrong is a silently different order rather than an error.
    LastVariableFirst,
}

/// A weighted monomial order: one positive integer weight per variable, graded by the weighted
/// degree `Σ w_i e_i`, with a stated tie-break.
///
/// Admissibility rests on the weights being **strictly positive**. Then the weighted degree is at
/// least the total degree, only `1` has weighted degree zero, and each weighted degree is attained
/// by finitely many monomials — so the order is a well-order and reduction terminates. A zero
/// weight breaks that, which is why [`Self::checked`] refuses one.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct WeightedOrder {
    weights: &'static [u32],
    tie_break: WeightedTieBreak,
}

impl WeightedOrder {
    /// A weighted order over `weights`, usable in a `const` or `static`.
    ///
    /// # Panics
    /// If `weights` is empty or holds a zero. In a `const`/`static` initializer that panic is a
    /// compile-time error, which is the point: the invalid weight vector never exists.
    pub const fn new(weights: &'static [u32], tie_break: WeightedTieBreak) -> Self {
        assert!(
            !weights.is_empty(),
            "weighted order needs at least one weight"
        );
        let mut i = 0;
        while i < weights.len() {
            assert!(
                weights[i] != 0,
                "weighted order needs strictly positive weights"
            );
            i += 1;
        }
        Self { weights, tie_break }
    }

    /// [`Self::new`], reporting an invalid weight vector instead of panicking.
    pub fn checked(
        weights: &'static [u32],
        tie_break: WeightedTieBreak,
    ) -> Result<Self, WeightedOrderError> {
        if weights.is_empty() {
            return Err(WeightedOrderError::Empty);
        }
        if let Some(index) = weights.iter().position(|w| *w == 0) {
            return Err(WeightedOrderError::NonPositiveWeight { index });
        }
        Ok(Self { weights, tie_break })
    }

    /// The weight vector.
    pub fn weights(&self) -> &'static [u32] {
        self.weights
    }

    /// The tie-break applied between monomials of equal weighted degree.
    pub fn tie_break(&self) -> WeightedTieBreak {
        self.tie_break
    }

    /// `Σ w_i e_i`.
    ///
    /// # Panics
    /// If the weight vector's arity is not `N`, or if the weighted degree overflows `u64`.
    pub fn weighted_degree<const N: usize>(&self, m: &Monomial<N>) -> u64 {
        self.assert_arity::<N>();
        let mut total: u64 = 0;
        for i in 0..N {
            // A `u32` times a `u32` cannot overflow `u64`, so only the accumulation is checked.
            // Checked in every build and not only where `overflow-checks` is on, for the reason
            // `&Monomial * &Monomial` gives: a wrapped weighted degree is not a large degree, it
            // is a *different* grading, and a release build would then reduce under an order
            // nobody asked for and return a basis that is wrong without being obviously wrong.
            let term = self.weights[i] as u64 * m.exponents()[i] as u64;
            total = total.checked_add(term).expect("weighted degree overflow");
        }
        total
    }

    /// Compare under the weighted order.
    ///
    /// # Panics
    /// If the weight vector's arity is not `N`. The check stays in release builds because the
    /// alternative is silent: zipping a short weight vector against an exponent vector would
    /// truncate, and the resulting comparison is a consistent order on a *different* ring.
    pub fn cmp<const N: usize>(&self, a: &Monomial<N>, b: &Monomial<N>) -> Ordering {
        match self.weighted_degree(a).cmp(&self.weighted_degree(b)) {
            Ordering::Equal => self.break_tie(a, b),
            ord => ord,
        }
    }

    fn break_tie<const N: usize>(&self, a: &Monomial<N>, b: &Monomial<N>) -> Ordering {
        match self.tie_break {
            WeightedTieBreak::Lexicographic => a.exponents().cmp(b.exponents()),
            WeightedTieBreak::ReverseLexicographic => {
                for i in (0..N).rev() {
                    match a.exponents()[i].cmp(&b.exponents()[i]).reverse() {
                        Ordering::Equal => continue,
                        ord => return ord,
                    }
                }
                Ordering::Equal
            }
            WeightedTieBreak::LastVariableFirst => {
                for i in (0..N).rev() {
                    match a.exponents()[i].cmp(&b.exponents()[i]) {
                        Ordering::Equal => continue,
                        ord => return ord,
                    }
                }
                Ordering::Equal
            }
        }
    }

    fn assert_arity<const N: usize>(&self) {
        assert_eq!(
            self.weights.len(),
            N,
            "weighted order has {} weights but was applied to monomials in {} variables",
            self.weights.len(),
            N
        );
    }
}

/// Why a weight vector is not a [`WeightedOrder`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WeightedOrderError {
    /// No weights at all, so there is no grading.
    Empty,

    /// A zero weight, which leaves infinitely many monomials of each weighted degree and so no
    /// well-order.
    NonPositiveWeight { index: usize },
}

impl Display for WeightedOrderError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Empty => write!(f, "a weighted order needs at least one weight"),
            Self::NonPositiveWeight { index } => write!(
                f,
                "weight {} is zero, so the weighted degree does not well-order the monomials",
                index
            ),
        }
    }
}

impl std::error::Error for WeightedOrderError {}

/// Lexicographic order.
///
/// Compares exponents of x1 in the monomials, and in case of equality compares exponents of x2, etc.
fn lex<const N: usize>(a: &Monomial<N>, b: &Monomial<N>) -> Ordering {
    a.exponents().cmp(b.exponents())
}

/// Graded lexicographic order.
///
/// Compares by total degree and then "breaks ties" using lexicographic order.
fn grlex<const N: usize>(a: &Monomial<N>, b: &Monomial<N>) -> Ordering {
    match a.degree().cmp(&b.degree()) {
        Ordering::Equal => lex(a, b),
        ord => ord,
    }
}

/// Graded reverse lexicographic order.
///
/// Compares by total degree (sum of all exponents), and then "breaks ties" by looking at the
/// right-most variable and favoring the monomial with the smaller exponent on that variable.
fn grevlex<const N: usize>(a: &Monomial<N>, b: &Monomial<N>) -> Ordering {
    match a.degree().cmp(&b.degree()) {
        Ordering::Equal => {
            for i in (0..N).rev() {
                match a.exponents()[i].cmp(&b.exponents()[i]).reverse() {
                    Ordering::Equal => continue,
                    ord => return ord,
                }
            }
            Ordering::Equal
        }
        ord => ord,
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        poly::multivariate::monomial_order::{grevlex, grlex, lex},
        Monomial, MonomialOrder, WeightedOrder, WeightedOrderError, WeightedTieBreak as TieBreak,
    };
    use proptest::{
        collection::vec,
        prelude::{any, Just, Strategy, TestCaseError},
        prop_assert, prop_assert_eq, prop_oneof, proptest,
    };
    use std::cmp::Ordering;

    #[test]
    fn spotcheck_lex_ordering() {
        // Equal
        {
            let a = Monomial::<3>::new(&[1, 5, 3]); // xy^5z^3
            assert_eq!(lex(&a, &a), Ordering::Equal); // (1,5,3) =_lex (1,5,3)
        }

        {
            let a = Monomial::<3>::new(&[1, 2, 0]); // y^5
            let b = Monomial::<3>::new(&[0, 3, 4]); // x^5
            assert_eq!(lex(&a, &b), Ordering::Greater); // (1,2,0) >_lex (0,3,4)
            assert_eq!(lex(&b, &a), Ordering::Less);
        }

        {
            let a = Monomial::<3>::new(&[3, 2, 4]); // x^3y^2z^4
            let b = Monomial::<3>::new(&[3, 2, 1]); // x^3y^2z
            assert_eq!(lex(&a, &b), Ordering::Greater); // (3,2,4) >_lex (3,2,1)
            assert_eq!(lex(&b, &a), Ordering::Less);
        }
    }

    #[test]
    fn spotcheck_grlex_ordering() {
        // Equal
        {
            let a = Monomial::<3>::new(&[1, 5, 3]); // xy^5z^3
            assert_eq!(grlex(&a, &a), Ordering::Equal);
        }

        // (1,2,3) >_grlex (3,2,0)
        {
            let a = Monomial::<3>::new(&[1, 2, 3]); // xy^2z^3
            let b = Monomial::<3>::new(&[3, 2, 0]); // x^3yz^0
            assert_eq!(grlex(&a, &b), Ordering::Greater);
            assert_eq!(grlex(&b, &a), Ordering::Less);
        }

        // (1,2,4) >_grlex (1,1,5)
        {
            let a = Monomial::<3>::new(&[1, 2, 4]); // xy^2z^4
            let b = Monomial::<3>::new(&[1, 1, 5]); // xy^1z^5
            assert_eq!(grlex(&a, &b), Ordering::Greater);
            assert_eq!(grlex(&b, &a), Ordering::Less);
        }
    }

    #[test]
    fn spotcheck_grevlex_ordering() {
        // Equal
        {
            let a = Monomial::<3>::new(&[1, 5, 3]); // xy^5z^3
            assert_eq!(grevlex(&a, &a), Ordering::Equal);
        }

        {
            let a = Monomial::<3>::new(&[4, 7, 1]); // x^4y^7z
            let b = Monomial::<3>::new(&[4, 2, 3]); // x^4y^2z^3
            assert_eq!(grevlex(&a, &b), Ordering::Greater); // (4,7,1) >_grlex (4,2,3)
            assert_eq!(grevlex(&b, &a), Ordering::Less);
        }

        {
            let a = Monomial::<3>::new(&[1, 5, 2]); // xy^5z^2
            let b = Monomial::<3>::new(&[4, 1, 3]); // x^4yz^3
            assert_eq!(grevlex(&a, &b), Ordering::Greater); // (1,5,2) >_grevlex (4,1,3)
            assert_eq!(grevlex(&b, &a), Ordering::Less);
        }
    }

    fn order_is_symmetric<const N: usize>(
        a: Monomial<N>,
        b: Monomial<N>,
    ) -> Result<(), TestCaseError> {
        prop_assert_eq!(lex(&a, &b), lex(&b, &a).reverse());
        prop_assert_eq!(grlex(&a, &b), grlex(&b, &a).reverse());
        prop_assert_eq!(grevlex(&a, &b), grevlex(&b, &a).reverse());
        Ok(())
    }

    proptest! {
        #[test]
        fn test_order_is_symmetric(a in any::<Monomial<7>>(), b in any::<Monomial<7>>()) {
            order_is_symmetric(a, b)?;
        }
    }

    /// Every order dispatches `cmp` to its own comparison, not another order's.
    ///
    /// Regression test for a dispatch bug: `GradedReverseLexicographic` routed `cmp` to `grlex`
    /// while `max` routed it to `grevlex`, so grevlex silently behaved as grlex everywhere
    /// `leading_term` was used, and the two functions disagreed with each other.
    #[test]
    fn test_cmp_dispatches_to_the_named_order() {
        // In three variables at degree two, grlex and grevlex disagree on x*z versus y^2:
        // grlex compares exponent vectors left to right, so x*z = (1,0,1) > y^2 = (0,2,0);
        // grevlex compares from the right preferring the smaller, so y^2 > x*z.
        let xz = Monomial::<3>::new(&[1, 0, 1]);
        let y2 = Monomial::<3>::new(&[0, 2, 0]);

        assert_eq!(
            MonomialOrder::GradedLexicographic.cmp(&xz, &y2),
            Ordering::Greater,
            "grlex should rank x*z above y^2"
        );
        assert_eq!(
            MonomialOrder::GradedReverseLexicographic.cmp(&xz, &y2),
            Ordering::Less,
            "grevlex should rank y^2 above x*z"
        );

        // The two orders must therefore not agree on this pair.
        assert_ne!(
            MonomialOrder::GradedLexicographic.cmp(&xz, &y2),
            MonomialOrder::GradedReverseLexicographic.cmp(&xz, &y2)
        );
    }

    /// `cmp` and `max` agree, for every order.
    #[test]
    fn test_cmp_and_max_agree() {
        let monomials = sample_monomials();
        for order in ALL_ORDERS {
            for a in &monomials {
                for b in &monomials {
                    let expected = match order.cmp(a, b) {
                        Ordering::Less => *b,
                        _ => *a,
                    };
                    assert_eq!(
                        order.max(a, b),
                        expected,
                        "{}: max disagrees with cmp on {:?} and {:?}",
                        order.name(),
                        a.exponents(),
                        b.exponents()
                    );
                }
            }
        }
    }

    /// Each order is a total order: antisymmetric, and equal only for equal monomials.
    #[test]
    fn test_orders_are_total() {
        let monomials = sample_monomials();
        for order in ALL_ORDERS {
            for a in &monomials {
                for b in &monomials {
                    assert_eq!(
                        order.cmp(a, b),
                        order.cmp(b, a).reverse(),
                        "{} is not antisymmetric",
                        order.name()
                    );
                    assert_eq!(
                        order.cmp(a, b) == Ordering::Equal,
                        a == b,
                        "{} reports equality for distinct monomials",
                        order.name()
                    );
                }
            }
        }
    }

    /// Each order is transitive.
    #[test]
    fn test_orders_are_transitive() {
        let monomials = sample_monomials();
        for order in ALL_ORDERS {
            for a in &monomials {
                for b in &monomials {
                    for c in &monomials {
                        if order.cmp(a, b) == Ordering::Less && order.cmp(b, c) == Ordering::Less {
                            assert_eq!(
                                order.cmp(a, c),
                                Ordering::Less,
                                "{} is not transitive",
                                order.name()
                            );
                        }
                    }
                }
            }
        }
    }

    /// Each order is multiplicative: a < b implies a*c < b*c.
    ///
    /// This is what makes a monomial order usable for division, and the sorted-merge reduction
    /// relies on it: multiplying a sorted sequence of terms by a monomial preserves the order.
    #[test]
    fn test_orders_are_multiplicative() {
        let monomials = sample_monomials();
        for order in ALL_ORDERS {
            for a in &monomials {
                for b in &monomials {
                    for c in &monomials {
                        let ac = a * c;
                        let bc = b * c;
                        assert_eq!(
                            order.cmp(a, b),
                            order.cmp(&ac, &bc),
                            "{}: multiplying by {:?} changed the order of {:?} and {:?}",
                            order.name(),
                            c.exponents(),
                            a.exponents(),
                            b.exponents()
                        );
                    }
                }
            }
        }
    }

    /// One is the least monomial under every order, so reduction terminates.
    #[test]
    fn test_one_is_minimal() {
        let one = Monomial::<3>::one();
        for order in ALL_ORDERS {
            for m in sample_monomials() {
                if m == one {
                    continue;
                }
                assert_eq!(
                    order.cmp(&one, &m),
                    Ordering::Less,
                    "{} does not rank 1 below {:?}",
                    order.name(),
                    m.exponents()
                );
            }
        }
    }

    /// Each order ranks degree-two monomials in three variables as the textbook does.
    #[test]
    fn test_known_orderings_of_degree_two() {
        let descending = |order: MonomialOrder, mut ms: Vec<Monomial<3>>| {
            ms.sort_by(|a, b| order.cmp(a, b).reverse());
            ms.iter()
                .map(|m| m.exponents().to_vec())
                .collect::<Vec<_>>()
        };
        let degree_two = vec![
            Monomial::<3>::new(&[2, 0, 0]), // x^2
            Monomial::<3>::new(&[1, 1, 0]), // xy
            Monomial::<3>::new(&[1, 0, 1]), // xz
            Monomial::<3>::new(&[0, 2, 0]), // y^2
            Monomial::<3>::new(&[0, 1, 1]), // yz
            Monomial::<3>::new(&[0, 0, 2]), // z^2
        ];

        // lex and grlex coincide within a single degree: x^2 > xy > xz > y^2 > yz > z^2.
        let expected_lex = vec![
            vec![2, 0, 0],
            vec![1, 1, 0],
            vec![1, 0, 1],
            vec![0, 2, 0],
            vec![0, 1, 1],
            vec![0, 0, 2],
        ];
        assert_eq!(
            descending(MonomialOrder::Lexicographic, degree_two.clone()),
            expected_lex
        );
        assert_eq!(
            descending(MonomialOrder::GradedLexicographic, degree_two.clone()),
            expected_lex
        );

        // grevlex differs: x^2 > xy > y^2 > xz > yz > z^2.
        assert_eq!(
            descending(MonomialOrder::GradedReverseLexicographic, degree_two),
            vec![
                vec![2, 0, 0],
                vec![1, 1, 0],
                vec![0, 2, 0],
                vec![1, 0, 1],
                vec![0, 1, 1],
                vec![0, 0, 2],
            ]
        );
    }

    /// Graded orders rank by total degree first; lex does not.
    #[test]
    fn test_graded_orders_rank_by_degree_first() {
        let low = Monomial::<3>::new(&[1, 0, 0]); // x, degree 1
        let high = Monomial::<3>::new(&[0, 0, 3]); // z^3, degree 3

        for order in [
            MonomialOrder::GradedLexicographic,
            MonomialOrder::GradedReverseLexicographic,
        ] {
            assert_eq!(order.cmp(&low, &high), Ordering::Less, "{}", order.name());
        }
        // Under lex, x outranks z^3 despite the lower degree.
        assert_eq!(
            MonomialOrder::Lexicographic.cmp(&low, &high),
            Ordering::Greater
        );
    }

    const ALL_ORDERS: [MonomialOrder; 3] = [
        MonomialOrder::Lexicographic,
        MonomialOrder::GradedLexicographic,
        MonomialOrder::GradedReverseLexicographic,
    ];

    // Weight vectors as `static`s, which is also the only test the `const` constructor's
    // compile-time rejection gets: a zero weight here would not compile.
    static ONES_LEX: WeightedOrder = WeightedOrder::new(&[1, 1, 1], TieBreak::Lexicographic);
    static ONES_REVLEX: WeightedOrder =
        WeightedOrder::new(&[1, 1, 1], TieBreak::ReverseLexicographic);
    static ONES_LAST: WeightedOrder = WeightedOrder::new(&[1, 1, 1], TieBreak::LastVariableFirst);
    static GRIFFIN_R5: WeightedOrder = WeightedOrder::new(&[1, 7, 49], TieBreak::LastVariableFirst);
    static SKEWED_LEX: WeightedOrder = WeightedOrder::new(&[3, 1, 4], TieBreak::Lexicographic);
    static SKEWED_REVLEX: WeightedOrder =
        WeightedOrder::new(&[3, 1, 4], TieBreak::ReverseLexicographic);
    static BIG: WeightedOrder = WeightedOrder::new(&[1, 1000, 7], TieBreak::LastVariableFirst);

    /// Weighted orders covering every tie-break, unit and non-unit weights, and a wide spread.
    const WEIGHTED_ORDERS: [MonomialOrder; 7] = [
        MonomialOrder::Weighted(&ONES_LEX),
        MonomialOrder::Weighted(&ONES_REVLEX),
        MonomialOrder::Weighted(&ONES_LAST),
        MonomialOrder::Weighted(&GRIFFIN_R5),
        MonomialOrder::Weighted(&SKEWED_LEX),
        MonomialOrder::Weighted(&SKEWED_REVLEX),
        MonomialOrder::Weighted(&BIG),
    ];

    /// With every weight 1, the lexicographic tie-break reproduces grlex exactly.
    #[test]
    fn test_unit_weights_reproduce_grlex() {
        for a in sample_monomials() {
            for b in sample_monomials() {
                assert_eq!(
                    MonomialOrder::Weighted(&ONES_LEX).cmp(&a, &b),
                    MonomialOrder::GradedLexicographic.cmp(&a, &b),
                    "disagreed on {:?} and {:?}",
                    a.exponents(),
                    b.exponents()
                );
            }
        }
    }

    /// With every weight 1, the reverse-lexicographic tie-break reproduces grevlex exactly.
    #[test]
    fn test_unit_weights_reproduce_grevlex() {
        for a in sample_monomials() {
            for b in sample_monomials() {
                assert_eq!(
                    MonomialOrder::Weighted(&ONES_REVLEX).cmp(&a, &b),
                    MonomialOrder::GradedReverseLexicographic.cmp(&a, &b),
                    "disagreed on {:?} and {:?}",
                    a.exponents(),
                    b.exponents()
                );
            }
        }
    }

    /// FreeLunch's tie-break is not grevlex's: they disagree on every tie.
    ///
    /// Both read the exponent vector from the last variable down, and they differ only in which
    /// exponent wins there. Picking the wrong one yields a perfectly admissible order on the
    /// wrong ideal, so the distinction gets a test of its own.
    #[test]
    fn test_freelunch_tie_break_is_not_grevlex() {
        let mut ties = 0;
        for a in sample_monomials() {
            for b in sample_monomials() {
                if a == b || a.degree() != b.degree() {
                    continue;
                }
                ties += 1;
                assert_eq!(
                    MonomialOrder::Weighted(&ONES_LAST).cmp(&a, &b),
                    MonomialOrder::Weighted(&ONES_REVLEX).cmp(&a, &b).reverse(),
                    "{:?} vs {:?}",
                    a.exponents(),
                    b.exponents()
                );
            }
        }
        assert!(ties > 0, "the sample contained no ties to break");
    }

    /// Every weighted order is a total order: antisymmetric, and equal only on equal monomials.
    #[test]
    fn test_weighted_orders_are_total() {
        for order in WEIGHTED_ORDERS {
            for a in &sample_monomials() {
                for b in &sample_monomials() {
                    assert_eq!(
                        order.cmp(a, b),
                        order.cmp(b, a).reverse(),
                        "a weighted order is not antisymmetric"
                    );
                    assert_eq!(
                        order.cmp(a, b) == Ordering::Equal,
                        a == b,
                        "a weighted order reports equality for distinct monomials"
                    );
                }
            }
        }
    }

    /// Every weighted order is transitive.
    #[test]
    fn test_weighted_orders_are_transitive() {
        let monomials = sample_monomials();
        for order in WEIGHTED_ORDERS {
            for a in &monomials {
                for b in &monomials {
                    for c in &monomials {
                        if order.cmp(a, b) == Ordering::Less && order.cmp(b, c) == Ordering::Less {
                            assert_eq!(order.cmp(a, c), Ordering::Less, "not transitive");
                        }
                    }
                }
            }
        }
    }

    /// Every weighted order is multiplicative: `a < b` implies `a*c < b*c`.
    ///
    /// This is the axiom the sorted-merge reduction in `normal_form` relies on, so a weighted
    /// order that failed it would corrupt reduction rather than merely rank monomials oddly.
    #[test]
    fn test_weighted_orders_are_multiplicative() {
        let monomials = sample_monomials();
        for order in WEIGHTED_ORDERS {
            for a in &monomials {
                for b in &monomials {
                    for c in &monomials {
                        assert_eq!(
                            order.cmp(a, b),
                            order.cmp(&(a * c), &(b * c)),
                            "multiplying by {:?} changed the order of {:?} and {:?}",
                            c.exponents(),
                            a.exponents(),
                            b.exponents()
                        );
                    }
                }
            }
        }
    }

    /// Every weighted order ranks a monomial strictly above each of its proper divisors.
    ///
    /// With multiplicativity this is admissibility, and so well-ordering: a strictly descending
    /// chain can only shrink the exponent vector, and `1` is the floor. It is the property a zero
    /// weight would break, which is why [`WeightedOrder::checked`] refuses one.
    #[test]
    fn test_weighted_orders_rank_a_monomial_above_its_proper_divisors() {
        let monomials = sample_monomials();
        for order in WEIGHTED_ORDERS {
            for m in &monomials {
                for d in &monomials {
                    if d == m || m.checked_div(d).is_none() {
                        continue;
                    }
                    assert_eq!(
                        order.cmp(d, m),
                        Ordering::Less,
                        "{:?} does not rank below its multiple {:?}",
                        d.exponents(),
                        m.exponents()
                    );
                }
            }
            assert_eq!(
                order.cmp(&Monomial::<3>::one(), &Monomial::<3>::new(&[0, 0, 1])),
                Ordering::Less,
                "1 is not the least monomial"
            );
        }
    }

    /// A weight vector that is empty or holds a zero is refused at construction.
    #[test]
    fn test_invalid_weight_vectors_are_refused() {
        assert_eq!(
            WeightedOrder::checked(&[], TieBreak::Lexicographic),
            Err(WeightedOrderError::Empty)
        );
        assert_eq!(
            WeightedOrder::checked(&[1, 0, 3], TieBreak::Lexicographic),
            Err(WeightedOrderError::NonPositiveWeight { index: 1 })
        );
        assert_eq!(
            MonomialOrder::weighted(&[2, 0], TieBreak::LastVariableFirst),
            Err(WeightedOrderError::NonPositiveWeight { index: 1 })
        );
        assert!(MonomialOrder::weighted(&[1, 7, 49], TieBreak::LastVariableFirst).is_ok());
    }

    /// A weight vector whose arity is not the monomial's panics rather than comparing a prefix.
    ///
    /// `zip` would silently truncate, which is a consistent order on a different ring — the
    /// failure class this whole module is written against.
    #[test]
    #[should_panic(expected = "weighted order has 2 weights")]
    fn test_arity_mismatch_panics() {
        static TWO: WeightedOrder = WeightedOrder::new(&[1, 7], TieBreak::Lexicographic);
        let _ = MonomialOrder::Weighted(&TWO).cmp(
            &Monomial::<3>::new(&[1, 1, 1]),
            &Monomial::<3>::new(&[1, 1, 2]),
        );
    }

    /// The weighted degree is a dot product, which overflows sooner than a total degree, and it
    /// panics rather than wrapping — in release builds too.
    #[test]
    #[should_panic(expected = "weighted degree overflow")]
    fn test_weighted_degree_overflow_panics() {
        static HEAVY: WeightedOrder =
            WeightedOrder::new(&[u32::MAX, u32::MAX, u32::MAX], TieBreak::Lexicographic);
        let m = Monomial::<3>::new(&[u32::MAX, u32::MAX, u32::MAX]);
        let _ = HEAVY.weighted_degree(&m);
    }

    /// The weighted degree is `Σ w_i e_i`, and `arity` reports the weight vector's length.
    #[test]
    fn test_weighted_degree_and_arity() {
        assert_eq!(
            GRIFFIN_R5.weighted_degree(&Monomial::<3>::new(&[2, 1, 3])),
            2 + 7 + 147
        );
        assert_eq!(GRIFFIN_R5.weighted_degree(&Monomial::<3>::one()), 0);
        assert_eq!(MonomialOrder::Weighted(&GRIFFIN_R5).arity(), Some(3));
        assert_eq!(MonomialOrder::GradedReverseLexicographic.arity(), None);
        assert_eq!(GRIFFIN_R5.weights(), &[1, 7, 49]);
        assert_eq!(GRIFFIN_R5.tie_break(), TieBreak::LastVariableFirst);
    }

    /// Non-unit weights reorder monomials that total degree ties, which is the capability.
    ///
    /// Under the Griffin `r = 5` vector `(1, 7, 49)`, `x_2` outranks `x_0^48` even though the
    /// latter has 48 times the total degree — a ranking no unweighted order here produces.
    #[test]
    fn test_non_unit_weights_are_not_a_relabelling_of_total_degree() {
        let order = MonomialOrder::Weighted(&GRIFFIN_R5);
        let x2 = Monomial::<3>::new(&[0, 0, 1]);
        let x0_48 = Monomial::<3>::new(&[48, 0, 0]);
        assert_eq!(order.cmp(&x2, &x0_48), Ordering::Greater);
        for unweighted in ALL_ORDERS {
            assert_eq!(
                unweighted.cmp(&x2, &x0_48),
                Ordering::Less,
                "{} already ranks x_2 below x_0^48",
                unweighted.name()
            );
        }
        // And at weighted degree 49 the weight vector ties x_2 with x_0^49, where the tie-break
        // takes over and prefers the larger exponent at the highest differing index.
        let x0_49 = Monomial::<3>::new(&[49, 0, 0]);
        assert_eq!(
            GRIFFIN_R5.weighted_degree(&x2),
            GRIFFIN_R5.weighted_degree(&x0_49)
        );
        assert_eq!(order.cmp(&x2, &x0_49), Ordering::Greater);
    }

    /// Weighted orders name themselves without distinguishing their weight vectors.
    #[test]
    fn test_weighted_name_is_not_injective() {
        assert_eq!(MonomialOrder::Weighted(&GRIFFIN_R5).name(), "weighted");
        assert_eq!(MonomialOrder::Weighted(&ONES_LEX).name(), "weighted");
        assert_eq!(
            MonomialOrder::Weighted(&GRIFFIN_R5).description(),
            "weighted graded"
        );
    }

    /// `MonomialOrder` is two words, so the signatures that take it by value still pass it in
    /// registers.
    ///
    /// There are 134 of those, threaded through `src/poly/multivariate/`, `src/grobner/f4/` and
    /// `src/grobner/fglm/`, and the reason the weighted variant carries a reference rather than an
    /// inline weight array is to keep this true: an aggregate above two words is passed in memory
    /// under the x86-64 ABI. A future variant that grows the type past this should be a deliberate
    /// decision with a measurement behind it, which is what this assertion forces.
    #[test]
    fn test_the_order_type_stays_two_words() {
        assert_eq!(
            std::mem::size_of::<MonomialOrder>(),
            2 * std::mem::size_of::<usize>()
        );
    }

    /// Two weighted orders are equal when their weight vectors and tie-breaks are, whichever
    /// allocation they came from.
    #[test]
    fn test_weighted_order_equality_is_by_value() {
        let built = MonomialOrder::weighted(&[1, 7, 49], TieBreak::LastVariableFirst).unwrap();
        assert_eq!(built, MonomialOrder::Weighted(&GRIFFIN_R5));
        assert_ne!(built, MonomialOrder::Weighted(&SKEWED_LEX));
        assert_ne!(built, MonomialOrder::GradedReverseLexicographic);
    }

    /// A random admissible weight vector and tie-break.
    fn weighted_order() -> impl Strategy<Value = (Vec<u32>, TieBreak)> {
        (
            vec(1u32..=97, 4),
            prop_oneof![
                Just(TieBreak::Lexicographic),
                Just(TieBreak::ReverseLexicographic),
                Just(TieBreak::LastVariableFirst),
            ],
        )
    }

    proptest! {
        /// Every order axiom, on random weight vectors and random monomials.
        ///
        /// The exhaustive sweeps above cover exponents 0..=2 in three variables, which is where
        /// the tie-breaks differ from each other; this covers weight vectors the fixed set does
        /// not contain. Each case interns one order, so it leaks a few dozen bytes — bounded by
        /// the case count, and the reason the fixed-weight sweeps are not written this way.
        #[test]
        fn test_weighted_order_axioms_on_random_inputs(
            (weights, tie_break) in weighted_order(),
            a in any::<Monomial<4>>(),
            b in any::<Monomial<4>>(),
            c in any::<Monomial<4>>(),
        ) {
            let order = MonomialOrder::weighted(&weights, tie_break).unwrap();

            // Total: antisymmetric, and equal only on equal monomials.
            prop_assert_eq!(order.cmp(&a, &b), order.cmp(&b, &a).reverse());
            prop_assert_eq!(order.cmp(&a, &b) == Ordering::Equal, a == b);

            // Multiplicative, which is what reduction's sorted merge relies on.
            prop_assert_eq!(order.cmp(&a, &b), order.cmp(&(a * c), &(b * c)));

            // Transitive, whenever the hypothesis happens to hold on this triple.
            if order.cmp(&a, &b) == Ordering::Less && order.cmp(&b, &c) == Ordering::Less {
                prop_assert_eq!(order.cmp(&a, &c), Ordering::Less);
            }

            // A well-order: 1 is least, and a proper multiple is strictly greater, so every
            // descending chain shrinks the exponent vector and terminates.
            let one = Monomial::<4>::one();
            prop_assert!(a == one || order.cmp(&one, &a) == Ordering::Less);
            if !c.is_one() {
                prop_assert_eq!(order.cmp(&a, &(a * c)), Ordering::Less);
            }
        }

        /// Unit weights reproduce grlex and grevlex on random monomials.
        #[test]
        fn test_unit_weights_reproduce_the_graded_orders_on_random_inputs(
            a in any::<Monomial<5>>(),
            b in any::<Monomial<5>>(),
        ) {
            static LEX5: WeightedOrder = WeightedOrder::new(&[1; 5], TieBreak::Lexicographic);
            static REV5: WeightedOrder =
                WeightedOrder::new(&[1; 5], TieBreak::ReverseLexicographic);
            prop_assert_eq!(
                MonomialOrder::Weighted(&LEX5).cmp(&a, &b),
                MonomialOrder::GradedLexicographic.cmp(&a, &b)
            );
            prop_assert_eq!(
                MonomialOrder::Weighted(&REV5).cmp(&a, &b),
                MonomialOrder::GradedReverseLexicographic.cmp(&a, &b)
            );
        }
    }

    /// Every monomial in three variables with exponents up to two, which covers the cases where
    /// the three orders differ.
    fn sample_monomials() -> Vec<Monomial<3>> {
        let mut out = Vec::new();
        for i in 0..3u32 {
            for j in 0..3u32 {
                for k in 0..3u32 {
                    out.push(Monomial::new(&[i, j, k]));
                }
            }
        }
        out
    }
}
