//! Monagan–Pearce heap division, behind [`DivisionRoute::Heap`](crate::poly::DivisionRoute).
//!
//! Implemented from the published description only — Monagan and Pearce, *Sparse polynomial
//! division using a heap*, J. Symbolic Comput. 46 (2011) 807–822 — in its quotient-heap form: one
//! heap entry per quotient term whose shifted divisor tail is not yet exhausted.
//!
//! # Why the remainder is bit-identical to the merge route's
//!
//! Both routes take the largest monomial of `dividend - Σ q·g` not yet processed, apply the first
//! divisor whose leading monomial divides it, and set it aside otherwise. The merge route holds
//! that difference as a sorted vector; this one holds it as the dividend's own terms plus a heap of
//! product streams, and sums every stream at the current monomial before deciding. A new quotient
//! term's tail lands strictly below the monomial that created it, because orders are
//! multiplicative, so nothing pending can ever exceed the current monomial. Field arithmetic is
//! exact, so the order the contributions are summed in cannot change the coefficient.

use std::cmp::Ordering;

use crate::{
    poly::{
        multivariate::{
            sparse_multivariate_polynomial::SparseMultiPoly,
            sparse_multivariate_polynomial_arithmetic::{sorted_terms, Reducer},
        },
        MonomialOrder,
    },
    FiniteField, Monomial,
};

/// The terms of `quotient term * reducer tail`, walked from the top down.
struct Stream<const N: usize, F> {
    quotient_monomial: Monomial<N>,
    /// The quotient coefficient negated, so a stream's terms are added rather than subtracted.
    negated_coefficient: F,
    reducer: u32,
    /// Index into the reducer's ascending tail of the term this stream contributes next.
    next: u32,
}

/// A heap entry: the monomial a stream contributes next, held inline so a sift compares without
/// chasing the stream.
#[derive(Clone, Copy)]
struct Entry<const N: usize> {
    monomial: Monomial<N>,
    stream: u32,
}

/// A max-heap of [`Entry`] under a runtime [`MonomialOrder`], which `BinaryHeap` cannot take.
struct Heap<const N: usize> {
    entries: Vec<Entry<N>>,
    order: MonomialOrder,
}

impl<const N: usize> Heap<N> {
    fn top(&self) -> Option<&Entry<N>> {
        self.entries.first()
    }

    fn push(&mut self, entry: Entry<N>) {
        let mut hole = self.entries.len();
        self.entries.push(entry);
        while hole > 0 {
            let parent = (hole - 1) / 2;
            if self
                .order
                .cmp(&self.entries[parent].monomial, &entry.monomial)
                != Ordering::Less
            {
                break;
            }
            self.entries[hole] = self.entries[parent];
            hole = parent;
        }
        self.entries[hole] = entry;
    }

    /// Replace the top with `entry` and restore the heap: one sift where a pop and a push are two.
    fn replace_top(&mut self, entry: Entry<N>) {
        let len = self.entries.len();
        let mut hole = 0;
        loop {
            let mut child = 2 * hole + 1;
            if child >= len {
                break;
            }
            if child + 1 < len
                && self.order.cmp(
                    &self.entries[child].monomial,
                    &self.entries[child + 1].monomial,
                ) == Ordering::Less
            {
                child += 1;
            }
            if self
                .order
                .cmp(&entry.monomial, &self.entries[child].monomial)
                != Ordering::Less
            {
                break;
            }
            self.entries[hole] = self.entries[child];
            hole = child;
        }
        self.entries[hole] = entry;
    }

    fn pop_top(&mut self) {
        let last = self.entries.pop().expect("pop_top on an empty heap");
        if !self.entries.is_empty() {
            self.replace_top(last);
        }
    }
}

/// Divide `dividend` by `reducers`, calling `on_quotient(reducer, monomial, coefficient)` once per
/// quotient term, and return the remainder's terms in descending order.
fn divide<const N: usize, F: FiniteField>(
    dividend: &SparseMultiPoly<N, F>,
    reducers: &[Reducer<N, F>],
    order: MonomialOrder,
    mut on_quotient: impl FnMut(usize, Monomial<N>, F),
) -> Vec<(Monomial<N>, F)> {
    // Ascending, so the dividend's own next term is its last and is popped in constant time. The
    // dividend is never pushed into the heap: it is already sorted, so one comparison against the
    // heap's top is all it costs to merge.
    let mut dividend_terms = sorted_terms(dividend, order);
    let mut heap = Heap {
        entries: Vec::new(),
        order,
    };
    let mut streams: Vec<Stream<N, F>> = Vec::new();
    // Exhausted streams, reused so `streams` stays as small as the live set rather than growing
    // with the quotient.
    let mut free: Vec<u32> = Vec::new();
    let mut remainder: Vec<(Monomial<N>, F)> = Vec::new();

    loop {
        let monomial = match (dividend_terms.last(), heap.top()) {
            (None, None) => break,
            (Some(term), None) => term.0,
            (None, Some(entry)) => entry.monomial,
            (Some(term), Some(entry)) => {
                if order.cmp(&term.0, &entry.monomial) == Ordering::Less {
                    entry.monomial
                } else {
                    term.0
                }
            }
        };

        let mut coefficient = F::zero();
        if dividend_terms.last().is_some_and(|term| term.0 == monomial) {
            coefficient = dividend_terms.pop().expect("just tested").1;
        }
        // Every stream at this monomial is summed before deciding anything; equality is the
        // array comparison, not the order's.
        while let Some(&Entry { stream: id, .. }) = heap.top().filter(|e| e.monomial == monomial) {
            let stream = &mut streams[id as usize];
            let tail = &reducers[stream.reducer as usize].tail;
            coefficient += stream.negated_coefficient * tail[stream.next as usize].1;
            if stream.next == 0 {
                heap.pop_top();
                free.push(id);
            } else {
                stream.next -= 1;
                heap.replace_top(Entry {
                    monomial: &tail[stream.next as usize].0 * &stream.quotient_monomial,
                    stream: id,
                });
            }
        }

        // Cancelled to zero: not a term of the working polynomial, exactly as the merge drops it.
        if coefficient.is_zero() {
            continue;
        }

        let applicable = reducers.iter().enumerate().find_map(|(index, reducer)| {
            monomial
                .checked_div(&reducer.lead_monomial)
                .map(|quotient| (index, quotient))
        });
        let Some((index, quotient_monomial)) = applicable else {
            remainder.push((monomial, coefficient));
            continue;
        };

        let reducer = &reducers[index];
        let quotient_coefficient = match reducer.lead_inverse {
            Some(inverse) => coefficient * inverse,
            None => coefficient,
        };
        on_quotient(index, quotient_monomial, quotient_coefficient);
        let Some(last) = reducer.tail.len().checked_sub(1) else {
            continue;
        };
        let stream = Stream {
            quotient_monomial,
            negated_coefficient: F::zero() - quotient_coefficient,
            reducer: index as u32,
            next: last as u32,
        };
        let id = match free.pop() {
            Some(id) => {
                streams[id as usize] = stream;
                id
            }
            None => {
                streams.push(stream);
                (streams.len() - 1) as u32
            }
        };
        heap.push(Entry {
            monomial: &reducer.tail[last].0 * &quotient_monomial,
            stream: id,
        });
    }

    remainder
}

pub(super) fn normal_form<const N: usize, F: FiniteField>(
    dividend: &SparseMultiPoly<N, F>,
    divisors: &[SparseMultiPoly<N, F>],
    order: MonomialOrder,
) -> SparseMultiPoly<N, F> {
    let reducers: Vec<Reducer<N, F>> = divisors
        .iter()
        .filter(|d| !d.is_zero())
        .map(|d| Reducer::new(d, order))
        .collect();
    if reducers.is_empty() {
        return dividend.clone();
    }
    SparseMultiPoly::new(&divide(dividend, &reducers, order, |_, _, _| {}))
}

pub(super) fn multi_div_rem<const N: usize, F: FiniteField>(
    dividend: &SparseMultiPoly<N, F>,
    divisors: &[SparseMultiPoly<N, F>],
    order: MonomialOrder,
) -> (Vec<SparseMultiPoly<N, F>>, SparseMultiPoly<N, F>) {
    assert!(!divisors.is_empty());
    assert!(divisors.iter().any(|d| !d.is_zero()));

    // Reducers are the nonzero divisors in their given order; `positions` maps each back to its
    // divisor, so a zero divisor keeps its slot and a zero quotient.
    let (positions, reducers): (Vec<usize>, Vec<Reducer<N, F>>) = divisors
        .iter()
        .enumerate()
        .filter(|(_, d)| !d.is_zero())
        .map(|(position, d)| (position, Reducer::new(d, order)))
        .unzip();
    let mut quotient_terms: Vec<Vec<(Monomial<N>, F)>> = vec![Vec::new(); divisors.len()];
    let remainder = divide(
        dividend,
        &reducers,
        order,
        |index, monomial, coefficient| {
            quotient_terms[positions[index]].push((monomial, coefficient));
        },
    );
    let quotients = quotient_terms
        .iter()
        .map(|terms| SparseMultiPoly::new(terms))
        .collect();
    (quotients, SparseMultiPoly::new(&remainder))
}

#[cfg(test)]
mod tests {
    use crate::{
        fields::{Gf256, PrimeFieldElement64, Zp18446744069414584321},
        poly::{
            multivariate::sparse_multivariate_polynomial::SparseMultiPoly, DivisionRoute,
            MonomialOrder,
        },
        FiniteField, Monomial, MultivariatePolynomial,
    };
    use proptest::{collection::vec, prelude::*, test_runner::TestRunner};

    const ALL_ORDERS: [MonomialOrder; 3] = [
        MonomialOrder::Lexicographic,
        MonomialOrder::GradedLexicographic,
        MonomialOrder::GradedReverseLexicographic,
    ];

    /// A polynomial of at most `terms` monomials with every exponent at most `max_exponent`.
    ///
    /// Small exponents are the point: with `Monomial`'s own 0..=16 range a random leading monomial
    /// almost never divides another, so a reduction takes no steps and the heap is never built.
    fn poly<const N: usize, F: FiniteField + Arbitrary>(
        terms: usize,
        max_exponent: u32,
    ) -> impl Strategy<Value = SparseMultiPoly<N, F>> {
        vec((vec(0..=max_exponent, N), F::arbitrary()), 0..=terms).prop_map(|terms| {
            let terms: Vec<(Monomial<N>, F)> = terms
                .into_iter()
                .map(|(exponents, coefficient)| (Monomial::new(&exponents), coefficient))
                .collect();
            SparseMultiPoly::new(&terms)
        })
    }

    /// Heap and merge agree on remainder and quotients, under every order, over random input.
    fn assert_heap_matches_merge<const N: usize, F: FiniteField + Arbitrary>() {
        let strategy = (poly::<N, F>(16, 4), vec(poly::<N, F>(5, 2), 1..5));
        // Cases whose division took more than one step, so the heap held a stream at all.
        let deep = std::cell::Cell::new(0usize);
        TestRunner::deterministic()
            .run(&strategy, |(dividend, divisors)| {
                if divisors.iter().any(|d| !d.is_zero()) {
                    let (quotients, _) =
                        dividend.multi_div_rem(&divisors, MonomialOrder::Lexicographic);
                    if quotients.iter().map(|q| q.terms().len()).sum::<usize>() > 1 {
                        deep.set(deep.get() + 1);
                    }
                }
                for order in ALL_ORDERS {
                    prop_assert_eq!(
                        dividend.normal_form_with(&divisors, order, DivisionRoute::Heap),
                        dividend.normal_form(&divisors, order),
                        "normal_form under {}",
                        order.name()
                    );
                    if divisors.iter().any(|d| !d.is_zero()) {
                        prop_assert_eq!(
                            dividend.multi_div_rem_with(&divisors, order, DivisionRoute::Heap),
                            dividend.multi_div_rem(&divisors, order),
                            "multi_div_rem under {}",
                            order.name()
                        );
                    }
                }
                Ok(())
            })
            .unwrap();
        assert!(
            deep.get() >= 32,
            "only {} of the generated cases took more than one division step",
            deep.get()
        );
    }

    // Bit-identical to the merge route over GF(13), at five arities and all three orders.
    #[test]
    fn test_heap_matches_merge_over_gf13() {
        type F = PrimeFieldElement64<13>;
        assert_heap_matches_merge::<1, F>();
        assert_heap_matches_merge::<2, F>();
        assert_heap_matches_merge::<3, F>();
        assert_heap_matches_merge::<4, F>();
        assert_heap_matches_merge::<6, F>();
    }

    // Bit-identical to the merge route over GF(2^8), whose characteristic 2 makes cancellation
    // common.
    #[test]
    fn test_heap_matches_merge_over_gf256() {
        assert_heap_matches_merge::<1, Gf256>();
        assert_heap_matches_merge::<2, Gf256>();
        assert_heap_matches_merge::<3, Gf256>();
        assert_heap_matches_merge::<4, Gf256>();
        assert_heap_matches_merge::<6, Gf256>();
    }

    // Bit-identical to the merge route over the 64-bit Goldilocks prime.
    #[test]
    fn test_heap_matches_merge_over_goldilocks() {
        type F = Zp18446744069414584321;
        assert_heap_matches_merge::<1, F>();
        assert_heap_matches_merge::<2, F>();
        assert_heap_matches_merge::<3, F>();
        assert_heap_matches_merge::<4, F>();
        assert_heap_matches_merge::<6, F>();
    }

    type F13 = PrimeFieldElement64<13>;

    fn parse<const N: usize>(text: &str, vars: [&str; N]) -> MultivariatePolynomial<N, F13> {
        MultivariatePolynomial::parse(text, vars).expect("a polynomial in these variables")
    }

    /// Both routes' remainders and quotients for `dividend` modulo `divisors`, asserted equal.
    fn assert_routes_agree<const N: usize>(dividend: &str, divisors: &[&str], vars: [&str; N]) {
        let f = parse(dividend, vars);
        let ds: Vec<_> = divisors.iter().map(|d| parse(d, vars)).collect();
        for order in ALL_ORDERS {
            assert_eq!(
                f.normal_form_with(&ds, order, DivisionRoute::Heap),
                f.normal_form(&ds, order),
                "{dividend} modulo {divisors:?} under {}",
                order.name()
            );
            if ds.iter().any(|d| !d.is_zero()) {
                assert_eq!(
                    f.multi_div_rem_with(&ds, order, DivisionRoute::Heap),
                    f.multi_div_rem(&ds, order),
                    "{dividend} by {divisors:?} under {}",
                    order.name()
                );
            }
        }
    }

    // The merge window's three boundary positions — below, above and strictly inside the working
    // polynomial — plus the cancelling case, through the heap route.
    #[test]
    fn test_heap_matches_merge_at_each_window_boundary() {
        let vars = ["x"];
        for (dividend, divisor) in [
            ("x^9 + x^8 + x^7", "x^9 - 1"),
            ("x^9 + x + 1", "x^9 - x^8"),
            ("x^9 + x^6 + x^3 + 1", "x^9 - x^5"),
            ("x^12 + x^7 + x^2", "x^12 - x^4"),
            ("x^9 + x^4", "x^9 + x^4"),
        ] {
            assert_routes_agree(dividend, &[divisor], vars);
        }
    }

    // A zero dividend has a zero remainder and zero quotients on the heap route.
    #[test]
    fn test_heap_divides_zero_to_zero() {
        let vars = ["x", "y"];
        assert_routes_agree("0", &["x + y"], vars);
        let (quotients, remainder) = parse("0", vars).multi_div_rem_with(
            &[parse("x", vars)],
            MonomialOrder::Lexicographic,
            DivisionRoute::Heap,
        );
        assert!(remainder.is_zero());
        assert!(quotients.iter().all(|q| q.is_zero()));
    }

    // A nonzero constant divisor divides everything, so the remainder is zero and the quotient is
    // the dividend scaled by the constant's inverse.
    #[test]
    fn test_heap_divides_by_a_constant() {
        let vars = ["x", "y"];
        assert_routes_agree("x^3*y + 2*x + 5", &["3"], vars);
        assert_routes_agree("7", &["3"], vars);
        assert_routes_agree("x^3*y + 2*x + 5", &["x^5", "3"], vars);
        let (_, remainder) = parse("x^3*y + 2*x + 5", vars).multi_div_rem_with(
            &[parse("3", vars)],
            MonomialOrder::Lexicographic,
            DivisionRoute::Heap,
        );
        assert!(remainder.is_zero());
    }

    // A constant dividend is irreducible by every non-constant divisor and is its own remainder.
    #[test]
    fn test_heap_leaves_a_constant_dividend_alone() {
        let vars = ["x", "y"];
        assert_routes_agree("4", &["x + 1", "y^2"], vars);
    }

    // One divisor: with a tail, without one, equal to the dividend, dividing nothing, non-monic.
    #[test]
    fn test_heap_divides_by_one_divisor() {
        let vars = ["x", "y", "z"];
        assert_routes_agree("x^5 + 1", &["x^2 + 1"], vars);
        assert_routes_agree("x^2*y + x*z + y^3", &["x*y"], vars);
        assert_routes_agree("x^2 + 2*x*y + y^2", &["x^2 + 2*x*y + y^2"], vars);
        assert_routes_agree("x + y + z", &["x^9"], vars);
        assert_routes_agree("x^3 + x^2*y + z", &["3*x - y + 2"], vars);
    }

    // Zero divisors are skipped by the search and get zero quotients, wherever they sit.
    #[test]
    fn test_heap_ignores_zero_divisors() {
        let vars = ["x", "y"];
        assert_routes_agree("x^2 + y", &["y", "0"], vars);
        assert_routes_agree("x^2 + y", &["0", "y"], vars);
        let f = parse("x^2 + y", vars);
        for order in ALL_ORDERS {
            assert_eq!(f.normal_form_with(&[], order, DivisionRoute::Heap), f);
            let zero = SparseMultiPoly::zero();
            assert_eq!(f.normal_form_with(&[zero], order, DivisionRoute::Heap), f);
        }
    }

    // Divisor order decides which divisor applies, and the heap route honours the same order.
    #[test]
    fn test_heap_applies_the_first_dividing_divisor() {
        let vars = ["x", "y"];
        assert_routes_agree("x^2*y^2 + x*y + 1", &["x*y - 1", "y^2 - 1"], vars);
        assert_routes_agree("x^2*y^2 + x*y + 1", &["y^2 - 1", "x*y - 1"], vars);
    }

    // `multi_div_rem_with` keeps `multi_div_rem`'s refusal of an empty divisor list.
    #[test]
    #[should_panic]
    fn test_heap_multi_div_rem_refuses_no_divisors() {
        let f = parse("x", ["x"]);
        let _ = f.multi_div_rem_with(&[], MonomialOrder::Lexicographic, DivisionRoute::Heap);
    }

    // `multi_div_rem_with` keeps `multi_div_rem`'s refusal of an all-zero divisor list.
    #[test]
    #[should_panic]
    fn test_heap_multi_div_rem_refuses_only_zero_divisors() {
        let f = parse("x", ["x"]);
        let zero = SparseMultiPoly::zero();
        let _ = f.multi_div_rem_with(&[zero], MonomialOrder::Lexicographic, DivisionRoute::Heap);
    }
}
