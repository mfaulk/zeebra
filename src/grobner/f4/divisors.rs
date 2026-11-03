//! The leading monomials of a basis, arranged so that a divisibility query need not touch them all.
//!
//! The index is a pruning device over the fold the linear scan performs, never a heuristic. It has
//! to return the *same* divisor the scan returns — a different divisor is a different multiplier,
//! hence a different matrix row, hence a different matrix — so each structure here is paired with
//! the necessary condition that justifies skipping what it skips:
//!
//! - `LM | u` requires `deg LM <= deg u`, so grouping the leading monomials by total degree lets
//!   every group above the query's degree be skipped without being looked at.
//! - Under a graded order a leading monomial of higher degree is strictly larger, so
//!   [`ReducerSelection::LargestLeadingMonomial`] can take the groups in descending degree and
//!   stop at the first that holds a divisor. Lex admits no such shortcut.
//!
//! The two policies need the degree grouping laid out differently, and the reason is worth stating
//! because getting it wrong costs more than it saves. First-applicable wants the *smallest* index
//! that divides, so it has to see the candidates in index order; walking one degree group after
//! another does not, and then a divisor found in a low-degree group does not license skipping a
//! lower-indexed one in a higher group. Measured, that walk examines *more* elements than the
//! plain scan on the instances where the scan is worst. So first-applicable instead reads a
//! precomputed ascending list of the indices whose degree is at most the query's — a subsequence
//! of the scan, in the scan's own order, which can only be shorter. The largest-leading-monomial
//! policy has no early exit to lose and uses the per-degree groups directly.

use std::cmp::Ordering;

use crate::{
    grobner::f4::{options::ReducerSelection, symbolic::MonicElement},
    poly::MonomialOrder,
    FiniteField, Monomial,
};

/// Total degrees at or above this bound share one group.
///
/// Bounded so that a single pathological generator cannot make the group vector proportional to an
/// exponent. Sharing is sound because a query is keyed the same way: an element in the shared group
/// has degree at least the bound, so it can only divide a monomial whose degree also reaches it.
const DEGREE_BOUND: u64 = 63;

/// The group a monomial of total degree `degree` belongs to, and the largest group a query of that
/// degree may draw from.
fn degree_key(degree: u64) -> usize {
    degree.min(DEGREE_BOUND) as usize
}

/// True when a monomial of strictly higher total degree is necessarily larger under `order`.
fn respects_degree(order: MonomialOrder) -> bool {
    match order {
        MonomialOrder::Lexicographic => false,
        MonomialOrder::GradedLexicographic | MonomialOrder::GradedReverseLexicographic => true,
    }
}

/// The leading monomials of a basis, grouped by total degree.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DivisorIndex<const N: usize> {
    order: MonomialOrder,

    /// How many elements have been recorded.
    ///
    /// The leading monomials themselves are not copied here: a query reads them from the basis,
    /// which is the array the plain scan read, so the lookup does not pull a second array through
    /// the cache alongside it.
    elements: usize,

    /// `by_degree[k]`: the indices whose degree key is exactly `k`, ascending.
    by_degree: Vec<Vec<usize>>,

    /// `at_most[k]`: the indices whose degree key is at most `k`, ascending.
    ///
    /// The prefix sums of `by_degree`, materialized rather than merged on demand so that a
    /// first-applicable scan pays nothing per step beyond what the plain scan pays. Costs
    /// `O(elements * distinct degrees)` indices, which for a basis whose leading monomials span a
    /// handful of degrees is a small multiple of the basis itself.
    at_most: Vec<Vec<usize>>,
}

impl<const N: usize> DivisorIndex<N> {
    pub fn new(order: MonomialOrder) -> Self {
        Self {
            order,
            elements: 0,
            by_degree: Vec::new(),
            at_most: Vec::new(),
        }
    }

    pub fn len(&self) -> usize {
        self.elements
    }

    pub fn is_empty(&self) -> bool {
        self.elements == 0
    }

    /// Record the leading monomial of the next basis element.
    ///
    /// Append-only, which is what the ascending order of every index list rests on, and what the
    /// basis itself does.
    pub fn push(&mut self, lead: Monomial<N>) {
        let index = self.elements;
        self.elements += 1;

        let key = degree_key(lead.degree());
        if self.by_degree.len() <= key {
            self.by_degree.resize(key + 1, Vec::new());
        }
        self.by_degree[key].push(index);

        // A key above everything seen so far opens new prefix lists, each of which starts as a
        // copy of the widest list there was — every element so far has a smaller key, so every one
        // of them belongs to it.
        if self.at_most.len() <= key {
            let widest = self.at_most.last().cloned().unwrap_or_default();
            while self.at_most.len() <= key {
                self.at_most.push(widest.clone());
            }
        }
        for list in &mut self.at_most[key..] {
            list.push(index);
        }
    }

    /// The groups that can hold a divisor of a monomial of total degree `degree`, ascending.
    fn candidates(&self, degree: u64) -> impl DoubleEndedIterator<Item = &Vec<usize>> {
        let groups = (degree_key(degree) + 1).min(self.by_degree.len());
        self.by_degree[..groups].iter()
    }

    /// The divisor `selection` names, with the quotient, counting the elements looked at.
    ///
    /// `examined` counts the basis elements the lookup looked at — the same quantity the linear
    /// scan reports, so that the two are comparable.
    pub fn find<F: FiniteField>(
        &self,
        elements: &[MonicElement<N, F>],
        monomial: &Monomial<N>,
        selection: ReducerSelection,
        examined: &mut usize,
    ) -> Option<(usize, Monomial<N>)> {
        debug_assert_eq!(elements.len(), self.elements);
        let degree = monomial.degree();
        match selection {
            ReducerSelection::FirstApplicable => {
                self.first_applicable(elements, monomial, degree, examined)
            }
            ReducerSelection::LargestLeadingMonomial => {
                self.largest(elements, monomial, degree, examined)
            }
        }
    }

    /// The smallest basis index whose leading monomial divides `monomial`.
    ///
    /// Reads the one prefix list the query's degree admits, which is the plain scan restricted to
    /// a subsequence of itself: same order, same first hit, no more elements looked at.
    fn first_applicable<F: FiniteField>(
        &self,
        elements: &[MonicElement<N, F>],
        monomial: &Monomial<N>,
        degree: u64,
        examined: &mut usize,
    ) -> Option<(usize, Monomial<N>)> {
        // A query above every recorded degree may draw on every element, which is the widest list.
        let key = degree_key(degree).min(self.at_most.len().checked_sub(1)?);
        for &index in &self.at_most[key] {
            *examined += 1;
            if let Some(quotient) = monomial.checked_div(&elements[index].leading_monomial) {
                return Some((index, quotient));
            }
        }
        None
    }

    /// The largest leading monomial that divides `monomial`, ties broken by the smaller index.
    fn largest<F: FiniteField>(
        &self,
        elements: &[MonicElement<N, F>],
        monomial: &Monomial<N>,
        degree: u64,
        examined: &mut usize,
    ) -> Option<(usize, Monomial<N>)> {
        // Taking the groups in descending degree only settles the answer when degree decides the
        // order, and when the shared high-degree group — whose members have different degrees — is
        // not among the candidates.
        let descending_degree_decides = respects_degree(self.order)
            && !(degree >= DEGREE_BOUND && self.by_degree.len() > DEGREE_BOUND as usize);

        let mut best: Option<(usize, Monomial<N>)> = None;
        for group in self.candidates(degree).rev() {
            for &index in group {
                *examined += 1;
                let lead = &elements[index].leading_monomial;
                let Some(quotient) = monomial.checked_div(lead) else {
                    continue;
                };
                // Strictly greater, so among equal leading monomials the smallest index — which,
                // the lists being ascending, is the one already held — wins.
                let beats_the_best = match best {
                    None => true,
                    Some((incumbent, _)) => {
                        self.order.cmp(lead, &elements[incumbent].leading_monomial)
                            == Ordering::Greater
                    }
                };
                if beats_the_best {
                    best = Some((index, quotient));
                }
            }
            if descending_degree_decides && best.is_some() {
                break;
            }
        }
        best
    }
}

#[cfg(test)]
mod tests {
    use super::{DivisorIndex, DEGREE_BOUND};
    use crate::{
        fields::Zp13,
        grobner::f4::{options::ReducerSelection, symbolic::MonicBasis, SymbolicCounts},
        poly::MonomialOrder,
        Monomial, MultivariatePolynomial,
    };
    use rand::{prelude::StdRng, Rng, SeedableRng};

    type F = Zp13;
    const ALL_ORDERS: [MonomialOrder; 3] = [
        MonomialOrder::Lexicographic,
        MonomialOrder::GradedLexicographic,
        MonomialOrder::GradedReverseLexicographic,
    ];

    /// A basis of single-term polynomials, so the leading monomials are exactly `leads`.
    fn basis_with_leads(leads: &[Monomial<4>], order: MonomialOrder) -> MonicBasis<4, F> {
        let polynomials: Vec<MultivariatePolynomial<4, F>> = leads
            .iter()
            .map(|lead| MultivariatePolynomial::from(*lead))
            .collect();
        MonicBasis::new(&polynomials, order)
    }

    fn random_monomial(rng: &mut StdRng, max_exponent: u32) -> Monomial<4> {
        let exponents: Vec<u32> = (0..4).map(|_| rng.gen_range(0..=max_exponent)).collect();
        Monomial::new(&exponents)
    }

    /// The index returns the identical divisor and quotient the reference scan does, under both
    /// policies, over randomized bases and query monomials in all three orders.
    #[test]
    fn test_index_agrees_with_the_scan() {
        let mut rng = StdRng::seed_from_u64(20260211);
        for order in ALL_ORDERS {
            for _ in 0..40 {
                // Leading monomials of degree at least one, so no element divides everything, plus
                // repeats drawn from a small range so equal leads and the tiebreaker occur.
                let size = rng.gen_range(1..=12);
                let leads: Vec<Monomial<4>> = (0..size)
                    .map(|_| {
                        let mut lead = random_monomial(&mut rng, 2);
                        if lead.is_one() {
                            lead = Monomial::new(&[1, 0, 0, 0]);
                        }
                        lead
                    })
                    .collect();
                let basis = basis_with_leads(&leads, order);

                for _ in 0..60 {
                    let monomial = random_monomial(&mut rng, 4);
                    let mut counts = SymbolicCounts::default();
                    assert_eq!(
                        basis.find_divisor_with(
                            &monomial,
                            ReducerSelection::FirstApplicable,
                            &mut counts
                        ),
                        basis.find_divisor(&monomial),
                        "{}: first-applicable disagreed on {} over {:?}",
                        order.name(),
                        monomial,
                        leads
                    );
                    assert_eq!(
                        basis.find_divisor_with(
                            &monomial,
                            ReducerSelection::LargestLeadingMonomial,
                            &mut counts
                        ),
                        basis.find_largest_divisor(&monomial),
                        "{}: largest-leading-monomial disagreed on {} over {:?}",
                        order.name(),
                        monomial,
                        leads
                    );
                }
            }
        }
    }

    /// A leading monomial past the degree bound shares the top group and is still found.
    #[test]
    fn test_index_finds_a_divisor_past_the_degree_bound() {
        let high = DEGREE_BOUND as u32 + 3;
        for order in ALL_ORDERS {
            let leads = [
                Monomial::<4>::new(&[high, 0, 0, 0]),
                Monomial::<4>::new(&[2, 0, 0, 0]),
            ];
            let basis = basis_with_leads(&leads, order);
            let query = Monomial::<4>::new(&[high + 1, 1, 0, 0]);

            let mut counts = SymbolicCounts::default();
            assert_eq!(
                basis.find_divisor_with(&query, ReducerSelection::FirstApplicable, &mut counts),
                basis.find_divisor(&query),
                "{}",
                order.name()
            );
            assert_eq!(
                basis.find_divisor_with(
                    &query,
                    ReducerSelection::LargestLeadingMonomial,
                    &mut counts
                ),
                basis.find_largest_divisor(&query),
                "{}",
                order.name()
            );
        }
    }

    /// The degree buckets skip elements whose leading monomial is too large to divide.
    #[test]
    fn test_degree_buckets_prune() {
        let order = MonomialOrder::GradedReverseLexicographic;
        // Nine leads of degree four and one of degree one, so a degree-one query can only be
        // divided by the last and should not look at the other nine.
        let mut leads: Vec<Monomial<4>> = (0..9).map(|_| Monomial::new(&[2, 2, 0, 0])).collect();
        leads.push(Monomial::new(&[0, 0, 1, 0]));
        let basis = basis_with_leads(&leads, order);

        let mut counts = SymbolicCounts::default();
        assert_eq!(
            basis.find_divisor_with(
                &Monomial::new(&[0, 0, 1, 0]),
                ReducerSelection::FirstApplicable,
                &mut counts
            ),
            Some((9, Monomial::new(&[0, 0, 0, 0])))
        );
        assert_eq!(
            counts.divisor_scan_steps, 1,
            "the degree-four leads should not have been looked at"
        );
    }

    /// An empty index finds nothing and examines nothing.
    #[test]
    fn test_empty_index() {
        let index = DivisorIndex::<4>::new(MonomialOrder::Lexicographic);
        assert!(index.is_empty());
        assert_eq!(index.len(), 0);
        let mut examined = 0;
        let elements: [crate::grobner::f4::MonicElement<4, F>; 0] = [];
        assert_eq!(
            index.find(
                &elements,
                &Monomial::new(&[1, 2, 3, 4]),
                ReducerSelection::FirstApplicable,
                &mut examined
            ),
            None
        );
        assert_eq!(examined, 0);
    }
}
