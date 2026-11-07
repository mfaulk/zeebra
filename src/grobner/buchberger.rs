//! Buchberger's algorithm for computing a Gröbner basis.
//!
//! Critical pairs are processed incrementally from a queue rather than by rescanning every pair of
//! basis elements on each pass. When a reduction yields a new basis element, only the pairs
//! involving that element are enqueued; everything already handled stays handled.
//!
//! Pair selection and the product criterion live in [`super::pairs`], which F4 shares.
//!
//! [`super::reference::buchberger_reference`] keeps the textbook formulation for comparison, and
//! the two are checked against each other over the benchmark families and all three orders.
//!
//! See Sec 2.7 of Ideals, Varieties, and Algorithms by Cox, Little, and O'Shea.

use std::collections::HashMap;

use crate::{
    grobner::{
        pairs::{divides, CriterionCounts, PairCriteria, PairQueue},
        s_polynomial::s_polynomial,
    },
    poly::MonomialOrder,
    FiniteField, Monomial, MultivariatePolynomial,
};

/// Counters describing the work a Gröbner basis computation performed.
///
/// Reported so that a change in runtime can be attributed — fewer pairs reduced, more pairs
/// eliminated, smaller intermediate polynomials — rather than guessed at.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Statistics {
    /// Pairs taken off the queue.
    pub pairs_considered: usize,

    /// Pairs discarded by Buchberger's first criterion, without forming an S-polynomial.
    pub pairs_eliminated_by_product_criterion: usize,

    /// Pairs whose S-polynomial was actually reduced.
    pub pairs_reduced: usize,

    /// Reductions that produced zero, and so contributed nothing to the basis.
    pub zero_reductions: usize,

    /// Basis elements appended during the computation, before interreduction.
    pub elements_added: usize,

    /// The largest total degree of any lcm selected.
    pub max_pair_degree: u64,

    /// The largest number of terms in any polynomial produced by a reduction.
    pub max_terms: usize,

    /// Pairs discarded, per criterion.
    ///
    /// `pairs_eliminated_by_product_criterion` is `criteria.product`; the other two fields are
    /// the only record of what the chain criterion and Gebauer–Möller did, and
    /// `criteria.gebauer_moller` counts pairs that were never selected and so are not in
    /// `pairs_considered` either.
    pub criteria: CriterionCounts,
}

/// The reduced Gröbner basis for the given polynomials, with respect to the given monomial order.
///
/// # Arguments
/// * `f` - Polynomials <f_0, ..., f_{s-1}>. Zero generators are ignored.
/// * `order` - A monomial order.
///
/// Returns the reduced Gröbner basis G for the ideal I = <f_0, ..., f_{s-1}>, sorted by leading
/// monomial in descending order. The empty basis is returned for the zero ideal.
pub fn buchberger<const N: usize, F: FiniteField>(
    f: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
) -> Vec<MultivariatePolynomial<N, F>> {
    buchberger_with_statistics(f, order).0
}

/// As [`buchberger`], additionally reporting the work performed.
pub fn buchberger_with_statistics<const N: usize, F: FiniteField>(
    f: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
) -> (Vec<MultivariatePolynomial<N, F>>, Statistics) {
    buchberger_with_criteria(f, order, &PairCriteria::default())
}

/// As [`buchberger_with_statistics`], under the given pair-elimination criteria.
///
/// A criterion is a theorem that a pair's S-polynomial reduces to zero modulo relations already
/// available, so enabling one must leave the computed reduced Gröbner basis unchanged. That makes
/// [`PairCriteria::NONE`] the reference every criterion is checked against, and it is the reason
/// this entry point exists at all: without it the criteria could only be compared through F4, and
/// a disagreement would not say which engine was wrong.
pub fn buchberger_with_criteria<const N: usize, F: FiniteField>(
    f: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
    criteria: &PairCriteria,
) -> (Vec<MultivariatePolynomial<N, F>>, Statistics) {
    let mut statistics = Statistics::default();

    // A zero generator contributes nothing to the ideal, and would otherwise reach
    // `leading_coefficient().inverse()` with a zero coefficient. Duplicates are dropped too, so
    // they cannot produce pairs with themselves.
    let mut basis: Vec<MultivariatePolynomial<N, F>> = Vec::new();
    for p in f.iter().filter(|p| !p.is_zero()) {
        let monic = p.scale(&p.leading_coefficient(order).inverse());
        if !basis.contains(&monic) {
            basis.push(monic);
        }
    }
    if basis.is_empty() {
        return (Vec::new(), statistics);
    }

    // The leading monomials, maintained alongside the basis. Pair handling needs these and
    // nothing else, and `leading_monomial` is a scan of a polynomial's whole term map — which
    // generating the pairs of a newly appended element would otherwise repeat once per pair.
    let mut leads: Vec<Monomial<N>> = basis.iter().map(|p| p.leading_monomial(order)).collect();

    let mut counts = CriterionCounts::default();
    let mut pending = PairQueue::seeded_from_leads(&leads, criteria, &mut counts);

    while let Some(pair) = pending.pop() {
        statistics.pairs_considered += 1;
        statistics.max_pair_degree = statistics.max_pair_degree.max(pair.degree);

        // The selection-time criteria: Buchberger's first criterion and the chain criterion,
        // both of which say S(left, right) is guaranteed to reduce to zero modulo relations the
        // computation already has, so the reduction can be skipped without affecting the result.
        let before = counts;
        if pending.is_discarded(&pair, &leads, criteria, &mut counts) {
            statistics.pairs_eliminated_by_product_criterion += counts.product - before.product;
            continue;
        }

        statistics.pairs_reduced += 1;
        let left = &basis[pair.left];
        let right = &basis[pair.right];
        let remainder = s_polynomial(left, right, order).normal_form(&basis, order);

        if remainder.is_zero() {
            statistics.zero_reductions += 1;
            continue;
        }

        statistics.max_terms = statistics.max_terms.max(remainder.terms().len());

        // Monic, so that the basis is normalized as it is built rather than only at the end.
        let monic = remainder.scale(&remainder.leading_coefficient(order).inverse());
        let added = basis.len();
        leads.push(monic.leading_monomial(order));
        basis.push(monic);
        statistics.elements_added += 1;

        // Only the pairs involving the new element are new. This is what makes the processing
        // incremental: the textbook formulation rebuilds every pair on every pass.
        pending.push_pairs_from_leads(&leads, added, criteria, &mut counts);
    }

    statistics.criteria = counts;

    (reduce_grobner_basis(basis, order), statistics)
}

/// Finds a minimal Grobner basis, paired with the leading monomial of each element kept.
///
/// # Arguments
/// * `g` - A Grobner basis.
/// * `order` - A monomial order.
///
/// A minimal Grobner basis has two properties:
/// 2. The leading coefficient of each polynomial is 1.
/// 1. No leading term of any polynomial in the basis is divisible by the leading term of any other polynomial in the basis.
///
/// The leading monomials are returned rather than recomputed because taking one is a scan of a
/// polynomial's whole term map, and both this function and its caller need all of them.
fn minimize_grobner_basis<const N: usize, F: FiniteField>(
    g: Vec<MultivariatePolynomial<N, F>>,
    order: MonomialOrder,
) -> Vec<(Monomial<N>, MultivariatePolynomial<N, F>)> {
    // Scale each polynomial to have leading coefficient 1, dropping zeros and duplicates.
    // First-occurrence order is preserved, so the outcome does not depend on hashing.
    //
    // Two polynomials can only be equal if their leading monomial and term count agree, so a
    // candidate is compared against the elements that share both and not against every element
    // kept so far. The full scan was a polynomial equality per element per element.
    let mut monic: Vec<(Monomial<N>, MultivariatePolynomial<N, F>)> = Vec::with_capacity(g.len());
    let mut by_shape: HashMap<(Monomial<N>, usize), Vec<usize>> = HashMap::new();
    // `g` is consumed and each element scaled **in place**. `scale` allocated a fresh term map per
    // element, which was a third full copy of the basis live beside the caller's two — #304. At
    // twenty variables a term is ~88 bytes of payload before hashbrown's slack, none of it covered
    // by `max_live_nonzeros` or `max_live_bytes`.
    for mut p in g.into_iter().filter(|p| !p.is_zero()) {
        let lead = p.leading_monomial(order);
        p.scale_assign(&p.leading_coefficient(order).inverse());
        let scaled = p;
        let shape = (lead, scaled.terms().len());
        let same_shape = by_shape.entry(shape).or_default();
        if same_shape.iter().any(|&i| monic[i].1 == scaled) {
            continue;
        }
        same_shape.push(monic.len());
        monic.push((lead, scaled));
    }

    // Drop any element whose leading term is divisible by another's, which is exactly
    // LT(p) in <LT(G \ {p})> for a set of leading terms.
    //
    // Two elements can share a leading monomial, in which case each divides the other and one
    // must go. Indices decide which, so the result is reproducible; a `HashSet` here made the
    // surviving element depend on iteration order.
    let mut keep = vec![true; monic.len()];
    for i in 0..monic.len() {
        for j in 0..monic.len() {
            if i == j || !keep[j] {
                continue;
            }
            if divides(&monic[j].0, &monic[i].0) {
                keep[i] = false;
                break;
            }
        }
    }

    monic
        .into_iter()
        .zip(keep)
        .filter(|(_, keep)| *keep)
        .map(|(element, _)| element)
        .collect()
}

/// Reduce a Grobner basis
/// # Arguments
/// * `g` - A Groebner basis.
/// * `order` - A monomial order.
///
/// A reduced Groebner basis has two properties:
/// 1. The leading coefficient of each polynomial is 1.
/// 2. For all p in G,no monomial of p lies in <LT(G \ {p})>.
pub(crate) fn reduce_grobner_basis<const N: usize, F: FiniteField>(
    g: Vec<MultivariatePolynomial<N, F>>,
    order: MonomialOrder,
) -> Vec<MultivariatePolynomial<N, F>> {
    match reduce_grobner_basis_until(g, order, || false) {
        Ok(reduced) => reduced,
        // Unreachable: the predicate above is constant `false`.
        Err(stopped) => unreachable!(
            "a never-stopping predicate stopped after {} elements",
            stopped.elements_reduced
        ),
    }
}

/// How far [`reduce_grobner_basis_until`] had got when its caller asked it to stop.
///
/// Carries the progress rather than only the fact, because the stage is **not** a loop over
/// batches: a caller reporting a stop here has no degree to name, and the element counts are the
/// only honest measure of how far a run got. See [`F4Error::InterreductionTimeBudgetExceeded`].
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct InterreductionStopped {
    /// Basis elements whose normal form had been written back before the stop.
    pub elements_reduced: usize,
    /// Elements in the minimized basis, which is how many the stage had to do.
    pub elements: usize,
}

/// [`reduce_grobner_basis`], asking `should_stop` before each element.
///
/// # Why this stage needs a stop at all
///
/// Final interreduction runs **after** F4's batch loop, so a per-batch wall-clock check cannot see
/// it: a budget can be honored at every check and then overrun inside this function. That is not a
/// corner case. #349 measured this stage at **80.4%** of `mq-random-10`, so on the instance M25
/// used to measure Zeebra against Singular, four fifths of the computation sat in a stage no clock
/// was consulted in — which is how a 120-second budget returned at ten minutes (#395).
///
/// # Granularity, and what it does not fix
///
/// One element. A single `normal_form` against a large basis can be arbitrarily long, so the
/// elapsed time at a stop is the budget plus whatever that one reduction still needed — the same
/// caveat the batch-loop check carries, and an external supervisor is still the right backstop.
/// What this removes is the unbounded case, where the stage is never checked at all.
///
/// # Errors
/// [`InterreductionStopped`] when `should_stop` returns true, with the element counts. The partial
/// basis is deliberately **not** returned: `F4Error`'s contract is that a successful return is
/// always a complete reduced Gröbner basis, and a half-interreduced basis handed back as success
/// is exactly the confusion that contract exists to prevent.
pub(crate) fn reduce_grobner_basis_until<const N: usize, F: FiniteField>(
    g: Vec<MultivariatePolynomial<N, F>>,
    order: MonomialOrder,
    mut should_stop: impl FnMut() -> bool,
) -> Result<Vec<MultivariatePolynomial<N, F>>, InterreductionStopped> {
    let mut minimal = minimize_grobner_basis(g, order);

    // Ascending by leading monomial, which is the whole optimization.
    //
    // Each element is replaced by its remainder on division by the others, and a divisor's *tail*
    // is what gets substituted in. Reducing in ascending order and writing each remainder back in
    // place means every divisor whose leading monomial is below the element's has already been
    // reduced, so the substitution introduces monomials that are already in normal form instead of
    // monomials that have to be reduced again through the whole basis. On katsura-6 under lex —
    // whose basis is in shape position, five linear elements over one univariate of degree 32 —
    // that is the difference between 2.5 seconds and a millisecond: reducing x1's tail against an
    // unreduced x2 substituted 31 terms that each needed reducing against an unreduced x3, and so
    // on down the chain.
    //
    // Neither the order nor the in-place update can change the result. A remainder r is congruent
    // to its element modulo the ideal, has the element's leading monomial — minimization left it
    // divisible by no other leading monomial, so division never cancels it — and has no monomial
    // divisible by any other element's leading monomial. Two elements with those three properties
    // differ by an ideal member all of whose monomials are irreducible, which is zero. So r is
    // determined by the element's leading monomial alone, and in particular does not depend on
    // which divisor was applied first or on whether a divisor's tail had been reduced yet: those
    // only change how many steps the reduction takes. Reducing an element also never changes its
    // leading monomial, which is all that divisibility is tested against.
    minimal.sort_by(|a, b| order.cmp(&a.0, &b.0));
    let mut reduced: Vec<MultivariatePolynomial<N, F>> =
        minimal.into_iter().map(|(_, p)| p).collect();

    // The element being reduced is swapped to the end so that the others are a contiguous slice,
    // which is what `normal_form` takes. The alternative, and what this replaced, is to clone all
    // `n - 1` of them once per element before computing anything.
    let last = reduced.len().saturating_sub(1);
    let elements = reduced.len();
    if reduced.len() > 1 {
        for i in 0..reduced.len() {
            // Before the element, not after: a stop that has already paid for the reduction it
            // was meant to prevent is not a stop.
            if should_stop() {
                return Err(InterreductionStopped {
                    elements_reduced: i,
                    elements,
                });
            }
            reduced.swap(i, last);
            let p = std::mem::take(&mut reduced[last]);
            let remainder = p.normal_form(&reduced[..last], order);
            debug_assert!(
                !remainder.is_zero(),
                "reducing a minimal basis element cannot cancel its leading term"
            );
            reduced[last] = remainder;
            reduced.swap(i, last);
        }
    }

    // Descending by leading monomial, so the basis is returned in a canonical order.
    // Minimization leaves the leading monomials distinct, so this is a total order on the
    // result, and a reduced Gröbner basis is unique as a set — which makes the sequence unique
    // too. Without this the order came from `HashSet` iteration and varied between runs.
    reduced.reverse();
    Ok(reduced)
}

#[cfg(test)]
mod interreduction_stop_tests {
    use super::{reduce_grobner_basis, reduce_grobner_basis_until};
    use crate::{fields::Zp13, poly::MonomialOrder, MultivariatePolynomial};

    const VARS: [&str; 2] = ["x", "y"];

    fn basis() -> Vec<MultivariatePolynomial<2, Zp13>> {
        // Two elements, so the interreduction loop runs at all.
        ["x^2 + y", "y^2 + x"]
            .iter()
            .map(|t| MultivariatePolynomial::parse(t, VARS).expect("a bivariate polynomial"))
            .collect()
    }

    /// A never-stopping predicate reproduces `reduce_grobner_basis` exactly.
    #[test]
    fn a_never_stopping_predicate_is_the_unbounded_result() {
        let g = basis();
        let order = MonomialOrder::GradedReverseLexicographic;
        let bounded = reduce_grobner_basis_until(g.clone(), order, || false).expect("never stops");
        assert_eq!(bounded, reduce_grobner_basis(g, order));
    }

    /// An always-stopping predicate stops before reducing any element.
    #[test]
    fn an_always_stopping_predicate_stops_before_the_first_element() {
        let g = basis();
        let stopped =
            reduce_grobner_basis_until(g, MonomialOrder::GradedReverseLexicographic, || true)
                .expect_err("an always-true predicate must stop");
        assert_eq!(stopped.elements_reduced, 0, "nothing was paid for");
        assert_eq!(stopped.elements, 2, "and it reports the work it had to do");
    }

    /// The predicate is consulted once per element, so a stop after the first is reported as such.
    #[test]
    fn the_predicate_is_consulted_once_per_element() {
        let g = basis();
        let mut calls = 0usize;
        let stopped =
            reduce_grobner_basis_until(g, MonomialOrder::GradedReverseLexicographic, || {
                calls += 1;
                calls > 1
            })
            .expect_err("stops on the second element");
        assert_eq!(stopped.elements_reduced, 1, "the first element was reduced");
        assert_eq!(calls, 2, "asked once per element, not once per basis");
    }
}

#[cfg(test)]
mod tests {
    use crate::util::contains_duplicates;
    use crate::{
        fields::Zp13, grobner::buchberger::buchberger, grobner::pairs::PairCriteria,
        poly::MonomialOrder, FiniteField, MultivariatePolynomial, One,
    };

    #[test]
    /// Spot-check a few examples.
    fn test_buchberger() {
        type F = Zp13;
        let vars = ["x", "y", "z"];
        let order = MonomialOrder::Lexicographic;

        let f: Vec<MultivariatePolynomial<3, F>> = vec![
            MultivariatePolynomial::parse("x + y + z", vars).unwrap(),
            MultivariatePolynomial::parse("x*y + x*z + y*z", vars).unwrap(),
            MultivariatePolynomial::parse("x*y*z - 1", vars).unwrap(),
        ];

        let g = buchberger(&f, order);

        // Computed with groebner.jl, and compared as a sequence rather than a set: the basis is
        // returned sorted by leading monomial, descending, so the order is part of the contract.
        let expected: Vec<MultivariatePolynomial<3, F>> = vec![
            MultivariatePolynomial::parse("x + y + z", vars).unwrap(),
            MultivariatePolynomial::parse("y^2 + y*z + z^2", vars).unwrap(),
            MultivariatePolynomial::parse("z^3 - 1", vars).unwrap(),
        ];

        assert_eq!(g, expected);
    }

    #[test]
    /// Reduced Grobner basis should not contain duplicates.
    fn test_buchberger_no_duplicates() {
        type F = Zp13;
        let vars = ["x", "y", "z"];
        let order = MonomialOrder::Lexicographic;

        let f: Vec<MultivariatePolynomial<3, F>> = vec![
            MultivariatePolynomial::parse("x + y + z", vars).unwrap(),
            MultivariatePolynomial::parse("x*y + x*z + y*z", vars).unwrap(),
            MultivariatePolynomial::parse("x*y*z - 1", vars).unwrap(),
        ];

        let g = buchberger(&f, order);
        for p in &g {
            println!("{}", p);
        }
        assert!(!contains_duplicates(&g));
    }

    #[test]
    fn test_buchberger_leading_coefficients_are_one() {
        type F = Zp13;
        let vars = ["x", "y", "z"];
        let order = MonomialOrder::Lexicographic;

        let f: Vec<MultivariatePolynomial<3, F>> = vec![
            MultivariatePolynomial::parse("x + y + z", vars).unwrap(),
            MultivariatePolynomial::parse("x*y + x*z + y*z", vars).unwrap(),
            MultivariatePolynomial::parse("x*y*z - 1", vars).unwrap(),
        ];

        let g = buchberger(&f, order);
        for p in &g {
            println!("{}", p);
            assert_eq!(p.leading_coefficient(order), F::ONE);
        }
    }

    /// Assert the defining properties of a reduced Grobner basis for the ideal generated by `f`.
    ///
    /// Checked against the definition rather than against a known answer, so this covers systems
    /// nobody has computed a basis for by hand.
    fn assert_is_reduced_grobner_basis<const N: usize, F: FiniteField>(
        f: &[MultivariatePolynomial<N, F>],
        order: MonomialOrder,
    ) {
        use crate::grobner::s_polynomial::s_polynomial;

        let g = buchberger(f, order);
        assert!(!g.is_empty(), "a nonzero ideal has a nonempty basis");

        // Every generator of the input ideal lies in the ideal generated by g, so it reduces to
        // zero. This is what fails if reduction drops a basis element.
        for p in f {
            assert!(
                p.multi_div_rem(&g, order).1.is_zero(),
                "input {} does not reduce to zero modulo the basis",
                p
            );
        }

        // Buchberger's criterion: g is a Grobner basis exactly when every S-polynomial of a pair
        // in g reduces to zero modulo g.
        for (i, g_i) in g.iter().enumerate() {
            for (j, g_j) in g.iter().enumerate() {
                if i >= j {
                    continue;
                }
                let s = s_polynomial(g_i, g_j, order);
                assert!(
                    s.multi_div_rem(&g, order).1.is_zero(),
                    "S({}, {}) does not reduce to zero modulo the basis",
                    g_i,
                    g_j
                );
            }
        }

        assert!(!contains_duplicates(&g), "basis contains duplicates");

        for p in &g {
            assert_eq!(p.leading_coefficient(order), F::ONE, "{} is not monic", p);
        }

        // Reduced: no monomial of p is divisible by the leading monomial of any other element.
        for (i, p) in g.iter().enumerate() {
            for m in p.terms().keys() {
                for (j, q) in g.iter().enumerate() {
                    if i == j {
                        continue;
                    }
                    assert!(
                        m.checked_div(&q.leading_monomial(order)).is_none(),
                        "monomial {:?} of {} lies in <LT(G \\ {{p}})>, via {}",
                        m.exponents(),
                        p,
                        q
                    );
                }
            }
        }
    }

    /// The basis properties hold across a range of systems, including a lone polynomial.
    #[test]
    fn test_buchberger_returns_a_reduced_grobner_basis() {
        type F = Zp13;
        let vars = ["x", "y", "z"];

        // A single generator is the smallest case, and the one that used to panic: its basis has
        // one element, leaving nothing to divide by during minimization.
        let systems: Vec<Vec<&str>> = vec![
            vec!["x^2 - y"],
            vec!["x + y + z"],
            vec!["x + y + z", "x*y + x*z + y*z", "x*y*z - 1"],
            vec!["x^2 - y", "x*y - 1"],
            vec!["x^2 + y^2 - 1", "x - y"],
            vec!["x*y - 1", "x - y"],
            vec!["x^2*y + x", "x*y^2 + y"],
            vec!["x^3 - 2*x*y", "x^2*y - 2*y^2 + x"],
            vec!["x + y", "x^2 + z", "y*z - 1"],
            vec!["x*y*z - 1", "x*y - z"],
        ];

        for order in [MonomialOrder::Lexicographic] {
            for system in &systems {
                let f: Vec<MultivariatePolynomial<3, F>> = system
                    .iter()
                    .map(|s| MultivariatePolynomial::parse(s, vars).unwrap())
                    .collect();
                assert_is_reduced_grobner_basis(&f, order);
            }
        }
    }

    /// An inconsistent system generates the whole ring, whose reduced basis is {1}.
    #[test]
    fn test_buchberger_detects_an_inconsistent_system() {
        type F = Zp13;
        let vars = ["x", "y", "z"];
        let order = MonomialOrder::Lexicographic;

        let f: Vec<MultivariatePolynomial<3, F>> = vec![
            MultivariatePolynomial::parse("x", vars).unwrap(),
            MultivariatePolynomial::parse("x - 1", vars).unwrap(),
        ];
        let g = buchberger(&f, order);
        assert_eq!(g.len(), 1);
        assert!(g[0].is_one(), "expected the basis {{1}}, got {}", g[0]);
    }

    /// A zero generator contributes nothing to the ideal and must not derail the computation.
    ///
    /// Regression test: `minimize_grobner_basis` scaled each element by the inverse of its
    /// leading coefficient, and the zero polynomial's is zero, so `inverse()` asserted.
    #[test]
    fn test_zero_generators_are_ignored() {
        type F = Zp13;
        let vars = ["x", "y", "z"];
        let parse = |s: &str| MultivariatePolynomial::<3, F>::parse(s, vars).unwrap();
        let zero = MultivariatePolynomial::<3, F>::zero();

        for order in ALL_ORDERS {
            // A zero generator alone generates the zero ideal, whose basis is empty.
            assert!(
                buchberger(std::slice::from_ref(&zero), order).is_empty(),
                "{}",
                order.name()
            );
            assert!(
                buchberger(&[zero.clone(), zero.clone()], order).is_empty(),
                "{}",
                order.name()
            );

            // Mixed with real generators, the zeros make no difference.
            let without = buchberger(&[parse("x + y"), parse("y^2 - 1")], order);
            let with = buchberger(
                &[parse("x + y"), zero.clone(), parse("y^2 - 1"), zero.clone()],
                order,
            );
            assert_eq!(with, without, "{}", order.name());
        }
    }

    /// Duplicate and redundant generators do not change the basis.
    #[test]
    fn test_duplicate_and_redundant_generators() {
        type F = Zp13;
        let vars = ["x", "y", "z"];
        let parse = |s: &str| MultivariatePolynomial::<3, F>::parse(s, vars).unwrap();

        for order in ALL_ORDERS {
            let base = buchberger(&[parse("x + y"), parse("y^2 - 1")], order);

            // The same generator twice.
            assert_eq!(
                buchberger(&[parse("x + y"), parse("x + y"), parse("y^2 - 1")], order),
                base,
                "{}: duplicates changed the basis",
                order.name()
            );

            // A scalar multiple of a generator is redundant.
            assert_eq!(
                buchberger(
                    &[parse("x + y"), parse("3*x + 3*y"), parse("y^2 - 1")],
                    order
                ),
                base,
                "{}: a scalar multiple changed the basis",
                order.name()
            );

            // A generator already in the ideal is redundant.
            assert_eq!(
                buchberger(
                    &[parse("x + y"), parse("y^2 - 1"), parse("x*y + y^2")],
                    order
                ),
                base,
                "{}: a redundant generator changed the basis",
                order.name()
            );
        }
    }

    /// The basis is returned in a deterministic order, run to run and regardless of input order.
    ///
    /// Regression test: the basis was accumulated into a `HashSet`, so its iteration order
    /// varied between runs of identical input.
    #[test]
    fn test_basis_order_is_deterministic() {
        type F = Zp13;
        let vars = ["x", "y", "z"];
        let parse = |s: &str| MultivariatePolynomial::<3, F>::parse(s, vars).unwrap();

        for order in ALL_ORDERS {
            let system = [
                parse("x + y + z"),
                parse("x*y + x*z + y*z"),
                parse("x*y*z - 1"),
            ];

            let first = buchberger(&system, order);
            for _ in 0..8 {
                assert_eq!(
                    buchberger(&system, order),
                    first,
                    "{}: repeated runs disagree",
                    order.name()
                );
            }

            // Permuting the generators yields the same basis in the same order, since a reduced
            // basis is unique as a set and the ordering is derived from it.
            let permuted = [system[2].clone(), system[0].clone(), system[1].clone()];
            assert_eq!(
                buchberger(&permuted, order),
                first,
                "{}: generator order changed the result",
                order.name()
            );

            // Strictly decreasing leading monomials, which is what makes the order canonical.
            for window in first.windows(2) {
                assert_eq!(
                    order.cmp(
                        &window[0].leading_monomial(order),
                        &window[1].leading_monomial(order)
                    ),
                    std::cmp::Ordering::Greater,
                    "{}: basis is not sorted by leading monomial",
                    order.name()
                );
            }
        }
    }

    /// An inconsistent system yields the basis {1} under every order.
    #[test]
    fn test_inconsistent_system_under_every_order() {
        type F = Zp13;
        let vars = ["x", "y", "z"];
        let parse = |s: &str| MultivariatePolynomial::<3, F>::parse(s, vars).unwrap();

        for order in ALL_ORDERS {
            for system in [
                vec![parse("x"), parse("x - 1")],
                vec![parse("x + y"), parse("x + y - 1")],
                vec![parse("1")],
            ] {
                let basis = buchberger(&system, order);
                assert_eq!(basis.len(), 1, "{}", order.name());
                assert!(basis[0].is_one(), "{}: got {}", order.name(), basis[0]);
            }
        }
    }

    /// The basis properties hold for every system under every order.
    #[test]
    fn test_grobner_properties_under_every_order() {
        type F = Zp13;
        let vars = ["x", "y", "z"];

        let systems: Vec<Vec<&str>> = vec![
            vec!["x^2 - y"],
            vec!["x + y + z"],
            vec!["x + y + z", "x*y + x*z + y*z", "x*y*z - 1"],
            vec!["x^2 - y", "x*y - 1"],
            vec!["x^2 + y^2 - 1", "x - y"],
            vec!["x*y - 1", "x - y"],
            vec!["x^2*y + x", "x*y^2 + y"],
            vec!["x^3 - 2*x*y", "x^2*y - 2*y^2 + x"],
            vec!["x + y", "x^2 + z", "y*z - 1"],
            vec!["x*y*z - 1", "x*y - z"],
        ];

        for order in ALL_ORDERS {
            for system in &systems {
                let f: Vec<MultivariatePolynomial<3, F>> = system
                    .iter()
                    .map(|s| MultivariatePolynomial::parse(s, vars).unwrap())
                    .collect();
                assert_is_reduced_grobner_basis(&f, order);
            }
        }
    }

    /// grevlex produces a genuinely different basis from grlex, and often a much smaller one.
    ///
    /// This is the observable consequence of the dispatch fix: before it, `cmp` sent grevlex to
    /// `grlex`, so the two orders computed identical bases and the advantage of grevlex — the
    /// reason it is the order of choice for Gröbner computation — was unavailable.
    #[test]
    fn test_grevlex_differs_from_grlex() {
        type F = Zp13;
        let vars = ["x", "y", "z"];
        let f: Vec<MultivariatePolynomial<3, F>> = ["x*z - y^2", "x^3 - z^2"]
            .iter()
            .map(|s| MultivariatePolynomial::parse(s, vars).unwrap())
            .collect();

        let grlex = buchberger(&f, MonomialOrder::GradedLexicographic);
        let grevlex = buchberger(&f, MonomialOrder::GradedReverseLexicographic);

        assert_ne!(grlex, grevlex);
        assert_eq!(grlex.len(), 5, "grlex basis size changed");
        assert_eq!(grevlex.len(), 2, "grevlex basis size changed");

        // Both are nonetheless valid bases for the same ideal.
        assert_is_reduced_grobner_basis(&f, MonomialOrder::GradedLexicographic);
        assert_is_reduced_grobner_basis(&f, MonomialOrder::GradedReverseLexicographic);
    }

    /// The optimized engine and the straightforward reference produce the same reduced basis.
    ///
    /// A reduced Gröbner basis is unique for a given ideal and order, so the two must agree
    /// exactly — and since both sort their output canonically, as sequences and not merely as
    /// sets. This is the check that the pair queue, the selection strategy, and the product
    /// criterion changed only the work done and not the answer.
    #[test]
    fn test_optimized_agrees_with_reference() {
        use crate::grobner::{
            benchmark_systems::{cyclic, katsura},
            reference::buchberger_reference,
        };
        type F = Zp13;
        let vars = ["x", "y", "z"];
        let parse = |s: &str| MultivariatePolynomial::<3, F>::parse(s, vars).unwrap();

        let hand_written: Vec<Vec<&str>> = vec![
            vec!["x^2 - y"],
            vec!["x + y + z"],
            vec!["x^2 - y", "x*y - 1"],
            vec!["x^2 + y^2 - 1", "x - y"],
            vec!["x*y - 1", "x - y"],
            vec!["x^2*y + x", "x*y^2 + y"],
            vec!["x^3 - 2*x*y", "x^2*y - 2*y^2 + x"],
            vec!["x + y", "x^2 + z", "y*z - 1"],
            vec!["x*y*z - 1", "x*y - z"],
            vec!["x*z - y^2", "x^3 - z^2"],
            // Degenerate and redundant input.
            vec!["x", "x - 1"],
            vec!["x + y", "x + y", "y^2 - 1"],
            vec!["x + y", "3*x + 3*y", "y^2 - 1"],
            // Relatively prime leading monomials, which the product criterion eliminates.
            vec!["x^2", "y^3"],
            vec!["x^2 - 1", "y^2 - 1", "z^2 - 1"],
        ];

        for order in ALL_ORDERS {
            for system in &hand_written {
                let f: Vec<MultivariatePolynomial<3, F>> =
                    system.iter().map(|s| parse(s)).collect();
                assert_eq!(
                    buchberger(&f, order),
                    buchberger_reference(&f, order),
                    "{:?} under {}",
                    system,
                    order.name()
                );
            }

            assert_eq!(
                buchberger(&cyclic::<3, F>(), order),
                buchberger_reference(&cyclic::<3, F>(), order),
                "cyclic-3 under {}",
                order.name()
            );
        }

        // katsura-3 only under the graded orders: the reference needs about two and a half
        // minutes on it in lex, which `test_optimized_agrees_with_reference_on_slow_systems`
        // covers instead.
        for order in [
            MonomialOrder::GradedLexicographic,
            MonomialOrder::GradedReverseLexicographic,
        ] {
            assert_eq!(
                buchberger(&katsura::<3, F>(), order),
                buchberger_reference(&katsura::<3, F>(), order),
                "katsura-3 under {}",
                order.name()
            );
        }
    }

    /// The same agreement on systems the reference implementation is too slow to run in CI.
    ///
    /// Ignored for runtime, not because it is unreliable: the reference takes about two minutes
    /// on katsura-3 in lex, which is the case the optimized engine most needs checked — the
    /// optimized engine finishes it in 83 us.
    ///
    /// Run with `cargo test --release -- --ignored`. A debug build makes the reference
    /// impractically slow.
    #[test]
    #[ignore] // Slow: the reference implementation takes minutes on these.
    fn test_optimized_agrees_with_reference_on_slow_systems() {
        use crate::grobner::{benchmark_systems::katsura, reference::buchberger_reference};
        type F = Zp13;

        let system = katsura::<3, F>();
        assert_eq!(
            buchberger(&system, MonomialOrder::Lexicographic),
            buchberger_reference(&system, MonomialOrder::Lexicographic),
            "katsura-3 under lex"
        );
    }

    /// The product criterion fires on relatively prime leading monomials, and changes no answer.
    #[test]
    fn test_product_criterion_eliminates_pairs() {
        use crate::grobner::{buchberger_with_statistics, reference::buchberger_reference};
        type F = Zp13;
        let vars = ["x", "y", "z"];
        let parse = |s: &str| MultivariatePolynomial::<3, F>::parse(s, vars).unwrap();

        // Leading monomials x^2, y^3, z^2 are pairwise relatively prime, so every initial pair
        // is eliminated without a reduction.
        let f: Vec<MultivariatePolynomial<3, F>> =
            vec![parse("x^2 - 1"), parse("y^3 - 1"), parse("z^2 - 1")];

        for order in ALL_ORDERS {
            let (basis, statistics) = buchberger_with_statistics(&f, order);

            assert!(
                statistics.pairs_eliminated_by_product_criterion >= 3,
                "{}: expected the three initial pairs to be eliminated, got {:?}",
                order.name(),
                statistics
            );
            assert_eq!(
                statistics.pairs_reduced,
                0,
                "{}: no reduction should have been needed",
                order.name()
            );
            // And the basis is still right.
            assert_eq!(basis, buchberger_reference(&f, order), "{}", order.name());
            assert_is_reduced_grobner_basis(&f, order);
        }
    }

    /// Statistics are consistent with each other.
    #[test]
    fn test_statistics_are_consistent() {
        use crate::grobner::{benchmark_systems::katsura, buchberger_with_statistics};
        type F = Zp13;

        for order in ALL_ORDERS {
            let (_, statistics) = buchberger_with_statistics(&katsura::<3, F>(), order);
            assert_eq!(
                statistics.pairs_considered,
                statistics.pairs_eliminated_by_product_criterion + statistics.pairs_reduced,
                "{}: every pair is either eliminated or reduced",
                order.name()
            );
            assert!(
                statistics.zero_reductions <= statistics.pairs_reduced,
                "{}",
                order.name()
            );
            assert_eq!(
                statistics.elements_added,
                statistics.pairs_reduced - statistics.zero_reductions,
                "{}: a nonzero reduction adds exactly one element",
                order.name()
            );
            assert!(statistics.pairs_considered > 0, "{}", order.name());
        }
    }

    /// Every combination of the pair criteria, so a differential test covers all of them.
    const CRITERIA_CONFIGURATIONS: [PairCriteria; 8] = [
        PairCriteria {
            product: false,
            chain: false,
            gebauer_moller: false,
        },
        PairCriteria {
            product: true,
            chain: false,
            gebauer_moller: false,
        },
        PairCriteria {
            product: false,
            chain: true,
            gebauer_moller: false,
        },
        PairCriteria {
            product: false,
            chain: false,
            gebauer_moller: true,
        },
        PairCriteria {
            product: true,
            chain: true,
            gebauer_moller: false,
        },
        PairCriteria {
            product: true,
            chain: false,
            gebauer_moller: true,
        },
        PairCriteria {
            product: false,
            chain: true,
            gebauer_moller: true,
        },
        PairCriteria {
            product: true,
            chain: true,
            gebauer_moller: true,
        },
    ];

    /// The correctness corpus: hand-written systems, degenerate input, and benchmark families.
    fn criteria_corpus() -> Vec<(String, Vec<MultivariatePolynomial<3, Zp13>>)> {
        use crate::grobner::benchmark_systems::{cyclic, katsura};
        type F = Zp13;
        let vars = ["x", "y", "z"];
        let parse = |s: &str| MultivariatePolynomial::<3, F>::parse(s, vars).unwrap();

        let written: Vec<Vec<&str>> = vec![
            vec!["x^2 - y"],
            vec!["x + y + z"],
            vec!["x + y + z", "x*y + x*z + y*z", "x*y*z - 1"],
            vec!["x^2 - y", "x*y - 1"],
            vec!["x^2 + y^2 - 1", "x - y"],
            vec!["x*y - 1", "x - y"],
            vec!["x^2*y + x", "x*y^2 + y"],
            vec!["x^3 - 2*x*y", "x^2*y - 2*y^2 + x"],
            vec!["x + y", "x^2 + z", "y*z - 1"],
            vec!["x*y*z - 1", "x*y - z"],
            vec!["x*z - y^2", "x^3 - z^2"],
            vec!["x^3 - y", "x^2 - z", "x - y*z", "y^2 - 1"],
            vec!["x^2 + y + 1", "y^2 + z + 2", "z^2 + x + 3"],
            // Inconsistent, so the basis is {1}.
            vec!["x", "x - 1"],
            // Duplicated, a scalar multiple, and a generator already in the ideal.
            vec!["x + y", "x + y", "y^2 - 1"],
            vec!["x + y", "3*x + 3*y", "y^2 - 1"],
            vec!["x + y", "y^2 - 1", "x*y + y^2"],
            // The configuration the chain criterion is about: three leading monomials each
            // dividing the lcm of the other two.
            vec!["x - 1", "y - 2", "x*y - 3"],
            // Relatively prime leading monomials, which the product criterion takes.
            vec!["x^2", "y^3"],
            vec!["x^2 - 1", "y^2 - 1", "z^2 - 1"],
        ];

        let mut corpus: Vec<(String, Vec<MultivariatePolynomial<3, F>>)> = written
            .iter()
            .map(|system| {
                (
                    format!("{:?}", system),
                    system.iter().map(|s| parse(s)).collect(),
                )
            })
            .collect();
        corpus.push(("cyclic-3".into(), cyclic::<3, F>()));
        corpus.push(("katsura-3".into(), katsura::<3, F>()));
        corpus
    }

    /// Every combination of the criteria computes the basis the criteria-free reference computes.
    #[test]
    fn test_criteria_do_not_change_the_basis() {
        use crate::grobner::buchberger_with_criteria;

        for order in ALL_ORDERS {
            for (name, f) in criteria_corpus() {
                let (expected, _) =
                    buchberger_with_criteria(&f, order, &CRITERIA_CONFIGURATIONS[0]);
                for criteria in CRITERIA_CONFIGURATIONS {
                    let (actual, _) = buchberger_with_criteria(&f, order, &criteria);
                    assert_eq!(
                        actual,
                        expected,
                        "{} under {} with {:?}",
                        name,
                        order.name(),
                        criteria
                    );
                }
            }
        }
    }

    /// Every combination of the criteria agrees with the naive textbook reference.
    ///
    /// The criteria-free computation shares the pair queue and the interreduction with the
    /// criteria-enabled one, so agreeing with it is necessary but not sufficient. The reference
    /// shares nothing.
    #[test]
    fn test_criteria_agree_with_the_reference() {
        use crate::grobner::{
            benchmark_systems::{cyclic, katsura},
            buchberger_with_criteria,
            reference::buchberger_reference,
        };
        type F = Zp13;

        // katsura-3 under lex takes the reference about two and a half minutes, so it is covered
        // under the graded orders here and by the ignored slow test under lex.
        for order in ALL_ORDERS {
            let mut systems = criteria_corpus();
            systems.retain(|(name, _)| name != "katsura-3");
            if order != MonomialOrder::Lexicographic {
                systems.push(("katsura-3".into(), katsura::<3, F>()));
            }
            systems.push(("cyclic-3".into(), cyclic::<3, F>()));

            for (name, f) in systems {
                let expected = buchberger_reference(&f, order);
                for criteria in CRITERIA_CONFIGURATIONS {
                    let (actual, _) = buchberger_with_criteria(&f, order, &criteria);
                    assert_eq!(
                        actual,
                        expected,
                        "{} under {} with {:?}",
                        name,
                        order.name(),
                        criteria
                    );
                }
            }
        }
    }

    /// The criteria survive permuted, duplicated, scaled and redundant generators.
    ///
    /// An unsound criterion usually agrees on a fixed corpus and fails once the generator order
    /// changes, because the order decides which pairs are handled before which.
    #[test]
    fn test_criteria_under_permuted_generators() {
        use crate::grobner::buchberger_with_criteria;
        type F = Zp13;

        for order in ALL_ORDERS {
            for (name, f) in criteria_corpus() {
                let (expected, _) =
                    buchberger_with_criteria(&f, order, &CRITERIA_CONFIGURATIONS[0]);

                // Every rotation of the generators, the reversal, and the generators with the
                // first one duplicated, doubled, and re-added as a redundant ideal member.
                let mut variants: Vec<Vec<MultivariatePolynomial<3, F>>> = Vec::new();
                for shift in 0..f.len() {
                    variants.push(
                        f.iter()
                            .cycle()
                            .skip(shift)
                            .take(f.len())
                            .cloned()
                            .collect(),
                    );
                }
                let mut reversed = f.clone();
                reversed.reverse();
                variants.push(reversed);
                let mut duplicated = f.clone();
                duplicated.push(f[0].clone());
                variants.push(duplicated);
                let mut scaled = f.clone();
                scaled.push(f[0].scale(&(F::ONE + F::ONE + F::ONE)));
                variants.push(scaled);
                let mut redundant = f.clone();
                redundant.push(&f[0] * &f[f.len() - 1]);
                variants.push(redundant);

                for variant in &variants {
                    for criteria in CRITERIA_CONFIGURATIONS {
                        let (actual, _) = buchberger_with_criteria(variant, order, &criteria);
                        assert_eq!(
                            actual,
                            expected,
                            "{} under {} with {:?}, generators {:?}",
                            name,
                            order.name(),
                            criteria,
                            variant
                        );
                    }
                }
            }
        }
    }

    /// Randomized systems over GF(7) and GF(13) agree with the criteria switched off.
    #[test]
    fn test_criteria_on_randomized_systems() {
        use crate::{
            fields::Zp7,
            grobner::buchberger_with_criteria,
            poly::{Monomial, MultivariatePolynomial as Poly},
        };
        use rand::{prelude::StdRng, Rng, SeedableRng};

        /// Three sparse polynomials of degree at most two in three variables.
        fn system<FF: FiniteField>(seed: u64) -> Vec<Poly<3, FF>> {
            let mut rng = StdRng::seed_from_u64(seed);
            (0..3)
                .map(|_| {
                    let terms: Vec<(Monomial<3>, FF)> = (0..4)
                        .map(|_| {
                            let mut exponents = [0u32; 3];
                            exponents[rng.gen_range(0..3)] += 1;
                            if rng.gen_bool(0.5) {
                                exponents[rng.gen_range(0..3)] += 1;
                            }
                            (Monomial::new(&exponents), FF::random(&mut rng))
                        })
                        .collect();
                    Poly::new(&terms)
                })
                .collect()
        }

        for seed in 0..24 {
            for order in ALL_ORDERS {
                let over_7: Vec<Poly<3, Zp7>> = system(seed);
                let over_13: Vec<Poly<3, Zp13>> = system(seed + 1000);

                let (expected_7, _) =
                    buchberger_with_criteria(&over_7, order, &CRITERIA_CONFIGURATIONS[0]);
                let (expected_13, _) =
                    buchberger_with_criteria(&over_13, order, &CRITERIA_CONFIGURATIONS[0]);

                for criteria in CRITERIA_CONFIGURATIONS {
                    assert_eq!(
                        buchberger_with_criteria(&over_7, order, &criteria).0,
                        expected_7,
                        "GF(7) seed {} under {} with {:?}",
                        seed,
                        order.name(),
                        criteria
                    );
                    assert_eq!(
                        buchberger_with_criteria(&over_13, order, &criteria).0,
                        expected_13,
                        "GF(13) seed {} under {} with {:?}",
                        seed,
                        order.name(),
                        criteria
                    );
                }
            }
        }
    }

    /// Each criterion's counter is nonzero when that criterion is enabled and zero when it is not.
    #[test]
    fn test_criterion_counts_are_attributed() {
        use crate::grobner::{benchmark_systems::katsura, buchberger_with_criteria, PairCriteria};
        type F = Zp13;

        let system = katsura::<3, F>();
        let order = MonomialOrder::Lexicographic;

        let (_, none) = buchberger_with_criteria(&system, order, &PairCriteria::NONE);
        assert_eq!(none.criteria.total(), 0, "nothing should be discarded");

        let (_, product) = buchberger_with_criteria(&system, order, &PairCriteria::PRODUCT_ONLY);
        assert!(product.criteria.product > 0);
        assert_eq!(product.criteria.chain, 0);
        assert_eq!(product.criteria.gebauer_moller, 0);

        let chain_only = PairCriteria {
            product: false,
            chain: true,
            gebauer_moller: false,
        };
        let (_, chain) = buchberger_with_criteria(&system, order, &chain_only);
        assert_eq!(chain.criteria.product, 0);
        assert!(
            chain.criteria.chain > 0,
            "the chain criterion discarded nothing: {:?}",
            chain
        );
        assert_eq!(chain.criteria.gebauer_moller, 0);

        let gebauer_moller_only = PairCriteria {
            product: false,
            chain: false,
            gebauer_moller: true,
        };
        let (_, gm) = buchberger_with_criteria(&system, order, &gebauer_moller_only);
        assert_eq!(gm.criteria.product, 0);
        assert_eq!(gm.criteria.chain, 0);
        assert!(
            gm.criteria.gebauer_moller > 0,
            "Gebauer-Möller discarded nothing: {:?}",
            gm
        );

        // Together they reduce the pairs actually reduced below what either manages alone.
        let (_, all) = buchberger_with_criteria(&system, order, &PairCriteria::ALL);
        assert!(all.pairs_reduced < product.pairs_reduced);
        assert!(all.pairs_reduced <= chain.pairs_reduced);
        assert!(all.pairs_reduced <= gm.pairs_reduced);
    }

    /// The interreduction as it was written before M16-C, kept as the differential oracle.
    ///
    /// Deliberately the naive formulation: minimize by comparing every element against every
    /// element kept so far, then reduce each element against a freshly cloned copy of all the
    /// others, in whatever order minimization left them. The optimized implementation must return
    /// exactly this, which is the only thing that makes the optimization safe.
    fn reduce_grobner_basis_reference<const N: usize, F: FiniteField>(
        g: &[MultivariatePolynomial<N, F>],
        order: MonomialOrder,
    ) -> Vec<MultivariatePolynomial<N, F>> {
        let mut monic: Vec<MultivariatePolynomial<N, F>> = Vec::with_capacity(g.len());
        for p in g.iter().filter(|p| !p.is_zero()) {
            let scaled = p.scale(&p.leading_coefficient(order).inverse());
            if !monic.contains(&scaled) {
                monic.push(scaled);
            }
        }

        let mut keep = vec![true; monic.len()];
        for i in 0..monic.len() {
            let lead_i = monic[i].leading_monomial(order);
            for j in 0..monic.len() {
                if i == j || !keep[j] {
                    continue;
                }
                if lead_i
                    .checked_div(&monic[j].leading_monomial(order))
                    .is_some()
                {
                    keep[i] = false;
                    break;
                }
            }
        }

        let minimal: Vec<MultivariatePolynomial<N, F>> = monic
            .into_iter()
            .zip(keep)
            .filter(|(_, keep)| *keep)
            .map(|(p, _)| p)
            .collect();

        let mut reduced: Vec<MultivariatePolynomial<N, F>> = Vec::with_capacity(minimal.len());
        for (i, p) in minimal.iter().enumerate() {
            let others: Vec<MultivariatePolynomial<N, F>> = minimal
                .iter()
                .enumerate()
                .filter(|(j, _)| *j != i)
                .map(|(_, q)| q.clone())
                .collect();
            if others.is_empty() {
                reduced.push(p.clone());
                continue;
            }
            reduced.push(p.normal_form(&others, order));
        }

        reduced.sort_by(|a, b| order.cmp(&b.leading_monomial(order), &a.leading_monomial(order)));
        reduced
    }

    /// The optimized interreduction returns exactly what the naive one does, element for element.
    #[test]
    fn test_interreduction_agrees_with_the_naive_formulation() {
        use crate::grobner::{
            benchmark_systems::{cyclic, katsura},
            buchberger::reduce_grobner_basis,
            pairs::{are_relatively_prime, CriterionCounts, PairCriteria, PairQueue},
            s_polynomial::s_polynomial,
        };
        type F = Zp13;

        // The pre-interreduction basis, which is the input the interreduction actually sees: much
        // longer than the answer, with duplicates and redundant elements still in it.
        fn raw_basis<const N: usize, F: FiniteField>(
            f: &[MultivariatePolynomial<N, F>],
            order: MonomialOrder,
        ) -> Vec<MultivariatePolynomial<N, F>> {
            let mut basis: Vec<MultivariatePolynomial<N, F>> = Vec::new();
            for p in f.iter().filter(|p| !p.is_zero()) {
                let monic = p.scale(&p.leading_coefficient(order).inverse());
                if !basis.contains(&monic) {
                    basis.push(monic);
                }
            }
            let mut leads: Vec<_> = basis.iter().map(|p| p.leading_monomial(order)).collect();
            let mut counts = CriterionCounts::default();
            let criteria = PairCriteria::PRODUCT_ONLY;
            let mut pending = PairQueue::seeded_from_leads(&leads, &criteria, &mut counts);
            while let Some(pair) = pending.pop() {
                if are_relatively_prime(&leads[pair.left], &leads[pair.right]) {
                    continue;
                }
                let s = s_polynomial(&basis[pair.left], &basis[pair.right], order);
                let remainder = s.normal_form(&basis, order);
                if remainder.is_zero() {
                    continue;
                }
                let monic = remainder.scale(&remainder.leading_coefficient(order).inverse());
                let added = basis.len();
                leads.push(monic.leading_monomial(order));
                basis.push(monic);
                pending.push_pairs_from_leads(&leads, added, &criteria, &mut counts);
            }
            basis
        }

        let vars = ["x", "y", "z"];
        let parse = |s: &str| MultivariatePolynomial::<3, F>::parse(s, vars).unwrap();

        let mut corpus: Vec<Vec<MultivariatePolynomial<3, F>>> = vec![
            vec![parse("x^2 - y")],
            vec![
                parse("x + y + z"),
                parse("x*y + x*z + y*z"),
                parse("x*y*z - 1"),
            ],
            vec![parse("x^2 - y"), parse("x*y - 1")],
            vec![parse("x*z - y^2"), parse("x^3 - z^2")],
            vec![parse("x^2*y + x"), parse("x*y^2 + y")],
            vec![
                parse("x + y"),
                parse("x + y"),
                parse("3*x + 3*y"),
                parse("y^2 - 1"),
            ],
            vec![parse("x"), parse("x - 1")],
        ];
        corpus.push(cyclic::<3, F>());
        corpus.push(katsura::<3, F>());

        for order in ALL_ORDERS {
            for f in &corpus {
                let raw = raw_basis(f, order);
                assert_eq!(
                    reduce_grobner_basis(raw.clone(), order),
                    reduce_grobner_basis_reference(&raw, order),
                    "{} on a {}-element pre-interreduction basis",
                    order.name(),
                    raw.len()
                );
            }

            // Degenerate inputs the two must also agree on.
            let zero = MultivariatePolynomial::<3, F>::zero();
            for raw in [
                vec![],
                vec![zero.clone()],
                vec![parse("x^2 - y")],
                // Equal leading monomials, so minimization has to break a tie.
                vec![parse("x^2 - y"), parse("x^2 - z"), parse("x^2 - y")],
                // Interleaved duplicates, which is the case the deduplication has to preserve.
                vec![
                    parse("x^2 - y"),
                    parse("x^2 - z"),
                    parse("x^2 - y"),
                    parse("y - 1"),
                ],
            ] {
                assert_eq!(
                    reduce_grobner_basis(raw.clone(), order),
                    reduce_grobner_basis_reference(&raw, order),
                    "{} on {:?}",
                    order.name(),
                    raw
                );
            }
        }
    }

    /// The interreduction establishes the properties it is defined by: monic, minimal, reduced,
    /// and canonically ordered.
    #[test]
    fn test_interreduction_establishes_its_properties() {
        use crate::grobner::{benchmark_systems::katsura, buchberger::reduce_grobner_basis};
        type F = Zp13;
        let vars = ["x", "y", "z"];
        let parse = |s: &str| MultivariatePolynomial::<3, F>::parse(s, vars).unwrap();

        for order in ALL_ORDERS {
            let mut inputs: Vec<Vec<MultivariatePolynomial<3, F>>> = vec![
                vec![parse("x^2 - y"), parse("x^2 - y"), parse("3*x^2 - 3*y")],
                vec![parse("x + y"), parse("x^2 + y^2"), parse("x^3 - 1")],
            ];
            inputs.push(buchberger(&katsura::<3, F>(), order));

            for input in &inputs {
                let basis = reduce_grobner_basis(input.to_vec(), order);

                for p in &basis {
                    assert_eq!(p.leading_coefficient(order), F::ONE, "{} is not monic", p);
                }

                // Minimal: no leading monomial divides another's.
                for (i, p) in basis.iter().enumerate() {
                    for (j, q) in basis.iter().enumerate() {
                        if i == j {
                            continue;
                        }
                        assert!(
                            p.leading_monomial(order)
                                .checked_div(&q.leading_monomial(order))
                                .is_none(),
                            "{} has a leading monomial divisible by {}'s",
                            p,
                            q
                        );
                    }
                }

                // Reduced: no monomial of one element is divisible by another's leading monomial.
                for (i, p) in basis.iter().enumerate() {
                    for m in p.terms().keys() {
                        for (j, q) in basis.iter().enumerate() {
                            if i == j {
                                continue;
                            }
                            assert!(
                                m.checked_div(&q.leading_monomial(order)).is_none(),
                                "monomial {:?} of {} is reducible by {}",
                                m.exponents(),
                                p,
                                q
                            );
                        }
                    }
                }

                // Canonically ordered: strictly decreasing leading monomials.
                for window in basis.windows(2) {
                    assert_eq!(
                        order.cmp(
                            &window[0].leading_monomial(order),
                            &window[1].leading_monomial(order)
                        ),
                        std::cmp::Ordering::Greater,
                        "{}: not sorted by leading monomial",
                        order.name()
                    );
                }

                // Idempotent, which is what makes the output canonical rather than merely tidy.
                assert_eq!(
                    reduce_grobner_basis(basis.clone(), order),
                    basis,
                    "{}: reducing a reduced basis changed it",
                    order.name()
                );
            }
        }
    }

    const ALL_ORDERS: [MonomialOrder; 3] = [
        MonomialOrder::Lexicographic,
        MonomialOrder::GradedLexicographic,
        MonomialOrder::GradedReverseLexicographic,
    ];
}
