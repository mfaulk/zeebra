//! Buchberger's algorithm for computing a Gröbner basis.
//!
//! Critical pairs are processed incrementally from a queue rather than by rescanning every pair of
//! basis elements on each pass. When a reduction yields a new basis element, only the pairs
//! involving that element are enqueued; everything already handled stays handled.
//!
//! Pairs are selected in order of the total degree of their lcm — the normal strategy — which
//! keeps the intermediate polynomials as small as possible for as long as possible. Ties are
//! broken by the lcm and then by the pair's indices, so the whole computation is deterministic.
//!
//! Buchberger's first criterion eliminates a pair outright when the two leading monomials are
//! relatively prime, because its S-polynomial is then guaranteed to reduce to zero. Skipping it
//! avoids the reduction entirely.
//!
//! [`super::reference::buchberger_reference`] keeps the textbook formulation for comparison, and
//! the two are checked against each other over the benchmark families and all three orders.
//!
//! See Sec 2.7 of Ideals, Varieties, and Algorithms by Cox, Little, and O'Shea.

use std::{cmp::Reverse, collections::BinaryHeap};

use crate::{
    grobner::s_polynomial::s_polynomial, poly::MonomialOrder, FiniteField, Monomial,
    MultivariatePolynomial,
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
}

/// A critical pair, keyed for selection.
///
/// Ordered by the total degree of the lcm first, which is the normal selection strategy, then by
/// the lcm and the indices so that the order is total and the computation reproducible. The lcm
/// comparison uses `Monomial`'s derived ordering rather than the monomial order under
/// computation: it only has to be deterministic, not meaningful.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct PairKey<const N: usize> {
    degree: u64,
    lcm: Monomial<N>,
    left: usize,
    right: usize,
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

    // Every pair of the initial generators. `Reverse` turns the max-heap into a min-heap, so the
    // lowest-degree pair is selected first.
    let mut pending: BinaryHeap<Reverse<PairKey<N>>> = BinaryHeap::new();
    for left in 0..basis.len() {
        for right in (left + 1)..basis.len() {
            pending.push(Reverse(pair_key(&basis, left, right, order)));
        }
    }

    while let Some(Reverse(pair)) = pending.pop() {
        statistics.pairs_considered += 1;
        statistics.max_pair_degree = statistics.max_pair_degree.max(pair.degree);

        let left = &basis[pair.left];
        let right = &basis[pair.right];

        // Buchberger's first criterion. If the leading monomials share no variable, their lcm is
        // their product and S(left, right) is guaranteed to reduce to zero modulo the two of
        // them, so the reduction can be skipped without affecting the result.
        if are_relatively_prime(
            &left.leading_monomial(order),
            &right.leading_monomial(order),
        ) {
            statistics.pairs_eliminated_by_product_criterion += 1;
            continue;
        }

        statistics.pairs_reduced += 1;
        let remainder = s_polynomial(left, right, order).normal_form(&basis, order);

        if remainder.is_zero() {
            statistics.zero_reductions += 1;
            continue;
        }

        statistics.max_terms = statistics.max_terms.max(remainder.terms().len());

        // Monic, so that the basis is normalized as it is built rather than only at the end.
        let monic = remainder.scale(&remainder.leading_coefficient(order).inverse());
        let added = basis.len();
        basis.push(monic);
        statistics.elements_added += 1;

        // Only the pairs involving the new element are new. This is what makes the processing
        // incremental: the textbook formulation rebuilds every pair on every pass.
        for existing in 0..added {
            pending.push(Reverse(pair_key(&basis, existing, added, order)));
        }
    }

    (reduce_grobner_basis(&basis, order), statistics)
}

/// The selection key for the pair of basis elements at `left` and `right`.
fn pair_key<const N: usize, F: FiniteField>(
    basis: &[MultivariatePolynomial<N, F>],
    left: usize,
    right: usize,
    order: MonomialOrder,
) -> PairKey<N> {
    let lcm = Monomial::lcm(
        &basis[left].leading_monomial(order),
        &basis[right].leading_monomial(order),
    );
    PairKey {
        degree: lcm.degree(),
        lcm,
        left,
        right,
    }
}

/// True if two monomials share no variable, i.e. their lcm is their product.
fn are_relatively_prime<const N: usize>(a: &Monomial<N>, b: &Monomial<N>) -> bool {
    a.exponents()
        .iter()
        .zip(b.exponents().iter())
        .all(|(x, y)| *x == 0 || *y == 0)
}

/// Finds a minimal Grobner basis.
///
/// # Arguments
/// * `g` - A Grobner basis.
/// * `order` - A monomial order.
///
/// A minimal Grobner basis has two properties:
/// 2. The leading coefficient of each polynomial is 1.
/// 1. No leading term of any polynomial in the basis is divisible by the leading term of any other polynomial in the basis.
fn minimize_grobner_basis<const N: usize, F: FiniteField>(
    g: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
) -> Vec<MultivariatePolynomial<N, F>> {
    // Scale each polynomial to have leading coefficient 1, dropping zeros and duplicates.
    // First-occurrence order is preserved, so the outcome does not depend on hashing.
    let mut monic: Vec<MultivariatePolynomial<N, F>> = Vec::with_capacity(g.len());
    for p in g.iter().filter(|p| !p.is_zero()) {
        let scaled = p.scale(&p.leading_coefficient(order).inverse());
        if !monic.contains(&scaled) {
            monic.push(scaled);
        }
    }

    // Drop any element whose leading term is divisible by another's, which is exactly
    // LT(p) in <LT(G \ {p})> for a set of leading terms.
    //
    // Two elements can share a leading monomial, in which case each divides the other and one
    // must go. Indices decide which, so the result is reproducible; a `HashSet` here made the
    // surviving element depend on iteration order.
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

    monic
        .into_iter()
        .zip(keep)
        .filter(|(_, keep)| *keep)
        .map(|(p, _)| p)
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
    g: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
) -> Vec<MultivariatePolynomial<N, F>> {
    let minimal: Vec<_> = minimize_grobner_basis(g, order);

    // Replace each p by its remainder on division by the others. Deleting p instead would drop a
    // generator and leave a set that no longer generates the ideal: a *non-leading* monomial of p
    // lying in <LT(G \ {p})> means p needs reducing, not discarding.
    //
    // The remainder is never zero, and the basis stays minimal: p's leading term is not divisible
    // by any other leading term, so division never cancels it.
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
        let remainder = p.normal_form(&others, order);
        debug_assert!(
            !remainder.is_zero(),
            "reducing a minimal basis element cannot cancel its leading term"
        );
        reduced.push(remainder);
    }

    // Sort by leading monomial, descending, so the basis is returned in a canonical order.
    // Minimization leaves the leading monomials distinct, so this is a total order on the
    // result, and a reduced Gröbner basis is unique as a set — which makes the sequence unique
    // too. Without this the order came from `HashSet` iteration and varied between runs.
    reduced.sort_by(|a, b| order.cmp(&b.leading_monomial(order), &a.leading_monomial(order)));
    reduced
}

#[cfg(test)]
mod tests {
    use crate::util::contains_duplicates;
    use crate::{
        fields::Zp13, grobner::buchberger::buchberger, poly::MonomialOrder, FiniteField,
        MultivariatePolynomial, One,
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

    const ALL_ORDERS: [MonomialOrder; 3] = [
        MonomialOrder::Lexicographic,
        MonomialOrder::GradedLexicographic,
        MonomialOrder::GradedReverseLexicographic,
    ];
}
