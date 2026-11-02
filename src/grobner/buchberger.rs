//! Buchberger's algorithm for computing a Grobner basis.
//!
//! See Sec 2.7 of Ideals, Varieties, and Algorithms by Cox, Little, and O'Shea.

use crate::{
    grobner::s_polynomial::s_polynomial, poly::MonomialOrder, FiniteField, MultivariatePolynomial,
};

/// The reduced Grobner basis for the given polynomials, w.r.t the given monomial order.
///
/// # Arguments
/// * `f` - Polynomials <f_0, ..., f_{s-1}>
/// * `order` - A monomial order.
///
/// Returns the reduced Grobner basis G for the ideal I = <f_0, ..., f_{s-1}>.
pub fn buchberger<const N: usize, F: FiniteField>(
    f: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
) -> Vec<MultivariatePolynomial<N, F>> {
    // A zero generator contributes nothing to the ideal, and would otherwise reach
    // `leading_coefficient().inverse()` with a zero coefficient.
    let mut g: Vec<MultivariatePolynomial<N, F>> =
        f.iter().filter(|p| !p.is_zero()).cloned().collect();
    if g.is_empty() {
        return Vec::new();
    }
    let mut g_prime: Vec<MultivariatePolynomial<N, F>>;

    loop {
        g_prime = g.clone();
        // For each pair g_i, g_j, i \neq j, in g_prime:
        for (i, g_i) in g_prime.iter().enumerate() {
            for (j, g_j) in g_prime.iter().enumerate() {
                if i >= j {
                    continue;
                }
                // S(g_i,g_j).
                let s = s_polynomial(g_i, g_j, order);
                // The remainder r of dividing S(g_i, g_j) by g_prime.
                let (_quotients, remainder) = s.multi_div_rem(&g_prime, order);

                if !remainder.is_zero() {
                    // If r != 0, add r to g.
                    g.push(remainder);
                }
            }
        }
        if g == g_prime {
            break;
        }
    }

    // g is now a Grobner basis for I, but not necessarily reduced.
    reduce_grobner_basis(&g, order)
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
fn reduce_grobner_basis<const N: usize, F: FiniteField>(
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
        let remainder = p.multi_div_rem(&others, order).1;
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

    const ALL_ORDERS: [MonomialOrder; 3] = [
        MonomialOrder::Lexicographic,
        MonomialOrder::GradedLexicographic,
        MonomialOrder::GradedReverseLexicographic,
    ];
}
