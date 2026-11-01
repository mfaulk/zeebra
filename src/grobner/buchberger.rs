//! Buchberger's algorithm for computing a Grobner basis.
//!
//! See Sec 2.7 of Ideals, Varieties, and Algorithms by Cox, Little, and O'Shea.

use std::collections::HashSet;

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
    let mut g: Vec<MultivariatePolynomial<N, F>> = f.to_vec();
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
    // Scale each polynomial to have leading coefficient 1.
    let g: Vec<MultivariatePolynomial<N, F>> = g
        .iter()
        .map(|p| {
            let lc = p.leading_coefficient(order);
            p.scale(&lc.inverse())
        })
        .collect();

    let mut g_minimal: HashSet<MultivariatePolynomial<N, F>> = g.iter().cloned().collect();
    for p in g {
        let lm_p: MultivariatePolynomial<N, F> = p.leading_monomial(order).into();
        let divisors: Vec<MultivariatePolynomial<N, F>> = g_minimal
            .iter()
            .filter(|q| p != **q)
            .map(|q| q.leading_monomial(order).into())
            .collect();
        // With nothing else left to divide by, LT(p) cannot lie in <LT(G \ {p})> — that ideal is
        // zero — so p is not redundant. `multi_div_rem` requires a non-empty divisor list.
        if divisors.is_empty() {
            continue;
        }
        if lm_p.multi_div_rem(&divisors, order).1.is_zero() {
            // LT(p) \in <LT(G \ {p})>
            g_minimal.remove(&p);
        }
    }
    g_minimal.into_iter().collect()
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
    reduced
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

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

        // TODO: Ensure that the basis is sorted, to simplify comparisons.
        let g: HashSet<MultivariatePolynomial<3, F>> = buchberger(&f, order).into_iter().collect();
        for p in &g {
            println!("{}", p);
        }

        // These were computed with groebner.jl
        let expected: HashSet<MultivariatePolynomial<3, F>> = HashSet::from([
            MultivariatePolynomial::parse("z^3 - 1", vars).unwrap(),
            MultivariatePolynomial::parse("y^2 + y*z + z^2", vars).unwrap(),
            MultivariatePolynomial::parse("x + y + z", vars).unwrap(),
        ]);

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
}
