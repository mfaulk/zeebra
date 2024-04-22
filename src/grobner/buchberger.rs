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
#[allow(dead_code)]
fn buchberger<const N: usize, F: FiniteField>(
    f: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
) -> Vec<MultivariatePolynomial<N, F>> {
    let mut g: Vec<MultivariatePolynomial<N, F>> = f.iter().cloned().collect();
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
#[allow(dead_code)]
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
#[allow(dead_code)]
fn reduce_grobner_basis<const N: usize, F: FiniteField>(
    g: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
) -> Vec<MultivariatePolynomial<N, F>> {
    let g: Vec<_> = minimize_grobner_basis(g, order);
    let mut reduced_g: HashSet<MultivariatePolynomial<N, F>> = g.iter().cloned().collect();
    for p in g {
        let p_monomials: Vec<MultivariatePolynomial<N, F>> =
            p.terms().iter().map(|(m, _c)| m.into()).collect::<Vec<_>>();
        let divisors: Vec<MultivariatePolynomial<N, F>> = reduced_g
            .iter()
            .filter(|q| p != **q)
            .map(|q| q.leading_monomial(order).into())
            .collect();
        for m in p_monomials {
            if m.multi_div_rem(&divisors, order).1.is_zero() {
                // m \in <LT(G \ {p})>
                reduced_g.remove(&p);
                break;
            }
        }
    }
    reduced_g.into_iter().collect()
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use crate::{
        fields::Zp13, grobner::buchberger::buchberger, poly::MonomialOrder, MultivariatePolynomial,
        One,
    };
    use crate::util::contains_duplicates;

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
}
