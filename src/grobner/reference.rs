//! The straightforward Buchberger algorithm, kept as a mathematical reference.
//!
//! This is the textbook formulation: repeatedly take every pair of basis elements, reduce their
//! S-polynomial against the whole basis, and append any nonzero remainder, until a full pass adds
//! nothing. It is quadratic in the basis size on every pass and applies no pair-elimination
//! criteria, so it is far too slow for real systems — but it is short enough to check against the
//! definition by reading, which is what makes it useful as an oracle for the optimized engine in
//! [`super::buchberger`].
//!
//! See Sec 2.7 of Ideals, Varieties, and Algorithms by Cox, Little, and O'Shea.

use crate::{
    grobner::{buchberger::reduce_grobner_basis, s_polynomial::s_polynomial},
    poly::MonomialOrder,
    FiniteField, MultivariatePolynomial,
};

pub fn buchberger_reference<const N: usize, F: FiniteField>(
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
    reduce_grobner_basis(g, order)
}
