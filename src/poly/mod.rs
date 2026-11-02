//! Polynomials over finite fields.

mod multivariate;
mod univariate;

pub use multivariate::{Monomial, MonomialOrder, MultivariatePolynomial};
pub use univariate::{
    factorize, gcd, is_irreducible, lagrange_interpolate, pow_mod, roots, Polynomial,
    PolynomialParams, UnivariatePolynomial,
};

#[cfg(test)]
pub(crate) use univariate::trace_to_gf2;
