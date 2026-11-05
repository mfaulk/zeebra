//! Polynomials over finite fields.

mod multivariate;
mod univariate;

pub use multivariate::{Monomial, MonomialOrder, MultivariatePolynomial};
pub use univariate::{
    factorize, gcd, inverse_exponent, is_irreducible, is_permutation_exponent,
    is_permutation_polynomial, lagrange_interpolate, permutation_exponents, pow_mod, roots,
    Polynomial, PolynomialParams, PowerPermutation, UnivariatePolynomial,
};

#[cfg(test)]
pub(crate) use univariate::trace_to_gf2;
