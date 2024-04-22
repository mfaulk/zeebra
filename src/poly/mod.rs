//! Polynomials over finite fields.

mod multivariate;
mod univariate;

pub use multivariate::{Monomial, MonomialOrder, MultivariatePolynomial};
pub use univariate::{gcd, lagrange_interpolate, Polynomial, UnivariatePolynomial};
