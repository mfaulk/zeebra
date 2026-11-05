//! Algebra
//!
//! This crate provides efficient operations for computing with finite fields and polynomials
//! over finite fields.  

// These are noisy. Maybe re-enable them later.
#![allow(clippy::suspicious_arithmetic_impl)]
#![allow(clippy::needless_range_loop)]
#![allow(clippy::op_ref)]
// Macros for implementing Add/Sub/Mul/Div variants trigger these.
#![allow(non_local_definitions)]

#[macro_use]
extern crate lazy_static;
extern crate core;
extern crate pest;

// macros should be at the top in order for macros to be accessible in subsequent modules
#[macro_use]
pub mod macros;
mod fft;
pub mod fields;
pub mod grobner;
mod identities;
pub mod integers;
pub mod linalg;
mod poly;
mod rings;

pub mod util;

#[cfg(test)]
pub(crate) mod test_support;

pub use fft::{evaluate, interpolate, powers_of, DomainError, FFTDomain};
pub use fields::{FiniteField, KnownOrder, ParseFieldElementError};
pub use identities::{One, Zero};
pub use poly::{
    factorize, gcd, inverse_exponent, is_irreducible, is_permutation_exponent,
    is_permutation_polynomial, lagrange_interpolate, permutation_exponents, pow_mod, roots,
    Monomial, MonomialOrder, MultivariatePolynomial, Polynomial, PolynomialParams,
    PowerPermutation, UnivariatePolynomial,
};
pub use rings::Ring;

/// The README's code examples, compiled and run.
///
/// The README is where a reader meets the public API, so its examples are the ones most worth
/// keeping true. `cfg(doctest)` means this item exists only when doc tests are collected, so the
/// README is not pulled into the rendered crate documentation — only its fenced Rust blocks become
/// tests.
#[cfg(doctest)]
#[doc = include_str!("../README.md")]
pub struct ReadmeExamples;
