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

pub use fft::{evaluate, interpolate, powers_of, FFTDomain};
pub use fields::{FiniteField, ParseFieldElementError};
pub use identities::{One, Zero};
pub use poly::{
    gcd, lagrange_interpolate, Monomial, MultivariatePolynomial, Polynomial, PolynomialParams,
    UnivariatePolynomial,
};
pub use rings::Ring;
