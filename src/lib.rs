//! Algebra
//!
//! This crate provides efficient operations for computing with finite fields and polynomials
//! over finite fields.  

#![feature(generic_const_exprs)]
// Allows constants to be initialized like `const foo: Foo = Foo::from(bar)`.
#![feature(const_trait_impl)]
// Provides u64 carrying_add and borrowing_sub.
#![feature(bigint_helper_methods)]
#![feature(is_sorted)]
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
mod grobner;
mod identities;
pub mod integers;
pub mod linalg;
mod poly;
mod rings;

pub mod util;

pub use fft::{evaluate, interpolate, powers_of, FFTDomain};
pub use fields::FiniteField;
pub use identities::{One, Zero};
pub use poly::{
    gcd, lagrange_interpolate, Monomial, MultivariatePolynomial, Polynomial, UnivariatePolynomial,
};
pub use rings::Ring;
