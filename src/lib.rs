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
pub mod codes;
mod fft;
pub mod fields;
pub mod grobner;
mod identities;
pub mod integers;
mod left_scalar_mul;
pub mod linalg;
mod poly;
mod rings;

pub mod util;

#[cfg(test)]
pub(crate) mod test_support;

pub use fft::{
    bluestein_convolution_domain, bluestein_convolution_length, bluestein_transform, evaluate,
    fft_multiplication_crossover, interpolate, multiply, multiply_above, multiply_over_domain,
    powers_of, try_interpolate, try_multiply_via_fft, with_bluestein, DomainError, FFTDomain,
    InterpolateError,
};
#[doc(hidden)]
pub use fft::{bluestein_crossover_unstable, dft_unstable};
pub use fields::{FiniteField, KnownOrder, ParseFieldElementError};
pub use identities::{One, Zero};
#[doc(hidden)]
pub use poly::{
    div_with_remainder_long_unstable, div_with_remainder_newton_unstable,
    from_zeros_crossover_unstable, interpolate_quadratic_unstable, karatsuba_base_case_unstable,
    karatsuba_unstable, multiply_multivariate_unstable, multivariate_multiply_route_unstable,
    newton_crossover_unstable, newton_is_cheaper_at_unstable, product_of_factors_unstable,
    subproduct_evaluate_unstable, subproduct_interpolate_unstable, tree_crossover_unstable,
    MultiplyRoute,
};
pub use poly::{
    factorize, gcd, graeffe_2, graeffe_2_over_domain, graeffe_all_roots, graeffe_l, graeffe_root,
    graeffe_root_with_stats, inverse_exponent, is_irreducible, is_permutation_exponent,
    is_permutation_polynomial, lagrange_interpolate, lcm, multipoint_evaluate, partial_bezout,
    permutation_exponents, pow_mod, resultant, resultant_at_formal_degrees,
    resultant_from_coefficients, roots, xgcd, BuildMonomialHasher, GcdRoute, GraeffeError,
    GraeffeStats, Monomial, MonomialHasher, MonomialMap, MonomialOrder, MonomialSet,
    MultivariatePolynomial, Polynomial, PolynomialParams, PowerPermutation, SquarefreeError,
    SubgroupRoute, UnivariatePolynomial,
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
