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
    newton_crossover_unstable, newton_floor_unstable, newton_is_cheaper_at_unstable,
    newton_is_cheaper_unstable, product_of_factors_unstable, subproduct_evaluate_unstable,
    subproduct_interpolate_unstable, tree_crossover_unstable, MultiplyRoute,
};
pub use poly::{
    factorize, gcd, graeffe_2, graeffe_2_over_domain, graeffe_all_roots, graeffe_l, graeffe_root,
    graeffe_root_with_stats, inverse_exponent, is_irreducible, is_permutation_exponent,
    is_permutation_polynomial, lagrange_interpolate, lcm, multipoint_evaluate, partial_bezout,
    permutation_exponents, pow_mod, resultant, resultant_at_formal_degrees,
    resultant_from_coefficients, roots, xgcd, BuildMonomialHasher, GcdError, GcdRoute,
    GraeffeError, GraeffeStats, Monomial, MonomialHasher, MonomialMap, MonomialOrder, MonomialSet,
    MultivariatePolynomial, NormalFormError, Polynomial, PolynomialParams, PowerPermutation,
    SquarefreeError, SubgroupRoute, UnivariatePolynomial, WeightedOrder, WeightedOrderError,
    WeightedTieBreak,
};
pub use rings::Ring;

/// The code examples in the README and in `docs/guide/`, compiled and run.
///
/// Those documents are where a reader meets the public API, so their examples are the ones most
/// worth keeping true. `cfg(doctest)` means this item exists only when doc tests are collected, so
/// the documents are not pulled into the rendered crate documentation — only their fenced Rust
/// blocks become tests. Every guide file is listed, because a guide added without a line here would
/// have examples nothing compiles.
#[cfg(doctest)]
#[doc = include_str!("../README.md")]
#[doc = include_str!("../docs/guide/benchmarking.md")]
#[doc = include_str!("../docs/guide/development.md")]
#[doc = include_str!("../docs/guide/external-engines.md")]
#[doc = include_str!("../docs/guide/f4.md")]
#[doc = include_str!("../docs/guide/finite-fields.md")]
#[doc = include_str!("../docs/guide/grobner-bases.md")]
#[doc = include_str!("../docs/guide/linear-algebra.md")]
#[doc = include_str!("../docs/guide/ntt.md")]
#[doc = include_str!("../docs/guide/number-theory.md")]
#[doc = include_str!("../docs/guide/polynomials.md")]
#[doc = include_str!("../docs/guide/reed-solomon.md")]
#[doc = include_str!("../docs/guide/solving-systems.md")]
#[doc = include_str!("../docs/guide/status.md")]
pub struct DocumentationExamples;
