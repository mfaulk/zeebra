//! Polynomials over finite fields.

mod multivariate;
mod univariate;

pub use multivariate::{Monomial, MonomialOrder, MultivariatePolynomial};
pub(crate) use univariate::multiply_dense;
pub use univariate::{
    factorize, gcd, graeffe_2, graeffe_2_over_domain, graeffe_l, graeffe_root,
    graeffe_root_with_stats, inverse_exponent, is_irreducible, is_permutation_exponent,
    is_permutation_polynomial, lagrange_interpolate, lcm, permutation_exponents, pow_mod,
    resultant, resultant_at_formal_degrees, roots, GraeffeError, GraeffeStats, Polynomial,
    PolynomialParams, PowerPermutation, SubgroupRoute, UnivariatePolynomial,
};
#[doc(hidden)]
pub use univariate::{karatsuba_base_case_unstable, karatsuba_unstable};

#[cfg(test)]
pub(crate) use univariate::trace_to_gf2;
