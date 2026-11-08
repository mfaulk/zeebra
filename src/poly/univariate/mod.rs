//! A univariate polynomial over a finite field.
//!
//! A polynomial is an expression of the form:
//!      a_n x^n + a_{n-1} x^{n-1} + \dots + a_1 x + a_0
//! where n is a non-negative integer and the coefficients a_i are drawn from some set.
//! Here, the coefficients belong to a finite field.
//!
//! The zero polynomial contains the single monomial '0'. Its degree is undefined.

mod dense_polynomial;
mod dense_polynomial_arithmetic;
mod div_with_remainder;
// Measurement and differential-testing hooks for `examples/division_crossover.rs`, not API. The
// two routes have to be separately reachable or the crossover cannot be swept and the differential
// test could only ever check whichever route the shipped constant happens to select.
#[doc(hidden)]
pub use div_with_remainder::{
    div_with_remainder_long_unstable, div_with_remainder_newton_unstable,
    newton_crossover_unstable, newton_is_cheaper_at_unstable,
};
mod factorize;
mod gcd;
mod graeffe;
mod karatsuba;
mod lagrange_interpolation;
mod polynomial_trait;
mod pow_mod;
mod power_permutation;
mod resultant;
pub use resultant::{resultant, resultant_at_formal_degrees, resultant_from_coefficients};
mod roots;
mod univariate_parser;

use crate::FiniteField;
pub use dense_polynomial::{DensePolynomial as UnivariatePolynomial, PolynomialParams};
#[cfg(test)]
pub(crate) use factorize::trace_to_gf2;
pub use factorize::{factorize, is_irreducible};
pub use gcd::{gcd, lcm, partial_bezout, xgcd};
pub use graeffe::{
    graeffe_2, graeffe_2_over_domain, graeffe_all_roots, graeffe_l, graeffe_root,
    graeffe_root_with_stats, GraeffeError, GraeffeStats, SubgroupRoute,
};
// The schoolbook-or-Karatsuba route, which `fft::multiply` dispatches to below its own crossover.
// Crate-internal: it is reached publicly through `fft::multiply`, and `Mul` is the operator a
// caller reaches for otherwise.
pub(crate) use karatsuba::multiply_dense;
// Measurement hooks for `examples/karatsuba_crossover.rs`, not API.
#[doc(hidden)]
pub use karatsuba::{karatsuba_base_case_unstable, karatsuba_unstable};
pub use lagrange_interpolation::interpolate as lagrange_interpolate;
// The cubic textbook form, for differential testing against the quadratic one. Not public: it was
// not public before, and it is strictly slower. Re-exported here, unused for now, so that #162's
// subproduct tree can diff against it from its own module rather than reintroducing it.
#[cfg(test)]
#[allow(unused_imports)]
pub(crate) use lagrange_interpolation::interpolate_reference as lagrange_interpolate_reference;
pub use polynomial_trait::Polynomial;
pub use pow_mod::pow_mod;
pub use power_permutation::{
    inverse_exponent, is_permutation_exponent, is_permutation_polynomial, permutation_exponents,
    PowerPermutation,
};
pub use roots::roots;
use std::cmp::max;

// Trim leading terms with zero coefficient so the highest power of x has non-zero coefficient.
pub fn trim<F: FiniteField>(coefficients: &mut Vec<F>) {
    // [] --> [0]
    if coefficients.is_empty() {
        coefficients.push(F::zero());
        return;
    }

    // Index of last non-zero coefficient.
    if let Some(num_trailing_zeros) = coefficients.iter().rev().position(|&f| f != F::zero()) {
        let result_len = max(1, coefficients.len() - num_trailing_zeros);
        coefficients.truncate(result_len);
    } else {
        // All elements are zero. Truncate to a single zero.
        coefficients.truncate(1);
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        fields::PrimeFieldElement64, identities::Zero, poly::univariate::trim, FiniteField,
    };

    fn get_elements(values: Vec<u64>) -> Vec<PrimeFieldElement64<13>> {
        values
            .iter()
            .map(|v| PrimeFieldElement64::new(*v))
            .collect()
    }

    #[test]
    // [] --> [0]
    fn test_trim_empty_slice() {
        type F = PrimeFieldElement64<13>;
        let mut empty: Vec<F> = vec![];
        trim(&mut empty);
        assert_eq!(empty, vec![F::zero()]);
    }

    #[test]
    // [0] --> [0]
    fn test_trim_zero() {
        let mut zero = vec![PrimeFieldElement64::<13>::zero()];
        trim(&mut zero);
        assert_eq!(zero, vec![PrimeFieldElement64::<13>::zero()]);
    }

    #[test]
    // [0,0,...,0] --> [0]
    fn test_trim_zeros() {
        let mut zeros = vec![PrimeFieldElement64::<13>::zero(); 3];
        trim(&mut zeros);
        assert_eq!(zeros, vec![PrimeFieldElement64::<13>::zero()]);
    }

    #[test]
    // [a, b, c, 0,  ..., 0] -> [a, b, c]
    fn test_trim() {
        let mut coefficients = get_elements(vec![1, 2, 0, 4, 0, 0, 0]);
        let expected = get_elements(vec![1, 2, 0, 4]);
        trim(&mut coefficients);
        assert_eq!(coefficients, expected);
    }
}
