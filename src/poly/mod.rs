//! Polynomials over finite fields.

mod multivariate;
mod univariate;

#[doc(hidden)]
pub use multivariate::{
    multiply_multivariate_unstable, multivariate_multiply_route_unstable, MultiplyRoute,
};
pub use multivariate::{
    BlockOrder, BlockOrderError, BlockOrderKind, BuildMonomialHasher, CrossCallRepeats, GcdError,
    GcdRoute, Monomial, MonomialHasher, MonomialMap, MonomialOrder, MonomialSet,
    MultivariatePolynomial, NormalFormCounts, NormalFormError, SquarefreeError, WeightedOrder,
    WeightedOrderError, WeightedTieBreak,
};
pub(crate) use univariate::multiply_dense;
#[doc(hidden)]
pub use univariate::{
    div_with_remainder_long_unstable, div_with_remainder_newton_unstable,
    from_zeros_crossover_unstable, gcd_classical_unstable, gcd_half_unstable,
    interpolate_quadratic_unstable, karatsuba_base_case_unstable, karatsuba_unstable,
    newton_crossover_unstable, newton_floor_unstable, newton_is_cheaper_at_unstable,
    newton_is_cheaper_unstable, product_of_factors_unstable, subproduct_evaluate_unstable,
    subproduct_interpolate_unstable, tree_crossover_unstable,
};
pub use univariate::{
    factorize, gcd, graeffe_2, graeffe_2_over_domain, graeffe_all_roots, graeffe_l, graeffe_root,
    graeffe_root_with_stats, inverse_exponent, is_irreducible, is_permutation_exponent,
    is_permutation_polynomial, lagrange_interpolate, lcm, multipoint_evaluate, partial_bezout,
    permutation_exponents, pow_mod, resultant, resultant_at_formal_degrees,
    resultant_from_coefficients, roots, xgcd, GraeffeError, GraeffeStats, Polynomial,
    PolynomialParams, PowerPermutation, SubgroupRoute, UnivariatePolynomial,
};

#[cfg(test)]
pub(crate) use univariate::trace_to_gf2;
