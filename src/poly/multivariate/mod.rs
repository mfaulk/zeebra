//! Multivariate polynomials over finite fields.

mod dense_index;
mod monomial;
mod monomial_arithmetic;
mod monomial_hash;
mod monomial_order;
mod multi_poly_parser;
mod multivariate_gcd;
mod sparse_multivariate_compose;
mod sparse_multivariate_multiply;
mod sparse_multivariate_polynomial;
mod sparse_multivariate_polynomial_arithmetic;
mod sparse_multivariate_polynomial_conversions;
mod term;
mod term_arithmetic;

pub use monomial::Monomial;
pub use monomial_hash::{BuildMonomialHasher, MonomialHasher, MonomialMap, MonomialSet};
pub use monomial_order::{MonomialOrder, WeightedOrder, WeightedOrderError, WeightedTieBreak};
pub use multivariate_gcd::{GcdError, GcdRoute, SquarefreeError};
pub use sparse_multivariate_multiply::{
    multiply_multivariate_unstable, multivariate_multiply_route_unstable, MultiplyRoute,
};
pub use sparse_multivariate_polynomial::SparseMultiPoly as MultivariatePolynomial;
pub use sparse_multivariate_polynomial_arithmetic::{CrossCallRepeats, NormalFormCounts};
