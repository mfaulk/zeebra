//! Monomial-order conversion for zero-dimensional ideals, by the FGLM algorithm.
//!
//! A lex Gröbner basis is what solving needs and the most expensive one to compute directly. For a
//! zero-dimensional ideal, `R/I` is a finite-dimensional vector space, and FGLM converts a basis
//! under a cheaper order — grevlex, which M16 made F4's best — into the lex basis by linear
//! algebra over that space rather than by more Gröbner computation.
//!
//! The design, the measured baseline it is justified by, and the cases where conversion is the
//! wrong choice are in `docs/MILESTONE-FGLM-SOLVING.md`.

mod conversion;
mod errors;
mod incremental_span;
mod multiplication;
mod options;
mod quotient_algebra;
mod quotient_basis;
mod statistics;

pub use conversion::{
    fglm_to_lex, fglm_to_lex_checked, fglm_to_lex_with_options, is_grobner_basis,
};
pub use errors::FglmError;
pub use incremental_span::{Dependence, IncrementalSpan};
pub use multiplication::MultiplicationOperator;
pub use options::FglmOptions;
pub use quotient_algebra::QuotientAlgebra;
pub use quotient_basis::{classify_ideal, IdealClass, QuotientBasis};
pub use statistics::FglmStatistics;
