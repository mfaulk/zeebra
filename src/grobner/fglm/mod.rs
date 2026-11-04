//! Monomial-order conversion for zero-dimensional ideals, by the FGLM algorithm.
//!
//! A lex Gröbner basis is what solving needs and the most expensive one to compute directly. For a
//! zero-dimensional ideal, `R/I` is a finite-dimensional vector space, and FGLM converts a basis
//! under a cheaper order — grevlex, which M16 made F4's best — into the lex basis by linear
//! algebra over that space rather than by more Gröbner computation.
//!
//! The design, the measured baseline it is justified by, and the cases where conversion is the
//! wrong choice are in `docs/MILESTONE-FGLM-SOLVING.md`.

mod border;
mod conversion;
mod errors;
mod incremental_span;
mod multiplication;
mod options;
mod quotient_algebra;
mod quotient_basis;
pub mod shape;
mod statistics;

/// Lexicographic bases from Singular, for the differential tests. Test-only: it is reference data,
/// not library code.
#[cfg(test)]
mod reference_bases;

pub use border::{BorderIndex, ColumnTarget};
pub use conversion::{
    fglm_to_lex, fglm_to_lex_checked, fglm_to_lex_with_options, is_grobner_basis,
};
pub use errors::FglmError;
pub use incremental_span::{Dependence, IncrementalSpan};
pub use multiplication::MultiplicationOperator;
pub use options::{FglmOptions, OperatorConstruction, OperatorStorage};
pub use quotient_algebra::{QuotientAlgebra, QuotientStatistics};
pub use quotient_basis::{classify_ideal, IdealClass, QuotientBasis};
pub use shape::{separating_variables, shape_lex_basis, shape_report, ShapeError, ShapeReport};
pub use statistics::{BorderStatistics, FglmMemory, FglmStageTimings, FglmStatistics};
