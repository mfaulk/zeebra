//! Monomial-order conversion for zero-dimensional ideals, by the FGLM algorithm.
//!
//! A lex Gröbner basis is what solving needs and the most expensive one to compute directly. For a
//! zero-dimensional ideal, `R/I` is a finite-dimensional vector space, and FGLM converts a basis
//! under a cheaper order — grevlex, which M16 made F4's best — into the lex basis by linear
//! algebra over that space rather than by more Gröbner computation.
//!
//! The design, the measured baseline it is justified by, and the cases where conversion is the
//! wrong choice are in `docs/MILESTONE-FGLM-SOLVING.md`.

mod errors;
mod quotient_basis;

pub use errors::FglmError;
pub use quotient_basis::{classify_ideal, IdealClass, QuotientBasis};
