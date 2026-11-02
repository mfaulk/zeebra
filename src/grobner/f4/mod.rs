//! Faugère's F4 algorithm for computing a Gröbner basis.
//!
//! Buchberger reduces one S-polynomial at a time and throws most of that work away: on katsura-5
//! under grevlex, 39 of 49 reductions produce zero. F4 instead takes a whole batch of critical
//! pairs, works out symbolically which polynomial multiples the batch's reductions could possibly
//! need, lays them out as the rows of one sparse matrix over a finite field, and reduces the lot
//! by Gaussian elimination. The cancellations Buchberger pays full price to rediscover become row
//! operations shared across the batch.
//!
//! The pipeline is one module per stage:
//!
//! - [`symbolic`] turns a batch of pairs into a set of rows closed under reduction.
//! - [`macaulay`] lays those rows out as a sparse matrix with monomials for columns.
//! - [`crate::linalg::sparse`] reduces it.
//! - [`reduction`] extracts the rows whose leading monomial is new.
//!
//! [`super::buchberger`] is unchanged and remains the correctness oracle.
//!
//! See Faugère, J.-C. (1999), *A new efficient algorithm for computing Gröbner bases (F4)*,
//! Journal of Pure and Applied Algebra 139, 61-88, and `docs/MILESTONE-F4.md` for the invariants
//! this implementation is built on.

pub mod macaulay;
pub mod options;
pub mod reduction;
pub mod statistics;
pub mod symbolic;

pub use macaulay::{BuildBudgetExceeded, MacaulayMatrix};
pub use options::{F4Error, F4Options};
pub use reduction::{reduce_batch, BatchOutcome};
pub use statistics::{BatchStatistics, F4Statistics};
pub use symbolic::{
    symbolic_preprocessing, symbolic_preprocessing_within, MonicBasis, MonicElement, Preprocessed,
    PreprocessedRow, RowBudgetExceeded, RowKind,
};
