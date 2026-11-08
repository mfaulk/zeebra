//! Sparse linear algebra over a finite field.
//!
//! Built for F4, whose matrices are wide, tall, and a few percent dense, and whose rows come from
//! polynomials. The dense [`Matrix`](crate::linalg::Matrix) stays as it is — it is the oracle these
//! are tested against — and nothing here attempts to replace it. Above some density a dense
//! representation is the better choice; choosing between them automatically is deliberately not
//! done yet, because the measurements that would justify a threshold do not exist.

mod elimination;
mod matrix;
mod row;

pub use elimination::{
    back_substitute_pivots_within, reduced_row_echelon, reduced_row_echelon_within, row_echelon,
    row_echelon_within, EliminationStatistics,
};
pub use matrix::SparseMatrix;
pub use row::{NotCanonical, SparseRow};
