//! Dense storage for finite-field elimination, with the sparse implementation's exact contract.
//!
//! Two representations, because they answer different questions. [`DenseRows`] stores the whole
//! matrix densely and is what makes a sparse/dense comparison mean anything: the same pivot rule,
//! the same normalization, and the same statistics, so the only thing that differs is storage.
//! [`DenseAccumulator`] keeps the matrix sparse and makes only the row being reduced dense, which
//! replaces a sorted merge per row operation with a scatter into a buffer reused across the whole
//! elimination.
//!
//! A nonzero is counted the way the sparse path counts one — a field element that is not zero — so
//! `peak_nonzeros` and the entry budget mean the same thing under every backend. What is *not*
//! comparable is the allocation: [`DenseRows`] holds `num_rows * num_columns` cells whatever the
//! budget says, and the budget bounds entries rather than bytes. [`DenseAccumulator`] holds one
//! row.

mod accumulator;
mod rows;

pub use accumulator::DenseAccumulator;
pub use rows::DenseRows;

pub(crate) use accumulator::{accumulated_reduce_rows_against_pivots, accumulated_row_echelon};
pub(crate) use rows::{dense_reduce_rows_against_pivots, dense_row_echelon};
