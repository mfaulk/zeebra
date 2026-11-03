//! Dense storage for finite-field elimination, with the sparse implementation's exact contract.
//!
//! [`DenseRows`] stores the whole matrix densely and is what makes a sparse/dense comparison mean
//! anything: the same pivot rule, the same normalization, and the same statistics, so the only
//! thing that differs is storage.
//!
//! A nonzero is counted the way the sparse path counts one — a field element that is not zero — so
//! `peak_nonzeros` and the entry budget mean the same thing under either backend. What is *not*
//! comparable is the allocation: [`DenseRows`] holds `num_rows * num_columns` cells whatever the
//! budget says, and the budget bounds entries rather than bytes.

mod rows;

pub use rows::DenseRows;

pub(crate) use rows::{dense_reduce_rows_against_pivots, dense_row_echelon};
