//! Linear Algebra

mod crout;
pub mod dense;
pub mod echelon;
mod gauss_jordan;
mod matrix;
pub mod sparse;
mod vector;
mod vector_indexing;
mod vector_ops;
mod vector_scalar_ops;

pub use crout::{crout_lu, crout_lu_pivoting};
pub use dense::DenseRows;
pub use echelon::{reduce_rows_against_pivots_with, row_echelon_with, Backend};
pub use gauss_jordan::gauss_jordan_elimination;
pub use matrix::*;
pub use vector::{Vector, VectorParams};
