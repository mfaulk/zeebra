mod crout;
pub mod dense;
pub mod echelon;
mod gauss_jordan;
mod matrix;
mod pivots;
pub mod sparse;
mod vector;
mod vector_indexing;
mod vector_ops;
mod vector_scalar_ops;
#[cfg(feature = "research-work")]
pub mod work;

pub use crout::{crout_lu, crout_lu_pivoting};
pub use dense::{DenseAccumulator, DenseRows};
pub use echelon::{reduce_rows_against_pivots_with, row_echelon_with, Backend};
pub use gauss_jordan::gauss_jordan_elimination;
pub use matrix::*;
pub(crate) use pivots::PivotIndex;
pub use vector::{Vector, VectorParams};
