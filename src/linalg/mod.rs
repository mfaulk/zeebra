#[cfg(feature = "research-work")]
pub mod concurrent;
mod crout;
pub mod dense;
pub mod echelon;
#[cfg(feature = "research-multirow")]
pub mod multirow {
    //! Research-only multirow sparse pivot reuse (#715); not a production path.
    pub use super::dense::band::{
        census, mode, take_census, with_mode, Census, MatrixCensus, Mode,
    };
}
mod gauss_jordan;
pub mod gf2;
mod matrix;
mod pivots;
#[cfg(feature = "research-work")]
pub mod selective;
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
