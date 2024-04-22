//! Linear Algebra

mod crout;
mod gauss_jordan;
mod matrix;
mod vector;
mod vector_indexing;
mod vector_ops;
mod vector_scalar_ops;

pub use crout::{crout_lu, crout_lu_pivoting};
pub use gauss_jordan::gauss_jordan_elimination;
pub use matrix::*;
pub use vector::Vector;
