//! Errors that can occur when working with matrices.

use std::fmt::{Display, Formatter};

#[derive(Debug, Eq, PartialEq)]
/// Errors that can occur when working with matrices.
pub enum Error {
    /// The given index in row or column major order was out of bounds.
    IndexOutOfBounds(usize),

    /// The given (row,column) indices were out of bounds.
    IndicesOutOfBounds(usize, usize),

    /// The dimensions given did not match the elements provided
    DimensionMismatch,

    /// There were not enough elements to fill the array.
    NotEnoughElements { num_elements: usize },

    /// The matrix is not square.
    NotSquare { num_rows: usize, num_columns: usize },

    /// The matrix is not invertible.
    NotInvertible,

    /// The algorithm cannot proceed without pivoting.
    PivotingRequired,
}

impl Display for Error {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::IndicesOutOfBounds(row, column) => {
                write!(f, "Indices ({},{}) out of bounds", row, column)
            }
            Error::IndexOutOfBounds(index) => write!(f, "Index {} out of bounds", index),
            Error::DimensionMismatch => write!(f, "Dimension mismatch"),
            Error::NotEnoughElements { num_elements } => {
                write!(f, "Not enough elements: {}", num_elements)
            }
            Error::NotSquare {
                num_rows,
                num_columns,
            } => write!(f, "Matrix is not square: {}x{}", num_rows, num_columns),
            Error::NotInvertible => write!(f, "Matrix is not invertible"),
            Error::PivotingRequired => write!(f, "Pivoting required"),
        }
    }
}
