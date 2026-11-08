//! Matrix-Scalar multiplication.

use crate::{linalg::Matrix, Ring};
use std::ops::Mul;

impl<T: Ring> Mul<&T> for &Matrix<T> {
    type Output = Matrix<T>;

    fn mul(self, scalar: &T) -> Self::Output {
        let elements = self.elements.iter().map(|a| *a * *scalar).collect();
        Self::Output {
            num_rows: self.num_rows,
            num_columns: self.num_columns,
            elements,
        }
    }
}

// The remaining ownership spellings, each delegating to the one above so there is a single
// definition of what scaling a matrix means. `impl_mul_variants!` does not serve here: the
// operands have different types, and that macro is for `T * T`.
impl<T: Ring> Mul<T> for &Matrix<T> {
    type Output = Matrix<T>;

    fn mul(self, scalar: T) -> Self::Output {
        self * &scalar
    }
}

impl<T: Ring> Mul<&T> for Matrix<T> {
    type Output = Matrix<T>;

    fn mul(self, scalar: &T) -> Self::Output {
        &self * scalar
    }
}

impl<T: Ring> Mul<T> for Matrix<T> {
    type Output = Matrix<T>;

    fn mul(self, scalar: T) -> Self::Output {
        &self * &scalar
    }
}
