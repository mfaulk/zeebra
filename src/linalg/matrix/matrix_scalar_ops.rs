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

// TODO: impl_mul_variants. The operands have different types. The operation is commutative.
