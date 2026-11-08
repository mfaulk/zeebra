//! Vector-Scalar multiplication.

use crate::{linalg::vector::Vector, Ring};
use std::ops::Mul;

impl<T: Ring> Mul<&T> for &Vector<T> {
    type Output = Vector<T>;

    fn mul(self, scalar: &T) -> Self::Output {
        let elements = self.elements.iter().map(|a| *a * *scalar).collect();
        Self::Output {
            elements,
            vector_type: self.vector_type,
        }
    }
}

// The remaining ownership spellings, each delegating to the one above so there is a single
// definition of what scaling a vector means. `impl_mul_variants!` does not serve here: the
// operands have different types, and that macro is for `T * T`.
impl<T: Ring> Mul<T> for &Vector<T> {
    type Output = Vector<T>;

    fn mul(self, scalar: T) -> Self::Output {
        self * &scalar
    }
}

impl<T: Ring> Mul<&T> for Vector<T> {
    type Output = Vector<T>;

    fn mul(self, scalar: &T) -> Self::Output {
        &self * scalar
    }
}

impl<T: Ring> Mul<T> for Vector<T> {
    type Output = Vector<T>;

    fn mul(self, scalar: T) -> Self::Output {
        &self * &scalar
    }
}
