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

// V * s = V
// impl_mul_variants!([T: Ring], Vector<T>, T: Ring, Vector<T>);
