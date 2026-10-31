//! Vector-Vector operations.

use crate::impl_add_variants;
use crate::{linalg::vector::Vector, Ring};
use std::ops::Add;

/// Vectors of the same size and type may be added element-wise.
impl<T: Ring> Add for &Vector<T> {
    type Output = Vector<T>;

    fn add(self, rhs: Self) -> Self::Output {
        assert_eq!(
            self.elements.len(),
            rhs.elements.len(),
            "elements.len(): {} != {}",
            self.elements.len(),
            rhs.elements.len()
        );

        assert_eq!(
            self.vector_type, rhs.vector_type,
            "vector_type: {:?} != {:?}",
            self.vector_type, rhs.vector_type
        );

        let elements = self
            .elements
            .iter()
            .zip(rhs.elements.iter())
            .map(|(a, b)| *a + *b)
            .collect();
        Self::Output {
            elements,
            vector_type: self.vector_type,
        }
    }
}

impl_add_variants!([T: Ring], Vector<T>);
