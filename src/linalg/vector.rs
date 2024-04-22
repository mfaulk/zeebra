//! Dense Vector

use crate::Ring;
use proptest::{
    arbitrary::{any, Arbitrary},
    collection::vec,
    prelude::{BoxedStrategy, Strategy},
};

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum VectorType {
    Column,
    Row,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Vector<T: Ring> {
    /// Elements of the vector.
    pub(crate) elements: Vec<T>,

    /// Row or column vector.
    pub vector_type: VectorType,
}

impl<T: Ring> Vector<T> {
    /// A column vector with the given elements.
    pub fn new(elements: &[T]) -> Self {
        Self {
            elements: elements.to_vec(),
            vector_type: VectorType::Column,
        }
    }

    /// The zero column vector.
    pub fn zero(size: usize) -> Self {
        Self {
            elements: vec![T::ZERO; size],
            vector_type: VectorType::Column,
        }
    }

    /// Number of elements in the vector.
    pub fn len(&self) -> usize {
        self.elements.len()
    }

    /// The elements of the vector.
    pub fn elements(&self) -> &Vec<T> {
        &self.elements
    }

    /// The elements of the vector, mutable.
    pub fn elements_mut(&mut self) -> &mut Vec<T> {
        &mut self.elements
    }

    /// Transpose this vector.
    pub fn transpose(&self) -> Self {
        let vector_type = match self.vector_type {
            VectorType::Column => VectorType::Row,
            VectorType::Row => VectorType::Column,
        };
        Self {
            elements: self.elements.clone(),
            vector_type,
        }
    }

    /// Apply a function to each element of the vector.
    pub fn apply<F>(&self, f: F) -> Self
    where
        F: Fn(&T) -> T,
    {
        let elements = self.elements.iter().map(f).collect();
        Self {
            elements,
            vector_type: self.vector_type,
        }
    }

    /// Apply a function, in place, to each element of the vector.
    pub fn apply_mut<F>(&mut self, f: F)
    where
        F: Fn(&T) -> T,
    {
        self.elements.iter_mut().for_each(|x| *x = f(x));
    }

    /// Dot product of two vectors.
    pub fn dot(&self, other: &Self) -> T {
        assert_eq!(self.elements.len(), other.elements.len());
        let mut sum = T::ZERO;
        for i in 0..self.elements.len() {
            sum += self.elements[i] * other.elements[i];
        }
        sum
    }
}

// TODO: as matrix

// TODO: try_from matrix

/// Implement Arbitrary
impl<T: Ring + 'static> Arbitrary for Vector<T> {
    type Parameters = usize; // size
    fn arbitrary_with(size: Self::Parameters) -> Self::Strategy {
        vec(any::<T>(), size)
            .prop_map(|elements| Vector::new(&elements))
            .boxed()
    }

    type Strategy = BoxedStrategy<Self>;
}

#[cfg(test)]
mod tests {
    use super::Vector;
    use crate::{fields::Zp541, identities::One};
    use proptest::prelude::*;

    proptest! {
        #[test]
        fn test_vector_transpose(v in any::<Vector<Zp541>>()) {
            let vt = v.transpose();
            assert_eq!(v.elements, vt.elements);
            assert_ne!(v.vector_type, vt.vector_type);
        }

        #[test]
        fn test_vector_apply(v in any::<Vector<Zp541>>()) {
            let w = v.apply(|x| x + &Zp541::one());
            assert_eq!(v.elements.len(), w.elements.len());
            assert_eq!(v.vector_type, w.vector_type);
            for i in 0..v.elements.len() {
                assert_eq!(v.elements[i] + &Zp541::one(), w.elements[i]);
            }
        }
    }
}
