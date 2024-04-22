//! Matrix-Vector Multiplication.

use crate::{
    linalg::{
        vector::{Vector, VectorType},
        Matrix,
    },
    Ring,
};
use std::ops::Mul;

/// A*x = y
impl<T: Ring> Mul<&Vector<T>> for &Matrix<T> {
    type Output = Vector<T>;

    fn mul(self, x: &Vector<T>) -> Self::Output {
        assert_eq!(x.vector_type, VectorType::Column);
        assert_eq!(
            self.num_columns,
            x.elements.len(),
            "num_columns: {} != {}",
            self.num_columns,
            x.elements.len()
        );

        let mut product = vec![T::ZERO; self.num_rows];
        for i in 0..self.num_rows {
            for j in 0..self.num_columns {
                product[i] += self[[i, j]] * x.elements[j];
            }
        }

        Self::Output::new(&product)
    }
}

impl<T: Ring> Mul<&Matrix<T>> for &Vector<T> {
    type Output = Vector<T>;

    fn mul(self, rhs: &Matrix<T>) -> Self::Output {
        assert_eq!(self.vector_type, VectorType::Row);
        assert_eq!(
            self.elements.len(),
            rhs.num_rows,
            "num_rows: {} != {}",
            self.elements.len(),
            rhs.num_rows
        );

        let mut product = vec![T::ZERO; rhs.num_columns];
        for i in 0..rhs.num_columns {
            for j in 0..self.elements.len() {
                product[i] += self.elements[j] * rhs[[j, i]];
            }
        }

        Self::Output::new(&product)
    }
}

// TODO: impl_mul_variants
