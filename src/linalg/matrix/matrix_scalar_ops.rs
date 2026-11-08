//! Matrix-Scalar multiplication.

use crate::{linalg::Matrix, Ring};
use std::ops::Mul;

impl<T: Ring> Matrix<T> {
    /// Scale every element by `factor`, in the matrix's own buffer.
    ///
    /// What the owned `Mul` spellings route through: `&m * &c` has to allocate, so scaling an
    /// owned matrix through it allocated a second buffer and dropped the one it was handed.
    pub fn scale_assign(&mut self, factor: &T) {
        for a in self.elements.iter_mut() {
            *a *= *factor;
        }
    }
}

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

// The remaining ownership spellings. Each delegates to the one with the same ownership, so an
// owned matrix is scaled in place rather than copied into a fresh buffer. `impl_mul_variants!`
// does not serve here: the operands have different types, and that macro is for `T * T`.
impl<T: Ring> Mul<T> for &Matrix<T> {
    type Output = Matrix<T>;

    fn mul(self, scalar: T) -> Self::Output {
        self * &scalar
    }
}

impl<T: Ring> Mul<&T> for Matrix<T> {
    type Output = Matrix<T>;

    fn mul(mut self, scalar: &T) -> Self::Output {
        self.scale_assign(scalar);
        self
    }
}

impl<T: Ring> Mul<T> for Matrix<T> {
    type Output = Matrix<T>;

    fn mul(self, scalar: T) -> Self::Output {
        self * &scalar
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        fields::Zp65537,
        identities::{One, Zero},
        linalg::Matrix,
        FiniteField,
    };

    fn fixture() -> (Matrix<Zp65537>, Zp65537) {
        type F = Zp65537;
        let m = Matrix::<F>::new(2, 3, &[1, 2, 3, 4, 5, 6].map(F::new));
        (m, F::new(7))
    }

    /// Every ownership spelling of `m * c` and `c * m` returns what the borrowed `&m * &c` does.
    #[test]
    fn test_every_ownership_spelling_agrees_with_the_borrowed_one() {
        let (m, c) = fixture();
        let expected = &m * &c;
        assert_eq!(&m * c, expected);
        assert_eq!(m.clone() * &c, expected);
        assert_eq!(m.clone() * c, expected);
        assert_eq!(&c * &m, expected);
        assert_eq!(&c * m.clone(), expected);
        assert_eq!(c * &m, expected);
        assert_eq!(c * m, expected);
    }

    /// `scale_assign` leaves the matrix equal to what the allocating `Mul` would have returned.
    #[test]
    fn test_scale_assign_matches_the_allocating_multiplication() {
        let (m, c) = fixture();
        let expected = &m * &c;
        let mut scaled = m;
        scaled.scale_assign(&c);
        assert_eq!(scaled, expected);
    }

    /// `scale_assign` preserves the shape, so a non-square matrix is not silently transposed.
    #[test]
    fn test_scale_assign_preserves_the_shape() {
        let (mut m, c) = fixture();
        m.scale_assign(&c);
        assert_eq!(m.shape(), (2, 3));
    }

    /// Scaling by zero gives the zero matrix; scaling by one is the identity on the matrix.
    #[test]
    fn test_scaling_by_zero_and_by_one() {
        type F = Zp65537;
        let (m, _) = fixture();

        let mut zeroed = m.clone();
        zeroed.scale_assign(&F::zero());
        assert_eq!(zeroed, Matrix::<F>::zero(2, 3));
        assert_eq!(m.clone() * F::zero(), Matrix::<F>::zero(2, 3));

        let mut unchanged = m.clone();
        unchanged.scale_assign(&F::one());
        assert_eq!(unchanged, m);
        assert_eq!(m.clone() * F::one(), m);
    }
}
