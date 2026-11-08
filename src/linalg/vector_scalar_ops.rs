//! Vector-Scalar multiplication.

use crate::{linalg::vector::Vector, Ring};
use std::ops::Mul;

impl<T: Ring> Vector<T> {
    /// Scale every element by `factor`, in the vector's own buffer.
    ///
    /// What the owned `Mul` spellings route through: `&v * &c` has to allocate, so scaling an
    /// owned vector through it allocated a second buffer and dropped the one it was handed.
    pub fn scale_assign(&mut self, factor: &T) {
        for a in self.elements.iter_mut() {
            *a *= *factor;
        }
    }
}

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

// The remaining ownership spellings. Each delegates to the one with the same ownership, so an
// owned vector is scaled in place rather than copied into a fresh buffer. `impl_mul_variants!`
// does not serve here: the operands have different types, and that macro is for `T * T`.
impl<T: Ring> Mul<T> for &Vector<T> {
    type Output = Vector<T>;

    fn mul(self, scalar: T) -> Self::Output {
        self * &scalar
    }
}

impl<T: Ring> Mul<&T> for Vector<T> {
    type Output = Vector<T>;

    fn mul(mut self, scalar: &T) -> Self::Output {
        self.scale_assign(scalar);
        self
    }
}

impl<T: Ring> Mul<T> for Vector<T> {
    type Output = Vector<T>;

    fn mul(self, scalar: T) -> Self::Output {
        self * &scalar
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        fields::Zp65537,
        identities::{One, Zero},
        linalg::{vector::VectorType, Vector},
        FiniteField,
    };

    fn fixture() -> (Vector<Zp65537>, Zp65537) {
        type F = Zp65537;
        let v = Vector::<F>::new(&[1, 2, 3].map(F::new));
        (v, F::new(7))
    }

    /// Every ownership spelling of `v * c` and `c * v` returns what the borrowed `&v * &c` does.
    #[test]
    fn test_every_ownership_spelling_agrees_with_the_borrowed_one() {
        let (v, c) = fixture();
        let expected = &v * &c;
        assert_eq!(&v * c, expected);
        assert_eq!(v.clone() * &c, expected);
        assert_eq!(v.clone() * c, expected);
        assert_eq!(&c * &v, expected);
        assert_eq!(&c * v.clone(), expected);
        assert_eq!(c * &v, expected);
        assert_eq!(c * v, expected);
    }

    /// `scale_assign` leaves the vector equal to what the allocating `Mul` would have returned.
    #[test]
    fn test_scale_assign_matches_the_allocating_multiplication() {
        let (v, c) = fixture();
        let expected = &v * &c;
        let mut scaled = v;
        scaled.scale_assign(&c);
        assert_eq!(scaled, expected);
    }

    /// A row vector stays a row vector through `scale_assign` and through the owned spellings.
    #[test]
    fn test_scaling_preserves_the_vector_type() {
        let (v, c) = fixture();
        let row = v.transpose();
        assert_eq!(row.vector_type, VectorType::Row);

        let mut scaled = row.clone();
        scaled.scale_assign(&c);
        assert_eq!(scaled.vector_type, VectorType::Row);
        assert_eq!((row.clone() * c).vector_type, VectorType::Row);
        assert_eq!((c * row).vector_type, VectorType::Row);
    }

    /// Scaling by zero gives the zero vector; scaling by one is the identity on the vector.
    #[test]
    fn test_scaling_by_zero_and_by_one() {
        type F = Zp65537;
        let (v, _) = fixture();

        let mut zeroed = v.clone();
        zeroed.scale_assign(&F::zero());
        assert_eq!(zeroed, Vector::<F>::zero(3));
        assert_eq!(v.clone() * F::zero(), Vector::<F>::zero(3));

        let mut unchanged = v.clone();
        unchanged.scale_assign(&F::one());
        assert_eq!(unchanged, v);
        assert_eq!(v.clone() * F::one(), v);
    }
}
