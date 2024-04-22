//! Arithmetic operations on monomials.

use crate::Monomial;
use std::ops;
use crate::impl_mul_variants;

// &Monomial * &Monomial
impl<const N: usize> ops::Mul<&Monomial<N>> for &Monomial<N> {
    type Output = Monomial<N>;

    fn mul(self, rhs: &Monomial<N>) -> Self::Output {
        let mut exponents = [0u32; N];
        for i in 0..N {
            exponents[i] = self.exponents[i] + rhs.exponents[i];
        }

        Monomial::new(&exponents)
    }
}

impl_mul_variants!([const N: usize], Monomial<N>);

impl<const N: usize> Monomial<N> {
    pub fn checked_div(&self, rhs: &Self) -> Option<Self> {
        let mut exponents = [0u32; N];
        for i in 0..N {
            if self.exponents[i] < rhs.exponents[i] {
                return None;
            }
            exponents[i] = self.exponents[i] - rhs.exponents[i];
        }

        Some(Self::new(&exponents))
    }
}

#[cfg(test)]
mod tests {
    use crate::Monomial;
    use proptest::prelude::*;

    proptest! {
        #[test]
        fn test_mul_with_one_is_self(x in any::<Monomial<3>>()) {
            let one = Monomial::<3>::one();
            prop_assert_eq!(x * &one, x);
        }
    }

    #[test]
    fn test_checked_div() {
        let a = Monomial::<3>::new(&[1, 2, 3]);
        let b = Monomial::<3>::new(&[1, 1, 1]);
        let c = Monomial::<3>::new(&[0, 1, 2]);
        assert_eq!(a.checked_div(&b), Some(c));

        let d = Monomial::<3>::new(&[2, 1, 1]);
        assert_eq!(a.checked_div(&d), None);
    }

    #[test]
    #[should_panic]
    #[ignore]
    // Should panic if any exponent overflows.
    fn test_overflow_panics() {
        todo!()
    }
}
