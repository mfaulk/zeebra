use crate::impl_mul_variants;
use crate::Monomial;
use std::ops;

// &Monomial * &Monomial
impl<const N: usize> ops::Mul<&Monomial<N>> for &Monomial<N> {
    type Output = Monomial<N>;

    fn mul(self, rhs: &Monomial<N>) -> Self::Output {
        let mut exponents = [0u32; N];
        for i in 0..N {
            // Checked in every build, not only where `overflow-checks` is on. A wrapped exponent
            // is not a large monomial, it is a *different* monomial, so a release build would
            // silently compute in the wrong ring — and release is where this is called millions of
            // times. The carry test costs a compare per variable against an add that is already
            // there.
            exponents[i] = self.exponents()[i]
                .checked_add(rhs.exponents()[i])
                .expect("monomial exponent overflow");
        }

        Monomial::new(&exponents)
    }
}

impl_mul_variants!([const N: usize], Monomial<N>);

impl<const N: usize> Monomial<N> {
    pub fn checked_div(&self, rhs: &Self) -> Option<Self> {
        let mut exponents = [0u32; N];
        for i in 0..N {
            if self.exponents()[i] < rhs.exponents()[i] {
                return None;
            }
            exponents[i] = self.exponents()[i] - rhs.exponents()[i];
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

    /// Multiplying monomials adds exponents, which panics rather than wrapping on overflow.
    ///
    /// Regression test for a release-only defect: the addition used to be a plain `+`, so this
    /// test passed in debug, where `overflow-checks` is on, and failed in release, where the
    /// exponent wrapped and the product was a different monomial entirely.
    #[test]
    #[should_panic(expected = "monomial exponent overflow")]
    fn test_overflow_panics() {
        let a = Monomial::<3>::new(&[u32::MAX, 0, 0]);
        let b = Monomial::<3>::new(&[1, 0, 0]);
        let _product = &a * &b;
    }
}
