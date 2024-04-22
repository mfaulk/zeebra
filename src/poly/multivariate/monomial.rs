//! A term (monomial) of a multivariate polynomial.

use crate::FiniteField;
use proptest::{
    arbitrary::{any, Arbitrary},
    collection::vec,
    prelude::{BoxedStrategy, Strategy},
};
use rand::{distributions::Standard, prelude::Distribution, Rng};
use serde::{Deserialize, Serialize};
use std::fmt::{Display, Formatter};

/// A monomial x^e = x_0^e_0 * x_1^e_1 * ... * x_{n-1}^e_{n-1} in N variables.
#[derive(Eq, PartialEq, Copy, Clone, Debug, Deserialize, Hash, Serialize, Ord, PartialOrd)]
pub struct Monomial<const N: usize> {
    // Exponent of each variable
    #[serde(with = "serde_arrays")]
    pub(crate) exponents: [u32; N],
}

impl<const N: usize> Monomial<N> {
    /// A monomial in N variables.
    pub fn new(exponents: &[u32]) -> Self {
        assert_eq!(exponents.len(), N);
        let mut e = [0; N];
        e.copy_from_slice(exponents);
        Self { exponents: e }
    }

    /// A monomial in N variables, with a single variable raised to a given exponent.
    pub fn univariate(index: usize, exponent: u32) -> Self {
        let mut exponents = [0; N];
        exponents[index] = exponent;
        Self { exponents }
    }

    /// x^0 = 1
    pub fn one() -> Self {
        Self { exponents: [0; N] }
    }

    /// True if x = x^0 = 1.
    pub fn is_one(&self) -> bool {
        self.exponents.iter().all(|e| *e == 0)
    }

    /// The exponents e_0, e_1, ..., e_{n-1}.
    pub fn exponents(&self) -> &[u32] {
        &self.exponents
    }

    /// The total degree (sum of exponents).
    pub fn degree(&self) -> u64 {
        // Cast to u64 before summing to avoid overflow.
        self.exponents.iter().map(|e| *e as u64).sum()
    }

    /// Evaluate the monomial at the vector x.
    pub fn eval<F: FiniteField>(&self, x: &[F]) -> F {
        assert_eq!(x.len(), N);
        self.exponents
            .iter()
            .zip(x)
            .fold(F::one(), |acc, (e, x)| acc * x.pow(*e as u128))
    }

    /// The least common multiple of two monomials.
    pub fn lcm(a: &Self, b: &Self) -> Self {
        let mut lcm = [0; N];
        for i in 0..N {
            lcm[i] = std::cmp::max(a.exponents()[i], b.exponents()[i]);
        }
        Self::new(&lcm)
    }
}

/// Default
impl<const N: usize> Default for Monomial<N> {
    fn default() -> Self {
        Self::one()
    }
}

/// Display
impl<const N: usize> Display for Monomial<N> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let mut first = true;
        for (i, exponent) in self.exponents.iter().enumerate() {
            if *exponent > 0 {
                if !first {
                    write!(f, "*")?;
                }
                if *exponent > 1 {
                    write!(f, "x_{}^{}", i, exponent)?;
                } else {
                    write!(f, "x_{}", i)?;
                }
                first = false;
            }
        }
        Ok(())
    }
}

/// Distribution
impl<const N: usize> Distribution<Monomial<N>> for Standard {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Monomial<N> {
        let mut exponents = [0u32; N];
        for i in 0..N {
            exponents[i] = rng.gen();
        }
        Monomial::new(&exponents)
    }
}

/// Arbitrary
impl<const N: usize> Arbitrary for Monomial<N> {
    type Parameters = ();
    fn arbitrary_with(_: Self::Parameters) -> Self::Strategy {
        // Create a strategy for generating a vector of N usizes
        vec(any::<u32>(), N)
            // Map the generated vector to a Monomial
            .prop_map(|vec| {
                let mut array = [0; N];
                for (i, &item) in vec.iter().enumerate() {
                    array[i] = item;
                }
                Monomial { exponents: array }
            })
            .boxed()
    }

    type Strategy = BoxedStrategy<Self>;
}

#[cfg(test)]
mod tests {
    use proptest::{
        prelude::{any, TestCaseError},
        prop_assert, prop_assert_eq, proptest,
    };

    use crate::{
        fields::PrimeFieldElement64, poly::MonomialOrder, FiniteField, Monomial, One, Zero,
    };

    // What is Monomial::<0>? It should probably have degree 0 and always evaluate to 1.

    #[test]
    fn test_degree() {
        // 1
        assert_eq!(Monomial::<3>::new(&[0, 0, 0]).degree(), 0);

        // xy^4z^2
        assert_eq!(Monomial::<3>::new(&[1, 4, 2]).degree(), 7)
    }

    #[test]
    fn test_eval() {
        type F = PrimeFieldElement64<7>;
        let m = Monomial::<3>::new(&[1, 5, 3]);
        assert_eq!(m.eval(&[F::new(1), F::new(1), F::new(1)]), F::one());
        assert_eq!(m.eval(&[F::new(1), F::new(0), F::new(1)]), F::zero());
        assert_eq!(m.eval(&[F::new(1), F::new(2), F::new(1)]), F::new(2).pow(5));
        assert_eq!(
            m.eval(&[F::new(3), F::new(2), F::new(9)]),
            F::new(3) * F::new(2).pow(5) * F::new(9).pow(3)
        );
    }

    #[test]
    /// Serializing and deserializing should recover the original struct.
    fn test_ser_de() {
        let monomial = Monomial::<3>::new(&[1, 5, 3]);
        let bytes = bincode::serialize(&monomial).unwrap();
        let recovered: Monomial<3> = bincode::deserialize(&bytes).unwrap();
        assert_eq!(monomial, recovered);
    }

    /// Assert properties of the least common multiple.
    fn test_lcm_helper(a: &Monomial<7>, b: &Monomial<7>) -> Result<(), TestCaseError> {
        let lcm = Monomial::lcm;
        prop_assert_eq!(lcm(a, b), lcm(b, a)); // LCM is symmetric.
        prop_assert_eq!(lcm(a, a), *a);
        prop_assert_eq!(lcm(a, &Monomial::one()), *a);
        prop_assert!(lcm(a, b) >= *a);
        prop_assert!(lcm(a, b) >= *b);
        Ok(())
    }

    proptest! {
        #[test]
        #[ignore]
        fn test_lcm(a in any::<Monomial<7>>(), b in any::<Monomial<7>>()) {
            // TODO: without parameters, this may only generate monomials with degree 0.
            test_lcm_helper(&a, &b)?;
        }

        #[test]
        /// The (derived) ordering is Lexicographic.
        fn test_ordering_is_lexicographic(a in any::<Monomial<7>>(), b in any::<Monomial<7>>()) {
            let cmp = a.cmp(&b);
            let lex = MonomialOrder::Lexicographic.cmp(&a, &b);
            prop_assert_eq!(cmp, lex);
        }
    }
}
