//! Fields GF(p^n) of power-prime dimension.
//!
//! For prime p, the field GF(q) with q = p^n is represented as polynomials over GF(p) whose
//! degree is strictly less than n. Addition and subtraction in GF(q) are the normal addition
//! and subtraction of polynomials over GF(p). Multiplication is constructed using an
//! irreducible polynomial P in GF(p)[X] of degree n: the product of two elements a, b, is the
//! remainder of Euclidean division by P of the product ab.

use std::{
    fmt::{Display, Formatter},
    ops,
};

use proptest::{prelude::Arbitrary, strategy::BoxedStrategy};
use rand::{CryptoRng, RngCore};
use serde::{
    ser::{Serialize, Serializer},
    Deserialize, Deserializer,
};

use crate::{impl_add_variants, impl_div_variants, impl_mul_variants, impl_sub_variants};

use crate::{
    identities::{One, Zero},
    FiniteField, Ring,
};

/// Element of the field GF(p^n).
#[derive(Copy, Clone, Hash, Debug, Eq, PartialEq)]
pub struct ExtensionFieldElement<const P: u64, const N: usize> {
    /// The coefficients of a polynomial in GF(p)[X] of degree less than N.
    pub coefficients: [u64; N],
}

impl<const P: u64, const N: usize> ExtensionFieldElement<P, N> {
    /// An element of GF(p^n).
    ///
    /// # Arguments
    /// * `coefficients` - coefficients[i] is c_i in the polynomial \sum_{i=1}^m c_i * x_i.
    pub fn new(coefficients: [u64; N]) -> Self {
        // TODO: each coefficient must be in [0,p-1]
        Self { coefficients }
    }
}

// impl Default
impl<const P: u64, const N: usize> Default for ExtensionFieldElement<P, N> {
    fn default() -> Self {
        Self {
            coefficients: [0u64; N],
        }
    }
}

// impl Serialize
impl<const P: u64, const N: usize> Serialize for ExtensionFieldElement<P, N> {
    fn serialize<S>(&self, _serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        todo!()
    }
}

// impl Deserialize
impl<'de, const P: u64, const N: usize> Deserialize<'de> for ExtensionFieldElement<P, N> {
    fn deserialize<D>(_deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        todo!()
    }
}

// impl Zero
impl<const P: u64, const N: usize> Zero for ExtensionFieldElement<P, N> {
    const ZERO: Self = ExtensionFieldElement {
        coefficients: [0u64; N],
    };
}

// impl One
impl<const P: u64, const N: usize> One for ExtensionFieldElement<P, N> {
    // TODO: this is wrong.
    const ONE: Self = ExtensionFieldElement {
        coefficients: [1u64; N],
    };
}

// impl Ring
impl<const P: u64, const N: usize> Ring for ExtensionFieldElement<P, N> {}

// impl FiniteField
impl<const P: u64, const N: usize> FiniteField for ExtensionFieldElement<P, N> {
    fn new(_val: u64) -> Self {
        todo!()
    }

    fn from_str(_value: &str) -> Result<Self, ()> {
        todo!()
    }

    fn random<R: RngCore + CryptoRng>(rng: &mut R) -> Self {
        let mut coefficients = [0u64; N];
        for c in coefficients.iter_mut() {
            *c = rng.next_u64() % P;
        }
        Self::new(coefficients)
    }

    fn primitive_element<R: RngCore + CryptoRng>(_rng: &mut R) -> Self {
        todo!()
    }

    fn root_of_unity<R: RngCore + CryptoRng>(_n: u64, _rng: &mut R) -> Self {
        todo!()
    }

    fn order() -> u128 {
        // TODO: p^n can be larger than u64
        (P as u128).pow(N as u32)
    }

    fn characteristic() -> u128 {
        P as u128
    }
}

// impl Display
impl<const P: u64, const N: usize> Display for ExtensionFieldElement<P, N> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        // TODO: ???
        write!(f, "{:?}", self.coefficients)
    }
}

// Borrowed + Borrowed
impl<const P: u64, const N: usize> ops::Add<&ExtensionFieldElement<P, N>>
    for &ExtensionFieldElement<P, N>
{
    type Output = ExtensionFieldElement<P, N>;

    fn add(self, rhs: &ExtensionFieldElement<P, N>) -> ExtensionFieldElement<P, N> {
        let mut coefficients = [0u64; N];
        for i in 0..N {
            let a = self.coefficients[i];
            let b = rhs.coefficients[i];
            let sum = a as u128 + b as u128;
            coefficients[i] = (sum % P as u128) as u64;
        }
        ExtensionFieldElement::new(coefficients)
    }
}

impl_add_variants!([const P:u64, const N: usize], ExtensionFieldElement<P, N>);

// Borrowed - Borrowed
impl<const P: u64, const N: usize> ops::Sub<&ExtensionFieldElement<P, N>>
    for &ExtensionFieldElement<P, N>
{
    type Output = ExtensionFieldElement<P, N>;

    fn sub(self, rhs: &ExtensionFieldElement<P, N>) -> Self::Output {
        let mut coefficients = [0u64; N];
        for i in 0..N {
            let a = self.coefficients[i];
            let b = rhs.coefficients[i];
            let difference = a as i128 - b as i128;
            coefficients[i] = difference.wrapping_rem_euclid(P as i128) as u64;
        }
        ExtensionFieldElement::new(coefficients)
    }
}

impl_sub_variants!([const P:u64, const N: usize], ExtensionFieldElement<P, N>);

impl<const P: u64, const N: usize> ops::Neg for ExtensionFieldElement<P, N> {
    type Output = ExtensionFieldElement<P, N>;

    fn neg(self) -> Self::Output {
        ExtensionFieldElement::zero() - self
    }
}

impl<const P: u64, const N: usize> ops::Neg for &ExtensionFieldElement<P, N> {
    type Output = ExtensionFieldElement<P, N>;

    fn neg(self) -> Self::Output {
        ExtensionFieldElement::zero() - self
    }
}

// Borrowed * Borrowed
impl<const P: u64, const N: usize> ops::Mul<Self> for &ExtensionFieldElement<P, N> {
    type Output = ExtensionFieldElement<P, N>;

    fn mul(self, rhs: Self) -> Self::Output {
        let mut coefficients = [0u64; N];
        for i in 0..N {
            let a = self.coefficients[i];
            let b = rhs.coefficients[i];
            let prod = a as u128 * b as u128;
            coefficients[i] = (prod % P as u128) as u64;
        }
        ExtensionFieldElement::new(coefficients)
    }
}

impl_mul_variants!([const P:u64, const N: usize], ExtensionFieldElement<P, N>);

// Borrowed / Borrowed
impl<const P: u64, const N: usize> ops::Div<Self> for &ExtensionFieldElement<P, N> {
    type Output = ExtensionFieldElement<P, N>;

    fn div(self, rhs: Self) -> Self::Output {
        // Division is multiplication by the inverse.
        self * &rhs.inverse()
    }
}

impl_div_variants!([const P:u64, const N: usize], ExtensionFieldElement<P, N>);

// impl Arbitrary
impl<const P: u64, const N: usize> Arbitrary for ExtensionFieldElement<P, N> {
    type Parameters = ();

    fn arbitrary_with(_args: Self::Parameters) -> Self::Strategy {
        todo!()
    }

    type Strategy = BoxedStrategy<Self>;
}

#[cfg(test)]
mod tests {
    use rand::thread_rng;

    use crate::{
        fields::extension_field::ExtensionFieldElement,
        identities::{One, Zero},
        FiniteField,
    };

    #[test]
    // random should not panic.
    fn test_random() {
        let mut rng = thread_rng();
        for _i in 0..1000 {
            let _element = ExtensionFieldElement::<61, 8>::random(&mut rng);
        }
    }

    #[test]
    // ZERO is the additive identity.
    fn test_add_zero() {
        type F = ExtensionFieldElement<61, 8>;
        let mut rng = thread_rng();
        let element = F::random(&mut rng);
        let sum = element + F::zero();
        assert_eq!(element, sum);
    }

    #[test]
    fn test_add() {
        const P: u64 = 13;
        const N: usize = 4;
        type Field = ExtensionFieldElement<P, N>;
        let a = Field::new([1, 2, 3, 4]);
        let b = Field::new([11, 11, 11, 11]);
        let sum = a + b;
        assert_eq!(sum, Field::new([12, 0, 1, 2]));
    }

    #[test]
    fn test_sub() {
        const P: u64 = 13;
        const N: usize = 4;
        type F = ExtensionFieldElement<P, N>;
        let a = F::new([1, 2, 3, 4]);
        let b = F::new([11, 11, 11, 11]);
        let diff = a - b;
        assert_eq!(diff, F::new([3, 4, 5, 6]));
    }

    #[test]
    // ONE is the multiplicative identity.
    fn test_mul_one() {
        type F = ExtensionFieldElement<61, 8>;
        let mut rng = thread_rng();
        let element = F::random(&mut rng);
        let prod = element * F::one();
        assert_eq!(element, prod);
    }

    #[test]
    fn test_mul() {
        type F = ExtensionFieldElement<13, 4>;
        let a = F::new([1, 2, 3, 4]);
        let b = F::new([11, 11, 11, 11]);
        let prod = a * b;
        assert_eq!(prod, F::new([11, 9, 7, 5]));
    }

    #[test]
    // a * a_inv = 1
    fn test_inverse() {
        type F = ExtensionFieldElement<13, 4>;
        let a = F::new([1, 2, 3, 4]);
        assert_eq!(a * a.inverse(), F::one());
    }

    #[test]
    #[should_panic]
    // Zero does not have a multiplicative inverse.
    fn test_inverse_of_zero() {
        type F = ExtensionFieldElement<61, 8>;
        let mut rng = thread_rng();
        let element = F::random(&mut rng);
        let _result = element / F::zero();
    }

    #[test]
    fn test_divide_by_one() {
        type F = ExtensionFieldElement<61, 8>;
        let mut rng = thread_rng();
        let element = F::random(&mut rng);
        let result = element / F::one();
        assert_eq!(element, result);
    }

    #[test]
    fn test_divide() {
        type F = ExtensionFieldElement<13, 4>;
        let a = F::new([1, 2, 3, 4]);
        let b = F::new([11, 11, 11, 11]);
        let result = a / b;
        assert_eq!(result, F::new([6, 12, 5, 11]));
    }
}
