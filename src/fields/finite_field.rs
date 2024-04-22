//! Trait defining a finite field.
//!
//! A finite field is a field of finite `order`, i.e., number of elements. The order of a finite
//! field is always a prime 'p' or a prime power 'p^n'.

use rand::{CryptoRng, RngCore};
use serde::{de::DeserializeOwned, Serialize};
use std::{
    fmt::Display,
    hash::Hash,
    ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};

use crate::Ring;

/// A Finite Field element.
pub trait FiniteField:
    Ring
    + Add<Output = Self>
    + AddAssign
    + Sub<Output = Self>
    + SubAssign
    + Div<Output = Self>
    + DivAssign
    + Mul<Output = Self>
    + MulAssign
    + Neg<Output = Self>
    + Sized
    + Clone
    + Display
    + Default
    + Hash
    + Serialize
    + DeserializeOwned
// + for<'de> Deserialize<'de>
where
    // owned + borrowed
    for<'a> Self: Add<&'a Self, Output = Self>,
    for<'a> Self: Sub<&'a Self, Output = Self>,
    for<'a> Self: Neg<Output = Self>,
    for<'a> Self: Mul<&'a Self, Output = Self>,
    for<'a> Self: Div<&'a Self, Output = Self>,
{
    fn new(val: u64) -> Self;

    /// Parse a string representation of a finite field element.
    fn from_str(_value: &str) -> Result<Self, ()>;

    /// A uniformly random field element.
    fn random<R: RngCore + CryptoRng>(rng: &mut R) -> Self;

    /// A primitive element of the finite field is a generator of the field's multiplicative group.
    fn primitive_element<R: RngCore + CryptoRng>(rng: &mut R) -> Self;

    /// A primitive, non-trivial nth root of unity, x^n = 1
    fn root_of_unity<R: RngCore + CryptoRng>(n: u64, rng: &mut R) -> Self;

    /// The number of elements q = p^k in the field, where p is a prime.
    fn order() -> u128;

    /// In a field of order q = p^k, the characteristic of the field is the prime p.
    fn characteristic() -> u128;

    /// a^b mod p
    fn pow(&self, b: u128) -> Self {
        if self.is_zero() {
            if b == 0 {
                // 0^0 = 1.
                return Self::one();
            }
            return Self::zero();
        }

        if b == 0 {
            return Self::one();
        }

        // Exponentiation by squaring.
        if b == 1 {
            *self
        } else if b % 2 == 0 {
            // b is even: a^b = a^(b/2) * a^(b/2)
            let y = self.pow(b / 2);
            y * y
        } else {
            // b is odd: a^b = a * a^(b-1)
            *self * self.pow(b - 1)
        }
    }

    /// The additive inverse of this element.
    fn neg(&self) -> Self {
        Self::zero() - self
    }

    /// The multiplicative inverse of this element. Panics if self is ZERO.
    fn inverse(&self) -> Self {
        assert_ne!(
            *self,
            Self::zero(),
            "The zero element does not have a multiplicative inverse."
        );
        let order = Self::order();
        self.pow(order - 2)
    }

    fn checked_div(&self, rhs: &Self) -> Option<Self> {
        if rhs.is_zero() {
            None
        } else {
            Some(*self / rhs)
        }
    }
}
