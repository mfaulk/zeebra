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

use crate::{
    integers::{big_uint::BigUInt, factor, FromDecStrErr},
    Ring,
};

/// The value of a `BigUInt` that is known to fit in a `u128`.
///
/// Used for the prime factors of q - 1, which cannot exceed q - 1 itself.
fn big_uint_to_u128(value: &BigUInt) -> u128 {
    let words = value.as_le_words();
    assert!(words.len() <= 2, "{:?} does not fit in a u128", value);
    let low = *words.first().unwrap_or(&0) as u128;
    let high = *words.get(1).unwrap_or(&0) as u128;
    low | (high << 64)
}

/// Why a string could not be parsed as a finite field element.
///
/// Carries which character was rejected, so a caller can report the position of the problem
/// rather than only that parsing failed.
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum ParseFieldElementError {
    /// A character was not a decimal digit. Holds the offending byte, offset from `b'0'`.
    InvalidCharacter(u8),

    /// The value did not fit the field's representation.
    OutOfRange,
}

impl Display for ParseFieldElementError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidCharacter(_) => write!(f, "a character is not in the range 0-9"),
            Self::OutOfRange => write!(f, "the value is too large for the field"),
        }
    }
}

impl std::error::Error for ParseFieldElementError {}

impl From<FromDecStrErr> for ParseFieldElementError {
    fn from(err: FromDecStrErr) -> Self {
        match err {
            FromDecStrErr::InvalidCharacter(c) => Self::InvalidCharacter(c),
            FromDecStrErr::InvalidLength => Self::OutOfRange,
        }
    }
}

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
    fn from_str(_value: &str) -> Result<Self, ParseFieldElementError>;

    /// A uniformly random field element.
    fn random<R: RngCore + CryptoRng>(rng: &mut R) -> Self;

    /// A primitive element of the finite field is a generator of the field's multiplicative group.
    ///
    /// Found by random search. The multiplicative group of a finite field is cyclic of order
    /// q - 1, and an element generates it unless its order is a proper divisor of q - 1. Every
    /// proper divisor divides (q - 1) / r for some prime r | q - 1, so those quotients are the
    /// only exponents worth testing. See Handbook of Applied Cryptography, Algorithm 4.80.
    ///
    /// This default works for any finite field, since it uses nothing but the field's own
    /// arithmetic. A type with a cheaper construction may override it — the prime fields do,
    /// via `find_generator`, which exploits their elements being integers mod p.
    fn primitive_element<R: RngCore + CryptoRng>(rng: &mut R) -> Self {
        let group_order = Self::order() - 1;
        let (prime_factors, _powers) = factor(&BigUInt::new_from_u128(group_order), rng);
        let quotients: Vec<u128> = prime_factors
            .iter()
            .map(|r| group_order / big_uint_to_u128(r))
            .collect();

        loop {
            let candidate = Self::random(rng);
            if candidate.is_zero() {
                continue;
            }
            if quotients
                .iter()
                .all(|&exponent| candidate.pow(exponent) != Self::one())
            {
                return candidate;
            }
        }
    }

    /// A primitive, non-trivial nth root of unity, x^n = 1
    ///
    /// # Panics
    /// Panics unless `n` divides the order of the multiplicative group.
    fn root_of_unity<R: RngCore + CryptoRng>(n: u64, rng: &mut R) -> Self {
        let group_order = Self::order() - 1;
        assert_eq!(group_order % n as u128, 0, "n must divide the group order.");

        // If g has order q - 1, then g^((q-1)/n) has order exactly n.
        let g = Self::primitive_element(rng);
        g.pow(group_order / n as u128)
    }

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
        } else if b.is_multiple_of(2) {
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
