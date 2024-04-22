//! Additive and Multiplicative identities.

use core::ops::{Add, Mul};

/// The additive identity.
pub trait Zero: Add<Self, Output = Self> + PartialEq + Sized {
    /// Additive identity.
    const ZERO: Self;

    /// Returns the additive identity element "0".
    fn zero() -> Self {
        Self::ZERO
    }

    /// Returns `true` if `self` is equal to the additive identity.
    fn is_zero(&self) -> bool {
        *self == Self::ZERO
    }
}

/// The multiplicative identity.
pub trait One: Mul<Self, Output = Self> + PartialEq + Sized {
    /// Multiplicative identity.
    const ONE: Self;

    /// Returns the multiplicative identity element "1".
    fn one() -> Self {
        Self::ONE
    }

    /// Returns `true` if `self` is equal to the multiplicative identity.
    fn is_one(&self) -> bool {
        *self == Self::ONE
    }
}
