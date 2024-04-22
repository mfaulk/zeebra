//! An element of a Ring.
//!
//! A ring is a set R equipped with two binary operations (+ and *) satisfying the conditions:
//!
//! 1. (R, +) is an abelian (commutative) group,
//! 2. (R, *) is a semigroup (which means that the multiplication operation is associative),
//! 3. Multiplication is distributive with respect to addition.

use crate::identities::{One, Zero};
use proptest::arbitrary::Arbitrary;
use std::{
    fmt::{Debug, Display},
    ops::{Add, AddAssign, Mul, MulAssign},
};

/// An element of a Ring.
pub trait Ring:
    Copy
    + Zero
    + One
    + Eq
    + PartialEq
    + Display
    + Debug
    + Add
    + AddAssign
    + Mul
    + MulAssign
    + Arbitrary
    + Sized
    + Copy
    + Clone
{
}
