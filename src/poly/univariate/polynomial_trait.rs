//! A Univariate Polynomial

use crate::FiniteField;
use rand::{CryptoRng, RngCore};
use serde::{de::DeserializeOwned, Serialize};
use std::{
    fmt::{Debug, Display},
    ops::{Add, AddAssign, Mul, Neg, Sub},
};

pub trait Polynomial<F: FiniteField>:
    Sized
    + Clone
    + Debug
    + Display
    + Eq
    + PartialEq
    + Serialize
    + DeserializeOwned
    + Add<Output = Self>
    + Sub<Output = Self>
    + Mul<Output = Self>
    + AddAssign
    + Neg
where
    for<'a> Self: AddAssign<&'a Self>,
{
    /// Lift the field element to the constant polynomial p(x) = c.
    fn lift(c: &F) -> Self;

    /// The polynomial's coefficients[i] = a_i
    fn coefficients(&self) -> &[F];

    /// Returns the total degree of the polynomial
    fn degree(&self) -> u32;

    /// Evaluates `self` at the given point 'x'.
    fn eval(&self, x: &F) -> F;

    /// Return the zero polynomial.
    fn zero() -> Self;

    /// True if this polynomial is 0 (or the empty polynomial).
    fn is_zero(&self) -> bool;

    /// The constant polynomial f(x) = 1.
    fn one() -> Self;

    /// True if this polynomial is 1.
    fn is_one(&self) -> bool;

    /// A random polynomial of degree `d`.
    fn rand<R: RngCore + CryptoRng>(d: u64, rng: &mut R) -> Self;

    /// p(x) -> c*p(x)
    fn scale(&self, c: &F) -> Self;

    /// p(x) --> p(x + k)
    fn shift(&self, k: &F) -> Self;

    /// This polynomial, raised to the given power.
    fn pow(&self, n: u32) -> Self;

    /// Symbolic composition of self with p: self(p(x)).
    fn compose(&self, p: &Self) -> Self;

    /// Division with remainder. Returns (quotient, remainder).
    /// TODO: return a result instead of panicking if divisor is zero.
    fn div(&self, divisor: &Self) -> (Self, Self);
}
