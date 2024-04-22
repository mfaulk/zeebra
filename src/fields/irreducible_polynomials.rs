//! Irreducible polynomials
//!
//! A non-constant univariate is 'irreducible' over a field F if its coefficients belong to F
//! and it cannot be factored into the product of two non-constant polynomials with coefficients
//! in F.
//!
//! Irreducible polynomials are useful for constructing non-prime fields...
//!
//! When constructing a non-prime field GF(p^n), the choice of irreducible univariate is not unique.
//! However, the choice influences the cost of multiplication in the field, and so care is taken
//! to choose efficient (or "low weight") irreducible polynomials.

/// Irreducible Polynomials over GF(2)
/// Trinomials, Pentanomials, ...

// Bit pattern for x^5 + x^2 + 1, irreducible over GF(2)
#[allow(unused)]
pub const X5_X2_1: u64 = (1 << 5) + (1 << 2) + 1;

// Bit pattern for x^8 + x^4 + x^3 + x + 1, irreducible over GF(2)
#[allow(unused)]
pub const X8_X4_X3_X_1: u64 = (1 << 8) + (1 << 4) + (1 << 3) + (1 << 1) + 1;

// Bit pattern for x^63 + x + 1, irreducible over GF(2)
#[allow(unused)]
pub const X63_X_1: u64 = (1 << 63) + (1 << 1) + 1;
