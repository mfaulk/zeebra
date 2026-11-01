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

// Irreducible polynomials over GF(2): trinomials, pentanomials, ...
//
// Certified by `binary_field::tests::test_declared_moduli_are_irreducible`, which runs Rabin's
// test; trial division is infeasible at degree 63.

// Bit pattern for x^5 + x^2 + 1, irreducible over GF(2)
#[allow(unused)]
pub const X5_X2_1: u64 = (1 << 5) + (1 << 2) + 1;

// Bit pattern for x^8 + x^4 + x^3 + x + 1, irreducible over GF(2)
#[allow(unused)]
pub const X8_X4_X3_X_1: u64 = (1 << 8) + (1 << 4) + (1 << 3) + (1 << 1) + 1;

// Bit pattern for x^63 + x + 1, irreducible over GF(2)
#[allow(unused)]
pub const X63_X_1: u64 = (1 << 63) + (1 << 1) + 1;

// Irreducible polynomials over GF(p) for p > 2, as moduli for `ExtensionFieldElement`.
//
// Each is monic of degree N with coefficients given low-order first, excluding the implicit
// leading 1. `tests::each_modulus_is_irreducible` certifies every one of them by trial division,
// so a wrong constant here fails the suite rather than silently producing a ring with zero
// divisors.
//
// Each is a zero-sized marker used only as a type argument, so none is ever constructed.

use super::extension_field::IrreduciblePolynomial;

/// x^2 + 1, irreducible over GF(3). Defines GF(9).
#[allow(dead_code)]
pub struct Modulus3Pow2;

impl IrreduciblePolynomial<3, 2> for Modulus3Pow2 {
    const COEFFICIENTS: [u64; 2] = [1, 0];
}

/// x^3 + x^2 + 1, irreducible over GF(5). Defines GF(125).
#[allow(dead_code)]
pub struct Modulus5Pow3;

impl IrreduciblePolynomial<5, 3> for Modulus5Pow3 {
    const COEFFICIENTS: [u64; 3] = [1, 0, 1];
}

/// x^4 + x^3 + 1, irreducible over GF(13). Defines GF(28561).
#[allow(dead_code)]
pub struct Modulus13Pow4;

impl IrreduciblePolynomial<13, 4> for Modulus13Pow4 {
    const COEFFICIENTS: [u64; 4] = [1, 0, 0, 1];
}

/// x^4 + 15x^3 + 1, irreducible over GF(251). Defines GF(3969126001).
#[allow(dead_code)]
pub struct Modulus251Pow4;

impl IrreduciblePolynomial<251, 4> for Modulus251Pow4 {
    const COEFFICIENTS: [u64; 4] = [1, 0, 0, 15];
}

/// x^8 + x^4 + x^3 + x + 1, irreducible over GF(2). Defines GF(256).
///
/// The same polynomial as [`X8_X4_X3_X_1`], in coefficient rather than bit-pattern form, which
/// lets `ExtensionFieldElement<2, 8, _>` be cross-checked against `BinaryFieldElement`.
#[allow(dead_code)]
pub struct Modulus2Pow8;

impl IrreduciblePolynomial<2, 8> for Modulus2Pow8 {
    const COEFFICIENTS: [u64; 8] = [1, 1, 0, 1, 1, 0, 0, 0];
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Trial division certifies that each declared modulus is irreducible over its base field.
    #[test]
    fn each_modulus_is_irreducible() {
        assert!(is_irreducible(3, &Modulus3Pow2::COEFFICIENTS));
        assert!(is_irreducible(5, &Modulus5Pow3::COEFFICIENTS));
        assert!(is_irreducible(13, &Modulus13Pow4::COEFFICIENTS));
        assert!(is_irreducible(251, &Modulus251Pow4::COEFFICIENTS));
        assert!(is_irreducible(2, &Modulus2Pow8::COEFFICIENTS));
    }

    /// A reducible polynomial is rejected, so the certification above is not vacuous.
    #[test]
    fn reducible_polynomials_are_rejected() {
        // x^2 + 4x + 3 = (x + 1)(x + 3) over GF(5).
        assert!(!is_irreducible(5, &[3, 4]));
        // x^2 + 1 = (x + 1)(x + 1) over GF(2).
        assert!(!is_irreducible(2, &[1, 0]));
    }

    /// True if the monic polynomial x^n + sum(tail[i] * x^i) has no factor of degree 1..=n/2.
    fn is_irreducible(p: u64, tail: &[u64]) -> bool {
        let n = tail.len();
        let mut modulus: Vec<u64> = tail.to_vec();
        modulus.push(1);
        // Enumerate every monic divisor of degree d by counting in base p.
        for d in 1..=n / 2 {
            for index in 0..p.pow(d as u32) {
                let mut divisor: Vec<u64> = (0..d).map(|i| index / p.pow(i as u32) % p).collect();
                divisor.push(1);
                if divides(p, &modulus, &divisor) {
                    return false;
                }
            }
        }
        true
    }

    /// True if `divisor` divides `dividend` over GF(p). Both are monic, low-order first.
    fn divides(p: u64, dividend: &[u64], divisor: &[u64]) -> bool {
        let mut remainder = dividend.to_vec();
        let degree = divisor.len() - 1;
        for i in (degree..remainder.len()).rev() {
            let factor = remainder[i];
            if factor == 0 {
                continue;
            }
            for j in 0..=degree {
                let term = factor * divisor[j] % p;
                remainder[i - degree + j] = (remainder[i - degree + j] + p - term) % p;
            }
        }
        remainder.iter().all(|c| *c == 0)
    }
}
