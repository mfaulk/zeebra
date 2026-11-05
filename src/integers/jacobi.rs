//! The Jacobi symbol, by the binary algorithm.

use crate::integers::big_uint::BigUInt;

/// The Jacobi symbol `(a/n)`, for odd `n`.
///
/// The product of the Legendre symbols of `a` over the prime factorization of `n`, computed
/// without that factorization: quadratic reciprocity lets the pair be reduced in the manner of a
/// binary gcd, two bits at a time. The result is 0 when `a` and `n` share a factor, and otherwise
/// +-1.
///
/// For prime `n` this is the Legendre symbol, and so a residue test. For composite `n` it is not —
/// `(2/15) = 1` though 2 is not a square mod 15 — which is what makes it a *compositeness*
/// witness rather than a residue test. The field-level residue test is
/// [`legendre_symbol`](crate::fields::legendre_symbol), by Euler's criterion.
///
/// # Panics
/// Panics unless `n` is odd and nonzero, outside which the symbol is not defined.
pub fn jacobi_symbol(a: &BigUInt, n: &BigUInt) -> i8 {
    assert!(
        !n.is_zero() && is_odd(n),
        "the Jacobi symbol (a/n) is defined for odd nonzero n, not {n}"
    );

    let mut a = a % n;
    let mut n = n.clone();
    let mut sign: i8 = 1;

    while !a.is_zero() {
        // (2/n) is 1 for n = +-1 mod 8 and -1 for n = +-3 mod 8, so each factor of two flips the
        // sign exactly when n is 3 or 5 mod 8.
        while !is_odd(&a) {
            a = &a >> 1;
            if matches!(low_bits(&n, 7), 3 | 5) {
                sign = -sign;
            }
        }

        // Reciprocity: (a/n)(n/a) = -1 exactly when both are 3 mod 4.
        std::mem::swap(&mut a, &mut n);
        if low_bits(&a, 3) == 3 && low_bits(&n, 3) == 3 {
            sign = -sign;
        }

        a = &a % &n;
    }

    // The recursion ends at gcd(a, n), which is n: coprime leaves 1, a common factor leaves more.
    if n.is_one() {
        sign
    } else {
        0
    }
}

/// The low bits of `value` under `mask`, which must be one less than a power of two.
fn low_bits(value: &BigUInt, mask: u64) -> u64 {
    value.as_le_words().first().unwrap_or(&0) & mask
}

/// True if `value` is odd.
fn is_odd(value: &BigUInt) -> bool {
    low_bits(value, 1) == 1
}

#[cfg(test)]
mod tests {
    use crate::integers::{big_uint::BigUInt, jacobi_symbol};

    fn jacobi(a: u64, n: u64) -> i8 {
        jacobi_symbol(&BigUInt::new_from_u64(a), &BigUInt::new_from_u64(n))
    }

    /// The symbol modulo a prime, against the quadratic residues mod 13 worked out by hand.
    #[test]
    fn test_the_symbol_modulo_a_prime_identifies_the_residues() {
        // The squares mod 13 are 1, 4, 9, 3, 12, 10.
        let residues = [1, 3, 4, 9, 10, 12];
        for a in 1..13u64 {
            let expected = if residues.contains(&a) { 1 } else { -1 };
            assert_eq!(jacobi(a, 13), expected, "({a}/13)");
        }
    }

    /// Modulo a composite the symbol is the product over the prime factorization.
    ///
    /// `(a/15) = (a/3)(a/5)`, so it can be 1 for a non-residue — which is exactly why the Jacobi
    /// symbol is not a residue test for composite moduli.
    #[test]
    fn test_the_symbol_modulo_a_composite_is_multiplicative() {
        // (2/15) = (2/3)(2/5) = (-1)(-1) = 1, though 2 is not a square mod 15.
        assert_eq!(jacobi(2, 15), 1);
        // (7/15) = (7/3)(7/5) = (1/3)(2/5) = (1)(-1) = -1.
        assert_eq!(jacobi(7, 15), -1);
        assert_eq!(jacobi(4, 15), 1);
    }

    /// A value sharing a factor with the modulus has symbol zero.
    #[test]
    fn test_a_common_factor_gives_zero() {
        assert_eq!(jacobi(0, 13), 0);
        assert_eq!(jacobi(13, 13), 0);
        assert_eq!(jacobi(3, 15), 0);
        assert_eq!(jacobi(5, 15), 0);
        assert_eq!(jacobi(10, 15), 0);
    }

    /// Modulo one every value has symbol 1, the empty product.
    #[test]
    fn test_the_symbol_modulo_one_is_one() {
        for a in 0..5u64 {
            assert_eq!(jacobi(a, 1), 1);
        }
    }

    /// The symbol depends only on `a` modulo `n`.
    #[test]
    fn test_the_symbol_is_periodic_in_its_numerator() {
        for a in 0..13u64 {
            assert_eq!(jacobi(a, 13), jacobi(a + 13, 13));
            assert_eq!(jacobi(a, 13), jacobi(a + 26, 13));
        }
    }

    /// The symbol is multiplicative in its numerator: `(ab/n) = (a/n)(b/n)`.
    #[test]
    fn test_the_symbol_is_multiplicative_in_its_numerator() {
        for a in 1..21u64 {
            for b in 1..21u64 {
                assert_eq!(jacobi(a * b, 21), jacobi(a, 21) * jacobi(b, 21), "{a}*{b}");
            }
        }
    }

    /// A modulus wider than a word, where the recursion runs through several limbs.
    ///
    /// `(2/n) = 1` exactly when `n = +-1 mod 8`, and `2^64 - 59` is 5 mod 8, so the symbol is -1.
    #[test]
    fn test_a_modulus_wider_than_a_word() {
        let p = BigUInt::new_from_u128((1u128 << 64) - 59);
        assert_eq!(p.as_le_words()[0] % 8, 5);
        assert_eq!(jacobi_symbol(&BigUInt::new_from_u64(2), &p), -1);
        // 4 is a square, so its symbol is 1 whatever the modulus it is coprime to.
        assert_eq!(jacobi_symbol(&BigUInt::new_from_u64(4), &p), 1);
    }

    /// An even modulus is outside the symbol's definition.
    #[test]
    #[should_panic(expected = "odd")]
    fn test_an_even_modulus_is_rejected() {
        let _ = jacobi(3, 14);
    }
}
