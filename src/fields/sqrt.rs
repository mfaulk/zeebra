//! Square roots in a finite field, and the quadratic character that decides which elements have
//! one.
//!
//! One implementation covers every field in the crate, because what changes between them is the
//! two-adicity of `q - 1` rather than the algorithm: `s = 1` degenerates to a single
//! exponentiation, larger s runs the Tonelli-Shanks loop s - 1 times at worst, and
//! characteristic two is a different computation entirely since squaring there is a bijection.

use rand::{CryptoRng, RngCore};

use crate::{
    fields::two_adic::{
        halved_group_order, increment, repeated_squaring, shift_right, two_adic_decomposition,
    },
    KnownOrder,
};

/// The quadratic character of `a`: 0 if `a` is zero, 1 if it is a nonzero square, -1 if it is not.
///
/// By Euler's criterion, `a^((q-1)/2)` is 1 on the squares and -1 on the rest. Over a prime field
/// this is the Legendre symbol `(a/p)`; over an extension field of odd characteristic it is the
/// same character on the larger group, which is what the square root needs. In characteristic two
/// squaring is a bijection, so every element is a square and the symbol is 1 off zero.
///
/// The integer counterpart is [`jacobi_symbol`](crate::integers::jacobi_symbol), which needs no
/// exponentiation but also no field.
pub fn legendre_symbol<F: KnownOrder>(a: &F) -> i8 {
    if a.is_zero() {
        return 0;
    }
    if F::characteristic_limbs() == [2] {
        return 1;
    }

    if a.pow_limbs(&halved_group_order(F::order_limbs())).is_one() {
        1
    } else {
        -1
    }
}

/// A square root of `a`, or `None` if it has none.
///
/// Tonelli-Shanks. With `q - 1 = 2^s * m` for odd m, `a^((m+1)/2)` is a square root up to a factor
/// in the 2-Sylow subgroup, and the loop corrects that factor one bit at a time. Of the two roots
/// `+-r` it is unspecified which is returned.
///
/// The rng draws only to find a quadratic non-residue, and only when the correction loop runs at
/// all: over a field with `q = 3 (mod 4)` — where `s = 1` and the root is just `a^((q+1)/4)` — and
/// over a field of characteristic two, no random element is consumed.
pub(crate) fn sqrt<F: KnownOrder, R: RngCore + CryptoRng>(a: &F, rng: &mut R) -> Option<F> {
    if a.is_zero() {
        return Some(F::zero());
    }

    if F::characteristic_limbs() == [2] {
        // Squaring is the Frobenius automorphism of GF(2^k), whose inverse is `x -> x^(q/2)`:
        // `(x^(2^(k-1)))^2 = x^(2^k) = x`. Every element has exactly one square root.
        return Some(a.pow_limbs(&shift_right(F::order_limbs(), 1)));
    }

    let (s, m) = two_adic_decomposition(F::order_limbs());

    // `a^m` lies in the 2-Sylow subgroup, and is 1 exactly when a is a square: its order divides
    // `2^(s-1)` iff `a^((q-1)/2) = 1`. So this is Euler's criterion and the loop's state at once.
    let mut t = a.pow_limbs(&m);
    let mut root = a.pow_limbs(&shift_right(&increment(&m), 1));
    if t.is_one() {
        return Some(root);
    }
    if repeated_squaring(t, s - 1) != F::one() {
        // `t` has order 2^s rather than a proper divisor, so a is a non-residue.
        return None;
    }

    // `c` generates the 2-Sylow subgroup, which is where the correction factors come from.
    let z = loop {
        let candidate = F::random(rng);
        if legendre_symbol(&candidate) == -1 {
            break candidate;
        }
    };
    let mut c = z.pow_limbs(&m);
    let mut exponent = s;

    while !t.is_one() {
        // The least i with `t^(2^i) = 1`. It is below `exponent`, since t's order divides
        // `2^(exponent - 1)` at the top of every iteration.
        let mut i = 0;
        let mut squared = t;
        while !squared.is_one() {
            squared = squared * squared;
            i += 1;
        }

        // `b` has order `2^(i)`, so multiplying halves the order of t and leaves root^2 = a * t.
        let b = repeated_squaring(c, exponent - i - 1);
        root *= b;
        c = b * b;
        t *= c;
        exponent = i;
    }

    Some(root)
}

#[cfg(test)]
mod tests {
    use rand::{prelude::StdRng, SeedableRng};

    use crate::{
        fields::{
            binary_field::BinaryFieldElement,
            extension_field::ExtensionFieldElement,
            irreducible_polynomials::{Modulus13Pow4, X8_X4_X3_X_1},
            legendre_symbol, Bn254Fr, Zp13, Zp2147483647, Zp65537,
        },
        integers::{big_uint::BigUInt, jacobi_symbol},
        FiniteField, KnownOrder, One, Zero,
    };

    /// GF(2^8), where squaring is a bijection.
    type Gf256 = BinaryFieldElement<X8_X4_X3_X_1>;

    /// GF(13^4), an odd-characteristic extension field.
    type F13x4 = ExtensionFieldElement<13, 4, Modulus13Pow4>;

    /// The character is 1 on squares, -1 on non-squares and 0 on zero.
    #[test]
    fn test_the_character_separates_the_squares_mod_13() {
        let residues = [1u64, 3, 4, 9, 10, 12];
        assert_eq!(legendre_symbol(&Zp13::zero()), 0);
        for a in 1..13u64 {
            let expected = if residues.contains(&a) { 1 } else { -1 };
            assert_eq!(legendre_symbol(&Zp13::new(a)), expected, "({a}/13)");
        }
    }

    /// Over a prime field the character agrees with the Jacobi symbol of the same residue.
    ///
    /// Two independent computations: Euler's criterion is an exponentiation in the field, the
    /// Jacobi symbol is a gcd-style recursion on integers that never touches the field.
    #[test]
    fn test_the_character_agrees_with_the_jacobi_symbol() {
        let modulus = BigUInt::new_from_u64(65537);
        for a in 0..400u64 {
            let x = Zp65537::new(a);
            assert_eq!(
                legendre_symbol(&x),
                jacobi_symbol(&BigUInt::new_from_u64(a), &modulus),
                "a = {a}"
            );
        }
    }

    /// Every nonzero element of a field of characteristic two is a square.
    #[test]
    fn test_every_element_of_a_binary_field_is_a_square() {
        let mut rng = StdRng::seed_from_u64(2);
        assert_eq!(legendre_symbol(&Gf256::zero()), 0);
        for _ in 0..50 {
            let x = Gf256::random(&mut rng);
            if !x.is_zero() {
                assert_eq!(legendre_symbol(&x), 1);
            }
        }
    }

    /// Half of the nonzero elements are squares, over a field small enough to count them.
    #[test]
    fn test_exactly_half_the_nonzero_elements_are_squares() {
        let squares = (1..13u64)
            .filter(|&a| legendre_symbol(&Zp13::new(a)) == 1)
            .count();
        assert_eq!(squares, 6);
    }

    /// A square root squares back to the element it was taken of.
    ///
    /// Run over every field family: `s = 2` for 13, `s = 1` for the Mersenne prime (where
    /// Tonelli-Shanks degenerates to a single exponentiation), `s = 16` for 65537, `s = 28` over a
    /// 254-bit field, characteristic two for GF(256), and an odd-characteristic extension.
    fn roots_square_back<F: KnownOrder>(seed: u64, trials: usize) {
        let mut rng = StdRng::seed_from_u64(seed);
        for _ in 0..trials {
            let x = F::random(&mut rng);
            let square = x * x;
            let root = square.sqrt(&mut rng).expect("a square has a square root");
            assert_eq!(root * root, square, "sqrt({square})^2 != {square}");
            assert!(root == x || root == -x, "the root is neither x nor -x");
        }
    }

    #[test]
    fn test_roots_square_back() {
        roots_square_back::<Zp13>(3, 40);
        roots_square_back::<Zp2147483647>(5, 40);
        roots_square_back::<Zp65537>(7, 40);
        roots_square_back::<Bn254Fr>(11, 10);
        roots_square_back::<Gf256>(13, 40);
        roots_square_back::<F13x4>(17, 40);
    }

    /// A non-square has no square root, and that is `None` rather than a wrong answer.
    fn non_squares_have_no_root<F: KnownOrder>(seed: u64, trials: usize) {
        let mut rng = StdRng::seed_from_u64(seed);
        let mut seen_a_non_square = false;
        for _ in 0..trials {
            let x = F::random(&mut rng);
            match legendre_symbol(&x) {
                -1 => {
                    seen_a_non_square = true;
                    assert!(x.sqrt(&mut rng).is_none(), "{x} is not a square");
                }
                _ => {
                    let root = x.sqrt(&mut rng).expect("a square has a square root");
                    assert_eq!(root * root, x);
                }
            }
        }
        assert!(seen_a_non_square, "the trials drew no non-square");
    }

    #[test]
    fn test_non_squares_have_no_root() {
        non_squares_have_no_root::<Zp13>(19, 40);
        non_squares_have_no_root::<Zp2147483647>(23, 40);
        non_squares_have_no_root::<Zp65537>(29, 40);
        non_squares_have_no_root::<Bn254Fr>(31, 10);
        non_squares_have_no_root::<F13x4>(37, 40);
    }

    /// Zero's root is zero and one's root is +-1, in every characteristic.
    #[test]
    fn test_the_roots_of_zero_and_one() {
        let mut rng = StdRng::seed_from_u64(41);
        assert_eq!(Zp13::zero().sqrt(&mut rng), Some(Zp13::zero()));
        assert_eq!(Zp65537::zero().sqrt(&mut rng), Some(Zp65537::zero()));
        assert_eq!(Gf256::zero().sqrt(&mut rng), Some(Gf256::zero()));
        assert_eq!(Gf256::one().sqrt(&mut rng), Some(Gf256::one()));
        let root = Zp65537::one().sqrt(&mut rng).expect("1 is a square");
        assert!(root.is_one() || root == -Zp65537::one());
    }

    /// Every element of a small field is covered, not only the sampled ones.
    #[test]
    fn test_every_element_of_a_small_field() {
        let mut rng = StdRng::seed_from_u64(43);
        for a in 0..13u64 {
            let x = Zp13::new(a);
            match x.sqrt(&mut rng) {
                Some(root) => assert_eq!(root * root, x, "sqrt({a})"),
                None => assert_eq!(legendre_symbol(&x), -1, "{a} has no root but is a square"),
            }
        }
    }

    /// -1 has a square root exactly when the field's two-adicity exceeds one.
    ///
    /// `-1` is a square iff `q = 1 mod 4`, which for `q - 1 = 2^s * m` is `s >= 2`.
    #[test]
    fn test_minus_one_has_a_root_exactly_when_the_two_adicity_allows_it() {
        let mut rng = StdRng::seed_from_u64(47);
        // 13 - 1 = 2^2 * 3, so s = 2 and -1 is a square.
        assert_eq!(Zp13::two_adicity(), 2);
        assert!((-Zp13::one()).sqrt(&mut rng).is_some());
        // 2^31 - 2 = 2 * (2^30 - 1), so s = 1 and -1 is not.
        assert_eq!(Zp2147483647::two_adicity(), 1);
        assert!((-Zp2147483647::one()).sqrt(&mut rng).is_none());
    }
}
