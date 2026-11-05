//! Traits defining a finite field.
//!
//! A finite field is a field of finite order, i.e., number of elements. The order of a finite
//! field is always a prime `p` or a prime power `p^k`.
//!
//! The order lives in [`KnownOrder`] rather than in [`FiniteField`], because a 254-bit prime
//! field has no order that fits in a machine integer and nothing in the algebraic core — the
//! polynomials, the linear algebra, F4, FGLM, Buchberger — ever asks for one. Only root finding,
//! factorization and enumerating the field itself do. Requiring the order of every coefficient
//! type would exclude the wide fields from algorithms that never use it.

use rand::{CryptoRng, RngCore};
use serde::{de::DeserializeOwned, Serialize};
use std::{
    fmt::Display,
    hash::Hash,
    ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};

use crate::{
    fields::two_adic,
    integers::{big_uint::BigUInt, bit, factor, highest_set_bit, num_digits, FromDecStrErr},
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

    /// `self^exponent`, with the exponent as little-endian 64-bit limbs.
    ///
    /// [`Self::pow`] takes a `u128`, which cannot express the exponents a wide field needs:
    /// `(q - 1) / 2^s` for a 254-bit q is itself 226 bits. The cost is one squaring per bit of
    /// the exponent either way, and trailing zero limbs cost nothing, so a caller may pass a
    /// fixed-width value without trimming it.
    ///
    /// `0^0 = 1`, as in [`Self::pow`].
    fn pow_limbs(&self, exponent: &[u64]) -> Self {
        let Some(highest) = highest_set_bit(exponent) else {
            // A zero exponent, including for a zero base.
            return Self::one();
        };

        let mut result = Self::one();
        let mut square = *self;
        for index in 0..=highest {
            if bit(exponent, index) {
                result *= square;
            }
            // The last squaring would be discarded, and for a wide exponent it is not cheap.
            if index < highest {
                square = square * square;
            }
        }
        result
    }

    /// The additive inverse of this element.
    fn neg(&self) -> Self {
        Self::zero() - self
    }

    /// The multiplicative inverse of this element.
    ///
    /// Required rather than provided: the obvious default is `a^(q-2)`, which needs the field's
    /// order as a machine integer and so cannot exist for a field whose order does not fit in
    /// one. Implementations over a cardinality that does fit may write exactly that; the rest
    /// delegate to their own inversion.
    ///
    /// # Panics
    /// Panics if `self` is zero. Use [`Self::checked_div`] where zero is possible — pivot
    /// normalization inverts only pivots, which are nonzero by construction, so no `Option`
    /// enters the inner loops.
    fn inverse(&self) -> Self;

    fn checked_div(&self, rhs: &Self) -> Option<Self> {
        if rhs.is_zero() {
            None
        } else {
            Some(*self / rhs)
        }
    }
}

/// `limbs` without its trailing zero words, so that the result is canonical.
///
/// Takes and returns `&'static` because an implementation of [`KnownOrder`] produces its limbs
/// from an associated const, which promotes.
pub fn trim_limbs(limbs: &'static [u64]) -> &'static [u64] {
    &limbs[..num_digits(limbs)]
}

/// A finite field whose order is known.
///
/// Separate from [`FiniteField`] so that a field whose order exceeds any machine integer can
/// still be a polynomial coefficient. The order is little-endian 64-bit limbs rather than an
/// integer type, which covers 64-, 128- and 256-bit orders without choosing a width or
/// allocating; [`Self::order_u128`] is there for the callers that genuinely need a machine
/// integer and are entitled to fail without one.
///
/// Implemented by every field in this crate, including the wide prime fields. What a wide field
/// cannot do is *enumerate* itself, which is a property of its size rather than of this trait.
pub trait KnownOrder: FiniteField {
    /// The number of elements q = p^k in the field, as little-endian 64-bit limbs.
    ///
    /// Canonical: no trailing zero limb, and empty is impossible since q >= 2. Implementations
    /// pass their order through [`trim_limbs`].
    fn order_limbs() -> &'static [u64];

    /// The characteristic p of a field of order q = p^k, as little-endian 64-bit limbs.
    ///
    /// Not the same as [`Self::order_limbs`] unless k = 1. Extension fields must keep the
    /// distinction.
    fn characteristic_limbs() -> &'static [u64];

    /// The order q, or `None` if it does not fit in a `u128`.
    fn order_u128() -> Option<u128> {
        limbs_to_u128(Self::order_limbs())
    }

    /// The characteristic p, or `None` if it does not fit in a `u128`.
    fn characteristic_u128() -> Option<u128> {
        limbs_to_u128(Self::characteristic_limbs())
    }

    /// A primitive element of the finite field is a generator of the field's multiplicative group.
    ///
    /// Found by random search. The multiplicative group of a finite field is cyclic of order
    /// q - 1, and an element generates it unless its order is a proper divisor of q - 1. Every
    /// proper divisor divides (q - 1) / r for some prime r | q - 1, so those quotients are the
    /// only exponents worth testing. See Handbook of Applied Cryptography, Algorithm 4.80.
    ///
    /// This default uses nothing but the field's own arithmetic, but it does factor q - 1, so it
    /// needs the order as an integer. A type with a cheaper construction should override it — the
    /// prime fields do, via `find_generator`, which exploits their elements being integers mod p,
    /// and a field whose provider declares a generator should return that.
    ///
    /// # Panics
    /// Panics if the order does not fit in a `u128`.
    fn primitive_element<R: RngCore + CryptoRng>(rng: &mut R) -> Self {
        let group_order = Self::order_u128()
            .expect("searching for a primitive element needs the order as an integer")
            - 1;
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
    /// Panics unless `n` divides the order of the multiplicative group, or if the order does not
    /// fit in a `u128`.
    fn root_of_unity<R: RngCore + CryptoRng>(n: u64, rng: &mut R) -> Self {
        let group_order = Self::order_u128()
            .expect("constructing a root of unity needs the order as an integer")
            - 1;
        assert_eq!(group_order % n as u128, 0, "n must divide the group order.");

        // If g has order q - 1, then g^((q-1)/n) has order exactly n.
        let g = Self::primitive_element(rng);
        g.pow(group_order / n as u128)
    }

    /// The field's two-adicity: the largest s with `2^s` dividing `q - 1`.
    ///
    /// The ceiling on every power-of-two NTT over this field — a transform of size `2^k` needs a
    /// primitive `2^k`-th root of unity, which exists exactly for `k <= s`. Read off `q - 1`
    /// rather than declared, so it cannot disagree with the compiled-in modulus.
    fn two_adicity() -> u32 {
        two_adic::two_adic_decomposition(Self::order_limbs()).0
    }

    /// A primitive `2^log_n`-th root of unity.
    ///
    /// Unlike [`Self::root_of_unity`] this needs no generator and so no factorization of `q - 1`,
    /// which is what makes it the only usable path over a 254-bit field. See
    /// [`two_adic`](super::two_adic).
    ///
    /// # Panics
    /// Panics if `log_n` exceeds [`Self::two_adicity`].
    fn two_adic_root_of_unity<R: RngCore + CryptoRng>(log_n: u32, rng: &mut R) -> Self {
        two_adic::two_adic_root_of_unity::<Self, R>(log_n, rng)
    }
}

/// `limbs` as a `u128`, or `None` if it is wider than that.
fn limbs_to_u128(limbs: &[u64]) -> Option<u128> {
    if limbs.len() > 2 {
        return None;
    }
    let low = *limbs.first().unwrap_or(&0) as u128;
    let high = *limbs.get(1).unwrap_or(&0) as u128;
    Some(low | (high << 64))
}

#[cfg(test)]
mod tests {
    use crate::{
        fields::{
            binary_field::BinaryFieldElement,
            extension_field::ExtensionFieldElement,
            irreducible_polynomials::{Modulus13Pow4, X8_X4_X3_X_1},
            PrimeFieldElement128, Zp2147483647,
        },
        FiniteField, KnownOrder, One, Zero,
    };

    /// An order below 2^64 reports one limb, not a word padded with a zero.
    #[test]
    fn test_a_narrow_order_reports_one_limb() {
        assert_eq!(Zp2147483647::order_limbs(), &[2147483647]);
        assert_eq!(Zp2147483647::order_u128(), Some(2147483647));
    }

    /// An order above 2^64 reports both limbs, least significant first.
    #[test]
    fn test_a_wide_order_reports_both_limbs_little_endian() {
        // 3 * 2^66 + 1 = 12 * 2^64 + 1.
        type F = PrimeFieldElement128<221360928884514619393>;
        assert_eq!(F::order_limbs(), &[1, 12]);
        assert_eq!(F::order_u128(), Some(221360928884514619393));
    }

    /// An extension field reports q = p^k and p separately, not the same value twice.
    #[test]
    fn test_an_extension_field_separates_its_order_from_its_characteristic() {
        type F = ExtensionFieldElement<13, 4, Modulus13Pow4>;
        assert_eq!(F::order_limbs(), &[28561]); // 13^4
        assert_eq!(F::characteristic_limbs(), &[13]);
    }

    /// A binary field has characteristic two whatever its order.
    #[test]
    fn test_a_binary_field_has_characteristic_two() {
        type F = BinaryFieldElement<X8_X4_X3_X_1>;
        assert_eq!(F::order_limbs(), &[256]);
        assert_eq!(F::characteristic_limbs(), &[2]);
    }

    /// `pow_limbs` agrees with `pow` on every exponent both can express.
    #[test]
    fn test_pow_limbs_agrees_with_pow() {
        type F = PrimeFieldElement128<221360928884514619393>;
        for value in [0u64, 1, 2, 3, 97, 12345] {
            let a = <F as FiniteField>::new(value);
            for exponent in [0u128, 1, 2, 3, 17, 64, 255, 1 << 40, u64::MAX as u128] {
                let limbs = [exponent as u64, (exponent >> 64) as u64];
                assert_eq!(a.pow_limbs(&limbs), a.pow(exponent), "{value}^{exponent}");
            }
        }
    }

    /// Trailing zero limbs do not change the result, so a fixed-width order needs no trimming.
    #[test]
    fn test_pow_limbs_ignores_trailing_zero_limbs() {
        let a = Zp2147483647::new(7);
        let expected = a.pow(1000);
        for padded in [vec![1000u64], vec![1000, 0], vec![1000, 0, 0, 0]] {
            assert_eq!(a.pow_limbs(&padded), expected);
        }
    }

    /// An exponent beyond a `u128`, checked against the squarings it is made of.
    ///
    /// Fermat pins the answer independently: `a^(q-1) = 1`, and `2^192 mod (q - 1)` is computed
    /// here by the same squaring chain rather than by the limb bit-walk under test.
    #[test]
    fn test_pow_limbs_handles_an_exponent_beyond_u128() {
        let a = Zp2147483647::new(5);

        // 2^192: the fourth limb's lowest bit.
        let exponent = [0u64, 0, 0, 1];
        let mut expected = a;
        for _ in 0..192 {
            expected = expected * expected;
        }
        assert_eq!(a.pow_limbs(&exponent), expected);
    }

    /// Zero to a zero exponent is one, as it is for `pow`; zero to any other is zero.
    #[test]
    fn test_pow_limbs_of_zero() {
        let zero = Zp2147483647::zero();
        assert!(zero.pow_limbs(&[0]).is_one());
        assert!(zero.pow_limbs(&[]).is_one());
        assert!(zero.pow_limbs(&[1]).is_zero());
        assert!(zero.pow_limbs(&[0, 1]).is_zero());
    }
}
