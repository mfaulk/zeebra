//! Finite field GF(2^m) of order 2^m.
//!
//! The elements of GF(2^m) are the polynomials over GF(2) whose degree is strictly less than m.
//!
//! The non-prime fields GF(p^n) can be represented as polynomials over GF(p) whose degree is
//! strictly less than n. This set is closed under addition and subtraction, i.e., adding two
//! polynomials of degree less than n yields a polynomial of degree less than n. However,
//! it is not closed under “normal” multiplication. Instead, the product of two elements is
//! defined as the remainder of the Euclidean division of the product by an irreducible
//! polynomial of degree n. Here, removing multiples of the irreducible polynomial sort of
//! serves the same roll as taking the integers mod p. The effect is that the remainder has
//! degree strictly less than n, and so this multiplication is closed.
//!
//! # Representing polynomials as bit patterns.
//! The i^th bit represents c_i in the polynomial \sum_{i=1}^m c_i * x_i.
//!
//! # Arithmetic in GF(2^m).
//! Addition and subtraction of bit patterns is XOR. Multiplying  two polynomials involves
//! "cross multiplying" the elements of their bit patters. Easiest to think about if you
//! write out the polynomials as powers of x, and then multiply the terms out.

use std::{
    fmt::{Display, Formatter},
    ops,
};

#[cfg(any(test, feature = "proptest"))]
use proptest::{arbitrary::Arbitrary, prelude::BoxedStrategy, strategy::Strategy};
use rand::{CryptoRng, RngCore};
use serde::{Deserialize, Serialize};

use crate::{impl_add_variants, impl_div_variants, impl_mul_variants, impl_sub_variants};

use crate::{
    fields::{trim_limbs, KnownOrder},
    identities::{One, Zero},
    integers::limbs_minus_two,
    FiniteField, ParseFieldElementError, Ring,
};

#[derive(Copy, Clone, Hash, Debug, Default, Eq, PartialEq, Serialize, Deserialize)]
/// A binary field GF(2^m), modulo an irreducible polynomial P.
pub struct BinaryFieldElement<const P: u64> {
    /// The i^th bit represents c_i in the polynomial \sum_{i=1}^m c_i * x_i.
    ///
    /// Private so that the bit pattern cannot be set from outside: `new` and deserialization both
    /// check it, and `PartialEq` and `Hash` are derived over it, so an unreduced pattern would
    /// compare unequal to the element it represents.
    #[serde(deserialize_with = "reduced_polynomial::<_, P>")]
    coefficients: u64,
}

/// The number of valid bit patterns, 2^m for the modulus' degree m.
///
/// Elements of GF(2^m) are the polynomials of degree strictly below m, so this is the exclusive
/// upper bound on a valid pattern. It is tighter than P: since P is monic of degree m, P itself is
/// 2^m plus lower-order terms, and every pattern in [2^m, P) has degree m and is not an element.
const fn num_elements<const P: u64>() -> u64 {
    1 << (63 - P.leading_zeros())
}

/// Accepts a bit pattern only if it denotes a polynomial of degree below the modulus' degree.
///
/// Rejecting rather than reducing: a pattern outside the field did not come from this field, so it
/// signals corruption or a mismatched modulus, and reducing it silently would hide that.
fn reduced_polynomial<'de, D, const P: u64>(deserializer: D) -> Result<u64, D::Error>
where
    D: serde::Deserializer<'de>,
{
    let coefficients = u64::deserialize(deserializer)?;
    if coefficients >= num_elements::<P>() {
        return Err(serde::de::Error::custom(format!(
            "the bit pattern {coefficients} has degree at least that of the modulus {P}, so it \
             does not denote an element of this field"
        )));
    }
    Ok(coefficients)
}

/// A decimal integer as a bit pattern of degree below the modulus' degree.
///
/// Rejects rather than reduces: a pattern of degree at least m is not an element of GF(2^m), and
/// masking it to one would silently accept input the field cannot represent. Overflow of a `u64`
/// is the same answer, since the pattern is at most 63 bits wide.
fn parse_bit_pattern<const P: u64>(value: &str) -> Result<u64, ParseFieldElementError> {
    let digits = value.strip_prefix('+').unwrap_or(value);
    if digits.is_empty() {
        return Err(ParseFieldElementError::OutOfRange);
    }
    if let Some(offender) = digits.bytes().find(|b| !b.is_ascii_digit()) {
        return Err(ParseFieldElementError::InvalidCharacter(
            offender.wrapping_sub(b'0'),
        ));
    }

    let pattern: u64 = digits
        .parse()
        .map_err(|_| ParseFieldElementError::OutOfRange)?;
    if pattern >= num_elements::<P>() {
        return Err(ParseFieldElementError::OutOfRange);
    }
    Ok(pattern)
}

impl<const P: u64> BinaryFieldElement<P> {
    /// An element in the binary field GF(2^m).
    ///
    /// Takes a representation, where [`FiniteField::new`] takes an integer to embed; this reaches
    /// every element and that one reaches GF(2). An inherent method wins method resolution, so
    /// `BinaryFieldElement::<P>::new(5)` is this one.
    ///
    /// # Arguments
    /// * `coefficients` - The i^th bit represents c_i in the polynomial \sum_{i=1}^m c_i * x_i.
    ///
    /// # Panics
    /// Panics if the pattern has degree at least that of the modulus, i.e. is not an element of
    /// this field. Use [`FiniteField::from_str`] or [`KnownOrder::element_at`] where the value is
    /// not known to be in range.
    pub fn new(coefficients: u64) -> Self {
        // TODO: debug_assert that P is irreducible?
        //
        // The bound is 2^m, not P. Both reject patterns of degree above the modulus, but P also
        // admits [2^m, P) — patterns of degree exactly m, which are not elements of GF(2^m) and
        // which no arithmetic here can produce.
        assert!(
            coefficients < num_elements::<P>(),
            "the bit pattern {coefficients} has degree at least that of the modulus {P}"
        );
        Self { coefficients }
    }

    /// (The bit pattern of) this field's modulus, i.e., irreducible polynomial.
    pub fn modulus(&self) -> u64 {
        P
    }

    /// The coefficient bit pattern: the i^th bit is c_i in \sum c_i x^i.
    pub fn coefficients(&self) -> u64 {
        self.coefficients
    }
}

// impl Zero
impl<const P: u64> Zero for BinaryFieldElement<P> {
    const ZERO: Self = BinaryFieldElement { coefficients: 0 };
}

// impl One
impl<const P: u64> One for BinaryFieldElement<P> {
    const ONE: Self = BinaryFieldElement { coefficients: 1 };
}

// impl Ring
impl<const P: u64> Ring for BinaryFieldElement<P> {}

// impl FiniteField
impl<const P: u64> FiniteField for BinaryFieldElement<P> {
    /// `val mod 2`: the prime subfield GF(2), which is all the integers reach here.
    ///
    /// Not the inherent [`BinaryFieldElement::new`], which takes a bit pattern and reaches every
    /// element. See [`FiniteField::new`] for why the trait method is the embedding instead, and
    /// [`KnownOrder::element_at`] for addressing elements by index.
    fn new(val: u64) -> Self {
        if val.is_multiple_of(2) {
            Self::zero()
        } else {
            Self::one()
        }
    }

    /// A decimal integer, read as the coefficient bit pattern — what [`Display`] writes.
    ///
    /// So `from_str("5")` is `x^2 + 1`, not `5 mod 2`. See [`FiniteField::from_str`].
    fn from_str(value: &str) -> Result<Self, ParseFieldElementError> {
        // The inherent `new`, which takes the bit pattern — an inherent method wins method
        // resolution over the trait method of the same name directly above.
        Ok(BinaryFieldElement::<P>::new(parse_bit_pattern::<P>(value)?))
    }

    fn random<R: RngCore + CryptoRng>(rng: &mut R) -> Self {
        // Generate a random m-bit coefficient bit pattern.
        let mask = Self::ORDER as u64 - 1; // The low-order m bits are set.
        let coefficients = rng.next_u64() & mask;
        Self::new(coefficients)
    }

    fn inverse(&self) -> Self {
        assert_ne!(
            *self,
            Self::zero(),
            "The zero element does not have a multiplicative inverse."
        );
        self.pow_limbs(&Self::FERMAT_EXPONENT_LIMBS)
    }
}

impl<const P: u64> BinaryFieldElement<P> {
    /// 2^m, where m is the degree of the modulus polynomial P.
    const ORDER: u128 = 2u128.pow(63 - P.leading_zeros());

    /// See [`KnownOrder::order_limbs`].
    const ORDER_LIMBS: [u64; 2] = [Self::ORDER as u64, (Self::ORDER >> 64) as u64];

    /// Characteristic two. See [`KnownOrder::characteristic_limbs`].
    const CHARACTERISTIC_LIMBS: [u64; 1] = [2];

    /// The Fermat inversion exponent q - 2, as little-endian limbs.
    ///
    /// Subtracted on the limbs rather than on a machine integer, and held at the width of
    /// [`Self::ORDER_LIMBS`], so nothing here caps the order at the width of a `u128`.
    const FERMAT_EXPONENT_LIMBS: [u64; 2] = limbs_minus_two(Self::ORDER_LIMBS);
}

impl<const P: u64> KnownOrder for BinaryFieldElement<P> {
    fn order_limbs() -> &'static [u64] {
        trim_limbs(&Self::ORDER_LIMBS)
    }

    fn characteristic_limbs() -> &'static [u64] {
        trim_limbs(&Self::CHARACTERISTIC_LIMBS)
    }

    /// The bit pattern `index`, so `0..2^m` covers the field exactly once.
    ///
    /// Overrides the default, which refuses an extension rather than enumerate its prime subfield.
    fn element_at(index: u128) -> Option<Self> {
        if index >= Self::ORDER {
            return None;
        }
        Some(BinaryFieldElement::<P>::new(index as u64))
    }
}

// Borrowed + Borrowed
impl<const P: u64> ops::Add<Self> for &BinaryFieldElement<P> {
    type Output = BinaryFieldElement<P>;

    fn add(self, rhs: Self) -> Self::Output {
        // Adding polynomials over GF(2) corresponds to XOR-ing the polynomials' coefficients.
        let coefficients = self.coefficients ^ rhs.coefficients;
        Self::Output { coefficients }
    }
}

impl_add_variants!([const P: u64], BinaryFieldElement<P>);

// Borrowed - Borrowed
impl<const P: u64> ops::Sub<Self> for &BinaryFieldElement<P> {
    type Output = BinaryFieldElement<P>;

    fn sub(self, rhs: Self) -> Self::Output {
        // Subtracting polynomials over GF(2) corresponds to XOR-ing the polynomials' coefficients.
        let coefficients = self.coefficients ^ rhs.coefficients;
        Self::Output { coefficients }
    }
}

impl_sub_variants!([const P: u64], BinaryFieldElement<P>);

impl<const P: u64> ops::Neg for BinaryFieldElement<P> {
    type Output = BinaryFieldElement<P>;

    fn neg(self) -> Self::Output {
        BinaryFieldElement::zero() - self
    }
}

impl<const P: u64> ops::Neg for &BinaryFieldElement<P> {
    type Output = BinaryFieldElement<P>;

    fn neg(self) -> Self::Output {
        BinaryFieldElement::zero() - self
    }
}

// Borrowed * Borrowed
impl<const P: u64> ops::Mul<Self> for &BinaryFieldElement<P> {
    type Output = BinaryFieldElement<P>;

    fn mul(self, rhs: Self) -> Self::Output {
        let product = multiply_polynomials(self.coefficients, rhs.coefficients);
        // The product modulo the irreducible polynomial. Barrett rather than `long_divide`, whose
        // loop runs once per degree the product must come down; the two agree on every product
        // this field can form, which `tests::test_barrett_agrees_with_long_division` checks.
        Self::Output {
            coefficients: barrett_reduce::<P>(product),
        }
    }
}

impl_mul_variants!([const P: u64], BinaryFieldElement<P>);

// Borrowed / Borrowed
impl<const P: u64> ops::Div<Self> for &BinaryFieldElement<P> {
    type Output = BinaryFieldElement<P>;

    fn div(self, rhs: Self) -> Self::Output {
        // Division is multiplication by the inverse.
        self * rhs.inverse()
    }
}

impl_div_variants!([const P: u64], BinaryFieldElement<P>);

// impl Display
//
// The bit pattern in decimal. `FiniteField::from_str` reads exactly this back, which is what makes
// the round trip hold and what fixes the meaning of a bare decimal over this field.
impl<const P: u64> Display for BinaryFieldElement<P> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.coefficients)
    }
}

#[cfg(any(test, feature = "proptest"))]
impl<const P: u64> Arbitrary for BinaryFieldElement<P> {
    type Parameters = ();

    fn arbitrary_with(_args: Self::Parameters) -> Self::Strategy {
        // Every bit pattern below the field's order is a distinct element. The modulus has degree
        // m, so it is at least 2^m = order, and `new`'s `coefficients < P` assertion holds.
        (0u64..Self::ORDER as u64).prop_map(Self::new).boxed()
    }

    type Strategy = BoxedStrategy<Self>;
}

/// Multiply the coefficient bit patterns for two polynomials in GF(2).
///
/// Carry-less multiplication is a single instruction on any x86-64 part with `pclmulqdq`, which
/// is not implied by the `x86-64-v3` floor this crate builds against — it arrived with the AES-NI
/// generation and is not part of any of the microarchitecture levels. So the choice is made at run
/// time, from a cached feature probe, and [`multiply_polynomials_scalar`] remains for everything
/// else.
fn multiply_polynomials(a: u64, b: u64) -> u128 {
    #[cfg(target_arch = "x86_64")]
    {
        if std::arch::is_x86_feature_detected!("pclmulqdq") {
            // SAFETY: guarded by the feature probe immediately above.
            return unsafe { multiply_polynomials_pclmulqdq(a, b) };
        }
    }
    multiply_polynomials_scalar(a, b)
}

/// One `PCLMULQDQ` in place of the bit-at-a-time loop.
///
/// # Safety
/// The caller must have established that the target supports `pclmulqdq`.
#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "pclmulqdq")]
unsafe fn multiply_polynomials_pclmulqdq(a: u64, b: u64) -> u128 {
    use std::arch::x86_64::{__m128i, _mm_clmulepi64_si128, _mm_set_epi64x, _mm_storeu_si128};

    let left = _mm_set_epi64x(0, a as i64);
    let right = _mm_set_epi64x(0, b as i64);
    // Immediate 0x00 selects the low quadword of each operand.
    let product = _mm_clmulepi64_si128(left, right, 0x00);

    // Stored rather than extracted with `_mm_extract_epi64`, which would pull in SSE4.1 on top of
    // the one feature this function actually needs.
    let mut halves = [0u64; 2];
    _mm_storeu_si128(halves.as_mut_ptr() as *mut __m128i, product);
    ((halves[1] as u128) << 64) | halves[0] as u128
}

/// Carry-less multiplication, one bit of `a` at a time.
///
/// The fallback for targets without `pclmulqdq`, and the oracle the accelerated path is tested
/// against.
fn multiply_polynomials_scalar(a: u64, b: u64) -> u128 {
    let b = b as u128;
    let mut result = 0;
    // If the i^th bit of a is 1, shift b left by i, and xor the shifted b into result.
    for i in 0..64 {
        if a & (1 << i) != 0 {
            result ^= b << i;
        }
    }
    result
}

/// `floor(x^(2m) / P)` for a modulus `P` of degree m: the Barrett reduction constant.
///
/// Computed by the same long division [`long_divide`] performs, but at compile time, so the two
/// agree by construction — `tests::test_the_barrett_constant_is_the_quotient_long_division_gives`
/// checks that they do.
///
/// The quotient has degree exactly m, so it needs m + 1 bits and fits a `u64` for every m up to
/// 63, which is the largest degree a `u64` modulus can have.
const fn barrett_constant(p: u64) -> u64 {
    let m = modulus_degree(p);
    let divisor = p as u128;
    let mut remainder: u128 = 1u128 << (2 * m);
    let mut quotient: u64 = 0;
    let mut shift = m;
    loop {
        if (remainder >> (m + shift)) & 1 == 1 {
            quotient |= 1u64 << shift;
            remainder ^= divisor << shift;
        }
        if shift == 0 {
            break;
        }
        shift -= 1;
    }
    quotient
}

/// The degree of a nonzero modulus bit pattern.
const fn modulus_degree(p: u64) -> u32 {
    63 - p.leading_zeros()
}

/// `product mod P`, by Barrett reduction rather than long division.
///
/// Three carry-less multiplications and two shifts, in place of a loop that runs once per degree
/// the product has to come down — up to m iterations, each recomputing a leading-zero count.
///
/// Requires `deg(product) < 2m`, which holds for every product this field can form: an element is
/// a pattern below `2^m`, so its degree is at most m - 1 and a product of two has degree at most
/// 2m - 2. The patterns in `[2^m, P)` have degree m and would break that bound, which is exactly
/// why `new` rejects them rather than merely requiring a pattern below P.
fn barrett_reduce<const P: u64>(product: u128) -> u64 {
    let m = modulus_degree(P);
    debug_assert!(
        product == 0 || degree_u128(product) < 2 * m,
        "a product of degree {} cannot be Barrett reduced modulo a degree-{} polynomial",
        degree_u128(product),
        m
    );

    // q1 = floor(product / x^m), of degree below m, so it fits a u64.
    let q1 = (product >> m) as u64;
    // q3 = floor(q1 * mu / x^m), the quotient estimate.
    let q3 = (multiply_polynomials(q1, barrett_constant(P)) >> m) as u64;
    // product - q3*P, which over GF(2) is an exclusive or. Only the low m bits survive; m is at
    // most 63 for a u64 modulus, so the mask cannot overflow.
    let mask = (1u64 << m) - 1;
    ((product ^ multiply_polynomials(q3, P)) as u64) & mask
}

/// Divide dividend by divisor. Return the quotient and remainder.
///
/// Retained as the oracle for [`barrett_reduce`] and [`barrett_constant`], which replaced it on
/// the multiplication path. It has no caller outside the tests, and it carries no precondition on
/// the numerator's degree, which is what makes it the reference the Barrett path is checked
/// against rather than something to ship beside it.
///
/// # Arguments
/// * `numerator` - Bit pattern of numerator polynomial.
/// * `denominator` - Bit pattern of denominator polynomial.
#[cfg(test)]
fn long_divide(numerator: u128, denominator: u64) -> (u64, u64) {
    assert_ne!(denominator, 0, "division by the zero polynomial");
    let denominator = denominator as u128;
    // The numerator will be reduced until it has degree less than m.
    let m = degree_u128(denominator);
    let mut quotient: u64 = 0;
    let mut remainder = numerator;
    // `degree_u128` reports 0 for the zero polynomial rather than "no degree", so a zero
    // remainder has to be excluded explicitly. Without that, dividing by a degree-0 polynomial
    // (the constant 1) loops forever: the remainder alternates between 0 and 1.
    while remainder != 0 && degree_u128(remainder) >= m {
        let shift = degree_u128(remainder) - m;
        quotient += 1 << shift;
        remainder ^= denominator << shift;
    }
    (quotient, remainder as u64)
}

// The degree of the polynomial corresponding to the bit pattern.
#[allow(unused)]
fn degree_u64(bit_pattern: u64) -> u32 {
    degree_u128(bit_pattern as u128)
}

// The degree of the polynomial corresponding to the bit pattern.
fn degree_u128(bit_pattern: u128) -> u32 {
    let num_bits_set = 128 - bit_pattern.leading_zeros();
    if num_bits_set > 0 {
        num_bits_set - 1
    } else {
        num_bits_set
    }
}

// // e.g. "x^4 + x + 1" --> 0b10011
// fn bit_pattern(s: &str) -> u64 {
//     let mut result = 0;
//     let terms: Vec<_> = s.split_whitespace().collect();
//     // Check for garbage input. Each term must be "+", "x^{exponent}", "x", or "1".
//     // There should not be duplicate terms.
//     // For each term, set corresponding bit of the bit pattern.
//     unimplemented!()
// }

#[cfg(test)]
mod tests {
    use crate::identities::{One, Zero};
    use proptest::{arbitrary::Arbitrary, proptest};
    use rand::thread_rng;
    use std::collections::HashSet;

    use crate::{
        fields::{
            binary_field::num_elements,
            binary_field::{
                barrett_constant, barrett_reduce, degree_u128, degree_u64, long_divide,
                modulus_degree, multiply_polynomials, multiply_polynomials_scalar,
                BinaryFieldElement,
            },
            finite_field::fermat_inverse_via_recursive_pow,
            irreducible_polynomials::{X5_X2_1, X63_X_1, X8_X4_X3_X2_1, X8_X4_X3_X_1},
        },
        FiniteField, KnownOrder, ParseFieldElementError,
    };
    use rand::{Rng, SeedableRng};

    /// A decimal is the coefficient bit pattern, so `from_str` inverts `Display` over GF(2^8).
    #[test]
    fn test_from_str_reads_a_decimal_as_the_bit_pattern() {
        type F = BinaryFieldElement<X8_X4_X3_X_1>;
        for pattern in 0..256u64 {
            let element = F::new(pattern);
            assert_eq!(
                <F as FiniteField>::from_str(&pattern.to_string()),
                Ok(element)
            );
            assert_eq!(element.to_string(), pattern.to_string());
        }
        // x^2 + 1, not 5 mod 2.
        assert_eq!(
            <F as FiniteField>::from_str("5"),
            Ok(F::new(0b101)),
            "a decimal is the bit pattern"
        );
    }

    /// The trait `new` is the prime-subfield embedding; the inherent `new` is the bit pattern.
    #[test]
    fn test_the_trait_new_embeds_the_prime_subfield() {
        type F = BinaryFieldElement<X8_X4_X3_X_1>;
        for value in 0..16u64 {
            let embedded = <F as FiniteField>::new(value);
            assert_eq!(
                embedded,
                if value % 2 == 0 { F::zero() } else { F::one() },
                "the embedding of {value} is not {value} mod 2"
            );
        }
        // The inherent `new`, which wins method resolution, means something else for the same 5.
        assert_eq!(<F as FiniteField>::new(5), F::one());
        assert_eq!(F::new(5).coefficients(), 0b101);
    }

    /// A pattern of degree at least the modulus' is out of range, not a masked element.
    #[test]
    fn test_from_str_rejects_a_pattern_outside_the_field() {
        type F = BinaryFieldElement<X8_X4_X3_X_1>;
        for value in ["256", "257", "1000", "18446744073709551616"] {
            assert_eq!(
                <F as FiniteField>::from_str(value),
                Err(ParseFieldElementError::OutOfRange),
                "{value} should be out of range for GF(2^8)"
            );
        }
        // GF(2^5) stops five bits earlier.
        assert_eq!(
            <BinaryFieldElement<X5_X2_1> as FiniteField>::from_str("32"),
            Err(ParseFieldElementError::OutOfRange)
        );
    }

    /// Malformed text is a `Result`, never a panic.
    #[test]
    fn test_from_str_rejects_malformed_text() {
        type F = BinaryFieldElement<X8_X4_X3_X_1>;
        assert_eq!(
            <F as FiniteField>::from_str(""),
            Err(ParseFieldElementError::OutOfRange)
        );
        assert_eq!(
            <F as FiniteField>::from_str("+"),
            Err(ParseFieldElementError::OutOfRange)
        );
        assert_eq!(
            <F as FiniteField>::from_str("x^2+1"),
            Err(ParseFieldElementError::InvalidCharacter(b'x' - b'0'))
        );
        assert_eq!(
            <F as FiniteField>::from_str("-1"),
            Err(ParseFieldElementError::InvalidCharacter(
                b'-'.wrapping_sub(b'0')
            ))
        );
        // A leading `+` is accepted, as the polynomial grammar may emit one.
        assert_eq!(<F as FiniteField>::from_str("+7"), Ok(F::new(7)));
    }

    /// `element_at` walks all 2^m bit patterns and stops there.
    #[test]
    fn test_element_at_is_the_bit_pattern() {
        type F = BinaryFieldElement<X5_X2_1>;
        for index in 0..32u128 {
            assert_eq!(F::element_at(index), Some(F::new(index as u64)));
        }
        assert_eq!(F::element_at(32), None);
    }

    /// A deterministic stream of operand pairs reduced for a degree-m modulus.
    fn operand_pairs(m: u32, count: usize, seed: u64) -> Vec<(u64, u64)> {
        let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
        let mask = if m >= 64 { u64::MAX } else { (1u64 << m) - 1 };
        (0..count)
            .map(|_| (rng.gen::<u64>() & mask, rng.gen::<u64>() & mask))
            .collect()
    }

    /// The accelerated carry-less multiply agrees with the bit-at-a-time fallback.
    ///
    /// Both paths are exercised here whatever the host supports: `multiply_polynomials` takes the
    /// accelerated route when the CPU has `pclmulqdq`, and `multiply_polynomials_scalar` is called
    /// directly, so a machine with the instruction still tests the fallback it would otherwise
    /// never run.
    #[test]
    fn test_carry_less_multiplication_agrees_with_the_scalar_fallback() {
        // The top bits matter most: a carry-less implementation fails differently from a loop, and
        // the full-width cases are where the 128-bit result is actually filled.
        let edges: [u64; 8] = [
            0,
            1,
            2,
            u64::MAX,
            1 << 63,
            (1 << 63) | 1,
            0xFFFF_FFFF,
            0xAAAA_AAAA_AAAA_AAAA,
        ];
        for a in edges {
            for b in edges {
                assert_eq!(
                    multiply_polynomials(a, b),
                    multiply_polynomials_scalar(a, b),
                    "{a:#x} * {b:#x}"
                );
            }
        }

        for (a, b) in operand_pairs(64, 4096, 0xC14) {
            assert_eq!(
                multiply_polynomials(a, b),
                multiply_polynomials_scalar(a, b),
                "{a:#x} * {b:#x}"
            );
        }
    }

    /// The Barrett constant is the quotient long division gives for `x^(2m) / P`.
    ///
    /// `barrett_constant` is a compile-time reimplementation of the same division `long_divide`
    /// performs, so the two must agree; a wrong constant is a silently wrong product, not a panic.
    #[test]
    fn test_the_barrett_constant_is_the_quotient_long_division_gives() {
        for p in [X5_X2_1, X8_X4_X3_X_1, X63_X_1, 0b11, 0b111, 0b1011] {
            let m = modulus_degree(p);
            let (quotient, _remainder) = long_divide(1u128 << (2 * m), p);
            assert_eq!(
                barrett_constant(p),
                quotient,
                "modulus {p:#x} of degree {m}"
            );
        }
    }

    /// Barrett reduction agrees with long division on every product this field can form.
    ///
    /// `long_divide` is the oracle: it is the algorithm the multiply used before, and it has no
    /// precondition on the product's degree. Operands are masked to below 2^m, which is the
    /// invariant `new` enforces and the precondition Barrett relies on.
    #[test]
    fn test_barrett_agrees_with_long_division() {
        fn check<const P: u64>(count: usize, seed: u64) {
            let m = modulus_degree(P);
            for (a, b) in operand_pairs(m, count, seed) {
                let product = multiply_polynomials(a, b);
                let (_quotient, expected) = long_divide(product, P);
                assert_eq!(
                    barrett_reduce::<P>(product),
                    expected,
                    "modulus {P:#x}: {a:#x} * {b:#x}"
                );
            }
        }

        check::<X5_X2_1>(4096, 1);
        check::<X8_X4_X3_X_1>(4096, 2);
        // Degree 63, where the product fills 125 bits and the constant needs all 64.
        check::<X63_X_1>(4096, 3);

        // Exhaustive over GF(2^5), which is small enough to enumerate completely.
        let m = modulus_degree(X5_X2_1);
        for a in 0..(1u64 << m) {
            for b in 0..(1u64 << m) {
                let product = multiply_polynomials(a, b);
                let (_quotient, expected) = long_divide(product, X5_X2_1);
                assert_eq!(barrett_reduce::<X5_X2_1>(product), expected, "{a} * {b}");
            }
        }
    }

    /// GF(2^5) modulo x^5 + x^2 + 1, whose 32 elements are the patterns below 2^5.
    type F32 = BinaryFieldElement<X5_X2_1>;

    /// The valid-pattern bound is 2^m, which is strictly tighter than the modulus itself.
    #[test]
    fn test_num_elements_is_two_to_the_modulus_degree() {
        // X5_X2_1 is 0b100101 = 37, of degree 5, so GF(2^5) has 32 elements.
        assert_eq!(num_elements::<X5_X2_1>(), 32);
        assert!(num_elements::<X5_X2_1>() < X5_X2_1);
        assert_eq!(
            num_elements::<X5_X2_1>() as u128,
            F32::order_u128().unwrap()
        );
    }

    /// Deserializing a bit pattern of degree at or above the modulus' is rejected.
    #[test]
    fn test_deserializing_a_pattern_outside_the_field_is_rejected() {
        // 32 = x^5 has degree 5, the modulus' own degree, so it is not an element.
        let encoded = bincode::serialize(&32u64).unwrap();
        let decoded: Result<F32, _> = bincode::deserialize(&encoded);
        assert!(decoded.is_err(), "x^5 is not an element of GF(2^5)");

        // 36 lies in [2^m, P), the gap the old `coefficients < P` bound wrongly admitted.
        let encoded = bincode::serialize(&36u64).unwrap();
        let decoded: Result<F32, _> = bincode::deserialize(&encoded);
        assert!(decoded.is_err(), "patterns in [2^m, P) are not elements");

        let encoded = bincode::serialize(&1000u64).unwrap();
        let decoded: Result<F32, _> = bincode::deserialize(&encoded);
        assert!(decoded.is_err(), "1000 is far outside GF(2^5)");
    }

    /// Validating deserialization does not change the wire format: every element round-trips.
    #[test]
    fn test_serde_round_trip_is_unchanged() {
        for coefficients in 0..32u64 {
            let element = F32::new(coefficients);
            let encoded = bincode::serialize(&element).unwrap();
            let decoded: F32 = bincode::deserialize(&encoded).unwrap();
            assert_eq!(decoded, element);
        }
    }

    /// `new` rejects a pattern of degree at or above the modulus', as deserialization does.
    #[test]
    #[should_panic(expected = "has degree at least that of the modulus")]
    fn test_new_rejects_a_pattern_outside_the_field() {
        let _ = F32::new(36);
    }

    // GF(2^5), GF(2^8), and GF(2^63): a small field, a byte-sized field, and one near the width
    // limit of the u64 bit-pattern representation.
    type Gf32 = BinaryFieldElement<X5_X2_1>;
    type Gf256 = BinaryFieldElement<X8_X4_X3_X_1>;
    type Gf2Pow63 = BinaryFieldElement<X63_X_1>;

    #[test]
    fn test_degree() {
        assert_eq!(degree_u64(0b100100), 5); // x^5 + x^2 + 1
        assert_eq!(degree_u64(0b10011110101), 10); // x^10 + ...
        assert_eq!(degree_u64(1 << 63), 63);

        assert_eq!(degree_u128(0), 0);
        assert_eq!(degree_u128(1), 0);
        assert_eq!(degree_u128(1 << 111), 111);
        assert_eq!(degree_u128(1 << 127), 127);
    }

    #[test]
    // Addition should XOR the coefficients.
    fn test_add() {
        let a = BinaryFieldElement::<X5_X2_1>::new(0b0101);
        let b = BinaryFieldElement::<X5_X2_1>::new(0b1101);
        assert_eq!(a + b, BinaryFieldElement::new(0b1000)); //0b0101 XOR 0b1101
    }

    #[test]
    // Subtraction should (also) XOR the coefficients.
    fn test_sub() {
        let a = BinaryFieldElement::<X5_X2_1>::new(0b0101);
        let b = BinaryFieldElement::<X5_X2_1>::new(0b1101);
        assert_eq!(a - b, BinaryFieldElement::new(0b1000)); //0b0101 XOR 0b1101
    }

    #[test]
    // (x^4 + x + 1)(x^6 + x + 1) = (x^10 + x^7 + x^6 + x^5 + x^4 + x^2 +1)
    fn test_multiply_polynomials() {
        let a = 0b10011; // x^4 + x + 1
        let b = 0b1000011; // x^6 + x + 1
        let prod = multiply_polynomials(a, b);
        assert_eq!(prod, 0b10011110101);
    }

    #[test]
    // (x^4 + x + 1)^2 = x^8 + x^2 + 1
    fn test_multiply_polynomials_two() {
        let a = (1 << 4) + (1 << 1) + 1;
        let a_squared = multiply_polynomials(a, a);
        let expected = (1 << 8) + (1 << 2) + 1;
        assert_eq!(a_squared, expected)
    }

    #[test]
    fn test_long_divide_one() {
        let a: u64 = 0b1101; // x^3 + x^2 + 1
        let (quotient, remainder) = long_divide(a as u128, a);
        assert_eq!(quotient, 0b1);
        assert_eq!(remainder, 0b0);

        let b: u64 = 0b10; // x
        let (quotient, remainder) = long_divide(a as u128, b); // x^3 + x^2 + 1
        assert_eq!(quotient, 0b110); // x^2 + x
        assert_eq!(remainder, 0b1); // 1
    }

    #[test]
    // x^5 + x^4 + x^3 + x^2 + x + 1 = (x+1)(x^4 + x^2 + 1) + 0
    fn test_long_divide_two() {
        let a = 0b111111; // x^5 + x^4 + x^3 + x^2 + x + 1
        let b = 0b11; // x + 1
        let (quotient, remainder) = long_divide(a, b);
        assert_eq!(quotient, 0b10101); // x^4 + x^2 + 1
        assert_eq!(remainder, 0b0);
    }

    #[test]
    // x^3 + 1 = (x^2)x + 1
    fn test_long_divide_three() {
        let a = 0b1001; // x^3 + 1;
        let b = 0b10; // x

        let (quotient, remainder) = long_divide(a, b);
        assert_eq!(quotient, 0b100); // x^2
        assert_eq!(remainder, 0b1); // 1
    }

    #[test]
    /// Return dividend as remainder if dividend is less than divisor.
    fn test_long_divide_four() {
        let a = 0b10; // x
        let b = 0b1001; // x^3 + 1;

        let (quotient, remainder) = long_divide(a, b);
        assert_eq!(quotient, 0b0); // 0
        assert_eq!(remainder, 0b10); // x
    }

    #[test]
    // x^10 + x^7 + x^6 + x^5 + x^4 + x^2 +1 = (x^8 + x^4 + x^3 + x + 1)(x^2) + (x^7 + x^4 + x^3 + 1)
    fn test_long_divide_five() {
        let a = 0b10011110101; // x^10 + x^7 + x^6 + x^5 + x^4 + x^2 +1
        let b = 0b100011011; // x^8 + x^4 + x^3 + x + 1
        let (quotient, remainder) = long_divide(a, b);
        assert_eq!(quotient, 0b100); // x^2
        assert_eq!(remainder, 0b10011001); // x^7 + x^4 + x^3 + 1
    }

    /// Dividing by the constant polynomial 1 terminates and returns the numerator.
    #[test]
    fn test_long_divide_by_one() {
        assert_eq!(long_divide(0b1101, 0b1), (0b1101, 0));
        assert_eq!(long_divide(0, 0b1), (0, 0));
        assert_eq!(long_divide(u64::MAX as u128, 0b1), (u64::MAX, 0));
    }

    /// The zero polynomial is not a valid divisor.
    #[test]
    #[should_panic(expected = "division by the zero polynomial")]
    fn test_long_divide_by_zero_panics() {
        let _ = long_divide(0b1101, 0);
    }

    #[test]
    fn test_mul_no_reduction() {
        let a = BinaryFieldElement::<X5_X2_1>::new(0b0101); // x^2 + 1
        let b = BinaryFieldElement::<X5_X2_1>::new(0b0100); // x^2
        let prod = a * b;
        assert_eq!(prod.coefficients, 0b10100); // x^4 + x^2
    }

    #[test]
    fn test_mul() {
        // sage: K.<x> = GF(2**8, name='x', modulus=x^8 + x^4 + x^3 + x + 1 )
        // sage: a = K.fetch_int( 2^4 + 2 + 1)
        // sage: b = K.fetch_int(2^6 + 2 + 1)
        // sage: a * b
        // x^7 + x^4 + x^3 + 1

        let a = BinaryFieldElement::<X8_X4_X3_X_1>::new(0b10011); // x^4 + x + 1
        let b = BinaryFieldElement::<X8_X4_X3_X_1>::new(0b1000011); // x^6 + x + 1)

        // See https://gendignoux.com/blog/2021/11/01/horcrux-1-math.html#arithmetic-in-mathrmgf2n
        // Difference between multiplying numbers and multiplying binary polynomials:
        // assert_eq!(0b10011 * 0b1000011, 0b10011110101); // x^10 + x^7 + x^6 + x^5 + x^4 + x^2 +1

        let prod = a * b;
        println!("a * b = {:#016b}", prod.coefficients);
        assert_eq!(prod.coefficients, 0b10011001); // // x^7 + x^4 + x^3 + 1
    }

    #[test]
    fn test_mul_a_times_a() {
        // sage: K.<x> = GF(2**8, name='x', modulus=x^8 + x^4 + x^3 + x + 1 )
        // sage: a = K.fetch_int( 2^4 + 2 + 1)
        // sage: a^2
        //   x^4 + x^3 + x^2 + x

        let bit_pattern = (1 << 4) + (1 << 1) + 1; // x^4 + x + 1
        let a = BinaryFieldElement::<X8_X4_X3_X_1>::new(bit_pattern);
        let a_squared = a * a;
        let expected = (1 << 4) + (1 << 3) + (1 << 2) + (1 << 1);
        assert_eq!(
            a_squared.coefficients, expected,
            "{:#016b}, {:#016b}",
            a_squared.coefficients, expected
        );
    }

    #[test]
    fn test_order() {
        // sage: K.<x> = GF(2**8, name='x', modulus=x^8 + x^4 + x^3 + x + 1 )
        // sage K.order
        // 256

        assert_eq!(
            BinaryFieldElement::<X8_X4_X3_X_1>::order_u128().unwrap(),
            256
        );
    }

    #[test]
    // random should not panic
    fn test_random() {
        let mut rng = thread_rng();
        for _i in 0..1000 {
            let _element = BinaryFieldElement::<X63_X_1>::random(&mut rng);
        }
    }

    #[test]
    fn test_pow() {
        let bit_pattern = (1 << 4) + (1 << 1) + 1; // x^4 + x + 1
        let a = BinaryFieldElement::<X8_X4_X3_X_1>::new(bit_pattern);

        assert_eq!(a.pow(1), a);
        assert_eq!(a.pow(2), a * a);
        assert_eq!(a.pow(3), a * a * a);

        // sage: K.<x> = GF(2**8, name='x', modulus=x^8 + x^4 + x^3 + x + 1 )
        // sage: a = K.fetch_int( 2^4 + 2 + 1)
        // sage: a^2
        //   x^4 + x^3 + x^2 + x

        assert_eq!(
            a.pow(2).coefficients,
            (1 << 4) + (1 << 3) + (1 << 2) + (1 << 1)
        );

        // sage: a^12
        //   x^7 + x
        assert_eq!(a.pow(12).coefficients, (1 << 7) + (1 << 1));

        // sage: a^241
        //  x^7 + x^5 + x^4 + x^3
        assert_eq!(
            a.pow(241).coefficients,
            (1 << 7) + (1 << 5) + (1 << 4) + (1 << 3)
        );
    }

    #[test]
    fn test_inverse() {
        for x in 1..123 {
            let a = BinaryFieldElement::<X8_X4_X3_X_1>::new(x);
            let a_inv = a.inverse();
            assert_eq!(a * a_inv, BinaryFieldElement::new(1));
        }
    }

    /// Zero does not have a multiplicative inverse.
    #[test]
    #[should_panic(expected = "does not have a multiplicative inverse")]
    fn test_inverse_of_zero() {
        let _inverse = Gf256::zero().inverse();
    }

    /// Every nonzero element of two small binary fields inverts to exactly what the recursive-pow
    /// reference gives, over the bit pattern and not merely up to the field axioms.
    #[test]
    fn test_inverse_is_bit_identical_to_the_reference_exhaustively() {
        fn check<const P: u64>() {
            let order = 1u64 << modulus_degree(P);
            for pattern in 1..order {
                let a = BinaryFieldElement::<P>::new(pattern);
                assert_eq!(
                    a.inverse(),
                    fermat_inverse_via_recursive_pow(&a),
                    "GF(2^{}): {pattern:b}",
                    modulus_degree(P)
                );
            }
        }

        check::<X5_X2_1>();
        check::<X8_X4_X3_X_1>();
    }

    proptest! {
        /// Inversion is bit-identical to the recursive-pow reference over GF(2^63), the widest
        /// binary field and wider than the `Gf256` that `for_each_field!` covers.
        #[test]
        fn test_inverse_is_bit_identical_to_the_reference(a in Gf2Pow63::arbitrary()) {
            if !a.is_zero() {
                assert_eq!(a.inverse(), fermat_inverse_via_recursive_pow(&a));
            }
        }
    }

    #[test]
    fn test_divide() {
        // sage: K.<x> = GF(2^35, name='x', modulus = x^35 + x^2 +1)
        const P: u64 = (1 << 35) + (1 << 2) + 1;

        // sage: a = K.random_element()
        // sage: a
        //   x^33 + x^32 + x^29 + x^25 + x^23 + x^22 + x^21 + x^16 + x^15 + x^13 + x^12 + x^8 + x^7 + x^6 + x^4 + 1
        let a = BinaryFieldElement::<P>::new(0b1100100010111000011011000111010001);

        // sage: b = K.random_element()
        // sage: b
        //   x^32 + x^31 + x^30 + x^29 + x^28 + x^27 + x^20 + x^17 + x^16 + x^15 + x^8 + x^7 + x^3 + x + 1
        let b = BinaryFieldElement::<P>::new(0b111111000000100111000000110001011);

        // sage: a / b
        //   x^29 + x^27 + x^26 + x^23 + x^22 + x^21 + x^17 + x^13 + x^11 + x^10 + x^8 + x^7 + x^6 + x^5
        let expected = BinaryFieldElement::<P>::new(0b101100111000100010110111100000);
        assert_eq!(a / b, expected);
    }

    // The field axioms, checked over arbitrary elements. Each helper is instantiated below for
    // GF(2^5), GF(2^8), and GF(2^63).

    fn addition_is_commutative<F: FiniteField>(a: F, b: F) {
        assert_eq!(a + b, b + a);
    }

    fn addition_is_associative<F: FiniteField>(a: F, b: F, c: F) {
        assert_eq!((a + b) + c, a + (b + c));
    }

    fn zero_is_the_additive_identity<F: FiniteField>(a: F) {
        assert_eq!(a + F::zero(), a);
    }

    fn every_element_is_its_own_additive_inverse<F: FiniteField>(a: F) {
        // GF(2^m) has characteristic 2, so a + a = 0.
        assert_eq!(a + a, F::zero());
    }

    fn multiplication_is_commutative<F: FiniteField>(a: F, b: F) {
        assert_eq!(a * b, b * a);
    }

    fn multiplication_is_associative<F: FiniteField>(a: F, b: F, c: F) {
        assert_eq!((a * b) * c, a * (b * c));
    }

    fn one_is_the_multiplicative_identity<F: FiniteField>(a: F) {
        assert_eq!(a * F::one(), a);
    }

    fn multiplication_distributes_over_addition<F: FiniteField>(a: F, b: F, c: F) {
        assert_eq!(a * (b + c), (a * b) + (a * c));
    }

    fn element_times_its_inverse_is_one<F: FiniteField>(a: F) {
        if a.is_zero() {
            return; // Zero has no multiplicative inverse.
        }
        assert_eq!(a * a.inverse(), F::one());
    }

    fn division_undoes_multiplication<F: FiniteField>(a: F, b: F) {
        if b.is_zero() {
            return; // Division by zero is undefined.
        }
        assert_eq!((a * b) / b, a);
    }

    fn frobenius_fixes_every_element<F: KnownOrder>(a: F) {
        // a^(2^m) = a for every a in GF(2^m), since the multiplicative group has order 2^m - 1.
        assert_eq!(a.pow(F::order_u128().unwrap()), a);
    }

    fn products_stay_within_the_field<const P: u64>(
        a: BinaryFieldElement<P>,
        b: BinaryFieldElement<P>,
    ) {
        // Reduction by the modulus must bring the product's degree back below m.
        let product = a * b;
        assert!((product.coefficients as u128) < BinaryFieldElement::<P>::order_u128().unwrap());
    }

    proptest! {
        #[test]
        fn test_addition_is_commutative_gf32(a in Gf32::arbitrary(), b in Gf32::arbitrary()) {
            addition_is_commutative(a, b);
        }

        #[test]
        fn test_addition_is_commutative_gf256(a in Gf256::arbitrary(), b in Gf256::arbitrary()) {
            addition_is_commutative(a, b);
        }

        #[test]
        fn test_addition_is_commutative_gf2pow63(a in Gf2Pow63::arbitrary(), b in Gf2Pow63::arbitrary()) {
            addition_is_commutative(a, b);
        }

        #[test]
        fn test_addition_is_associative_gf256(a in Gf256::arbitrary(), b in Gf256::arbitrary(), c in Gf256::arbitrary()) {
            addition_is_associative(a, b, c);
        }

        #[test]
        fn test_addition_is_associative_gf2pow63(a in Gf2Pow63::arbitrary(), b in Gf2Pow63::arbitrary(), c in Gf2Pow63::arbitrary()) {
            addition_is_associative(a, b, c);
        }

        #[test]
        fn test_zero_is_the_additive_identity_gf256(a in Gf256::arbitrary()) {
            zero_is_the_additive_identity(a);
        }

        #[test]
        fn test_zero_is_the_additive_identity_gf2pow63(a in Gf2Pow63::arbitrary()) {
            zero_is_the_additive_identity(a);
        }

        #[test]
        fn test_every_element_is_its_own_additive_inverse_gf32(a in Gf32::arbitrary()) {
            every_element_is_its_own_additive_inverse(a);
        }

        #[test]
        fn test_every_element_is_its_own_additive_inverse_gf2pow63(a in Gf2Pow63::arbitrary()) {
            every_element_is_its_own_additive_inverse(a);
        }

        #[test]
        fn test_multiplication_is_commutative_gf32(a in Gf32::arbitrary(), b in Gf32::arbitrary()) {
            multiplication_is_commutative(a, b);
        }

        #[test]
        fn test_multiplication_is_commutative_gf256(a in Gf256::arbitrary(), b in Gf256::arbitrary()) {
            multiplication_is_commutative(a, b);
        }

        #[test]
        fn test_multiplication_is_commutative_gf2pow63(a in Gf2Pow63::arbitrary(), b in Gf2Pow63::arbitrary()) {
            multiplication_is_commutative(a, b);
        }

        #[test]
        fn test_multiplication_is_associative_gf32(a in Gf32::arbitrary(), b in Gf32::arbitrary(), c in Gf32::arbitrary()) {
            multiplication_is_associative(a, b, c);
        }

        #[test]
        fn test_multiplication_is_associative_gf256(a in Gf256::arbitrary(), b in Gf256::arbitrary(), c in Gf256::arbitrary()) {
            multiplication_is_associative(a, b, c);
        }

        #[test]
        fn test_multiplication_is_associative_gf2pow63(a in Gf2Pow63::arbitrary(), b in Gf2Pow63::arbitrary(), c in Gf2Pow63::arbitrary()) {
            multiplication_is_associative(a, b, c);
        }

        #[test]
        fn test_one_is_the_multiplicative_identity_gf256(a in Gf256::arbitrary()) {
            one_is_the_multiplicative_identity(a);
        }

        #[test]
        fn test_one_is_the_multiplicative_identity_gf2pow63(a in Gf2Pow63::arbitrary()) {
            one_is_the_multiplicative_identity(a);
        }

        #[test]
        fn test_multiplication_distributes_over_addition_gf32(a in Gf32::arbitrary(), b in Gf32::arbitrary(), c in Gf32::arbitrary()) {
            multiplication_distributes_over_addition(a, b, c);
        }

        #[test]
        fn test_multiplication_distributes_over_addition_gf256(a in Gf256::arbitrary(), b in Gf256::arbitrary(), c in Gf256::arbitrary()) {
            multiplication_distributes_over_addition(a, b, c);
        }

        #[test]
        fn test_multiplication_distributes_over_addition_gf2pow63(a in Gf2Pow63::arbitrary(), b in Gf2Pow63::arbitrary(), c in Gf2Pow63::arbitrary()) {
            multiplication_distributes_over_addition(a, b, c);
        }

        #[test]
        fn test_element_times_its_inverse_is_one_gf32(a in Gf32::arbitrary()) {
            element_times_its_inverse_is_one(a);
        }

        #[test]
        fn test_element_times_its_inverse_is_one_gf256(a in Gf256::arbitrary()) {
            element_times_its_inverse_is_one(a);
        }

        #[test]
        fn test_element_times_its_inverse_is_one_gf2pow63(a in Gf2Pow63::arbitrary()) {
            element_times_its_inverse_is_one(a);
        }

        #[test]
        fn test_division_undoes_multiplication_gf256(a in Gf256::arbitrary(), b in Gf256::arbitrary()) {
            division_undoes_multiplication(a, b);
        }

        #[test]
        fn test_division_undoes_multiplication_gf2pow63(a in Gf2Pow63::arbitrary(), b in Gf2Pow63::arbitrary()) {
            division_undoes_multiplication(a, b);
        }

        #[test]
        fn test_frobenius_fixes_every_element_gf32(a in Gf32::arbitrary()) {
            frobenius_fixes_every_element(a);
        }

        #[test]
        fn test_frobenius_fixes_every_element_gf256(a in Gf256::arbitrary()) {
            frobenius_fixes_every_element(a);
        }

        #[test]
        fn test_products_stay_within_the_field_gf256(a in Gf256::arbitrary(), b in Gf256::arbitrary()) {
            products_stay_within_the_field(a, b);
        }
    }

    /// The strategy is usable, equal values hash equally, and elements stay below the order.
    #[test]
    fn test_arbitrary_and_representation_are_sound() {
        use crate::identities::{One, Zero};
        use crate::test_support::{
            assert_hash_agrees_with_eq, assert_strategy_is_not_degenerate, draw,
        };
        let strategy = Gf256::arbitrary();
        assert_strategy_is_not_degenerate(&strategy, "BinaryFieldElement");

        let mut values = draw(&strategy, 32);
        values.extend([Gf256::zero(), Gf256::one(), Gf256::default()]);
        assert_hash_agrees_with_eq(&values, "BinaryFieldElement");

        for v in &values {
            assert!(
                (v.coefficients as u128) < Gf256::order_u128().unwrap(),
                "{:?} is not reduced",
                v
            );
        }
    }

    /// A primitive element generates the whole multiplicative group, so its order is q - 1.
    #[test]
    fn test_primitive_element_generates_the_group() {
        use rand::{prelude::StdRng, SeedableRng};
        let mut rng = StdRng::seed_from_u64(13);

        // GF(32) and GF(256) are small enough to enumerate: the powers of a generator must be
        // every nonzero element exactly once, which pins the order to exactly q - 1. The weaker
        // `g^(q-1) == 1` holds for every element and would not distinguish a generator.
        let g = Gf32::primitive_element(&mut rng);
        let mut seen = HashSet::new();
        let mut x = Gf32::one();
        for _ in 0..(Gf32::order_u128().unwrap() - 1) {
            x *= g;
            seen.insert(x);
        }
        assert_eq!(seen.len() as u128, Gf32::order_u128().unwrap() - 1);
        assert!(!seen.contains(&Gf32::zero()));

        let g = Gf256::primitive_element(&mut rng);
        let mut seen = HashSet::new();
        let mut x = Gf256::one();
        for _ in 0..(Gf256::order_u128().unwrap() - 1) {
            x *= g;
            seen.insert(x);
        }
        assert_eq!(seen.len() as u128, Gf256::order_u128().unwrap() - 1);

        // GF(2^63) is far too large to enumerate, so check the order against each prime divisor
        // of q - 1 = 2^63 - 1 = 7^2 * 73 * 127 * 337 * 92737 * 649657.
        let g = Gf2Pow63::primitive_element(&mut rng);
        let group_order = Gf2Pow63::order_u128().unwrap() - 1;
        assert_eq!(g.pow(group_order), Gf2Pow63::one());
        for r in [7u128, 73, 127, 337, 92737, 649657] {
            assert_eq!(group_order % r, 0, "{} should divide {}", r, group_order);
            assert_ne!(g.pow(group_order / r), Gf2Pow63::one(), "r = {}", r);
        }
    }

    /// A primitive nth root of unity satisfies r^n = 1 and r^k != 1 for every 0 < k < n.
    #[test]
    fn test_root_of_unity_is_primitive() {
        use rand::{prelude::StdRng, SeedableRng};
        let mut rng = StdRng::seed_from_u64(31);

        // The group order of GF(256) is 255 = 3 * 5 * 17.
        for n in [3u64, 5, 15, 17, 51, 85, 255] {
            let r = Gf256::root_of_unity(n, &mut rng);
            assert_eq!(r.pow(n as u128), Gf256::one(), "n = {}", n);
            for k in 1..n {
                assert_ne!(r.pow(k as u128), Gf256::one(), "n = {}, k = {}", n, k);
            }
        }

        // The group order of GF(32) is the prime 31, so 31 is the only nontrivial divisor.
        let r = Gf32::root_of_unity(31, &mut rng);
        assert_eq!(r.pow(31), Gf32::one());
        for k in 1..31 {
            assert_ne!(r.pow(k), Gf32::one(), "k = {}", k);
        }
    }

    /// `n` must divide the order of the multiplicative group, and otherwise is an error value.
    #[test]
    fn test_root_of_unity_rejects_n_not_dividing_the_group_order() {
        use rand::{prelude::StdRng, SeedableRng};
        let mut rng = StdRng::seed_from_u64(5);
        // 4 does not divide 255, the group order of GF(256).
        assert_eq!(
            Gf256::try_root_of_unity(4, &mut rng),
            Err(crate::fields::RootOfUnityError::OrderDoesNotDivide { n: 4 })
        );
    }

    /// Rabin's irreducibility test over GF(2), built on the bit-pattern arithmetic above.
    ///
    /// A degree-n polynomial f is irreducible over GF(2) exactly when x^(2^n) = x mod f and
    /// gcd(x^(2^(n/p)) - x, f) = 1 for every prime p dividing n. Trial division is not an option
    /// at degree 63: there are 2^31 monic candidate divisors.
    fn is_irreducible_over_gf2(f: u64) -> bool {
        let n = degree_u64(f);
        const X: u64 = 0b10;

        // x^(2^n) must be x again.
        if x_to_the_2_to_the(n, f) != X {
            return false;
        }
        for p in prime_divisors(n) {
            // Subtraction is XOR in characteristic 2.
            let h = x_to_the_2_to_the(n / p, f) ^ X;
            if h == 0 || gcd_over_gf2(h, f) != 1 {
                return false;
            }
        }
        true
    }

    /// x^(2^k) mod f, by k repeated squarings starting from x.
    fn x_to_the_2_to_the(k: u32, f: u64) -> u64 {
        let mut acc: u64 = 0b10;
        for _ in 0..k {
            acc = long_divide(multiply_polynomials(acc, acc), f).1;
        }
        acc
    }

    /// The monic gcd of two polynomials over GF(2), by the Euclidean algorithm.
    fn gcd_over_gf2(mut a: u64, mut b: u64) -> u64 {
        while b != 0 {
            let remainder = long_divide(a as u128, b).1;
            a = b;
            b = remainder;
        }
        a
    }

    fn prime_divisors(mut n: u32) -> Vec<u32> {
        let mut divisors = Vec::new();
        let mut d = 2;
        while d * d <= n {
            if n.is_multiple_of(d) {
                divisors.push(d);
                while n.is_multiple_of(d) {
                    n /= d;
                }
            }
            d += 1;
        }
        if n > 1 {
            divisors.push(n);
        }
        divisors
    }

    /// Every modulus this crate declares for GF(2^m) really is irreducible.
    ///
    /// `primitive_element` searches until it finds a generator, so a reducible modulus would not
    /// merely give wrong answers — it would not terminate.
    #[test]
    fn test_declared_moduli_are_irreducible() {
        assert!(is_irreducible_over_gf2(X5_X2_1));
        assert!(is_irreducible_over_gf2(X8_X4_X3_X_1));
        assert!(is_irreducible_over_gf2(X8_X4_X3_X2_1));
        assert!(is_irreducible_over_gf2(X63_X_1));
    }

    /// The two degree-eight moduli define different fields: one pair of bytes, two products.
    #[test]
    fn test_the_two_degree_eight_moduli_are_different_fields() {
        type Aes = BinaryFieldElement<X8_X4_X3_X_1>;
        type Mq = BinaryFieldElement<X8_X4_X3_X2_1>;

        // FIPS-197 section 4.2 works this product out by hand: 0x57 * 0x83 = 0xc1 over the AES
        // modulus. Anchoring on a published value rather than on this crate's own output is what
        // makes the inequality below evidence about the moduli instead of about the implementation.
        assert_eq!((Aes::new(0x57) * Aes::new(0x83)).coefficients(), 0xc1);

        // The same bit patterns, reduced modulo x^8 + x^4 + x^3 + x^2 + 1 instead.
        let mq = (Mq::new(0x57) * Mq::new(0x83)).coefficients();
        assert_ne!(
            mq, 0xc1,
            "0x11D must not agree with 0x11B here, or the two moduli would be \
             indistinguishable on this operand pair and the test would be vacuous"
        );

        // Checked against an independent reduction: carry-less multiply, then subtract shifted
        // copies of the modulus bit by bit. The shipped path is PCLMULQDQ plus Barrett reduction,
        // so this shares no code with it.
        assert_eq!(mq, reduce_bitwise(clmul(0x57, 0x83), X8_X4_X3_X2_1));
        // And the same reference reproduces the AES product, so it is not tuned to one modulus.
        assert_eq!(reduce_bitwise(clmul(0x57, 0x83), X8_X4_X3_X_1), 0xc1);

        // Most operand pairs separate the two fields, but not every pair does, which is why one
        // pair cannot characterize the difference: whenever the carry-less product already has
        // degree below 8 there is nothing to reduce and both moduli return it unchanged. Every
        // product by 1 is such a case.
        let differing = (1u64..256)
            .flat_map(|a| (1u64..256).map(move |b| (a, b)))
            .filter(|(a, b)| {
                (Aes::new(*a) * Aes::new(*b)).coefficients()
                    != (Mq::new(*a) * Mq::new(*b)).coefficients()
            })
            .count();
        assert!(
            differing > 50_000,
            "only {differing} of 65025 nonzero operand pairs differ between the two moduli"
        );
    }

    /// Carry-less product of two polynomials over GF(2), by shift and xor.
    fn clmul(a: u64, b: u64) -> u128 {
        let mut product = 0u128;
        for i in 0..64 {
            if b >> i & 1 == 1 {
                product ^= (a as u128) << i;
            }
        }
        product
    }

    /// `value` reduced modulo `modulus` over GF(2), one bit at a time.
    fn reduce_bitwise(mut value: u128, modulus: u64) -> u64 {
        let m = modulus_degree(modulus);
        while degree_u128(value) >= m {
            let shift = degree_u128(value) - m;
            value ^= (modulus as u128) << shift;
        }
        value as u64
    }

    /// The test rejects reducible input, so the certification above is not vacuous.
    #[test]
    fn test_reducible_polynomials_are_rejected() {
        assert!(!is_irreducible_over_gf2(0b100)); // x^2 = x * x
        assert!(!is_irreducible_over_gf2(0b101)); // x^2 + 1 = (x + 1)^2
        assert!(!is_irreducible_over_gf2(0b10001)); // x^4 + 1 = (x + 1)^4
        assert!(!is_irreducible_over_gf2(0b1001)); // x^3 + 1 = (x + 1)(x^2 + x + 1)

        // And it accepts the smallest irreducibles of degree 2 and 3.
        assert!(is_irreducible_over_gf2(0b111)); // x^2 + x + 1
        assert!(is_irreducible_over_gf2(0b1011)); // x^3 + x + 1
        assert!(is_irreducible_over_gf2(0b1101)); // x^3 + x^2 + 1
    }

    /// `roots` works over GF(2^m), which needs the trace-based splitter.
    ///
    /// This test lives here rather than beside `roots` because `BinaryFieldElement` is private to
    /// the `fields` module, so the odd-characteristic path is all that is reachable from there.
    /// Without this, the `(q-1)/2` branch would be the only one exercised with m > 1.
    #[test]
    fn test_univariate_roots_over_gf256() {
        use crate::{identities::One, roots, Polynomial, UnivariatePolynomial};
        use rand::{prelude::StdRng, SeedableRng};

        let mut rng = StdRng::seed_from_u64(41);

        // (x - a)(x - b)(x - c) for three distinct elements, so the roots are known in advance.
        let chosen = [Gf256::new(1), Gf256::new(100), Gf256::new(255)];
        let f = chosen
            .iter()
            .fold(UnivariatePolynomial::<Gf256>::one(), |acc, a| {
                acc * UnivariatePolynomial::new(&[Gf256::zero() - *a, Gf256::one()])
            });
        let expected: HashSet<Gf256> = chosen.into_iter().collect();
        let found: HashSet<Gf256> = roots(&f, &mut rng).into_iter().collect();
        assert_eq!(found, expected);

        // And agree with evaluation at all 256 elements, for polynomials whose roots are not
        // known in advance.
        let all: Vec<Gf256> = (0..256u64).map(Gf256::new).collect();
        let candidates = [
            vec![7u64, 3, 1, 5],
            vec![1, 0, 0, 0, 1],
            vec![0, 1, 1],
            vec![200, 17],
            vec![9, 9, 9, 9, 9, 9],
        ];
        for coefficients in &candidates {
            let g = UnivariatePolynomial::new(
                &coefficients
                    .iter()
                    .map(|c| Gf256::new(*c))
                    .collect::<Vec<_>>(),
            );
            let by_evaluation: HashSet<Gf256> = all
                .iter()
                .copied()
                .filter(|a| g.eval(a).is_zero())
                .collect();
            let by_roots: HashSet<Gf256> = roots(&g, &mut rng).into_iter().collect();
            assert_eq!(by_roots, by_evaluation, "coefficients {:?}", coefficients);
        }
    }

    /// The trace maps GF(2^m) onto GF(2), so evaluating it at a root of g yields 0 or 1.
    ///
    /// Worth testing directly: `roots` accepts a split only after checking the divisor's degree,
    /// so a wrong trace would cost extra attempts rather than produce a wrong answer, and the
    /// root-finding tests cannot tell the two apart. Truncating the trace sum leaves them
    /// passing.
    #[test]
    fn test_trace_maps_into_gf2() {
        use crate::{identities::One, poly::trace_to_gf2, Polynomial, UnivariatePolynomial};
        use rand::{prelude::StdRng, Rng, SeedableRng};

        let mut rng = StdRng::seed_from_u64(43);

        // g = (x - a)(x - b)(x - c), whose roots are known.
        let chosen = [Gf256::new(2), Gf256::new(57), Gf256::new(201)];
        let g = chosen
            .iter()
            .fold(UnivariatePolynomial::<Gf256>::one(), |acc, a| {
                acc * UnivariatePolynomial::new(&[Gf256::zero() - *a, Gf256::one()])
            });

        for _ in 0..32 {
            let coefficients: Vec<Gf256> = (0..g.degree())
                .map(|_| Gf256::new(rng.gen_range(0..256)))
                .collect();
            let h = UnivariatePolynomial::new(&coefficients);
            let t = trace_to_gf2(&h, &g, 1);

            for a in &chosen {
                let value = t.eval(a);
                assert!(
                    value == Gf256::zero() || value == Gf256::one(),
                    "trace evaluated to {} at {}, which is outside GF(2)",
                    value,
                    a
                );
            }
        }
    }

    /// The trace satisfies T^2 = T, because it lands in GF(2) where squaring is the identity.
    ///
    /// Holds for any degree, unlike evaluating at a root: for d > 1 the roots live in
    /// GF(2^(m*d)) and cannot be represented as elements of GF(2^m). This is what catches an
    /// error in the trace at d > 1, since factorization itself cannot — any candidate that
    /// splits is accepted, so a wrong trace merely costs attempts.
    #[test]
    fn test_trace_is_idempotent() {
        use crate::{
            identities::One, is_irreducible, poly::trace_to_gf2, pow_mod, Polynomial,
            UnivariatePolynomial,
        };
        use rand::{prelude::StdRng, Rng, SeedableRng};

        let mut rng = StdRng::seed_from_u64(59);

        // d = 1: a product of distinct linear factors.
        let linear = [Gf256::new(2), Gf256::new(57), Gf256::new(201)]
            .iter()
            .fold(UnivariatePolynomial::<Gf256>::one(), |acc, a| {
                acc * UnivariatePolynomial::new(&[Gf256::zero() - *a, Gf256::one()])
            });

        // d = 2: a product of distinct irreducible quadratics.
        let mut quadratics: Vec<UnivariatePolynomial<Gf256>> = Vec::new();
        for c in 1..80u64 {
            let candidate = UnivariatePolynomial::new(&[Gf256::new(c), Gf256::one(), Gf256::one()]);
            if is_irreducible(&candidate) {
                quadratics.push(candidate);
            }
            if quadratics.len() == 2 {
                break;
            }
        }
        assert_eq!(quadratics.len(), 2);
        let quadratic = &quadratics[0] * &quadratics[1];

        for (g, d) in [(&linear, 1u32), (&quadratic, 2)] {
            for _ in 0..16 {
                let coefficients: Vec<Gf256> = (0..g.degree())
                    .map(|_| Gf256::new(rng.gen_range(0..256)))
                    .collect();
                let h = UnivariatePolynomial::new(&coefficients);
                let t = trace_to_gf2(&h, g, d);
                assert_eq!(
                    pow_mod(&t, 2, g),
                    &t % g,
                    "the trace of {} is not idempotent at d = {}",
                    h,
                    d
                );
            }
        }
    }

    /// Factorization over GF(2^m), which drives the characteristic-two splitter at degree > 1.
    ///
    /// Lives here because `BinaryFieldElement` is private to the `fields` module, so from `poly`
    /// only GF(2) is reachable in characteristic two — and at m = 1 the trace has a single term.
    #[test]
    fn test_factorize_over_gf256() {
        use crate::{factorize, identities::One, is_irreducible, Polynomial, UnivariatePolynomial};
        use rand::{prelude::StdRng, SeedableRng};

        let mut rng = StdRng::seed_from_u64(53);

        // Two distinct irreducible monic quadratics, found rather than assumed.
        let mut quadratics: Vec<UnivariatePolynomial<Gf256>> = Vec::new();
        for c in 1..80u64 {
            let candidate = UnivariatePolynomial::new(&[Gf256::new(c), Gf256::one(), Gf256::one()]);
            if is_irreducible(&candidate) {
                quadratics.push(candidate);
            }
            if quadratics.len() == 2 {
                break;
            }
        }
        assert_eq!(quadratics.len(), 2, "expected two irreducible quadratics");

        // Their product has two degree-two factors, so the splitter has to separate them —
        // the case m = 1 never reaches.
        let f = &quadratics[0] * &quadratics[1];
        let factors = factorize(&f, &mut rng);
        assert_eq!(factors.len(), 2);
        for (factor, multiplicity) in &factors {
            assert_eq!(*multiplicity, 1);
            assert_eq!(factor.degree(), 2);
            assert!(is_irreducible(factor), "{} is not irreducible", factor);
        }

        // With a repeated factor too.
        let g = quadratics[0].pow(3) * quadratics[1].clone();
        let factors = factorize(&g, &mut rng);
        let product = factors
            .iter()
            .fold(UnivariatePolynomial::<Gf256>::one(), |acc, (p, m)| {
                acc * p.pow(*m as u32)
            });
        assert_eq!(product, g);
        assert_eq!(factors.len(), 2);

        // And on polynomials whose factor structure is not known in advance: the product of the
        // factors must reconstruct the input, and each factor must be irreducible. Those two
        // together are complete, factorization being unique up to units.
        let candidates = [
            vec![7u64, 3, 1, 5],
            vec![1, 0, 0, 0, 1],
            vec![200, 17, 99],
            vec![9, 9, 9, 9, 9, 9],
            vec![1, 2, 3, 4, 5, 6, 7],
        ];
        for coefficients in &candidates {
            let p = UnivariatePolynomial::new(
                &coefficients
                    .iter()
                    .map(|c| Gf256::new(*c))
                    .collect::<Vec<_>>(),
            );
            let factors = factorize(&p, &mut rng);
            let product = factors
                .iter()
                .fold(UnivariatePolynomial::<Gf256>::one(), |acc, (g, m)| {
                    acc * g.pow(*m as u32)
                });
            let monic = p.scale(&p.coefficients().last().unwrap().inverse());
            assert_eq!(product, monic, "coefficients {:?}", coefficients);
            for (factor, _) in &factors {
                assert!(is_irreducible(factor), "{} is not irreducible", factor);
            }
        }
    }
}
