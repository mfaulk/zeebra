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

use proptest::{arbitrary::Arbitrary, prelude::BoxedStrategy};
use rand::{CryptoRng, RngCore};
use serde::{Deserialize, Serialize};

use crate::{impl_add_variants, impl_div_variants, impl_mul_variants, impl_sub_variants};

use crate::{
    FiniteField,
    identities::{One, Zero}, Ring,
};

#[derive(Copy, Clone, Hash, Debug, Default, Eq, PartialEq, Serialize, Deserialize)]
/// A binary field GF(2^m), modulo an irreducible polynomial P.
pub struct BinaryFieldElement<const P: u64> {
    /// The i^th bit represents c_i in the polynomial \sum_{i=1}^m c_i * x_i.
    pub coefficients: u64,
}

impl<const P: u64> BinaryFieldElement<P> {
    /// An element in the binary field GF(2^m).
    ///
    /// # Arguments
    /// * `coefficients` - The i^th bit represents c_i in the polynomial \sum_{i=1}^m c_i * x_i.
    pub fn new(coefficients: u64) -> Self {
        // TODO: debug_assert that P is irreducible?
        assert!(coefficients < P);
        Self { coefficients }
    }

    /// (The bit pattern of) this field's modulus, i.e., irreducible polynomial.
    pub fn modulus(&self) -> u64 {
        P
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
    fn new(_val: u64) -> Self {
        todo!()
    }

    fn from_str(_value: &str) -> Result<Self, ()> {
        todo!()
    }

    fn random<R: RngCore + CryptoRng>(rng: &mut R) -> Self {
        // Generate a random m-bit coefficient bit pattern.
        let mask = Self::order() as u64 - 1; // The low-order m bits are set.
        let coefficients = rng.next_u64() & mask;
        Self::new(coefficients)
    }

    fn primitive_element<R: RngCore + CryptoRng>(_rng: &mut R) -> Self {
        todo!()
    }

    fn root_of_unity<R: RngCore + CryptoRng>(_n: u64, _rng: &mut R) -> Self {
        todo!()
    }

    fn order() -> u128 {
        // 2^m where m is determined by the degree of the modulus polynomial.
        let m = 63 - P.leading_zeros();
        2u128.pow(m)
    }

    fn characteristic() -> u128 {
        2
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

        // Divide by an irreducible polynomial, yielding a quotient and a remainder.
        // Product is defined as the remainder.
        let (_quotient, remainder) = long_divide(product, P);
        Self::Output {
            coefficients: remainder,
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
impl<const P: u64> Display for BinaryFieldElement<P> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        // TODO: ???
        write!(f, "{}", self.coefficients)
    }
}

// impl Arbitrary
impl<const P: u64> Arbitrary for BinaryFieldElement<P> {
    type Parameters = ();

    fn arbitrary_with(_args: Self::Parameters) -> Self::Strategy {
        todo!()
    }

    type Strategy = BoxedStrategy<Self>;
}

/// Multiply the coefficient bit patterns for two polynomials in GF(2).
fn multiply_polynomials(a: u64, b: u64) -> u128 {
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

/// Divide dividend by divisor. Return the quotient and remainder.
///
/// # Arguments
/// * `numerator` - Bit pattern of numerator polynomial.
/// * `denominator` - Bit pattern of denominator polynomial.
fn long_divide(numerator: u128, denominator: u64) -> (u64, u64) {
    let denominator = denominator as u128;
    // The numerator will be reduced until it has degree less than m.
    let m = degree_u128(denominator);
    let mut quotient: u64 = 0;
    let mut remainder = numerator;
    while degree_u128(remainder) >= m {
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
    use rand::thread_rng;

    use crate::{
        fields::{
            binary_field::{
                BinaryFieldElement, degree_u128, degree_u64, long_divide, multiply_polynomials,
            },
            irreducible_polynomials::{X5_X2_1, X63_X_1, X8_X4_X3_X_1},
        },
        FiniteField,
    };

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

    #[test]
    fn test_mul_no_reduction() {
        let a = BinaryFieldElement::<X5_X2_1>::new(0b0101); // x^2 + 1
        let b = BinaryFieldElement::<X5_X2_1>::new(0b0100); // x^2
        let prod = a * b;
        assert_eq!(prod.coefficients, 0b10100); // x^4 + x^2
    }

    #[test]
    /// a * b = b * a
    fn test_mul_is_commutative() {
        for a_coefficients in 0..1000 {
            for b_coefficients in 0..1000 {
                let a = BinaryFieldElement::<X63_X_1>::new(a_coefficients);
                let b = BinaryFieldElement::<X63_X_1>::new(b_coefficients);
                assert_eq!(a * b, b * a)
            }
        }
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

        assert_eq!(BinaryFieldElement::<X8_X4_X3_X_1>::order(), 256);
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
}
