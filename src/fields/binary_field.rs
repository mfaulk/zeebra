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

use proptest::{arbitrary::Arbitrary, prelude::BoxedStrategy, strategy::Strategy};
use rand::{CryptoRng, RngCore};
use serde::{Deserialize, Serialize};

use crate::{impl_add_variants, impl_div_variants, impl_mul_variants, impl_sub_variants};

use crate::{
    identities::{One, Zero},
    FiniteField, ParseFieldElementError, Ring,
};

#[derive(Copy, Clone, Hash, Debug, Default, Eq, PartialEq, Serialize, Deserialize)]
/// A binary field GF(2^m), modulo an irreducible polynomial P.
pub struct BinaryFieldElement<const P: u64> {
    /// The i^th bit represents c_i in the polynomial \sum_{i=1}^m c_i * x_i.
    ///
    /// Private so that the bit pattern cannot be set outside the field's order from outside:
    /// `new` asserts `coefficients < P`, and `PartialEq` and `Hash` are derived over this.
    coefficients: u64,
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
    fn new(_val: u64) -> Self {
        todo!()
    }

    fn from_str(_value: &str) -> Result<Self, ParseFieldElementError> {
        todo!()
    }

    fn random<R: RngCore + CryptoRng>(rng: &mut R) -> Self {
        // Generate a random m-bit coefficient bit pattern.
        let mask = Self::order() as u64 - 1; // The low-order m bits are set.
        let coefficients = rng.next_u64() & mask;
        Self::new(coefficients)
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
        // Every bit pattern below the field's order is a distinct element. The modulus has degree
        // m, so it is at least 2^m = order, and `new`'s `coefficients < P` assertion holds.
        (0u64..Self::order() as u64).prop_map(Self::new).boxed()
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
            binary_field::{
                degree_u128, degree_u64, long_divide, multiply_polynomials, BinaryFieldElement,
            },
            irreducible_polynomials::{X5_X2_1, X63_X_1, X8_X4_X3_X_1},
        },
        FiniteField,
    };

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

    fn frobenius_fixes_every_element<F: FiniteField>(a: F) {
        // a^(2^m) = a for every a in GF(2^m), since the multiplicative group has order 2^m - 1.
        assert_eq!(a.pow(F::order()), a);
    }

    fn products_stay_within_the_field<const P: u64>(
        a: BinaryFieldElement<P>,
        b: BinaryFieldElement<P>,
    ) {
        // Reduction by the modulus must bring the product's degree back below m.
        let product = a * b;
        assert!((product.coefficients as u128) < BinaryFieldElement::<P>::order());
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
                (v.coefficients as u128) < Gf256::order(),
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
        for _ in 0..(Gf32::order() - 1) {
            x *= g;
            seen.insert(x);
        }
        assert_eq!(seen.len() as u128, Gf32::order() - 1);
        assert!(!seen.contains(&Gf32::zero()));

        let g = Gf256::primitive_element(&mut rng);
        let mut seen = HashSet::new();
        let mut x = Gf256::one();
        for _ in 0..(Gf256::order() - 1) {
            x *= g;
            seen.insert(x);
        }
        assert_eq!(seen.len() as u128, Gf256::order() - 1);

        // GF(2^63) is far too large to enumerate, so check the order against each prime divisor
        // of q - 1 = 2^63 - 1 = 7^2 * 73 * 127 * 337 * 92737 * 649657.
        let g = Gf2Pow63::primitive_element(&mut rng);
        let group_order = Gf2Pow63::order() - 1;
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

    /// `n` must divide the order of the multiplicative group.
    #[test]
    #[should_panic(expected = "must divide the group order")]
    fn test_root_of_unity_rejects_n_not_dividing_the_group_order() {
        use rand::{prelude::StdRng, SeedableRng};
        let mut rng = StdRng::seed_from_u64(5);
        // 4 does not divide 255, the group order of GF(256).
        let _r = Gf256::root_of_unity(4, &mut rng);
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
        assert!(is_irreducible_over_gf2(X63_X_1));
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
}
