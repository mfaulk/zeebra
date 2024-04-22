//! Variable-length signed integer.

use crate::integers::{
    big_integers::{
        multi_word_cmp::multi_word_cmp,
        multi_word_shift::{shift_left, shift_right},
    },
    multi_word_add, multi_word_div, multi_word_mul, multi_word_sub, num_digits,
    ux64::Ux64,
    FromDecStrErr,
};
use proptest::{
    arbitrary::{any, Arbitrary},
    collection::vec,
    prelude::{BoxedStrategy, Strategy},
};
use rand::Rng;
use std::{
    cmp::Ordering,
    fmt::{Display, Formatter},
    ops::{Add, Div, Mul, Rem, Shl, Shr, Sub},
};

lazy_static! {
    pub static ref ZERO: BigUInt = BigUInt::zero();
    pub static ref ONE: BigUInt = BigUInt::one();
    pub static ref TWO: BigUInt = BigUInt::new_from_u64(2);
}

#[derive(Default, Debug, Clone, Hash)]
pub struct BigUInt {
    // The integer's words, in little-endian order. An empty vector is also interpreted as 0.
    words: Vec<u64>,
}

impl BigUInt {
    /// A BigUInt
    pub fn new(words: &[u64]) -> Self {
        // Ignore higher-order zero digits.
        let words = &words[0..num_digits(words)];
        Self {
            words: words.into(),
        }
    }

    pub fn new_from_u64(value: u64) -> Self {
        Self { words: vec![value] }
    }

    pub fn new_from_u128(value: u128) -> Self {
        let low = value as u64;
        let hi = (value >> 64) as u64;
        Self {
            words: vec![low, hi],
        }
    }

    /// Randomly sample a value in the range [low,high].
    pub fn sample_inclusive<R: Rng>(low: &BigUInt, high: &BigUInt, rng: &mut R) -> Self {
        assert!(low <= high);
        let width = high - low;
        if width.is_zero() {
            return low.clone();
        }
        let num_words = width.words.len();
        let mut words: Vec<u64> = Vec::with_capacity(num_words);
        // Uniformly sample the lower words.
        for _i in 0..(num_words - 1) {
            words.push(rng.next_u64());
        }

        // Sample the last word.
        let high_word = width.words.last().unwrap();
        words.push(rng.gen_range(0..=*high_word));

        let sampled = BigUInt::new(&words);
        sampled + low
    }

    /// Zero.
    pub fn zero() -> Self {
        Self { words: vec![] }
    }

    /// One.
    pub fn one() -> Self {
        Self { words: vec![1] }
    }

    /// Integer value of a string of decimal digits.
    pub fn from_dec_str(value: &str) -> Result<BigUInt, FromDecStrErr> {
        let mut words = vec![0u64; 1];
        for b in value.bytes().map(|b| b.wrapping_sub(b'0')) {
            if b > 9 {
                return Err(FromDecStrErr::InvalidCharacter(b));
            }

            words = multi_word_mul(&words, &[10u64]);
            words = multi_word_add(&words, &[b as u64]);
        }
        Ok(Self { words })
    }

    /// Convert to UTF-8 bytes of a decimal string.
    pub fn to_dec_str(&self) -> String {
        if self.is_zero() {
            return String::from("0");
        }

        let mut result = String::new();
        let mut remainder = self.clone();

        let ten = BigUInt::new_from_u64(10);
        while !remainder.is_zero() {
            let digit = &remainder % &ten;
            remainder = &remainder / &ten;

            if digit.is_zero() {
                let c: u8 = 0;
                result.push_str(&c.to_string());
            } else {
                let words = digit.as_le_words();
                let c = words[0] as u8;
                assert!(c < 10);
                result.push_str(&c.to_string());
            }
        }

        result.chars().rev().collect()
    }

    pub fn is_zero(&self) -> bool {
        self.words == vec![0] || self.words == vec![]
    }

    pub fn is_one(&self) -> bool {
        *self == *ONE
    }

    /// x^n
    pub fn pow(&self, n: &BigUInt) -> BigUInt {
        if self.is_zero() {
            return Self::zero();
        }

        if n.is_zero() {
            return Self::one();
        }

        // Exponentiation by squaring.
        if *n == *ONE {
            self.clone()
        } else if n % &TWO == *ZERO {
            // n is even: a^n = a^(n/2) * a^(n/2)
            let y = self.pow(&(n / &TWO));
            &y * &y
        } else {
            // n is odd: a^n = a * a^(n-1)
            self * &self.pow(&(n - &ONE))
        }
    }

    /// x^n (mod p).
    pub fn pow_mod_p(&self, n: &BigUInt, p: &BigUInt) -> BigUInt {
        if self.is_zero() {
            return Self::zero();
        }

        if n.is_zero() {
            return Self::one();
        }

        // Modular exponentiation by squaring.
        if *n == *ONE {
            self % p
        } else if n % &TWO == *ZERO {
            // n is even: a^n = a^(n/2) * a^(n/2)
            let y = self.pow_mod_p(&(n / &TWO), p);
            (&y * &y) % p
        } else {
            // n is odd: a^n = a * a^(n-1)
            (self * &self.pow_mod_p(&(n - &ONE), p)) % p
        }
    }

    /// The greatest common divisor of a and b, not both zero.
    pub fn gcd(&self, b: &Self) -> Self {
        let mut a = self.clone();
        let mut b = b.clone();
        assert!(!a.is_zero() || !b.is_zero(), "a and b may not both be zero");
        if a.is_zero() {
            return b;
        }
        while !b.is_zero() {
            // If a = qb + r, then gcd(a,b) = gcd(b,r)
            let temp = b.clone();
            b = a % &b;
            a = temp;
        }
        a
    }

    /// The integer's words, in little-endian order. An empty vector is also interpreted as 0.
    pub fn as_le_words(&self) -> &[u64] {
        &self.words
    }

    /// The integer's words, in big-endian order. An empty vector is also interpreted as 0.
    pub fn as_be_words(&self) -> &[u64] {
        todo!()
    }
}

impl<const N_WORDS: usize> From<Ux64<N_WORDS>> for BigUInt {
    fn from(src: Ux64<N_WORDS>) -> Self {
        BigUInt::new(&src.words)
    }
}

impl PartialEq for BigUInt {
    fn eq(&self, other: &Self) -> bool {
        // Zero can be represented as [0] or as the empty list of words [].
        if self.is_zero() && other.is_zero() {
            return true;
        }
        self.words == other.words
    }
}

impl Eq for BigUInt {}

impl Display for BigUInt {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let s = self.to_dec_str();
        f.pad_integral(true, "0x", &s)
    }
}

impl Ord for BigUInt {
    fn cmp(&self, other: &Self) -> Ordering {
        multi_word_cmp(&self.words, &other.words)
    }
}

impl PartialOrd for BigUInt {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

// Borrowed + Borrowed
impl Add<&BigUInt> for &BigUInt {
    type Output = BigUInt;

    fn add(self, rhs: &BigUInt) -> Self::Output {
        let words = multi_word_add(&self.words, &rhs.words);
        BigUInt::new(&words)
    }
}

// Owned + Borrowed
impl Add<&BigUInt> for BigUInt {
    type Output = BigUInt;

    fn add(self, rhs: &BigUInt) -> Self::Output {
        &self + rhs
    }
}

// Owned + Owned
impl Add<BigUInt> for BigUInt {
    type Output = BigUInt;

    fn add(self, rhs: BigUInt) -> Self::Output {
        &self + &rhs
    }
}

impl Sub<&BigUInt> for BigUInt {
    type Output = BigUInt;

    fn sub(self, rhs: &BigUInt) -> Self::Output {
        &self - rhs
    }
}

impl Sub<&BigUInt> for &BigUInt {
    type Output = BigUInt;

    fn sub(self, rhs: &BigUInt) -> Self::Output {
        let (words, borrow) = multi_word_sub(&self.words, &rhs.words);
        assert!(!borrow);
        BigUInt::new(&words)
    }
}

impl Mul<&BigUInt> for BigUInt {
    type Output = BigUInt;

    fn mul(self, rhs: &BigUInt) -> Self::Output {
        &self * rhs
    }
}

impl Mul<&BigUInt> for &BigUInt {
    type Output = BigUInt;

    fn mul(self, rhs: &BigUInt) -> Self::Output {
        let words = multi_word_mul(&self.words, &rhs.words);
        BigUInt::new(&words)
    }
}

impl Div<&BigUInt> for BigUInt {
    type Output = BigUInt;

    fn div(self, rhs: &BigUInt) -> Self::Output {
        &self / rhs
    }
}

impl Div<&BigUInt> for &BigUInt {
    type Output = BigUInt;

    fn div(self, rhs: &BigUInt) -> Self::Output {
        let (quotient, _remainder) = multi_word_div(&self.words, &rhs.words);
        BigUInt::new(&quotient)
    }
}

impl Rem<&BigUInt> for BigUInt {
    type Output = BigUInt;

    fn rem(self, rhs: &BigUInt) -> Self::Output {
        &self % rhs
    }
}

impl Rem<&BigUInt> for &BigUInt {
    type Output = BigUInt;

    fn rem(self, rhs: &BigUInt) -> Self::Output {
        let (_quotient, remainder) = multi_word_div(&self.words, &rhs.words);
        BigUInt::new(&remainder)
    }
}

impl Shl<usize> for &BigUInt {
    type Output = BigUInt;

    fn shl(self, shift: usize) -> Self::Output {
        let words = shift_left(&self.words, shift as u32);
        BigUInt::new(&words)
    }
}

impl Shr<usize> for &BigUInt {
    type Output = BigUInt;

    fn shr(self, shift: usize) -> Self::Output {
        let words = shift_right(&self.words, shift as u32);
        BigUInt { words }
    }
}

impl Arbitrary for BigUInt {
    type Parameters = ();

    fn arbitrary_with(_args: Self::Parameters) -> Self::Strategy {
        const MAX_WORDS: usize = 16;
        vec(any::<u64>(), 0..=MAX_WORDS)
            .prop_map(|values| BigUInt::new(&values))
            .boxed()
    }

    type Strategy = BoxedStrategy<Self>;
}

#[cfg(test)]
mod tests {
    use crate::integers::big_integers::big_uint::{BigUInt, ONE, TWO};
    use proptest::prelude::*;
    use rand::{rngs::StdRng, SeedableRng};

    #[test]
    fn test_zero() {
        // The empty list of words is zero.
        assert!(BigUInt::new(&[]).is_zero());
        // The single word 0 is zero.
        assert!(BigUInt::new(&[0]).is_zero());
        // Higher-order zero words are ignored.
        assert!(BigUInt::new(&[0, 0]).is_zero());
    }

    #[test]
    fn test_to_dec_str() {
        assert_eq!(BigUInt::zero().to_dec_str(), "0");
        assert_eq!(BigUInt::one().to_dec_str(), "1");
        assert_eq!(BigUInt::new_from_u64(1234).to_dec_str(), "1234");
    }

    fn from_and_to_str(s: &str) {
        let s2 = BigUInt::from_dec_str(s).unwrap().to_dec_str();
        // Trim leading zeros from s.
        let mut s_trimmed = s.trim_start_matches('0');
        if s_trimmed.len() == 0 {
            s_trimmed = "0";
        }
        assert_eq!(s_trimmed, s2);
    }

    proptest! {
        #[test]
        fn test_from_dec_str(s in "[0-9]{0,20}") { // Regex for numerical strings up to 20 digits long.
            from_and_to_str(&s);
        }
    }

    fn order_is_symmetric(a: &BigUInt, b: &BigUInt) -> Result<(), TestCaseError> {
        prop_assert_eq!(a.cmp(b), b.cmp(a).reverse());
        Ok(())
    }

    proptest! {
        #[test]
        fn test_cmp_symmetric(a in any::<BigUInt>(), b in any::<BigUInt>()) {
            order_is_symmetric(&a, &b)?;
        }
    }

    #[test]
    // Spot check a few values against Sage.
    fn test_add_spotcheck() {
        // sage: 123412341234879879287349 + 9879879872387429871097651026509182659178625
        // 9879879872387429871221063367744062538465974

        let a = BigUInt::from_dec_str("123412341234879879287349").unwrap();
        let b = BigUInt::from_dec_str("9879879872387429871097651026509182659178625").unwrap();
        let c = BigUInt::from_dec_str("9879879872387429871221063367744062538465974").unwrap();
        assert_eq!(a + b, c);
    }

    // a + b = b + a
    fn add_is_commutative(a: &BigUInt, b: &BigUInt) {
        assert_eq!(a + b, b + a);
    }

    proptest! {
        #[test]
        fn test_add_is_commutative(a in any::<BigUInt>(), b in any::<BigUInt>()) {
            add_is_commutative(&a, &b);
        }
    }

    #[test]
    #[ignore]
    // Spot check a few values against Sage.
    fn test_sub_spotcheck() {
        todo!()
    }

    // (a + b) - b = a
    fn add_then_subtract(a: &BigUInt, b: &BigUInt) {
        let c = a + b;
        let d = &c - b;
        assert_eq!(d, *a);
    }

    proptest! {
        #[test]
        // Add then subtract is the identity function.
        fn test_add_then_subtract(a in any::<BigUInt>(), b in any::<BigUInt>()) {
            add_then_subtract(&a, &b);
        }
    }

    #[test]
    #[ignore]
    // Spot check a few values against Sage.
    fn test_mul_spotcheck() {
        todo!()
    }

    // a * b = b * a
    fn mul_is_commutative(a: &BigUInt, b: &BigUInt) {
        assert_eq!(a * b, b * a);
    }

    proptest! {
        #[test]
        fn test_mul_is_commutative(a in any::<BigUInt>(), b in any::<BigUInt>()) {
            mul_is_commutative(&a, &b);
        }
    }

    // (a * b) / b = 1
    fn mul_then_divide(a: BigUInt, b: BigUInt) -> Result<(), TestCaseError> {
        let c = &a * &b;
        let d = &c / &b;
        prop_assert_eq!(d, a);
        Ok(())
    }

    proptest! {
        #[test]
        // Multiplying than dividing by a non-zero number is the identity function.
        fn test_mul_then_divide(a in any::<BigUInt>(), b in any::<BigUInt>().prop_filter("b != 0", |b| !b.is_zero())) {
            mul_then_divide(a, b)?
        }
    }

    #[test]
    fn test_pow() {
        let zero = BigUInt::zero();
        // 0^0 is undefined.

        // 0^1 = 0
        assert_eq!(zero.pow(&ONE), zero);

        // n^0 = 1
        let twelve = BigUInt::new_from_u64(12);
        assert_eq!(twelve.pow(&zero), *ONE);

        let x = BigUInt::from_dec_str("1827736739876791827398").unwrap();
        assert_eq!(x.pow(&ONE), x);

        assert_eq!(
            x.pow(&TWO),
            BigUInt::from_dec_str("3340621590295443392549306658835924223450404").unwrap()
        );

        assert_eq!(
            x.pow(&BigUInt::new_from_u64(3)),
            BigUInt::from_dec_str(
                "6105776814608617461657521324197728919438988478521889807981368792"
            )
            .unwrap()
        );

        let expected = BigUInt::from_dec_str("51813812898308257351053623420465676002365693702507278033976508628001433463753973209625878961440530940450056289336892891832807568039641901397346439639638436919268642308995887913573837332783847806760204207754830834034272870866846844324020091874256413141750348697649315894043837525475807936094027355124286884246856578854568367415579572191059798071405856197151657543747458438823516831744").unwrap();
        assert_eq!(x.pow(&BigUInt::new_from_u64(18)), expected);
    }

    #[test]
    #[ignore]
    fn test_div() {
        todo!()
    }

    #[test]
    #[ignore]
    fn test_rem() {
        todo!()
    }

    proptest! {
        #[test]
        // gcd(a,b) = gcd(b,a)
        fn test_gcd_is_symmetric(a in any::<BigUInt>(), b in any::<BigUInt>().prop_filter("b != 0", |b| !b.is_zero())) {
            assert_eq!(a.gcd(&b), b.gcd(&a))
        }
    }

    #[test]
    #[ignore]
    fn test_gcd_divides_a_and_b() {
        todo!()
    }

    #[test]
    // Spot-check a few values against Sage.
    fn test_gcd_spotchecks() {
        assert_eq!(
            BigUInt::new_from_u64(19).gcd(&BigUInt::zero()),
            BigUInt::new_from_u64(19)
        );

        let a = BigUInt::new_from_u64(515);
        let b = BigUInt::new_from_u64(2005);
        assert_eq!(a.gcd(&b), BigUInt::new_from_u64(5));
    }

    #[test]
    #[ignore]
    fn test_shift_left() {
        todo!()
    }

    #[test]
    #[ignore]
    fn test_shift_right() {
        todo!()
    }

    #[test]
    // Sampling from [x,x] should return x.
    fn test_sample_inclusive_empty_range() {
        let mut rng = StdRng::seed_from_u64(1);
        let x = BigUInt::new_from_u64(1827);
        let sample = BigUInt::sample_inclusive(&x, &x, &mut rng);
        assert_eq!(sample, x);
    }

    #[test]
    // Sampling from [low,high] should return a value in [low,high].
    fn test_sample_inclusive() {
        let mut rng = StdRng::seed_from_u64(2);
        // These are single-word integers.
        let low = BigUInt::new_from_u64(1827);
        let high = BigUInt::new_from_u64(2827);
        for _i in 0..100 {
            let sample = BigUInt::sample_inclusive(&low, &high, &mut rng);
            assert!(low <= sample);
            assert!(sample <= high);
        }
    }

    #[test]
    // Sampling from [low,high] should return a value in [low,high].
    fn test_sample_inclusive_multi_word_integers() {
        let mut rng = StdRng::seed_from_u64(3);
        // These are single-word integers.
        let low = BigUInt::from_dec_str("3340621590295443392549306658835924223450404").unwrap();
        let high = BigUInt::from_dec_str(
            "6105776814608617461657521324197728919438988478521889807981368792",
        )
        .unwrap();

        for _i in 0..100 {
            let sample = BigUInt::sample_inclusive(&low, &high, &mut rng);
            assert!(low <= sample);
            assert!(sample <= high);
        }
    }

    #[ignore]
    #[test]
    // sample_inclusive should uniformly sample from the given range.
    fn test_sample_inclusive_distribution() {
        unimplemented!()
    }

    #[test]
    #[should_panic]
    // Should panic if low is greater than high.
    fn test_sample_inclusive_should_panic() {
        let mut rng = StdRng::seed_from_u64(5);
        let low = BigUInt::new_from_u64(19880);
        let high = BigUInt::new_from_u64(14);
        let _sample = BigUInt::sample_inclusive(&low, &high, &mut rng);
    }
}
