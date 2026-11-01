//! Variable-length signed integer.

use crate::integers::{big_integers::big_uint::BigUInt, FromDecStrErr};
use proptest::{
    arbitrary::Arbitrary,
    prelude::{any, BoxedStrategy, Strategy},
    sample::select,
};
use std::{
    cmp::Ordering,
    fmt::{Display, Formatter},
    ops::{Add, Div, Mul, Neg, Rem, Shl, Shr, Sub},
};

#[derive(Eq, PartialEq, Debug, Default, Clone)]
pub struct BigInt {
    /// Signum of the number (-1 for negative, 0 for zero, 1 for positive).
    signum: i8,

    magnitude: BigUInt,
}

impl BigInt {
    /// A BigInteger from sign-magnitude representation.
    ///
    /// # Arguments
    /// * `signum` - Sign of the number. Must be -1, 0, or 1.
    /// * `magnitude` - Absolute value of the number, in little-endian order.
    ///
    /// # Panics
    /// Panics if `signum` is not -1, 0, or 1.
    /// Panics if `magnitude` is zero and `signum` is not zero.
    pub fn new(mut signum: i8, magnitude: &[u64]) -> Self {
        assert!(signum == -1 || signum == 0 || signum == 1);
        let magnitude = BigUInt::new(magnitude);
        if magnitude.is_zero() {
            signum = 0;
        } else {
            assert_ne!(signum, 0);
        }
        Self { signum, magnitude }
    }

    /// Zero.
    pub fn zero() -> Self {
        Self {
            signum: 0,
            magnitude: BigUInt::zero(),
        }
    }

    /// One.
    pub fn one() -> Self {
        Self {
            signum: 1,
            magnitude: BigUInt::one(),
        }
    }

    /// Integer value of a string of decimal digits.
    pub fn from_dec_str(s: &str) -> Result<BigInt, FromDecStrErr> {
        println!("BigInt::from_dec_str({})", s);
        let mut signum = 0;
        let mut magnitude = BigUInt::zero();

        // if the first character is + or -
        if let Some(c) = s.chars().next() {
            match c {
                '-' => {
                    signum = -1;
                    magnitude = BigUInt::from_dec_str(&s[1..])?;
                }
                '+' => {
                    signum = 1;
                    magnitude = BigUInt::from_dec_str(&s[1..])?;
                }
                _ => {
                    signum = 1;
                    magnitude = BigUInt::from_dec_str(s)?;
                }
            }
        }

        Ok(BigInt::new(signum, magnitude.as_le_words()))
    }

    pub fn to_dec_str(&self) -> String {
        let digits = self.magnitude.to_dec_str();
        if !self.is_zero() && self.signum == -1 {
            format!("-{}", digits)
        } else {
            digits
        }
    }

    pub fn is_negative(&self) -> bool {
        self.signum == -1
    }

    pub fn is_positive(&self) -> bool {
        self.signum == 1
    }

    pub fn is_zero(&self) -> bool {
        self.signum == 0 || self.magnitude.is_zero()
    }

    /// Computes -self.
    pub fn neg(&self) -> Self {
        BigInt {
            signum: self.signum.neg(),
            magnitude: self.magnitude.clone(),
        }
    }
}

impl From<&BigUInt> for BigInt {
    fn from(src: &BigUInt) -> Self {
        Self {
            signum: i8::from(!src.is_zero()),
            magnitude: src.clone(),
        }
    }
}

impl From<BigUInt> for BigInt {
    fn from(src: BigUInt) -> Self {
        Self::from(&src)
    }
}

impl Display for BigInt {
    fn fmt(&self, _f: &mut Formatter<'_>) -> std::fmt::Result {
        todo!()
    }
}

impl Ord for BigInt {
    fn cmp(&self, _other: &Self) -> Ordering {
        todo!()
    }
}

impl PartialOrd for BigInt {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Add<&BigInt> for &BigInt {
    type Output = BigInt;

    fn add(self, rhs: &BigInt) -> Self::Output {
        match (self.signum, rhs.signum) {
            (0, 0) => BigInt::zero(),
            (_, 0) => self.clone(), // a + 0 = a
            (0, _) => rhs.clone(),  // 0 + b = b
            (1, 1) => {
                let magnitude = &self.magnitude + &rhs.magnitude;
                BigInt::from(magnitude)
            }
            (1, -1) => self - &rhs.neg(), // a + (-b) = a - b
            (-1, 1) => rhs - &self.neg(), // (-a) + b = b - a
            (-1, -1) => {
                // (-a) + (-b) = -(a + b)
                let magnitude = &self.magnitude + &rhs.magnitude;
                BigInt::from(magnitude).neg()
            }
            _ => {
                panic!("Signums must be -1, 0, or 1.")
            }
        }
    }
}

impl Add<BigInt> for BigInt {
    type Output = Self;

    fn add(self, rhs: BigInt) -> Self::Output {
        &self + &rhs
    }
}

impl Sub<&BigInt> for &BigInt {
    type Output = BigInt;

    fn sub(self, rhs: &BigInt) -> Self::Output {
        match (self.signum, rhs.signum) {
            (0, 0) => BigInt::zero(),
            (_, 0) => self.clone(), // a - 0 = a
            (0, _) => rhs.neg(),    // 0 - b = -b
            (1, 1) => match (&self.magnitude, &rhs.magnitude) {
                (left, right) if left == right => BigInt::zero(),
                (left, right) if left > right => BigInt::from(left - right),
                (left, right) => BigInt::from(right - left).neg(),
            },
            (1, -1) => self + &rhs.neg(), // a - (-b) = a + b
            (-1, 1) => {
                // (-a) - b = -(a + b)
                let magnitude = &self.magnitude + &rhs.magnitude;
                BigInt::from(magnitude).neg()
            }
            (-1, -1) => {
                // (-a) - (-b) = b - a
                &rhs.neg() - &self.neg()
            }
            _ => {
                panic!("Signums must be -1, 0, or 1.")
            }
        }
    }
}

impl Sub<BigInt> for BigInt {
    type Output = BigInt;

    fn sub(self, rhs: BigInt) -> Self::Output {
        &self - &rhs
    }
}

impl Mul<&BigInt> for &BigInt {
    type Output = BigInt;

    fn mul(self, rhs: &BigInt) -> Self::Output {
        let magnitude = &self.magnitude * &rhs.magnitude;
        let signum = self.signum * rhs.signum;
        debug_assert!(signum == -1 || signum == 0 || signum == 1);
        if signum == -1 {
            BigInt::from(magnitude).neg()
        } else {
            BigInt::from(magnitude)
        }
    }
}

impl Mul<BigInt> for BigInt {
    type Output = BigInt;

    fn mul(self, rhs: BigInt) -> Self::Output {
        &self * &rhs
    }
}

impl Div<&BigInt> for &BigInt {
    type Output = BigInt;

    fn div(self, rhs: &BigInt) -> Self::Output {
        let quotient = &self.magnitude / &rhs.magnitude;
        let signum = self.signum * rhs.signum;
        debug_assert!(signum == -1 || signum == 0 || signum == 1);
        if signum == -1 {
            BigInt::from(quotient).neg()
        } else {
            BigInt::from(quotient)
        }
    }
}

impl Rem<&BigInt> for &BigInt {
    type Output = BigInt;

    fn rem(self, rhs: &BigInt) -> Self::Output {
        let rem = &self.magnitude % &rhs.magnitude;
        // Under truncated division the remainder takes the sign of the dividend alone, which is
        // what makes `a == (a / b) * b + (a % b)` hold for a negative divisor.
        if self.signum == -1 {
            BigInt::from(rem).neg()
        } else {
            BigInt::from(rem)
        }
    }
}

impl Shl<usize> for &BigInt {
    type Output = BigInt;

    fn shl(self, shift: usize) -> Self::Output {
        let magnitude = &self.magnitude << shift;
        if self.signum == -1 {
            BigInt::from(magnitude).neg()
        } else {
            BigInt::from(magnitude)
        }
    }
}

impl Shr<usize> for &BigInt {
    type Output = BigInt;

    fn shr(self, shift: usize) -> Self::Output {
        let magnitude = &self.magnitude >> shift;
        if self.signum == -1 {
            BigInt::from(magnitude).neg()
        } else {
            BigInt::from(magnitude)
        }
    }
}

impl Arbitrary for BigInt {
    type Parameters = ();

    fn arbitrary_with(_args: Self::Parameters) -> Self::Strategy {
        (any::<BigUInt>(), select(vec![-1, 0, 1]))
            .prop_filter(
                "Signum must be nonzero if magnitude is non-zero",
                |(magnitude, signum)| magnitude.is_zero() || *signum != 0,
            )
            .prop_map(|(magnitude, signum)| BigInt::new(signum, magnitude.as_le_words()))
            .boxed()
    }

    type Strategy = BoxedStrategy<Self>;
}

#[cfg(test)]
mod tests {
    use crate::integers::big_integers::{big_int::BigInt, big_uint::BigUInt};
    use proptest::{prelude::*, sample::select};

    #[test]
    // Zero should have a signum of 0.
    fn test_zero_signum() {
        let zero = BigInt::zero();
        assert_eq!(zero.signum, 0);
    }

    #[test]
    // New should correctly set the signum to -1, 0, or 1.
    fn test_new_signum() {
        let zero_int = BigInt::new(0, &[]);
        assert_eq!(zero_int.signum, 0);
        assert_eq!(zero_int.magnitude, BigUInt::zero());

        let positive_int = BigInt::new(1, &[2]);
        assert_eq!(positive_int.signum, 1);
        assert_eq!(positive_int.magnitude, BigUInt::new(&[2]));
    }

    fn from_and_to_str(mut s: &str) {
        let s2 = BigInt::from_dec_str(s).unwrap().to_dec_str();
        // Standardize various versions of input zeros
        if s.is_empty() || s == "-0" || s == "+0" {
            s = "0"
        }

        // BigInt does not display "+" for positive numbers.
        if s.starts_with('+') {
            s = &s[1..];
        }

        assert_eq!(s, s2);
    }

    proptest! {
        #[test]
        fn test_from_dec_str(digits in "[0-9]{1,20}", signum in select(vec!["+", "-", ""])) { // Regex for numerical strings up to 20 digits long.
            println!("digits: {}", digits);
            let mut digits_trimmed = digits.trim_start_matches('0');
            if digits_trimmed.is_empty() {
                digits_trimmed = "0";
            }
            from_and_to_str(&(signum.to_owned() + digits_trimmed));
        }
    }

    #[test]
    // Spot check a few values against Sage.
    fn test_add_spotcheck() {
        // sage:  -123412341234879879287349 + 9879879872387429871097651026509182659178625
        // 9879879872387429870974238685274302779891276

        let a = BigInt::from_dec_str("-123412341234879879287349").unwrap();
        let b = BigInt::from_dec_str("9879879872387429871097651026509182659178625").unwrap();
        let c = BigInt::from_dec_str("9879879872387429870974238685274302779891276").unwrap();
        assert_eq!(a + b, c);
    }

    // a + b = b + a
    fn add_is_commutative(a: &BigInt, b: &BigInt) {
        assert_eq!(a + b, b + a);
    }

    proptest! {
        #[test]
        fn test_add_is_commutative(a in any::<BigInt>(), b in any::<BigInt>()) {
            add_is_commutative(&a, &b);
        }
    }

    #[test]
    // Spot check a few values against Sage.
    fn test_sub_spotcheck() {
        // sage:  123412341234879879287349 - 9879879872387429871097651026509182659178625
        // -9879879872387429870974238685274302779891276
        let a = BigInt::from_dec_str("123412341234879879287349").unwrap();
        let b = BigInt::from_dec_str("9879879872387429871097651026509182659178625").unwrap();
        let c = BigInt::from_dec_str("-9879879872387429870974238685274302779891276").unwrap();
        assert_eq!(a - b, c);
    }

    #[test]
    // Spot check a few values against Sage.
    fn test_mul_spotcheck() {
        // sage:  -123412341234879879287349 * 9879879872387429871097651026509182659178625
        //     -1219299106170698971165357923477608746286580788604285807318693715125

        let a = BigInt::from_dec_str("-123412341234879879287349").unwrap();
        let b = BigInt::from_dec_str("9879879872387429871097651026509182659178625").unwrap();
        let c = BigInt::from_dec_str(
            "-1219299106170698971165357923477608746286580788604285807318693715125",
        )
        .unwrap();
        assert_eq!(a * b, c);
    }

    // a * b = b * a
    fn mul_is_commutative(a: &BigInt, b: &BigInt) {
        assert_eq!(a * b, b * a);
    }

    proptest! {
        #[test]
        fn test_mul_is_commutative(a in any::<BigInt>(), b in any::<BigInt>()) {
            mul_is_commutative(&a, &b);
        }
    }

    // (a * b) / b = 1
    fn mul_then_divide(a: BigInt, b: BigInt) -> Result<(), TestCaseError> {
        let c = &a * &b;
        let d = &c / &b;
        prop_assert_eq!(d, a);
        Ok(())
    }

    proptest! {
        #[test]
        // Multiplying than dividing by a non-zero number is the identity function.
        fn test_mul_then_divide(a in any::<BigInt>(), b in any::<BigInt>().prop_filter("b != 0", |b| !b.is_zero())) {
            mul_then_divide(a, b)?
        }
    }

    /// Division truncates toward zero; the quotient's sign is the product of the operands' signs.
    #[test]
    fn test_div() {
        let magnitude = BigInt::from_dec_str("1361129467683753853853498429727072845824").unwrap(); // 2^130
        let divisor = BigInt::from_dec_str("3486784401").unwrap(); // 3^20
        let quotient = BigInt::from_dec_str("390368118915923145387932584629").unwrap();

        assert_eq!(&magnitude / &divisor, quotient);
        assert_eq!(&magnitude.neg() / &divisor, quotient.neg());
        assert_eq!(&magnitude / &divisor.neg(), quotient.neg());
        assert_eq!(&magnitude.neg() / &divisor.neg(), quotient);

        // A dividend smaller in magnitude than the divisor truncates to zero, without a sign.
        assert_eq!(&divisor / &magnitude, BigInt::zero());
        assert_eq!(&divisor.neg() / &magnitude, BigInt::zero());
    }

    /// The remainder takes the sign of the dividend, so a = (a / b) * b + (a % b) always holds.
    #[test]
    fn test_rem() {
        let magnitude = BigInt::from_dec_str("1361129467683753853853498429727072845824").unwrap(); // 2^130
        let divisor = BigInt::from_dec_str("3486784401").unwrap(); // 3^20
        let remainder = BigInt::from_dec_str("3063273595").unwrap();

        // The sign of the divisor does not affect the remainder.
        assert_eq!(&magnitude % &divisor, remainder);
        assert_eq!(&magnitude % &divisor.neg(), remainder);
        assert_eq!(&magnitude.neg() % &divisor, remainder.neg());
        assert_eq!(&magnitude.neg() % &divisor.neg(), remainder.neg());

        // Truncated division's defining identity, over every sign combination.
        for a in [magnitude.clone(), magnitude.neg()] {
            for b in [divisor.clone(), divisor.neg()] {
                let recovered = &(&(&a / &b) * &b) + &(&a % &b);
                assert_eq!(recovered, a, "a = {:?}, b = {:?}", a, b);
            }
        }
    }

    /// Shifting left by k multiplies the magnitude by 2^k and preserves the sign.
    #[test]
    fn test_shift_left() {
        let a = BigInt::from_dec_str("1267650600228229401496703205507").unwrap(); // 2^100+2^7+3
        let expected = BigInt::from_dec_str("174224571863520493293247799023069827170304").unwrap();

        assert_eq!(&a << 37, expected);
        assert_eq!(&a.neg() << 37, expected.neg());
        assert_eq!(&a << 0, a);
        assert_eq!(&BigInt::zero() << 64, BigInt::zero());
    }

    /// Shifting right by k divides the magnitude by 2^k and preserves the sign.
    #[test]
    fn test_shift_right() {
        let a = BigInt::from_dec_str("1267650600228229401496703205507").unwrap(); // 2^100+2^7+3
        let expected = BigInt::from_dec_str("9903520314283042199192993793").unwrap();

        assert_eq!(&a >> 7, expected);
        assert_eq!(&a.neg() >> 7, expected.neg());
        assert_eq!(&a >> 0, a);
        // Shifting past the width of the value leaves zero, which is unsigned.
        assert_eq!(&a >> 200, BigInt::zero());
        assert_eq!(&a.neg() >> 200, BigInt::zero());
    }
}
