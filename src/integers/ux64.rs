//! An (N*64)-bit unsigned integer.

use crate::integers::{
    big_integers::big_uint::BigUInt, from_dec_str, multi_word_div, utils::split_u128, FromDecStrErr,
};
use rand::{CryptoRng, RngCore};
use std::{
    cmp::Ordering,
    fmt::{Display, Formatter},
    ops::{Add, Div, Mul, Rem, Sub},
    str::FromStr,
};

/// An (N*64)-bit unsigned integer. N must be 2 or greater.
#[derive(Eq, PartialEq, Debug, Copy, Clone)]
pub struct Ux64<const N_WORDS: usize> {
    // Little-endian
    pub words: [u64; N_WORDS],
}

impl<const N: usize> Default for Ux64<N> {
    fn default() -> Self {
        Self { words: [0u64; N] }
    }
}

impl<const N_WORDS: usize> Ux64<N_WORDS> {
    pub const fn new(words: [u64; N_WORDS]) -> Self {
        Self { words }
    }

    pub const fn new_from_u128(value: u128) -> Self {
        let (low, high) = split_u128(value);
        let mut words = [0u64; N_WORDS];
        words[0] = low;
        words[1] = high;
        Self { words }
    }

    /// Zero.
    pub const fn zero() -> Self {
        Self {
            words: [0u64; N_WORDS],
        }
    }

    /// One.
    pub const fn one() -> Self {
        let mut words = [0u64; N_WORDS];
        words[0] = 1;
        Self { words }
    }

    pub const fn max() -> Self {
        Self {
            words: [u64::MAX; N_WORDS],
        }
    }

    /// The greatest common divisor of a and b, not both zero.
    pub fn gcd(mut a: Self, mut b: Self) -> Self {
        assert!(!a.is_zero() || !b.is_zero(), "a and b may not both be zero");
        if a.is_zero() {
            return b;
        }
        while !b.is_zero() {
            // If a = qb + r, then gcd(a,b) = gcd(b,r)
            (a, b) = (b, a % b)
        }
        a
    }

    pub fn random<R: RngCore + CryptoRng>(rng: &mut R) -> Self {
        let mut words = [0u64; N_WORDS];
        for word in words.iter_mut() {
            *word = rng.next_u64()
        }
        Self { words }
    }

    /// Convert from a decimal string.
    pub fn from_dec_str(value: &str) -> Result<Self, FromDecStrErr> {
        // A variable-length integer.
        let x = from_dec_str(value)?;
        if x.len() > N_WORDS {
            return Err(FromDecStrErr::InvalidLength);
        }

        let mut words = [0u64; N_WORDS];
        for (i, word) in words.iter_mut().enumerate() {
            *word = *x.get(i).unwrap_or(&0u64);
        }
        Ok(Self { words })
    }

    pub fn as_64_bit_words(&self) -> [u64; N_WORDS] {
        self.words
    }

    /// Cast as u64, discarding higher words.
    pub fn as_u64(&self) -> u64 {
        self.words[0]
    }

    /// Cast as u128, discarding higher words.
    pub fn as_u128(&self) -> u128 {
        self.words[0] as u128 + ((self.words[1] as u128) << 64)
    }

    pub fn is_zero(&self) -> bool {
        self.words == [0u64; N_WORDS]
    }

    pub fn is_one(&self) -> bool {
        *self == Self::one()
    }

    /// Calculates self + rhs + carry without the ability to overflow.
    ///
    /// Performs “ternary addition” which takes in an extra bit to add, and may return an additional
    /// bit of overflow. This allows for chaining together multiple additions to create
    /// “big integers” which represent larger values.
    pub fn carrying_add(self, rhs: Self, mut carry: bool) -> (Self, bool) {
        let mut result = [0u64; N_WORDS];

        for i in 0..N_WORDS {
            let a = self.words[i];
            let b = rhs.words[i];
            let (sum, c) = a.carrying_add(b, carry);
            result[i] = sum;
            carry = c;
        }

        (Self { words: result }, carry)
    }

    /// Calculates self - rhs - borrow without the ability to overflow.
    ///
    /// Performs “ternary subtraction” which takes in an extra bit to subtract, and may return an
    /// additional bit of overflow. If an overflow occurred, then the wrapped value is returned.
    pub fn borrowing_sub(self, rhs: Self, mut borrow: bool) -> (Self, bool) {
        let mut result = [0u64; N_WORDS];

        for i in 0..N_WORDS {
            let a = self.words[i];
            let b = rhs.words[i];
            let (diff, borrowed) = a.borrowing_sub(b, borrow);
            result[i] = diff;
            borrow = borrowed;
        }

        (Self { words: result }, borrow)
    }

    /// Calculates self * rhs + carry without the ability to overflow.
    ///
    /// Performs "multi-digit" multiplication in base-256, returning (low,high).
    pub fn carrying_mul(self, rhs: Self, _carry_in: Self) -> (Self, Self) {
        // See Knuth, TAOCP, Volume 2, section 4.3.1.
        // Multiplying an m-place integer by an n-place integer yields an (m+n)-place product.
        let mut product = vec![0u64; 2 * N_WORDS]; // TODO: initialize with carry_in.
        for (i, a) in self.words.into_iter().enumerate() {
            let mut carry: u64 = 0;
            for (j, b) in rhs.as_64_bit_words().into_iter().enumerate() {
                let t = (a as u128 * b as u128) + product[i + j] as u128 + carry as u128;
                let (low, high) = split_u128(t);
                product[i + j] = low;
                carry = high;
            }
            product[i + N_WORDS] = carry; // 4 is the number of 64-bit words in rhs.
        }

        // Split product into low and high Selfs.
        let low = Self::new(product[0..N_WORDS].try_into().unwrap());
        let high = Self::new(product[N_WORDS..2 * N_WORDS].try_into().unwrap());
        (low, high)
    }

    pub fn div_with_remainder(self, rhs: Self) -> (Self, Self) {
        let (q, r) = multi_word_div(&self.words, &rhs.words);
        // Convert to arrays.
        debug_assert!(q.len() <= N_WORDS);
        debug_assert!(r.len() <= N_WORDS);
        let mut q_words = [0u64; N_WORDS];
        let mut r_words = [0u64; N_WORDS];
        for i in 0..N_WORDS {
            q_words[i] = *q.get(i).unwrap_or(&0u64);
            r_words[i] = *r.get(i).unwrap_or(&0u64);
        }
        (Self::new(q_words), Self::new(r_words))
    }
}

impl<const N_WORDS: usize> From<u64> for Ux64<N_WORDS> {
    fn from(val: u64) -> Self {
        let mut words = [0u64; N_WORDS];
        words[0] = val;
        Self { words }
    }
}

impl<const N_WORDS: usize> From<&BigUInt> for Ux64<N_WORDS> {
    fn from(src: &BigUInt) -> Self {
        // Take the first N_WORDS words, ignoring the rest.
        let words_as_vec: Vec<_> = src
            .as_le_words()
            .iter()
            .chain(std::iter::repeat(&0))
            .take(N_WORDS)
            .cloned()
            .collect();

        let words: [u64; N_WORDS] = words_as_vec.try_into().unwrap();
        Ux64::<N_WORDS>::new(words)
    }
}

impl<const N_WORDS: usize> FromStr for Ux64<N_WORDS> {
    type Err = FromDecStrErr;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ux64::from_dec_str(s)
    }
}

impl<const N_WORDS: usize> Display for Ux64<N_WORDS> {
    fn fmt(&self, _f: &mut Formatter<'_>) -> std::fmt::Result {
        // See Knuth, TAOCP, Volume 2, section 4.4
        unimplemented!()
    }
}

impl<const N_WORDS: usize> Add for Ux64<N_WORDS> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        let (value, overflow) = self.carrying_add(rhs, false);
        assert!(!overflow);
        value
    }
}

impl<const N_WORDS: usize> Sub for Ux64<N_WORDS> {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self {
        let (value, borrow) = self.borrowing_sub(rhs, false);
        assert!(!borrow);
        value
    }
}

impl<const N_WORDS: usize> Mul for Ux64<N_WORDS> {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self {
        let (low, high) = self.carrying_mul(rhs, Self::zero());
        assert!(high.is_zero()); // Overflow
        low
    }
}

impl<const N_WORDS: usize> Div for Ux64<N_WORDS> {
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        let (q, _r) = self.div_with_remainder(rhs);
        q
    }
}

impl<const N_WORDS: usize> Rem for Ux64<N_WORDS> {
    type Output = Self;

    fn rem(self, rhs: Self) -> Self::Output {
        let (_q, r) = self.div_with_remainder(rhs);
        r
    }
}

impl<const N_WORDS: usize> PartialOrd for Ux64<N_WORDS> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<const N_WORDS: usize> Ord for Ux64<N_WORDS> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.words.iter().rev().cmp(other.words.iter().rev())
    }
}

#[cfg(test)]
mod tests {
    use crate::integers::ux64::Ux64;

    // N_WORDS must be 2 or greater.
    type _U128 = Ux64<2>;
    type _U196 = Ux64<3>;
    type _U256 = Ux64<4>;
    type _U320 = Ux64<5>;
    type _U384 = Ux64<6>;
    type _U512 = Ux64<8>;
    type _U1024 = Ux64<16>;

    // Using these will cause panics.
    type _U00 = Ux64<0>;
    type _U64 = Ux64<1>;

    // TODO:
}
