//! Large unsigned integer types.
//!
//! Unlike other implementations, these types are created by const functions, which allows them to
//! be used as const generic parameters.

mod big_integers;

mod gcd;
mod jacobi;
mod prime_factors;
mod u256;
pub mod utils;
mod ux64;

pub use big_integers::{
    big_uint,
    from_dec_str::{from_dec_str, FromDecStrErr},
    multi_word_add::multi_word_add,
    multi_word_div::multi_word_div,
    multi_word_mul::multi_word_mul,
    multi_word_sub::multi_word_sub,
};
pub use gcd::*;
pub use jacobi::jacobi_symbol;
pub use prime_factors::{factor, find_generator, from_prime_factorization};
#[cfg(test)]
use rand::{CryptoRng, RngCore};
pub use u256::U256;

/// Bit `index` of `limbs`, counted from the least significant bit of the least significant limb.
///
/// `false` beyond the width of `limbs`, so a caller may ask about a position the value cannot
/// reach without bounds-checking first.
#[inline]
pub fn bit(limbs: &[u64], index: usize) -> bool {
    match limbs.get(index / 64) {
        Some(limb) => limb >> (index % 64) & 1 == 1,
        None => false,
    }
}

/// The index of the highest set bit of `limbs`, or `None` if `limbs` is zero.
pub fn highest_set_bit(limbs: &[u64]) -> Option<usize> {
    limbs
        .iter()
        .rposition(|&limb| limb != 0)
        .map(|position| position * 64 + (63 - limbs[position].leading_zeros() as usize))
}

/// The index of the lowest set bit of `limbs`, or `None` if `limbs` is zero.
///
/// The two-adic valuation of the value: the largest s with `2^s` dividing it.
pub fn lowest_set_bit(limbs: &[u64]) -> Option<usize> {
    limbs
        .iter()
        .position(|&limb| limb != 0)
        .map(|position| position * 64 + limbs[position].trailing_zeros() as usize)
}

/// Number of digits, omitting higher-order zeros.
pub fn num_digits(words: &[u64]) -> usize {
    words
        .iter()
        .enumerate()
        .rev()
        .find(|&(_i, x)| *x != 0)
        .map(|(i, _x)| i + 1)
        .unwrap_or(0)
}

#[cfg(test)]
/// Generate a random vector of `n_words` 64-bit words.
pub fn sample_n_words<R: RngCore + CryptoRng>(n: usize, rng: &mut R) -> Vec<u64> {
    (0..n).map(|_| rng.next_u64()).collect()
}

#[cfg(test)]
mod tests {
    use crate::integers::{bit, highest_set_bit, lowest_set_bit, num_digits};

    /// A bit is read from the limb that holds it, and positions past the end read as zero.
    #[test]
    fn test_bit() {
        assert!(bit(&[1], 0));
        assert!(!bit(&[1], 1));
        assert!(bit(&[0, 1], 64));
        assert!(bit(&[0, 1 << 63], 127));
        // Beyond the width of the value.
        assert!(!bit(&[1], 64));
        assert!(!bit(&[], 0));
    }

    /// The highest set bit, or `None` for zero however many limbs hold it.
    #[test]
    fn test_highest_set_bit() {
        assert_eq!(highest_set_bit(&[]), None);
        assert_eq!(highest_set_bit(&[0, 0]), None);
        assert_eq!(highest_set_bit(&[1]), Some(0));
        assert_eq!(highest_set_bit(&[0b1011]), Some(3));
        assert_eq!(highest_set_bit(&[u64::MAX, 1]), Some(64));
        assert_eq!(highest_set_bit(&[0, 0, 1 << 63]), Some(191));
    }

    /// The lowest set bit, which is the two-adic valuation.
    #[test]
    fn test_lowest_set_bit() {
        assert_eq!(lowest_set_bit(&[]), None);
        assert_eq!(lowest_set_bit(&[0, 0]), None);
        assert_eq!(lowest_set_bit(&[1]), Some(0));
        assert_eq!(lowest_set_bit(&[0b1000]), Some(3));
        assert_eq!(lowest_set_bit(&[1 << 63]), Some(63));
        assert_eq!(lowest_set_bit(&[0, 1]), Some(64));
        assert_eq!(lowest_set_bit(&[0, 0, 1 << 4]), Some(132));
    }

    #[test]
    fn test_num_digits() {
        assert_eq!(num_digits(&[]), 0);
        assert_eq!(num_digits(&[0]), 0);
        assert_eq!(num_digits(&[5]), 1);
        assert_eq!(num_digits(&[5, 5]), 2);
        assert_eq!(num_digits(&[5, 5, 0]), 2);
        assert_eq!(num_digits(&[5, 5, 0, 0, 0, 0, 0, 0]), 2);
        assert_eq!(num_digits(&[5, 5, 0, 0, 0, 0, 0, 0, 5]), 9);
    }
}
