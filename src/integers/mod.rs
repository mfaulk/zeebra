//! Large unsigned integer types.
//!
//! Unlike other implementations, these types are created by const functions, which allows them to
//! be used as const generic parameters.

mod big_integers;

mod gcd;
mod jacobi;
mod prime_factors;
mod roots;
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
pub use roots::perfect_power;
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

/// `limbs - 2`, over little-endian 64-bit limbs and at the same width.
///
/// The Fermat inversion exponent `q - 2`. Const and allocation-free, so a field can hold it in an
/// associated const as wide as its order rather than routing it through a `u128` — which is what
/// keeps the computation correct for an order too wide for any machine integer.
/// [`multi_word_sub`] is the general case and does neither.
///
/// # Panics
/// Panics if the value is below two. No finite field has an order below two, so a caller
/// computing a Fermat exponent cannot reach this.
pub const fn limbs_minus_two<const N: usize>(mut limbs: [u64; N]) -> [u64; N] {
    let mut borrow = 2u64;
    let mut index = 0;
    while index < N {
        let (difference, borrowed) = limbs[index].overflowing_sub(borrow);
        limbs[index] = difference;
        if !borrowed {
            return limbs;
        }
        borrow = 1;
        index += 1;
    }
    panic!("subtracting two underflows this value");
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
    use crate::integers::{bit, highest_set_bit, limbs_minus_two, lowest_set_bit, num_digits};

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

    /// Subtracting two borrows across limbs and never widens to a machine integer.
    #[test]
    fn test_limbs_minus_two() {
        assert_eq!(limbs_minus_two([2]), [0]);
        assert_eq!(limbs_minus_two([3]), [1]);
        assert_eq!(limbs_minus_two([u64::MAX]), [u64::MAX - 2]);

        // A borrow out of the low limb.
        assert_eq!(limbs_minus_two([0, 1]), [u64::MAX - 1, 0]);
        assert_eq!(limbs_minus_two([1, 1]), [u64::MAX, 0]);
        assert_eq!(limbs_minus_two([2, 1]), [0, 1]);

        // A borrow that propagates the whole way up, which is where a `u128` round trip would
        // have lost the value entirely.
        assert_eq!(
            limbs_minus_two([0, 0, 0, 1]),
            [u64::MAX - 1, u64::MAX, u64::MAX, 0]
        );
        assert_eq!(
            limbs_minus_two([1, 0, 0, 1]),
            [u64::MAX, u64::MAX, u64::MAX, 0]
        );

        // Usable in a const context, which is the point: a field holds its Fermat exponent in an
        // associated const of the same width as its order.
        const EXPONENT: [u64; 2] = limbs_minus_two([0, 1]);
        assert_eq!(EXPONENT, [u64::MAX - 1, 0]);
    }

    /// Subtracting two from a value below two is rejected rather than wrapping.
    #[test]
    #[should_panic(expected = "underflows")]
    fn test_limbs_minus_two_underflows() {
        let _ = limbs_minus_two([1, 0]);
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
