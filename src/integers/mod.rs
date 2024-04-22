//! Large unsigned integer types.
//!
//! Unlike other implementations, these types are created by const functions, which allows them to
//! be used as const generic parameters.

mod big_integers;

mod gcd;
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
pub use prime_factors::{factor, find_generator, from_prime_factorization};
#[cfg(test)]
use rand::{CryptoRng, RngCore};
pub use u256::U256;

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
    use crate::integers::num_digits;

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
