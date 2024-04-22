//! Multiple-Word Addition of Non-negative Integers
//!
//! Large integers are represented by multiple 64-bit words, in little-endian order.

use crate::integers::num_digits;
use std::cmp::max;

pub fn multi_word_add(a: &[u64], b: &[u64]) -> Vec<u64> {
    // Ignore higher-order zero digits.
    let a = &a[0..num_digits(a)];
    let b = &b[0..num_digits(b)];

    let m = a.len();
    let n = b.len();

    let mut result: Vec<u64> = Vec::with_capacity(max(m, n) + 1);

    // Index of the last non-zero digit in `sum`.
    let mut last_digit_index: usize = 0;
    let mut carry = false;
    for i in 0..max(m, n) {
        let a_i = a.get(i).unwrap_or(&0u64);
        let b_i = b.get(i).unwrap_or(&0u64);
        let (sum, c) = a_i.carrying_add(*b_i, carry);
        if sum != 0 {
            last_digit_index = i;
        }
        result.push(sum);
        carry = c;
    }
    if carry {
        result.push(1);
        last_digit_index = result.len() - 1;
    }

    // Truncate the result so that it does not contain unnecessary zero digits.
    result.resize(last_digit_index + 1, 0);
    result
}

#[cfg(test)]
mod tests {
    use crate::integers::{big_integers::multi_word_add::multi_word_add, sample_n_words};
    use rand::thread_rng;

    #[test]
    // Zero is the additive identity.
    fn test_additive_identity() {
        let mut rng = thread_rng();
        for n_words in 1..12 {
            for _n_iterations in 0..1000 {
                let a = sample_n_words(n_words, &mut rng);
                let zero = [0u64];
                let sum = multi_word_add(&a, &zero);
                assert_eq!(a, sum);
            }
        }
    }

    #[test]
    // a + b = b + a
    fn test_addition_is_commutative() {
        let mut rng = thread_rng();
        for _n_iterations in 0..1000 {
            for n_words_a in 1..12 {
                let a = sample_n_words(n_words_a, &mut rng);
                for n_words_b in 1..12 {
                    let b = sample_n_words(n_words_b, &mut rng);
                    assert_eq!(multi_word_add(&a, &b), multi_word_add(&b, &a));
                }
            }
        }
    }

    #[test]
    // Sum does not contain high-order zeros.
    fn test_sum_is_trimmed() {
        let a = [1u64, 0, 0, 0, 0];
        let b = [3u64, 2, 1, 0, 0];
        assert_eq!(multi_word_add(&a, &b), vec![4, 2, 1]);
    }

    #[test]
    // "Overflow" creates another digit, equal to 1.
    fn test_addition_overflow() {
        let a = [u64::MAX, u64::MAX];
        let b = [3u64];
        assert_eq!(multi_word_add(&a, &b), vec![2, 0, 1]);
    }
}
