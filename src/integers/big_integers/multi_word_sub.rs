//! Multiple-Word Subtraction of Non-negative Integers
//!
//! Large integers are represented by multiple 64-bit words, in little-endian order.

use crate::integers::num_digits;
use std::cmp::max;

/// Wrapping multi-word subtraction.
///
/// Returns the difference `a - b` and a boolean indicating whether the difference is negative.
pub fn multi_word_sub(a: &[u64], b: &[u64]) -> (Vec<u64>, bool) {
    // Ignore higher-order zero digits.
    let a = &a[0..num_digits(a)];
    let b = &b[0..num_digits(b)];

    let m = a.len();
    let n = b.len();

    let mut result: Vec<u64> = Vec::with_capacity(max(m, n) + 1);

    let mut last_digit_index: usize = 0;
    let mut borrow = false;
    for i in 0..max(m, n) {
        let a_i = a.get(i).unwrap_or(&0u64);
        let b_i = b.get(i).unwrap_or(&0u64);
        let (diff, borrowed) = a_i.borrowing_sub(*b_i, borrow);
        if diff != 0 {
            last_digit_index = i;
        }
        result.push(diff);
        borrow = borrowed;
    }

    // Truncate the result so that it does not contain unnecessary zero digits.
    result.resize(last_digit_index + 1, 0);
    (result, borrow)
}

#[cfg(test)]
mod tests {
    use crate::integers::{big_integers::multi_word_sub::multi_word_sub, sample_n_words};
    use rand::thread_rng;

    #[test]
    // a - 0 = a
    fn test_additive_identity() {
        let mut rng = thread_rng();
        for n_words in 1..12 {
            for _n_iterations in 0..1000 {
                let a = sample_n_words(n_words, &mut rng);
                let zero = [0u64];
                let (res, borrow) = multi_word_sub(&a, &zero);
                assert!(!borrow);
                assert_eq!(a, res);
            }
        }
    }

    #[test]
    fn test_sub() {
        let a = vec![2, 3, 4, 5, 6];
        let b = vec![1, 0, 1, 0];

        let (res, borrow) = multi_word_sub(&a, &b);
        assert!(!borrow);
        assert_eq!(res, vec![1, 3, 3, 5, 6]);
    }

    #[test]
    fn test_borrow() {
        let a = vec![0];
        let b = vec![1];
        let (res, borrow) = multi_word_sub(&a, &b);
        assert!(borrow);
        assert_eq!(res, vec![u64::MAX]); // wrap around to MAX.
    }
}
