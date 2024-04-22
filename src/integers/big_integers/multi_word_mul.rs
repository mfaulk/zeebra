//! Multiple-Word Addition of Non-negative Integers
//!
//! Large integers are represented by multiple 64-bit words, in little-endian order.

use crate::integers::{num_digits, utils::split_u128};

pub fn multi_word_mul(a: &[u64], b: &[u64]) -> Vec<u64> {
    // Ignore higher-order zero digits.
    let a = &a[0..num_digits(a)];
    let b = &b[0..num_digits(b)];

    // See Knuth, TAOCP, Volume 2, section 4.3.1.
    let m = a.len();
    let n = b.len();

    // Multiplication of an m-place integer by an n-place integer yields an (m+n)-place integer.
    let mut product: Vec<u64> = vec![0u64; m + n];
    let mut last_digit_index: usize = 0;

    for (i, a_i) in a.iter().enumerate() {
        let mut carry: u64 = 0;
        for (j, b_j) in b.iter().enumerate() {
            let t = (*a_i as u128 * *b_j as u128) + product[i + j] as u128 + carry as u128;
            let (low, high) = split_u128(t);
            if low != 0 {
                last_digit_index = i + j;
            }
            product[i + j] = low;
            carry = high;
        }
        if carry != 0 {
            last_digit_index = product.len() - 1;
        }
        product[i + n] = carry;
    }

    // Trim high zeros.
    product.resize(last_digit_index + 1, 0);
    product
}

#[cfg(test)]
mod tests {
    use crate::integers::{multi_word_mul, sample_n_words};
    use rand::thread_rng;

    #[test]
    // One is the multiplicative identity.
    fn test_multiplicative_identity() {
        let mut rng = thread_rng();
        for n_words in 1..12 {
            for _n_iterations in 0..1000 {
                let a = sample_n_words(n_words, &mut rng);
                let one = [1u64];
                let prod = multi_word_mul(&a, &one);
                assert_eq!(a, prod);
            }
        }
    }

    #[test]
    // a * b = b * a
    fn test_mul_is_commutative() {
        let mut rng = thread_rng();
        for _n_iterations in 0..1000 {
            for n_words_a in 1..12 {
                let a = sample_n_words(n_words_a, &mut rng);
                for n_words_b in 1..12 {
                    let b = sample_n_words(n_words_b, &mut rng);
                    assert_eq!(multi_word_mul(&a, &b), multi_word_mul(&b, &a));
                }
            }
        }
    }

    #[test]
    // Product does not contain high-order zeros.
    fn test_sum_is_trimmed() {
        let a = [2u64, 0, 0, 0, 0];
        let b = [3u64, 2, 1, 0, 0];
        assert_eq!(multi_word_mul(&a, &b), vec![6, 4, 2]);
    }
}
