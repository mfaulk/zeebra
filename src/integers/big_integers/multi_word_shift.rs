use crate::integers::{num_digits, utils::split_u128};

pub fn shift_left(x: &[u64], shift: u32) -> Vec<u64> {
    let x = &x[0..num_digits(x)];

    // If `shift` is greater than 64, shift in a zero digit for each multiple of 64.
    let num_zeros_shifted_in = shift / 64;
    let remaining_shift = shift % 64;

    let mut result = vec![0u64; num_zeros_shifted_in as usize];

    // Shift each word by the remaining number of bits, with overflow moving into `carry`.
    let mut carry = 0u64;
    for x_i in x {
        let shifted = (*x_i as u128) << remaining_shift;
        let (low, high) = split_u128(shifted);
        result.push(low + carry);
        carry = high;
    }

    if carry != 0 {
        result.push(carry);
    }

    result
}

pub fn shift_right(x: &[u64], shift: u32) -> Vec<u64> {
    let n = x.len();

    // Shift out a digit for each multiple of 64.
    let num_digits_shifted_out = (shift / 64) as usize;

    if num_digits_shifted_out >= n {
        return vec![0];
    }

    let mut result: Vec<u64> = vec![0u64; n - num_digits_shifted_out];

    // Shift each word by the remaining number of bits, with underflow moving into `carry`.
    let remaining_shift = shift % 64;
    let mut last_digit_index: usize = 0;
    let mut carry = 0u64;
    for (i, x_i) in x.iter().skip(num_digits_shifted_out).enumerate().rev() {
        // Shift x_i into the upper word of a u128, then partially shift it back down.
        // let (low, high) = split_u128(((*x_i as u128) << 64) >> remaining_shift);
        // Or, equivalently:
        let (low, high) = split_u128((*x_i as u128) << (64 - remaining_shift));
        result[i] = high + carry;
        if result[i] != 0 && i > last_digit_index {
            last_digit_index = i;
        }
        carry = low;
    }
    // Any value in carry is shifted out.

    // The highest digit(s) could be zero. If so, drop them.
    result.resize(last_digit_index + 1, 0);
    result
}

#[cfg(test)]
mod tests {
    use crate::integers::{
        big_integers::multi_word_shift::{shift_left, shift_right},
        sample_n_words,
    };
    use rand::thread_rng;

    #[test]
    // Shifting left by zero is the identity.
    fn test_shift_left_by_zero() {
        for n in 1..13 {
            let mut rng = thread_rng();
            let x = sample_n_words(n, &mut rng);
            assert_eq!(x, shift_left(&x, 0));
        }
    }

    #[test]
    // Shift left by less than 64.
    fn test_shift_left_small() {
        let x = [u64::MAX];
        let shifted = shift_left(&x, 1);
        assert_eq!(shifted, [u64::MAX - 1, 1u64]);
    }

    #[test]
    // Shift left by 64 or more bits.
    fn test_shift_left_big() {
        // Shift left by one 64-bit word.
        assert_eq!(shift_left(&[u64::MAX], 64), [0, u64::MAX]);
        // Shift left by three 64-bit words.
        assert_eq!(shift_left(&[u64::MAX], 3 * 64), [0, 0, 0, u64::MAX]);

        assert_eq!(
            shift_left(&[u64::MAX, 0, 1], 3 * 64),
            [0, 0, 0, u64::MAX, 0, 1]
        );
    }

    #[test]
    // Shifting right by zero is the identity.
    fn test_shift_right_by_zero() {
        for n in 1..13 {
            let mut rng = thread_rng();
            let x = sample_n_words(n, &mut rng);
            assert_eq!(x, shift_right(&x, 0));
        }
    }

    #[test]
    // Shift right by less than 64.
    fn test_shift_right_small() {
        assert_eq!(shift_right(&[u64::MAX], 18), [(1u64 << 46) - 1]); // 2^(64 - 18) - 1
    }

    #[test]
    // The high digit of the result should not be zero.
    fn test_shift_right_no_high_zeros() {
        // Shifting by two bits should result in a single 64-bit word.
        assert_eq!(shift_right(&[u64::MAX, 3], 2), [u64::MAX]);
    }

    #[test]
    // Shift right by 64 or more bits.
    fn test_shift_right_big() {
        assert_eq!(shift_right(&[u64::MAX], 64), [0]);
        assert_eq!(shift_right(&[u64::MAX; 3], 128), [u64::MAX]);
    }

    #[test]
    // Shifting left then shifting right is the identity.
    fn test_shift_and_unshift() {
        let mut rng = thread_rng();
        for n_words in 1..13 {
            for shift in 0..256 {
                let x = sample_n_words(n_words, &mut rng);
                println!("x:{:?}, shift: {}", x, shift);
                assert_eq!(x, shift_right(&shift_left(&x, shift), shift));
            }
        }
    }
}
