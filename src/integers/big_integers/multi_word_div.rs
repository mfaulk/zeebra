//! Long division of multi-word unsigned integers.
//!
//! This is based on Knuth's Algorithm D (TAOCP, Volume 2, section 4.3.1). The idea is similar
//! to performing long division with pencil and paper: starting with the dividend u and the
//! divisor v, figure out how many times v goes into the first several digits of u. This value is
//! the first digit `q` of the quotient. Next, we subtract off q*v from the first few digits of u,
//! and "bring down" the next digit of u. Then, we repeat the process until the remainder is less
//! than the divisor. For example:
//!
//! '''ignore
//!             3098 = quotient
//!        _________
//!    102 | 0316097
//!          0306    = 3 * 102
//!          ----
//!           0100
//!           0000   = 0 * 102
//!           ----
//!            1009
//!            0918  = 9 * 102
//!            ----
//!             0917
//!             0816 = 8 * 102
//!             ----
//!              101 = remainder
//! '''
//!
//! Note that for an n-digit divisor, we always worked with n+1 digits at a time (and we added
//! a leading zero to the dividend so that this would always work). The hard part here is guessing
//! the right quotient digits 3,0,9,8. They would be easy to find if we could divide multi-word
//! integers( e.g., floor(0316 / 102) = 3), but that's exactly the operation we are trying to build.
//! Since we can't compute a quotient digit exactly, we will estimate it and then correct. The meat
//! of the algorithm is about choosing a good estimate of the quotient digit, so that we don't
//! need to do much work correcting it.
//!
//! Knuth estimates a quotient digit `q` using the first two digits of the dividend (i.e., running
//! remainder) and the first digit of the divisor. It turns out that this is a good guess when the
//! first digit of the divisor is large. To ensure that is always the case, the algorithm starts
//! by "normalizing" the dividend and divisor by multiplying each by the same scale factor. Here,
//! the scale factor is a power of two, so normalizing is just bit shifting. Normalizing does not
//! change the quotient, but it does change the remainder. The remainder needs to be "de-normalized",
//! e.g. by shifting. For example, dividing 316097 by 102 could by done by scaling each by 5:
//!
//! '''ignore
//!          3098
//!        ________
//!    510 |1580485      Guess q = 15/5 = 3
//!         1530
//!         ----
//!          0504        Guess q = 05/5 = 1. Oops! Can't subtract 510 from 504. Decrease q...
//!          0000
//!          ----
//!           5048       Guess q = 50/5 = 10. Oops! 10 is not a single digit. Decrease q...   
//!           4590
//!           ----
//!            4585      Guess q = 45/5 = 9. Oops! Can't subtract 9*510 from 4585. Decrease q...
//!            4080
//!            ----
//!             505      Divide by 5 to "denormalize". The remainder is 101.           
//! '''  
//!
//! # References
//! * Knuth, TAOCP, Volume 2, section 4.3.1,
//! * "Multiple-length division revisited: a tour of the minefield"

use crate::integers::{
    big_integers::{
        multi_word_cmp::multi_word_cmp,
        multi_word_shift::{shift_left, shift_right},
    },
    multi_word_mul, multi_word_sub, num_digits,
};
use std::cmp::Ordering;

// Radix
const B: u128 = 1 << 64;

/// Computes u/v, returning quotient and remainder.
///
/// # Arguments
/// * `u` - Dividend. Little-endian, without high-order zero digits.
/// * `v` - Divisor. Little-endian, without high-order zero digits.
///
/// Returns the quotient `u div v` and remainder `u mod v`. Panics if v is zero.
pub fn multi_word_div(u: &[u64], v: &[u64]) -> (Vec<u64>, Vec<u64>) {
    // Ignore higher-order zero digits.
    let u = &u[0..num_digits(u)];
    let v = &v[0..num_digits(v)];

    // The length in digits of the divisor (omitting high-order zeros).
    let n = v.len();
    assert!(n > 0);

    // If the divisor is longer than the dividend, the quotient is 0 and the remainder is x.
    if n > u.len() {
        let quotient = vec![0];
        let remainder = u.to_vec();
        return (quotient, remainder);
    }

    // The number of digits that u is longer than v.
    let m = u.len() - n;

    // println!("u: {:?}, v: {:?}", u, v);
    // println!("m: {}, n: {}", m, n);

    // If the divisor is a single digit, a simpler division routine can be used.
    if n == 1 {
        return n_by_one_div(u, v[0]);
    }

    // Normalize u and v.
    // Long division iteratively computes the digits of the quotient through a process of
    // estimation and correction. It turns out that the number of corrections can be reduced
    // if the operands are scaled so that the leading digit of the divisor is greater than half
    // the radix, i.e., its most significant bit is 1. A bit shift is one way to achieve this.

    let shift = v.last().expect("v should not be empty").leading_zeros();

    // The normalized running remainder.
    let mut u = shift_left(u, shift);
    // Normalization may introduce another digit; if not, we append 0. This avoids special cases.
    if u.len() == m + n {
        u.push(0u64);
    }
    debug_assert_eq!(u.len(), m + n + 1);

    // The normalized divisor. The highest bit of its highest digit should be 1.
    let v = shift_left(v, shift);
    debug_assert!(v.len() == n);

    // Leading and second-leading digits of the divisor.
    let v_n1 = v[n - 1] as u128;
    let v_n2 = v[n - 2] as u128;

    // Iteratively finds the next digit `q` of the quotient, and reduces the running remainder.
    // We don't yet have the ability to divide the remainder by the dividend to find the quotient
    // digit, so we will start with an estimate and then refine it until we reach the true value.
    let mut quotient = vec![0u64; m + 1];
    for j in (0..=m).rev() {
        // Estimate the next quotient digit `q` by dividing the first two digits of the
        // current remainder by the first digit of the divisor.
        let (mut q, mut r) = {
            // The first two digits of the running remainder u, as a u128 value.
            let x = ((u[j + n] as u128) << 64) + u[j + n - 1] as u128;
            let q = x / v_n1;
            let r = x % v_n1;
            (q, r)
        };

        debug_assert!(q <= B);

        loop {
            // if q = b or q * v_{n-2} > b* r+ u_{j+n-2}...
            // * The radix B does not fit in a single digit, so q == B must be reduced.
            // * The second condition detects when q is off by two, and usually detects when it is off by one.
            if q == B || q * v_n2 > r * B + u[j + n - 2] as u128 {
                q -= 1;
                r += v_n1;
                if r >= B {
                    break;
                }
            } else {
                break;
            }
        }

        // At this point, q is a single digit. The true quotient digit is either q or q-1.
        debug_assert!(q <= u64::MAX as u128);
        let mut q = q as u64;

        // If q*v is greater than u, subtract 1 from q, then recompute q*v.
        let mut qv = multi_word_mul(&[q], &v);
        if multi_word_cmp(&qv, &u[j..=j + n]) == Ordering::Greater {
            println!("This step should happen extremely rarely.");
            q -= 1;
            // Subtracting v from `qv` is cheaper than recomputing it by multiplying.
            let (new_qv, borrow) = multi_word_sub(&qv, &v);
            debug_assert!(!borrow);
            qv = new_qv;
        }

        // q is now the correct quotient digit.
        quotient[j] = q;
        let (remainder_digits, borrow) = multi_word_sub(&u[j..=j + n], &qv);
        debug_assert!(!borrow);
        debug_assert!(remainder_digits.len() <= n + 1);
        for i in 0..=n {
            u[j + i] = *remainder_digits.get(i).unwrap_or(&0u64);
        }
    }

    // Un-normalize the remainder.
    let remainder = shift_right(&u, shift);
    (quotient, remainder)
}

/// Divide an n-digit number by a 1-digit number.
fn n_by_one_div(u: &[u64], v: u64) -> (Vec<u64>, Vec<u64>) {
    // TODO: Enforce that u does not contain higher-order zero digits.
    assert_ne!(v, 0);

    let n = u.len();
    let mut quotient = vec![0u64; n];
    let mut temp: u128 = 0;
    let v = v as u128;
    for (i, u_i) in u.iter().enumerate().rev() {
        temp = (temp << 64) + *u_i as u128;
        let q = temp / v;
        debug_assert!(q <= u64::MAX as u128);
        temp -= q * v;
        quotient[i] = q as u64;
    }

    debug_assert!(temp < v);
    (quotient, vec![temp as u64])
}

#[cfg(test)]
mod tests {

    #[test]
    fn test_n_by_one_div() {
        let u = [10, 20];
        let v = 5;
        let (q, r) = n_by_one_div(&u, v);
        assert_eq!(q, vec![2, 4]);
        assert_eq!(r, vec![0]);
    }

    #[test]
    #[should_panic]
    // Dividing by zero should panic.
    fn test_div_zero() {
        let u: [u64; 2] = [10, 20];
        let v: [u64; 1] = [0];
        let (_q, _r) = multi_word_div(&u, &v);
    }

    // TODO: Input(s) have higher-order zeros.

    #[test]
    // The divisor is longer than the dividend.
    fn test_divisor_has_more_digits() {
        let u: [u64; 2] = [10, 20];
        let v: [u64; 3] = [2, 18, 44];
        let (q, r) = multi_word_div(&u, &v);
        assert_eq!(q, vec![0]);
        assert_eq!(r, u);
    }

    use crate::integers::{
        big_integers::multi_word_div::n_by_one_div, from_dec_str, multi_word_add, multi_word_div,
        multi_word_mul, sample_n_words,
    };
    use rand::thread_rng;

    #[test]
    fn test_div_warm_up() {
        let u: [u64; 2] = [10, 20];
        let v: [u64; 2] = [5, 10];
        let (q, r) = multi_word_div(&u, &v);
        assert_eq!(q, vec![2]);
        assert_eq!(r, vec![0]);
    }

    #[test]
    // u = qv + r
    fn test_div() {
        let mut rng = thread_rng();
        // Divide an (n+m)-digit word by an n-digit word.
        for n in 1..13 {
            for m in 0..9 {
                for _iteration in 0..1000 {
                    // Divide an (m+n)-place number by an n-place number.
                    let u = sample_n_words(m + n, &mut rng);
                    let v = sample_n_words(n, &mut rng);
                    let (q, r) = multi_word_div(&u, &v);

                    // u = q*v + r
                    let qv = multi_word_mul(&q, &v);
                    assert_eq!(u, multi_word_add(&qv, &r));
                }
            }
        }
    }

    #[test]
    // Spot-check against Sage. Divide a three-digit number by a two-digit number.
    fn test_div_spot_check() {
        let a = from_dec_str("1090809809809888800987987098700920403924309243098987098").unwrap();
        assert_eq!(a.len(), 3);
        let b = from_dec_str("5987987892497234098234092348423").unwrap();
        assert_eq!(b.len(), 2);

        // sage: a = 1090809809809888800987987098700920403924309243098987098
        // sage: b = 5987987892497234098234092348423
        // sage: quotient = a // b
        // sage: remainder = a % b

        let quotient = from_dec_str("182166335235353459789298").unwrap();
        assert_eq!(quotient, vec![4737507471637581298, 9875]);

        let remainder = from_dec_str("1463012738159024550375516410044").unwrap();
        assert_eq!(remainder, vec![5516379191842312380, 79310079454]);

        let (q, r) = multi_word_div(&a, &b);
        assert_eq!(quotient, q);
        assert_eq!(remainder, r);
    }

    #[ignore]
    #[test]
    // Test the "rare" correction to q.
    fn test_div_rare_update_to_q() {
        // TODO: When does this happen?
        unimplemented!()
    }

    #[test]
    // The initial estimate q equals the radix.
    fn test_div_q_equals_b() {
        let u = [0u64, 0u64, 1u64 << 63];
        let v = [1u64, 1u64 << 63];

        // v is chosen so that it does not need to be normalized.
        // When the first quotient digit is estimated, it will divide [1<<63, 0] / [1<<63], which
        // yields the radix B = 1<<64.
        let (_q, _r) = multi_word_div(&u, &v);
    }

    // TODO: the quotient should have at most m+1 digits. It should not have high-order zeros.

    // TODO: the remainder should have at most n digits. It should not have high-order zeros.

    // TODO: u and v have the same number of digits, v needs to be normalized.

    // TODO: u has more digits, v does not need to be normalized.

    // TODO: u has more digits, v needs to be normalized.
}
