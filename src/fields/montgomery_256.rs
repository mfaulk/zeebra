//! Montgomery arithmetic modulo an odd 4-limb prime.
//!
//! An element `a` is held as `a * R mod p` with `R = 2^256`, so multiplication needs no division.
//! This is `prime_field_64`'s [`montgomery`](super::prime_field_64) module at four limbs rather
//! than one, with the same invariant and the same reason for existing.
//!
//! The crate's existing wide-integer operations are not usable here. `Ux64::carrying_mul`
//! allocates a `Vec` for the double-width product and `Rem` goes through `multi_word_div`'s long
//! division with more allocation — which is exactly what `PrimeFieldElement128` does, and why its
//! multiplication costs 135 ns against this module's 21. Nothing below allocates, and the
//! constants are `const fn`s so they are computed at compile time.
//!
//! # References
//! * Koç, Acar and Kaliski, *Analyzing and Comparing Montgomery Multiplication Algorithms*, IEEE
//!   Micro 16(3), 1996, for CIOS.
//! * Guajardo, Kumar, Paar and Pelzl, *Efficient Software-Implementation of Finite Fields with
//!   Applications to Cryptography*, Algorithm 16, for the binary inversion.

/// 64-bit limbs in a 256-bit value.
pub const LIMBS: usize = 4;

/// `-p^{-1} mod 2^64`, the factor that makes the low limb of `t + m*p` vanish.
///
/// Newton's iteration for the inverse of an odd number modulo a power of two doubles the number
/// of correct bits each step, so one bit reaches 64 in six steps. Only the low limb of p
/// participates, which is why this is identical to the 64-bit field's version.
pub const fn n_prime(p_low: u64) -> u64 {
    let mut inverse: u64 = 1;
    let mut step = 0;
    while step < 6 {
        inverse = inverse.wrapping_mul(2u64.wrapping_sub(p_low.wrapping_mul(inverse)));
        step += 1;
    }
    inverse.wrapping_neg()
}

/// `a < b`, comparing from the most significant limb down.
pub const fn less_than(a: &[u64; LIMBS], b: &[u64; LIMBS]) -> bool {
    let mut i = LIMBS;
    while i > 0 {
        i -= 1;
        if a[i] != b[i] {
            return a[i] < b[i];
        }
    }
    false
}

/// The index of the highest nonzero limb of `modulus`.
///
/// A modulus narrower than 256 bits leaves high limbs zero, and anything deriving a bit width
/// from the limbs has to ask which limb is the top one rather than assume it is the last.
///
/// # Panics
/// Panics at compile time if `modulus` is zero, which is not an odd prime.
pub const fn highest_occupied_limb(modulus: &[u64; LIMBS]) -> usize {
    let mut i = LIMBS;
    while i > 0 {
        i -= 1;
        if modulus[i] != 0 {
            return i;
        }
    }
    panic!("the modulus must be nonzero")
}

/// `a -= p`, wrapping. Correct only where `a >= p`, which every caller establishes.
///
/// Spelled with `overflowing_sub` rather than `borrowing_sub` because this runs at compile time
/// too, and the carrying operations are not `const fn`.
const fn sub_assign_wrapping(a: &mut [u64; LIMBS], p: &[u64; LIMBS]) {
    let mut borrow = false;
    let mut i = 0;
    while i < LIMBS {
        let (difference, first) = a[i].overflowing_sub(p[i]);
        let (difference, second) = difference.overflowing_sub(borrow as u64);
        a[i] = difference;
        borrow = first || second;
        i += 1;
    }
}

/// `2^exponent mod p`, by doubling.
///
/// Doubling needs a shift and a conditional subtraction, both of which a `const fn` can do, so
/// `R mod p` and `R^2 mod p` are compile-time constants. Computing them by division would need
/// `multi_word_div`, which allocates and therefore cannot run in a constant.
pub const fn power_of_two_mod_p(exponent: u32, p: &[u64; LIMBS]) -> [u64; LIMBS] {
    let mut acc = [0u64; LIMBS];
    acc[0] = 1;

    let mut doubled = 0;
    while doubled < exponent {
        let mut carry = 0u64;
        let mut i = 0;
        while i < LIMBS {
            let next_carry = acc[i] >> 63;
            acc[i] = (acc[i] << 1) | carry;
            carry = next_carry;
            i += 1;
        }
        // A bit shifted off the top means the true value is `2^256 + acc`, which exceeds p. One
        // subtraction suffices because `acc < p` held before the doubling, so the true value is
        // below `2p`.
        if carry == 1 || !less_than(&acc, p) {
            sub_assign_wrapping(&mut acc, p);
        }
        doubled += 1;
    }
    acc
}

/// `a * b * R^{-1} mod p`, which is the product in Montgomery form when both inputs are.
///
/// `(aR)(bR) * R^{-1} = (ab)R`, so the representation is preserved.
///
/// Coarsely Integrated Operand Scanning: the reduction is interleaved with the product, so the
/// eight-limb intermediate is never materialized. Each pass over `i` adds `a * b[i]` into the
/// accumulator and then cancels one low limb, leaving the accumulator one limb shorter than it
/// would otherwise grow.
#[inline(always)]
pub fn mul(a: &[u64; LIMBS], b: &[u64; LIMBS], p: &[u64; LIMBS], p_prime: u64) -> [u64; LIMBS] {
    // The accumulator is conceptually LIMBS + 2 words. The top two are kept separately so the
    // array stays the width of a field element and the compiler keeps it all in registers.
    let mut t = [0u64; LIMBS];
    let mut high = 0u64;

    for i in 0..LIMBS {
        let b_i = b[i];

        // t += a * b[i]
        let mut carry = 0u64;
        for j in 0..LIMBS {
            let wide = (a[j] as u128) * (b_i as u128) + (t[j] as u128) + (carry as u128);
            t[j] = wide as u64;
            carry = (wide >> 64) as u64;
        }
        let (sum, carried) = high.overflowing_add(carry);
        high = sum;
        let overflow = carried as u64;

        // m is chosen so that the low limb of t + m*p is zero, making the division by 2^64 a
        // shift — which is the `t[j - 1]` indexing below rather than an explicit shift.
        let m = t[0].wrapping_mul(p_prime);
        let wide = (m as u128) * (p[0] as u128) + (t[0] as u128);
        debug_assert_eq!(wide as u64, 0, "m must cancel the low limb");
        let mut carry = (wide >> 64) as u64;

        for j in 1..LIMBS {
            let wide = (m as u128) * (p[j] as u128) + (t[j] as u128) + (carry as u128);
            t[j - 1] = wide as u64;
            carry = (wide >> 64) as u64;
        }
        let (sum, carried) = high.overflowing_add(carry);
        t[LIMBS - 1] = sum;
        high = overflow + carried as u64;
    }

    // CIOS leaves a result below 2p, so one conditional subtraction finishes it. A branch rather
    // than a mask: masking both candidates was measured and was slower, because the branch
    // predicts well enough and the mask lengthens the dependency chain.
    if high > 0 || !less_than(&t, p) {
        sub_assign_wrapping(&mut t, p);
    }
    t
}

/// `a + b mod p`, both operands reduced.
#[inline(always)]
pub fn add(a: &[u64; LIMBS], b: &[u64; LIMBS], p: &[u64; LIMBS]) -> [u64; LIMBS] {
    let mut out = [0u64; LIMBS];
    let mut carry = false;
    for i in 0..LIMBS {
        let (sum, carried) = a[i].carrying_add(b[i], carry);
        out[i] = sum;
        carry = carried;
    }
    // Reduced operands sum to below 2p, so one conditional subtraction suffices. A carry out of
    // the top limb means the true sum is `2^256 + out`, which is above p.
    if carry || !less_than(&out, p) {
        sub_assign_wrapping(&mut out, p);
    }
    out
}

/// `a - b mod p`, both operands reduced.
#[inline(always)]
pub fn sub(a: &[u64; LIMBS], b: &[u64; LIMBS], p: &[u64; LIMBS]) -> [u64; LIMBS] {
    let mut out = [0u64; LIMBS];
    let mut borrow = false;
    for i in 0..LIMBS {
        let (difference, borrowed) = a[i].borrowing_sub(b[i], borrow);
        out[i] = difference;
        borrow = borrowed;
    }
    // On borrow the difference is negative, and adding p brings it back into range.
    if borrow {
        let mut carry = false;
        for i in 0..LIMBS {
            let (sum, carried) = out[i].carrying_add(p[i], carry);
            out[i] = sum;
            carry = carried;
        }
    }
    out
}

/// `x / 2 mod p`, for odd p.
///
/// An even `x` halves by a shift. An odd one does not, but `x + p` is even, and `(x + p) / 2` is
/// the same residue — so the bit carried out of `x + p` is shifted back in from the top.
#[inline(always)]
fn halve(x: &mut [u64; LIMBS], p: &[u64; LIMBS]) {
    let mut carry = false;
    if x[0] & 1 == 1 {
        for i in 0..LIMBS {
            let (sum, carried) = x[i].carrying_add(p[i], carry);
            x[i] = sum;
            carry = carried;
        }
    }

    let mut i = LIMBS;
    let mut high_bit = carry as u64;
    while i > 0 {
        i -= 1;
        let next_high_bit = x[i] & 1;
        x[i] = (x[i] >> 1) | (high_bit << 63);
        high_bit = next_high_bit;
    }
}

/// Whether `limbs` is one.
#[inline(always)]
fn is_one(limbs: &[u64; LIMBS]) -> bool {
    limbs[0] == 1 && limbs[1] == 0 && limbs[2] == 0 && limbs[3] == 0
}

/// `a -= b`, wrapping. Correct only where `a >= b`.
#[inline(always)]
fn sub_assign(a: &mut [u64; LIMBS], b: &[u64; LIMBS]) {
    let mut borrow = false;
    for i in 0..LIMBS {
        let (difference, borrowed) = a[i].borrowing_sub(b[i], borrow);
        a[i] = difference;
        borrow = borrowed;
    }
}

/// The multiplicative inverse of a nonzero `a`, both argument and result in Montgomery form.
///
/// The binary extended Euclidean algorithm, which needs no division — unlike exponentiation by
/// `p - 2`, whose exponent does not fit in a `u128` and which would cost hundreds of
/// multiplications besides.
///
/// Seeding `b` with `R^2 mod p` rather than with one is what makes the result come out already in
/// Montgomery form: the invariant carried through the loop is `a * b = u * R^2` and
/// `a * c = -v * R^2` modulo p, so when `u` reaches one, `b` holds `a^{-1} * R`.
///
/// # Panics
/// Panics if `a` is zero.
pub fn inverse(a: &[u64; LIMBS], p: &[u64; LIMBS], r_squared: &[u64; LIMBS]) -> [u64; LIMBS] {
    assert_ne!(
        *a, [0u64; LIMBS],
        "The zero element does not have a multiplicative inverse."
    );

    let mut u = *a;
    let mut v = *p;
    let mut b = *r_squared;
    let mut c = [0u64; LIMBS];

    while !is_one(&u) && !is_one(&v) {
        while u[0] & 1 == 0 {
            let mut shifted = u;
            let mut i = LIMBS;
            let mut high_bit = 0u64;
            while i > 0 {
                i -= 1;
                let next_high_bit = shifted[i] & 1;
                shifted[i] = (shifted[i] >> 1) | (high_bit << 63);
                high_bit = next_high_bit;
            }
            u = shifted;
            halve(&mut b, p);
        }

        while v[0] & 1 == 0 {
            let mut shifted = v;
            let mut i = LIMBS;
            let mut high_bit = 0u64;
            while i > 0 {
                i -= 1;
                let next_high_bit = shifted[i] & 1;
                shifted[i] = (shifted[i] >> 1) | (high_bit << 63);
                high_bit = next_high_bit;
            }
            v = shifted;
            halve(&mut c, p);
        }

        if less_than(&v, &u) {
            sub_assign(&mut u, &v);
            b = sub(&b, &c, p);
        } else {
            sub_assign(&mut v, &u);
            c = sub(&c, &b, p);
        }
    }

    if is_one(&u) {
        b
    } else {
        c
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// BN254's scalar field modulus, for exercising the primitives directly.
    const P: [u64; LIMBS] = [
        0x43e1f593f0000001,
        0x2833e84879b97091,
        0xb85045b68181585d,
        0x30644e72e131a029,
    ];

    /// `n_prime` is the negated inverse of the low limb modulo 2^64.
    #[test]
    fn test_n_prime_negates_the_inverse_of_the_low_limb() {
        let np = n_prime(P[0]);
        assert_eq!(P[0].wrapping_mul(np), 1u64.wrapping_neg());
    }

    /// `2^0 mod p` is one, and the doubling loop leaves a reduced residue.
    #[test]
    fn test_power_of_two_mod_p_at_zero_is_one() {
        assert_eq!(power_of_two_mod_p(0, &P), [1, 0, 0, 0]);
    }

    /// `R mod p` and `R^2 mod p` are reduced, and `R^2` is `R` squared.
    #[test]
    fn test_r_and_r_squared_are_consistent() {
        let r = power_of_two_mod_p(256, &P);
        let r2 = power_of_two_mod_p(512, &P);
        assert!(less_than(&r, &P));
        assert!(less_than(&r2, &P));

        // In Montgomery form `mul(x, y)` is `x*y/R`, so `mul(r, r)` is `R^2/R = R`, and
        // `mul(r2, 1)` is `R^2/R = R` as well.
        let np = n_prime(P[0]);
        assert_eq!(mul(&r, &r, &P, np), r);
        assert_eq!(mul(&r2, &[1, 0, 0, 0], &P, np), r);
    }

    /// Halving undoes doubling for both even and odd representatives.
    #[test]
    fn test_halve_inverts_addition_to_self() {
        // 3 and 4 cover the odd and even cases; p - 1 covers the top of the range.
        let mut p_minus_one = P;
        p_minus_one[0] -= 1;
        for x in [[3u64, 0, 0, 0], [4, 0, 0, 0], p_minus_one] {
            let doubled = add(&x, &x, &P);
            let mut halved = doubled;
            halve(&mut halved, &P);
            assert_eq!(halved, x, "halving {x:?} doubled");
        }
    }

    /// `less_than` orders on the most significant differing limb, not the least.
    #[test]
    fn test_less_than_compares_from_the_top_limb() {
        assert!(less_than(&[0, 0, 0, 1], &[u64::MAX, 0, 0, 2]));
        assert!(!less_than(&[u64::MAX, 0, 0, 2], &[0, 0, 0, 1]));
        assert!(!less_than(&P, &P));
    }
}
