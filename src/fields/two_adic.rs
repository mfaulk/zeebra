//! Two-adic roots of unity, derived from the field's order without factoring `q - 1`.
//!
//! The multiplicative group of GF(q) is cyclic of order `q - 1 = 2^s * m` with m odd, so its
//! 2-Sylow subgroup is cyclic of order `2^s`: a primitive `2^k`-th root of unity exists for every
//! `k <= s` and for no larger k. For any non-square z, `z^m` generates that subgroup, so finding
//! one needs s and m — both read off `q - 1` by shifting — and no factorization of m.
//!
//! That is the point. [`KnownOrder::primitive_element`](super::KnownOrder::primitive_element)
//! factors `q - 1`, which for a 254-bit field is not a computation to start by accident, and is
//! why `PrimeFieldElement256` had no root of unity at all and so no NTT.

use rand::{CryptoRng, RngCore};

use crate::{integers::lowest_set_bit, FiniteField, KnownOrder};

/// The two-adicity s and odd part m of `q - 1`, for q given as little-endian 64-bit limbs.
///
/// `q - 1 = 2^s * m` with m odd. The odd part is returned as little-endian limbs because it is an
/// exponent for [`FiniteField::pow_limbs`] and, for a 254-bit field, is no narrower than q.
///
/// # Panics
/// Panics if `order_limbs` is zero or one; a field has order at least two.
pub fn two_adic_decomposition(order_limbs: &[u64]) -> (u32, Vec<u64>) {
    let group_order = decrement(order_limbs);
    let s = lowest_set_bit(&group_order).expect("a field of order q >= 2 has q - 1 >= 1") as u32;
    (s, shift_right(&group_order, s as usize))
}

/// A primitive `2^log_n`-th root of unity in F, found by rejection sampling.
///
/// Expected to draw twice: `z^m` has order exactly `2^s` precisely when z is a non-square, which
/// half of the nonzero elements are.
///
/// # Panics
/// Panics if `log_n` exceeds the field's two-adicity, since no such root exists there.
pub fn two_adic_root_of_unity<F: KnownOrder, R: RngCore + CryptoRng>(log_n: u32, rng: &mut R) -> F {
    let (s, odd_part) = two_adic_decomposition(F::order_limbs());
    assert!(
        log_n <= s,
        "no primitive 2^{log_n}-th root of unity exists: the two-adicity of this field is {s}"
    );

    // The only first root of unity is 1, and the loop below would square `s - 1` times for it.
    if log_n == 0 {
        return F::one();
    }

    // `z^m` lies in the 2-Sylow subgroup whatever z is, and generates it exactly when
    // `(z^m)^(2^(s-1)) != 1`, i.e. when `z^((q-1)/2) != 1`, i.e. when z is a non-square.
    let mut root = loop {
        let z = F::random(rng);
        if z.is_zero() {
            continue;
        }
        let w = z.pow_limbs(&odd_part);
        if repeated_squaring(w, s - 1) != F::one() {
            break w;
        }
    };

    // Squaring halves the order, so `s - log_n` of them leave order exactly `2^log_n`.
    root = repeated_squaring(root, s - log_n);
    root
}

/// `x^(2^times)`.
fn repeated_squaring<F: FiniteField>(mut x: F, times: u32) -> F {
    for _ in 0..times {
        x = x * x;
    }
    x
}

/// `limbs - 1`, little-endian.
///
/// # Panics
/// Panics if `limbs` is zero.
fn decrement(limbs: &[u64]) -> Vec<u64> {
    let mut out = limbs.to_vec();
    for limb in out.iter_mut() {
        if *limb != 0 {
            *limb -= 1;
            return out;
        }
        // Borrow into the next limb.
        *limb = u64::MAX;
    }
    panic!("cannot decrement zero");
}

/// `limbs >> bits`, little-endian.
fn shift_right(limbs: &[u64], bits: usize) -> Vec<u64> {
    let whole = bits / 64;
    let part = bits % 64;
    if whole >= limbs.len() {
        return vec![0];
    }

    let mut out = Vec::with_capacity(limbs.len() - whole);
    for i in whole..limbs.len() {
        let low = limbs[i] >> part;
        // `64 - part` would be a 64-bit shift when `part` is zero, which is undefined.
        let high = if part == 0 || i + 1 >= limbs.len() {
            0
        } else {
            limbs[i + 1] << (64 - part)
        };
        out.push(low | high);
    }
    out
}

#[cfg(test)]
mod tests {
    use rand::{prelude::StdRng, SeedableRng};

    use super::{two_adic_decomposition, two_adic_root_of_unity};
    use crate::{
        fields::{
            Bls12_381Fr, Bn254Fr, PrimeFieldElement64, Zp13, Zp18446744069414584321, Zp2147483647,
            Zp65537,
        },
        integers::big_uint::BigUInt,
        KnownOrder, One, Zero,
    };

    /// KoalaBear, `2^31 - 2^24 + 1`, the field the 2026 Poseidon challenges are over.
    type KoalaBear = PrimeFieldElement64<2_130_706_433>;

    /// Goldilocks, `2^64 - 2^32 + 1`.
    type Goldilocks = Zp18446744069414584321;

    /// The decomposition of a handful of small orders, worked out by hand.
    #[test]
    fn test_two_adic_decomposition_of_small_orders() {
        // q = 2: q - 1 = 1 = 2^0 * 1.
        assert_eq!(two_adic_decomposition(&[2]), (0, vec![1]));
        // q = 3: q - 1 = 2 = 2^1 * 1.
        assert_eq!(two_adic_decomposition(&[3]), (1, vec![1]));
        // q = 13: q - 1 = 12 = 2^2 * 3.
        assert_eq!(two_adic_decomposition(&[13]), (2, vec![3]));
        // q = 97: q - 1 = 96 = 2^5 * 3.
        assert_eq!(two_adic_decomposition(&[97]), (5, vec![3]));
        // q = 65537: q - 1 = 2^16 * 1.
        assert_eq!(two_adic_decomposition(&[65537]), (16, vec![1]));
    }

    /// A borrow across limbs: q = 2^64 + 1, so q - 1 = 2^64 = 2^64 * 1.
    #[test]
    fn test_two_adic_decomposition_borrows_across_limbs() {
        assert_eq!(two_adic_decomposition(&[1, 1]), (64, vec![1]));
        // q = 2^128 + 1, where the borrow runs through two limbs.
        assert_eq!(two_adic_decomposition(&[1, 0, 1]), (128, vec![1]));
        // q = 2^64, so q - 1 fills the low limb and the odd part is q - 1 itself.
        assert_eq!(two_adic_decomposition(&[0, 1]), (0, vec![u64::MAX, 0]));
    }

    /// `2^s * m` recovers `q - 1`, and m is odd.
    ///
    /// The independent check on the whole decomposition: it is recomputed with `BigUInt`
    /// multiplication and shifting, which share no code with the limb walk above.
    fn decomposition_reconstructs_the_group_order<F: KnownOrder>() {
        let (s, odd_part) = two_adic_decomposition(F::order_limbs());
        let group_order = &BigUInt::new(F::order_limbs()) - &BigUInt::one();
        let m = BigUInt::new(&odd_part);

        assert_eq!(&m << s as usize, group_order, "2^s * m is not q - 1");
        assert_eq!(
            &m % &BigUInt::new_from_u64(2),
            BigUInt::one(),
            "the odd part {m} is even, so s = {s} is not the full two-adicity"
        );
    }

    /// Every prime field in the crate decomposes `q - 1` consistently.
    #[test]
    fn test_decomposition_reconstructs_the_group_order() {
        decomposition_reconstructs_the_group_order::<Zp13>();
        decomposition_reconstructs_the_group_order::<Zp65537>();
        decomposition_reconstructs_the_group_order::<Zp2147483647>();
        decomposition_reconstructs_the_group_order::<KoalaBear>();
        decomposition_reconstructs_the_group_order::<Goldilocks>();
        decomposition_reconstructs_the_group_order::<Bn254Fr>();
        decomposition_reconstructs_the_group_order::<Bls12_381Fr>();
    }

    /// The two-adicity of each field of interest, against the value its modulus implies.
    ///
    /// `docs/MILESTONE-LARGE-PRIME-FIELDS.md` §7 records 28 for BN254 and 32 for BLS12-381 as a
    /// note. These are computed from the compiled-in moduli instead, and
    /// `test_decomposition_reconstructs_the_group_order` is what makes that computation
    /// trustworthy.
    #[test]
    fn test_the_two_adicity_of_each_target_field() {
        // 2^31 - 1 is a Mersenne prime: q - 1 = 2 * (2^30 - 1), so there is no NTT here beyond
        // size two. This is the field most of the crate's F4 benchmarks use.
        assert_eq!(Zp2147483647::two_adicity(), 1);
        // 2^31 - 2^24 + 1, chosen for exactly this property.
        assert_eq!(KoalaBear::two_adicity(), 24);
        // 2^64 - 2^32 + 1.
        assert_eq!(Goldilocks::two_adicity(), 32);
        // 2^16 + 1.
        assert_eq!(Zp65537::two_adicity(), 16);
        assert_eq!(Bn254Fr::two_adicity(), 28);
        assert_eq!(Bls12_381Fr::two_adicity(), 32);
    }

    /// A `2^log_n`-th root of unity has order exactly `2^log_n`, not merely dividing it.
    fn roots_have_exact_order<F: KnownOrder>(seed: u64, highest: u32) {
        let mut rng = StdRng::seed_from_u64(seed);
        let s = F::two_adicity();

        for log_n in 0..=highest.min(s) {
            let w: F = two_adic_root_of_unity(log_n, &mut rng);
            let n = 1u128 << log_n;
            assert!(
                w.pow(n).is_one(),
                "w^{n} != 1 in a field of two-adicity {s}"
            );
            if log_n > 0 {
                assert!(
                    !w.pow(n / 2).is_one(),
                    "w^{} = 1, so w is not a primitive {n}-th root",
                    n / 2
                );
            }
        }
    }

    /// Roots of unity have exact order over every field, including the two wide ones.
    #[test]
    fn test_two_adic_roots_have_exact_order() {
        roots_have_exact_order::<Zp13>(1, 8);
        roots_have_exact_order::<Zp65537>(2, 8);
        roots_have_exact_order::<Zp2147483647>(3, 8);
        roots_have_exact_order::<KoalaBear>(4, 8);
        roots_have_exact_order::<Goldilocks>(5, 8);
        roots_have_exact_order::<Bn254Fr>(6, 8);
        roots_have_exact_order::<Bls12_381Fr>(7, 8);
    }

    /// At the two-adicity itself a root exists, and `w^(2^(s-1))` is -1 — the group's involution.
    #[test]
    fn test_a_root_exists_at_the_full_two_adicity() {
        let mut rng = StdRng::seed_from_u64(11);
        let s = Bn254Fr::two_adicity();
        let w: Bn254Fr = two_adic_root_of_unity(s, &mut rng);

        let mut x = w;
        for _ in 0..s - 1 {
            x = x * x;
        }
        assert_eq!(x, Bn254Fr::zero() - Bn254Fr::one());
        assert!((x * x).is_one());
    }

    /// Beyond the two-adicity there is no such root, and that is a panic rather than a wrong value.
    #[test]
    #[should_panic(expected = "the two-adicity of this field is 28")]
    fn test_beyond_the_two_adicity_panics() {
        let mut rng = StdRng::seed_from_u64(13);
        let _: Bn254Fr = two_adic_root_of_unity(29, &mut rng);
    }

    /// The only first root of unity is 1, even in a field with no two-adicity at all.
    #[test]
    fn test_the_first_root_of_unity_is_one() {
        let mut rng = StdRng::seed_from_u64(17);
        assert!(two_adic_root_of_unity::<Zp2147483647, _>(0, &mut rng).is_one());
        assert!(two_adic_root_of_unity::<Bn254Fr, _>(0, &mut rng).is_one());
        // GF(2) has q - 1 = 1, so its two-adicity is zero and 1 is all there is.
        assert!(two_adic_root_of_unity::<PrimeFieldElement64<2>, _>(0, &mut rng).is_one());
    }

    /// The powers of a `2^log_n`-th root are n distinct elements summing to zero.
    ///
    /// The cyclotomic identity `1 + w + ... + w^(n-1) = 0`, which holds for a primitive n-th root
    /// and fails for any other n-th root of unity. Checked over a wide field, where it is the
    /// property the NTT depends on.
    #[test]
    fn test_the_powers_of_a_root_sum_to_zero() {
        let mut rng = StdRng::seed_from_u64(19);
        for log_n in 1..=10u32 {
            let w: Bn254Fr = two_adic_root_of_unity(log_n, &mut rng);
            let n = 1usize << log_n;

            let mut power = Bn254Fr::one();
            let mut sum = Bn254Fr::zero();
            let mut seen = std::collections::HashSet::new();
            for _ in 0..n {
                sum += power;
                assert!(seen.insert(power), "the powers of w repeat before w^{n}");
                power *= w;
            }
            assert!(power.is_one(), "w^{n} != 1");
            assert!(sum.is_zero(), "the powers of w do not sum to zero");
        }
    }
}
