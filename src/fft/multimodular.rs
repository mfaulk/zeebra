//! Polynomial multiplication over a word-size prime field with no usable two-adic root (#1226).
//!
//! A field such as `2^64 - 59` has two-adicity 2, so no power-of-two transform of useful size
//! exists in it and [`multiply`](super::multiply) used to fall back to Karatsuba at every degree.
//! This route never transforms in the target field. It lifts the coefficients to integers in
//! `[0, p)`, computes their integer product modulo `k` NTT-friendly 64-bit primes (one transform
//! each), recombines the `k` residues by the Chinese remainder theorem in Garner's mixed-radix form,
//! and reduces the result into the target field. The technique is textbook (von zur Gathen and
//! Gerhard, *Modern Computer Algebra*, §8.3), and FLINT and NTL both multiply over a general modulus
//! this way. The code here is written from that description, not from either library.
//!
//! # The coefficient bound
//!
//! With `a_i` and `b_j` lifted to `[0, p - 1]`, coefficient `c_t = sum_{i + j = t} a_i b_j` of the
//! integer product has at most `m = min(len a, len b)` terms, so `0 <= c_t <= m (p - 1)^2`. CRT
//! over primes whose product is `M` determines `c_t mod M`, and that is `c_t` itself exactly when
//! `m (p - 1)^2 < M`. [`auxiliary_prime_count`] takes the smallest prefix of [`AUXILIARY_PRIMES`]
//! for which that holds, checked in exact 256-bit arithmetic, and refuses when none does.
//!
//! The refusal is defensive for the lengths the transforms admit. A product has at most `2^32`
//! coefficients, because Goldilocks' two-adicity of 32 bounds the transform. So `m < 2^32` and
//! `m (p - 1)^2 < 2^160`, while the three primes multiply to more than `2^191`. One prime suffices
//! for a tiny `p`, two up to about `2^48` at any admitted length, and three for the rest of the word.

use std::fmt::{Display, Formatter};

use crate::{
    fft::{powers_of, transform::transform_in_place},
    fields::PrimeFieldElement64,
    FiniteField, Polynomial, UnivariatePolynomial,
};

/// The auxiliary primes, in the order the planner takes them. Each is `2^64 - 2^e + 1`.
///
/// Goldilocks first because its own reduction is cheaper than Montgomery's (#781), and every
/// product uses the first prime.
pub const AUXILIARY_PRIMES: [u64; 3] = [Q1, Q2, Q3];

/// `2^64 - 2^32 + 1`, Goldilocks. Two-adicity 32.
const Q1: u64 = 18_446_744_069_414_584_321;
/// `2^64 - 2^34 + 1`. Two-adicity 34.
const Q2: u64 = 18_446_744_056_529_682_433;
/// `2^64 - 2^40 + 1`. Two-adicity 40.
const Q3: u64 = 18_446_742_974_197_923_841;

type F1 = PrimeFieldElement64<Q1>;
type F2 = PrimeFieldElement64<Q2>;
type F3 = PrimeFieldElement64<Q3>;

/// `log2` of the largest transform every auxiliary prime hosts: the smallest two-adicity, Q1's.
pub const MAX_LOG_POINTS: u32 = 32;

/// Why the multi-modular product refused. Every variant is a fact about the field or the lengths.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MultimodularError {
    /// The field reports no [`FiniteField::word_residue`]: it is not a prime field of
    /// characteristic below `2^64`.
    NotAWordPrimeField,

    /// The product has more coefficients than the auxiliary primes' transforms can hold.
    TooLong { points: usize, max_points: u64 },

    /// No prefix of [`AUXILIARY_PRIMES`] multiplies to more than `terms (p - 1)^2`.
    CoefficientBoundExceeded { terms: usize },
}

impl Display for MultimodularError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NotAWordPrimeField => {
                write!(f, "the field is not a prime field of characteristic below 2^64")
            }
            Self::TooLong { points, max_points } => write!(
                f,
                "a product of {points} coefficients exceeds the {max_points} the auxiliary primes \
                 can transform"
            ),
            Self::CoefficientBoundExceeded { terms } => write!(
                f,
                "a coefficient summing {terms} terms can exceed the product of every auxiliary prime"
            ),
        }
    }
}

impl std::error::Error for MultimodularError {}

/// The product of `a` and `b` through [`AUXILIARY_PRIMES`] and the Chinese remainder theorem.
///
/// Equal to `a * b` whenever it returns `Ok`. Bounded on [`FiniteField`] alone, so a caller without
/// [`KnownOrder`](crate::KnownOrder) can reach it; the modulus is read off
/// [`FiniteField::word_residue`].
///
/// # Errors
/// [`MultimodularError`] for a field that is not a word-size prime field, a product too long for
/// the transforms, or a coefficient bound no prefix of the primes exceeds.
pub fn try_multiply_multimodular<F: FiniteField>(
    a: &UnivariatePolynomial<F>,
    b: &UnivariatePolynomial<F>,
) -> Result<UnivariatePolynomial<F>, MultimodularError> {
    let p_minus_one = (-F::one())
        .word_residue()
        .ok_or(MultimodularError::NotAWordPrimeField)?;
    if a.is_zero() || b.is_zero() {
        return Ok(UnivariatePolynomial::zero());
    }
    let (a, b) = (a.coefficients(), b.coefficients());
    transform_log_size(a.len() + b.len() - 1)?;
    let terms = a.len().min(b.len());
    let count = auxiliary_prime_count(p_minus_one, terms)
        .ok_or(MultimodularError::CoefficientBoundExceeded { terms })?;
    Ok(UnivariatePolynomial::from_coefficients(
        multiply_with_prime_count(a, b, count)?,
    ))
}

/// The fewest [`AUXILIARY_PRIMES`] whose product exceeds `terms (p - 1)^2`, or `None`.
///
/// Exact: both sides are formed in four 64-bit limbs, which hold `terms (p - 1)^2 < 2^192` and the
/// product of all three primes.
pub(crate) fn auxiliary_prime_count(p_minus_one: u64, terms: usize) -> Option<usize> {
    let square = mul_limbs(mul_limbs([1, 0, 0, 0], p_minus_one), p_minus_one);
    let bound = mul_limbs(square, terms as u64);
    let mut modulus = [1, 0, 0, 0];
    for (count, &q) in AUXILIARY_PRIMES.iter().enumerate() {
        modulus = mul_limbs(modulus, q);
        if less_than(bound, modulus) {
            return Some(count + 1);
        }
    }
    None
}

/// `x * y` over little-endian limbs. Every call site stays below `2^256`, so no carry is lost.
fn mul_limbs(x: [u64; 4], y: u64) -> [u64; 4] {
    let mut out = [0; 4];
    let mut carry = 0u128;
    for (o, &limb) in out.iter_mut().zip(&x) {
        let wide = u128::from(limb) * u128::from(y) + carry;
        *o = wide as u64;
        carry = wide >> 64;
    }
    debug_assert_eq!(carry, 0, "a limb product overflowed 256 bits");
    out
}

/// `x < y` over little-endian limbs.
fn less_than(x: [u64; 4], y: [u64; 4]) -> bool {
    x.iter().rev().lt(y.iter().rev())
}

/// The `log2` of the transform a product of `points` coefficients needs.
fn transform_log_size(points: usize) -> Result<u32, MultimodularError> {
    let too_long = MultimodularError::TooLong {
        points,
        max_points: 1 << MAX_LOG_POINTS,
    };
    let Some(size) = points.checked_next_power_of_two() else {
        return Err(too_long);
    };
    let log_size = size.trailing_zeros();
    if log_size > MAX_LOG_POINTS {
        return Err(too_long);
    }
    Ok(log_size)
}

/// The product over exactly the first `count` auxiliary primes, with no bound check.
///
/// Separate from [`try_multiply_multimodular`] so the tests can show the bound is necessary, by
/// running with one prime fewer than the planner chose. Both operands are nonempty.
fn multiply_with_prime_count<F: FiniteField>(
    a: &[F],
    b: &[F],
    count: usize,
) -> Result<Vec<F>, MultimodularError> {
    let lift = |c: &[F]| -> Result<Vec<u64>, MultimodularError> {
        c.iter()
            .map(|x| {
                x.word_residue()
                    .ok_or(MultimodularError::NotAWordPrimeField)
            })
            .collect()
    };
    let (a, b) = (lift(a)?, lift(b)?);
    let log_size = transform_log_size(a.len() + b.len() - 1)?;

    // Garner's mixed radix: the integer is `v1 + v2 Q1 + v3 Q1 Q2` with `v_i` in `[0, Q_i)`, and
    // each `v_i` is fixed by the residue modulo `Q_i` and the digits before it. Reduced into F term
    // by term, which is where `Q1 mod p` and `Q1 Q2 mod p` come from; `new` reduces mod p.
    let q1 = F::new(Q1);
    let q12 = q1 * F::new(Q2);
    let r1 = cyclic_product::<F1>(&a, &b, log_size);
    let out = match count {
        1 => r1.iter().map(|x| F::new(x.value())).collect(),
        2 => {
            let r2 = cyclic_product::<F2>(&a, &b, log_size);
            let inv_q1_mod_q2 = F2::new(Q1).inverse();
            r1.iter()
                .zip(&r2)
                .map(|(x1, x2)| {
                    let v1 = x1.value();
                    let v2 = ((*x2 - F2::new(v1)) * inv_q1_mod_q2).value();
                    F::new(v1) + F::new(v2) * q1
                })
                .collect()
        }
        3 => {
            let r2 = cyclic_product::<F2>(&a, &b, log_size);
            let r3 = cyclic_product::<F3>(&a, &b, log_size);
            let inv_q1_mod_q2 = F2::new(Q1).inverse();
            let inv_q1_mod_q3 = F3::new(Q1).inverse();
            let inv_q2_mod_q3 = F3::new(Q2).inverse();
            r1.iter()
                .zip(&r2)
                .zip(&r3)
                .map(|((x1, x2), x3)| {
                    let v1 = x1.value();
                    let v2 = ((*x2 - F2::new(v1)) * inv_q1_mod_q2).value();
                    let t = (*x3 - F3::new(v1)) * inv_q1_mod_q3;
                    let v3 = ((t - F3::new(v2)) * inv_q2_mod_q3).value();
                    F::new(v1) + F::new(v2) * q1 + F::new(v3) * q12
                })
                .collect()
        }
        _ => unreachable!("there are {} auxiliary primes", AUXILIARY_PRIMES.len()),
    };
    Ok(out)
}

/// The product of the integer sequences `a` and `b` modulo the auxiliary prime of `Q`, through a
/// transform of `2^log_size` points, truncated to `len a + len b - 1`.
///
/// `2^log_size` is at least that length, so the cyclic product does not wrap.
fn cyclic_product<Q: FiniteField>(a: &[u64], b: &[u64], log_size: u32) -> Vec<Q> {
    let size = 1usize << log_size;
    let root = Q::transform_root_of_unity(log_size)
        .expect("every auxiliary prime hosts a transform of 2^MAX_LOG_POINTS points");
    let domain = powers_of(&root, size);
    let forward = |c: &[u64]| {
        let mut values = vec![Q::zero(); size];
        for (v, &x) in values.iter_mut().zip(c) {
            *v = Q::new(x);
        }
        transform_in_place(&mut values, &domain);
        values
    };
    let mut values = forward(a);
    {
        let other = forward(b);
        for (v, w) in values.iter_mut().zip(&other) {
            *v *= *w;
        }
    }
    // The inverse transform runs over `w^{-i} = w^{size - i}`, the same table read backwards.
    let inverse: Vec<Q> = (0..size).map(|i| domain[(size - i) % size]).collect();
    drop(domain);
    transform_in_place(&mut values, &inverse);
    values.truncate(a.len() + b.len() - 1);
    // Odd modulus, so the power of two is invertible.
    let scale = Q::new(size as u64).inverse();
    for v in values.iter_mut() {
        *v *= scale;
    }
    values
}

#[cfg(test)]
mod tests {
    use rand::{prelude::StdRng, CryptoRng, RngCore, SeedableRng};

    use super::*;
    use crate::{
        fields::{
            Bn254Fr, Gf13Pow4, Gf256, Mersenne31, Zp1091, Zp18446744073709551263,
            Zp18446744073709551557, Zp2147483647, Zp7,
        },
        poly::multiply_dense,
        test_support::schoolbook_product,
        KnownOrder,
    };

    /// A 61-bit prime of two-adicity 1 placed so that two auxiliary primes cover a coefficient of
    /// up to 99 worst-case terms and not 100: `floor((Q1 Q2 - 1) / (p - 1)^2) = 99`.
    const BOUNDARY_PRIME: u64 = 1_844_674_406_297_213_347;
    type Boundary = PrimeFieldElement64<BOUNDARY_PRIME>;

    fn random_polynomial<F: FiniteField, R: RngCore + CryptoRng>(
        len: usize,
        rng: &mut R,
    ) -> UnivariatePolynomial<F> {
        let mut coefficients: Vec<F> = (0..len).map(|_| F::random(rng)).collect();
        while coefficients[len - 1].is_zero() {
            coefficients[len - 1] = F::random(rng);
        }
        UnivariatePolynomial::new(&coefficients)
    }

    /// Every coefficient `p - 1`, the input that maximizes every coefficient of the integer product.
    fn worst_case<F: FiniteField>(len: usize) -> UnivariatePolynomial<F> {
        UnivariatePolynomial::new(&vec![-F::one(); len])
    }

    /// The product of two all-`(p - 1)` polynomials in closed form: `(p - 1)^2 = 1 mod p`, so
    /// coefficient `t` is its number of terms.
    fn worst_case_product<F: FiniteField>(la: usize, lb: usize) -> UnivariatePolynomial<F> {
        let coefficients: Vec<F> = (0..la + lb - 1)
            .map(|t| {
                let low = t.saturating_sub(lb - 1);
                let high = t.min(la - 1);
                F::new((high - low + 1) as u64)
            })
            .collect();
        UnivariatePolynomial::new(&coefficients)
    }

    /// Lengths around the Karatsuba base cases, the power-of-two boundaries of the transform size,
    /// and the dispatcher's crossover, in equal and unequal pairs.
    const LENGTH_PAIRS: [(usize, usize); 16] = [
        (1, 1),
        (1, 2),
        (2, 1),
        (3, 5),
        (16, 17),
        (17, 16),
        (32, 33),
        (48, 49),
        (64, 65),
        (100, 1),
        (1, 300),
        (128, 129),
        (129, 128),
        (255, 258),
        (256, 257),
        (700, 333),
    ];

    /// The multi-modular product is the schoolbook and the Karatsuba product, coefficient for
    /// coefficient, over one field.
    fn agrees_with_schoolbook_and_karatsuba<F: KnownOrder>(seed: u64) {
        let mut rng = StdRng::seed_from_u64(seed);
        for &(la, lb) in &LENGTH_PAIRS {
            let a = random_polynomial::<F, _>(la, &mut rng);
            let b = random_polynomial::<F, _>(lb, &mut rng);
            let product = try_multiply_multimodular(&a, &b).expect("a word-size prime field");
            assert_eq!(product, schoolbook_product(&a, &b), "lengths {la}, {lb}");
            assert_eq!(product, multiply_dense(&a, &b), "lengths {la}, {lb}");
        }
    }

    #[test]
    fn test_the_product_agrees_with_schoolbook_and_karatsuba_on_low_two_adicity_primes() {
        assert_eq!(Zp18446744073709551557::two_adicity(), 2);
        assert_eq!(Zp18446744073709551263::two_adicity(), 1);
        assert_eq!(Mersenne31::two_adicity(), 1);
        assert_eq!(Boundary::two_adicity(), 1);
        agrees_with_schoolbook_and_karatsuba::<Zp18446744073709551557>(1);
        agrees_with_schoolbook_and_karatsuba::<Zp18446744073709551263>(2);
        agrees_with_schoolbook_and_karatsuba::<Boundary>(3);
        agrees_with_schoolbook_and_karatsuba::<Zp2147483647>(4);
        agrees_with_schoolbook_and_karatsuba::<Mersenne31>(5);
        agrees_with_schoolbook_and_karatsuba::<Zp1091>(6);
        agrees_with_schoolbook_and_karatsuba::<Zp7>(7);
    }

    /// All-`(p - 1)` operands, the largest integer coefficients there are, against both the
    /// closed form and Karatsuba.
    fn worst_case_agrees<F: KnownOrder>(pairs: &[(usize, usize)]) {
        for &(la, lb) in pairs {
            let a = worst_case::<F>(la);
            let b = worst_case::<F>(lb);
            let product = try_multiply_multimodular(&a, &b).expect("a word-size prime field");
            assert_eq!(
                product,
                worst_case_product::<F>(la, lb),
                "lengths {la}, {lb}"
            );
            assert_eq!(product, multiply_dense(&a, &b), "lengths {la}, {lb}");
        }
    }

    #[test]
    fn test_worst_case_coefficients_are_recovered_exactly() {
        let pairs = [
            (1, 1),
            (99, 99),
            (100, 100),
            (101, 7),
            (513, 1025),
            (2048, 2048),
        ];
        worst_case_agrees::<Zp18446744073709551557>(&pairs);
        worst_case_agrees::<Zp18446744073709551263>(&pairs);
        worst_case_agrees::<Boundary>(&pairs);
        worst_case_agrees::<Mersenne31>(&pairs);
        worst_case_agrees::<Zp7>(&pairs);
    }

    /// The largest product this suite runs: `2^17 - 1` coefficients from two operands of `2^16`,
    /// checked against the closed form because Karatsuba at this length is slow in a debug build.
    /// The supported maximum, `2^32` coefficients, is the planner's to enforce; see
    /// `test_the_transform_size_stops_at_the_auxiliary_two_adicity`.
    #[test]
    fn test_a_long_worst_case_product_is_exact() {
        let len = 1 << 16;
        let a = worst_case::<Zp18446744073709551557>(len);
        let product = try_multiply_multimodular(&a, &a).unwrap();
        assert_eq!(product, worst_case_product(len, len));
    }

    /// The number of primes grows with the field: one for a tiny prime, two for a 31-bit one,
    /// three for a 64-bit one.
    #[test]
    fn test_the_prime_count_follows_the_field_size() {
        assert_eq!(auxiliary_prime_count(6, 1 << 20), Some(1));
        assert_eq!(auxiliary_prime_count((1 << 31) - 2, 1 << 20), Some(2));
        assert_eq!(auxiliary_prime_count(u64::MAX - 59, 1), Some(3));
        assert_eq!(auxiliary_prime_count(u64::MAX - 59, 1 << 32), Some(3));
    }

    /// The bound is exact: the boundary prime takes two primes at 99 worst-case terms and three
    /// at 100.
    #[test]
    fn test_the_prime_count_switches_exactly_at_the_bound() {
        let p_minus_one = BOUNDARY_PRIME - 1;
        assert_eq!(auxiliary_prime_count(p_minus_one, 99), Some(2));
        assert_eq!(auxiliary_prime_count(p_minus_one, 100), Some(3));
        // The figure the doc comment states, in u128: Q1 Q2 < 2^128.
        let square = u128::from(p_minus_one) * u128::from(p_minus_one);
        assert_eq!((u128::from(Q1) * u128::from(Q2) - 1) / square, 99);
    }

    /// The bound is necessary, not merely sufficient: with one prime fewer than the planner chose,
    /// the worst case past the boundary comes out wrong, and the same count is right below it.
    #[test]
    fn test_one_prime_fewer_than_the_bound_requires_is_wrong() {
        let below = worst_case::<Boundary>(99);
        let product = multiply_with_prime_count(below.coefficients(), below.coefficients(), 2);
        assert_eq!(
            UnivariatePolynomial::new(&product.unwrap()),
            worst_case_product::<Boundary>(99, 99)
        );

        let past = worst_case::<Boundary>(100);
        let product = multiply_with_prime_count(past.coefficients(), past.coefficients(), 2);
        assert_ne!(
            UnivariatePolynomial::new(&product.unwrap()),
            worst_case_product::<Boundary>(100, 100)
        );
        // Through the public route the planner takes the third prime, and the product is right.
        assert_eq!(
            try_multiply_multimodular(&past, &past).unwrap(),
            worst_case_product::<Boundary>(100, 100)
        );
    }

    /// A bound no prefix of the primes exceeds is refused rather than computed wrong.
    #[test]
    fn test_an_unmeetable_bound_is_refused() {
        // (2^64 - 2)^2 (2^64 - 1) is about 2^192 - 5 * 2^128, above Q1 Q2 Q3 ~ 2^192 - 2^168.
        assert_eq!(auxiliary_prime_count(u64::MAX - 1, u64::MAX as usize), None);
    }

    /// The transform size stops at `2^32` points, Goldilocks' two-adicity.
    #[test]
    fn test_the_transform_size_stops_at_the_auxiliary_two_adicity() {
        assert_eq!(transform_log_size(1), Ok(0));
        assert_eq!(transform_log_size(3), Ok(2));
        assert_eq!(transform_log_size(1 << 20), Ok(20));
        assert_eq!(transform_log_size((1 << 20) + 1), Ok(21));
        assert_eq!(transform_log_size(1 << 32), Ok(32));
        assert_eq!(
            transform_log_size((1 << 32) + 1),
            Err(MultimodularError::TooLong {
                points: (1 << 32) + 1,
                max_points: 1 << 32,
            })
        );
        assert_eq!(
            transform_log_size(usize::MAX),
            Err(MultimodularError::TooLong {
                points: usize::MAX,
                max_points: 1 << 32,
            })
        );
    }

    /// Each auxiliary prime hosts the largest transform the planner admits.
    #[test]
    fn test_every_auxiliary_prime_hosts_the_largest_transform() {
        assert_eq!(F1::two_adicity(), 32);
        assert_eq!(F2::two_adicity(), 34);
        assert_eq!(F3::two_adicity(), 40);
        assert!(F1::transform_root_of_unity(MAX_LOG_POINTS).is_some());
        assert!(F2::transform_root_of_unity(MAX_LOG_POINTS).is_some());
        assert!(F3::transform_root_of_unity(MAX_LOG_POINTS).is_some());
    }

    /// A field that is not a word-size prime field is refused: wide, binary, and extension.
    #[test]
    fn test_a_field_without_a_word_residue_is_refused() {
        fn refused<F: FiniteField>() {
            let a = UnivariatePolynomial::new(&[F::one(), F::one()]);
            assert_eq!(
                try_multiply_multimodular(&a, &a),
                Err(MultimodularError::NotAWordPrimeField)
            );
        }
        refused::<Bn254Fr>();
        refused::<Gf256>();
        refused::<Gf13Pow4>();
    }

    /// `word_residue` is the residue `new` maps back from, over both word widths.
    #[test]
    fn test_the_word_residue_round_trips_through_new() {
        fn round_trips<F: FiniteField>(values: &[u64]) {
            for &v in values {
                let x = F::new(v);
                let r = x.word_residue().expect("a word-size prime field");
                assert_eq!(F::new(r), x);
                assert_eq!(r, (-F::one()).word_residue().map(|m| v % (m + 1)).unwrap());
            }
        }
        round_trips::<Mersenne31>(&[0, 1, 2, (1 << 31) - 2, (1 << 31) - 1, u64::MAX]);
        round_trips::<Zp18446744073709551557>(&[0, 1, u64::MAX - 59, u64::MAX - 58, u64::MAX]);
        round_trips::<Zp7>(&[0, 6, 7, 13]);
    }

    #[test]
    fn test_a_zero_operand_gives_zero() {
        let a = worst_case::<Zp18446744073709551557>(5);
        let zero = UnivariatePolynomial::<Zp18446744073709551557>::zero();
        assert!(try_multiply_multimodular(&a, &zero).unwrap().is_zero());
        assert!(try_multiply_multimodular(&zero, &a).unwrap().is_zero());
    }
}
