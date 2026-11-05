//! Modular exponentiation of univariate polynomials.
//!
//! `Polynomial::pow` raises a polynomial to a power outright, so its result has degree
//! `n * deg(base)`. That is unusable for the exponents that matter in polynomial factorization:
//! finding the roots of `f` in GF(q) starts from `gcd(f, x^q - x)`, and `x^q` alone would have
//! q coefficients — around 2^61 of them for a 61-bit prime field.
//!
//! Reducing modulo `f` after every squaring keeps the degree below `deg(f)` throughout, so the
//! cost depends on `log(exponent)` rather than on the exponent itself.

use crate::{
    integers::{bit, highest_set_bit},
    poly::univariate::{Polynomial, UnivariatePolynomial},
    FiniteField,
};

/// `base^exponent mod modulus`, by square-and-multiply.
///
/// # Panics
/// Panics if `modulus` is the zero polynomial.
pub fn pow_mod<F: FiniteField>(
    base: &UnivariatePolynomial<F>,
    exponent: u128,
    modulus: &UnivariatePolynomial<F>,
) -> UnivariatePolynomial<F> {
    pow_mod_limbs(base, &[exponent as u64, (exponent >> 64) as u64], modulus)
}

/// `base^exponent mod modulus`, with the exponent as little-endian 64-bit limbs.
///
/// The exponents root finding and factorization need are q, `q - 1` and `(q - 1) / 2`, none of
/// which fits in a machine integer for a 254-bit field. Limbs carry all of them, and the cost is
/// unchanged: one squaring per bit of the exponent, so `O(log q)` polynomial multiplications
/// rather than anything proportional to q itself.
///
/// Trailing zero limbs cost nothing — the loop stops at the highest set bit — so a caller may
/// pass a fixed-width order without padding the work.
///
/// # Panics
/// Panics if `modulus` is the zero polynomial.
pub fn pow_mod_limbs<F: FiniteField>(
    base: &UnivariatePolynomial<F>,
    exponent: &[u64],
    modulus: &UnivariatePolynomial<F>,
) -> UnivariatePolynomial<F> {
    assert!(
        !modulus.is_zero(),
        "the modulus must be a nonzero polynomial"
    );

    // Reducing the identity is not redundant: modulo a nonzero constant, F[x]/(c) is the zero
    // ring, where 1 and 0 coincide. Starting from an unreduced `one` would wrongly report 1.
    let mut result = reduce(&UnivariatePolynomial::one(), modulus);

    let Some(highest) = highest_set_bit(exponent) else {
        // A zero exponent leaves the identity, reduced.
        return result;
    };

    let mut square = reduce(base, modulus);
    for index in 0..=highest {
        if bit(exponent, index) {
            result = reduce(&(&result * &square), modulus);
        }
        // The last squaring would be discarded, and for a wide exponent it is not cheap.
        if index < highest {
            square = reduce(&(&square * &square), modulus);
        }
    }

    result
}

/// The remainder of `p` on division by `modulus`.
fn reduce<F: FiniteField>(
    p: &UnivariatePolynomial<F>,
    modulus: &UnivariatePolynomial<F>,
) -> UnivariatePolynomial<F> {
    p.div(modulus).1
}

#[cfg(test)]
mod tests {
    use crate::{
        fields::PrimeFieldElement64,
        identities::Zero,
        poly::univariate::{
            pow_mod::{pow_mod, pow_mod_limbs},
            Polynomial, UnivariatePolynomial,
        },
        FiniteField,
    };

    type F = PrimeFieldElement64<7>;
    type P = UnivariatePolynomial<F>;

    /// The polynomial with the given coefficients, lowest order first.
    fn poly(coefficients: &[u64]) -> P {
        UnivariatePolynomial::new(&coefficients.iter().map(|c| F::new(*c)).collect::<Vec<_>>())
    }

    /// For exponents small enough to compute both ways, `pow_mod` agrees with `pow` then reduce.
    ///
    /// `pow` is untouched existing code that never reduces, so this is an independent check on
    /// the whole square-and-multiply loop rather than a restatement of it.
    #[test]
    fn test_pow_mod_agrees_with_pow_then_reduce() {
        let moduli = [poly(&[1, 0, 1]), poly(&[6, 1, 1, 1]), poly(&[3, 2])];
        let bases = [poly(&[0, 1]), poly(&[1, 1]), poly(&[2, 0, 3]), poly(&[5])];

        for modulus in &moduli {
            for base in &bases {
                for exponent in 0..=12u32 {
                    let expected = base.pow(exponent).div(modulus).1;
                    assert_eq!(
                        pow_mod(base, exponent as u128, modulus),
                        expected,
                        "base {} exponent {} modulus {}",
                        base,
                        exponent,
                        modulus
                    );
                }
            }
        }
    }

    /// The result always has degree below the modulus, which is what bounds the cost.
    #[test]
    fn test_pow_mod_stays_reduced() {
        let modulus = poly(&[1, 0, 1]); // x^2 + 1
        for exponent in [0u128, 1, 2, 3, 47, 48, 49, 1_000_000] {
            let result = pow_mod(&poly(&[0, 1]), exponent, &modulus);
            assert!(
                result.is_zero() || result.degree() < modulus.degree(),
                "exponent {} left degree {}",
                exponent,
                result.degree()
            );
        }
    }

    /// Exponents are additive: `b^(i+j) = b^i * b^j`.
    #[test]
    fn test_pow_mod_is_multiplicative_in_the_exponent() {
        let modulus = poly(&[6, 1, 1, 1]);
        let base = poly(&[1, 1]);
        for i in 0..8u128 {
            for j in 0..8u128 {
                let combined = pow_mod(&base, i + j, &modulus);
                let separate = (&pow_mod(&base, i, &modulus) * &pow_mod(&base, j, &modulus))
                    .div(&modulus)
                    .1;
                assert_eq!(combined, separate, "i = {}, j = {}", i, j);
            }
        }
    }

    /// With `f` irreducible of degree d over GF(q), the quotient F[x]/(f) is the field GF(q^d),
    /// so every element satisfies a^(q^d) = a.
    ///
    /// A theorem about the quotient ring rather than a property of this implementation, so it
    /// pins the answer independently.
    #[test]
    fn test_pow_mod_satisfies_frobenius() {
        // x^2 + 1 over GF(7): irreducible because it has no root, as asserted below.
        let modulus = poly(&[1, 0, 1]);
        for a in 0..7u64 {
            assert!(
                !modulus.eval(&F::new(a)).is_zero(),
                "{} is a root, so the modulus is not irreducible",
                a
            );
        }

        let q_to_the_d = 49u128; // |GF(7^2)|
        for c0 in 0..7u64 {
            for c1 in 0..7u64 {
                let a = poly(&[c0, c1]);
                assert_eq!(
                    pow_mod(&a, q_to_the_d, &modulus),
                    a.div(&modulus).1,
                    "a = {}",
                    a
                );
            }
        }
    }

    /// An exponent far beyond what `pow` could represent, whose value theory still determines.
    #[test]
    fn test_pow_mod_handles_an_exponent_pow_cannot() {
        let modulus = poly(&[1, 0, 1]); // x^2 + 1 over GF(7), so the quotient is GF(49)
        let x = poly(&[0, 1]);

        // x is a unit: x * (-x) = -x^2 = 1. The multiplicative group of GF(49) has order 48, so
        // the order of x divides 48 and x^(48k) = 1. Computing x^48000000 with `pow` would mean
        // materializing a polynomial of that degree.
        assert!(pow_mod(&x, 48 * 1_000_000, &modulus).is_one());
        assert!(pow_mod(&x, 48, &modulus).is_one());

        // x^(48k + 1) = x.
        assert_eq!(pow_mod(&x, 48 * 1_000_000 + 1, &modulus), x);
    }

    /// Modulo a nonzero constant the quotient ring is trivial, so every power is zero.
    #[test]
    fn test_pow_mod_by_a_constant_is_zero() {
        let modulus = poly(&[5]);
        for exponent in [0u128, 1, 7, 1_000] {
            assert!(pow_mod(&poly(&[1, 1]), exponent, &modulus).is_zero());
        }
    }

    /// The zero polynomial is not a valid modulus.
    #[test]
    #[should_panic(expected = "modulus must be a nonzero polynomial")]
    fn test_pow_mod_by_zero_panics() {
        let _ = pow_mod(&poly(&[1, 1]), 3, &UnivariatePolynomial::zero());
    }

    /// The limb form agrees with the `u128` one, which is the contract the wrapper rests on.
    #[test]
    fn test_pow_mod_limbs_agrees_with_the_u128_exponent() {
        let modulus = poly(&[6, 1, 1, 1]);
        let base = poly(&[2, 3, 1]);
        for exponent in [0u128, 1, 2, 3, 17, 64, 255, 1 << 40, u64::MAX as u128] {
            let limbs = [exponent as u64, (exponent >> 64) as u64];
            assert_eq!(
                pow_mod(&base, exponent, &modulus),
                pow_mod_limbs(&base, &limbs, &modulus),
                "exponent {exponent}"
            );
        }
    }

    /// An exponent above 2^128, which the `u128` form cannot express at all.
    ///
    /// `base^(2^192)` is reached by squaring 192 times, so it is checkable against a loop that
    /// does exactly that without going through the limb bit-walk.
    #[test]
    fn test_pow_mod_limbs_handles_an_exponent_beyond_u128() {
        let modulus = poly(&[6, 1, 1, 1]);
        let base = poly(&[2, 3, 1]);

        // 2^192 as limbs: the fourth limb's lowest bit.
        let exponent = [0u64, 0, 0, 1];

        let mut expected = base.div(&modulus).1;
        for _ in 0..192 {
            expected = (&expected * &expected).div(&modulus).1;
        }
        assert_eq!(pow_mod_limbs(&base, &exponent, &modulus), expected);
    }

    /// Trailing zero limbs do not change the result, so a fixed-width order needs no trimming.
    #[test]
    fn test_trailing_zero_limbs_are_ignored() {
        let modulus = poly(&[6, 1, 1, 1]);
        let base = poly(&[2, 3, 1]);
        let expected = pow_mod_limbs(&base, &[37], &modulus);
        for padded in [vec![37u64, 0], vec![37, 0, 0], vec![37, 0, 0, 0, 0]] {
            assert_eq!(pow_mod_limbs(&base, &padded, &modulus), expected);
        }
    }

    /// A zero exponent gives the identity, reduced — including modulo a constant.
    #[test]
    fn test_a_zero_exponent_gives_the_reduced_identity() {
        let base = poly(&[2, 3, 1]);
        assert_eq!(
            pow_mod_limbs(&base, &[0, 0, 0, 0], &poly(&[6, 1, 1, 1])),
            UnivariatePolynomial::one()
        );
        // Modulo a nonzero constant the quotient ring is trivial, so 1 and 0 coincide.
        assert!(pow_mod_limbs(&base, &[0], &poly(&[3])).is_zero());
    }
}
