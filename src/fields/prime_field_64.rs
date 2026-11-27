//! Prime-order finite field.
//!
//! For each prime p, the finite field F_p is defined to be the quotient ring Z/pZ.
//!
//! Elements are held in Montgomery form when P is odd, at least 2^32 and not Goldilocks, so that
//! multiplication needs no division. `mul` used to compute `(a as u128 * b as u128) % P as u128`, and a
//! const-generic modulus does not save that: LLVM does not strength-reduce a 128-bit remainder, so
//! every multiplication compiled to a call to `__umodti3`, compiler-rt's software 128-bit division.
//! Montgomery reduction replaces it with two multiplications and a shift. See [`montgomery`] for
//! the representation and the invariant it carries.
//!
//! Below 2^32 the product of two residues fits a `u64`, and a `u64` remainder by a constant *is*
//! strength-reduced, to a multiply by a precomputed reciprocal. Those moduli keep canonical
//! residues, and 2^31 - 1 reduces by shift and add instead. Goldilocks, 2^64 - 2^32 + 1, is also
//! canonical: its modulus makes 2^64 = 2^32 - 1 and 2^96 = -1, which reduce a 128-bit product with
//! one multiply by 2^32 - 1 and carry fixes (#781). Measured in
//! `docs/research/field-arithmetic-specialization.md` (#270, #781).

use std::{
    fmt::{Display, Formatter},
    ops,
};

#[cfg(any(test, feature = "proptest"))]
use proptest::prelude::{any, Arbitrary, BoxedStrategy, Strategy};
use rand::{CryptoRng, Rng, RngCore};
use serde::{Deserialize, Serialize};

use crate::{
    fields::{trim_limbs, KnownOrder, PreparedFactor, RootOfUnityError},
    identities::{One, Zero},
    impl_add_variants, impl_div_variants, impl_mul_variants, impl_sub_variants,
    integers::{big_uint::BigUInt, factor, find_generator, limbs_minus_two},
    FiniteField, ParseFieldElementError, Ring,
};

/// Montgomery arithmetic modulo an odd P, with R = 2^64.
///
/// An element `a` is stored as `a * R mod P`. The map is a ring isomorphism for addition and
/// subtraction — `aR + bR = (a + b)R` — so those operations are untouched by the change of
/// representation and are not duplicated here. Only multiplication and the conversions differ.
///
/// R = 2^64 requires `gcd(P, R) = 1`, which for a power of two means P must be odd. P = 2 is a
/// legitimate modulus for this type and is used by the GF(2) Gröbner tests, so an even modulus
/// keeps a remainder path, as does every modulus below 2^32, and Goldilocks has its own reduction.
/// [`uses_montgomery`] is the one predicate that decides, and
/// because P is a const generic every branch on it folds away at compile time.
mod montgomery {
    /// Whether modulus `p` is represented in Montgomery form.
    ///
    /// Odd moduli only: R = 2^64 is not invertible modulo an even number. And only from 2^32 up:
    /// below that the product fits a `u64`, whose remainder by a constant is cheaper than a
    /// reduction over a 128-bit product. Goldilocks is excluded because its special form reduces
    /// a canonical product more cheaply than Montgomery does (#781).
    pub const fn uses_montgomery(p: u64) -> bool {
        p % 2 == 1 && p >> 32 != 0 && p != super::GOLDILOCKS
    }

    /// `-P^{-1} mod 2^64`, the factor that makes the low limb of `t + m*P` vanish.
    ///
    /// Newton's iteration for the inverse of an odd number modulo a power of two doubles the
    /// number of correct bits each step: starting from one bit, six steps reach 64. Requires `p`
    /// odd; for even `p` the result is meaningless but harmless, since every caller is guarded by
    /// [`uses_montgomery`] and the arithmetic here only wraps.
    pub const fn n_prime(p: u64) -> u64 {
        let mut inverse: u64 = 1;
        let mut step = 0;
        while step < 6 {
            // x <- x * (2 - p*x), which is exact modulo 2^(2k) when x is exact modulo 2^k.
            inverse = inverse.wrapping_mul(2u64.wrapping_sub(p.wrapping_mul(inverse)));
            step += 1;
        }
        inverse.wrapping_neg()
    }

    /// `R^2 mod P`, which converts a canonical residue into Montgomery form via one reduction.
    ///
    /// Computed as `(R mod P)^2 mod P` so the intermediate stays inside a `u128`: `R mod P` is
    /// below 2^64, so its square is below 2^128. This runs at compile time, so the wide remainder
    /// it uses costs nothing at run time.
    pub const fn r2_mod_p(p: u64) -> u64 {
        let r = ((1u128 << 64) % p as u128) as u64;
        ((r as u128 * r as u128) % p as u128) as u64
    }

    /// Montgomery reduction: `t * R^{-1} mod P`, for `t < P * R`.
    ///
    /// `m` is chosen so that `t + m*P` is divisible by R, which makes the division by R a shift.
    /// The quotient is below 2P, so one conditional subtraction finishes the reduction.
    ///
    /// `t + m*P` can need 129 bits when P is close to 2^64, which is why the addition is done with
    /// `overflowing_add` rather than in a `u128` that would silently wrap. On overflow the true
    /// sum is `2^128 + sum`, so the true quotient is `(sum >> 64) + 2^64`; that exceeds P, and
    /// subtracting P brings it back below 2^64, which `wrapping_sub` computes exactly. The low 64
    /// bits of the true sum are zero by construction, so the shift loses nothing.
    #[inline(always)]
    pub const fn redc<const P: u64>(t: u128) -> u64 {
        let m = (t as u64).wrapping_mul(n_prime(P));
        let (sum, carry) = t.overflowing_add(m as u128 * P as u128);
        let high = (sum >> 64) as u64;
        if carry {
            // The quotient is 2^64 + high, which is above P; the difference fits in 64 bits.
            high.wrapping_sub(P)
        } else if high >= P {
            high - P
        } else {
            high
        }
    }

    /// `a * b * R^{-1} mod P`, which is the product in Montgomery form when both inputs are.
    ///
    /// `(aR)(bR) * R^{-1} = (ab)R`, so the representation is preserved.
    #[inline(always)]
    pub const fn mul<const P: u64>(a: u64, b: u64) -> u64 {
        redc::<P>(a as u128 * b as u128)
    }

    /// A canonical residue in [0,P) to the internal representation.
    #[inline(always)]
    pub const fn to_internal<const P: u64>(canonical: u64) -> u64 {
        if uses_montgomery(P) {
            mul::<P>(canonical, r2_mod_p(P))
        } else {
            canonical
        }
    }

    /// The internal representation back to a canonical residue in [0,P).
    #[inline(always)]
    pub const fn to_canonical<const P: u64>(internal: u64) -> u64 {
        if uses_montgomery(P) {
            redc::<P>(internal as u128)
        } else {
            internal
        }
    }
}

/// Shoup's multiplication by a fixed factor, for the Montgomery moduli below 2^63 (#779).
///
/// With `f` canonical and `w = floor(f * 2^64 / P)`, the estimate `floor(x * w / 2^64)` of
/// `floor(x * f / P)` is low by at most one, so `x * f - q * P` lies in `[0, 2P)`: one wrapping
/// multiply-subtract and a conditional subtraction, against Montgomery's two full products. `2P`
/// must fit a `u64`, hence the bound. `x` may be in Montgomery form: `(aR) * f mod P = (af)R`, the
/// Montgomery form of the product, so the representation is untouched and only the factor is
/// converted, once per [`PreparedFactor`].
mod shoup {
    /// Whether `prepare_factor` records Shoup's words for modulus `p`. Below 2^32 the residues
    /// are canonical and their own product is already cheap, so those keep the plain multiply.
    pub const fn applies(p: u64) -> bool {
        super::montgomery::uses_montgomery(p) && p >> 63 == 0
    }

    /// `floor(f * 2^64 / P)` for a canonical `f < P`; below 2^64 because `f < P`.
    #[inline]
    pub fn quotient<const P: u64>(f: u64) -> u64 {
        (((f as u128) << 64) / P as u128) as u64
    }

    /// `x * f mod P`, for `x < P` and `w = quotient(f)`.
    #[inline(always)]
    pub fn mul<const P: u64>(x: u64, f: u64, w: u64) -> u64 {
        let q = ((x as u128 * w as u128) >> 64) as u64;
        let r = x.wrapping_mul(f).wrapping_sub(q.wrapping_mul(P));
        if r >= P {
            r - P
        } else {
            r
        }
    }
}

#[derive(Copy, Clone, Debug, Default, Eq, Hash, PartialEq, Deserialize, Serialize)]
/// Element of a prime field with prime modulus P.
pub struct PrimeFieldElement64<const P: u64> {
    /// The element's internal representation: `a * 2^64 mod P` for the moduli
    /// `montgomery::uses_montgomery` selects (odd, at least 2^32, not Goldilocks), and the
    /// canonical residue `a` otherwise. [`value`](Self::value) converts back; nothing else should read this
    /// field expecting a residue.
    ///
    /// Private so that neither the reduced-residue invariant nor the choice of representation can
    /// be broken from outside: every operation here assumes the stored value is below P, and
    /// `PartialEq` and `Hash` are derived over it. Deriving them over the Montgomery form is
    /// sound because the map is a bijection on [0,P), so two elements are equal in one
    /// representation exactly when they are equal in the other.
    ///
    /// Deserialization is the one construction path that bypasses a constructor, so it validates
    /// rather than trusting its input, and converts. Add and sub reduce by conditional
    /// subtraction, which assumes the operands are already reduced: `sub` would pass an unreduced
    /// value straight through, and `add` would still be unreduced for any input at or above 2P.
    #[serde(
        serialize_with = "canonical_residue::<_, P>",
        deserialize_with = "reduced_residue::<_, P>"
    )]
    value: u64,
}

/// Accepts a representative only if it is already reduced modulo P, then converts it.
///
/// Rejecting rather than reducing: a value outside [0,P) did not come from this field, so it
/// signals either corruption or a mismatched modulus, and silently reinterpreting it would hide
/// that. The wire format is the canonical residue in both directions, so the representation change
/// is invisible to a stored or transmitted element.
fn reduced_residue<'de, D, const P: u64>(deserializer: D) -> Result<u64, D::Error>
where
    D: serde::Deserializer<'de>,
{
    let value = u64::deserialize(deserializer)?;
    if value >= P {
        return Err(serde::de::Error::custom(format!(
            "{value} is not a reduced residue modulo {P}"
        )));
    }
    Ok(montgomery::to_internal::<P>(value))
}

/// Writes the canonical residue, whatever the internal representation is.
///
/// Paired with [`reduced_residue`] so that the serialized form is the mathematical value. Without
/// this the derived implementation would emit the Montgomery form, which would both change the
/// format and be rejected on the way back in by any peer that reduced differently.
fn canonical_residue<S, const P: u64>(value: &u64, serializer: S) -> Result<S::Ok, S::Error>
where
    S: serde::Serializer,
{
    serializer.serialize_u64(montgomery::to_canonical::<P>(*value))
}

impl<const P: u64> PrimeFieldElement64<P> {
    /// The element's representative integer in [0,p-1].
    ///
    /// For a Montgomery modulus this is a reduction, not a field read, so a hot loop should
    /// hold field elements rather than call this per iteration.
    pub fn value(&self) -> u64 {
        montgomery::to_canonical::<P>(self.value)
    }
}

impl<const P: u64> Zero for PrimeFieldElement64<P> {
    // Zero is a fixed point of the Montgomery map, so this needs no conversion.
    const ZERO: Self = Self { value: 0 };
}

impl<const P: u64> One for PrimeFieldElement64<P> {
    // One is not a fixed point: in Montgomery form it is R mod P.
    const ONE: Self = Self {
        value: montgomery::to_internal::<P>(1),
    };
}

impl<const P: u64> Ring for PrimeFieldElement64<P> {}

impl<const P: u64> FiniteField for PrimeFieldElement64<P> {
    fn concurrent_elimination() -> Option<crate::linalg::concurrent::Dispatch<Self>> {
        Some(crate::linalg::concurrent::Dispatch::new())
    }

    fn run_concurrent<J: crate::fields::ConcurrentJob<Self>>(job: J) -> Result<J::Output, J> {
        Ok(job.run())
    }

    fn prime31_lane() -> Option<crate::linalg::lane::Lane<Self>> {
        if P <= crate::linalg::lane::MAX_LANE_PRIME as u64
            || P > crate::linalg::lane::MAX_LANE31_PRIME as u64
        {
            return None;
        }
        // The stored representative, Montgomery or not, is below P < 2^31 and linear.
        crate::linalg::lane::Lane::new_31(
            P as u32,
            |element| element.value as u32,
            |raw| Self {
                value: u64::from(raw),
            },
            |element| element.value() as u32,
        )
    }

    fn new(val: u64) -> Self {
        Self {
            value: montgomery::to_internal::<P>(val % P),
        }
    }

    fn from_str(value: &str) -> Result<Self, ParseFieldElementError> {
        let parsed = BigUInt::from_dec_str(value)?;
        let modulus = BigUInt::new_from_u64(P);
        let residue = parsed % &modulus;
        let words = residue.as_le_words();
        assert!(words.len() <= 1);

        Ok(Self {
            value: montgomery::to_internal::<P>(*words.first().unwrap_or(&0)),
        })
    }

    fn random<R: RngCore + CryptoRng>(rng: &mut R) -> Self {
        let value = rng.gen_range(0..P);
        Self::new(value)
    }

    fn transform_root_of_unity(log_n: u32) -> Option<Self> {
        crate::fields::two_adic::deterministic_two_adic_root(log_n)
    }

    fn word_residue(&self) -> Option<u64> {
        Some(self.value())
    }

    fn inverse(&self) -> Self {
        assert_ne!(
            *self,
            Self::zero(),
            "The zero element does not have a multiplicative inverse."
        );
        self.pow_limbs(&Self::FERMAT_EXPONENT_LIMBS)
    }

    #[inline]
    fn prepare_factor(&self) -> PreparedFactor<Self> {
        if shoup::applies(P) {
            let f = self.value();
            PreparedFactor::with_words(*self, [f, shoup::quotient::<P>(f)])
        } else {
            PreparedFactor::plain(*self)
        }
    }

    #[inline]
    fn mul_prepared(&self, factor: &PreparedFactor<Self>) -> Self {
        if shoup::applies(P) {
            let [f, w] = factor.words();
            Self {
                value: shoup::mul::<P>(self.value, f, w),
            }
        } else {
            *self * factor.element()
        }
    }
}

impl<const P: u64> PrimeFieldElement64<P> {
    /// The order q = p of the field, as little-endian limbs. See [`KnownOrder::order_limbs`].
    const ORDER_LIMBS: [u64; 1] = [P];

    /// The Fermat inversion exponent q - 2, as little-endian limbs.
    ///
    /// Subtracted on the limbs rather than on a machine integer, and held at the width of
    /// [`Self::ORDER_LIMBS`], so nothing here caps the order at the width of a `u128`.
    const FERMAT_EXPONENT_LIMBS: [u64; 1] = limbs_minus_two(Self::ORDER_LIMBS);
}

impl<const P: u64> KnownOrder for PrimeFieldElement64<P> {
    fn order_limbs() -> &'static [u64] {
        trim_limbs(&Self::ORDER_LIMBS)
    }

    fn characteristic_limbs() -> &'static [u64] {
        // Prime order, so q = p and k = 1.
        trim_limbs(&Self::ORDER_LIMBS)
    }

    fn try_primitive_element<R: RngCore + CryptoRng>(
        rng: &mut R,
    ) -> Result<Self, RootOfUnityError> {
        // See Algorithm 4.80 of Handbook of Applied Cryptography.
        let n = BigUInt::new_from_u64(P - 1);
        let (prime_factors, powers) = factor(&n, rng);
        let generator = find_generator(&prime_factors, &powers, rng);
        // Convert generator to an integer in [0,P).
        assert!(generator <= n);
        let value = generator.as_le_words()[0];
        Ok(Self {
            value: montgomery::to_internal::<P>(value),
        })
    }

    fn try_root_of_unity<R: RngCore + CryptoRng>(
        n: u64,
        rng: &mut R,
    ) -> Result<Self, RootOfUnityError> {
        let group_order = P as u128 - 1;
        if n == 0 || !group_order.is_multiple_of(n as u128) {
            return Err(RootOfUnityError::OrderDoesNotDivide { n });
        }

        let x = Self::try_primitive_element(rng)?;
        Ok(x.pow(group_order / n as u128))
    }
}

/// Display
impl<const P: u64> Display for PrimeFieldElement64<P> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value())
    }
}

/// Borrowed + Borrowed
impl<const P: u64> ops::Add<&PrimeFieldElement64<P>> for &PrimeFieldElement64<P> {
    type Output = PrimeFieldElement64<P>;

    fn add(self, rhs: &PrimeFieldElement64<P>) -> Self::Output {
        // Both operands are reduced, so their sum is below 2P and a single conditional
        // subtraction reduces it. `overflowing_add` keeps this entirely in 64 bits even when P is
        // close to 2^64: on carry the true sum is 2^64 + sum, and the wrapping subtraction of P
        // yields exactly that less P. A 128-bit remainder costs an order of magnitude more.
        let (sum, carry) = self.value.overflowing_add(rhs.value);
        let value = if carry || sum >= P {
            sum.wrapping_sub(P)
        } else {
            sum
        };
        PrimeFieldElement64 { value }
    }
}

impl_add_variants!([const P: u64], PrimeFieldElement64<P>);

/// 2^31 - 1, which gets a shift-and-add reduction: 25% off MQ10's F4 call over the narrow remainder's
/// 7% (#270).
const MERSENNE_31: u64 = (1 << 31) - 1;

/// 2^64 - 2^32 + 1, held canonically and reduced by [`reduce_goldilocks`] (#781).
const GOLDILOCKS: u64 = 0xFFFF_FFFF_0000_0001;

/// `t mod (2^64 - 2^32 + 1)` for any `t < 2^128`, by 2^64 = 2^32 - 1 and 2^96 = -1.
///
/// Splitting `t = hi_hi * 2^96 + hi_lo * 2^64 + lo` gives `t = lo - hi_hi + hi_lo * (2^32 - 1)`.
/// A borrow in the subtraction is a lost -2^64, corrected by subtracting 2^32 - 1; it cannot wrap
/// again, because after a borrow the difference is at least `2^64 - 2^32`. A carry in the addition
/// is a lost 2^64, corrected by adding 2^32 - 1; that cannot wrap either, because
/// `hi_lo * (2^32 - 1) <= 2^64 - 2^33 + 1`. The result is then below 2^64 < 2P, so one
/// conditional subtraction makes it canonical.
#[inline(always)]
const fn reduce_goldilocks(t: u128) -> u64 {
    const EPSILON: u64 = 0xFFFF_FFFF;
    let (lo, hi) = (t as u64, (t >> 64) as u64);
    let (hi_hi, hi_lo) = (hi >> 32, hi & EPSILON);
    let (mut r, borrow) = lo.overflowing_sub(hi_hi);
    if borrow {
        r = r.wrapping_sub(EPSILON);
    }
    let (mut r, carry) = r.overflowing_add(hi_lo * EPSILON);
    if carry {
        r = r.wrapping_add(EPSILON);
    }
    if r >= GOLDILOCKS {
        r - GOLDILOCKS
    } else {
        r
    }
}

/// Borrowed * Borrowed
impl<const P: u64> ops::Mul<&PrimeFieldElement64<P>> for &PrimeFieldElement64<P> {
    type Output = PrimeFieldElement64<P>;

    fn mul(self, rhs: &PrimeFieldElement64<P>) -> Self::Output {
        // Both operands carry the same factor of R, and Montgomery reduction removes exactly one
        // of them, so the product is in the same representation as the inputs. Below 2^32 the
        // residues are canonical and their product fits a u64, whose remainder by a constant LLVM
        // lowers to a reciprocal multiply. Goldilocks is canonical too, with its own reduction. The
        // wide remainder survives only for an even modulus of 2^32 or more, which is never prime.
        // Every branch is on a const generic.
        let value = if montgomery::uses_montgomery(P) {
            montgomery::mul::<P>(self.value, rhs.value)
        } else if P == GOLDILOCKS {
            reduce_goldilocks(self.value as u128 * rhs.value as u128)
        } else if P == MERSENNE_31 {
            // 2^31 = 1 mod P. With t <= (P-1)^2 < 2^62 the folded sum is at most 2P - 1, since
            // reaching 2P would need t = 2^62 - 1; one conditional subtraction finishes it.
            let t = self.value * rhs.value;
            let r = (t & P) + (t >> 31);
            if r >= P {
                r - P
            } else {
                r
            }
        } else if P >> 32 == 0 {
            (self.value * rhs.value) % P
        } else {
            ((self.value as u128 * rhs.value as u128) % P as u128) as u64
        };
        Self::Output { value }
    }
}

impl_mul_variants!([const P: u64], PrimeFieldElement64<P>);

/// Borrowed - Borrowed
impl<const P: u64> ops::Sub for &PrimeFieldElement64<P> {
    type Output = PrimeFieldElement64<P>;

    fn sub(self, rhs: Self) -> Self::Output {
        // On borrow the difference is negative, and adding P brings it back into range. Replaces
        // a signed 128-bit euclidean remainder.
        let (difference, borrow) = self.value.overflowing_sub(rhs.value);
        let value = if borrow {
            difference.wrapping_add(P)
        } else {
            difference
        };
        Self::Output { value }
    }
}

impl_sub_variants!([const P: u64], PrimeFieldElement64<P>);

impl<const P: u64> ops::Neg for PrimeFieldElement64<P> {
    type Output = PrimeFieldElement64<P>;

    fn neg(self) -> Self::Output {
        Self::zero() - self
    }
}

impl<const P: u64> ops::Neg for &PrimeFieldElement64<P> {
    type Output = PrimeFieldElement64<P>;

    fn neg(self) -> Self::Output {
        PrimeFieldElement64::zero() - self
    }
}

/// Borrowed / Borrowed
impl<const P: u64> ops::Div<Self> for &PrimeFieldElement64<P> {
    type Output = PrimeFieldElement64<P>;

    fn div(self, rhs: Self) -> Self::Output {
        // Division is multiplication by the inverse modulo p.
        self * rhs.inverse()
    }
}

impl_div_variants!([const P: u64], PrimeFieldElement64<P>);

#[cfg(any(test, feature = "proptest"))]
impl<const P: u64> Arbitrary for PrimeFieldElement64<P> {
    type Parameters = ();

    fn arbitrary_with(_args: Self::Parameters) -> Self::Strategy {
        any::<u64>().prop_map(Self::new).boxed()
    }

    type Strategy = BoxedStrategy<Self>;
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use proptest::{arbitrary::Arbitrary, prelude::any, prop_assert_eq, proptest};
    use rand::{prelude::StdRng, thread_rng, SeedableRng};

    use crate::{
        fields::{
            finite_field::fermat_inverse_via_recursive_pow, PrimeFieldElement64, Zp1091, Zp13,
            Zp18446744069414584321, Zp18446744073709551557, Zp2147483647, Zp541, Zp65537, Zp7,
        },
        identities::{One, Zero},
        FiniteField, KnownOrder, ParseFieldElementError,
    };

    /// Multiplication agrees with reducing the full 128-bit product by a wide remainder.
    ///
    /// The oracle is the textbook formula `(a * b) % P` in 128 bits. This is the characterization
    /// test for the internal representation: Montgomery form changes what `value` holds, and the
    /// only thing that must not change is what `value()` reports. Boundary values matter most —
    /// with P near 2^64 the product spans the full 128 bits, which is where a reduction gets the
    /// high limb wrong. An even modulus is included because Montgomery multiplication requires an
    /// odd one, so GF(2) exercises the fallback rather than the fast path.
    #[test]
    fn test_multiplication_matches_wide_reduction() {
        fn check<const P: u64>(values: &[u64]) {
            for &a in values {
                for &b in values {
                    let (x, y) = (
                        PrimeFieldElement64::<P>::new(a),
                        PrimeFieldElement64::<P>::new(b),
                    );
                    let expected = ((x.value() as u128 * y.value() as u128) % P as u128) as u64;
                    assert_eq!(
                        (x * y).value(),
                        expected,
                        "P = {}: {} * {}",
                        P,
                        x.value(),
                        y.value()
                    );
                }
            }
        }

        // Exhaustive over small fields, including an even modulus for the fallback path.
        check::<2>(&[0, 1]);
        check::<3>(&(0..3).collect::<Vec<_>>());
        let small: Vec<u64> = (0..7).collect();
        check::<7>(&small);
        let small: Vec<u64> = (0..13).collect();
        check::<13>(&small);

        // Goldilocks, 2^64 - 2^32 + 1.
        const GOLDILOCKS: u64 = 18446744069414584321;
        check::<GOLDILOCKS>(&[
            0,
            1,
            2,
            0xFFFF_FFFF,
            1 << 32,
            GOLDILOCKS / 2,
            GOLDILOCKS - 2,
            GOLDILOCKS - 1,
        ]);

        // The largest 64-bit prime, where the product uses the full 128 bits.
        const BIG: u64 = 18446744073709551557;
        check::<BIG>(&[0, 1, 2, BIG / 2, BIG - 3, BIG - 2, BIG - 1]);

        // 2^64 - 353, the modulus the Anemoi reference data is over. Odd, so Montgomery form
        // applies with no new arithmetic; it is here because an Anemoi model was the first caller
        // to instantiate this width at a modulus that was not already covered.
        const ANEMOI: u64 = 18446744073709551263;
        check::<ANEMOI>(&[0, 1, 2, ANEMOI / 2, ANEMOI - 3, ANEMOI - 2, ANEMOI - 1]);

        // 2^31 - 1, where the product stays inside 62 bits.
        check::<2147483647>(&[0, 1, 2, 1073741823, 2147483645, 2147483646]);

        // The largest prime below 2^32, where a narrow product reaches (2^32 - 6)^2 and only just
        // fits a u64; and the smallest prime above it, which must take the Montgomery path.
        const NARROW_MAX: u64 = 4294967291;
        check::<NARROW_MAX>(&[0, 1, 2, 1 << 31, NARROW_MAX - 2, NARROW_MAX - 1]);
        const WIDE_MIN: u64 = 4294967311;
        check::<WIDE_MIN>(&[0, 1, 2, 1 << 32, WIDE_MIN - 2, WIDE_MIN - 1]);
        check::<1481823929>(&[0, 1, 2, 740911964, 1481823927, 1481823928]);
    }

    /// A modulus below 2^32 is stored as its canonical residue, and one above it in Montgomery form.
    #[test]
    fn test_moduli_below_two_to_the_32_are_held_canonically() {
        assert!(!super::montgomery::uses_montgomery(2147483647));
        assert!(!super::montgomery::uses_montgomery(4294967291));
        assert!(!super::montgomery::uses_montgomery(7));
        assert!(super::montgomery::uses_montgomery(4294967311));
        assert!(super::montgomery::uses_montgomery(18446744073709551557));
        assert_eq!(PrimeFieldElement64::<2147483647>::new(5).value, 5);
        assert_eq!(
            PrimeFieldElement64::<4294967291>::new(u64::MAX).value,
            u64::MAX % 4294967291
        );
    }

    proptest! {
        /// Multiplication matches the wide-reduction oracle over random input, near the boundary.
        #[test]
        fn test_multiplication_matches_wide_reduction_randomly(a in any::<u64>(), b in any::<u64>()) {
            const BIG: u64 = 18446744073709551557;
            let (x, y) = (PrimeFieldElement64::<BIG>::new(a), PrimeFieldElement64::<BIG>::new(b));
            let expected = ((x.value() as u128 * y.value() as u128) % BIG as u128) as u64;
            prop_assert_eq!((x * y).value(), expected);

            const GOLDILOCKS: u64 = 18446744069414584321;
            let (x, y) = (
                PrimeFieldElement64::<GOLDILOCKS>::new(a),
                PrimeFieldElement64::<GOLDILOCKS>::new(b),
            );
            let expected = ((x.value() as u128 * y.value() as u128) % GOLDILOCKS as u128) as u64;
            prop_assert_eq!((x * y).value(), expected);

            const NARROW_MAX: u64 = 4294967291;
            let (x, y) = (
                PrimeFieldElement64::<NARROW_MAX>::new(a),
                PrimeFieldElement64::<NARROW_MAX>::new(b),
            );
            let expected = ((x.value() as u128 * y.value() as u128) % NARROW_MAX as u128) as u64;
            prop_assert_eq!((x * y).value(), expected);

            let (x, y) = (Zp2147483647::new(a), Zp2147483647::new(b));
            let expected = ((x.value() as u128 * y.value() as u128) % 2147483647) as u64;
            prop_assert_eq!((x * y).value(), expected);
        }
    }

    /// The serialized bytes are the canonical residue, not whatever the internal representation is.
    ///
    /// The round-trip test below would pass even if the wire format silently became Montgomery
    /// form, because it only checks that encoding and decoding compose to the identity. This pins
    /// the bytes themselves against a plain `u64`, so a representation change cannot leak into the
    /// format a stored or transmitted element uses.
    #[test]
    fn test_the_wire_format_is_the_canonical_residue() {
        // 7 mod 13 is 7, and Montgomery form of 7 mod 13 is not 7, so the two disagree.
        assert_eq!(
            bincode::serialize(&Zp13::new(7)).unwrap(),
            bincode::serialize(&7u64).unwrap()
        );

        // Goldilocks, where the canonical value and the Montgomery value both span 64 bits.
        let value = 0xDEAD_BEEF_0000_1234u64;
        assert_eq!(
            bincode::serialize(&Zp18446744069414584321::new(value)).unwrap(),
            bincode::serialize(&value).unwrap()
        );

        // One is the case most likely to leak: in Montgomery form it is R mod P, not 1.
        assert_eq!(
            bincode::serialize(&Zp13::one()).unwrap(),
            bincode::serialize(&1u64).unwrap()
        );
        assert_eq!(
            bincode::serialize(&Zp13::zero()).unwrap(),
            bincode::serialize(&0u64).unwrap()
        );
    }

    /// `Display` shows the canonical residue, not the internal representation.
    #[test]
    fn test_display_shows_the_canonical_residue() {
        assert_eq!(format!("{}", Zp13::new(7)), "7");
        assert_eq!(format!("{}", Zp13::one()), "1");
        assert_eq!(format!("{}", Zp13::zero()), "0");
        assert_eq!(format!("{}", Zp13::new(20)), "7");
    }

    /// Elements built by different routes compare and hash as the same element.
    ///
    /// Every construction path has to agree on the representation. A path that forgot to convert
    /// would still produce a reduced-looking value, so equality across paths is what catches it.
    #[test]
    fn test_construction_paths_agree() {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};

        fn hash_of<T: Hash>(value: &T) -> u64 {
            let mut hasher = DefaultHasher::new();
            value.hash(&mut hasher);
            hasher.finish()
        }

        let direct = Zp13::new(7);
        let wrapped = Zp13::new(20); // 20 = 7 mod 13
        let parsed = Zp13::from_str("7").unwrap();
        let summed = Zp13::new(3) + Zp13::new(4);
        let decoded: Zp13 = bincode::deserialize(&bincode::serialize(&direct).unwrap()).unwrap();

        for other in [wrapped, parsed, summed, decoded] {
            assert_eq!(direct, other);
            assert_eq!(hash_of(&direct), hash_of(&other));
            assert_eq!(direct.value(), other.value());
        }

        // One and zero are identities under the operations, in whatever representation.
        assert!(Zp13::one().is_one());
        assert!(Zp13::zero().is_zero());
        assert_eq!(Zp13::new(7) * Zp13::one(), Zp13::new(7));
        assert_eq!(Zp13::new(7) + Zp13::zero(), Zp13::new(7));
        assert_eq!(Zp13::new(7) * Zp13::new(7).inverse(), Zp13::one());
    }

    /// Deserializing an unreduced representative is rejected rather than admitted.
    #[test]
    fn test_deserializing_an_unreduced_representative_is_rejected() {
        // 9 is congruent to 2 mod 7, but is not the representative this field uses. Admitting it
        // would break the invariant that addition and subtraction rely on.
        let encoded = bincode::serialize(&9u64).unwrap();
        let decoded: Result<Zp7, _> = bincode::deserialize(&encoded);
        assert!(decoded.is_err(), "9 should be rejected modulo 7");
    }

    /// The modulus itself is not a valid representative; P-1 is the largest one.
    #[test]
    fn test_deserializing_rejects_the_modulus_and_admits_p_minus_one() {
        let encoded = bincode::serialize(&7u64).unwrap();
        let decoded: Result<Zp7, _> = bincode::deserialize(&encoded);
        assert!(decoded.is_err(), "7 should be rejected modulo 7");

        let encoded = bincode::serialize(&6u64).unwrap();
        let decoded: Zp7 = bincode::deserialize(&encoded).expect("6 is a valid residue mod 7");
        assert_eq!(decoded.value(), 6);
    }

    /// Validating deserialization does not change the wire format: every element round-trips.
    #[test]
    fn test_serde_round_trip_is_unchanged() {
        for value in 0..7u64 {
            let element = Zp7::new(value);
            let encoded = bincode::serialize(&element).unwrap();
            let decoded: Zp7 = bincode::deserialize(&encoded).unwrap();
            assert_eq!(decoded, element);
        }

        // A value near the top of the range, where the largest 64-bit prime lives.
        let element = Zp18446744073709551557::new(u64::MAX);
        let encoded = bincode::serialize(&element).unwrap();
        let decoded: Zp18446744073709551557 = bincode::deserialize(&encoded).unwrap();
        assert_eq!(decoded, element);
    }

    /// Arithmetic on a deserialized element agrees with arithmetic on a constructed one.
    ///
    /// This is the defect the rejection prevents: the conditional add subtracts P at most once, so
    /// an unreduced input would have produced an unreduced output.
    #[test]
    fn test_deserialized_elements_arithmetic_agrees_with_constructed() {
        for value in 0..7u64 {
            let encoded = bincode::serialize(&value).unwrap();
            let decoded: Zp7 = bincode::deserialize(&encoded).unwrap();
            assert_eq!(decoded + Zp7::zero(), Zp7::new(value));
            assert_eq!(decoded - Zp7::zero(), Zp7::new(value));
            assert_eq!(decoded + Zp7::one(), Zp7::new(value + 1));
        }
    }

    #[test]
    // The default value should be zero.
    fn test_default_is_zero() {
        type F = PrimeFieldElement64<5807>;
        assert_eq!(F::default(), F::zero());
    }

    #[test]
    // Should parse a decimal string mod P.
    fn test_from_str() {
        type Zp = Zp1091;
        for x in 0..10000 {
            assert_eq!(Zp::new(x), Zp::from_str(&x.to_string()).unwrap());
        }
    }

    #[test]
    // random should not panic.
    fn test_random_does_not_panic() {
        let mut rng = thread_rng();
        for _i in 0..1000 {
            let _element = PrimeFieldElement64::<61>::random(&mut rng);
        }
    }

    /// Sampling is uniform over the whole field: a chi-squared test over every residue.
    #[test]
    fn test_random_distribution() {
        const P: u64 = 61;
        const DRAWS: usize = 200_000;

        let mut rng = StdRng::seed_from_u64(20);
        let mut counts = [0usize; P as usize];
        for _ in 0..DRAWS {
            counts[PrimeFieldElement64::<P>::random(&mut rng).value() as usize] += 1;
        }

        let expected = DRAWS as f64 / P as f64;
        let chi_squared: f64 = counts
            .iter()
            .map(|&count| {
                let deviation = count as f64 - expected;
                deviation * deviation / expected
            })
            .sum();

        // 99.6 is the 0.999 quantile of chi-squared with 60 degrees of freedom, so a uniform
        // sampler fails this once in a thousand seeds — and the seed is fixed.
        assert!(
            chi_squared < 99.6,
            "chi-squared {chi_squared:.1} over {P} residues: {counts:?}"
        );
    }

    // A non-zero element times its inverse must be 1.
    fn element_times_inverse_is_one<F: FiniteField>(element: &F) {
        if element.is_zero() {
            return;
        }
        let inverse = element.inverse();
        assert_eq!(*element * inverse, F::one());
    }

    proptest! {
        #[test]
        fn test_inverse_p_7(element in Zp7::arbitrary()) {
            element_times_inverse_is_one(&element);
        }

        #[test]
        fn test_inverse_p_541(element in Zp541::arbitrary()) {
            element_times_inverse_is_one(&element);
        }
    }

    #[test]
    #[should_panic(expected = "does not have a multiplicative inverse")]
    // Zero does not have a multiplicative inverse.
    fn test_inverse_of_zero() {
        type Zp = PrimeFieldElement64<7>;
        let element = Zp::new(0);
        let _inverse = element.inverse();
    }

    /// Every nonzero element of a small field inverts to exactly what the recursive-pow reference
    /// gives, over the internal representation and not merely up to the field axioms.
    #[test]
    fn test_inverse_is_bit_identical_to_the_reference_exhaustively() {
        fn check<const P: u64>() {
            for value in 1..P {
                let a = PrimeFieldElement64::<P>::new(value);
                assert_eq!(
                    a.inverse(),
                    fermat_inverse_via_recursive_pow(&a),
                    "P = {P}: {value}"
                );
            }
        }

        check::<7>();
        check::<541>();
        check::<65537>();
    }

    proptest! {
        /// Inversion is bit-identical to the recursive-pow reference at the moduli
        /// `for_each_field!` does not reach — including the largest 64-bit prime, which is the
        /// benchmark's `p64` and whose exponent fills a whole limb.
        #[test]
        fn test_inverse_is_bit_identical_to_the_reference(seed in any::<u64>()) {
            fn check<const P: u64>(seed: u64) {
                let a = PrimeFieldElement64::<P>::new(seed);
                if a.is_zero() {
                    return;
                }
                assert_eq!(a.inverse(), fermat_inverse_via_recursive_pow(&a), "P = {P}: {seed}");
            }

            check::<7>(seed);
            check::<541>(seed);
            check::<2147483647>(seed);
            check::<4611624995532046337>(seed);
            check::<18446744073709551557>(seed);
        }
    }

    fn addition_is_commutative<F: FiniteField>(a: F, b: F) {
        assert_eq!(a + b, b + a);
    }

    proptest! {

        #[test]
        fn test_addition_is_commutative_p_7(a in Zp7::arbitrary(), b in Zp7::arbitrary()) {
            addition_is_commutative(a, b);
        }

        #[test]
        fn test_addition_is_commutative_p_18446744073709551557(a in Zp18446744073709551557::arbitrary(), b in Zp18446744073709551557::arbitrary()) {
            addition_is_commutative(a, b);
        }
    }

    proptest! {
        #[test]
        fn test_addition_is_modulo_p(a in Zp65537::arbitrary(), b in Zp65537::arbitrary()) {
            let sum = a + b;
            assert!(sum.value < 65537);
        }
    }

    #[test]
    // Spot-check that subtraction produces correct values.
    fn test_sub() {
        type Zp = PrimeFieldElement64<7>;
        let a = Zp::new(3);
        let b = Zp::new(2);

        assert_eq!(a - a, Zp::new(0)); // 3 - 3 mod 7
        assert_eq!(a - b, Zp::new(1)); // 3 - 2 mod 7
        assert_eq!(b - a, Zp::new(6)); // 2 - 3 mod 7
    }

    #[test]
    // Spot-check that multiplication produces correct values.
    fn test_mul() {
        type Zp = PrimeFieldElement64<7>;
        let a = Zp::new(3);
        let b = Zp::new(2);

        assert_eq!(a * b, Zp::new(6)); // 3 * 2 mod 7

        let c = Zp::new(6);
        assert_eq!(a * c, Zp::new(4)); // 3 * 6 mod 7
    }

    #[test]
    // Multiply large values so the prod exceeds u64::MAX
    fn test_mul_large_values() {
        const P: u64 = (1u64 << 61) + 20 * (1u64 << 32) + 1; // 2^61 + 20*2^32 + 1
        type Zp = PrimeFieldElement64<P>;
        let a = Zp::new(2u64.pow(50));
        // a * a = 1758668848648192 = 2^100 (mod p)
        assert_eq!(a * a, Zp::new(1758668848648192));
    }

    fn multiplication_is_commutative<F: FiniteField>(a: F, b: F) {
        assert_eq!(a * b, b * a);
    }

    proptest! {
        #[test]
        fn test_multiplication_is_commutative_p_7(a in Zp7::arbitrary(), b in Zp7::arbitrary()) {
            multiplication_is_commutative(a, b);
        }

        #[test]
        fn test_multiplication_is_commutative_p_18446744073709551557(a in Zp18446744073709551557::arbitrary(), b in Zp18446744073709551557::arbitrary()) {
            multiplication_is_commutative(a, b);
        }
    }

    proptest! {
        #[test]
        fn test_multiplication_is_modulo_p(a in Zp65537::arbitrary(), b in Zp65537::arbitrary()) {
            let prod = a * b;
            assert!(prod.value < 65537);
        }
    }

    #[test]
    // x^0 = 1
    fn test_pow_zero() {
        type Zp = PrimeFieldElement64<2147483647>;
        let mut rng = StdRng::seed_from_u64(333378);
        let x = Zp::random(&mut rng);
        assert_eq!(x.pow(0), Zp::one());
    }

    #[test]
    // Spot-check that pow() correctly compute powers.
    fn test_pow() {
        type Zp = Zp2147483647;

        // `value()` rather than the private field: the expected numbers are canonical residues,
        // and the field holds the Montgomery form.
        let a = Zp::new(827376);
        assert_eq!(a.pow(1), a);
        assert_eq!(a.pow(2).value(), 1651245630);
        assert_eq!(a.pow(7).value(), 1787801728);
        assert_eq!(a.pow(43).value(), 263804505);
        assert_eq!(a.pow(196).value(), 1889125610);
    }

    #[test]
    // Spot-check that division produces correct values.
    fn test_div() {
        type Zp = PrimeFieldElement64<7>;
        let a = Zp::new(6);
        let b = Zp::new(2);
        assert_eq!(a / b, Zp::new(3)); // 6 / 2 mod 7
        assert_eq!(b / a, Zp::new(5)); // 2 / 6 mod 7
    }

    #[test]
    #[should_panic]
    // Dividing by zero should panic.
    fn test_div_by_zero_panics() {
        type Zp = Zp2147483647;
        let a = Zp::new(6);
        let _boom = a / Zp::zero();
    }

    #[test]
    // Powers of the primitive element generate all non-zero elements of the field.
    fn test_primitive_element() {
        const P: u64 = 73;
        type Zp = PrimeFieldElement64<P>;
        let mut rng = StdRng::seed_from_u64(87878);
        let alpha = Zp::primitive_element(&mut rng);
        let nonzero_elements: HashSet<Zp> = (1..P).into_iter().map(Zp::new).collect();
        assert!(nonzero_elements.contains(&alpha));

        let mut generated_elements: HashSet<Zp> = Default::default();
        // \alpha^x, x \in {0, 1, ..., P-2}
        for i in 0..=(P - 2) {
            generated_elements.insert(alpha.pow(i as u128));
        }
        assert_eq!(generated_elements, nonzero_elements);
    }

    #[test]
    // Should not return the trivial root.
    fn test_root_of_unity_is_not_one() {
        let mut rng = StdRng::seed_from_u64(88283746);
        type Zp = PrimeFieldElement64<541>;
        // 540 = 2^2 × 3^3 × 5
        for _i in 1..100 {
            assert_ne!(Zp::root_of_unity(2, &mut rng), Zp::one());
            assert_ne!(Zp::root_of_unity(3, &mut rng), Zp::one());
            assert_ne!(Zp::root_of_unity(5, &mut rng), Zp::one());
        }
    }

    #[test]
    // Should return an nth root of unity, r^n = 1.
    fn test_root_of_unity() {
        let mut rng = StdRng::seed_from_u64(88283746);
        type Zp = PrimeFieldElement64<541>;
        // 540 = 2^2 × 3^3 × 5
        for _i in 1..100 {
            let r_2 = Zp::root_of_unity(2, &mut rng);
            assert_eq!(r_2.pow(2), Zp::one());

            let r_3 = Zp::root_of_unity(3, &mut rng);
            assert_eq!(r_3.pow(3), Zp::one());

            let r_5 = Zp::root_of_unity(5, &mut rng);
            assert_eq!(r_5.pow(5), Zp::one());
        }
    }

    /// A primitive nth root of unity satisfies r^n = 1 and r^k != 1 for every 0 < k < n.
    #[test]
    fn test_root_of_unity_is_primitive() {
        type Zp = Zp541;
        let mut rng = StdRng::seed_from_u64(7);
        // 540 = 2^2 * 3^3 * 5, so these all divide the multiplicative group's order.
        for n in [2u64, 4, 5, 10, 27, 108] {
            let r = Zp::root_of_unity(n, &mut rng);
            assert_eq!(r.pow(n as u128), Zp::one(), "n = {}", n);
            for k in 1..n {
                assert_ne!(r.pow(k as u128), Zp::one(), "n = {}, k = {}", n, k);
            }
        }
    }

    /// The strategy is usable, equal values hash equally, and representatives stay below P.
    #[test]
    fn test_arbitrary_and_representation_are_sound() {
        use crate::test_support::{
            assert_hash_agrees_with_eq, assert_strategy_is_not_degenerate, draw,
        };
        let strategy = Zp541::arbitrary();
        assert_strategy_is_not_degenerate(&strategy, "PrimeFieldElement64");

        let mut values = draw(&strategy, 32);
        values.extend([Zp541::zero(), Zp541::one(), Zp541::default()]);
        assert_hash_agrees_with_eq(&values, "PrimeFieldElement64");

        for v in &values {
            assert!(v.value < 541, "{:?} is not reduced", v);
        }
    }

    /// A parse failure reports which character was rejected, rather than only that it failed.
    #[test]
    fn test_from_str_reports_the_offending_character() {
        type Zp = Zp541;
        // `from_dec_str` reports the byte offset from b'0', so 'x' (120) arrives as 72.
        assert_eq!(
            Zp::from_str("12x3"),
            Err(ParseFieldElementError::InvalidCharacter(b'x' - b'0'))
        );
        assert_eq!(
            Zp::from_str("-5"),
            Err(ParseFieldElementError::InvalidCharacter(
                b'-'.wrapping_sub(b'0')
            ))
        );
        // A valid string still parses, reduced mod P.
        assert_eq!(Zp::from_str("542").unwrap(), Zp::new(1));
    }

    /// Conditional addition and subtraction agree with reducing by a 128-bit remainder.
    ///
    /// The previous implementation computed `(a + b) % P` in 128 bits, which is correct but an
    /// order of magnitude slower. That formula is the oracle here. Boundary values matter most:
    /// with P close to 2^64 the sum overflows 64 bits, which is exactly the case the carry
    /// handling exists for.
    #[test]
    fn test_conditional_arithmetic_matches_wide_reduction() {
        fn check<const P: u64>(values: &[u64]) {
            for &a in values {
                for &b in values {
                    let (x, y) = (
                        PrimeFieldElement64::<P>::new(a),
                        PrimeFieldElement64::<P>::new(b),
                    );

                    let expected_sum = ((x.value() as u128 + y.value() as u128) % P as u128) as u64;
                    assert_eq!(
                        (x + y).value(),
                        expected_sum,
                        "P = {}: {} + {}",
                        P,
                        x.value(),
                        y.value()
                    );

                    let expected_difference =
                        (x.value() as i128 - y.value() as i128).rem_euclid(P as i128) as u64;
                    assert_eq!(
                        (x - y).value(),
                        expected_difference,
                        "P = {}: {} - {}",
                        P,
                        x.value(),
                        y.value()
                    );
                }
            }
        }

        // Exhaustive over small fields.
        let small: Vec<u64> = (0..7).collect();
        check::<7>(&small);
        let small: Vec<u64> = (0..13).collect();
        check::<13>(&small);

        // The largest 64-bit prime, where a + b overflows 64 bits for most pairs.
        const BIG: u64 = 18446744073709551557;
        check::<BIG>(&[0, 1, 2, BIG / 2, BIG - 3, BIG - 2, BIG - 1, u64::MAX % BIG]);

        // 2^31 - 1, which cannot overflow, to cover the branch that is not taken.
        check::<2147483647>(&[0, 1, 2, 1073741823, 2147483644, 2147483645, 2147483646]);
    }

    proptest! {
        /// The same equivalence over random input, including a field near the 64-bit boundary.
        #[test]
        fn test_conditional_arithmetic_matches_wide_reduction_randomly(a in any::<u64>(), b in any::<u64>()) {
            const BIG: u64 = 18446744073709551557;
            let (x, y) = (PrimeFieldElement64::<BIG>::new(a), PrimeFieldElement64::<BIG>::new(b));

            let expected_sum = ((x.value() as u128 + y.value() as u128) % BIG as u128) as u64;
            prop_assert_eq!((x + y).value(), expected_sum);

            let expected_difference =
                (x.value() as i128 - y.value() as i128).rem_euclid(BIG as i128) as u64;
            prop_assert_eq!((x - y).value(), expected_difference);
        }
    }

    /// Multiplying by a prepared factor equals the `u128` product for every boundary residue and
    /// factor, at moduli that take Shoup, at the 2^63 bound, above it, and below 2^32.
    #[test]
    fn test_mul_prepared_matches_wide_reduction() {
        fn check<const P: u64>() {
            let mut values = vec![0, 1, 2, P / 2, P - 2, P - 1];
            let mut state = 0x9e37_79b9_7f4a_7c15_u64 ^ P;
            for _ in 0..24 {
                state = state
                    .wrapping_mul(6364136223846793005)
                    .wrapping_add(1442695040888963407);
                values.push(state % P);
            }
            for &f in &values {
                let factor = PrimeFieldElement64::<P>::new(f);
                let prepared = factor.prepare_factor();
                for &a in &values {
                    let coefficient = PrimeFieldElement64::<P>::new(a);
                    let expected = ((a as u128 * f as u128) % P as u128) as u64;
                    assert_eq!(
                        coefficient.mul_prepared(&prepared).value(),
                        expected,
                        "P = {P}: {a} * {f}"
                    );
                }
            }
        }

        // The largest prime below 2^63, the edge of Shoup's `2p < 2^64` requirement.
        check::<9223372036854775783>();
        check::<4611624995532046337>();
        // The smallest prime above 2^32: the first Montgomery modulus.
        check::<4294967311>();
        // Above the bound: Goldilocks (canonical) and the largest 64-bit prime (Montgomery) keep
        // the plain product.
        check::<18446744069414584321>();
        check::<18446744073709551557>();
        // Canonical residues below 2^32, including the Mersenne branch.
        check::<2147483647>();
        check::<1481823929>();
        check::<13>();
    }

    /// Below 2^63 a prepared Montgomery factor carries its canonical value and Shoup's
    /// `floor(f * 2^64 / p)`; elsewhere it carries neither.
    #[test]
    fn test_prepare_factor_records_the_shoup_quotient() {
        const P: u64 = 9223372036854775783;
        for f in [0, 1, 2, P - 1] {
            let prepared = PrimeFieldElement64::<P>::new(f).prepare_factor();
            let quotient = (((f as u128) << 64) / P as u128) as u64;
            assert_eq!(prepared.words(), [f, quotient], "f = {f}");
        }
        let above = Zp18446744073709551557::new(5).prepare_factor();
        assert_eq!(above.words(), [0, 0]);
        let narrow = Zp2147483647::new(5).prepare_factor();
        assert_eq!(narrow.words(), [0, 0]);
    }

    /// Goldilocks, 2^64 - 2^32 + 1, held canonically and reduced by 2^64 = 2^32 - 1, 2^96 = -1.
    const GOLDILOCKS: u64 = 18446744069414584321;

    /// `a^e mod GOLDILOCKS` by square-and-multiply over `u128`, the oracle for `pow` and `inverse`.
    fn goldilocks_pow_reference(a: u64, mut e: u128) -> u64 {
        let p = GOLDILOCKS as u128;
        let (mut base, mut acc) = (a as u128 % p, 1u128);
        while e != 0 {
            if e & 1 == 1 {
                acc = acc * base % p;
            }
            base = base * base % p;
            e >>= 1;
        }
        acc as u64
    }

    /// Checks every operation on one Goldilocks pair against `u128` arithmetic.
    fn check_goldilocks_pair(a: u64, b: u64) {
        let p = GOLDILOCKS as u128;
        let (x, y) = (
            Zp18446744069414584321::new(a),
            Zp18446744069414584321::new(b),
        );
        let (a, b) = (a as u128 % p, b as u128 % p);
        assert_eq!((x * y).value() as u128, a * b % p, "{a} * {b}");
        assert_eq!((x + y).value() as u128, (a + b) % p, "{a} + {b}");
        assert_eq!((x - y).value() as u128, (a + p - b) % p, "{a} - {b}");
        assert_eq!((-x).value() as u128, (p - a) % p, "-{a}");
        assert_eq!(
            x.pow(b).value(),
            goldilocks_pow_reference(a as u64, b),
            "{a}^{b}"
        );
        if a != 0 {
            let inverse = x.inverse();
            assert_eq!(
                inverse.value(),
                goldilocks_pow_reference(a as u64, p - 2),
                "1/{a}"
            );
            assert!((x * inverse).is_one(), "{a} * 1/{a}");
        }
    }

    /// Goldilocks elements are stored as their canonical residue, not in Montgomery form.
    #[test]
    fn test_goldilocks_is_held_canonically() {
        assert!(!super::montgomery::uses_montgomery(GOLDILOCKS));
        for value in [0, 1, 5, 1 << 32, GOLDILOCKS - 1] {
            assert_eq!(Zp18446744069414584321::new(value).value, value);
        }
        assert_eq!(Zp18446744069414584321::one().value, 1);
        assert_eq!(
            Zp18446744069414584321::new(u64::MAX).value,
            u64::MAX - GOLDILOCKS
        );
    }

    /// The Goldilocks reduction is exact on its extreme products, including the largest.
    #[test]
    fn test_goldilocks_boundary_products() {
        type G = Zp18446744069414584321;
        // (p - 1)^2 = (-1)^2 = 1: the largest product the reduction ever sees.
        assert_eq!((G::new(GOLDILOCKS - 1) * G::new(GOLDILOCKS - 1)).value(), 1);
        // 2^32 * 2^32 = 2^64 = 2^32 - 1.
        assert_eq!((G::new(1 << 32) * G::new(1 << 32)).value(), 0xFFFF_FFFF);
        // 2^63 * 2^33 = 2^96 = -1: the low word is zero and the subtraction borrows.
        assert_eq!((G::new(1 << 63) * G::new(1 << 33)).value(), GOLDILOCKS - 1);
        // 2^48 * 2^48 = 2^96 = -1 again, reached through a different split of the product.
        assert_eq!((G::new(1 << 48) * G::new(1 << 48)).value(), GOLDILOCKS - 1);
    }

    /// Every operation matches `u128` arithmetic on all pairs of Goldilocks edge values.
    #[test]
    fn test_goldilocks_edge_values_match_u128_reference() {
        let edges = [
            0,
            1,
            2,
            3,
            0xFFFF_FFFF,
            1 << 32,
            (1 << 32) + 1,
            1 << 33,
            1 << 48,
            1 << 63,
            (1 << 63) + 1,
            GOLDILOCKS / 2,
            GOLDILOCKS - (1 << 32),
            GOLDILOCKS - 2,
            GOLDILOCKS - 1,
            // 2^64 - 2^32 = p - 1, and unreduced inputs at and above the modulus.
            u64::MAX - 0xFFFF_FFFF,
            GOLDILOCKS,
            GOLDILOCKS + 1,
            u64::MAX,
        ];
        for &a in &edges {
            for &b in &edges {
                check_goldilocks_pair(a, b);
            }
        }
    }

    /// Every operation matches `u128` arithmetic over a seeded random sweep of Goldilocks pairs.
    #[test]
    fn test_goldilocks_random_sweep_matches_u128_reference() {
        use rand::Rng;
        let mut rng = StdRng::seed_from_u64(781);
        for _ in 0..20_000 {
            let (a, b) = (rng.gen::<u64>(), rng.gen::<u64>());
            check_goldilocks_pair(a, b);
            // Operands concentrated near the top of the range, where the high word is largest.
            check_goldilocks_pair(GOLDILOCKS - 1 - (a >> 40), GOLDILOCKS - 1 - (b >> 40));
        }
    }

    /// Goldilocks elements built by every route compare, hash and serialize as the same element.
    #[test]
    fn test_goldilocks_construction_paths_agree() {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};
        type G = Zp18446744069414584321;

        fn hash_of<T: Hash>(value: &T) -> u64 {
            let mut hasher = DefaultHasher::new();
            value.hash(&mut hasher);
            hasher.finish()
        }

        // Below 2^64 - p = 2^32 - 1, so `value + p` is a second u64 representative of it.
        let value = 0xDEAD_BEEF;
        let direct = G::new(value);
        let wrapped = G::new(value + GOLDILOCKS);
        let parsed = G::from_str(&(value as u128 + GOLDILOCKS as u128).to_string()).unwrap();
        let summed = G::new(value - 7) + G::new(7);
        let multiplied = G::new(value) * G::one();
        let decoded: G = bincode::deserialize(&bincode::serialize(&value).unwrap()).unwrap();
        for other in [wrapped, parsed, summed, multiplied, decoded] {
            assert_eq!(direct, other);
            assert_eq!(hash_of(&direct), hash_of(&other));
            assert_eq!(other.value(), value);
        }
        assert_eq!(
            bincode::serialize(&direct).unwrap(),
            bincode::serialize(&value).unwrap()
        );
        assert_eq!(format!("{direct}"), value.to_string());
        let rejected: Result<G, _> =
            bincode::deserialize(&bincode::serialize(&GOLDILOCKS).unwrap());
        assert!(rejected.is_err());
    }

    proptest! {
        /// Every Goldilocks operation matches `u128` arithmetic on arbitrary operands.
        #[test]
        fn test_goldilocks_matches_u128_reference_randomly(a in any::<u64>(), b in any::<u64>()) {
            check_goldilocks_pair(a, b);
        }
    }
}
