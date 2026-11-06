//! Prime-order finite field, for a modulus below 2^32.
//!
//! The same field as [`PrimeFieldElement64`](super::PrimeFieldElement64) for any modulus both can
//! hold, and this type exists only for its storage width: a 31-bit residue in a `u64` wastes half
//! of every cache line, and the dense elimination kernel is bandwidth-bound once the matrix leaves
//! L2. Four bytes a cell halves the bytes that kernel moves.
//!
//! Elements are held in Montgomery form with R = 2^32 when P is odd, so that multiplication needs
//! no division; see [`montgomery`]. An even modulus keeps a remainder, but by a *constant* 64-bit
//! divisor, which LLVM strength-reduces to a multiply and a shift — so no path from multiplication
//! reaches a software division routine, which is what [`PrimeFieldElement64`] needed Montgomery
//! form to achieve.
//!
//! [`PrimeFieldElement64`]: super::PrimeFieldElement64

use std::{
    fmt::{Display, Formatter},
    ops,
};

use proptest::prelude::{any, Arbitrary, BoxedStrategy, Strategy};
use rand::{CryptoRng, Rng, RngCore};
use serde::{Deserialize, Serialize};

use crate::{
    fields::{trim_limbs, KnownOrder, RootOfUnityError},
    identities::{One, Zero},
    impl_add_variants, impl_div_variants, impl_mul_variants, impl_sub_variants,
    integers::{big_uint::BigUInt, factor, find_generator, limbs_minus_two},
    FiniteField, ParseFieldElementError, Ring,
};

/// Montgomery arithmetic modulo an odd P, with R = 2^32.
///
/// An element `a` is stored as `a * R mod P`. The map is a ring isomorphism for addition and
/// subtraction — `aR + bR = (a + b)R` — so those operations are untouched by the change of
/// representation. Only multiplication and the conversions differ.
///
/// This is [`prime_field_64::montgomery`](super::prime_field_64) at half the width, with one
/// difference that is not a mechanical substitution: the intermediate `t + m*P` needs 65 bits only
/// when P exceeds 2^31, and every modulus this type is declared for is below that. The predicate
/// is [`sum_fits_in_64_bits`], it is on a const generic, and it folds at compile time — so the
/// primes that motivate the type get a reduction with no carry handling in it, which is also what
/// lets the kernel over them vectorize in 32-bit lanes.
mod montgomery {
    /// Whether modulus `p` is represented in Montgomery form.
    ///
    /// Odd moduli only: R = 2^32 is not invertible modulo an even number.
    pub const fn uses_montgomery(p: u32) -> bool {
        p % 2 == 1
    }

    /// `-P^{-1} mod 2^32`, the factor that makes the low half of `t + m*P` vanish.
    ///
    /// Newton's iteration for the inverse of an odd number modulo a power of two doubles the
    /// number of correct bits each step: starting from one bit, five steps reach 32. Requires `p`
    /// odd; for even `p` the result is meaningless but harmless, since every caller is guarded by
    /// [`uses_montgomery`] and the arithmetic here only wraps.
    pub const fn n_prime(p: u32) -> u32 {
        let mut inverse: u32 = 1;
        let mut step = 0;
        while step < 5 {
            // x <- x * (2 - p*x), which is exact modulo 2^(2k) when x is exact modulo 2^k.
            inverse = inverse.wrapping_mul(2u32.wrapping_sub(p.wrapping_mul(inverse)));
            step += 1;
        }
        inverse.wrapping_neg()
    }

    /// `R^2 mod P`, which converts a canonical residue into Montgomery form via one reduction.
    ///
    /// Computed as `(R mod P)^2 mod P` so the intermediate stays inside a `u64`. This runs at
    /// compile time, so the remainder it uses costs nothing at run time.
    pub const fn r2_mod_p(p: u32) -> u32 {
        let r = ((1u64 << 32) % p as u64) as u32;
        ((r as u64 * r as u64) % p as u64) as u32
    }

    /// Whether `t + m*P` stays inside 64 bits for every `t < P*R` and `m < R`.
    ///
    /// The sum is below `2*P*R - P`, so 64 bits suffice exactly when `P <= 2^31`. Every modulus
    /// declared for this type — 31, 65537, Mersenne-31, BabyBear, KoalaBear — satisfies it; the
    /// carry-handling branch exists for a modulus in the top half of the range, and is covered by
    /// the oracle tests at P = 4294967291.
    const fn sum_fits_in_64_bits(p: u32) -> bool {
        p <= 1u32 << 31
    }

    /// Montgomery reduction: `t * R^{-1} mod P`, for `t < P * R`.
    ///
    /// `m` is chosen so that `t + m*P` is divisible by R, which makes the division by R a shift.
    /// The quotient is below 2P, so one conditional subtraction finishes the reduction.
    #[inline(always)]
    pub const fn redc<const P: u32>(t: u64) -> u32 {
        let m = (t as u32).wrapping_mul(n_prime(P));
        let addend = m as u64 * P as u64;

        if sum_fits_in_64_bits(P) {
            let high = ((t + addend) >> 32) as u32;
            return if high >= P { high - P } else { high };
        }

        // P is in the top half of the range, so the true sum can need 65 bits. On overflow it is
        // `2^64 + sum`, so the true quotient is `(sum >> 32) + 2^32`; that exceeds P, and
        // subtracting P brings it back below 2^32, which `wrapping_sub` computes exactly. The low
        // 32 bits of the true sum are zero by construction, so the shift loses nothing.
        let (sum, carry) = t.overflowing_add(addend);
        let high = (sum >> 32) as u32;
        if carry {
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
    pub const fn mul<const P: u32>(a: u32, b: u32) -> u32 {
        redc::<P>(a as u64 * b as u64)
    }

    /// A canonical residue in [0,P) to the internal representation.
    #[inline(always)]
    pub const fn to_internal<const P: u32>(canonical: u32) -> u32 {
        if uses_montgomery(P) {
            mul::<P>(canonical, r2_mod_p(P))
        } else {
            canonical
        }
    }

    /// The internal representation back to a canonical residue in [0,P).
    #[inline(always)]
    pub const fn to_canonical<const P: u32>(internal: u32) -> u32 {
        if uses_montgomery(P) {
            redc::<P>(internal as u64)
        } else {
            internal
        }
    }
}

/// Whether a sum of two reduced residues can overflow a `u32`.
///
/// False for every modulus at or below 2^31, which is all of them that this type is declared for.
/// On a const generic, so the branch it guards folds away.
const fn sum_fits_in_32_bits(p: u32) -> bool {
    p <= 1u32 << 31
}

#[derive(Copy, Clone, Debug, Default, Eq, Hash, PartialEq, Deserialize, Serialize)]
/// Element of a prime field with prime modulus P below 2^32.
///
/// The same field as [`PrimeFieldElement64`](super::PrimeFieldElement64) over the same modulus,
/// in half the bytes:
///
/// ```
/// use zeebra::{fields::{BabyBear, Mersenne31, Zp2147483647}, FiniteField, KnownOrder};
///
/// assert_eq!(std::mem::size_of::<Mersenne31>(), 4);
/// assert_eq!(std::mem::size_of::<Zp2147483647>(), 8);
/// assert_eq!(Mersenne31::order_u128(), Zp2147483647::order_u128());
///
/// // Montgomery form is not observable: `value()` is the canonical residue.
/// let a = Mersenne31::new(827376);
/// assert_eq!(a.pow(2).value(), 1651245630);
/// assert_eq!(a * a.inverse(), Mersenne31::new(1));
///
/// // NTT-friendly moduli are declared for the same type.
/// assert_eq!(BabyBear::order_u128(), Some(2013265921));
/// ```
pub struct PrimeFieldElement32<const P: u32> {
    /// The element's internal representation: `a * 2^32 mod P` for odd P, and the canonical
    /// residue `a` for even P. [`value`](Self::value) converts back; nothing else should read this
    /// field expecting a residue.
    ///
    /// Private so that neither the reduced-residue invariant nor the choice of representation can
    /// be broken from outside: every operation here assumes the stored value is below P, and
    /// `PartialEq` and `Hash` are derived over it. Deriving them over the Montgomery form is
    /// sound because the map is a bijection on [0,P).
    ///
    /// Deserialization is the one construction path that bypasses a constructor, so it validates
    /// rather than trusting its input, and converts.
    #[serde(
        serialize_with = "canonical_residue::<_, P>",
        deserialize_with = "reduced_residue::<_, P>"
    )]
    value: u32,
}

/// Accepts a representative only if it is already reduced modulo P, then converts it.
///
/// Rejecting rather than reducing: a value outside [0,P) did not come from this field, so it
/// signals either corruption or a mismatched modulus, and silently reinterpreting it would hide
/// that. The wire format is the canonical residue in both directions, so the representation change
/// is invisible to a stored or transmitted element.
fn reduced_residue<'de, D, const P: u32>(deserializer: D) -> Result<u32, D::Error>
where
    D: serde::Deserializer<'de>,
{
    let value = u32::deserialize(deserializer)?;
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
/// format and be rejected on the way back in by any peer that reduced differently. The width is
/// four bytes, not eight: this is the whole point of the type, and the wire format follows it.
fn canonical_residue<S, const P: u32>(value: &u32, serializer: S) -> Result<S::Ok, S::Error>
where
    S: serde::Serializer,
{
    serializer.serialize_u32(montgomery::to_canonical::<P>(*value))
}

impl<const P: u32> PrimeFieldElement32<P> {
    /// The element's representative integer in [0,p-1].
    ///
    /// For an odd modulus this is a Montgomery reduction, not a field read, so a hot loop should
    /// hold field elements rather than call this per iteration.
    pub fn value(&self) -> u32 {
        montgomery::to_canonical::<P>(self.value)
    }
}

impl<const P: u32> Zero for PrimeFieldElement32<P> {
    // Zero is a fixed point of the Montgomery map, so this needs no conversion.
    const ZERO: Self = Self { value: 0 };
}

impl<const P: u32> One for PrimeFieldElement32<P> {
    // One is not a fixed point: in Montgomery form it is R mod P.
    const ONE: Self = Self {
        value: montgomery::to_internal::<P>(1),
    };
}

impl<const P: u32> Ring for PrimeFieldElement32<P> {}

impl<const P: u32> FiniteField for PrimeFieldElement32<P> {
    fn new(val: u64) -> Self {
        // The argument is a `u64` because the trait says so; a value above P reduces, as it does
        // for every other prime field here.
        Self {
            value: montgomery::to_internal::<P>((val % P as u64) as u32),
        }
    }

    fn from_str(value: &str) -> Result<Self, ParseFieldElementError> {
        let parsed = BigUInt::from_dec_str(value)?;
        let modulus = BigUInt::new_from_u64(P as u64);
        let residue = parsed % &modulus;
        let words = residue.as_le_words();
        assert!(words.len() <= 1);

        Ok(Self {
            value: montgomery::to_internal::<P>(*words.first().unwrap_or(&0) as u32),
        })
    }

    fn random<R: RngCore + CryptoRng>(rng: &mut R) -> Self {
        let value = rng.gen_range(0..P);
        Self::new(value as u64)
    }

    fn inverse(&self) -> Self {
        assert_ne!(
            *self,
            Self::zero(),
            "The zero element does not have a multiplicative inverse."
        );
        self.pow_limbs(&Self::FERMAT_EXPONENT_LIMBS)
    }
}

impl<const P: u32> PrimeFieldElement32<P> {
    /// The order q = p of the field, as little-endian limbs. See [`KnownOrder::order_limbs`].
    const ORDER_LIMBS: [u64; 1] = [P as u64];

    /// The Fermat inversion exponent q - 2, as little-endian limbs.
    ///
    /// Subtracted on the limbs rather than on a machine integer, and held at the width of
    /// [`Self::ORDER_LIMBS`], so nothing here caps the order at the width of a `u128`.
    const FERMAT_EXPONENT_LIMBS: [u64; 1] = limbs_minus_two(Self::ORDER_LIMBS);
}

impl<const P: u32> KnownOrder for PrimeFieldElement32<P> {
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
        let n = BigUInt::new_from_u64(P as u64 - 1);
        let (prime_factors, powers) = factor(&n, rng);
        let generator = find_generator(&prime_factors, &powers, rng);
        assert!(generator <= n);
        let value = *generator.as_le_words().first().unwrap_or(&0) as u32;
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
impl<const P: u32> Display for PrimeFieldElement32<P> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value())
    }
}

/// Borrowed + Borrowed
impl<const P: u32> ops::Add<&PrimeFieldElement32<P>> for &PrimeFieldElement32<P> {
    type Output = PrimeFieldElement32<P>;

    fn add(self, rhs: &PrimeFieldElement32<P>) -> Self::Output {
        // Both operands are reduced, so their sum is below 2P and a single conditional
        // subtraction reduces it. For P at or below 2^31 the sum cannot leave 32 bits, and the
        // whole operation is an add and a select — which is what vectorizes at eight lanes.
        let value = if sum_fits_in_32_bits(P) {
            let sum = self.value + rhs.value;
            if sum >= P {
                sum - P
            } else {
                sum
            }
        } else {
            // On carry the true sum is 2^32 + sum, which is above P, and the wrapping subtraction
            // of P yields exactly that less P.
            let (sum, carry) = self.value.overflowing_add(rhs.value);
            if carry || sum >= P {
                sum.wrapping_sub(P)
            } else {
                sum
            }
        };
        PrimeFieldElement32 { value }
    }
}

impl_add_variants!([const P: u32], PrimeFieldElement32<P>);

/// Borrowed * Borrowed
impl<const P: u32> ops::Mul<&PrimeFieldElement32<P>> for &PrimeFieldElement32<P> {
    type Output = PrimeFieldElement32<P>;

    fn mul(self, rhs: &PrimeFieldElement32<P>) -> Self::Output {
        // Both operands carry the same factor of R, and Montgomery reduction removes exactly one
        // of them, so the product is in the same representation as the inputs. The remainder
        // survives only for an even modulus, where R is not invertible; that branch is on a const
        // generic, so it is resolved at compile time, and the divisor is a constant, so what is
        // left is a multiply and a shift rather than a call to a division routine.
        let value = if montgomery::uses_montgomery(P) {
            montgomery::mul::<P>(self.value, rhs.value)
        } else {
            ((self.value as u64 * rhs.value as u64) % P as u64) as u32
        };
        Self::Output { value }
    }
}

impl_mul_variants!([const P: u32], PrimeFieldElement32<P>);

/// Borrowed - Borrowed
impl<const P: u32> ops::Sub for &PrimeFieldElement32<P> {
    type Output = PrimeFieldElement32<P>;

    fn sub(self, rhs: Self) -> Self::Output {
        // On borrow the difference is negative, and adding P brings it back into range. The
        // difference is above -P, so this is exact in 32 bits for every P.
        let (difference, borrow) = self.value.overflowing_sub(rhs.value);
        let value = if borrow {
            difference.wrapping_add(P)
        } else {
            difference
        };
        Self::Output { value }
    }
}

impl_sub_variants!([const P: u32], PrimeFieldElement32<P>);

impl<const P: u32> ops::Neg for PrimeFieldElement32<P> {
    type Output = PrimeFieldElement32<P>;

    fn neg(self) -> Self::Output {
        Self::zero() - self
    }
}

impl<const P: u32> ops::Neg for &PrimeFieldElement32<P> {
    type Output = PrimeFieldElement32<P>;

    fn neg(self) -> Self::Output {
        PrimeFieldElement32::zero() - self
    }
}

/// Borrowed / Borrowed
impl<const P: u32> ops::Div<Self> for &PrimeFieldElement32<P> {
    type Output = PrimeFieldElement32<P>;

    fn div(self, rhs: Self) -> Self::Output {
        // Division is multiplication by the inverse modulo p.
        self * rhs.inverse()
    }
}

impl_div_variants!([const P: u32], PrimeFieldElement32<P>);

/// impl Arbitrary
impl<const P: u32> Arbitrary for PrimeFieldElement32<P> {
    type Parameters = ();

    fn arbitrary_with(_args: Self::Parameters) -> Self::Strategy {
        // Drawn over the backing width rather than over [0,P), so the top of the range is
        // reachable for a modulus near 2^32 and proptest's special values land on the boundary.
        any::<u32>()
            .prop_map(|value| Self::new(value as u64))
            .boxed()
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
            finite_field::fermat_inverse_via_recursive_pow, BabyBear, KoalaBear, Mersenne31,
            PrimeFieldElement32, PrimeFieldElement64, Zp31, Zp65537_32,
        },
        identities::{One, Zero},
        FiniteField, KnownOrder, ParseFieldElementError,
    };

    /// The largest prime below 2^32, where `t + m*P` needs the carry-handling path in `redc`.
    const BIG: u32 = 4294967291;

    /// Multiplication agrees with reducing the full 64-bit product by a wide remainder.
    ///
    /// The oracle is the textbook formula `(a * b) % P` in 64 bits. This is the characterization
    /// test for the internal representation: Montgomery form changes what `value` holds, and the
    /// only thing that must not change is what `value()` reports. Both widths of modulus are
    /// covered — below 2^31, where the reduction has no carry handling, and above it, where it
    /// does — and an even modulus, which exercises the remainder fallback.
    #[test]
    fn test_multiplication_matches_wide_reduction() {
        fn check<const P: u32>(values: &[u32]) {
            for &a in values {
                for &b in values {
                    let (x, y) = (
                        PrimeFieldElement32::<P>::new(a as u64),
                        PrimeFieldElement32::<P>::new(b as u64),
                    );
                    let expected = ((x.value() as u64 * y.value() as u64) % P as u64) as u32;
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
        check::<7>(&(0..7).collect::<Vec<_>>());
        check::<31>(&(0..31).collect::<Vec<_>>());

        // 2^31 - 1, the modulus the benchmarks use, at the top of the no-carry range.
        const MERSENNE: u32 = 2147483647;
        check::<MERSENNE>(&[0, 1, 2, 1073741823, MERSENNE - 2, MERSENNE - 1]);

        // BabyBear and KoalaBear.
        check::<2013265921>(&[0, 1, 2, 1006632960, 2013265919, 2013265920]);
        check::<2130706433>(&[0, 1, 2, 1065353216, 2130706431, 2130706432]);

        // The largest 32-bit prime, where the product uses the full 64 bits and `t + m*P` can
        // need 65. Nothing else in this file reaches that branch.
        check::<BIG>(&[0, 1, 2, BIG / 2, BIG - 3, BIG - 2, BIG - 1]);
    }

    proptest! {
        /// Multiplication matches the wide-reduction oracle over random input, at both widths.
        #[test]
        fn test_multiplication_matches_wide_reduction_randomly(a in any::<u32>(), b in any::<u32>()) {
            let (x, y) = (
                PrimeFieldElement32::<BIG>::new(a as u64),
                PrimeFieldElement32::<BIG>::new(b as u64),
            );
            let expected = ((x.value() as u64 * y.value() as u64) % BIG as u64) as u32;
            prop_assert_eq!((x * y).value(), expected);

            let (x, y) = (Mersenne31::new(a as u64), Mersenne31::new(b as u64));
            let expected = ((x.value() as u64 * y.value() as u64) % 2147483647u64) as u32;
            prop_assert_eq!((x * y).value(), expected);
        }
    }

    /// Conditional addition and subtraction agree with reducing by a wide remainder.
    ///
    /// Boundary values matter most: with P above 2^31 the sum overflows 32 bits, which is the case
    /// the carry handling exists for, and below it the branch that is not taken has to be right
    /// for the same inputs.
    #[test]
    fn test_conditional_arithmetic_matches_wide_reduction() {
        fn check<const P: u32>(values: &[u32]) {
            for &a in values {
                for &b in values {
                    let (x, y) = (
                        PrimeFieldElement32::<P>::new(a as u64),
                        PrimeFieldElement32::<P>::new(b as u64),
                    );

                    let expected_sum = ((x.value() as u64 + y.value() as u64) % P as u64) as u32;
                    assert_eq!(
                        (x + y).value(),
                        expected_sum,
                        "P = {}: {} + {}",
                        P,
                        x.value(),
                        y.value()
                    );

                    let expected_difference =
                        (x.value() as i64 - y.value() as i64).rem_euclid(P as i64) as u32;
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

        check::<7>(&(0..7).collect::<Vec<_>>());
        check::<31>(&(0..31).collect::<Vec<_>>());

        // 2^31 - 1, which cannot overflow, to cover the branch that is not taken.
        const MERSENNE: u32 = 2147483647;
        check::<MERSENNE>(&[0, 1, 2, 1073741823, MERSENNE - 2, MERSENNE - 1]);

        // The largest 32-bit prime, where a + b overflows 32 bits for most pairs.
        check::<BIG>(&[0, 1, 2, BIG / 2, BIG - 3, BIG - 2, BIG - 1, u32::MAX % BIG]);
    }

    proptest! {
        /// The same equivalence over random input, including a field near the 32-bit boundary.
        #[test]
        fn test_conditional_arithmetic_matches_wide_reduction_randomly(a in any::<u32>(), b in any::<u32>()) {
            let (x, y) = (
                PrimeFieldElement32::<BIG>::new(a as u64),
                PrimeFieldElement32::<BIG>::new(b as u64),
            );

            let expected_sum = ((x.value() as u64 + y.value() as u64) % BIG as u64) as u32;
            prop_assert_eq!((x + y).value(), expected_sum);

            let expected_difference =
                (x.value() as i64 - y.value() as i64).rem_euclid(BIG as i64) as u32;
            prop_assert_eq!((x - y).value(), expected_difference);
        }
    }

    /// The 32-bit field and the 64-bit field agree element for element on the same modulus.
    ///
    /// The point of the type is that it computes the same function in half the bytes, so the
    /// existing implementation is the natural oracle for the new one — stronger than a formula,
    /// because it also pins `value()`, `Display` and the parse path to the same answers.
    #[test]
    fn test_the_two_widths_agree_on_the_same_modulus() {
        const P: u32 = 2147483647;
        type Narrow = PrimeFieldElement32<P>;
        type Wide = PrimeFieldElement64<{ P as u64 }>;

        let values: [u64; 8] = [0, 1, 2, 7, 827376, 1073741823, 2147483645, 2147483646];
        for &a in &values {
            for &b in &values {
                let (xn, yn) = (Narrow::new(a), Narrow::new(b));
                let (xw, yw) = (Wide::new(a), Wide::new(b));

                assert_eq!((xn * yn).value() as u64, (xw * yw).value());
                assert_eq!((xn + yn).value() as u64, (xw + yw).value());
                assert_eq!((xn - yn).value() as u64, (xw - yw).value());
                if !yn.is_zero() {
                    assert_eq!((xn / yn).value() as u64, (xw / yw).value());
                }
            }

            assert_eq!(
                format!("{xn}", xn = Narrow::new(a)),
                format!("{}", Wide::new(a))
            );
            assert_eq!(
                Narrow::from_str(&a.to_string()).unwrap().value() as u64,
                Wide::from_str(&a.to_string()).unwrap().value()
            );
        }
    }

    /// An element occupies four bytes, and a dense row of them half of what the 64-bit type needs.
    ///
    /// This is the entire reason the type exists, so it is pinned rather than assumed: a stray
    /// field, a wider backing integer, or an alignment change would make the type correct and
    /// pointless at the same time, and no other test here would notice.
    #[test]
    fn test_an_element_is_four_bytes() {
        assert_eq!(std::mem::size_of::<Mersenne31>(), 4);
        assert_eq!(std::mem::align_of::<Mersenne31>(), 4);
        assert_eq!(std::mem::size_of::<PrimeFieldElement64<2147483647>>(), 8);

        let narrow = vec![Mersenne31::one(); 1024];
        let wide = vec![PrimeFieldElement64::<2147483647>::one(); 1024];
        assert_eq!(
            std::mem::size_of_val(&narrow[..]) * 2,
            std::mem::size_of_val(&wide[..])
        );
    }

    /// The serialized bytes are the canonical residue in four bytes, not the Montgomery form.
    ///
    /// The round-trip test below would pass even if the wire format silently became Montgomery
    /// form, because it only checks that encoding and decoding compose to the identity. This pins
    /// the bytes themselves against a plain `u32`.
    #[test]
    fn test_the_wire_format_is_the_canonical_residue() {
        // 7 mod 31 is 7, and the Montgomery form of 7 mod 31 is not 7, so the two disagree.
        assert_eq!(
            bincode::serialize(&Zp31::new(7)).unwrap(),
            bincode::serialize(&7u32).unwrap()
        );

        // One is the case most likely to leak: in Montgomery form it is R mod P, not 1.
        assert_eq!(
            bincode::serialize(&Mersenne31::one()).unwrap(),
            bincode::serialize(&1u32).unwrap()
        );
        assert_eq!(
            bincode::serialize(&Mersenne31::zero()).unwrap(),
            bincode::serialize(&0u32).unwrap()
        );

        // A value near the top of the range, for a modulus near 2^32.
        let value = 0xDEAD_BEEFu32 % BIG;
        assert_eq!(
            bincode::serialize(&PrimeFieldElement32::<BIG>::new(value as u64)).unwrap(),
            bincode::serialize(&value).unwrap()
        );

        // Four bytes on the wire, not eight. The 64-bit type of the same modulus emits twice this.
        assert_eq!(bincode::serialize(&Mersenne31::new(7)).unwrap().len(), 4);
    }

    /// `Display` shows the canonical residue, not the internal representation.
    #[test]
    fn test_display_shows_the_canonical_residue() {
        assert_eq!(format!("{}", Zp31::new(7)), "7");
        assert_eq!(format!("{}", Zp31::one()), "1");
        assert_eq!(format!("{}", Zp31::zero()), "0");
        assert_eq!(format!("{}", Zp31::new(38)), "7");
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

        let direct = Zp31::new(7);
        let wrapped = Zp31::new(38); // 38 = 7 mod 31
        let parsed = Zp31::from_str("7").unwrap();
        let summed = Zp31::new(3) + Zp31::new(4);
        let decoded: Zp31 = bincode::deserialize(&bincode::serialize(&direct).unwrap()).unwrap();

        for other in [wrapped, parsed, summed, decoded] {
            assert_eq!(direct, other);
            assert_eq!(hash_of(&direct), hash_of(&other));
            assert_eq!(direct.value(), other.value());
        }

        // One and zero are identities under the operations, in whatever representation.
        assert!(Zp31::one().is_one());
        assert!(Zp31::zero().is_zero());
        assert_eq!(Zp31::new(7) * Zp31::one(), Zp31::new(7));
        assert_eq!(Zp31::new(7) + Zp31::zero(), Zp31::new(7));
        assert_eq!(Zp31::new(7) * Zp31::new(7).inverse(), Zp31::one());
    }

    /// Deserializing an unreduced representative is rejected rather than admitted.
    #[test]
    fn test_deserializing_an_unreduced_representative_is_rejected() {
        // 38 is congruent to 7 mod 31, but is not the representative this field uses. Admitting it
        // would break the invariant that addition and subtraction rely on.
        let encoded = bincode::serialize(&38u32).unwrap();
        let decoded: Result<Zp31, _> = bincode::deserialize(&encoded);
        assert!(decoded.is_err(), "38 should be rejected modulo 31");
    }

    /// The modulus itself is not a valid representative; P-1 is the largest one.
    #[test]
    fn test_deserializing_rejects_the_modulus_and_admits_p_minus_one() {
        let encoded = bincode::serialize(&31u32).unwrap();
        let decoded: Result<Zp31, _> = bincode::deserialize(&encoded);
        assert!(decoded.is_err(), "31 should be rejected modulo 31");

        let encoded = bincode::serialize(&30u32).unwrap();
        let decoded: Zp31 = bincode::deserialize(&encoded).expect("30 is a valid residue mod 31");
        assert_eq!(decoded.value(), 30);
    }

    /// Validating deserialization does not change the wire format: every element round-trips.
    #[test]
    fn test_serde_round_trip_is_unchanged() {
        for value in 0..31u64 {
            let element = Zp31::new(value);
            let encoded = bincode::serialize(&element).unwrap();
            let decoded: Zp31 = bincode::deserialize(&encoded).unwrap();
            assert_eq!(decoded, element);
        }

        // A value near the top of the range, where the largest 32-bit prime lives.
        let element = PrimeFieldElement32::<BIG>::new(u32::MAX as u64);
        let encoded = bincode::serialize(&element).unwrap();
        let decoded: PrimeFieldElement32<BIG> = bincode::deserialize(&encoded).unwrap();
        assert_eq!(decoded, element);
    }

    /// Arithmetic on a deserialized element agrees with arithmetic on a constructed one.
    #[test]
    fn test_deserialized_elements_arithmetic_agrees_with_constructed() {
        for value in 0..31u32 {
            let encoded = bincode::serialize(&value).unwrap();
            let decoded: Zp31 = bincode::deserialize(&encoded).unwrap();
            assert_eq!(decoded + Zp31::zero(), Zp31::new(value as u64));
            assert_eq!(decoded - Zp31::zero(), Zp31::new(value as u64));
            assert_eq!(decoded + Zp31::one(), Zp31::new(value as u64 + 1));
        }
    }

    /// The default value is zero.
    #[test]
    fn test_default_is_zero() {
        type F = PrimeFieldElement32<5807>;
        assert_eq!(F::default(), F::zero());
    }

    /// A decimal string parses to its residue mod P, including strings far above the modulus.
    #[test]
    fn test_from_str() {
        for x in 0..10000u64 {
            assert_eq!(
                Zp65537_32::new(x),
                Zp65537_32::from_str(&x.to_string()).unwrap()
            );
        }
        // A value above 2^32, which has to reduce rather than overflow the backing integer.
        assert_eq!(
            Mersenne31::from_str("4294967294").unwrap(),
            Mersenne31::new(4294967294 % 2147483647)
        );
    }

    /// A parse failure reports which character was rejected, rather than only that it failed.
    #[test]
    fn test_from_str_reports_the_offending_character() {
        // `from_dec_str` reports the byte offset from b'0', so 'x' (120) arrives as 72.
        assert_eq!(
            Zp31::from_str("12x3"),
            Err(ParseFieldElementError::InvalidCharacter(b'x' - b'0'))
        );
        // A valid string still parses, reduced mod P.
        assert_eq!(Zp31::from_str("32").unwrap(), Zp31::new(1));
    }

    /// `random` does not panic, over a small and a large modulus.
    #[test]
    fn test_random_does_not_panic() {
        let mut rng = thread_rng();
        for _ in 0..1000 {
            let _element = PrimeFieldElement32::<61>::random(&mut rng);
            let _element = PrimeFieldElement32::<BIG>::random(&mut rng);
        }
    }

    /// Sampling is uniform over the whole field: a chi-squared test over every residue.
    #[test]
    fn test_random_distribution() {
        const P: u32 = 61;
        const DRAWS: usize = 200_000;

        let mut rng = StdRng::seed_from_u64(20);
        let mut counts = [0usize; P as usize];
        for _ in 0..DRAWS {
            counts[PrimeFieldElement32::<P>::random(&mut rng).value() as usize] += 1;
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
        assert_eq!(*element * element.inverse(), F::one());
    }

    proptest! {
        #[test]
        fn test_inverse_p_31(element in Zp31::arbitrary()) {
            element_times_inverse_is_one(&element);
        }

        #[test]
        fn test_inverse_mersenne31(element in Mersenne31::arbitrary()) {
            element_times_inverse_is_one(&element);
        }

        #[test]
        fn test_inverse_baby_bear(element in BabyBear::arbitrary()) {
            element_times_inverse_is_one(&element);
        }

        #[test]
        fn test_inverse_koala_bear(element in KoalaBear::arbitrary()) {
            element_times_inverse_is_one(&element);
        }
    }

    /// Zero does not have a multiplicative inverse.
    #[test]
    #[should_panic(expected = "does not have a multiplicative inverse")]
    fn test_inverse_of_zero() {
        let _inverse = Zp31::new(0).inverse();
    }

    /// Every nonzero element of a small field inverts to exactly what the recursive-pow reference
    /// gives, over the internal representation and not merely up to the field axioms.
    #[test]
    fn test_inverse_is_bit_identical_to_the_reference_exhaustively() {
        fn check<const P: u32>() {
            for value in 1..P {
                let a = PrimeFieldElement32::<P>::new(value as u64);
                assert_eq!(
                    a.inverse(),
                    fermat_inverse_via_recursive_pow(&a),
                    "P = {P}: {value}"
                );
            }
        }

        check::<31>();
        check::<65537>();
    }

    proptest! {
        /// Inversion is bit-identical to the recursive-pow reference at the moduli
        /// `for_each_field!` does not reach — including the one above 2^31, where `redc` takes
        /// its carry-handling branch.
        #[test]
        fn test_inverse_is_bit_identical_to_the_reference(seed in any::<u32>()) {
            fn check<const P: u32>(seed: u32) {
                let a = PrimeFieldElement32::<P>::new(seed as u64);
                if a.is_zero() {
                    return;
                }
                assert_eq!(a.inverse(), fermat_inverse_via_recursive_pow(&a), "P = {P}: {seed}");
            }

            check::<65537>(seed);
            check::<2013265921>(seed);
            check::<BIG>(seed);
        }

        /// The 31-bit Mersenne field inverts the same whether it is backed by a `u32` or a `u64`.
        ///
        /// Two separate implementations of one field: a disagreement here is a defect in whichever
        /// of them changed, and neither type can be the oracle for the other by construction.
        #[test]
        fn test_inversion_agrees_across_the_two_mersenne31_backings(seed in any::<u32>()) {
            const P: u32 = 2147483647;
            let narrow = Mersenne31::new(seed as u64);
            if !narrow.is_zero() {
                let wide = PrimeFieldElement64::<{ P as u64 }>::new(seed as u64);
                prop_assert_eq!(narrow.inverse().value() as u64, wide.inverse().value());
            }
        }
    }

    proptest! {
        /// Addition is commutative, at both ends of the modulus range.
        #[test]
        fn test_addition_is_commutative(a in Mersenne31::arbitrary(), b in Mersenne31::arbitrary()) {
            assert_eq!(a + b, b + a);
        }

        /// Multiplication is commutative, at both ends of the modulus range.
        #[test]
        fn test_multiplication_is_commutative(
            a in PrimeFieldElement32::<BIG>::arbitrary(),
            b in PrimeFieldElement32::<BIG>::arbitrary(),
        ) {
            assert_eq!(a * b, b * a);
        }

        /// Every representative stays below P, which the conditional reductions depend on.
        #[test]
        fn test_representatives_are_reduced(
            a in Zp65537_32::arbitrary(),
            b in Zp65537_32::arbitrary(),
        ) {
            assert!((a + b).value < 65537);
            assert!((a * b).value < 65537);
            assert!((a - b).value < 65537);
        }
    }

    /// Spot-check that subtraction produces correct values.
    #[test]
    fn test_sub() {
        type Zp = PrimeFieldElement32<7>;
        let (a, b) = (Zp::new(3), Zp::new(2));
        assert_eq!(a - a, Zp::new(0));
        assert_eq!(a - b, Zp::new(1));
        assert_eq!(b - a, Zp::new(6));
    }

    /// Spot-check that multiplication produces correct values.
    #[test]
    fn test_mul() {
        type Zp = PrimeFieldElement32<7>;
        let a = Zp::new(3);
        assert_eq!(a * Zp::new(2), Zp::new(6));
        assert_eq!(a * Zp::new(6), Zp::new(4));
    }

    /// x^0 = 1.
    #[test]
    fn test_pow_zero() {
        let mut rng = StdRng::seed_from_u64(333378);
        let x = Mersenne31::random(&mut rng);
        assert_eq!(x.pow(0), Mersenne31::one());
    }

    /// Spot-check that `pow` computes powers, against the figures recorded for the 64-bit type.
    #[test]
    fn test_pow() {
        let a = Mersenne31::new(827376);
        assert_eq!(a.pow(1), a);
        assert_eq!(a.pow(2).value(), 1651245630);
        assert_eq!(a.pow(7).value(), 1787801728);
        assert_eq!(a.pow(43).value(), 263804505);
        assert_eq!(a.pow(196).value(), 1889125610);
    }

    /// Spot-check that division produces correct values.
    #[test]
    fn test_div() {
        type Zp = PrimeFieldElement32<7>;
        let (a, b) = (Zp::new(6), Zp::new(2));
        assert_eq!(a / b, Zp::new(3));
        assert_eq!(b / a, Zp::new(5));
    }

    /// Dividing by zero panics.
    #[test]
    #[should_panic]
    fn test_div_by_zero_panics() {
        let _boom = Mersenne31::new(6) / Mersenne31::zero();
    }

    /// The order and the characteristic are the modulus, in one limb.
    #[test]
    fn test_order_is_the_modulus() {
        assert_eq!(Mersenne31::order_limbs(), &[2147483647]);
        assert_eq!(Mersenne31::order_u128(), Some(2147483647));
        assert_eq!(Mersenne31::characteristic_limbs(), &[2147483647]);
        assert_eq!(BabyBear::order_u128(), Some(2013265921));
        assert_eq!(KoalaBear::order_u128(), Some(2130706433));
        assert_eq!(Zp31::order_u128(), Some(31));
    }

    /// Powers of the primitive element generate all non-zero elements of the field.
    #[test]
    fn test_primitive_element() {
        const P: u32 = 73;
        type Zp = PrimeFieldElement32<P>;
        let mut rng = StdRng::seed_from_u64(87878);
        let alpha = Zp::primitive_element(&mut rng);
        let nonzero_elements: HashSet<Zp> = (1..P as u64).map(Zp::new).collect();
        assert!(nonzero_elements.contains(&alpha));

        let generated: HashSet<Zp> = (0..=(P as u128 - 2)).map(|i| alpha.pow(i)).collect();
        assert_eq!(generated, nonzero_elements);
    }

    /// An nth root of unity satisfies r^n = 1, and is not the trivial root.
    #[test]
    fn test_root_of_unity() {
        let mut rng = StdRng::seed_from_u64(88283746);
        type Zp = PrimeFieldElement32<541>;
        // 540 = 2^2 * 3^3 * 5.
        for n in [2u64, 3, 5] {
            let r = Zp::root_of_unity(n, &mut rng);
            assert_eq!(r.pow(n as u128), Zp::one());
            assert_ne!(r, Zp::one());
        }
    }

    /// A primitive nth root of unity satisfies r^n = 1 and r^k != 1 for every 0 < k < n.
    ///
    /// Run over BabyBear, whose 2^27 | p - 1 is the property the NTT work needs from it.
    #[test]
    fn test_root_of_unity_is_primitive() {
        let mut rng = StdRng::seed_from_u64(7);
        for n in [2u64, 4, 8, 16, 32] {
            let r = BabyBear::root_of_unity(n, &mut rng);
            assert_eq!(r.pow(n as u128), BabyBear::one(), "n = {n}");
            for k in 1..n {
                assert_ne!(r.pow(k as u128), BabyBear::one(), "n = {n}, k = {k}");
            }
        }
    }

    /// The strategy is usable, equal values hash equally, and representatives stay below P.
    #[test]
    fn test_arbitrary_and_representation_are_sound() {
        use crate::test_support::{
            assert_hash_agrees_with_eq, assert_strategy_is_not_degenerate, draw,
        };
        let strategy = Zp31::arbitrary();
        assert_strategy_is_not_degenerate(&strategy, "PrimeFieldElement32");

        let mut values = draw(&strategy, 32);
        values.extend([Zp31::zero(), Zp31::one(), Zp31::default()]);
        assert_hash_agrees_with_eq(&values, "PrimeFieldElement32");

        for v in &values {
            assert!(v.value < 31, "{v:?} is not reduced");
        }
    }
}
