//! Prime-order finite field.
//!
//! For each prime p, the finite field F_p is defined to be the quotient ring Z/pZ.
//!
//! Elements are held in Montgomery form when P is odd, so that multiplication needs no division.
//! `mul` used to compute `(a as u128 * b as u128) % P as u128`, and a const-generic modulus does
//! not save that: LLVM does not strength-reduce a 128-bit remainder, so every multiplication
//! compiled to a call to `__umodti3`, compiler-rt's software 128-bit division. Montgomery
//! reduction replaces it with two multiplications and a shift. See [`montgomery`] for the
//! representation and the invariant it carries.

use std::{
    fmt::{Display, Formatter},
    ops,
};

use proptest::prelude::{any, Arbitrary, BoxedStrategy, Strategy};
use rand::{CryptoRng, Rng, RngCore};
use serde::{Deserialize, Serialize};

use crate::{
    identities::{One, Zero},
    impl_add_variants, impl_div_variants, impl_mul_variants, impl_sub_variants,
    integers::{big_uint::BigUInt, factor, find_generator},
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
/// keeps the wide-remainder path. [`uses_montgomery`] is the one predicate that decides, and
/// because P is a const generic every branch on it folds away at compile time.
mod montgomery {
    /// Whether modulus `p` is represented in Montgomery form.
    ///
    /// Odd moduli only: R = 2^64 is not invertible modulo an even number.
    pub const fn uses_montgomery(p: u64) -> bool {
        p % 2 == 1
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

#[derive(Copy, Clone, Debug, Default, Eq, Hash, PartialEq, Deserialize, Serialize)]
/// Element of a prime field with prime modulus P.
pub struct PrimeFieldElement64<const P: u64> {
    /// The element's internal representation: `a * 2^64 mod P` for odd P, and the canonical
    /// residue `a` for even P. [`value`](Self::value) converts back; nothing else should read this
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
    /// For an odd modulus this is a Montgomery reduction, not a field read, so a hot loop should
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

    fn primitive_element<R: RngCore + CryptoRng>(rng: &mut R) -> Self {
        // See Algorithm 4.80 of Handbook of Applied Cryptography.
        let n = BigUInt::new_from_u64(P - 1);
        let (prime_factors, powers) = factor(&n, rng);
        let generator = find_generator(&prime_factors, &powers, rng);
        // Convert generator to an integer in [0,P).
        assert!(generator <= n);
        let value = generator.as_le_words()[0];
        Self {
            value: montgomery::to_internal::<P>(value),
        }
    }

    fn root_of_unity<R: RngCore + CryptoRng>(n: u64, rng: &mut R) -> Self {
        // n must divide the group order.
        let group_order = Self::order() - 1;
        assert_eq!(group_order % n as u128, 0, "n must divide the group order.");

        let x = Self::primitive_element(rng);
        x.pow(group_order / n as u128)
    }

    fn order() -> u128 {
        P as u128
    }

    fn characteristic() -> u128 {
        P as u128
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

/// Borrowed * Borrowed
impl<const P: u64> ops::Mul<&PrimeFieldElement64<P>> for &PrimeFieldElement64<P> {
    type Output = PrimeFieldElement64<P>;

    fn mul(self, rhs: &PrimeFieldElement64<P>) -> Self::Output {
        // Both operands carry the same factor of R, and Montgomery reduction removes exactly one
        // of them, so the product is in the same representation as the inputs. The wide remainder
        // survives only for an even modulus, where R is not invertible; that branch is on a const
        // generic, so it is resolved at compile time and costs nothing here.
        let value = if montgomery::uses_montgomery(P) {
            montgomery::mul::<P>(self.value, rhs.value)
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

/// impl Arbitrary
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
            PrimeFieldElement64, Zp1091, Zp13, Zp18446744069414584321, Zp18446744073709551557,
            Zp2147483647, Zp541, Zp65537, Zp7,
        },
        identities::{One, Zero},
        FiniteField, ParseFieldElementError,
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

        // 2^31 - 1, where the product stays inside 62 bits.
        check::<2147483647>(&[0, 1, 2, 1073741823, 2147483645, 2147483646]);
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

    #[ignore]
    #[test]
    // random() should sample a field element uniformly at random.
    fn test_random_distribution() {
        unimplemented!()
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
    #[should_panic]
    // Zero does not have a multiplicative inverse.
    fn test_inverse_of_zero() {
        type Zp = PrimeFieldElement64<7>;
        let element = Zp::new(0);
        let _inverse = element.inverse();
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
}
