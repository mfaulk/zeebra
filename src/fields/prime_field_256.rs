//! Prime fields of 254- to 256-bit order, for the scalar fields of the pairing-friendly curves.
//!
//! Elements are held in Montgomery form; see [`montgomery_256`](super::montgomery_256) for the
//! representation and for why the crate's existing wide-integer operations are not used.
//!
//! The modulus arrives through the [`PrimeModulus256`] trait rather than as a const generic,
//! because a const generic parameter cannot be 256 bits wide. That is the same device
//! [`IrreduciblePolynomial`](super::extension_field::IrreduciblePolynomial) already uses to carry
//! an extension field's modulus.

use std::{
    fmt::{Debug, Display, Formatter},
    hash::{Hash, Hasher},
    marker::PhantomData,
    ops,
};

use proptest::{
    prelude::{any, Arbitrary},
    strategy::{BoxedStrategy, Strategy},
};
use rand::{CryptoRng, RngCore};
use serde::{
    de::{self, SeqAccess, Visitor},
    ser::{SerializeTuple, Serializer},
    Deserialize, Deserializer, Serialize,
};

use crate::{
    fields::{
        montgomery_256::{self, LIMBS},
        trim_limbs, KnownOrder, RootOfUnityError,
    },
    identities::{One, Zero},
    impl_add_variants, impl_div_variants, impl_mul_variants, impl_sub_variants,
    integers::big_uint::BigUInt,
    FiniteField, ParseFieldElementError, Ring,
};

/// A prime modulus of at most 256 bits.
///
/// # Correctness
/// `MODULUS` must be an odd prime. Oddness is what makes `R = 2^256` invertible modulo p, and the
/// whole representation rests on it; a composite modulus yields a ring with zero divisors in which
/// [`FiniteField::inverse`] returns a silently wrong value for the non-units.
pub trait PrimeModulus256: Copy + Clone + Debug + Eq + PartialEq + Hash + 'static {
    /// p, as little-endian 64-bit limbs.
    const MODULUS: [u64; LIMBS];
}

/// Element of the prime field of order `M::MODULUS`.
pub struct PrimeFieldElement256<M: PrimeModulus256> {
    /// `a * R mod p`, with `R = 2^256`.
    ///
    /// Private so that neither the reduced-residue invariant nor the choice of representation can
    /// be broken from outside: every operation here assumes the stored value is below p. Equality
    /// and hashing key on it, which is sound because the Montgomery map is a bijection on `[0,p)`,
    /// so two elements agree in one representation exactly when they agree in the other.
    value: [u64; LIMBS],
    modulus: PhantomData<M>,
}

// The impls below are written out rather than derived: a derive would bound the modulus marker
// type M by each trait, even though M appears only in a `PhantomData`.

impl<M: PrimeModulus256> Clone for PrimeFieldElement256<M> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<M: PrimeModulus256> Copy for PrimeFieldElement256<M> {}

impl<M: PrimeModulus256> PartialEq for PrimeFieldElement256<M> {
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value
    }
}

impl<M: PrimeModulus256> Eq for PrimeFieldElement256<M> {}

impl<M: PrimeModulus256> Hash for PrimeFieldElement256<M> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.value.hash(state);
    }
}

impl<M: PrimeModulus256> Debug for PrimeFieldElement256<M> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        // The canonical residue, not the stored limbs: a Montgomery representative is not a
        // number anyone wants to read in a test failure.
        write!(f, "{}", self.to_big_uint())
    }
}

impl<M: PrimeModulus256> Display for PrimeFieldElement256<M> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.to_big_uint())
    }
}

impl<M: PrimeModulus256> Default for PrimeFieldElement256<M> {
    fn default() -> Self {
        Self::ZERO
    }
}

impl<M: PrimeModulus256> PrimeFieldElement256<M> {
    /// `-p^{-1} mod 2^64`.
    const P_PRIME: u64 = montgomery_256::n_prime(M::MODULUS[0]);

    /// `R mod p`, which is the Montgomery representative of one.
    const R: [u64; LIMBS] = montgomery_256::power_of_two_mod_p(256, &M::MODULUS);

    /// `R^2 mod p`, which converts a canonical residue into Montgomery form by one multiplication.
    const R_SQUARED: [u64; LIMBS] = montgomery_256::power_of_two_mod_p(512, &M::MODULUS);

    /// The order q = p, as limbs. See [`KnownOrder::order_limbs`].
    const ORDER_LIMBS: [u64; LIMBS] = M::MODULUS;

    /// The index of the modulus' highest nonzero limb.
    ///
    /// Four for the two provided fields, lower for a narrower modulus. Anything that derives a
    /// bit width from the modulus must go through this rather than assume `LIMBS - 1`.
    const TOP_LIMB: usize = montgomery_256::highest_occupied_limb(&M::MODULUS);

    /// The element whose canonical residue is `limbs`, or `None` if `limbs` is not reduced.
    ///
    /// Rejecting rather than reducing: a value outside `[0,p)` did not come from this field, so it
    /// signals corruption or a mismatched modulus, and reinterpreting it silently would hide that.
    /// Use [`Self::from_limbs_reduced`] where reduction is what is wanted.
    pub fn from_canonical_limbs(limbs: [u64; LIMBS]) -> Option<Self> {
        if !montgomery_256::less_than(&limbs, &M::MODULUS) {
            return None;
        }
        Some(Self {
            value: montgomery_256::mul(&limbs, &Self::R_SQUARED, &M::MODULUS, Self::P_PRIME),
            modulus: PhantomData,
        })
    }

    /// The element congruent to `limbs` modulo p, reducing if necessary.
    ///
    /// Named for what it does, so that a caller cannot reach reduction by accident where
    /// [`Self::from_canonical_limbs`] was meant.
    pub fn from_limbs_reduced(limbs: [u64; LIMBS]) -> Self {
        let reduced = &BigUInt::new(&limbs) % &BigUInt::new(&M::MODULUS);
        Self::from_canonical_limbs(limbs_from_big_uint(&reduced))
            .expect("a remainder modulo p is reduced")
    }

    /// The element's canonical residue in `[0,p)`, as little-endian limbs.
    ///
    /// This is a Montgomery reduction rather than a field read, so a hot loop should hold field
    /// elements and convert at the boundary rather than call this per iteration.
    pub fn canonical_limbs(&self) -> [u64; LIMBS] {
        let one = [1u64, 0, 0, 0];
        montgomery_256::mul(&self.value, &one, &M::MODULUS, Self::P_PRIME)
    }

    /// The element's canonical residue in `[0,p)`.
    pub fn to_big_uint(&self) -> BigUInt {
        BigUInt::new(&self.canonical_limbs())
    }

    /// The canonical residue as 32 little-endian bytes.
    pub fn to_bytes_le(&self) -> [u8; 32] {
        let mut bytes = [0u8; 32];
        for (i, limb) in self.canonical_limbs().iter().enumerate() {
            bytes[i * 8..(i + 1) * 8].copy_from_slice(&limb.to_le_bytes());
        }
        bytes
    }

    /// The element encoded by 32 little-endian bytes, or `None` if they are not reduced.
    pub fn try_from_bytes_le(bytes: &[u8; 32]) -> Option<Self> {
        let mut limbs = [0u64; LIMBS];
        for (i, limb) in limbs.iter_mut().enumerate() {
            *limb = u64::from_le_bytes(bytes[i * 8..(i + 1) * 8].try_into().expect("eight bytes"));
        }
        Self::from_canonical_limbs(limbs)
    }
}

/// `value`'s limbs, zero-extended to the field's width.
///
/// `BigUInt` drops higher-order zero words, so a small residue has fewer than `LIMBS` of them.
fn limbs_from_big_uint(value: &BigUInt) -> [u64; LIMBS] {
    let words = value.as_le_words();
    assert!(words.len() <= LIMBS, "{value} is wider than {LIMBS} limbs");
    let mut limbs = [0u64; LIMBS];
    limbs[..words.len()].copy_from_slice(words);
    limbs
}

impl<M: PrimeModulus256> Zero for PrimeFieldElement256<M> {
    const ZERO: Self = Self {
        value: [0u64; LIMBS],
        modulus: PhantomData,
    };
}

impl<M: PrimeModulus256> One for PrimeFieldElement256<M> {
    // One is `R mod p` in this representation, not the limbs of the integer one.
    const ONE: Self = Self {
        value: Self::R,
        modulus: PhantomData,
    };
}

impl<M: PrimeModulus256> Ring for PrimeFieldElement256<M> {}

impl<M: PrimeModulus256> FiniteField for PrimeFieldElement256<M> {
    fn new(val: u64) -> Self {
        let limbs = [val, 0, 0, 0];
        match Self::from_canonical_limbs(limbs) {
            // The usual case: a u64 cannot reach a modulus of more than one limb.
            Some(element) => element,
            // A modulus small enough for a u64 to pass it needs real reduction. `new` is a
            // constructor from a small integer and not on any hot path, so the `BigUInt`
            // remainder is acceptable here.
            None => Self::from_limbs_reduced(limbs),
        }
    }

    fn from_str(value: &str) -> Result<Self, ParseFieldElementError> {
        let parsed = BigUInt::from_dec_str(value)?;
        let residue = &parsed % &BigUInt::new(&M::MODULUS);
        Ok(Self::from_canonical_limbs(limbs_from_big_uint(&residue))
            .expect("a remainder modulo p is reduced"))
    }

    fn random<R: RngCore + CryptoRng>(rng: &mut R) -> Self {
        // Rejection sampling, masked down to the bit width of p so that fewer than half of all
        // draws are rejected. Reducing a uniform 256-bit integer modulo a 254-bit prime would
        // favour the low residues instead.
        //
        // The mask comes from the highest *occupied* limb, and the limbs above it are left zero.
        // Taking it from `MODULUS[LIMBS - 1]` unconditionally would shift by 64 for any modulus
        // below 2^192 — an overflowing shift — and would draw into limbs the modulus cannot
        // reach, so every draw would be rejected and the loop would not terminate.
        let top = Self::TOP_LIMB;
        let mask = u64::MAX >> M::MODULUS[top].leading_zeros();

        loop {
            let mut limbs = [0u64; LIMBS];
            for limb in limbs.iter_mut().take(top + 1) {
                *limb = rng.next_u64();
            }
            limbs[top] &= mask;

            if let Some(element) = Self::from_canonical_limbs(limbs) {
                return element;
            }
        }
    }

    fn inverse(&self) -> Self {
        Self {
            value: montgomery_256::inverse(&self.value, &M::MODULUS, &Self::R_SQUARED),
            modulus: PhantomData,
        }
    }
}

impl<M: PrimeModulus256> KnownOrder for PrimeFieldElement256<M> {
    fn order_limbs() -> &'static [u64] {
        trim_limbs(&Self::ORDER_LIMBS)
    }

    fn characteristic_limbs() -> &'static [u64] {
        // Prime order, so q = p and k = 1.
        trim_limbs(&Self::ORDER_LIMBS)
    }

    /// No generator: [`RootOfUnityError::NoKnownGenerator`], rather than a search.
    ///
    /// The default searches by testing candidate orders against the prime factors of q - 1, which
    /// means factoring a 254-bit integer. That is not a computation this crate should start by
    /// accident, and no algorithm in it needs a generator of a field this large.
    fn try_primitive_element<R: RngCore + CryptoRng>(
        _rng: &mut R,
    ) -> Result<Self, RootOfUnityError> {
        Err(RootOfUnityError::NoKnownGenerator)
    }

    /// A primitive nth root of unity, for n a power of two.
    ///
    /// The default would factor `q - 1` to find a generator. For a power-of-two n the two-adic
    /// construction needs no generator at all — see [`two_adic`](super::two_adic) — and a
    /// power-of-two n is the only kind the NTT uses. Any other n still needs the factorization,
    /// and so is [`RootOfUnityError::NoKnownGenerator`] however many elements of that order the
    /// field holds.
    fn try_root_of_unity<R: RngCore + CryptoRng>(
        n: u64,
        rng: &mut R,
    ) -> Result<Self, RootOfUnityError> {
        if n == 0 {
            return Err(RootOfUnityError::OrderDoesNotDivide { n });
        }
        if !n.is_power_of_two() {
            return Err(RootOfUnityError::NoKnownGenerator);
        }
        Self::try_two_adic_root_of_unity(n.trailing_zeros(), rng)
    }
}

// === operators ===
//
// Borrowed/borrowed is the base case; `impl_*_variants!` derives the owned and mixed forms.

impl<M: PrimeModulus256> ops::Add<Self> for &PrimeFieldElement256<M> {
    type Output = PrimeFieldElement256<M>;

    fn add(self, rhs: Self) -> Self::Output {
        PrimeFieldElement256 {
            value: montgomery_256::add(&self.value, &rhs.value, &M::MODULUS),
            modulus: PhantomData,
        }
    }
}

impl_add_variants!([M: PrimeModulus256], PrimeFieldElement256<M>);

impl<M: PrimeModulus256> ops::Sub<Self> for &PrimeFieldElement256<M> {
    type Output = PrimeFieldElement256<M>;

    fn sub(self, rhs: Self) -> Self::Output {
        PrimeFieldElement256 {
            value: montgomery_256::sub(&self.value, &rhs.value, &M::MODULUS),
            modulus: PhantomData,
        }
    }
}

impl_sub_variants!([M: PrimeModulus256], PrimeFieldElement256<M>);

impl<M: PrimeModulus256> ops::Mul<Self> for &PrimeFieldElement256<M> {
    type Output = PrimeFieldElement256<M>;

    fn mul(self, rhs: Self) -> Self::Output {
        PrimeFieldElement256 {
            value: montgomery_256::mul(
                &self.value,
                &rhs.value,
                &M::MODULUS,
                PrimeFieldElement256::<M>::P_PRIME,
            ),
            modulus: PhantomData,
        }
    }
}

impl_mul_variants!([M: PrimeModulus256], PrimeFieldElement256<M>);

impl<M: PrimeModulus256> ops::Div<Self> for &PrimeFieldElement256<M> {
    type Output = PrimeFieldElement256<M>;

    fn div(self, rhs: Self) -> Self::Output {
        self * &rhs.inverse()
    }
}

impl_div_variants!([M: PrimeModulus256], PrimeFieldElement256<M>);

impl<M: PrimeModulus256> ops::Neg for PrimeFieldElement256<M> {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self::ZERO - self
    }
}

impl<M: PrimeModulus256> ops::Neg for &PrimeFieldElement256<M> {
    type Output = PrimeFieldElement256<M>;

    fn neg(self) -> Self::Output {
        PrimeFieldElement256::ZERO - self
    }
}

// === serialization ===
//
// The wire format is the canonical residue, so the Montgomery representation is invisible to a
// stored or transmitted element. Serializing the stored limbs instead would make the encoding
// depend on an internal choice and would not round-trip through any other implementation.

impl<M: PrimeModulus256> Serialize for PrimeFieldElement256<M> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut tuple = serializer.serialize_tuple(LIMBS)?;
        for limb in &self.canonical_limbs() {
            tuple.serialize_element(limb)?;
        }
        tuple.end()
    }
}

/// Reads the canonical residue back into an element.
struct CanonicalLimbsVisitor<M: PrimeModulus256> {
    modulus: PhantomData<M>,
}

impl<'de, M: PrimeModulus256> Visitor<'de> for CanonicalLimbsVisitor<M> {
    type Value = PrimeFieldElement256<M>;

    fn expecting(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{LIMBS} limbs of a reduced residue")
    }

    fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
    where
        A: SeqAccess<'de>,
    {
        let mut limbs = [0u64; LIMBS];
        for (i, limb) in limbs.iter_mut().enumerate() {
            *limb = seq
                .next_element()?
                .ok_or_else(|| de::Error::invalid_length(i, &self))?;
        }
        // Rejected rather than reduced, for the reason given on `from_canonical_limbs`.
        PrimeFieldElement256::from_canonical_limbs(limbs).ok_or_else(|| {
            de::Error::custom(format!(
                "{} is not a reduced residue modulo {}",
                BigUInt::new(&limbs),
                BigUInt::new(&M::MODULUS)
            ))
        })
    }
}

impl<'de, M: PrimeModulus256> Deserialize<'de> for PrimeFieldElement256<M> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_tuple(
            LIMBS,
            CanonicalLimbsVisitor::<M> {
                modulus: PhantomData,
            },
        )
    }
}

impl<M: PrimeModulus256> Arbitrary for PrimeFieldElement256<M> {
    type Parameters = ();

    fn arbitrary_with(_args: Self::Parameters) -> Self::Strategy {
        // Reduced rather than rejected, so that every draw yields a value and the strategy
        // shrinks. Uniformity is `random`'s job; coverage is this one's.
        any::<[u64; LIMBS]>()
            .prop_map(Self::from_limbs_reduced)
            .boxed()
    }

    type Strategy = BoxedStrategy<Self>;
}

// === the target fields ===

/// The scalar field modulus of the BN254 curve, 254 bits.
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct Bn254FrModulus;

impl PrimeModulus256 for Bn254FrModulus {
    // 21888242871839275222246405745257275088548364400416034343698204186575808495617,
    // checked against the decimal form in this module's tests.
    const MODULUS: [u64; LIMBS] = [
        0x43e1f593f0000001,
        0x2833e84879b97091,
        0xb85045b68181585d,
        0x30644e72e131a029,
    ];
}

/// The scalar field modulus of the BLS12-381 curve, 255 bits.
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct Bls12_381FrModulus;

impl PrimeModulus256 for Bls12_381FrModulus {
    // 52435875175126190479447740508185965837690552500527637822603658699938581184513
    const MODULUS: [u64; LIMBS] = [
        0xffffffff00000001,
        0x53bda402fffe5bfe,
        0x3339d80809a1d805,
        0x73eda753299d7d48,
    ];
}

/// The Proth prime 3*2^66 + 1 = 221360928884514619393, 68 bits.
///
/// Occupies the low two limbs, which is the whole point: a modulus between 2^64 and 2^128 is
/// served here rather than by the deprecated [`PrimeFieldElement128`](crate::fields::PrimeFieldElement128).
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct Proth68FrModulus;

impl PrimeModulus256 for Proth68FrModulus {
    // 3*2^66 + 1 = 12*2^64 + 1, checked against its decimal and its two-adicity in the tests.
    const MODULUS: [u64; LIMBS] = [1, 12, 0, 0];
}

/// The BN254 curve's scalar field, of 254-bit prime order.
pub type Bn254Fr = PrimeFieldElement256<Bn254FrModulus>;

/// The field of order 3*2^66 + 1, the NTT-friendly 68-bit prime of two-adicity 66.
///
/// The replacement for the deprecated
/// [`Zp221360928884514619393`](crate::fields::Zp221360928884514619393), which is the same field
/// over a `u128` that reduces by software long division. Same modulus, same arithmetic, and
/// multiplication and inversion are faster by the factors recorded in the README's field table.
pub type Proth68Fr = PrimeFieldElement256<Proth68FrModulus>;

/// The BLS12-381 curve's scalar field, of 255-bit prime order.
pub type Bls12_381Fr = PrimeFieldElement256<Bls12_381FrModulus>;

/// BN254's scalar field modulus in decimal, as published.
///
/// Public so that a caller can check the limbs this crate compiled in against the value they
/// expect, which is what `test_bn254_modulus_limbs_match_the_published_decimal` does.
pub const BN254_FR_MODULUS_DECIMAL: &str =
    "21888242871839275222246405745257275088548364400416034343698204186575808495617";

/// BLS12-381's scalar field modulus in decimal, as published.
pub const BLS12_381_FR_MODULUS_DECIMAL: &str =
    "52435875175126190479447740508185965837690552500527637822603658699938581184513";

#[cfg(test)]
// `ark_ff::MontConfig` expands to a check of ark-ff's own `asm` feature, which is not a feature
// of this crate. The derive is only used by the test oracle.
#[allow(unexpected_cfgs)]
mod tests {
    use std::collections::HashSet;

    use ark_ff::{
        fields::{Fp256, MontBackend, MontConfig},
        PrimeField,
    };
    use proptest::{prelude::any, proptest};
    use rand::{prelude::StdRng, SeedableRng};

    use super::*;

    // The oracle. `ark-ff` is a dev-dependency, declared from the same decimal moduli, so these
    // two types are an independent implementation of the same two fields. The generators are the
    // published ones; nothing here uses them, but `MontConfig` requires the attribute.

    #[derive(MontConfig)]
    #[modulus = "21888242871839275222246405745257275088548364400416034343698204186575808495617"]
    #[generator = "5"]
    struct ArkBn254FrConfig;
    type ArkBn254Fr = Fp256<MontBackend<ArkBn254FrConfig, 4>>;

    #[derive(MontConfig)]
    #[modulus = "52435875175126190479447740508185965837690552500527637822603658699938581184513"]
    #[generator = "7"]
    struct ArkBls12_381FrConfig;
    type ArkBls12_381Fr = Fp256<MontBackend<ArkBls12_381FrConfig, 4>>;

    /// A zeebra element carrying the same residue as an oracle element.
    fn from_oracle<M: PrimeModulus256, O: PrimeField<BigInt = ark_ff::BigInt<4>>>(
        a: O,
    ) -> PrimeFieldElement256<M> {
        PrimeFieldElement256::from_canonical_limbs(a.into_bigint().0)
            .expect("the oracle's canonical form is reduced")
    }

    /// Agreement with the oracle on add, sub, mul, square, negate and invert.
    ///
    /// Generic over both the zeebra field and its oracle so that each target field is checked by
    /// the same body, and the two cannot drift apart.
    fn agrees_with_oracle<M, O>(seed: u64, cases: usize)
    where
        M: PrimeModulus256,
        O: PrimeField<BigInt = ark_ff::BigInt<4>>,
    {
        let mut rng = StdRng::seed_from_u64(seed);
        type Z<M> = PrimeFieldElement256<M>;

        // Random residues, then the edges: zero, one, and p - 1.
        let mut pairs: Vec<(O, O)> = (0..cases)
            .map(|_| {
                (
                    O::from_le_bytes_mod_order(&random_bytes(&mut rng)),
                    O::from_le_bytes_mod_order(&random_bytes(&mut rng)),
                )
            })
            .collect();
        let edges = [O::ZERO, O::ONE, -O::ONE];
        for a in edges {
            for b in edges {
                pairs.push((a, b));
            }
        }

        for (i, (a, b)) in pairs.into_iter().enumerate() {
            let (za, zb): (Z<M>, Z<M>) = (from_oracle(a), from_oracle(b));

            assert_eq!(
                (a + b).into_bigint().0,
                (za + zb).canonical_limbs(),
                "add, case {i}"
            );
            assert_eq!(
                (a - b).into_bigint().0,
                (za - zb).canonical_limbs(),
                "sub, case {i}"
            );
            assert_eq!(
                (a * b).into_bigint().0,
                (za * zb).canonical_limbs(),
                "mul, case {i}"
            );
            assert_eq!(
                a.square().into_bigint().0,
                (za * za).canonical_limbs(),
                "square, case {i}"
            );
            assert_eq!(
                (-a).into_bigint().0,
                (-za).canonical_limbs(),
                "neg, case {i}"
            );

            if !a.is_zero() {
                assert_eq!(
                    a.inverse().expect("nonzero").into_bigint().0,
                    za.inverse().canonical_limbs(),
                    "inverse, case {i}"
                );
                assert_eq!(
                    (b / a).into_bigint().0,
                    (zb / za).canonical_limbs(),
                    "div, case {i}"
                );
            }
        }
    }

    /// 32 random bytes, for driving the oracle's own reduction.
    fn random_bytes(rng: &mut StdRng) -> [u8; 32] {
        let mut bytes = [0u8; 32];
        for chunk in bytes.chunks_mut(8) {
            chunk.copy_from_slice(&rand::RngCore::next_u64(rng).to_le_bytes());
        }
        bytes
    }

    /// The BN254 modulus limbs are the published decimal value, checked without the oracle.
    #[test]
    fn test_bn254_modulus_limbs_match_the_published_decimal() {
        let decimal = BigUInt::from_dec_str(BN254_FR_MODULUS_DECIMAL).expect("valid decimal");
        assert_eq!(limbs_from_big_uint(&decimal), Bn254FrModulus::MODULUS);
        // 254 bits: the top bit of a 256-bit value is clear, and so is the one below it.
        assert_eq!(Bn254FrModulus::MODULUS[LIMBS - 1].leading_zeros(), 2);
    }

    /// The BLS12-381 modulus limbs are the published decimal value, checked without the oracle.
    #[test]
    fn test_bls12_381_modulus_limbs_match_the_published_decimal() {
        let decimal = BigUInt::from_dec_str(BLS12_381_FR_MODULUS_DECIMAL).expect("valid decimal");
        assert_eq!(limbs_from_big_uint(&decimal), Bls12_381FrModulus::MODULUS);
        // 255 bits.
        assert_eq!(Bls12_381FrModulus::MODULUS[LIMBS - 1].leading_zeros(), 1);
    }

    /// The oracle derived the same moduli from the same decimal strings.
    ///
    /// Without this, agreement on arithmetic would only show the two agree with each other over
    /// *some* field.
    #[test]
    fn test_the_oracle_is_over_the_same_fields() {
        assert_eq!(
            <ArkBn254Fr as PrimeField>::MODULUS.0,
            Bn254FrModulus::MODULUS
        );
        assert_eq!(
            <ArkBls12_381Fr as PrimeField>::MODULUS.0,
            Bls12_381FrModulus::MODULUS
        );
    }

    /// BN254 arithmetic agrees with the independent implementation.
    #[test]
    fn test_bn254_agrees_with_the_oracle() {
        agrees_with_oracle::<Bn254FrModulus, ArkBn254Fr>(7, 20_000);
    }

    /// BLS12-381 arithmetic agrees with the independent implementation.
    #[test]
    fn test_bls12_381_agrees_with_the_oracle() {
        agrees_with_oracle::<Bls12_381FrModulus, ArkBls12_381Fr>(8, 20_000);
    }

    /// A nonzero element times its inverse is one.
    #[test]
    fn test_element_times_inverse_is_one() {
        let mut rng = StdRng::seed_from_u64(9);
        for _ in 0..2_000 {
            let a = Bn254Fr::random(&mut rng);
            if a.is_zero() {
                continue;
            }
            assert_eq!(a * a.inverse(), Bn254Fr::one());
        }
        // p - 1 is its own inverse, being -1.
        let minus_one = -Bn254Fr::one();
        assert_eq!(minus_one * minus_one.inverse(), Bn254Fr::one());
        assert_eq!(Bn254Fr::one().inverse(), Bn254Fr::one());
    }

    /// Zero has no multiplicative inverse.
    #[test]
    #[should_panic(expected = "does not have a multiplicative inverse")]
    fn test_inverse_of_zero_panics() {
        let _boom = Bn254Fr::zero().inverse();
    }

    /// `pow` agrees with repeated multiplication, which exercises the `u128` exponent path.
    #[test]
    fn test_pow_agrees_with_repeated_multiplication() {
        let mut rng = StdRng::seed_from_u64(10);
        let a = Bn254Fr::random(&mut rng);
        let mut expected = Bn254Fr::one();
        for exponent in 0..50u128 {
            assert_eq!(a.pow(exponent), expected, "a^{exponent}");
            expected *= a;
        }
    }

    /// Every sampled element is a reduced residue, and sampling does not repeat itself.
    #[test]
    fn test_random_is_reduced_and_varied() {
        let mut rng = StdRng::seed_from_u64(11);
        let mut seen = HashSet::new();
        for _ in 0..5_000 {
            let a = Bn254Fr::random(&mut rng);
            assert!(montgomery_256::less_than(
                &a.canonical_limbs(),
                &Bn254FrModulus::MODULUS
            ));
            seen.insert(a);
        }
        assert_eq!(seen.len(), 5_000, "a 254-bit field should not collide");
    }

    /// Sampling is unbiased in the low bits, where masked rejection would show a skew.
    ///
    /// A full chi-squared test over a 254-bit field is impossible, but the residues are uniform
    /// on [0,p) only if their low bits are uniform, and reducing a 256-bit draw instead of
    /// rejecting it would bias exactly those.
    #[test]
    fn test_random_is_unbiased_in_the_low_bits() {
        const BUCKETS: usize = 16;
        const DRAWS: usize = 200_000;

        let mut rng = StdRng::seed_from_u64(12);
        let mut counts = [0usize; BUCKETS];
        for _ in 0..DRAWS {
            let low = Bn254Fr::random(&mut rng).canonical_limbs()[0];
            counts[(low % BUCKETS as u64) as usize] += 1;
        }

        let expected = DRAWS as f64 / BUCKETS as f64;
        let chi_squared: f64 = counts
            .iter()
            .map(|&count| {
                let deviation = count as f64 - expected;
                deviation * deviation / expected
            })
            .sum();

        // 37.7 is the 0.999 quantile of chi-squared with 15 degrees of freedom.
        assert!(
            chi_squared < 37.7,
            "chi-squared {chi_squared:.1}: {counts:?}"
        );
    }

    /// A canonical encoding round-trips through serde and through bytes.
    #[test]
    fn test_canonical_encoding_round_trips() {
        let mut rng = StdRng::seed_from_u64(13);
        for _ in 0..500 {
            let a = Bn254Fr::random(&mut rng);

            let encoded = bincode::serialize(&a).expect("serializable");
            let decoded: Bn254Fr = bincode::deserialize(&encoded).expect("round trip");
            assert_eq!(a, decoded);

            let bytes = a.to_bytes_le();
            assert_eq!(Bn254Fr::try_from_bytes_le(&bytes), Some(a));
        }
    }

    /// The wire format is the canonical residue, not the Montgomery representative.
    ///
    /// Without this, the encoding would depend on an internal representation choice and would not
    /// agree with any other implementation of the same field.
    #[test]
    fn test_serialization_is_the_canonical_residue() {
        let seven = Bn254Fr::new(7);
        assert_eq!(seven.to_bytes_le()[0], 7);
        assert_eq!(seven.to_bytes_le()[1..], [0u8; 31]);

        let encoded = bincode::serialize(&seven).expect("serializable");
        let as_limbs: [u64; LIMBS] = bincode::deserialize(&encoded).expect("four limbs");
        assert_eq!(as_limbs, [7, 0, 0, 0]);
    }

    /// Encodings at or above the modulus are rejected rather than reduced.
    #[test]
    fn test_non_canonical_encodings_are_rejected() {
        let modulus = Bn254FrModulus::MODULUS;
        let mut above = modulus;
        above[0] += 1;

        for limbs in [modulus, above, [u64::MAX; LIMBS]] {
            assert_eq!(
                Bn254Fr::from_canonical_limbs(limbs),
                None,
                "{limbs:?} should be rejected"
            );

            let encoded = bincode::serialize(&limbs).expect("serializable");
            let decoded: Result<Bn254Fr, _> = bincode::deserialize(&encoded);
            assert!(decoded.is_err(), "{limbs:?} should not deserialize");
        }
    }

    /// The explicitly named constructor reduces where the canonical one refuses.
    #[test]
    fn test_from_limbs_reduced_reduces() {
        let modulus = Bn254FrModulus::MODULUS;
        assert_eq!(Bn254Fr::from_limbs_reduced(modulus), Bn254Fr::zero());

        let mut above = modulus;
        above[0] += 1;
        assert_eq!(Bn254Fr::from_limbs_reduced(above), Bn254Fr::one());
    }

    /// Parsing and `Display` agree, and parsing reduces out-of-range decimals.
    #[test]
    fn test_parsing_and_display_round_trip() {
        for decimal in ["0", "1", "7", "123456789012345678901234567890"] {
            let parsed = <Bn254Fr as FiniteField>::from_str(decimal).expect("valid decimal");
            assert_eq!(parsed.to_string(), decimal);
        }

        // The modulus itself parses to zero, as a reduction.
        let p = <Bn254Fr as FiniteField>::from_str(BN254_FR_MODULUS_DECIMAL).expect("valid");
        assert_eq!(p, Bn254Fr::zero());

        // p - 1 is the largest representable residue and prints in full.
        let expected = BigUInt::from_dec_str(BN254_FR_MODULUS_DECIMAL).expect("valid")
            - &BigUInt::new_from_u64(1);
        assert_eq!((-Bn254Fr::one()).to_string(), expected.to_string());
    }

    /// A non-digit is reported rather than accepted.
    #[test]
    fn test_parsing_rejects_a_non_digit() {
        assert!(matches!(
            <Bn254Fr as FiniteField>::from_str("12x4"),
            Err(ParseFieldElementError::InvalidCharacter(_))
        ));
    }

    /// `KnownOrder` reports a four-limb order, and the characteristic equals it.
    #[test]
    fn test_known_order_reports_the_modulus() {
        assert_eq!(Bn254Fr::order_limbs(), Bn254FrModulus::MODULUS);
        assert_eq!(Bn254Fr::characteristic_limbs(), Bn254FrModulus::MODULUS);
        // The whole point of the `KnownOrder` split: this order does not fit in a u128.
        assert_eq!(Bn254Fr::order_u128(), None);
        assert_eq!(Bls12_381Fr::order_u128(), None);
    }

    /// The two-adicity of both fields agrees with `ark-ff`'s own constant.
    ///
    /// The oracle check on the figure every NTT size over these fields is bounded by. zeebra
    /// derives it from the compiled-in modulus; `ark-ff` carries it as a `FftField` constant
    /// computed by its own derive from the same decimal. `two_adic::tests` separately checks the
    /// derivation against `q - 1` without any oracle.
    #[test]
    fn test_two_adicity_agrees_with_the_oracle() {
        assert_eq!(
            Bn254Fr::two_adicity(),
            <ArkBn254Fr as ark_ff::FftField>::TWO_ADICITY
        );
        assert_eq!(
            Bls12_381Fr::two_adicity(),
            <ArkBls12_381Fr as ark_ff::FftField>::TWO_ADICITY
        );
        // The values themselves, so a change to either side is visible rather than merely equal.
        assert_eq!(Bn254Fr::two_adicity(), 28);
        assert_eq!(Bls12_381Fr::two_adicity(), 32);
    }

    /// `root_of_unity` now works over a wide field, for a power-of-two order.
    ///
    /// It was `unimplemented!()`, which is what left the crate with no NTT over these fields at
    /// all (`docs/MILESTONE-LARGE-PRIME-FIELDS.md` §7, open item 6).
    #[test]
    fn test_root_of_unity_over_a_wide_field() {
        let mut rng = StdRng::seed_from_u64(21);
        for log_n in 0..=12u32 {
            let n = 1u64 << log_n;
            let w = Bn254Fr::root_of_unity(n, &mut rng);
            assert!(w.pow(n as u128).is_one(), "w^{n} != 1");
            if n > 1 {
                assert!(!w.pow(n as u128 / 2).is_one(), "w is not primitive");
            }
        }
    }

    /// An order that is not a power of two still needs the factorization of `q - 1`.
    #[test]
    fn test_root_of_unity_of_non_power_of_two_order_is_an_error() {
        let mut rng = StdRng::seed_from_u64(22);
        assert_eq!(
            Bn254Fr::try_root_of_unity(3, &mut rng),
            Err(RootOfUnityError::NoKnownGenerator)
        );
    }

    /// An order beyond `2^s` does not exist in the field, and is refused rather than approximated.
    #[test]
    fn test_root_of_unity_beyond_the_two_adicity_is_an_error() {
        let mut rng = StdRng::seed_from_u64(23);
        assert_eq!(
            Bn254Fr::try_root_of_unity(1 << 29, &mut rng),
            Err(RootOfUnityError::TwoAdicityExceeded {
                log_n: 29,
                two_adicity: 28,
            })
        );
    }

    /// The panicking form of the same request still aborts, for the call sites that take it.
    #[test]
    #[should_panic(expected = "the two-adicity of this field is 28")]
    fn test_root_of_unity_beyond_the_two_adicity_panics() {
        let mut rng = StdRng::seed_from_u64(23);
        let _ = Bn254Fr::root_of_unity(1 << 29, &mut rng);
    }

    /// Finding a generator of the whole multiplicative group is still not attempted.
    #[test]
    fn test_primitive_element_is_still_not_searched_for() {
        let mut rng = StdRng::seed_from_u64(24);
        assert_eq!(
            Bn254Fr::try_primitive_element(&mut rng),
            Err(RootOfUnityError::NoKnownGenerator)
        );
    }

    /// Equal elements hash equally, which `Hash`'s contract with `Eq` requires.
    #[test]
    fn test_equal_elements_hash_equally() {
        let mut rng = StdRng::seed_from_u64(14);
        for _ in 0..200 {
            let a = Bn254Fr::random(&mut rng);
            let same = <Bn254Fr as FiniteField>::from_str(&a.to_string()).expect("its own decimal");
            assert_eq!(a, same);

            let mut set = HashSet::new();
            set.insert(a);
            assert!(set.contains(&same), "{a} and {same} must hash alike");
        }
    }

    proptest! {
        /// The field laws hold on arbitrary elements.
        #[test]
        fn test_the_field_laws_hold(
            a in any::<Bn254Fr>(),
            b in any::<Bn254Fr>(),
            c in any::<Bn254Fr>(),
        ) {
            assert_eq!(a + b, b + a);
            assert_eq!(a * b, b * a);
            assert_eq!((a + b) + c, a + (b + c));
            assert_eq!((a * b) * c, a * (b * c));
            assert_eq!(a * (b + c), a * b + a * c);
            assert_eq!(a + Bn254Fr::zero(), a);
            assert_eq!(a * Bn254Fr::one(), a);
            assert_eq!(a - a, Bn254Fr::zero());
            assert_eq!(a + (-a), Bn254Fr::zero());
            if !a.is_zero() {
                assert_eq!(a * a.inverse(), Bn254Fr::one());
                assert_eq!(b / a * a, b);
            }
        }
    }

    // === narrower moduli ===
    //
    // `PrimeModulus256` promises support for any odd prime of at most 256 bits, and the two
    // provided fields both occupy all four limbs — so they cannot catch a width assumption. These
    // three sit at one, two and three limbs.

    /// GF(7), one limb. Small enough to check exhaustively against `PrimeFieldElement64`.
    #[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
    struct Modulus7;
    impl PrimeModulus256 for Modulus7 {
        const MODULUS: [u64; LIMBS] = [7, 0, 0, 0];
    }
    type F7 = PrimeFieldElement256<Modulus7>;

    /// The Mersenne prime 2^127 - 1, two limbs with the top limb's high bit clear.
    #[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
    struct Mersenne127;
    impl PrimeModulus256 for Mersenne127 {
        const MODULUS: [u64; LIMBS] = [u64::MAX, u64::MAX >> 1, 0, 0];
    }
    type F127 = PrimeFieldElement256<Mersenne127>;

    /// The NIST P-192 prime 2^192 - 2^64 - 1, three limbs with the top limb full.
    #[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
    struct P192;
    impl PrimeModulus256 for P192 {
        const MODULUS: [u64; LIMBS] = [u64::MAX, u64::MAX - 1, u64::MAX, 0];
    }
    type F192 = PrimeFieldElement256<P192>;

    /// The three narrow moduli are the values they are meant to be.
    #[test]
    fn test_the_narrow_moduli_are_as_intended() {
        assert_eq!(F7::order_u128(), Some(7));
        assert_eq!(F127::order_u128(), Some((1u128 << 127) - 1));
        // 2^192 - 2^64 - 1 does not fit a u128, so check it through BigUInt instead.
        assert_eq!(
            BigUInt::new(&P192::MODULUS).to_string(),
            "6277101735386680763835789423207666416083908700390324961279"
        );

        // And the limb width each one occupies, which is what the sampler and `new` turn on.
        assert_eq!(F7::order_limbs().len(), 1);
        assert_eq!(F127::order_limbs().len(), 2);
        assert_eq!(F192::order_limbs().len(), 3);
        assert_eq!(Bn254Fr::order_limbs().len(), 4);
    }

    /// `new` reduces a `u64` that reaches past a narrow modulus instead of panicking.
    ///
    /// Regression: `new` asserted that every `u64` is below the modulus, which holds only for a
    /// modulus of more than one limb.
    #[test]
    fn test_new_reduces_past_a_narrow_modulus() {
        assert_eq!(F7::new(8), F7::new(1));
        assert_eq!(F7::new(7), F7::zero());
        assert_eq!(F7::new(u64::MAX).canonical_limbs()[0], u64::MAX % 7);

        // A modulus of two limbs or more is beyond any u64, so no reduction happens.
        assert_eq!(F127::new(u64::MAX).canonical_limbs(), [u64::MAX, 0, 0, 0]);
        assert_eq!(
            Bn254Fr::new(u64::MAX).canonical_limbs(),
            [u64::MAX, 0, 0, 0]
        );
    }

    /// Sampling terminates and stays reduced at every modulus width.
    ///
    /// Regression: the mask was taken from `MODULUS[3]`, which is zero for any modulus below
    /// 2^192 — an overflowing shift, and then a loop that rejects every draw.
    #[test]
    fn test_random_works_at_every_modulus_width() {
        fn check<M: PrimeModulus256>(draws: usize) {
            let mut rng = StdRng::seed_from_u64(31);
            for _ in 0..draws {
                let a = <PrimeFieldElement256<M> as FiniteField>::random(&mut rng);
                assert!(
                    montgomery_256::less_than(&a.canonical_limbs(), &M::MODULUS),
                    "{a} is not reduced modulo {}",
                    BigUInt::new(&M::MODULUS)
                );
            }
        }

        check::<Modulus7>(2_000);
        check::<Mersenne127>(2_000);
        check::<P192>(2_000);
        check::<Bn254FrModulus>(2_000);
    }

    /// Sampling over GF(7) covers all seven residues and is roughly uniform.
    #[test]
    fn test_random_covers_a_tiny_field_uniformly() {
        const DRAWS: usize = 70_000;
        let mut rng = StdRng::seed_from_u64(32);
        let mut counts = [0usize; 7];
        for _ in 0..DRAWS {
            counts[F7::random(&mut rng).canonical_limbs()[0] as usize] += 1;
        }
        assert!(counts.iter().all(|&c| c > 0), "every residue should appear");

        let expected = DRAWS as f64 / 7.0;
        let chi_squared: f64 = counts
            .iter()
            .map(|&c| {
                let d = c as f64 - expected;
                d * d / expected
            })
            .sum();
        // 22.5 is the 0.999 quantile of chi-squared with 6 degrees of freedom.
        assert!(
            chi_squared < 22.5,
            "chi-squared {chi_squared:.1}: {counts:?}"
        );
    }

    /// Over GF(7) the 256-bit field agrees with the 64-bit one on every pair of residues.
    ///
    /// Two unrelated implementations — Montgomery over four limbs against Montgomery over one —
    /// checked exhaustively rather than sampled.
    #[test]
    fn test_a_tiny_field_agrees_with_the_64_bit_implementation() {
        type Narrow = crate::fields::PrimeFieldElement64<7>;

        for a in 0u64..7 {
            for b in 0u64..7 {
                let (wide_a, wide_b) = (F7::new(a), F7::new(b));
                let (narrow_a, narrow_b) = (Narrow::new(a), Narrow::new(b));

                assert_eq!(
                    (wide_a + wide_b).canonical_limbs()[0],
                    (narrow_a + narrow_b).value(),
                    "{a} + {b}"
                );
                assert_eq!(
                    (wide_a - wide_b).canonical_limbs()[0],
                    (narrow_a - narrow_b).value(),
                    "{a} - {b}"
                );
                assert_eq!(
                    (wide_a * wide_b).canonical_limbs()[0],
                    (narrow_a * narrow_b).value(),
                    "{a} * {b}"
                );
                if b != 0 {
                    assert_eq!(
                        wide_b.inverse().canonical_limbs()[0],
                        narrow_b.inverse().value(),
                        "1 / {b}"
                    );
                    assert_eq!(
                        (wide_a / wide_b).canonical_limbs()[0],
                        (narrow_a / narrow_b).value(),
                        "{a} / {b}"
                    );
                }
            }
        }
    }

    /// Arithmetic at two and three limbs agrees with big-integer arithmetic modulo p.
    ///
    /// `BigUInt` is plain long arithmetic with no Montgomery form, so this is independent of the
    /// representation under test — and independent of `ark-ff`, which cannot be instantiated at
    /// these moduli without another `MontConfig`.
    #[test]
    fn test_narrow_arithmetic_agrees_with_big_integer_arithmetic() {
        fn check<M: PrimeModulus256>(seed: u64, cases: usize) {
            type Z<M> = PrimeFieldElement256<M>;
            let modulus = BigUInt::new(&M::MODULUS);
            let mut rng = StdRng::seed_from_u64(seed);

            for i in 0..cases {
                let a = <Z<M> as FiniteField>::random(&mut rng);
                let b = <Z<M> as FiniteField>::random(&mut rng);
                let (big_a, big_b) = (a.to_big_uint(), b.to_big_uint());

                assert_eq!(
                    (a + b).to_big_uint(),
                    (&big_a + &big_b) % &modulus,
                    "add, case {i}"
                );
                assert_eq!(
                    (a * b).to_big_uint(),
                    (&big_a * &big_b) % &modulus,
                    "mul, case {i}"
                );
                // a - b, computed over the integers by adding p first to stay unsigned.
                assert_eq!(
                    (a - b).to_big_uint(),
                    (&(&big_a + &modulus) - &big_b) % &modulus,
                    "sub, case {i}"
                );
                if !a.is_zero() {
                    assert_eq!(a * a.inverse(), Z::<M>::one(), "inverse, case {i}");
                }
            }
        }

        check::<Mersenne127>(33, 2_000);
        check::<P192>(34, 2_000);
    }

    /// Canonical encoding round-trips and rejects out-of-range values at a narrow modulus too.
    #[test]
    fn test_narrow_canonical_encoding() {
        let mut rng = StdRng::seed_from_u64(35);
        for _ in 0..200 {
            let a = F127::random(&mut rng);
            let encoded = bincode::serialize(&a).expect("serializable");
            assert_eq!(bincode::deserialize::<F127>(&encoded).ok(), Some(a));
            assert_eq!(F127::try_from_bytes_le(&a.to_bytes_le()), Some(a));
        }

        // The modulus and everything above it are rejected, including values that occupy limbs
        // the modulus does not.
        for limbs in [
            Mersenne127::MODULUS,
            [u64::MAX, u64::MAX >> 1, 1, 0],
            [0, 0, 0, 1],
            [u64::MAX; LIMBS],
        ] {
            assert_eq!(F127::from_canonical_limbs(limbs), None, "{limbs:?}");
        }
    }

    /// `from_str` and `Display` round-trip at a narrow modulus, reducing where they should.
    #[test]
    fn test_narrow_parsing_and_display() {
        assert_eq!(
            <F7 as FiniteField>::from_str("13")
                .expect("valid")
                .to_string(),
            "6"
        );
        assert_eq!(
            <F7 as FiniteField>::from_str("7").expect("valid"),
            F7::zero()
        );

        let p127 = "170141183460469231731687303715884105727";
        assert_eq!(
            <F127 as FiniteField>::from_str(p127).expect("valid"),
            F127::zero()
        );
        assert_eq!(
            (-F127::one()).to_string(),
            "170141183460469231731687303715884105726"
        );
    }

    /// Root finding works over a narrow `PrimeFieldElement256`, whose order fits in a `u128`.
    ///
    /// The wide fields exercise the multi-limb exponent; this exercises the same code path at a
    /// width where the answer can be checked by trying every element.
    #[test]
    fn test_roots_over_a_tiny_prime_field_256() {
        use crate::{Polynomial, UnivariatePolynomial};

        // x^2 - 2 over GF(7): 3^2 = 2 and 4^2 = 2, so the roots are 3 and 4.
        let f = UnivariatePolynomial::<F7>::new(&[F7::zero() - F7::new(2), F7::zero(), F7::one()]);
        let mut rng = StdRng::seed_from_u64(36);
        let mut found: Vec<u64> = crate::roots(&f, &mut rng)
            .into_iter()
            .map(|r| r.canonical_limbs()[0])
            .collect();
        found.sort_unstable();
        assert_eq!(found, vec![3, 4]);

        // Cross-checked by evaluating at every element of the field.
        let by_evaluation: Vec<u64> = (0u64..7)
            .filter(|&c| f.eval(&F7::new(c)).is_zero())
            .collect();
        assert_eq!(found, by_evaluation);
    }

    // === the 68-bit Proth prime, the migration target for the deprecated 128-bit field ===
    //
    // `PrimeFieldElement128` is deprecated in favour of this type (#163). The deprecation is only
    // honest if the replacement actually serves the one modulus the 128-bit field was declared
    // for, so these three tests pin that: the modulus, agreement with the type being retired, and
    // the two-adic structure that was the sole argument for keeping a 68-bit field at all.

    /// The migration target is the same prime the deprecated 128-bit alias was declared over.
    #[test]
    fn test_the_proth_68_modulus_is_three_times_two_to_the_66_plus_one() {
        // 3*2^66 + 1 = 12*2^64 + 1, so the limbs are exactly [1, 12, 0, 0].
        assert_eq!(Proth68FrModulus::MODULUS, [1, 12, 0, 0]);
        assert_eq!(
            Proth68Fr::order_u128(),
            Some(221_360_928_884_514_619_393u128)
        );
        assert_eq!(3 * (1u128 << 66) + 1, 221_360_928_884_514_619_393u128);

        // Two limbs, so it exercises the narrow-modulus paths rather than the 4-limb ones.
        assert_eq!(Proth68Fr::order_limbs().len(), 2);
    }

    /// Arithmetic over the migration target agrees with the deprecated 128-bit field it replaces.
    #[test]
    #[allow(deprecated)]
    fn test_proth_68_agrees_with_the_deprecated_128_bit_field() {
        use crate::fields::PrimeFieldElement128;

        type Old = PrimeFieldElement128<221_360_928_884_514_619_393>;

        // Operands are drawn once and handed to both fields through their decimal form, so the two
        // sides are the same mathematical element however each represents it internally.
        let mut rng = StdRng::seed_from_u64(163);
        for _ in 0..500 {
            let a_old = <Old as FiniteField>::random(&mut rng);
            let b_old = <Old as FiniteField>::random(&mut rng);
            let a_new = <Proth68Fr as FiniteField>::from_str(&a_old.to_string()).expect("decimal");
            let b_new = <Proth68Fr as FiniteField>::from_str(&b_old.to_string()).expect("decimal");

            assert_eq!((a_old + b_old).to_string(), (a_new + b_new).to_string());
            assert_eq!((a_old - b_old).to_string(), (a_new - b_new).to_string());
            assert_eq!((a_old * b_old).to_string(), (a_new * b_new).to_string());
            if !a_old.is_zero() {
                assert_eq!(a_old.inverse().to_string(), a_new.inverse().to_string());
                assert_eq!((b_old / a_old).to_string(), (b_new / a_new).to_string());
            }
        }
    }

    /// The migration target serves the two-adic structure that justified a 68-bit field.
    ///
    /// `two_adicity` is a property of the order, not of the backing width, so an NTT-friendly
    /// prime in the 68-127 bit range was the only candidate caller #163 identified. A 256-bit
    /// backing serves it: p - 1 = 3*2^66, and a root of unity of each order has that exact order.
    #[test]
    fn test_proth_68_serves_its_two_adic_orders() {
        assert_eq!(Proth68Fr::two_adicity(), 66);

        // 2^log_n as little-endian limbs, which is how orders above 2^64 have to be expressed.
        fn two_to_the(log_n: u32) -> Vec<u64> {
            if log_n < 64 {
                vec![1u64 << log_n]
            } else {
                vec![0, 1u64 << (log_n - 64)]
            }
        }

        let mut rng = StdRng::seed_from_u64(1663);
        for log_n in [1u32, 2, 8, 32, 63, 64, 65, 66] {
            let w: Proth68Fr = crate::fields::two_adic::two_adic_root_of_unity(log_n, &mut rng);

            // Order exactly 2^log_n: w^(2^log_n) = 1 and w^(2^(log_n-1)) != 1, which for a
            // power-of-two order is the whole condition — every proper divisor divides the half.
            assert!(
                w.pow_limbs(&two_to_the(log_n)).is_one(),
                "w^(2^{log_n}) should be 1"
            );
            assert!(
                !w.pow_limbs(&two_to_the(log_n - 1)).is_one(),
                "w^(2^{log_n} / 2) should not be 1"
            );
        }

        // `root_of_unity` takes `n: u64`, so it reaches the orders up to 2^63 only; the two-adic
        // constructor above is what serves 2^64 through 2^66.
        let mut rng = StdRng::seed_from_u64(1664);
        let w = Proth68Fr::root_of_unity(1u64 << 32, &mut rng);
        assert!(w.pow_limbs(&two_to_the(32)).is_one());
        assert!(!w.pow_limbs(&two_to_the(31)).is_one());
    }
}
