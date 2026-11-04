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
        trim_limbs, KnownOrder,
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
        // A u64 is always below a 254-bit modulus, so no reduction is needed.
        Self::from_canonical_limbs([val, 0, 0, 0]).expect("a u64 is below a 254-bit modulus")
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
        let top = M::MODULUS[LIMBS - 1];
        let mask = u64::MAX >> top.leading_zeros();

        loop {
            let mut limbs = [0u64; LIMBS];
            for limb in limbs.iter_mut() {
                *limb = rng.next_u64();
            }
            limbs[LIMBS - 1] &= mask;

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

    fn primitive_element<R: RngCore + CryptoRng>(_rng: &mut R) -> Self {
        // The default searches by testing candidate orders against the prime factors of q - 1,
        // which means factoring a 254-bit integer. That is not a computation this crate should
        // start by accident, and no algorithm in it needs a generator of a field this large.
        unimplemented!(
            "finding a generator of a 254-bit field's multiplicative group needs the \
             factorization of q - 1"
        )
    }

    fn root_of_unity<R: RngCore + CryptoRng>(_n: u64, _rng: &mut R) -> Self {
        // Reachable only through `primitive_element`. A two-adic root of unity is derivable from
        // the field's two-adicity without factoring, but nothing here asks for one yet.
        unimplemented!("a root of unity in a 254-bit field needs a known generator")
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

/// The BN254 curve's scalar field, of 254-bit prime order.
pub type Bn254Fr = PrimeFieldElement256<Bn254FrModulus>;

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
}
