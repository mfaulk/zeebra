//! Fields GF(p^n) of prime-power order.
//!
//! For prime p, the field GF(q) with q = p^n is represented as polynomials over GF(p) of degree
//! strictly less than n. Addition and subtraction are the coefficientwise operations of GF(p). The
//! product of a and b is the remainder of ab on Euclidean division by a monic irreducible
//! polynomial of degree n, supplied by the [`IrreduciblePolynomial`] parameter. That reduction is
//! what keeps multiplication closed and makes every nonzero element invertible.

use std::{
    fmt::{Debug, Display, Formatter},
    hash::{Hash, Hasher},
    marker::PhantomData,
    ops,
};

#[cfg(any(test, feature = "proptest"))]
use proptest::{
    prelude::Arbitrary,
    strategy::{BoxedStrategy, Strategy},
};
use rand::{CryptoRng, RngCore};
use serde::{
    de::{self, SeqAccess, Visitor},
    ser::{Serialize, SerializeTuple, Serializer},
    Deserialize, Deserializer,
};

use crate::{impl_add_variants, impl_div_variants, impl_mul_variants, impl_sub_variants};

use crate::{
    fields::{trim_limbs, KnownOrder},
    identities::{One, Zero},
    integers::limbs_minus_two,
    FiniteField, ParseFieldElementError, Ring,
};

/// The monic irreducible polynomial of degree N over GF(P) that defines GF(P^N).
///
/// The polynomial must genuinely be irreducible over GF(P). A reducible modulus yields a ring with
/// zero divisors, in which some nonzero elements have no multiplicative inverse and `inverse` —
/// which relies on Fermat's little theorem — returns a silently wrong value.
pub trait IrreduciblePolynomial<const P: u64, const N: usize>: 'static {
    /// Coefficients c_0, ..., c_{N-1} of `x^N + c_{N-1} x^{N-1} + ... + c_1 x + c_0`, low-order
    /// first. The leading coefficient is implicitly 1.
    const COEFFICIENTS: [u64; N];
}

/// Element of the field GF(P^N), with multiplication reduced by the irreducible polynomial M.
pub struct ExtensionFieldElement<const P: u64, const N: usize, M: IrreduciblePolynomial<P, N>> {
    /// Coefficients c_0, ..., c_{N-1} of the polynomial `sum c_i x^i`, low-order first. Every
    /// coefficient is a reduced residue mod P, which `new` establishes and the arithmetic
    /// operations preserve. `PartialEq` and `Hash` both key on this array, so that canonical form
    /// is what keeps them consistent.
    coefficients: [u64; N],
    modulus: PhantomData<M>,
}

// The trait impls below are written out rather than derived: a derive would bound the modulus
// marker type M by each trait, even though M appears only in `PhantomData`.

impl<const P: u64, const N: usize, M: IrreduciblePolynomial<P, N>> Clone
    for ExtensionFieldElement<P, N, M>
{
    fn clone(&self) -> Self {
        *self
    }
}

impl<const P: u64, const N: usize, M: IrreduciblePolynomial<P, N>> Copy
    for ExtensionFieldElement<P, N, M>
{
}

impl<const P: u64, const N: usize, M: IrreduciblePolynomial<P, N>> PartialEq
    for ExtensionFieldElement<P, N, M>
{
    fn eq(&self, other: &Self) -> bool {
        self.coefficients == other.coefficients
    }
}

impl<const P: u64, const N: usize, M: IrreduciblePolynomial<P, N>> Eq
    for ExtensionFieldElement<P, N, M>
{
}

impl<const P: u64, const N: usize, M: IrreduciblePolynomial<P, N>> Hash
    for ExtensionFieldElement<P, N, M>
{
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.coefficients.hash(state);
    }
}

impl<const P: u64, const N: usize, M: IrreduciblePolynomial<P, N>> Debug
    for ExtensionFieldElement<P, N, M>
{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.coefficients)
    }
}

impl<const P: u64, const N: usize, M: IrreduciblePolynomial<P, N>> Default
    for ExtensionFieldElement<P, N, M>
{
    fn default() -> Self {
        Self::ZERO
    }
}

impl<const P: u64, const N: usize, M: IrreduciblePolynomial<P, N>> ExtensionFieldElement<P, N, M> {
    /// An element of GF(P^N).
    ///
    /// # Arguments
    /// * `coefficients` - coefficients[i] is c_i in the polynomial `sum c_i x^i`. Each is reduced
    ///   mod P so that equal elements share one representation.
    pub fn new(coefficients: [u64; N]) -> Self {
        let mut reduced = coefficients;
        for c in reduced.iter_mut() {
            *c %= P;
        }
        Self {
            coefficients: reduced,
            modulus: PhantomData,
        }
    }

    /// The polynomial's coefficients, low-order first, each reduced mod P.
    pub fn coefficients(&self) -> &[u64; N] {
        &self.coefficients
    }

    /// `c_0, c_1, ..., c_{N-1}` — the inside of the bracketed form [`Display`] writes.
    ///
    /// Exactly N coefficients are required, so a list written for a different degree is rejected
    /// rather than zero-padded into a different field's element. Each is reduced mod P, as the
    /// inherent `new` and the prime fields' `from_str` both do.
    fn from_coefficient_list(inner: &str) -> Result<Self, ParseFieldElementError> {
        let mut coefficients = [0u64; N];
        let mut count = 0usize;
        for field in inner.split(',') {
            if count == N {
                return Err(ParseFieldElementError::OutOfRange);
            }
            coefficients[count] = parse_decimal_u128(field.trim())? as u64 % P;
            count += 1;
        }
        if count != N {
            return Err(ParseFieldElementError::OutOfRange);
        }
        Ok(Self::new(coefficients))
    }
}

/// A decimal integer, with the leading `+` the polynomial grammar may emit.
///
/// `u128` because an extension field's order is held as one; a value beyond that cannot name an
/// element of any field in this crate and so is [`ParseFieldElementError::OutOfRange`].
fn parse_decimal_u128(value: &str) -> Result<u128, ParseFieldElementError> {
    let digits = value.strip_prefix('+').unwrap_or(value);
    if digits.is_empty() {
        return Err(ParseFieldElementError::OutOfRange);
    }
    if let Some(offender) = digits.bytes().find(|b| !b.is_ascii_digit()) {
        return Err(ParseFieldElementError::InvalidCharacter(
            offender.wrapping_sub(b'0'),
        ));
    }
    digits
        .parse()
        .map_err(|_| ParseFieldElementError::OutOfRange)
}

// impl Serialize
//
// Only the coefficients are encoded: P, N, and the modulus are carried by the type, so there is
// nothing about them to transmit. Written by hand rather than derived because `M` appears in a
// `PhantomData` and a derive would demand that it implement `Serialize` too.
impl<const P: u64, const N: usize, M: IrreduciblePolynomial<P, N>> Serialize
    for ExtensionFieldElement<P, N, M>
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut tuple = serializer.serialize_tuple(N)?;
        for coefficient in &self.coefficients {
            tuple.serialize_element(coefficient)?;
        }
        tuple.end()
    }
}

/// Reads the N coefficients back into an element.
struct CoefficientsVisitor<const P: u64, const N: usize, M: IrreduciblePolynomial<P, N>> {
    modulus: PhantomData<M>,
}

impl<'de, const P: u64, const N: usize, M: IrreduciblePolynomial<P, N>> Visitor<'de>
    for CoefficientsVisitor<P, N, M>
{
    type Value = ExtensionFieldElement<P, N, M>;

    fn expecting(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} field element coefficients", N)
    }

    fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
    where
        A: SeqAccess<'de>,
    {
        let mut coefficients = [0u64; N];
        for (i, coefficient) in coefficients.iter_mut().enumerate() {
            *coefficient = seq
                .next_element()?
                .ok_or_else(|| de::Error::invalid_length(i, &self))?;
        }
        // Through `new`, so coefficients that arrive unreduced are brought back into canonical
        // form. `PartialEq` and `Hash` key on the array, so a decoded value must not be able to
        // compare unequal to the element it represents.
        Ok(ExtensionFieldElement::new(coefficients))
    }
}

// impl Deserialize
impl<'de, const P: u64, const N: usize, M: IrreduciblePolynomial<P, N>> Deserialize<'de>
    for ExtensionFieldElement<P, N, M>
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_tuple(
            N,
            CoefficientsVisitor::<P, N, M> {
                modulus: PhantomData,
            },
        )
    }
}

// impl Zero
impl<const P: u64, const N: usize, M: IrreduciblePolynomial<P, N>> Zero
    for ExtensionFieldElement<P, N, M>
{
    const ZERO: Self = ExtensionFieldElement {
        coefficients: [0u64; N],
        modulus: PhantomData,
    };
}

// impl One
impl<const P: u64, const N: usize, M: IrreduciblePolynomial<P, N>> One
    for ExtensionFieldElement<P, N, M>
{
    const ONE: Self = {
        // The constant polynomial 1.
        let mut coefficients = [0u64; N];
        coefficients[0] = 1;
        ExtensionFieldElement {
            coefficients,
            modulus: PhantomData,
        }
    };
}

// impl Ring
impl<const P: u64, const N: usize, M: IrreduciblePolynomial<P, N>> Ring
    for ExtensionFieldElement<P, N, M>
{
}

// impl FiniteField
impl<const P: u64, const N: usize, M: IrreduciblePolynomial<P, N>> FiniteField
    for ExtensionFieldElement<P, N, M>
{
    /// The constant polynomial `val mod P`: the prime subfield, which is all the integers reach.
    ///
    /// Not the inherent [`ExtensionFieldElement::new`], which takes the whole coefficient array.
    /// See [`FiniteField::new`], and [`KnownOrder::element_at`] to address elements by index.
    fn new(val: u64) -> Self {
        // The constant polynomial `val`.
        let mut coefficients = [0u64; N];
        coefficients[0] = val % P;
        Self {
            coefficients,
            modulus: PhantomData,
        }
    }

    /// Either `[c_0, c_1, ..., c_{N-1}]` — what [`Display`] writes — or a bare decimal read as the
    /// base-`P` digits of that same list.
    ///
    /// So `from_str("5")` over GF(13^4) is `[5, 0, 0, 0]` and `from_str("170")` is `[1, 0, 1, 0]`,
    /// rather than `170 mod 13`. See [`FiniteField::from_str`] for why a representation and not
    /// the integer embedding.
    fn from_str(value: &str) -> Result<Self, ParseFieldElementError> {
        let trimmed = value.trim();
        match trimmed.strip_prefix('[') {
            Some(inner) => {
                let inner = inner
                    .strip_suffix(']')
                    .ok_or(ParseFieldElementError::OutOfRange)?;
                Self::from_coefficient_list(inner)
            }
            // A bare decimal: the element's index, as base-P digits. Agrees with `new` on `0..P`.
            None => {
                let index = parse_decimal_u128(trimmed)?;
                <Self as KnownOrder>::element_at(index).ok_or(ParseFieldElementError::OutOfRange)
            }
        }
    }

    fn random<R: RngCore + CryptoRng>(rng: &mut R) -> Self {
        let mut coefficients = [0u64; N];
        for c in coefficients.iter_mut() {
            *c = rng.next_u64() % P;
        }
        Self {
            coefficients,
            modulus: PhantomData,
        }
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

impl<const P: u64, const N: usize, M: IrreduciblePolynomial<P, N>> ExtensionFieldElement<P, N, M> {
    /// q = p^N.
    ///
    /// A `u128` still, as `order` was: an extension whose order exceeds that is a compile error
    /// here rather than the silent overflow it used to be at run time. Widening this is not what
    /// the wide prime fields need, so it is left until an extension field asks for it.
    const ORDER: u128 = (P as u128).pow(N as u32);

    /// See [`KnownOrder::order_limbs`].
    const ORDER_LIMBS: [u64; 2] = [Self::ORDER as u64, (Self::ORDER >> 64) as u64];

    /// See [`KnownOrder::characteristic_limbs`].
    const CHARACTERISTIC_LIMBS: [u64; 1] = [P];

    /// The Fermat inversion exponent q - 2, as little-endian limbs.
    ///
    /// Subtracted on the limbs rather than on a machine integer, and held at the width of
    /// [`Self::ORDER_LIMBS`], so nothing here caps the order at the width of a `u128`.
    const FERMAT_EXPONENT_LIMBS: [u64; 2] = limbs_minus_two(Self::ORDER_LIMBS);
}

impl<const P: u64, const N: usize, M: IrreduciblePolynomial<P, N>> KnownOrder
    for ExtensionFieldElement<P, N, M>
{
    fn order_limbs() -> &'static [u64] {
        trim_limbs(&Self::ORDER_LIMBS)
    }

    fn characteristic_limbs() -> &'static [u64] {
        // q = p^N with N > 1, so the characteristic is genuinely not the order.
        trim_limbs(&Self::CHARACTERISTIC_LIMBS)
    }

    /// The base-P digits of `index` as coefficients, so `0..P^N` covers the field exactly once.
    ///
    /// Overrides the default, which refuses an extension rather than enumerate its prime subfield.
    fn element_at(index: u128) -> Option<Self> {
        if index >= Self::ORDER {
            return None;
        }
        let mut coefficients = [0u64; N];
        let mut remaining = index;
        for c in coefficients.iter_mut() {
            *c = (remaining % P as u128) as u64;
            remaining /= P as u128;
        }
        Some(Self::new(coefficients))
    }
}

// impl Display
impl<const P: u64, const N: usize, M: IrreduciblePolynomial<P, N>> Display
    for ExtensionFieldElement<P, N, M>
{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.coefficients)
    }
}

// Borrowed + Borrowed
impl<const P: u64, const N: usize, M: IrreduciblePolynomial<P, N>>
    ops::Add<&ExtensionFieldElement<P, N, M>> for &ExtensionFieldElement<P, N, M>
{
    type Output = ExtensionFieldElement<P, N, M>;

    fn add(self, rhs: &ExtensionFieldElement<P, N, M>) -> Self::Output {
        let mut coefficients = [0u64; N];
        for i in 0..N {
            let sum = self.coefficients[i] as u128 + rhs.coefficients[i] as u128;
            coefficients[i] = (sum % P as u128) as u64;
        }
        ExtensionFieldElement::new(coefficients)
    }
}

impl_add_variants!([const P: u64, const N: usize, M: IrreduciblePolynomial<P, N>], ExtensionFieldElement<P, N, M>);

// Borrowed - Borrowed
impl<const P: u64, const N: usize, M: IrreduciblePolynomial<P, N>>
    ops::Sub<&ExtensionFieldElement<P, N, M>> for &ExtensionFieldElement<P, N, M>
{
    type Output = ExtensionFieldElement<P, N, M>;

    fn sub(self, rhs: &ExtensionFieldElement<P, N, M>) -> Self::Output {
        let mut coefficients = [0u64; N];
        for i in 0..N {
            let difference = self.coefficients[i] as i128 - rhs.coefficients[i] as i128;
            coefficients[i] = difference.rem_euclid(P as i128) as u64;
        }
        ExtensionFieldElement::new(coefficients)
    }
}

impl_sub_variants!([const P: u64, const N: usize, M: IrreduciblePolynomial<P, N>], ExtensionFieldElement<P, N, M>);

impl<const P: u64, const N: usize, M: IrreduciblePolynomial<P, N>> ops::Neg
    for ExtensionFieldElement<P, N, M>
{
    type Output = ExtensionFieldElement<P, N, M>;

    fn neg(self) -> Self::Output {
        ExtensionFieldElement::zero() - self
    }
}

impl<const P: u64, const N: usize, M: IrreduciblePolynomial<P, N>> ops::Neg
    for &ExtensionFieldElement<P, N, M>
{
    type Output = ExtensionFieldElement<P, N, M>;

    fn neg(self) -> Self::Output {
        ExtensionFieldElement::zero() - self
    }
}

// Borrowed * Borrowed
impl<const P: u64, const N: usize, M: IrreduciblePolynomial<P, N>> ops::Mul<Self>
    for &ExtensionFieldElement<P, N, M>
{
    type Output = ExtensionFieldElement<P, N, M>;

    fn mul(self, rhs: Self) -> Self::Output {
        let p = P as u128;
        let modulus = M::COEFFICIENTS;

        // The schoolbook product of two polynomials of degree < N has degree at most 2N - 2, so it
        // needs 2N - 1 accumulators. They are held as two arrays of N rather than one of 2N - 1
        // because `[u128; 2 * N - 1]` needs const-expression arithmetic while `[u128; N]` does
        // not. Degree `d` lives in `low[d]` for `d < N` and in `high[d - N]` above it; `high`'s
        // last slot is unused, which is cheaper than a heap allocation per multiplication.
        let mut low = [0u128; N];
        let mut high = [0u128; N];

        if delayed_reduction_fits::<P, N>() {
            // Every partial product is accumulated and each slot reduced once, rather than
            // reducing after every multiply-add. `delayed_reduction_fits` is what licenses it: a
            // slot takes at most N products of two residues, so the sum is below N(P-1)^2, and
            // that bound is checked against `u128::MAX` at compile time.
            for i in 0..N {
                let a = self.coefficients[i] as u128;
                if a == 0 {
                    continue;
                }
                // Split rather than test `i + j < N` inside the loop: for `j` below `N - i` the
                // product's degree is below N, and at or above it the degree is not.
                let split = N - i;
                for j in 0..split {
                    low[i + j] += a * rhs.coefficients[j] as u128;
                }
                for j in split..N {
                    high[i + j - N] += a * rhs.coefficients[j] as u128;
                }
            }
            for slot in low.iter_mut().chain(high.iter_mut()) {
                *slot %= p;
            }
        } else {
            // P is large enough that two residues multiplied and accumulated could overflow a
            // u128. Reduce after every multiply-add, which is what this did before delayed
            // reduction existed. No modulus in this crate reaches here; see
            // `delayed_reduction_fits`.
            for i in 0..N {
                let a = self.coefficients[i] as u128;
                if a == 0 {
                    continue;
                }
                let split = N - i;
                for j in 0..split {
                    low[i + j] = (low[i + j] + a * rhs.coefficients[j] as u128) % p;
                }
                for j in split..N {
                    high[i + j - N] = (high[i + j - N] + a * rhs.coefficients[j] as u128) % p;
                }
            }
        }

        // Reduce to degree < N. The modulus gives x^N = -(c_{N-1} x^{N-1} + ... + c_0), so each
        // term of degree i >= N folds down into the N coefficients below it. Working downwards
        // means a folded term has itself been folded into before it is read.
        //
        // `leading` is reduced once here rather than the product being reduced once per term: it
        // has to be below P before multiplying by a modulus coefficient, or that product could
        // overflow. The targets are then accumulated without reduction, each taking at most N
        // addends below P, so they stay below N*P and are reduced on the way out.
        for i in (N..(2 * N).saturating_sub(1)).rev() {
            let leading = high[i - N] % p;
            high[i - N] = 0;
            if leading == 0 {
                continue;
            }
            // As above: the fold target `i - N + j` crosses N at `j = 2N - i`. The index into
            // `high` is written `i + j - 2N` and not `i - 2N + j`: the value is non-negative
            // because `j >= 2N - i` in this loop, but `i - 2N` alone underflows a `usize`.
            let split = 2 * N - i;
            for j in 0..split {
                low[i - N + j] += p - (leading * modulus[j] as u128) % p;
            }
            for j in split..N {
                high[i + j - 2 * N] += p - (leading * modulus[j] as u128) % p;
            }
        }

        let mut coefficients = [0u64; N];
        for (coefficient, accumulated) in coefficients.iter_mut().zip(low.iter()) {
            *coefficient = (*accumulated % p) as u64;
        }
        ExtensionFieldElement::new(coefficients)
    }
}

/// Whether a slot can accumulate N products of two residues modulo P without overflowing a u128.
///
/// A residue is below P, so a product is at most `(P-1)^2`, and a coefficient of the schoolbook
/// product takes at most N of them. `(P-1)^2` always fits — `P` is a `u64` — so only the final
/// multiplication by N can overflow, which is the one checked.
///
/// Every modulus this crate declares is far inside the bound: the largest is P = 251 at N = 4.
/// The predicate exists because the type is generic over `const P: u64`, so a caller may define an
/// irreducible polynomial over a prime near 2^64, where two residues multiplied already fill a
/// u128 and nothing may be accumulated on top.
const fn delayed_reduction_fits<const P: u64, const N: usize>() -> bool {
    let max_product = (P as u128 - 1) * (P as u128 - 1);
    max_product.checked_mul(N as u128).is_some()
}

impl_mul_variants!([const P: u64, const N: usize, M: IrreduciblePolynomial<P, N>], ExtensionFieldElement<P, N, M>);

// Borrowed / Borrowed
impl<const P: u64, const N: usize, M: IrreduciblePolynomial<P, N>> ops::Div<Self>
    for &ExtensionFieldElement<P, N, M>
{
    type Output = ExtensionFieldElement<P, N, M>;

    fn div(self, rhs: Self) -> Self::Output {
        // Division is multiplication by the inverse.
        self * &rhs.inverse()
    }
}

impl_div_variants!([const P: u64, const N: usize, M: IrreduciblePolynomial<P, N>], ExtensionFieldElement<P, N, M>);

#[cfg(any(test, feature = "proptest"))]
impl<const P: u64, const N: usize, M: IrreduciblePolynomial<P, N>> Arbitrary
    for ExtensionFieldElement<P, N, M>
{
    type Parameters = ();

    fn arbitrary_with(_args: Self::Parameters) -> Self::Strategy {
        // Each of the N coefficients is independently drawn from GF(p).
        proptest::collection::vec(0u64..P, N)
            .prop_map(|drawn| {
                let mut coefficients = [0u64; N];
                coefficients.copy_from_slice(&drawn);
                Self::new(coefficients)
            })
            .boxed()
    }

    type Strategy = BoxedStrategy<Self>;
}

#[cfg(test)]
mod tests {
    use proptest::{arbitrary::Arbitrary, prop_assert_eq, proptest};
    use rand::{prelude::StdRng, thread_rng, SeedableRng};

    use crate::{
        fields::{
            binary_field::BinaryFieldElement,
            extension_field::{ExtensionFieldElement, IrreduciblePolynomial},
            finite_field::fermat_inverse_via_recursive_pow,
            irreducible_polynomials::{
                Modulus13Pow4, Modulus251Pow4, Modulus2Pow8, Modulus3Pow2, Modulus5Pow3,
                X8_X4_X3_X_1,
            },
        },
        identities::{One, Zero},
        FiniteField, KnownOrder,
    };

    use super::delayed_reduction_fits;
    use crate::ParseFieldElementError;

    /// The bracketed coefficient list `Display` writes is read straight back.
    #[test]
    fn test_from_str_reads_the_bracketed_coefficient_list() {
        type F = ExtensionFieldElement<13, 4, Modulus13Pow4>;
        let a = F::new([1, 0, 2, 12]);
        assert_eq!(a.to_string(), "[1, 0, 2, 12]");
        assert_eq!(<F as FiniteField>::from_str("[1, 0, 2, 12]"), Ok(a));
        // Whitespace is not significant.
        assert_eq!(<F as FiniteField>::from_str("[1,0,2,12]"), Ok(a));
    }

    /// A bare decimal is the element's index in base P, not the integer reduced mod P.
    #[test]
    fn test_from_str_reads_a_bare_decimal_as_the_base_p_index() {
        type F = ExtensionFieldElement<13, 4, Modulus13Pow4>;
        // 170 = 1 + 13^2, so the digits are [1, 0, 1, 0] — not 170 mod 13 = 1.
        assert_eq!(
            <F as FiniteField>::from_str("170"),
            Ok(F::new([1, 0, 1, 0]))
        );
        assert_ne!(
            <F as FiniteField>::from_str("170"),
            Ok(<F as FiniteField>::new(170))
        );
        // Below P the index and the embedding agree, so small constants read as expected.
        for value in 0..13u64 {
            assert_eq!(
                <F as FiniteField>::from_str(&value.to_string()),
                Ok(<F as FiniteField>::new(value))
            );
        }
    }

    /// An index at or above q, and a coefficient list of the wrong degree, are out of range.
    #[test]
    fn test_from_str_rejects_input_outside_the_field() {
        type F = ExtensionFieldElement<13, 4, Modulus13Pow4>;
        // 13^4 = 28561.
        assert_eq!(
            <F as FiniteField>::from_str("28561"),
            Err(ParseFieldElementError::OutOfRange)
        );
        for malformed in ["[1, 0, 2]", "[1, 0, 2, 12, 5]", "[]", "[1, 0, 2, 12", "[+]"] {
            assert_eq!(
                <F as FiniteField>::from_str(malformed),
                Err(ParseFieldElementError::OutOfRange),
                "{malformed} should be rejected"
            );
        }
    }

    /// Malformed text is a `Result`, never a panic.
    #[test]
    fn test_from_str_rejects_malformed_text() {
        type F = ExtensionFieldElement<13, 4, Modulus13Pow4>;
        assert_eq!(
            <F as FiniteField>::from_str(""),
            Err(ParseFieldElementError::OutOfRange)
        );
        assert_eq!(
            <F as FiniteField>::from_str("[a, 0, 0, 0]"),
            Err(ParseFieldElementError::InvalidCharacter(b'a' - b'0'))
        );
        assert_eq!(
            <F as FiniteField>::from_str("nonsense"),
            Err(ParseFieldElementError::InvalidCharacter(b'n' - b'0'))
        );
    }

    /// `element_at` walks all P^N coefficient vectors and stops there.
    #[test]
    fn test_element_at_is_the_base_p_digit_expansion() {
        type F = ExtensionFieldElement<3, 2, Modulus3Pow2>;
        let mut seen = Vec::new();
        for index in 0..9u128 {
            seen.push(*F::element_at(index).expect("below q").coefficients());
        }
        assert_eq!(
            seen,
            vec![
                [0, 0],
                [1, 0],
                [2, 0],
                [0, 1],
                [1, 1],
                [2, 1],
                [0, 2],
                [1, 2],
                [2, 2]
            ]
        );
        assert_eq!(F::element_at(9), None);
    }

    /// x^2 + 1 over GF(2^31 - 1), for the large-coefficient multiplication tests.
    ///
    /// Not in `irreducible_polynomials`, which certifies its moduli by trial division — that
    /// enumerates `p^d` candidates and is hopeless at this size. For this particular shape the
    /// criterion is exact and cheap instead: `x^2 + 1` is irreducible over GF(p) exactly when -1
    /// is a quadratic non-residue, which for odd p happens exactly when p = 3 (mod 4).
    /// `test_the_mersenne_modulus_is_irreducible` asserts that congruence.
    struct ModulusMersenne31Pow2;

    const MERSENNE_31: u64 = 2147483647;

    impl IrreduciblePolynomial<MERSENNE_31, 2> for ModulusMersenne31Pow2 {
        const COEFFICIENTS: [u64; 2] = [1, 0];
    }

    type FM31x2 = ExtensionFieldElement<MERSENNE_31, 2, ModulusMersenne31Pow2>;

    /// The large test modulus really is irreducible, by the p = 3 (mod 4) criterion.
    #[test]
    fn test_the_mersenne_modulus_is_irreducible() {
        assert_eq!(
            MERSENNE_31 % 4,
            3,
            "x^2 + 1 is reducible over GF(p) unless p = 3 (mod 4)"
        );
        assert_eq!(ModulusMersenne31Pow2::COEFFICIENTS, [1, 0], "not x^2 + 1");
    }

    /// The delayed-reduction bound admits every declared modulus and rejects what would overflow.
    ///
    /// The fast path accumulates N products of two residues in a u128 before reducing. This is the
    /// predicate that decides whether that is safe, so it is tested directly rather than only
    /// through its effect — a wrong answer in the permissive direction is a silent wrong result,
    /// not a panic, once overflow checks are off in release.
    #[test]
    fn test_the_delayed_reduction_bound_is_exact() {
        // Every modulus this crate declares, and the large test one.
        assert!(delayed_reduction_fits::<3, 2>());
        assert!(delayed_reduction_fits::<5, 3>());
        assert!(delayed_reduction_fits::<13, 4>());
        assert!(delayed_reduction_fits::<251, 4>());
        assert!(delayed_reduction_fits::<2, 8>());
        assert!(delayed_reduction_fits::<MERSENNE_31, 2>());

        // A prime near 2^64 fills a u128 with one product, so nothing may be accumulated on top.
        const BIG: u64 = 18446744073709551557;
        assert!(!delayed_reduction_fits::<BIG, 2>());
        assert!(!delayed_reduction_fits::<BIG, 4>());

        // The boundary, at a P whose crossing point is a representable N. With P - 1 = 2^48 a
        // single product is 2^96, so N can reach 2^32 - 1 before (P-1)^2 * N passes u128::MAX.
        // (P - 1 = 2^32 would put the boundary at N = 2^64, which a usize cannot hold.)
        const P_48: u64 = (1u64 << 48) + 1;
        assert!(delayed_reduction_fits::<P_48, { (1usize << 32) - 1 }>());
        assert!(!delayed_reduction_fits::<P_48, { 1usize << 32 }>());
    }

    /// Multiplication over a 31-bit prime agrees with a reference that reduces at every step.
    ///
    /// This is the test the delayed reduction has to pass. The oracle is the algorithm this
    /// replaced: reduce after every multiply-add and after every fold term, which cannot overflow
    /// and is therefore correct by construction but slow. Coefficients are driven to P-1, where a
    /// single product is about 2^62 and two accumulated exceed any 64-bit accumulator — so a
    /// reduction that was delayed too far shows up here rather than on the small moduli, whose
    /// products fit in a handful of bits.
    #[test]
    fn test_multiplication_over_a_large_prime_matches_a_step_reducing_reference() {
        /// The pre-delay algorithm, kept here as the oracle.
        fn reference(a: [u64; 2], b: [u64; 2], p: u64, modulus: [u64; 2]) -> [u64; 2] {
            let p = p as u128;
            let mut product = [0u128; 3];
            for (i, &ai) in a.iter().enumerate() {
                for (j, &bj) in b.iter().enumerate() {
                    product[i + j] = (product[i + j] + ai as u128 * bj as u128) % p;
                }
            }
            for i in (2..product.len()).rev() {
                let leading = product[i];
                product[i] = 0;
                if leading == 0 {
                    continue;
                }
                for j in 0..2 {
                    let term = (leading * modulus[j] as u128) % p;
                    product[i - 2 + j] = (product[i - 2 + j] + p - term) % p;
                }
            }
            [product[0] as u64, product[1] as u64]
        }

        let m = MERSENNE_31;
        let cases: [[u64; 2]; 7] = [
            [0, 0],
            [1, 0],
            [0, 1],
            [m - 1, m - 1],
            [m - 1, 1],
            [1, m - 1],
            [m / 2, m - 2],
        ];

        for a in cases {
            for b in cases {
                let expected = reference(a, b, m, ModulusMersenne31Pow2::COEFFICIENTS);
                let product = FM31x2::new(a) * FM31x2::new(b);
                assert_eq!(
                    *product.coefficients(),
                    expected,
                    "({:?}) * ({:?}) over GF({}^2)",
                    a,
                    b,
                    m
                );
            }
        }
    }

    /// The field laws hold over the large prime, which is what a wrong fold would break.
    ///
    /// Agreeing with a reference on a fixed list does not prove the reduction is a ring
    /// homomorphism; associativity and distributivity over random elements do, and they are
    /// sensitive to the fold writing to the wrong coefficient.
    #[test]
    fn test_the_large_field_obeys_the_field_laws() {
        let mut rng = StdRng::seed_from_u64(0xA11CE);
        for _ in 0..512 {
            let a = FM31x2::random(&mut rng);
            let b = FM31x2::random(&mut rng);
            let c = FM31x2::random(&mut rng);

            assert_eq!(a * b, b * a, "multiplication is not commutative");
            assert_eq!(
                (a * b) * c,
                a * (b * c),
                "multiplication is not associative"
            );
            assert_eq!(
                a * (b + c),
                a * b + a * c,
                "multiplication does not distribute"
            );
            assert_eq!(a * FM31x2::one(), a, "one is not the identity");
            assert_eq!(
                a * FM31x2::zero(),
                FM31x2::zero(),
                "zero does not annihilate"
            );
            if !a.is_zero() {
                assert_eq!(a * a.inverse(), FM31x2::one(), "inverse is wrong");
            }
        }
    }

    type F3x2 = ExtensionFieldElement<3, 2, Modulus3Pow2>;
    type F13x4 = ExtensionFieldElement<13, 4, Modulus13Pow4>;
    type F251x4 = ExtensionFieldElement<251, 4, Modulus251Pow4>;
    type F5x3 = ExtensionFieldElement<5, 3, Modulus5Pow3>;
    type F2x8 = ExtensionFieldElement<2, 8, Modulus2Pow8>;

    #[test]
    // random should not panic.
    fn test_random() {
        let mut rng = thread_rng();
        for _i in 0..1000 {
            let _element = F251x4::random(&mut rng);
        }
    }

    #[test]
    // ZERO is the additive identity.
    fn test_add_zero() {
        type F = F251x4;
        let mut rng = thread_rng();
        let element = F::random(&mut rng);
        let sum = element + F::zero();
        assert_eq!(element, sum);
    }

    #[test]
    fn test_add() {
        type Field = F13x4;
        let a = Field::new([1, 2, 3, 4]);
        let b = Field::new([11, 11, 11, 11]);
        let sum = a + b;
        assert_eq!(sum, Field::new([12, 0, 1, 2]));
    }

    #[test]
    fn test_sub() {
        type F = F13x4;
        let a = F::new([1, 2, 3, 4]);
        let b = F::new([11, 11, 11, 11]);
        let diff = a - b;
        assert_eq!(diff, F::new([3, 4, 5, 6]));
    }

    #[test]
    // ONE is the multiplicative identity.
    fn test_mul_one() {
        type F = F251x4;
        let mut rng = thread_rng();
        let element = F::random(&mut rng);
        let prod = element * F::one();
        assert_eq!(element, prod);
    }

    #[test]
    fn test_mul() {
        // (1 + 2X + 3X^2 + 4X^3)(11 + 11X + 11X^2 + 11X^3) mod X^4 + X^3 + 1 over GF(13).
        type F = F13x4;
        let a = F::new([1, 2, 3, 4]);
        let b = F::new([11, 11, 11, 11]);
        let prod = a * b;
        assert_eq!(prod, F::new([10, 0, 9, 5]));
    }

    /// Multiplication is polynomial multiplication: X * X is X^2, not a componentwise product.
    #[test]
    fn test_multiplication_is_polynomial_multiplication() {
        let x = F13x4::new([0, 1, 0, 0]); // X
        assert_eq!(x * x, F13x4::new([0, 0, 1, 0])); // X^2
    }

    /// ONE is the constant polynomial 1, not an all-ones coefficient vector.
    #[test]
    fn test_one_is_the_constant_polynomial_one() {
        assert_eq!(F13x4::one(), F13x4::new([1, 0, 0, 0]));
    }

    /// Every nonzero element is invertible, including those with a zero coefficient.
    #[test]
    fn test_inverse_of_element_with_a_zero_coefficient() {
        let a = F13x4::new([1, 0, 1, 1]);
        assert_eq!(a * a.inverse(), F13x4::one());
    }

    /// Reduction by X^N wraps a product back into degree less than N.
    #[test]
    fn test_multiplication_reduces_by_the_modulus() {
        // In GF(13^4) modulo X^4 + X^3 + 1, X^3 * X = X^4 = -(X^3 + 1) = 12*X^3 + 12.
        let x = F13x4::new([0, 1, 0, 0]);
        let x_cubed = F13x4::new([0, 0, 0, 1]);
        assert_eq!(x_cubed * x, F13x4::new([12, 0, 0, 12]));
    }

    #[test]
    // a * a_inv = 1
    fn test_inverse() {
        type F = F13x4;
        let a = F::new([1, 2, 3, 4]);
        assert_eq!(a * a.inverse(), F::one());
    }

    #[test]
    #[should_panic(expected = "does not have a multiplicative inverse")]
    // Zero does not have a multiplicative inverse.
    fn test_inverse_of_zero() {
        type F = F251x4;
        let mut rng = thread_rng();
        let element = F::random(&mut rng);
        let _result = element / F::zero();
    }

    /// `inverse` on zero panics with the stated message, rather than through division.
    #[test]
    #[should_panic(expected = "does not have a multiplicative inverse")]
    fn test_inverse_of_zero_panics_directly() {
        let _inverse = F13x4::zero().inverse();
    }

    /// Every element of a field of order p^N, by reading an index off in base p.
    fn enumerate<const P: u64, const N: usize, M: IrreduciblePolynomial<P, N>>(
    ) -> Vec<ExtensionFieldElement<P, N, M>> {
        let order = P.pow(N as u32);
        (0..order)
            .map(|index| {
                let mut coefficients = [0u64; N];
                let mut rest = index;
                for c in coefficients.iter_mut() {
                    *c = rest % P;
                    rest /= P;
                }
                ExtensionFieldElement::new(coefficients)
            })
            .collect()
    }

    /// Every nonzero element of three small extensions inverts to exactly what the recursive-pow
    /// reference gives, over the coefficient representation and not merely up to the field axioms.
    #[test]
    fn test_inverse_is_bit_identical_to_the_reference_exhaustively() {
        fn check<const P: u64, const N: usize, M: IrreduciblePolynomial<P, N>>() {
            for a in enumerate::<P, N, M>() {
                if a.is_zero() {
                    continue;
                }
                assert_eq!(
                    a.inverse(),
                    fermat_inverse_via_recursive_pow(&a),
                    "GF({P}^{N}): {a}"
                );
            }
        }

        check::<3, 2, Modulus3Pow2>();
        check::<5, 3, Modulus5Pow3>();
        check::<2, 8, Modulus2Pow8>();
    }

    proptest! {
        /// Inversion is bit-identical to the recursive-pow reference over the two extensions
        /// wider than the `Gf13Pow4` that `for_each_field!` covers; GF((2^31-1)^2) is the one
        /// whose order needs two limbs.
        #[test]
        fn test_inverse_is_bit_identical_to_the_reference(
            a in F251x4::arbitrary(),
            b in FM31x2::arbitrary(),
        ) {
            if !a.is_zero() {
                prop_assert_eq!(a.inverse(), fermat_inverse_via_recursive_pow(&a));
            }
            if !b.is_zero() {
                prop_assert_eq!(b.inverse(), fermat_inverse_via_recursive_pow(&b));
            }
        }
    }

    #[test]
    fn test_divide_by_one() {
        type F = F251x4;
        let mut rng = thread_rng();
        let element = F::random(&mut rng);
        let result = element / F::one();
        assert_eq!(element, result);
    }

    #[test]
    fn test_divide() {
        // b^-1 = 9 + 8X + 4X^2 + 8X^3 mod X^4 + X^3 + 1 over GF(13), so a/b = a * b^-1.
        type F = F13x4;
        let a = F::new([1, 2, 3, 4]);
        let b = F::new([11, 11, 11, 11]);
        let result = a / b;
        assert_eq!(result, F::new([9, 5, 2, 11]));
    }

    // The field axioms, checked over arbitrary elements of GF(5^3), GF(13^4), and GF(251^4).

    fn addition_is_commutative<F: FiniteField>(a: F, b: F) {
        assert_eq!(a + b, b + a);
    }

    fn addition_is_associative<F: FiniteField>(a: F, b: F, c: F) {
        assert_eq!((a + b) + c, a + (b + c));
    }

    fn zero_is_the_additive_identity<F: FiniteField>(a: F) {
        assert_eq!(a + F::zero(), a);
    }

    // `a - a` is the point of the test, not a mistake.
    #[allow(clippy::eq_op)]
    fn subtracting_an_element_from_itself_gives_zero<F: FiniteField>(a: F) {
        assert_eq!(a - a, F::zero());
    }

    fn multiplication_is_commutative<F: FiniteField>(a: F, b: F) {
        assert_eq!(a * b, b * a);
    }

    fn multiplication_is_associative<F: FiniteField>(a: F, b: F, c: F) {
        assert_eq!((a * b) * c, a * (b * c));
    }

    fn one_is_the_multiplicative_identity<F: FiniteField>(a: F) {
        assert_eq!(a * F::one(), a);
    }

    fn multiplication_distributes_over_addition<F: FiniteField>(a: F, b: F, c: F) {
        assert_eq!(a * (b + c), (a * b) + (a * c));
    }

    fn element_times_its_inverse_is_one<F: FiniteField>(a: F) {
        if a.is_zero() {
            return; // Zero has no multiplicative inverse.
        }
        assert_eq!(a * a.inverse(), F::one());
    }

    fn division_undoes_multiplication<F: FiniteField>(a: F, b: F) {
        if b.is_zero() {
            return; // Division by zero is undefined.
        }
        assert_eq!((a * b) / b, a);
    }

    fn frobenius_fixes_every_element<F: KnownOrder>(a: F) {
        // a^(p^n) = a for every a in GF(p^n).
        assert_eq!(a.pow(F::order_u128().unwrap()), a);
    }

    fn coefficients_stay_reduced<const P: u64, const N: usize, M: IrreduciblePolynomial<P, N>>(
        a: ExtensionFieldElement<P, N, M>,
        b: ExtensionFieldElement<P, N, M>,
    ) {
        // Every coefficient of a sum or product must be a reduced residue mod p.
        for c in (a + b)
            .coefficients
            .iter()
            .chain((a * b).coefficients.iter())
        {
            assert!(*c < P);
        }
    }

    proptest! {
        #[test]
        fn test_addition_is_commutative_13x4(a in F13x4::arbitrary(), b in F13x4::arbitrary()) {
            addition_is_commutative(a, b);
        }

        #[test]
        fn test_addition_is_commutative_61x8(a in F251x4::arbitrary(), b in F251x4::arbitrary()) {
            addition_is_commutative(a, b);
        }

        #[test]
        fn test_addition_is_associative_13x4(a in F13x4::arbitrary(), b in F13x4::arbitrary(), c in F13x4::arbitrary()) {
            addition_is_associative(a, b, c);
        }

        #[test]
        fn test_addition_is_associative_61x8(a in F251x4::arbitrary(), b in F251x4::arbitrary(), c in F251x4::arbitrary()) {
            addition_is_associative(a, b, c);
        }

        #[test]
        fn test_zero_is_the_additive_identity_13x4(a in F13x4::arbitrary()) {
            zero_is_the_additive_identity(a);
        }

        #[test]
        fn test_zero_is_the_additive_identity_61x8(a in F251x4::arbitrary()) {
            zero_is_the_additive_identity(a);
        }

        #[test]
        fn test_subtracting_an_element_from_itself_gives_zero_13x4(a in F13x4::arbitrary()) {
            subtracting_an_element_from_itself_gives_zero(a);
        }

        #[test]
        fn test_subtracting_an_element_from_itself_gives_zero_61x8(a in F251x4::arbitrary()) {
            subtracting_an_element_from_itself_gives_zero(a);
        }

        #[test]
        fn test_multiplication_is_commutative_13x4(a in F13x4::arbitrary(), b in F13x4::arbitrary()) {
            multiplication_is_commutative(a, b);
        }

        #[test]
        fn test_multiplication_is_commutative_61x8(a in F251x4::arbitrary(), b in F251x4::arbitrary()) {
            multiplication_is_commutative(a, b);
        }

        #[test]
        fn test_multiplication_is_associative_13x4(a in F13x4::arbitrary(), b in F13x4::arbitrary(), c in F13x4::arbitrary()) {
            multiplication_is_associative(a, b, c);
        }

        #[test]
        fn test_multiplication_is_associative_61x8(a in F251x4::arbitrary(), b in F251x4::arbitrary(), c in F251x4::arbitrary()) {
            multiplication_is_associative(a, b, c);
        }

        #[test]
        fn test_one_is_the_multiplicative_identity_13x4(a in F13x4::arbitrary()) {
            one_is_the_multiplicative_identity(a);
        }

        #[test]
        fn test_one_is_the_multiplicative_identity_61x8(a in F251x4::arbitrary()) {
            one_is_the_multiplicative_identity(a);
        }

        #[test]
        fn test_multiplication_distributes_over_addition_13x4(a in F13x4::arbitrary(), b in F13x4::arbitrary(), c in F13x4::arbitrary()) {
            multiplication_distributes_over_addition(a, b, c);
        }

        #[test]
        fn test_multiplication_distributes_over_addition_61x8(a in F251x4::arbitrary(), b in F251x4::arbitrary(), c in F251x4::arbitrary()) {
            multiplication_distributes_over_addition(a, b, c);
        }

        #[test]
        fn test_coefficients_stay_reduced_13x4(a in F13x4::arbitrary(), b in F13x4::arbitrary()) {
            coefficients_stay_reduced(a, b);
        }

        #[test]
        fn test_coefficients_stay_reduced_61x8(a in F251x4::arbitrary(), b in F251x4::arbitrary()) {
            coefficients_stay_reduced(a, b);
        }

        #[test]
        fn test_element_times_its_inverse_is_one_5x3(a in F5x3::arbitrary()) {
            element_times_its_inverse_is_one(a);
        }

        #[test]
        fn test_element_times_its_inverse_is_one_13x4(a in F13x4::arbitrary()) {
            element_times_its_inverse_is_one(a);
        }

        #[test]
        fn test_element_times_its_inverse_is_one_251x4(a in F251x4::arbitrary()) {
            element_times_its_inverse_is_one(a);
        }

        #[test]
        fn test_division_undoes_multiplication_13x4(a in F13x4::arbitrary(), b in F13x4::arbitrary()) {
            division_undoes_multiplication(a, b);
        }

        #[test]
        fn test_division_undoes_multiplication_251x4(a in F251x4::arbitrary(), b in F251x4::arbitrary()) {
            division_undoes_multiplication(a, b);
        }

        #[test]
        fn test_frobenius_fixes_every_element_5x3(a in F5x3::arbitrary()) {
            frobenius_fixes_every_element(a);
        }

        #[test]
        fn test_frobenius_fixes_every_element_13x4(a in F13x4::arbitrary()) {
            frobenius_fixes_every_element(a);
        }

        #[test]
        fn test_multiplication_is_associative_5x3(a in F5x3::arbitrary(), b in F5x3::arbitrary(), c in F5x3::arbitrary()) {
            multiplication_is_associative(a, b, c);
        }

        #[test]
        fn test_multiplication_distributes_over_addition_5x3(a in F5x3::arbitrary(), b in F5x3::arbitrary(), c in F5x3::arbitrary()) {
            multiplication_distributes_over_addition(a, b, c);
        }

        /// GF(2^8) built as an extension field agrees with the independent bit-pattern
        /// implementation in `binary_field`, given the same irreducible polynomial.
        #[test]
        fn test_gf256_agrees_with_binary_field(a in 0u64..256, b in 0u64..256) {
            let extension = |bits: u64| {
                let mut coefficients = [0u64; 8];
                for (i, c) in coefficients.iter_mut().enumerate() {
                    *c = (bits >> i) & 1;
                }
                F2x8::new(coefficients)
            };
            let bits = |element: F2x8| {
                element
                    .coefficients
                    .iter()
                    .enumerate()
                    .fold(0u64, |acc, (i, c)| acc | (c << i))
            };

            let binary_product = BinaryFieldElement::<X8_X4_X3_X_1>::new(a)
                * BinaryFieldElement::<X8_X4_X3_X_1>::new(b);
            prop_assert_eq!(bits(extension(a) * extension(b)), binary_product.coefficients());
        }
    }

    /// The strategy is usable, equal values hash equally, and coefficients stay reduced mod P.
    #[test]
    fn test_arbitrary_and_representation_are_sound() {
        use crate::test_support::{
            assert_hash_agrees_with_eq, assert_strategy_is_not_degenerate, draw,
        };
        let strategy = F13x4::arbitrary();
        assert_strategy_is_not_degenerate(&strategy, "ExtensionFieldElement");

        let mut values = draw(&strategy, 32);
        values.extend([F13x4::zero(), F13x4::one(), F13x4::default()]);
        assert_hash_agrees_with_eq(&values, "ExtensionFieldElement");

        for v in &values {
            for c in v.coefficients {
                assert!(c < 13, "{:?} has an unreduced coefficient", v);
            }
        }
    }

    /// A primitive element generates the whole multiplicative group, so its order is q - 1.
    #[test]
    fn test_primitive_element_generates_the_group() {
        let mut rng = StdRng::seed_from_u64(11);

        // GF(9) is small enough to enumerate: the powers of a generator must be every nonzero
        // element exactly once.
        let g = F3x2::primitive_element(&mut rng);
        let mut seen = std::collections::HashSet::new();
        let mut x = F3x2::one();
        for _ in 0..(F3x2::order_u128().unwrap() - 1) {
            x *= g;
            seen.insert(x);
        }
        assert_eq!(seen.len() as u128, F3x2::order_u128().unwrap() - 1);
        assert!(!seen.contains(&F3x2::zero()));
        assert_eq!(g.pow(F3x2::order_u128().unwrap() - 1), F3x2::one());

        // GF(125) likewise.
        let g = F5x3::primitive_element(&mut rng);
        let mut seen = std::collections::HashSet::new();
        let mut x = F5x3::one();
        for _ in 0..(F5x3::order_u128().unwrap() - 1) {
            x *= g;
            seen.insert(x);
        }
        assert_eq!(seen.len() as u128, F5x3::order_u128().unwrap() - 1);

        // GF(13^4) is too large to enumerate, so check the order via the prime divisors of
        // q - 1: a generator must not be killed by any proper divisor.
        let g = F13x4::primitive_element(&mut rng);
        let group_order = F13x4::order_u128().unwrap() - 1;
        assert_eq!(g.pow(group_order), F13x4::one());
        for r in [2u128, 3, 5, 7, 17] {
            assert_eq!(group_order % r, 0, "{} should divide {}", r, group_order);
            assert_ne!(g.pow(group_order / r), F13x4::one(), "r = {}", r);
        }
    }

    /// A primitive nth root of unity satisfies r^n = 1 and r^k != 1 for every 0 < k < n.
    #[test]
    fn test_root_of_unity_is_primitive() {
        let mut rng = StdRng::seed_from_u64(29);

        // The group order of GF(125) is 124 = 2^2 * 31.
        for n in [2u64, 4, 31, 62, 124] {
            let r = F5x3::root_of_unity(n, &mut rng);
            assert_eq!(r.pow(n as u128), F5x3::one(), "n = {}", n);
            for k in 1..n {
                assert_ne!(r.pow(k as u128), F5x3::one(), "n = {}, k = {}", n, k);
            }
        }

        // The group order of GF(9) is 8, so these are the powers of two up to it.
        for n in [2u64, 4, 8] {
            let r = F3x2::root_of_unity(n, &mut rng);
            assert_eq!(r.pow(n as u128), F3x2::one(), "n = {}", n);
            for k in 1..n {
                assert_ne!(r.pow(k as u128), F3x2::one(), "n = {}, k = {}", n, k);
            }
        }
    }

    /// Serialization round-trips, and deserialization reduces coefficients into canonical form.
    #[test]
    fn test_ser_de() {
        let mut rng = StdRng::seed_from_u64(7);
        for _ in 0..32 {
            let element = F13x4::random(&mut rng);
            let bytes = bincode::serialize(&element).unwrap();
            let recovered: F13x4 = bincode::deserialize(&bytes).unwrap();
            assert_eq!(element, recovered);
        }
        // Only the coefficients are encoded; P, N and the modulus live in the type.
        let bytes = bincode::serialize(&F13x4::one()).unwrap();
        assert_eq!(bytes.len(), 4 * std::mem::size_of::<u64>());

        // Coefficients that arrive unreduced are brought back into canonical form, so a decoded
        // value can never compare unequal to the element it represents.
        let unreduced = bincode::serialize(&[14u64, 0, 0, 0]).unwrap();
        let decoded: F13x4 = bincode::deserialize(&unreduced).unwrap();
        assert_eq!(decoded, F13x4::new([1, 0, 0, 0]));
    }
}
