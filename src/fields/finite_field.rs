//! Traits defining a finite field.
//!
//! A finite field is a field of finite order, i.e., number of elements. The order of a finite
//! field is always a prime `p` or a prime power `p^k`.
//!
//! The order lives in [`KnownOrder`] rather than in [`FiniteField`], because a 254-bit prime
//! field has no order that fits in a machine integer and nothing in the algebraic core — the
//! polynomials, the linear algebra, F4, FGLM, Buchberger — ever asks for one. Only root finding,
//! factorization and enumerating the field itself do. Requiring the order of every coefficient
//! type would exclude the wide fields from algorithms that never use it.

use rand::{CryptoRng, RngCore};
use serde::{de::DeserializeOwned, Serialize};
use std::{
    fmt::Display,
    hash::Hash,
    ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};

use crate::{
    fields::two_adic,
    integers::{big_uint::BigUInt, bit, factor, highest_set_bit, num_digits, FromDecStrErr},
    Ring,
};

/// The value of a `BigUInt` that is known to fit in a `u128`.
///
/// Used for the prime factors of q - 1, which cannot exceed q - 1 itself.
fn big_uint_to_u128(value: &BigUInt) -> u128 {
    let words = value.as_le_words();
    assert!(words.len() <= 2, "{:?} does not fit in a u128", value);
    let low = *words.first().unwrap_or(&0) as u128;
    let high = *words.get(1).unwrap_or(&0) as u128;
    low | (high << 64)
}

/// The highest set bit up to which [`FiniteField::pow_limbs`] walks the exponent downward rather
/// than upward — so exponents of 1 through 7, which is every small-exponent call site.
///
/// Neither walk dominates, which is #181's whole finding. The upward walk seeds its accumulator
/// with one and so pays one multiplication *by* one; the downward walk needs no seed, because the
/// highest bit is set by definition, but its squaring and its accumulate are the same value and so
/// form one serial chain where the upward walk's are two values the pipeline overlaps. The seed is
/// a fixed cost and the serialization grows with the exponent, so the downward walk wins while the
/// exponent is short and loses once it is not.
///
/// Measured at both ends and set at the top of the measured downward-wins region rather than at a
/// crossover: `2` is `d5`'s highest bit, and the next width measured is `e31`'s 30. Nothing in this
/// crate uses an exponent between 8 and 2^30 — the small sites are degrees 1 to 5 and the wide ones
/// are `q`-sized — so the unmeasured middle is excluded by the threshold rather than guessed at.
/// `docs/MILESTONE-LARGE-PRIME-FIELDS.md` §4.1.2 has the table.
const NARROW_EXPONENT_BITS: usize = 2;

/// Why a string could not be parsed as a finite field element.
///
/// Carries which character was rejected, so a caller can report the position of the problem
/// rather than only that parsing failed.
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum ParseFieldElementError {
    /// A character was not a decimal digit. Holds the offending byte, offset from `b'0'`.
    InvalidCharacter(u8),

    /// The value did not fit the field's representation.
    OutOfRange,
}

impl Display for ParseFieldElementError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidCharacter(_) => write!(f, "a character is not in the range 0-9"),
            Self::OutOfRange => write!(f, "the value is too large for the field"),
        }
    }
}

impl std::error::Error for ParseFieldElementError {}

impl From<FromDecStrErr> for ParseFieldElementError {
    fn from(err: FromDecStrErr) -> Self {
        match err {
            FromDecStrErr::InvalidCharacter(c) => Self::InvalidCharacter(c),
            FromDecStrErr::InvalidLength => Self::OutOfRange,
        }
    }
}

/// A Finite Field element.
pub trait FiniteField:
    Ring
    + Add<Output = Self>
    + AddAssign
    + Sub<Output = Self>
    + SubAssign
    + Div<Output = Self>
    + DivAssign
    + Mul<Output = Self>
    + MulAssign
    + Neg<Output = Self>
    + Sized
    + Clone
    + Display
    + Default
    + Hash
    + Serialize
    + DeserializeOwned
// + for<'de> Deserialize<'de>
where
    // owned + borrowed
    for<'a> Self: Add<&'a Self, Output = Self>,
    for<'a> Self: Sub<&'a Self, Output = Self>,
    for<'a> Self: Neg<Output = Self>,
    for<'a> Self: Mul<&'a Self, Output = Self>,
    for<'a> Self: Div<&'a Self, Output = Self>,
{
    /// The image of the integer `val` under the unique ring homomorphism from the integers into
    /// this field: `val` copies of [`one`](crate::One::one), which is `val mod p` for
    /// characteristic `p`.
    ///
    /// **This is not an index into the field.** Over a prime field the two coincide, which is why
    /// the distinction went unnoticed until #377; over an extension of degree `k > 1` the image is
    /// the prime subfield — `p` of the `q = p^k` elements — so `new` is not onto and walking it
    /// over `0..q` covers the field `q/p` times rather than once. Use
    /// [`KnownOrder::element_at`] to address elements by index.
    ///
    /// Both characteristic-two types also have an *inherent* `new` that takes a representation
    /// (a bit pattern, or an array of coefficients) rather than an integer. Inherent methods win
    /// method resolution, so `BinaryFieldElement::<P>::new(5)` is the bit pattern `0b101` while
    /// `<BinaryFieldElement<P> as FiniteField>::new(5)` is `5 mod 2 = 1`.
    fn new(val: u64) -> Self;

    /// Parse a field element from the text [`Display`] writes for it.
    ///
    /// `Self::from_str(&a.to_string()) == Ok(a)` for every element `a` of every field in this
    /// crate. That round trip, and not the integer embedding of [`Self::new`], is the contract:
    /// `Display` has to distinguish all `q` elements, which an integer embedding cannot, so over
    /// an extension field the accepted syntax is a *representation* and `from_str("5")` is
    /// deliberately not `new(5)`.
    ///
    /// Per field, the accepted syntax is:
    ///
    /// - **prime fields** — a decimal integer, taken mod `p`. Representation and embedding agree
    ///   here, so this is both.
    /// - **[`BinaryFieldElement`](super::BinaryFieldElement)** — a decimal integer read as the
    ///   coefficient bit pattern, which is what its `Display` writes.
    /// - **[`ExtensionFieldElement`](super::ExtensionFieldElement)** — either the bracketed
    ///   coefficient list `[c_0, c_1, ..., c_{k-1}]` its `Display` writes, or a bare decimal read
    ///   as the base-`p` digits of the same list.
    ///
    /// The two characteristic-two readings are the same rule: a bare decimal is the element's
    /// index, [`KnownOrder::element_at`]. It agrees with `new` on `0..p` — so on `0` and `1` in
    /// every field — and extends it to the whole field instead of folding onto the subfield.
    ///
    /// Returns [`ParseFieldElementError`] rather than panicking; a value outside the field's
    /// representation is [`ParseFieldElementError::OutOfRange`].
    fn from_str(_value: &str) -> Result<Self, ParseFieldElementError>;

    /// A uniformly random field element.
    fn random<R: RngCore + CryptoRng>(rng: &mut R) -> Self;

    /// `self^b`. `0^0 = 1`.
    ///
    /// Exponentiation by squaring, by delegation to [`Self::pow_limbs`] — the same algorithm as a
    /// loop. The body was recursive until #181. The recursion cost about `2 log2(b)` non-inlined
    /// frames, which is nothing against an expensive multiplication and most of the call against
    /// a cheap one: dropping it is **1.9x** at the ~31- and ~63-bit exponents
    /// `PowerPermutation::invert` uses over a 31-bit or 64-bit field, and 1.4x at the degree-3 and
    /// degree-5 exponents of `Monomial::eval`, `SparseMultiPoly::substitute` and Poseidon's
    /// S-box. See `docs/MILESTONE-LARGE-PRIME-FIELDS.md` §4.1.2.
    fn pow(&self, b: u128) -> Self {
        self.pow_limbs(&[b as u64, (b >> 64) as u64])
    }

    /// `self^exponent`, with the exponent as little-endian 64-bit limbs.
    ///
    /// [`Self::pow`] takes a `u128`, which cannot express the exponents a wide field needs:
    /// `(q - 1) / 2^s` for a 254-bit q is itself 226 bits. The cost is one squaring per bit of
    /// the exponent either way, and trailing zero limbs cost nothing, so a caller may pass a
    /// fixed-width value without trimming it.
    ///
    /// `0^0 = 1`, as in [`Self::pow`].
    ///
    /// Two walks, chosen on the exponent's width: see [`NARROW_EXPONENT_BITS`].
    fn pow_limbs(&self, exponent: &[u64]) -> Self {
        let Some(highest) = highest_set_bit(exponent) else {
            // A zero exponent, including for a zero base.
            return Self::one();
        };

        if highest <= NARROW_EXPONENT_BITS {
            // Downward. The highest bit is set by definition, so the accumulator starts at the
            // base and the multiplication that would consume that bit never happens.
            let mut result = *self;
            for index in (0..highest).rev() {
                result = result * result;
                if bit(exponent, index) {
                    result *= *self;
                }
            }
            return result;
        }

        // Upward, from an accumulator seeded with one. The seed costs one multiplication *by*
        // one, which is why the narrow case is not taken this way; what it buys is that the
        // squaring and the accumulate are two different values rather than one, so the pipeline
        // overlaps them instead of serializing them.
        let mut result = Self::one();
        let mut square = *self;
        for index in 0..=highest {
            if bit(exponent, index) {
                result *= square;
            }
            // The last squaring would be discarded, and for a wide exponent it is not cheap.
            if index < highest {
                square = square * square;
            }
        }
        result
    }

    /// The additive inverse of this element.
    fn neg(&self) -> Self {
        Self::zero() - self
    }

    /// The multiplicative inverse of this element.
    ///
    /// Required rather than provided: the obvious default is `a^(q-2)`, which needs the field's
    /// order, and the order lives in [`KnownOrder`] precisely so that `FiniteField` does not
    /// demand it. An implementation that has an order writes Fermat as
    /// `self.pow_limbs(&FERMAT_EXPONENT_LIMBS)` — no width limit, since both the exponent and the
    /// walk are over limbs; the rest delegate to their own inversion.
    ///
    /// # Panics
    /// Panics if `self` is zero. Use [`Self::checked_div`] where zero is possible — pivot
    /// normalization inverts only pivots, which are nonzero by construction, so no `Option`
    /// enters the inner loops.
    fn inverse(&self) -> Self;

    fn checked_div(&self, rhs: &Self) -> Option<Self> {
        if rhs.is_zero() {
            None
        } else {
            Some(*self / rhs)
        }
    }
}

/// `limbs` without its trailing zero words, so that the result is canonical.
///
/// Takes and returns `&'static` because an implementation of [`KnownOrder`] produces its limbs
/// from an associated const, which promotes.
pub fn trim_limbs(limbs: &'static [u64]) -> &'static [u64] {
    &limbs[..num_digits(limbs)]
}

/// Why a generator or a root of unity could not be constructed.
///
/// Every variant is a fact about the field and the requested order rather than a programmer error:
/// whether `n` divides `q - 1` depends on the modulus, and which field a caller instantiated is
/// often a runtime choice. So these are returned by the `try_` constructors on [`KnownOrder`]
/// instead of aborting the process.
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum RootOfUnityError {
    /// `n` does not divide `q - 1`, so no element has order exactly `n`. Includes `n = 0`.
    OrderDoesNotDivide { n: u64 },

    /// A `2^log_n`-th root was asked of a field whose two-adicity is smaller.
    TwoAdicityExceeded { log_n: u32, two_adicity: u32 },

    /// The order does not fit in a `u128`, which the generator search needs to factor `q - 1`.
    OrderTooWide,

    /// The field declares no generator, and finding one would mean factoring a `q - 1` this
    /// crate will not factor by accident. See [`PrimeFieldElement256`](super::PrimeFieldElement256).
    NoKnownGenerator,
}

impl Display for RootOfUnityError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::OrderDoesNotDivide { n } => {
                write!(f, "{n} does not divide q - 1, so no element has order {n}")
            }
            Self::TwoAdicityExceeded { log_n, two_adicity } => write!(
                f,
                "no primitive 2^{log_n}-th root of unity exists: the two-adicity of this field \
                 is {two_adicity}"
            ),
            Self::OrderTooWide => {
                write!(f, "the field's order does not fit in a u128")
            }
            Self::NoKnownGenerator => write!(
                f,
                "this field declares no generator, and finding one would mean factoring q - 1"
            ),
        }
    }
}

impl std::error::Error for RootOfUnityError {}

/// [`KnownOrder::try_primitive_element`]'s default, as a function so that a field which overrides
/// it can still be tested against the behaviour it inherited.
pub(crate) fn default_primitive_element<F: KnownOrder, R: RngCore + CryptoRng>(
    rng: &mut R,
) -> Result<F, RootOfUnityError> {
    let group_order = F::order_u128().ok_or(RootOfUnityError::OrderTooWide)? - 1;
    let (prime_factors, _powers) = factor(&BigUInt::new_from_u128(group_order), rng);
    let quotients: Vec<u128> = prime_factors
        .iter()
        .map(|r| group_order / big_uint_to_u128(r))
        .collect();

    loop {
        let candidate = F::random(rng);
        if candidate.is_zero() {
            continue;
        }
        if quotients
            .iter()
            .all(|&exponent| candidate.pow(exponent) != F::one())
        {
            return Ok(candidate);
        }
    }
}

/// A finite field whose order is known.
///
/// Separate from [`FiniteField`] so that a field whose order exceeds any machine integer can
/// still be a polynomial coefficient. The order is little-endian 64-bit limbs rather than an
/// integer type, which covers 64-, 128- and 256-bit orders without choosing a width or
/// allocating; [`Self::order_u128`] is there for the callers that genuinely need a machine
/// integer and are entitled to fail without one.
///
/// Implemented by every field in this crate, including the wide prime fields. What a wide field
/// cannot do is *enumerate* itself, which is a property of its size rather than of this trait.
pub trait KnownOrder: FiniteField {
    /// The number of elements q = p^k in the field, as little-endian 64-bit limbs.
    ///
    /// Canonical: no trailing zero limb, and empty is impossible since q >= 2. Implementations
    /// pass their order through [`trim_limbs`].
    fn order_limbs() -> &'static [u64];

    /// The characteristic p of a field of order q = p^k, as little-endian 64-bit limbs.
    ///
    /// Not the same as [`Self::order_limbs`] unless k = 1. Extension fields must keep the
    /// distinction.
    fn characteristic_limbs() -> &'static [u64];

    /// The order q, or `None` if it does not fit in a `u128`.
    fn order_u128() -> Option<u128> {
        limbs_to_u128(Self::order_limbs())
    }

    /// The characteristic p, or `None` if it does not fit in a `u128`.
    fn characteristic_u128() -> Option<u128> {
        limbs_to_u128(Self::characteristic_limbs())
    }

    /// The element at `index` in a fixed enumeration of the field, or `None` if `index >= q`.
    ///
    /// A bijection from `0..q` onto the field, which is what [`FiniteField::new`] is not: over an
    /// extension `new` lands in the prime subfield, so an enumeration driven by it covers `p` of
    /// the `q` elements. The two agree on `0..p`, and so on `0` and `1` in every field. Which
    /// element sits at which index is implementation-defined beyond that; only coverage is
    /// promised.
    ///
    /// The index is a `u128` because that is the widest the order is exposed as — see
    /// [`Self::order_u128`].
    ///
    /// # The default
    /// The default is `new`, which is that bijection exactly when `q = p`. Over a field whose
    /// order and characteristic differ it returns `None` for every index rather than an element
    /// `new` would have put in the wrong place: a field that has not overridden this reports that
    /// it cannot be enumerated, and never enumerates wrongly. Both extension families in this
    /// crate override it.
    ///
    /// `new` takes a `u64`, so the default also stops at index `2^64` over a prime field wider
    /// than that. Nothing is lost: a field of order above `2^64` is not enumerable by any route.
    fn element_at(index: u128) -> Option<Self> {
        if Self::order_limbs() != Self::characteristic_limbs() {
            // An extension field: `new` would fold `0..q` onto the prime subfield.
            return None;
        }
        if Self::order_u128().is_some_and(|q| index >= q) {
            return None;
        }
        Some(Self::new(u64::try_from(index).ok()?))
    }

    /// A primitive element of the finite field is a generator of the field's multiplicative group.
    ///
    /// Found by random search. The multiplicative group of a finite field is cyclic of order
    /// q - 1, and an element generates it unless its order is a proper divisor of q - 1. Every
    /// proper divisor divides (q - 1) / r for some prime r | q - 1, so those quotients are the
    /// only exponents worth testing. See Handbook of Applied Cryptography, Algorithm 4.80.
    ///
    /// This default uses nothing but the field's own arithmetic, but it does factor q - 1, so it
    /// needs the order as an integer. A type with a cheaper construction should override it — the
    /// prime fields do, via `find_generator`, which exploits their elements being integers mod p,
    /// and a field whose provider declares a generator should return that.
    fn try_primitive_element<R: RngCore + CryptoRng>(
        rng: &mut R,
    ) -> Result<Self, RootOfUnityError> {
        default_primitive_element::<Self, R>(rng)
    }

    /// A primitive element, panicking if the field has none this crate can find.
    ///
    /// A convenience over [`Self::try_primitive_element`], which is the one to override.
    ///
    /// # Panics
    /// Panics with the [`RootOfUnityError`] the fallible form returns.
    fn primitive_element<R: RngCore + CryptoRng>(rng: &mut R) -> Self {
        Self::try_primitive_element(rng).unwrap_or_else(|e| panic!("{e}"))
    }

    /// True if this element generates the whole multiplicative group.
    ///
    /// An element fails to generate exactly when its order is a proper divisor of `q - 1`, and
    /// every proper divisor divides `(q - 1) / r` for some prime `r | q - 1`, so those quotients
    /// are the only exponents worth testing — the same factorization and the same reasoning as
    /// [`Self::try_primitive_element`]'s search, which is how that search can now be checked
    /// against something other than itself.
    ///
    /// Fails if the order does not fit in a `u128`, since the factorization does not either.
    fn try_is_generator<R: RngCore + CryptoRng>(
        &self,
        rng: &mut R,
    ) -> Result<bool, RootOfUnityError> {
        let group_order = Self::order_u128().ok_or(RootOfUnityError::OrderTooWide)? - 1;
        if self.is_zero() {
            return Ok(false);
        }

        let (prime_factors, _powers) = factor(&BigUInt::new_from_u128(group_order), rng);
        Ok(prime_factors
            .iter()
            .all(|r| self.pow(group_order / big_uint_to_u128(r)) != Self::one()))
    }

    /// True if this element generates the whole multiplicative group.
    ///
    /// # Panics
    /// Panics if the order does not fit in a `u128`. Use [`Self::try_is_generator`] over a field
    /// whose width is a runtime choice.
    fn is_generator<R: RngCore + CryptoRng>(&self, rng: &mut R) -> bool {
        self.try_is_generator(rng).unwrap_or_else(|e| panic!("{e}"))
    }

    /// True if this element has order exactly `n`.
    ///
    /// `self^n = 1` and `self^(n/r) != 1` for each prime `r | n`. This factors only `n`, never
    /// `q - 1`, so unlike [`Self::try_is_generator`] it is available over the wide fields — which
    /// is what makes it the check on [`Self::try_two_adic_root_of_unity`]'s construction.
    ///
    /// False for `n = 0`, which no element satisfies.
    ///
    /// `n: u64` caps the testable order at `2^63`, the same ceiling [`Self::try_root_of_unity`]
    /// has. For a power-of-two order above it, test `2^k` limb-wise instead:
    /// `pow_limbs(2^k) == 1` and `pow_limbs(2^(k-1)) != 1` is the whole condition, since every
    /// proper divisor of `2^k` divides its half.
    fn is_primitive_nth_root<R: RngCore + CryptoRng>(&self, n: u64, rng: &mut R) -> bool {
        if n == 0 || self.pow(n as u128) != Self::one() {
            return false;
        }

        let (prime_factors, _powers) = factor(&BigUInt::new_from_u64(n), rng);
        prime_factors
            .iter()
            .all(|r| self.pow(n as u128 / big_uint_to_u128(r)) != Self::one())
    }

    /// A primitive nth root of unity: an element of order exactly `n`.
    ///
    /// Fails unless `n` divides `q - 1`, which is when such an element exists at all, and unless
    /// the field has a generator this crate can produce. A power-of-two `n` over a wide field
    /// needs neither — see [`Self::try_two_adic_root_of_unity`].
    ///
    /// `n: u64` caps the nameable order at `2^63`, there being no `u64` equal to `2^64`. A field
    /// whose [`Self::two_adicity`] exceeds 63 — `3*2^66 + 1` is one — therefore holds primitive
    /// power-of-two roots this cannot be asked for at all; [`Self::try_two_adic_root_of_unity`]
    /// takes `log_n: u32` and reaches them. The ceiling costs no capability: a transform of size
    /// `2^64` is not computable, so the orders it hides are not orders an NTT would run at.
    fn try_root_of_unity<R: RngCore + CryptoRng>(
        n: u64,
        rng: &mut R,
    ) -> Result<Self, RootOfUnityError> {
        let group_order = Self::order_u128().ok_or(RootOfUnityError::OrderTooWide)? - 1;
        if n == 0 || !group_order.is_multiple_of(n as u128) {
            return Err(RootOfUnityError::OrderDoesNotDivide { n });
        }

        // If g has order q - 1, then g^((q-1)/n) has order exactly n.
        let g = Self::try_primitive_element(rng)?;
        Ok(g.pow(group_order / n as u128))
    }

    /// A primitive nth root of unity, panicking if the field holds none.
    ///
    /// A convenience over [`Self::try_root_of_unity`], whose `2^63` ceiling on `n` it inherits.
    /// That is also the method to override.
    ///
    /// # Panics
    /// Panics with the [`RootOfUnityError`] the fallible form returns.
    fn root_of_unity<R: RngCore + CryptoRng>(n: u64, rng: &mut R) -> Self {
        Self::try_root_of_unity(n, rng).unwrap_or_else(|e| panic!("{e}"))
    }

    /// The field's two-adicity: the largest s with `2^s` dividing `q - 1`.
    ///
    /// The ceiling on every power-of-two NTT over this field — a transform of size `2^k` needs a
    /// primitive `2^k`-th root of unity, which exists exactly for `k <= s`. Read off `q - 1`
    /// rather than declared, so it cannot disagree with the compiled-in modulus.
    ///
    /// Where `s > 63` this exceeds what [`Self::try_root_of_unity`] can be asked for, since its
    /// `n: u64` names no order above `2^63`. [`Self::try_two_adic_root_of_unity`] serves the
    /// whole range.
    fn two_adicity() -> u32 {
        two_adic::two_adic_decomposition(Self::order_limbs()).0
    }

    /// A square root of this element, or `None` if it is not a square.
    ///
    /// Tonelli-Shanks, over every field in the crate including characteristic two; see
    /// [`sqrt`](super::sqrt). On [`KnownOrder`] rather than [`FiniteField`] because the exponents
    /// it raises to are read off `q - 1`.
    ///
    /// Of the two roots `+-r` it is unspecified which is returned. The rng is drawn from only
    /// where a quadratic non-residue is needed — see the module comment for when that is.
    fn sqrt<R: RngCore + CryptoRng>(&self, rng: &mut R) -> Option<Self> {
        super::sqrt::sqrt(self, rng)
    }

    /// A primitive `2^log_n`-th root of unity.
    ///
    /// Unlike [`Self::try_root_of_unity`] this needs no generator and so no factorization of
    /// `q - 1`, which is what makes it the only usable path over a 254-bit field. See
    /// [`two_adic`](super::two_adic).
    ///
    /// Fails only if `log_n` exceeds [`Self::two_adicity`], where no such root exists.
    fn try_two_adic_root_of_unity<R: RngCore + CryptoRng>(
        log_n: u32,
        rng: &mut R,
    ) -> Result<Self, RootOfUnityError> {
        two_adic::try_two_adic_root_of_unity::<Self, R>(log_n, rng)
    }

    /// A primitive `2^log_n`-th root of unity, panicking if the field holds none.
    ///
    /// # Panics
    /// Panics if `log_n` exceeds [`Self::two_adicity`].
    fn two_adic_root_of_unity<R: RngCore + CryptoRng>(log_n: u32, rng: &mut R) -> Self {
        Self::try_two_adic_root_of_unity(log_n, rng).unwrap_or_else(|e| panic!("{e}"))
    }
}

/// The recursive square-and-multiply that every `inverse` reached through before #160.
///
/// Frozen here rather than delegating to [`FiniteField::pow`], so that the differential tests
/// keep comparing against the historical behaviour even if `pow`'s default body changes.
#[cfg(test)]
pub(crate) fn recursive_pow<F: FiniteField>(a: &F, b: u128) -> F {
    if a.is_zero() {
        if b == 0 {
            // 0^0 = 1.
            return F::one();
        }
        return F::zero();
    }

    if b == 0 {
        return F::one();
    }

    if b == 1 {
        *a
    } else if b.is_multiple_of(2) {
        let y = recursive_pow(a, b / 2);
        y * y
    } else {
        *a * recursive_pow(a, b - 1)
    }
}

/// `a^(q - 2)` by the pre-#160 route: [`recursive_pow`] over an exponent taken in a `u128`.
///
/// The reference every field's `inverse` is differentially tested against.
///
/// # Panics
/// Panics if the order does not fit in a `u128`, which excludes the fields that never used this
/// route in the first place.
#[cfg(test)]
pub(crate) fn fermat_inverse_via_recursive_pow<F: KnownOrder>(a: &F) -> F {
    let order = F::order_u128().expect("the reference inverse needs the order as an integer");
    recursive_pow(a, order - 2)
}

/// `limbs` as a `u128`, or `None` if it is wider than that.
fn limbs_to_u128(limbs: &[u64]) -> Option<u128> {
    if limbs.len() > 2 {
        return None;
    }
    let low = *limbs.first().unwrap_or(&0) as u128;
    let high = *limbs.get(1).unwrap_or(&0) as u128;
    Some(low | (high << 64))
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use rand::{prelude::StdRng, SeedableRng};

    use super::{
        default_primitive_element, fermat_inverse_via_recursive_pow, recursive_pow,
        RootOfUnityError,
    };
    use crate::{
        fields::{
            binary_field::BinaryFieldElement,
            extension_field::ExtensionFieldElement,
            irreducible_polynomials::{Modulus13Pow4, X8_X4_X3_X_1},
            Bn254Fr, Gf13Pow4, Gf256, Zp13, Zp2, Zp2147483647,
        },
        FiniteField, KnownOrder, One, Zero,
    };

    // Inversion returns exactly what the pre-#160 recursive-pow route returned, over every field.
    for_each_field!(
        fn inverse_matches_the_recursive_pow_reference<F>() {
            // A 254-bit order has no `u128` for the reference to take `q - 2` in, and those
            // fields invert by extended Euclid rather than by Fermat, so there is no recursive
            // route to compare against.
            if F::order_u128().is_some() {
                let mut rng = StdRng::seed_from_u64(160);
                for _ in 0..20 {
                    let a = F::random(&mut rng);
                    if !a.is_zero() {
                        assert_eq!(
                            a.inverse(),
                            fermat_inverse_via_recursive_pow(&a),
                            "1/{a} changed"
                        );
                    }
                }
            }
        }
    );

    // `pow` returns exactly what the frozen recursive square-and-multiply returned, over every
    // field and at every exponent width the call sites use.
    for_each_field!(
        fn pow_matches_the_recursive_pow_reference<F>() {
            let mut rng = StdRng::seed_from_u64(181);
            let mut values = vec![F::zero(), F::one()];
            for _ in 0..8 {
                values.push(F::random(&mut rng));
            }
            for a in values {
                // 3 and 5 are every small-exponent site; the two wide ones are the width of
                // `PowerPermutation`'s inverse exponent over a 31-bit and a 64-bit field; and 1
                // and `u128::MAX` are the ends of the range `pow` accepts.
                for b in [
                    0u128,
                    1,
                    2,
                    3,
                    5,
                    17,
                    255,
                    0x5A5A_5A5B,
                    0x5A5A_5A5A_5A5A_5A5B,
                    u64::MAX as u128,
                    u128::MAX,
                ] {
                    assert_eq!(a.pow(b), recursive_pow(&a, b), "{a}^{b} changed");
                }
            }
        }
    );

    // `from_str` reads back exactly the text `Display` wrote, over every field.
    for_each_field!(
        fn from_str_inverts_display<F>() {
            let mut rng = StdRng::seed_from_u64(377);
            for _ in 0..20 {
                let a = F::random(&mut rng);
                assert_eq!(F::from_str(&a.to_string()), Ok(a), "{a} did not round trip");
            }
            assert_eq!(F::from_str(&F::zero().to_string()), Ok(F::zero()));
            assert_eq!(F::from_str(&F::one().to_string()), Ok(F::one()));
        }
    );

    // `new(k)` is k copies of one — the integer embedding — in every field.
    for_each_field!(
        fn new_is_the_integer_embedding<F>() {
            let mut sum = F::zero();
            for k in 0..10u64 {
                assert_eq!(F::new(k), sum, "new({k}) is not {k} copies of one");
                sum += F::one();
            }
        }
    );

    // `element_at` is a bijection from `0..q` onto the field, and `None` at `q`.
    for_each_small_field!(
        fn element_at_covers_the_field_exactly_once<F>() {
            let q = F::order_u128().expect("a small field has an order");
            let elements: HashSet<F> = (0..q)
                .map(|i| F::element_at(i).expect("every index below q names an element"))
                .collect();
            assert_eq!(elements.len(), q as usize, "element_at repeated an element");
            assert_eq!(F::element_at(q), None);
        }
    );

    /// Over GF(2) the embedding and the index coincide, so text input there is unchanged by #377.
    #[test]
    fn test_over_gf2_the_embedding_and_the_index_agree() {
        for value in 0..2u64 {
            assert_eq!(Zp2::element_at(value as u128), Some(Zp2::new(value)));
            assert_eq!(Zp2::from_str(&value.to_string()), Ok(Zp2::new(value)));
        }
        assert_eq!(Zp2::element_at(2), None);
        assert_eq!(Zp2::new(0).to_string(), "0");
        assert_eq!(Zp2::new(1).to_string(), "1");
    }

    /// `element_at` covers an extension field; `new` over the same range covers only `p` elements.
    ///
    /// The distinction #377 turns on, asserted rather than described: both maps are run over
    /// `0..q` and their images counted.
    #[test]
    fn test_element_at_covers_an_extension_field_where_new_does_not() {
        fn both_maps<F: KnownOrder>() {
            let q = F::order_u128().expect("a small field has an order");
            let p = F::characteristic_u128().expect("a small characteristic");

            let indexed: HashSet<F> = (0..q)
                .map(|i| F::element_at(i).expect("every index below q names an element"))
                .collect();
            assert_eq!(indexed.len(), q as usize, "element_at missed an element");

            let embedded: HashSet<F> = (0..q).map(|i| F::new(i as u64)).collect();
            assert_eq!(
                embedded.len(),
                p as usize,
                "new reaches more than the prime subfield"
            );
        }

        both_maps::<Gf256>();
        both_maps::<Gf13Pow4>();
    }

    /// An order below 2^64 reports one limb, not a word padded with a zero.
    #[test]
    fn test_a_narrow_order_reports_one_limb() {
        assert_eq!(Zp2147483647::order_limbs(), &[2147483647]);
        assert_eq!(Zp2147483647::order_u128(), Some(2147483647));
    }

    /// An order above 2^64 reports both limbs, least significant first.
    #[test]
    #[allow(deprecated)]
    fn test_a_wide_order_reports_both_limbs_little_endian() {
        // 3 * 2^66 + 1 = 12 * 2^64 + 1.
        type F = crate::fields::PrimeFieldElement128<221360928884514619393>;
        assert_eq!(F::order_limbs(), &[1, 12]);
        assert_eq!(F::order_u128(), Some(221360928884514619393));
    }

    /// An extension field reports q = p^k and p separately, not the same value twice.
    #[test]
    fn test_an_extension_field_separates_its_order_from_its_characteristic() {
        type F = ExtensionFieldElement<13, 4, Modulus13Pow4>;
        assert_eq!(F::order_limbs(), &[28561]); // 13^4
        assert_eq!(F::characteristic_limbs(), &[13]);
    }

    /// A binary field has characteristic two whatever its order.
    #[test]
    fn test_a_binary_field_has_characteristic_two() {
        type F = BinaryFieldElement<X8_X4_X3_X_1>;
        assert_eq!(F::order_limbs(), &[256]);
        assert_eq!(F::characteristic_limbs(), &[2]);
    }

    /// `pow_limbs` agrees with the frozen recursive reference on every exponent both can express.
    ///
    /// Against [`recursive_pow`] and not against `pow`, which since #181 *is* `pow_limbs` and so
    /// would make this tautological.
    #[test]
    #[allow(deprecated)]
    fn test_pow_limbs_agrees_with_the_recursive_reference() {
        type F = crate::fields::PrimeFieldElement128<221360928884514619393>;
        for value in [0u64, 1, 2, 3, 97, 12345] {
            let a = <F as FiniteField>::new(value);
            for exponent in [0u128, 1, 2, 3, 8, 17, 64, 255, 1 << 40, u64::MAX as u128] {
                let limbs = [exponent as u64, (exponent >> 64) as u64];
                assert_eq!(
                    a.pow_limbs(&limbs),
                    recursive_pow(&a, exponent),
                    "{value}^{exponent}"
                );
            }
        }
    }

    /// Trailing zero limbs do not change the result, so a fixed-width order needs no trimming.
    #[test]
    fn test_pow_limbs_ignores_trailing_zero_limbs() {
        let a = Zp2147483647::new(7);
        let expected = a.pow(1000);
        for padded in [vec![1000u64], vec![1000, 0], vec![1000, 0, 0, 0]] {
            assert_eq!(a.pow_limbs(&padded), expected);
        }
    }

    /// An exponent beyond a `u128`, checked against the squarings it is made of.
    ///
    /// Fermat pins the answer independently: `a^(q-1) = 1`, and `2^192 mod (q - 1)` is computed
    /// here by the same squaring chain rather than by the limb bit-walk under test.
    #[test]
    fn test_pow_limbs_handles_an_exponent_beyond_u128() {
        let a = Zp2147483647::new(5);

        // 2^192: the fourth limb's lowest bit.
        let exponent = [0u64, 0, 0, 1];
        let mut expected = a;
        for _ in 0..192 {
            expected = expected * expected;
        }
        assert_eq!(a.pow_limbs(&exponent), expected);
    }

    /// An order that does not divide `q - 1` is a value, not a panic.
    #[test]
    fn test_a_requested_order_that_does_not_divide_the_group_order_is_an_error() {
        let mut rng = StdRng::seed_from_u64(1);
        // Zp13 has group order 12, which 5 does not divide.
        assert_eq!(
            Zp13::try_root_of_unity(5, &mut rng),
            Err(RootOfUnityError::OrderDoesNotDivide { n: 5 })
        );
    }

    /// A zero order is rejected as an error rather than dividing by zero.
    #[test]
    fn test_a_zero_order_is_an_error_rather_than_a_division_by_zero() {
        let mut rng = StdRng::seed_from_u64(2);
        assert_eq!(
            Zp13::try_root_of_unity(0, &mut rng),
            Err(RootOfUnityError::OrderDoesNotDivide { n: 0 })
        );
    }

    /// An order that does divide `q - 1` still returns a root of that exact order.
    #[test]
    fn test_an_order_dividing_the_group_order_yields_a_root_of_that_order() {
        let mut rng = StdRng::seed_from_u64(3);
        let w = Zp13::try_root_of_unity(6, &mut rng).expect("6 divides 12");
        assert!(w.pow(6).is_one());
        assert!(!w.pow(3).is_one());
        assert!(!w.pow(2).is_one());
    }

    /// A field that declares no generator says so as a value.
    #[test]
    fn test_a_wide_field_reports_that_it_has_no_known_generator() {
        let mut rng = StdRng::seed_from_u64(5);
        assert_eq!(
            Bn254Fr::try_primitive_element(&mut rng),
            Err(RootOfUnityError::NoKnownGenerator)
        );
    }

    /// The generator search reports an order too wide to express rather than panicking on it.
    ///
    /// Reached through the default implementation directly: the only field in the crate whose
    /// order exceeds a `u128` overrides it with [`RootOfUnityError::NoKnownGenerator`], so this is
    /// the behaviour any future wide field inherits before it overrides anything.
    #[test]
    fn test_the_default_generator_search_rejects_an_order_wider_than_a_u128() {
        let mut rng = StdRng::seed_from_u64(7);
        assert_eq!(
            default_primitive_element::<Bn254Fr, _>(&mut rng),
            Err(RootOfUnityError::OrderTooWide)
        );
    }

    /// A two-adic root beyond the field's two-adicity is an error naming both exponents.
    #[test]
    fn test_a_two_adic_root_beyond_the_two_adicity_is_an_error() {
        let mut rng = StdRng::seed_from_u64(11);
        assert_eq!(
            Bn254Fr::try_two_adic_root_of_unity(29, &mut rng),
            Err(RootOfUnityError::TwoAdicityExceeded {
                log_n: 29,
                two_adicity: 28,
            })
        );
    }

    /// The panicking wrappers still panic, so existing call sites keep their behaviour.
    #[test]
    #[should_panic(expected = "does not divide q - 1")]
    fn test_the_panicking_wrapper_still_panics() {
        let mut rng = StdRng::seed_from_u64(13);
        let _ = Zp13::root_of_unity(5, &mut rng);
    }

    /// A primitive root mod 13 is recognized as a generator, and an element of order 3 is not.
    #[test]
    fn test_is_generator_separates_a_primitive_root_from_the_rest() {
        let mut rng = StdRng::seed_from_u64(29);
        // 2 has order 12 mod 13; 3 has order 3, since 3^3 = 27 = 1.
        assert!(Zp13::new(2).is_generator(&mut rng));
        assert!(!Zp13::new(3).is_generator(&mut rng));
        assert!(!Zp13::new(12).is_generator(&mut rng)); // order 2
        assert!(!Zp13::one().is_generator(&mut rng));
        assert!(!Zp13::zero().is_generator(&mut rng));
    }

    /// Whatever the search returns is a generator, over every field it can search.
    ///
    /// The predicate and the search share the factorization but not the acceptance test, so this
    /// is the check `primitive_element` never had on its own result.
    #[test]
    fn test_the_search_returns_something_the_predicate_accepts() {
        fn search_agrees_with_the_predicate<F: KnownOrder>(seed: u64) {
            let mut rng = StdRng::seed_from_u64(seed);
            let g = F::primitive_element(&mut rng);
            assert!(g.is_generator(&mut rng), "{g} is not a generator");
        }

        search_agrees_with_the_predicate::<Zp13>(31);
        search_agrees_with_the_predicate::<Zp2147483647>(37);
        search_agrees_with_the_predicate::<BinaryFieldElement<X8_X4_X3_X_1>>(41);
        search_agrees_with_the_predicate::<ExtensionFieldElement<13, 4, Modulus13Pow4>>(43);
    }

    /// Checking a generator of a field whose order exceeds a `u128` is an error, not a panic.
    #[test]
    fn test_is_generator_over_a_wide_field_is_an_error() {
        let mut rng = StdRng::seed_from_u64(47);
        assert_eq!(
            Bn254Fr::one().try_is_generator(&mut rng),
            Err(RootOfUnityError::OrderTooWide)
        );
    }

    /// An element of order exactly n is a primitive nth root; one of order dividing n is not.
    #[test]
    fn test_is_primitive_nth_root_requires_the_exact_order() {
        let mut rng = StdRng::seed_from_u64(53);
        let w = Zp13::try_root_of_unity(6, &mut rng).expect("6 divides 12");
        assert!(w.is_primitive_nth_root(6, &mut rng));
        // w^2 has order 3 and w^3 has order 2, so neither is a primitive 6th root.
        assert!(!w.pow(2).is_primitive_nth_root(6, &mut rng));
        assert!(!w.pow(3).is_primitive_nth_root(6, &mut rng));
        assert!(w.pow(2).is_primitive_nth_root(3, &mut rng));
        assert!(w.pow(3).is_primitive_nth_root(2, &mut rng));
    }

    /// One is the only primitive first root of unity, and no element is a primitive 0th root.
    #[test]
    fn test_the_degenerate_orders_of_is_primitive_nth_root() {
        let mut rng = StdRng::seed_from_u64(59);
        assert!(Zp13::one().is_primitive_nth_root(1, &mut rng));
        assert!(!Zp13::new(2).is_primitive_nth_root(1, &mut rng));
        assert!(!Zp13::one().is_primitive_nth_root(0, &mut rng));
        assert!(!Zp13::zero().is_primitive_nth_root(1, &mut rng));
    }

    /// The nth-root predicate works over a field too wide to have a findable generator.
    ///
    /// It factors only `n`, never `q - 1`, which is the whole reason it exists separately.
    #[test]
    fn test_is_primitive_nth_root_works_over_a_wide_field() {
        let mut rng = StdRng::seed_from_u64(61);
        let w = Bn254Fr::two_adic_root_of_unity(10, &mut rng);
        assert!(w.is_primitive_nth_root(1 << 10, &mut rng));
        assert!(!w.is_primitive_nth_root(1 << 11, &mut rng));
        assert!(!(w * w).is_primitive_nth_root(1 << 10, &mut rng));
    }

    /// Zero to a zero exponent is one, as it is for `pow`; zero to any other is zero.
    #[test]
    fn test_pow_limbs_of_zero() {
        let zero = Zp2147483647::zero();
        assert!(zero.pow_limbs(&[0]).is_one());
        assert!(zero.pow_limbs(&[]).is_one());
        assert!(zero.pow_limbs(&[1]).is_zero());
        assert!(zero.pow_limbs(&[0, 1]).is_zero());
    }
}
