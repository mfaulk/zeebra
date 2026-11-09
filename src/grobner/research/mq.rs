//! Importing Fukuoka MQ Challenge instances, exactly as published.
//!
//! <https://www.mqchallenge.org/>. Six problem types: GF(2), GF(2^8) and GF(31), each as an
//! encryption family (`m = 2n`, overdetermined) and a signature family (`n ≈ 1.5m`,
//! underdetermined). The GF(31) and GF(2^8) types are importable here; GF(2) is not — see
//! [`MqField`] for why.
//!
//! # The file format, as it actually is
//!
//! ```text
//! Galois Field : GF(31)
//! Number of variables (n) : 10
//! Number of polynomials (m) : 20
//! Seed : 0
//! Order : graded reverse lex order
//!
//! *********************
//! 16 3 26 15 ... 18 ;
//! 5 0 18 23 ... 15 ;
//! ```
//!
//! One line per polynomial, terminated by ` ;`, each carrying `n(n+1)/2 + n + 1` coefficients.
//!
//! # The base a coefficient is written in is decided by the header
//!
//! A GF(2^8) file does not say `GF(2^8)`. It states the quotient ring, verbatim:
//!
//! ```text
//! Galois Field : GF(2)[x] / x^8 + x^4 + x^3 + x^2 + 1
//! ```
//!
//! and its coefficients are **two-digit hex bytes**, not decimal. Those two facts are one defect
//! apart rather than two: 100 of the 256 bytes have an all-decimal spelling, so relaxing the header
//! check without also switching the base would turn a loud `BadHeader` into a system built from
//! different field elements than the published one (#414). [`MqField::radix`] is therefore not a
//! rendering choice — it is part of reading the file correctly.
//!
//! The upside is larger than the defect. Because the header *names the modulus*, the importer can
//! **verify** it against the coefficient type rather than assume one, which is what
//! [`MqInstance::check_coefficient_field`] does: the challenge's `x^8 + x^4 + x^3 + x^2 + 1` is not
//! the AES modulus, and `fields::Gf256` is refused for a challenge file where `fields::Gf256Mq` is
//! accepted. Nothing about a system built under the wrong one of the two looks wrong.
//!
//! **The layout is every monomial of degree at most two, in descending grevlex order.** That is
//! what the file's own `Order` header says, and this module implements it by sorting with
//! [`MonomialOrder::GradedReverseLexicographic`] rather than by a hand-rolled index loop — a loop
//! that happened to agree would be a coincidence nobody could check, and
//! [`tests::test_the_layout_is_descending_grevlex`] pins the agreement both ways.
//!
//! It was also *verified* rather than assumed: four candidate layouts were evaluated at a
//! published answer, and exactly one makes all `m` polynomials vanish. That check is the
//! committed test [`tests::test_a_published_instance_is_reproduced`], because a monomial-order
//! translation error is the failure mode an importer has, and it is silent.
//!
//! # A quirk worth knowing
//!
//! **Coefficients are uniform over `0..=31`, not `0..=30`.** `31` appears literally in the
//! published files and is congruent to zero. Counted over type-III `n=10` seed 0: residue 0 occurs
//! 86 times across the 1,320 coefficients and every other residue about 40 times — so **zero is
//! twice as likely as any other coefficient** in the published data. Not a defect to correct, but
//! the kind of thing that should be recorded rather than rediscovered, and the parser accepts
//! `0..=p` and reduces rather than rejecting `p` as out of range.
//!
//! # Runtime `n` against `const N`
//!
//! [`MultivariatePolynomial`] takes its variable count as a const generic, so an instance whose
//! `n` is known only at runtime cannot be handed to a generic function without choosing a
//! compiled `N`. [`MqInstance::dispatch`] does that for a **documented finite set** — the toy
//! sizes 10, 15 and 20 — and returns [`MqError::UnsupportedDimension`] otherwise. The polynomial
//! type system is not redesigned, and an unsupported size is an error rather than a panic.

use std::fmt::{Display, Formatter};

use crate::{KnownOrder, Monomial, MonomialOrder, MultivariatePolynomial};

/// Which base field an instance is over.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum MqField {
    /// Types I and IV. Importable, over `fields::Zp2`.
    ///
    /// The order alone settles the field — there is one field of order two — so unlike
    /// [`Self::Gf256`] there is no modulus to check. `docs/research/boolean-solving.md` §8 decided
    /// the representation is `Zp2` (`PrimeFieldElement32<2>`) rather than
    /// `BinaryFieldElement<0b11>`, on storage rather than behaviour, and
    /// `tests/boolean_readiness.rs::gf2_by_either_route_is_one_field_at_twice_the_storage` pins
    /// the two as one field at twice the storage.
    ///
    /// Type I publishes toy sizes `n = 10, 15, 20` and type IV `n = 5, 10, 15` — which is why
    /// [`SUPPORTED_DIMENSIONS`] carries 5. **Field equations belong in the ideal here**: over
    /// GF(2) `x_i^2 - x_i` has degree 2, so `grobner::field_equations` is cheap and a solving
    /// degree stated without it is not comparable to any published figure.
    Gf2,

    /// Types II and V. Importable, and the modulus is **checked** rather than assumed.
    ///
    /// The challenge's own GF(2^8) — `x^8 + x^4 + x^3 + x^2 + 1`, which is **not** the AES modulus
    /// `fields::Gf256` uses — is `fields::Gf256Mq`. Reading these coefficient bytes under the wrong
    /// one of the two builds a different system from the published one and nothing about the result
    /// looks wrong, so [`MqInstance::check_coefficient_field`] refuses a coefficient type whose
    /// modulus is not the one the file's header states. See [`MqField::PUBLISHED_GF256_MODULUS`].
    Gf256,

    /// Types III and VI. `PrimeFieldElement64<31>`, which already exists — no new arithmetic is a
    /// prerequisite for this importer, and a compact 32-bit field is an independent optimization.
    Gf31,
}

impl MqField {
    /// The modulus the challenge publishes for GF(2^8), as a bit pattern over GF(2).
    ///
    /// `x^8 + x^4 + x^3 + x^2 + 1`. Verified by evaluation rather than taken from prose: all 20
    /// polynomials of type II `n = 10` seed 0 vanish at its published answer under this modulus and
    /// **0 of 20** vanish under the AES `0x11B` — asserted by
    /// [`tests::test_the_published_answer_vanishes_only_under_the_challenges_modulus`]. See
    /// `docs/research/fukuoka-mq.md` §2.4.
    pub const PUBLISHED_GF256_MODULUS: u64 = 0x11D;

    /// The field's order.
    pub fn order(&self) -> u64 {
        match self {
            Self::Gf2 => 2,
            Self::Gf256 => 256,
            Self::Gf31 => 31,
        }
    }

    /// The base this field's elements are written in, in both the instance and the answer file.
    ///
    /// GF(2^8) publishes bytes as two hex digits — coefficient rows and answer vectors alike
    /// (`[a3, 67, 64, ...]`) — and the prime-field types publish decimal. `format.html`, every
    /// genuine instance file and every `-answer` file agree; the hex is not a rendering choice this
    /// crate makes, so it is not optional to read. A decimal read of a hex byte does not fail, it
    /// succeeds at a different element.
    ///
    /// GF(2) is 10 only because `0` and `1` are the same in every base.
    pub fn radix(&self) -> u32 {
        match self {
            Self::Gf2 | Self::Gf31 => 10,
            Self::Gf256 => 16,
        }
    }

    /// The largest coefficient token this field admits, inclusive.
    ///
    /// `q` rather than `q - 1` over a prime field: `31` occurs literally in the published GF(31)
    /// files and is congruent to zero (see the module docs). A binary field has no analogous wrap —
    /// its coefficients are bytes written as exactly two hex digits — so there `q - 1` is the
    /// ceiling and `100` is a malformed token rather than a reducible one.
    pub fn max_coefficient(&self) -> u64 {
        match self {
            Self::Gf2 | Self::Gf31 => self.order(),
            Self::Gf256 => self.order() - 1,
        }
    }

    /// The `Galois Field :` header value, as a field and whatever modulus the header states.
    ///
    /// Three spellings occur. `GF(31)` and `GF(2)` name a prime field and state no modulus. A
    /// binary field is spelled as the quotient ring it is — `GF(2)[x] / x^8 + x^4 + x^3 + x^2 + 1`,
    /// which is what every genuine type II and type V file prints — and the stated polynomial is
    /// returned so that it can be checked against the coefficient type rather than assumed.
    /// `GF(256)` and `GF(2^8)` are accepted as the field with no modulus stated, since a file that
    /// names the field without naming its modulus can still only mean the published one.
    fn parse_header(value: &str) -> Option<(Self, Option<u64>)> {
        let value = value.trim();
        if let Some((ring, modulus)) = value.split_once('/') {
            if ring.trim() != "GF(2)[x]" {
                return None;
            }
            let modulus = parse_gf2_polynomial(modulus)?;
            // The modulus' degree is the extension degree, so it decides which field this is.
            let field = match 63 - modulus.leading_zeros() {
                1 => Self::Gf2,
                8 => Self::Gf256,
                _ => return None,
            };
            return Some((field, Some(modulus)));
        }
        match value {
            "GF(2)" => Some((Self::Gf2, None)),
            "GF(256)" | "GF(2^8)" => Some((Self::Gf256, None)),
            "GF(31)" => Some((Self::Gf31, None)),
            _ => None,
        }
    }
}

/// The irreducible polynomial `F` reduces modulo, as a bit pattern, if that is derivable.
///
/// Derived from arithmetic rather than read off a type parameter, because the modulus of
/// `fields::BinaryFieldElement<P>` is a const generic and no trait exposes it. In a binary field
/// `KnownOrder::element_at` enumerates by bit pattern, so index `2` is `x`, and `x^m` is the
/// modulus with its leading term dropped — which is the *defining relation* of the quotient ring,
/// and the only thing that distinguishes two irreducible polynomials of the same degree.
///
/// `None` rather than a guess whenever that derivation does not apply: a field of odd
/// characteristic, an order that is not a power of two, one wide enough that the index search is
/// not worth running, or an enumeration that is not the bit pattern. Every one of those makes the
/// caller refuse the import, which is the safe direction — the failure this exists to prevent is a
/// coefficient read under the wrong modulus, not a refused one.
fn binary_modulus_of<F: KnownOrder>() -> Option<u64> {
    if F::characteristic_limbs() != [2] {
        return None;
    }
    let order = u64::try_from(F::order_u128()?).ok()?;
    // 2^16 bounds the search at 65536 element constructions. Every binary field this importer
    // reaches is GF(2^8); a wider one would need the modulus exposed rather than derived.
    if !order.is_power_of_two() || !(4..=1 << 16).contains(&order) {
        return None;
    }
    let degree = u128::from(order.trailing_zeros());
    let reduced = F::element_at(2)?.pow(degree);
    let tail = (0..u128::from(order)).find(|&i| F::element_at(i).as_ref() == Some(&reduced))?;
    Some(order | u64::try_from(tail).ok()?)
}

/// A polynomial over GF(2) written as `x^8 + x^4 + x^3 + x^2 + 1`, as a bit pattern.
///
/// Returns `None` on anything it does not fully understand, including a repeated term: a header
/// this cannot read in full is a header to report, not one to read approximately.
fn parse_gf2_polynomial(text: &str) -> Option<u64> {
    let mut bits = 0u64;
    for term in text.split('+') {
        let exponent = match term.trim() {
            "1" => 0,
            "x" => 1,
            term => term.strip_prefix("x^")?.trim().parse::<u32>().ok()?,
        };
        if exponent >= 64 || bits & (1 << exponent) != 0 {
            return None;
        }
        bits |= 1 << exponent;
    }
    (bits != 0).then_some(bits)
}

impl Display for MqField {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Gf2 => write!(f, "GF(2)"),
            Self::Gf256 => write!(f, "GF(2^8)"),
            Self::Gf31 => write!(f, "GF(31)"),
        }
    }
}

/// Why an instance could not be imported.
///
/// Every variant names something specific about the input or about this crate's current reach.
/// None of them is a panic: a malformed or oversized challenge file is a thing to report.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum MqError {
    /// A required header line is absent.
    MissingHeader { key: &'static str },

    /// A header's value does not parse.
    BadHeader { key: &'static str, value: String },

    /// The coefficient type is not the field the instance declares.
    ///
    /// **The check that keeps an import faithful.** A GF(31) instance built over GF(7) is a
    /// different mathematical problem — every coefficient silently reduced modulo seven — and its
    /// solutions and Gröbner behaviour cannot be attributed to the challenge. Nothing about the
    /// resulting system looks wrong, which is exactly why this is an error and not a convention.
    WrongCoefficientField {
        /// The order the instance's header declares.
        declared: u64,
        /// The coefficient type's order, as limbs. A wide field is not representable as one `u64`.
        coefficient_field: Vec<u64>,
    },

    /// The coefficient type has the declared order but reduces modulo a different polynomial.
    ///
    /// The GF(2^8) analogue of [`Self::WrongCoefficientField`], and the sharper of the two: the
    /// challenge's `x^8 + x^4 + x^3 + x^2 + 1` and the AES `x^8 + x^4 + x^3 + x + 1` give
    /// isomorphic fields of the same order, so no order comparison separates them, and a system
    /// built under the wrong one is a different system whose coefficients all look plausible.
    WrongModulus {
        /// The irreducible polynomial the instance's header states, as a bit pattern.
        declared: u64,
        /// The one the coefficient type reduces modulo, as a bit pattern.
        coefficient_field: u64,
    },

    /// A coefficient line has the wrong length for the declared `n`.
    ///
    /// The check that catches a truncated download and a misread `n` at once, which is why it
    /// carries both numbers rather than just complaining.
    WrongCoefficientCount {
        polynomial: usize,
        found: usize,
        expected: usize,
    },

    /// A coefficient is not an integer in `0..=q`.
    BadCoefficient {
        polynomial: usize,
        position: usize,
        token: String,
    },

    /// The file declares `m` polynomials and carries a different number.
    WrongPolynomialCount { found: usize, expected: usize },

    /// The instance's `n` is not one of the compiled dimensions.
    ///
    /// Not a defect in the instance. See the module docs on `const N`.
    UnsupportedDimension {
        variables: usize,
        supported: &'static [usize],
    },

    /// A system was requested at a dimension the instance is not in.
    DimensionMismatch { requested: usize, instance: usize },

    /// An answer-file element is not a value of the declared field, read in the declared base.
    ///
    /// Carries the token verbatim, because the interesting failure is a GF(2^8) byte read as
    /// decimal — which does not look wrong, it looks like a different element.
    BadAnswerValue { position: usize, token: String },

    /// The answer file carries a different number of coordinates than the instance has variables.
    ///
    /// The check that distinguishes a truncated download from a good one. Without it a short
    /// vector is returned as an answer, and the solution check it exists to perform silently
    /// compares the wrong number of coordinates.
    WrongAnswerCount { found: usize, expected: usize },
}

impl Display for MqError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MissingHeader { key } => write!(f, "the header has no `{}` line", key),
            Self::BadHeader { key, value } => {
                write!(f, "the `{}` header does not parse: {:?}", key, value)
            }
            Self::WrongCoefficientField {
                declared,
                coefficient_field,
            } => write!(
                f,
                "the instance is over GF({}) and the coefficient type has order {:?}",
                declared, coefficient_field
            ),
            Self::WrongModulus {
                declared,
                coefficient_field,
            } => write!(
                f,
                "the instance reduces modulo {:#x} and the coefficient type modulo {:#x}",
                declared, coefficient_field
            ),
            Self::WrongCoefficientCount {
                polynomial,
                found,
                expected,
            } => write!(
                f,
                "polynomial {} has {} coefficients, expected {} for the declared variable count",
                polynomial, found, expected
            ),
            Self::BadCoefficient {
                polynomial,
                position,
                token,
            } => write!(
                f,
                "polynomial {} has {:?} at position {}, which is not a field element",
                polynomial, token, position
            ),
            Self::WrongPolynomialCount { found, expected } => write!(
                f,
                "the file declares {} polynomials and carries {}",
                expected, found
            ),
            Self::UnsupportedDimension {
                variables,
                supported,
            } => write!(
                f,
                "{} variables is not a compiled dimension; this build supports {:?}",
                variables, supported
            ),
            Self::DimensionMismatch {
                requested,
                instance,
            } => write!(
                f,
                "the instance has {} variables and a system was requested at {}",
                instance, requested
            ),
            Self::BadAnswerValue { position, token } => write!(
                f,
                "answer coordinate {} is {:?}, which is not an element of the declared field \
                 written in the base that field publishes",
                position, token
            ),
            Self::WrongAnswerCount { found, expected } => write!(
                f,
                "the answer file has {} coordinates and the instance has {} variables",
                found, expected
            ),
        }
    }
}

impl std::error::Error for MqError {}

/// Variable counts this build can turn into polynomials.
///
/// Every published toy-example size plus **24**, which is where the real challenge starts in a type
/// this crate can import: both signature families publish `m = 16..=35`, the generator computes
/// `n = m * 1.5`, and `m = 16` therefore gives `n = 24`. So one arm serves two fields — type VI over
/// GF(31) and type V over GF(2^8). Below it every importable instance is a toy example published so
/// an implementation can check itself.
///
/// **The toy sizes are not the same per type** and the union is `{5, 10, 15, 20}`: types I, II and
/// III publish `n = 10, 15, 20`, and types IV, V and VI publish `n = 5, 10, 15`. `5` is here for
/// the signature families' smallest toy, which carries only `m = 3` polynomials in 5 unknowns.
///
/// The list stops there rather than covering the published ranges. Type III's real range is
/// `n = 34..=53` and type I's is `n = 55..=100`, both far past anything the solvers reach; compiling
/// a dimension that cannot be used would be worse than
/// [`MqError::UnsupportedDimension`](MqError::UnsupportedDimension) naming it. Each entry costs a
/// monomorphization of the whole multivariate stack at that `N`.
pub const SUPPORTED_DIMENSIONS: &[usize] = &[5, 10, 15, 20, 24];

/// A parsed instance, before a compile-time dimension is chosen.
///
/// Holds exactly what the file says, with the coefficients **unreduced and in file order**. Nothing
/// is interpreted until [`Self::system`] or [`Self::dispatch`], so a round-trip through this type
/// is lossless against the source and a checksum over it means something.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MqInstance {
    /// The base field.
    pub field: MqField,

    /// The irreducible polynomial the `Galois Field :` header states, as a bit pattern over GF(2).
    ///
    /// `None` for a prime field, and also for a binary field whose header names only the field
    /// (`GF(2^8)`). Where it is present it is **what the file says**, not what this crate expects:
    /// a file declaring the AES modulus parses and records the AES modulus, and it is
    /// [`Self::check_coefficient_field`] that decides whether a coefficient type matches it.
    pub modulus: Option<u64>,

    /// `n`.
    pub variables: usize,

    /// `m`.
    pub polynomials: usize,

    /// The generator seed, if the header has one.
    pub seed: Option<u64>,

    /// The `Order :` header, verbatim. Kept as text rather than parsed into a
    /// [`MonomialOrder`]: it is provenance, and a mismatch with what this module implements should
    /// be visible rather than silently normalized.
    pub order: String,

    /// One coefficient vector per polynomial, in file order, **unreduced**.
    pub coefficients: Vec<Vec<u64>>,
}

impl MqInstance {
    /// Coefficients per polynomial for `n` variables: every monomial of degree at most two.
    ///
    /// `n(n+1)/2` quadratic, `n` linear, one constant.
    pub fn coefficients_per_polynomial(variables: usize) -> usize {
        variables * (variables + 1) / 2 + variables + 1
    }

    /// Parse a published challenge or toy-example file.
    ///
    /// Strict: every header this relies on must be present and parse, every coefficient line must
    /// have exactly the length `n` implies, and the number of lines must match `m`. A silently
    /// truncated download is the failure this is strict against.
    ///
    /// # Errors
    /// [`MqError`], naming the line and position wherever the input is at fault.
    pub fn parse(text: &str) -> Result<Self, MqError> {
        let mut field: Option<MqField> = None;
        let mut modulus: Option<u64> = None;
        let mut variables: Option<usize> = None;
        let mut polynomials: Option<usize> = None;
        let mut seed: Option<u64> = None;
        let mut order: Option<String> = None;
        let mut coefficients: Vec<Vec<u64>> = Vec::new();

        for line in text.lines() {
            let line = line.trim();
            if line.is_empty() || line.starts_with('*') {
                continue;
            }

            // A coefficient row, not a header: headers never end in a semicolon.
            if let Some(body) = line.strip_suffix(';') {
                let n = variables.ok_or(MqError::MissingHeader {
                    key: "Number of variables (n)",
                })?;
                let expected = Self::coefficients_per_polynomial(n);
                let index = coefficients.len();
                let mut row = Vec::with_capacity(expected);
                let field = field.ok_or(MqError::MissingHeader {
                    key: "Galois Field",
                })?;
                // Base 16 over GF(2^8), base 10 over a prime field. The header decides, and it is
                // read before any coefficient row because a coefficient row cannot say.
                let radix = field.radix();
                let largest = field.max_coefficient();
                for (position, token) in body.split_whitespace().enumerate() {
                    let value =
                        u64::from_str_radix(token, radix).map_err(|_| MqError::BadCoefficient {
                            polynomial: index,
                            position,
                            token: token.to_string(),
                        })?;
                    if value > largest {
                        return Err(MqError::BadCoefficient {
                            polynomial: index,
                            position,
                            token: token.to_string(),
                        });
                    }
                    row.push(value);
                }
                if row.len() != expected {
                    return Err(MqError::WrongCoefficientCount {
                        polynomial: index,
                        found: row.len(),
                        expected,
                    });
                }
                coefficients.push(row);
                continue;
            }

            let Some((key, value)) = line.split_once(':') else {
                continue;
            };
            match key.trim() {
                "Galois Field" => {
                    let (parsed, stated) =
                        MqField::parse_header(value).ok_or_else(|| MqError::BadHeader {
                            key: "Galois Field",
                            value: value.trim().to_string(),
                        })?;
                    field = Some(parsed);
                    modulus = stated;
                }
                "Number of variables (n)" => {
                    variables = Some(value.trim().parse().map_err(|_| MqError::BadHeader {
                        key: "Number of variables (n)",
                        value: value.trim().to_string(),
                    })?)
                }
                "Number of polynomials (m)" => {
                    polynomials = Some(value.trim().parse().map_err(|_| MqError::BadHeader {
                        key: "Number of polynomials (m)",
                        value: value.trim().to_string(),
                    })?)
                }
                "Seed" => seed = value.trim().parse().ok(),
                "Order" => order = Some(value.trim().to_string()),
                _ => {}
            }
        }

        let field = field.ok_or(MqError::MissingHeader {
            key: "Galois Field",
        })?;
        let variables = variables.ok_or(MqError::MissingHeader {
            key: "Number of variables (n)",
        })?;
        let polynomials = polynomials.ok_or(MqError::MissingHeader {
            key: "Number of polynomials (m)",
        })?;
        if coefficients.len() != polynomials {
            return Err(MqError::WrongPolynomialCount {
                found: coefficients.len(),
                expected: polynomials,
            });
        }

        Ok(Self {
            field,
            modulus,
            variables,
            polynomials,
            seed,
            order: order.unwrap_or_default(),
            coefficients,
        })
    }

    /// Parse the companion `-answer` file: the published solution, if there is one.
    ///
    /// `[22, 22, 28, ...]` over GF(31), `[a3, 67, 64, ...]` over GF(2^8). Returned as integers
    /// rather than field elements, so that the caller chooses the coefficient type and the parse
    /// stays independent of it.
    ///
    /// **A method, and fallible, because the field decides the base.** This cannot be
    /// field-agnostic: a GF(2^8) element is a hex byte and 100 of the 256 of them have an
    /// all-decimal spelling, so a decimal read of one does not fail — it succeeds at a different
    /// element (#415). Nor can it drop what it cannot read: the published answer is the cheapest
    /// available check on an importer, one evaluation per polynomial, and a check that silently
    /// shortened its own input would report a correct importer as broken or an incorrect one as
    /// fine depending on which way the garbage fell.
    pub fn parse_answer(&self, text: &str) -> Result<Vec<u64>, MqError> {
        let radix = self.field.radix();
        let order = self.field.order();
        let mut values = Vec::with_capacity(self.variables);
        for token in text
            .split(|c: char| !c.is_ascii_alphanumeric())
            .filter(|t| !t.is_empty())
        {
            let value = u64::from_str_radix(token, radix).map_err(|_| MqError::BadAnswerValue {
                position: values.len(),
                token: token.to_string(),
            })?;
            if value >= order {
                return Err(MqError::BadAnswerValue {
                    position: values.len(),
                    token: token.to_string(),
                });
            }
            values.push(value);
        }
        if values.len() != self.variables {
            return Err(MqError::WrongAnswerCount {
                found: values.len(),
                expected: self.variables,
            });
        }
        Ok(values)
    }

    /// Whether `F` is the field the instance's header declares.
    ///
    /// Two questions, and both have to be answered before a single coefficient is converted.
    /// First, whether the coefficient type the caller supplied *is* the declared field, which is
    /// the one a generic `F: FiniteField` signature cannot ask and so cannot enforce. Second, over
    /// GF(2^8), whether it reduces modulo the polynomial the file's header states — and that
    /// question is *not* answered by the first, because the challenge's modulus and the AES one
    /// give fields of the same order.
    ///
    /// **The order alone settles GF(2) and GF(31), and does not settle GF(2^8).** There is one
    /// field of order 2 and one of order 31, so a type of that order is that field however it is
    /// implemented; `x + 1` is the only irreducible of degree one, so `Zp2` and
    /// `BinaryFieldElement<0b11>` are checked identically here. Which of the two the importer
    /// *should* be handed is a storage question decided in
    /// `docs/research/boolean-solving.md` §8 — `Zp2`, at half the size — and not a correctness
    /// question this check can or should enforce.
    ///
    /// Orders are compared as limb slices rather than as integers, because a field order need not
    /// fit a `u64` — the comparison has to be correct for the wide fields M20 added, not only for
    /// the ones this importer currently reaches.
    ///
    /// # Errors
    /// [`MqError::WrongCoefficientField`] or [`MqError::WrongModulus`].
    pub fn check_coefficient_field<F: KnownOrder>(&self) -> Result<(), MqError> {
        let declared = self.field.order();
        if F::order_limbs() != [declared] {
            return Err(MqError::WrongCoefficientField {
                declared,
                coefficient_field: F::order_limbs().to_vec(),
            });
        }

        if self.field == MqField::Gf256 {
            // A header that names the field without naming its modulus can still only mean the
            // published one; a header that names a modulus is believed over this crate's
            // expectation, which is what makes the check a verification rather than an assertion.
            let declared = self.modulus.unwrap_or(MqField::PUBLISHED_GF256_MODULUS);
            let found = binary_modulus_of::<F>().ok_or(MqError::WrongCoefficientField {
                declared: self.field.order(),
                coefficient_field: F::order_limbs().to_vec(),
            })?;
            if found != declared {
                return Err(MqError::WrongModulus {
                    declared,
                    coefficient_field: found,
                });
            }
        }
        Ok(())
    }

    /// Every monomial of degree at most two in `N` variables, descending grevlex.
    ///
    /// The file's coefficient layout, derived from the order the file names rather than
    /// reimplemented as an index pattern.
    pub fn monomial_layout<const N: usize>() -> Vec<Monomial<N>> {
        let mut monomials = Vec::with_capacity(Self::coefficients_per_polynomial(N));
        monomials.push(Monomial::one());
        for i in 0..N {
            monomials.push(Monomial::univariate(i, 1));
        }
        for i in 0..N {
            for j in i..N {
                let mut exponents = [0u32; N];
                exponents[i] += 1;
                exponents[j] += 1;
                monomials.push(Monomial::new(&exponents));
            }
        }
        let order = MonomialOrder::GradedReverseLexicographic;
        monomials.sort_by(|a, b| order.cmp(b, a));
        monomials
    }

    /// The polynomial system, at a compile-time dimension and over the field the file declares.
    ///
    /// `F: KnownOrder` rather than `F: FiniteField`, and that bound is the point: a field whose
    /// order cannot be read cannot be checked against the instance's header, and an unchecked
    /// coefficient type silently reduces every coefficient into the wrong field. See
    /// [`MqError::WrongCoefficientField`].
    ///
    /// # Errors
    /// [`MqError::DimensionMismatch`] if `N` is not the instance's `n`;
    /// [`MqError::WrongCoefficientField`] if `F` is not that field.
    pub fn system<const N: usize, F: KnownOrder>(
        &self,
    ) -> Result<Vec<MultivariatePolynomial<N, F>>, MqError> {
        if N != self.variables {
            return Err(MqError::DimensionMismatch {
                requested: N,
                instance: self.variables,
            });
        }
        self.check_coefficient_field::<F>()?;

        let layout = Self::monomial_layout::<N>();
        let mut system = Vec::with_capacity(self.coefficients.len());
        for (polynomial, row) in self.coefficients.iter().enumerate() {
            let mut terms: Vec<(Monomial<N>, F)> = Vec::with_capacity(layout.len());
            for (position, (monomial, coefficient)) in layout.iter().zip(row).enumerate() {
                let element =
                    self.element::<F>(*coefficient)
                        .ok_or_else(|| MqError::BadCoefficient {
                            polynomial,
                            position,
                            token: self.render_coefficient(*coefficient),
                        })?;
                terms.push((*monomial, element));
            }
            // Through `new`, which drops the terms whose coefficients are zero — and `31` over
            // GF(31) is one of those.
            system.push(MultivariatePolynomial::new(&terms));
        }
        Ok(system)
    }

    /// One value from this instance's file as a field element, or `None` if it is not one.
    ///
    /// Public because a *coefficient* is not the only thing a file holds: an answer vector is
    /// parsed by [`Self::parse_answer`] into the same `u64` tokens, and a consumer that is generic
    /// over the coefficient type — the scoreboard's MQ visitors are, since #510 — has no other way
    /// to read one at the field the header names.
    ///
    /// **Not `FiniteField::new`, which over an extension is the prime-subfield embedding.**
    /// `Gf256Mq::new(0xa7)` is `1`, so a byte-wise read through `new` collapses every coefficient
    /// of a GF(2^8) instance to a bit and builds a system with the right shape and the wrong
    /// contents. [`KnownOrder::element_at`] is the bijection onto the field, and for a binary field
    /// it is the bit pattern the file writes.
    ///
    /// A prime field still goes through `new`, because the published GF(31) files carry the literal
    /// token `31` — congruent to zero, and so outside `element_at`'s `0..q`.
    pub fn element<F: KnownOrder>(&self, value: u64) -> Option<F> {
        match self.field {
            MqField::Gf2 | MqField::Gf31 => Some(F::new(value)),
            MqField::Gf256 => F::element_at(u128::from(value)),
        }
    }

    /// A coefficient rendered in the base the file writes it in, for an error message.
    fn render_coefficient(&self, value: u64) -> String {
        match self.field.radix() {
            16 => format!("{:02x}", value),
            _ => value.to_string(),
        }
    }

    /// Hand the instance's system to `visitor` at whichever compiled dimension it needs.
    ///
    /// The `const N` bridge. See [`SUPPORTED_DIMENSIONS`].
    ///
    /// # Errors
    /// [`MqError::UnsupportedDimension`] if `n` is not compiled in, plus whatever
    /// [`Self::system`] reports.
    pub fn dispatch<F: KnownOrder, V: MqVisitor<F>>(
        &self,
        visitor: V,
    ) -> Result<V::Output, MqError> {
        match self.variables {
            5 => Ok(visitor.visit(&self.system::<5, F>()?)),
            10 => Ok(visitor.visit(&self.system::<10, F>()?)),
            15 => Ok(visitor.visit(&self.system::<15, F>()?)),
            20 => Ok(visitor.visit(&self.system::<20, F>()?)),
            24 => Ok(visitor.visit(&self.system::<24, F>()?)),
            variables => Err(MqError::UnsupportedDimension {
                variables,
                supported: SUPPORTED_DIMENSIONS,
            }),
        }
    }
}

impl Display for MqInstance {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{} instance: {} polynomials in {} variables",
            self.field, self.polynomials, self.variables
        )?;
        if let Some(seed) = self.seed {
            write!(f, ", seed {}", seed)?;
        }
        Ok(())
    }
}

/// Something to do with an instance's system once its dimension is known.
///
/// A visitor rather than a returned system, because the dimension is a type parameter and a
/// function cannot return `Vec<MultivariatePolynomial<N, F>>` for an `N` chosen at runtime. The
/// visitor's `Output` can be anything that does not mention `N` — a solution's coordinates as a
/// `Vec`, a verdict, a measurement.
pub trait MqVisitor<F: KnownOrder> {
    /// What the visit produces. Must not mention the dimension.
    type Output;

    /// Called once, with the instance's system at its own dimension.
    fn visit<const N: usize>(self, system: &[MultivariatePolynomial<N, F>]) -> Self::Output;
}

#[cfg(test)]
mod tests {
    use super::{
        parse_gf2_polynomial, MqError, MqField, MqInstance, MqVisitor, SUPPORTED_DIMENSIONS,
    };
    use crate::{
        fields::{Gf256, Gf256Mq, PrimeFieldElement64, Zp2},
        FiniteField, Monomial, MonomialOrder, MultivariatePolynomial, One, Zero,
    };

    type F = PrimeFieldElement64<31>;

    /// A hand-written instance in the published format, with a known solution.
    ///
    /// Not challenge data: the Fukuoka files are "All Rights Reserved" and are not redistributed
    /// here (see `docs/research/fukuoka-mq.md`), so the parser's unconditional coverage comes from
    /// a system written for the purpose. Three variables, so the layout is
    /// `3*4/2 + 3 + 1 = 10` coefficients: descending grevlex gives
    /// `x0^2, x0x1, x1^2, x0x2, x1x2, x2^2, x0, x1, x2, 1`.
    ///
    /// `x0 = 1, x1 = 2, x2 = 3` is a solution of both polynomials:
    ///   `x0*x1 - x2 + 1  = 2 - 3 + 1 = 0`
    ///   `x2^2 - x1^2 - 5 = 9 - 4 - 5 = 0`
    const FIXTURE: &str = "\
Galois Field : GF(31)
Number of variables (n) : 3
Number of polynomials (m) : 2
Seed : 7
Order : graded reverse lex order

*********************
0 1 0 0 0 0 0 0 30 1 ;
0 0 30 0 0 1 0 0 0 26 ;
";

    /// A hand-written GF(2^8) instance with the header a genuine type II or V file prints.
    ///
    /// Not challenge data, for the reason [`FIXTURE`] gives. Three variables, so the ten
    /// coefficients are `x0^2, x0x1, x1^2, x0x2, x1x2, x2^2, x0, x1, x2, 1` descending grevlex, and
    /// every one of them is a **two-digit hex byte**.
    ///
    /// Built to separate the two moduli and the two bases at once. At
    /// `(x0, x1, x2) = (de, ad, be)`:
    ///   `a7*x0x1 + x2^2 + 14    = 0` under `x^8+x^4+x^3+x^2+1`, and `61` under the AES modulus.
    ///   `13*x0^2 + x1x2 + x0 + 21 = 0` under it, and `a9` under AES.
    /// `13` is the all-decimal hex token: read as decimal thirteen rather than as `0x13`, the
    /// second polynomial leaves `1c` at the same point.
    const GF256_FIXTURE: &str = "\
Galois Field : GF(2)[x] / x^8 + x^4 + x^3 + x^2 + 1
Number of variables (n) : 3
Number of polynomials (m) : 2
Seed : 0
Order : graded reverse lex order

*********************
00 a7 00 00 00 01 00 00 00 14 ;
13 00 00 00 01 00 01 00 00 21 ;
";

    /// [`GF256_FIXTURE`]'s solution, in the form an `-answer` file publishes.
    const GF256_ANSWER: &str = "[de, ad, be]\n";

    /// The layout is descending grevlex over all monomials of degree at most two.
    ///
    /// Asserted both ways: the enumeration is sorted, and the sort is what the file's `Order`
    /// header names. A hand-rolled index loop that happened to agree would be a coincidence, and
    /// this is what makes the agreement checkable.
    #[test]
    fn test_the_layout_is_descending_grevlex() {
        let layout = MqInstance::monomial_layout::<4>();
        assert_eq!(layout.len(), MqInstance::coefficients_per_polynomial(4));
        assert_eq!(layout.len(), 4 * 5 / 2 + 4 + 1);

        // Strictly descending under the order the file declares.
        let order = MonomialOrder::GradedReverseLexicographic;
        for pair in layout.windows(2) {
            assert_eq!(
                order.cmp(&pair[0], &pair[1]),
                std::cmp::Ordering::Greater,
                "{:?} should be greater than {:?}",
                pair[0].exponents(),
                pair[1].exponents()
            );
        }

        // Graded, so the quadratics come first, then the linears, then the constant.
        assert_eq!(layout[0], Monomial::new(&[2, 0, 0, 0]));
        assert_eq!(layout[1], Monomial::new(&[1, 1, 0, 0]));
        assert_eq!(layout[2], Monomial::new(&[0, 2, 0, 0]));
        assert_eq!(layout[3], Monomial::new(&[1, 0, 1, 0]));
        assert_eq!(layout[layout.len() - 1], Monomial::one());
        assert_eq!(layout[layout.len() - 2], Monomial::univariate(3, 1));
    }

    /// The header and every coefficient row are read exactly as written.
    #[test]
    fn test_parsing_the_header_and_rows() {
        let instance = MqInstance::parse(FIXTURE).expect("the fixture parses");
        assert_eq!(instance.field, MqField::Gf31);
        assert_eq!(instance.variables, 3);
        assert_eq!(instance.polynomials, 2);
        assert_eq!(instance.seed, Some(7));
        assert_eq!(instance.order, "graded reverse lex order");
        assert_eq!(instance.coefficients.len(), 2);
        assert_eq!(instance.coefficients[0].len(), 10);
        // Unreduced and in file order, so the parse is lossless against the source.
        assert_eq!(
            instance.coefficients[0],
            vec![0, 1, 0, 0, 0, 0, 0, 0, 30, 1]
        );
        assert_eq!(
            instance.to_string(),
            "GF(31) instance: 2 polynomials in 3 variables, seed 7"
        );
    }

    /// The reconstructed polynomials vanish at the known solution.
    ///
    /// The check that catches a monomial-order translation error, which is the failure mode an
    /// importer has and the only one that is completely silent.
    #[test]
    fn test_the_reconstructed_system_vanishes_at_its_solution() {
        let instance = MqInstance::parse(FIXTURE).expect("parses");
        let system = instance.system::<3, F>().expect("GF(31) at n = 3");
        assert_eq!(system.len(), 2);

        let solution = [F::new(1), F::new(2), F::new(3)];
        for (index, p) in system.iter().enumerate() {
            assert!(
                p.eval(&solution).is_zero(),
                "polynomial {} does not vanish at the fixture's solution: {}",
                index,
                p
            );
        }

        // And the reconstruction is the intended polynomial, not merely something vanishing there.
        let expected: Vec<MultivariatePolynomial<3, F>> = ["x*y - z + 1", "z^2 - y^2 - 5"]
            .iter()
            .map(|s| MultivariatePolynomial::parse(s, ["x", "y", "z"]).expect("parses"))
            .collect();
        assert_eq!(system, expected);
    }

    /// A reduced-to-zero coefficient drops out, which is what `31` over GF(31) does.
    #[test]
    fn test_the_field_order_is_a_legal_coefficient_and_means_zero() {
        // `31` in the constant position, where the fixture has 1.
        let text = FIXTURE.replace("0 0 30 0 0 1 0 0 0 26 ;", "0 0 30 0 0 1 0 0 0 31 ;");
        let instance = MqInstance::parse(&text).expect("31 is a legal coefficient");
        assert_eq!(
            instance.coefficients[1][9], 31,
            "kept unreduced in the parse"
        );

        let system = instance.system::<3, F>().expect("builds");
        // z^2 - y^2 + 0, so the constant term is gone rather than present and zero.
        assert_eq!(system[1].terms().len(), 2);

        // 32 is not: the parser is strict above the field order.
        let text = FIXTURE.replace("0 0 30 0 0 1 0 0 0 26 ;", "0 0 30 0 0 1 0 0 0 32 ;");
        assert_eq!(
            MqInstance::parse(&text),
            Err(MqError::BadCoefficient {
                polynomial: 1,
                position: 9,
                token: "32".to_string()
            })
        );
    }

    /// A truncated row, a missing header, and a miscounted `m` are all refused.
    ///
    /// Strictness is the point: a silently truncated download that parsed would produce a
    /// different polynomial system and a wrong answer.
    #[test]
    fn test_malformed_input_is_refused() {
        // One coefficient short.
        let text = FIXTURE.replace("0 1 0 0 0 0 0 0 30 1 ;", "0 1 0 0 0 0 0 0 30 ;");
        assert_eq!(
            MqInstance::parse(&text),
            Err(MqError::WrongCoefficientCount {
                polynomial: 0,
                found: 9,
                expected: 10
            })
        );

        // `m` says two, the file carries one.
        let text = FIXTURE.replace("0 0 30 0 0 1 0 0 0 26 ;\n", "");
        assert_eq!(
            MqInstance::parse(&text),
            Err(MqError::WrongPolynomialCount {
                found: 1,
                expected: 2
            })
        );

        // No field header.
        let text = FIXTURE.replace("Galois Field : GF(31)\n", "");
        assert_eq!(
            MqInstance::parse(&text),
            Err(MqError::MissingHeader {
                key: "Galois Field"
            })
        );

        // An unknown field.
        let text = FIXTURE.replace("GF(31)", "GF(7)");
        assert_eq!(
            MqInstance::parse(&text),
            Err(MqError::BadHeader {
                key: "Galois Field",
                value: "GF(7)".to_string()
            })
        );

        // A non-numeric variable count.
        let text = FIXTURE.replace("(n) : 3", "(n) : many");
        assert!(matches!(
            MqInstance::parse(&text),
            Err(MqError::BadHeader {
                key: "Number of variables (n)",
                ..
            })
        ));
    }

    /// A GF(31) instance refuses to be built over a different field.
    ///
    /// **The defect this test exists for**: `system` was generic over `F: FiniteField` and checked
    /// only that the *header* said GF(31), so a GF(7) coefficient type produced a system with
    /// every coefficient silently reduced modulo seven. A different mathematical problem, whose
    /// solutions and Gröbner behaviour cannot be attributed to the challenge — and nothing about
    /// the result looks wrong, which is what made it worth a type bound rather than a convention.
    #[test]
    fn test_a_mismatched_coefficient_field_is_refused() {
        type Wrong = PrimeFieldElement64<7>;
        type AlsoWrong = PrimeFieldElement64<2147483647>;

        let instance = MqInstance::parse(FIXTURE).expect("parses");

        for error in [
            instance.system::<3, Wrong>().err(),
            instance.system::<3, AlsoWrong>().err(),
            instance.check_coefficient_field::<Wrong>().err(),
        ] {
            match error {
                Some(MqError::WrongCoefficientField {
                    declared,
                    coefficient_field,
                }) => {
                    assert_eq!(declared, 31);
                    assert_ne!(coefficient_field, vec![31]);
                }
                other => panic!("expected a field mismatch, got {:?}", other),
            }
        }

        // The right field builds, and the check agrees.
        assert!(instance.check_coefficient_field::<F>().is_ok());
        assert!(instance.system::<3, F>().is_ok());

        // Dispatch is covered by the same check, so the bridge cannot route around it.
        struct Nothing;
        impl<FF: crate::KnownOrder> MqVisitor<FF> for Nothing {
            type Output = ();
            fn visit<const N: usize>(self, _: &[MultivariatePolynomial<N, FF>]) -> Self::Output {}
        }
        let ten = MqInstance {
            field: MqField::Gf31,
            modulus: None,
            variables: 10,
            polynomials: 1,
            seed: None,
            order: "graded reverse lex order".to_string(),
            coefficients: vec![vec![0; MqInstance::coefficients_per_polynomial(10)]],
        };
        assert!(matches!(
            ten.dispatch::<Wrong, _>(Nothing),
            Err(MqError::WrongCoefficientField { .. })
        ));
        assert!(ten.dispatch::<F, _>(Nothing).is_ok());
    }

    /// A field mismatch is checked *before* the dimension is, so neither error hides the other.
    ///
    /// Order matters for the message a caller sees: a GF(7) request at the wrong `N` should not
    /// report only the dimension and leave the field problem to be discovered later.
    #[test]
    fn test_the_dimension_is_checked_before_the_field() {
        let instance = MqInstance::parse(FIXTURE).expect("parses");
        // Both wrong: the dimension is reported, which is the cheaper and more specific fact.
        assert_eq!(
            instance.system::<4, PrimeFieldElement64<7>>(),
            Err(MqError::DimensionMismatch {
                requested: 4,
                instance: 3
            })
        );
        // Dimension right, field wrong: the field is reported rather than silently accepted.
        assert!(matches!(
            instance.system::<3, PrimeFieldElement64<7>>(),
            Err(MqError::WrongCoefficientField { .. })
        ));
    }

    /// A GF(2) instance builds a system over `Zp2`, and refuses a coefficient type of another order.
    #[test]
    fn test_the_gf2_types_import_under_zp2() {
        // Built rather than parsed: the fixture's coefficients are out of range for GF(2), and
        // what is under test is `system`, not the parse. `x0*x1 + x0 + x1 + 1 = (x0+1)(x1+1)` over
        // GF(2), whose layout at n = 3 is
        // `x0^2, x0x1, x1^2, x0x2, x1x2, x2^2, x0, x1, x2, 1`. Its roots are exactly the points
        // with `x0 = 1` or `x1 = 1`, so one root and one non-root pin the coefficient positions
        // as well as the field.
        let instance = MqInstance {
            field: MqField::Gf2,
            modulus: None,
            variables: 3,
            polynomials: 1,
            seed: None,
            order: "graded reverse lex order".to_string(),
            coefficients: vec![vec![0, 1, 0, 0, 0, 0, 1, 1, 0, 1]],
        };

        let system = instance
            .system::<3, Zp2>()
            .expect("GF(2) imports under Zp2 — the representation #197 decided on");
        assert_eq!(system.len(), 1);
        let root = [Zp2::one(), Zp2::zero(), Zp2::zero()];
        assert!(
            system[0].eval(&root).is_zero(),
            "the GF(2) coefficients were not read as written"
        );
        let non_root = [Zp2::zero(), Zp2::zero(), Zp2::one()];
        assert!(!system[0].eval(&non_root).is_zero());

        // There is only one field of order two, so the order alone settles the field and no
        // modulus check is needed — but a coefficient type of another order is still refused.
        assert!(matches!(
            instance.system::<3, F>(),
            Err(MqError::WrongCoefficientField { declared: 2, .. })
        ));
        assert!(matches!(
            instance.system::<3, Gf256Mq>(),
            Err(MqError::WrongCoefficientField { declared: 2, .. })
        ));
    }

    /// The coefficient range follows the declared field, so GF(2) refuses a GF(31) coefficient.
    ///
    /// Worth its own test because it is the check that catches a file whose header and body
    /// disagree — a mis-filed download, which is otherwise indistinguishable from valid data.
    #[test]
    fn test_the_coefficient_range_follows_the_declared_field() {
        // `30` is in range over GF(31), and over GF(256) where it is read as the byte 0x30.
        assert!(MqInstance::parse(FIXTURE).is_ok());
        assert!(MqInstance::parse(&FIXTURE.replace("GF(31)", "GF(256)")).is_ok());
        assert_eq!(
            MqInstance::parse(&FIXTURE.replace("GF(31)", "GF(2)")),
            Err(MqError::BadCoefficient {
                polynomial: 0,
                position: 8,
                token: "30".to_string()
            })
        );
        // Over GF(2^8) the ceiling is 0xff rather than the order, because a byte has no analogue
        // of the `31` that occurs literally in the GF(31) files.
        assert_eq!(
            MqInstance::parse(&FIXTURE.replace("GF(31)", "GF(2^8)").replace("30", "100")),
            Err(MqError::BadCoefficient {
                polynomial: 0,
                position: 8,
                token: "100".to_string()
            })
        );
    }

    /// A GF(2) polynomial in the header's spelling becomes its bit pattern, or nothing.
    #[test]
    fn test_reading_a_gf2_polynomial_from_the_header() {
        assert_eq!(
            parse_gf2_polynomial(" x^8 + x^4 + x^3 + x^2 + 1 "),
            Some(0x11D)
        );
        assert_eq!(parse_gf2_polynomial("x^8 + x^4 + x^3 + x + 1"), Some(0x11B));
        assert_eq!(parse_gf2_polynomial("x + 1"), Some(0b11));
        assert_eq!(parse_gf2_polynomial("1"), Some(1));
        // A repeated term would cancel over GF(2), so reading it as a set of bits would be wrong.
        assert_eq!(parse_gf2_polynomial("x^8 + x^8 + 1"), None);
        assert_eq!(parse_gf2_polynomial("x^64 + 1"), None);
        assert_eq!(parse_gf2_polynomial("y^8 + 1"), None);
        assert_eq!(parse_gf2_polynomial("2x^8 + 1"), None);
        assert_eq!(parse_gf2_polynomial(""), None);
    }

    /// The genuine GF(2^8) header parses, and the modulus it states is recorded verbatim.
    #[test]
    fn test_the_real_gf256_header_parses_and_records_its_modulus() {
        let instance = MqInstance::parse(GF256_FIXTURE).expect("the real header parses");
        assert_eq!(instance.field, MqField::Gf256);
        assert_eq!(instance.modulus, Some(0x11D));
        assert_eq!(instance.modulus, Some(MqField::PUBLISHED_GF256_MODULUS));

        // What the file says, not what this crate expects: an AES-modulus declaration is a valid
        // GF(2^8) declaration and is recorded as the one it is.
        let aes = MqInstance::parse(
            &GF256_FIXTURE.replace("x^8 + x^4 + x^3 + x^2 + 1", "x^8 + x^4 + x^3 + x + 1"),
        )
        .expect("an AES-modulus header is still a GF(2^8) header");
        assert_eq!(aes.field, MqField::Gf256);
        assert_eq!(aes.modulus, Some(0x11B));

        // A field named without its modulus still parses, and states none.
        let bare = MqInstance::parse(
            &GF256_FIXTURE.replace("GF(2)[x] / x^8 + x^4 + x^3 + x^2 + 1", "GF(2^8)"),
        )
        .expect("`GF(2^8)` parses");
        assert_eq!(bare.field, MqField::Gf256);
        assert_eq!(bare.modulus, None);

        // A header this cannot read in full is reported rather than read approximately.
        assert_eq!(
            MqInstance::parse(&GF256_FIXTURE.replace("x^4 + ", "x^4 * ")),
            Err(MqError::BadHeader {
                key: "Galois Field",
                value: "GF(2)[x] / x^8 + x^4 * x^3 + x^2 + 1".to_string(),
            })
        );
    }

    /// GF(2^8) coefficients are read base 16, so an all-decimal hex token is not read as decimal.
    ///
    /// The half of #414 that would have been silent: of the 256 bytes, 100 have an all-decimal
    /// spelling, so relaxing the header check alone would have built a different system rather
    /// than failing.
    #[test]
    fn test_gf256_coefficients_are_read_base_sixteen() {
        let instance = MqInstance::parse(GF256_FIXTURE).expect("parses");
        // `a7` is not a decimal number at all: a decimal read fails here rather than lying.
        assert_eq!(instance.coefficients[0][1], 0xa7);
        // `13` is, and it means nineteen.
        assert_eq!(instance.coefficients[1][0], 0x13);
        assert_ne!(instance.coefficients[1][0], 13);
        // The answer file is the same base, which is what `radix` says rather than two settings.
        assert_eq!(
            instance.parse_answer(GF256_ANSWER),
            Ok(vec![0xde, 0xad, 0xbe])
        );
    }

    /// A GF(2^8) system is built over the modulus the header states, and refused under any other.
    ///
    /// The acceptance criterion of #414, and the only check that separates the two moduli: they
    /// give fields of the same order, so no order comparison sees the difference, and a system
    /// built under the wrong one has plausible coefficients throughout.
    #[test]
    fn test_a_gf256_instance_is_built_over_the_modulus_its_header_states() {
        let instance = MqInstance::parse(GF256_FIXTURE).expect("parses");
        let answer = instance
            .parse_answer(GF256_ANSWER)
            .expect("the answer parses");
        let point: Vec<Gf256Mq> = answer.iter().map(|v| Gf256Mq::new(*v)).collect();

        let system = instance
            .system::<3, Gf256Mq>()
            .expect("the challenge modulus is accepted");
        assert_eq!(system.len(), 2);
        for (index, p) in system.iter().enumerate() {
            assert!(
                p.eval(&point).is_zero(),
                "polynomial {} does not vanish at the fixture's answer: {}",
                index,
                p
            );
        }

        // The AES modulus is the same order and a different field, and is refused by name.
        assert_eq!(
            instance.system::<3, Gf256>(),
            Err(MqError::WrongModulus {
                declared: 0x11D,
                coefficient_field: 0x11B,
            })
        );

        // And the refusal is load-bearing rather than fussy: read under AES, the same bytes do
        // not vanish at the same point, so the two moduli are different systems.
        let aes_point: Vec<Gf256> = answer.iter().map(|v| Gf256::new(*v)).collect();
        let mut forced = instance.clone();
        forced.modulus = Some(0x11B);
        let under_aes = forced
            .system::<3, Gf256>()
            .expect("an AES-declared instance builds over AES");
        assert!(
            under_aes.iter().any(|p| !p.eval(&aes_point).is_zero()),
            "the fixture must distinguish the two moduli, or the test proves nothing"
        );
    }

    /// `FiniteField::new` is not the coefficient route over an extension.
    ///
    /// The trap this guards: `Gf256Mq::new(0xa7)` is the prime-subfield embedding, so it is `1`.
    /// Building a GF(2^8) system through it collapses every byte to a bit and produces a system of
    /// the right shape whose every coefficient is wrong.
    #[test]
    fn test_gf256_coefficients_do_not_go_through_the_prime_subfield_embedding() {
        use crate::FiniteField;
        assert_eq!(<Gf256Mq as FiniteField>::new(0xa7), Gf256Mq::one());
        let instance = MqInstance::parse(GF256_FIXTURE).expect("parses");
        let system = instance.system::<3, Gf256Mq>().expect("builds");
        // `a7 * x0x1` survives as `a7`, which is what the embedding would have destroyed.
        assert_eq!(
            system[0].terms().get(&Monomial::new(&[1, 1, 0])).copied(),
            Some(Gf256Mq::new(0xa7))
        );
    }

    /// A dimension mismatch is an error, not a panic or a wrong answer.
    #[test]
    fn test_a_dimension_mismatch_is_reported() {
        let instance = MqInstance::parse(FIXTURE).expect("parses");
        assert_eq!(
            instance.system::<4, F>(),
            Err(MqError::DimensionMismatch {
                requested: 4,
                instance: 3
            })
        );
    }

    /// Dispatch reaches the compiled dimensions and reports the others.
    #[test]
    fn test_dispatch_covers_the_documented_set() {
        /// Reports the system's size without mentioning `N`, which is the point of the visitor.
        struct Count;
        impl MqVisitor<F> for Count {
            type Output = (usize, usize);
            fn visit<const N: usize>(
                self,
                system: &[MultivariatePolynomial<N, F>],
            ) -> Self::Output {
                (N, system.len())
            }
        }

        // The fixture's `n = 3` is not compiled in, and says so rather than panicking.
        let instance = MqInstance::parse(FIXTURE).expect("parses");
        assert_eq!(
            instance.dispatch::<F, _>(Count),
            Err(MqError::UnsupportedDimension {
                variables: 3,
                supported: SUPPORTED_DIMENSIONS
            })
        );

        // A supported one goes through. Built rather than parsed from a file, so the test stays
        // independent of any instance data.
        let n = 10;
        let row = vec![0u64; MqInstance::coefficients_per_polynomial(n)];
        let instance = MqInstance {
            field: MqField::Gf31,
            modulus: None,
            variables: n,
            polynomials: 2,
            seed: None,
            order: "graded reverse lex order".to_string(),
            coefficients: vec![row.clone(), row],
        };
        assert_eq!(instance.dispatch::<F, _>(Count), Ok((10, 2)));
    }

    /// Every dimension `SUPPORTED_DIMENSIONS` advertises has a dispatch arm behind it.
    ///
    /// The failure this is against is a one-sided edit: adding a size to the list without adding
    /// the arm leaves a build that promises a dimension and then returns
    /// `UnsupportedDimension` for it, and the error message itself would name the size it had just
    /// refused.
    #[test]
    fn test_every_advertised_dimension_dispatches() {
        struct Count;
        impl MqVisitor<F> for Count {
            type Output = (usize, usize);
            fn visit<const N: usize>(
                self,
                system: &[MultivariatePolynomial<N, F>],
            ) -> Self::Output {
                (N, system.len())
            }
        }

        for &n in SUPPORTED_DIMENSIONS {
            let row = vec![0u64; MqInstance::coefficients_per_polynomial(n)];
            let instance = MqInstance {
                field: MqField::Gf31,
                modulus: None,
                variables: n,
                polynomials: 2,
                seed: None,
                order: "graded reverse lex order".to_string(),
                coefficients: vec![row.clone(), row],
            };
            assert_eq!(
                instance.dispatch::<F, _>(Count),
                Ok((n, 2)),
                "{} is advertised and has no arm",
                n
            );
        }
    }

    /// `n = 24` is reachable, which is the smallest real challenge in an importable type.
    ///
    /// Type VI at `m = 16`: the generator's `n = m * 1.5` truncates to 24, so this is the first
    /// dimension at which an imported instance is challenge data rather than a toy example.
    #[test]
    fn test_the_smallest_real_challenge_dimension_is_compiled() {
        assert!(
            SUPPORTED_DIMENSIONS.contains(&24),
            "type VI m = 16 is n = 24"
        );
        assert_eq!(MqInstance::coefficients_per_polynomial(24), 325);
        let layout = MqInstance::monomial_layout::<24>();
        assert_eq!(layout.len(), 325);
        let distinct: std::collections::BTreeSet<_> = layout.iter().collect();
        assert_eq!(distinct.len(), 325, "the layout repeats a monomial");
        let order = MonomialOrder::GradedReverseLexicographic;
        assert!(
            layout.windows(2).all(|w| order.cmp(&w[0], &w[1]).is_gt()),
            "the layout is descending grevlex"
        );
    }

    /// A genuine Fukuoka instance is imported, solved, and verified against its published answer.
    ///
    /// **`#[ignore]`d because it needs data this repository does not redistribute.** The Fukuoka
    /// files are "All Rights Reserved" with no stated licence, so `tools/fetch-mq-challenge.sh`
    /// fetches them and this reads what it fetched. A test that silently passed when its data is
    /// absent would be worse than no test, so it is opt-in rather than conditional:
    ///
    /// ```sh
    /// tools/fetch-mq-challenge.sh
    /// cargo test --release --lib -- --ignored --exact \
    ///     grobner::research::mq::tests::test_a_published_instance_is_reproduced
    /// ```
    ///
    /// Type III, `n = 10`, seed 0: 20 quadratics in 10 unknowns over GF(31), so `m = 2n` and the
    /// system is overdetermined. Checked in both directions — the reconstruction vanishes at the
    /// published answer, **and** the solver independently recovers that same point, which is what
    /// rules out a monomial-order translation that happens to vanish somewhere.
    #[test]
    #[ignore = "needs tools/fetch-mq-challenge.sh; the instance data is not redistributable"]
    fn test_a_published_instance_is_reproduced() {
        use rand::{prelude::StdRng, SeedableRng};

        use crate::grobner::{solve_one_planned, PlannedSolveOptions, SolveOutcome, SolvePolicy};

        let directory =
            std::env::var("ZEEBRA_MQ_DIR").unwrap_or_else(|_| "research/instances/mq".to_string());
        let stem = format!("{}/ToyExample-type3-n10-seed0", directory);
        let text = std::fs::read_to_string(&stem)
            .unwrap_or_else(|e| panic!("run tools/fetch-mq-challenge.sh first: {}: {}", stem, e));
        let answer_text =
            std::fs::read_to_string(format!("{}-answer", stem)).expect("the companion answer file");

        let instance = MqInstance::parse(&text).expect("a published instance parses");
        assert_eq!(instance.field, MqField::Gf31);
        assert_eq!(instance.variables, 10);
        assert_eq!(instance.polynomials, 20, "type III is m = 2n");
        assert_eq!(instance.seed, Some(0));
        assert_eq!(instance.order, "graded reverse lex order");

        let published: Vec<F> = instance
            .parse_answer(&answer_text)
            .expect("the published answer parses")
            .into_iter()
            .map(F::new)
            .collect();
        assert_eq!(published.len(), 10);

        // Direction one: the reconstruction vanishes at the published answer. This is the check
        // that caught the monomial order in the first place.
        let system = instance.system::<10, F>().expect("GF(31) at n = 10");
        for (index, p) in system.iter().enumerate() {
            assert!(
                p.eval(&published).is_zero(),
                "polynomial {} does not vanish at the published answer — the monomial layout is \
                 wrong",
                index
            );
        }

        // Direction two: the solver finds that point without being told it. A wrong layout could
        // in principle vanish at one point by accident; it could not also be solved to the same
        // one.
        let (outcome, plan) = solve_one_planned(
            &system,
            &mut StdRng::seed_from_u64(1),
            &PlannedSolveOptions::with_policy(SolvePolicy::AutoWithFallback),
        );
        match outcome {
            Ok(SolveOutcome::Point(point)) => {
                assert_eq!(
                    point.to_vec(),
                    published,
                    "the solver found a different point than the published one"
                );
            }
            other => panic!("expected the published point, got {:?}", other),
        }
        // An overdetermined encryption instance has a unique solution, so D = 1.
        let conversion = plan
            .attempts
            .iter()
            .filter_map(|a| a.statistics.fglm.as_ref())
            .next()
            .expect("the conversion ran");
        assert_eq!(conversion.quotient_dimension, 1);
    }

    /// Both real `n = 24` challenge files import at the dimension #454 compiled.
    ///
    /// **`#[ignore]`d for the reason [`test_a_published_instance_is_reproduced`] gives.**
    ///
    /// ```sh
    /// tools/fetch-mq-challenge.sh
    /// cargo test --release --lib -- --ignored --exact \
    ///     grobner::research::mq::tests::test_the_real_n24_challenges_import
    /// ```
    ///
    /// `m = 16` is `n = 24` in both signature families, so one arm serves two fields: type VI over
    /// GF(31) and type V over GF(2^8) with the challenge's `0x11D` modulus and hex coefficients.
    /// Not solved — these are open-sized instances and §4.4 of `docs/research/fukuoka-mq.md` is
    /// where the resource diagnostic lives. What is asserted is the import: the header, the shape,
    /// 325 coefficients per polynomial, and a system that reaches the compiled dimension through
    /// `dispatch` rather than through a hand-written `N`.
    #[test]
    #[ignore = "needs tools/fetch-mq-challenge.sh; the instance data is not redistributable"]
    fn test_the_real_n24_challenges_import() {
        /// Reports the shape without mentioning `N`.
        struct Shape;
        impl MqVisitor<F> for Shape {
            type Output = (usize, usize, usize);
            fn visit<const N: usize>(
                self,
                system: &[MultivariatePolynomial<N, F>],
            ) -> Self::Output {
                (N, system.len(), system[0].terms().len())
            }
        }
        impl MqVisitor<Gf256Mq> for Shape {
            type Output = (usize, usize, usize);
            fn visit<const N: usize>(
                self,
                system: &[MultivariatePolynomial<N, Gf256Mq>],
            ) -> Self::Output {
                (N, system.len(), system[0].terms().len())
            }
        }

        let directory =
            std::env::var("ZEEBRA_MQ_DIR").unwrap_or_else(|_| "research/instances/mq".to_string());
        let read = |name: &str| {
            let path = format!("{}/{}", directory, name);
            std::fs::read_to_string(&path).unwrap_or_else(|e| {
                panic!("run tools/fetch-mq-challenge.sh first: {}: {}", path, e)
            })
        };

        // Type VI over GF(31). The dimension the registry row names.
        let six =
            MqInstance::parse(&read("challenge-6-16-0")).expect("a published instance parses");
        assert_eq!(six.field, MqField::Gf31);
        assert_eq!((six.variables, six.polynomials), (24, 16));
        assert_eq!(six.seed, Some(0));
        assert_eq!(six.coefficients[0].len(), 325, "binomial(26, 2)");
        let (n, equations, terms) = six.dispatch::<F, _>(Shape).expect("n = 24 is compiled");
        assert_eq!((n, equations), (24, 16));
        assert!(terms > 0 && terms <= 325);

        // Type V over GF(2^8), the same dimension and a different field. The header names the
        // modulus, so the coefficient type is verified against it rather than assumed; `Gf256`
        // (AES, 0x11B) would be refused here and `Gf256Mq` (0x11D) is accepted.
        let five =
            MqInstance::parse(&read("challenge-5-16-0")).expect("a published instance parses");
        assert_eq!(five.field, MqField::Gf256);
        assert_eq!(five.modulus, Some(MqField::PUBLISHED_GF256_MODULUS));
        assert_eq!((five.variables, five.polynomials), (24, 16));
        assert_eq!(five.coefficients[0].len(), 325);
        assert!(
            five.check_coefficient_field::<Gf256>().is_err(),
            "the AES modulus is not the challenge's"
        );
        let (n, equations, terms) = five
            .dispatch::<Gf256Mq, _>(Shape)
            .expect("n = 24 is compiled over GF(2^8) too");
        assert_eq!((n, equations), (24, 16));
        assert!(terms > 0 && terms <= 325);
    }

    /// Both real `m = 16` challenges vanish at the answer vector their solver published.
    ///
    /// **`#[ignore]`d for the reason [`test_a_published_instance_is_reproduced`] gives.**
    ///
    /// ```sh
    /// tools/fetch-mq-challenge.sh
    /// cargo test --release --lib -- --ignored --exact \
    ///     grobner::research::mq::tests::test_the_real_m16_challenges_vanish_at_their_published_answers
    /// ```
    ///
    /// **A real challenge file ships no answer, but a *solved* real challenge has one anyway**: the
    /// challenge publishes the submitted answer vector on the submission's detail page, and both
    /// `m = 16` seed-0 instances were solved in 2015 by J.-C. Faugère with F5/FGb. So the two
    /// instances this crate has registered are not open instances with nothing to check against —
    /// they have an independent correctness oracle, which is what this test is. The vectors are
    /// transcribed from the detail pages rather than fetched, the way the solve figures in
    /// `research/fukuoka-mq/solved-instances.tsv` are; the instance files they are evaluated
    /// against are the ones `tools/fetch-mq-challenge.sh` checksums.
    ///
    /// | instance | page | sha256 of the page | solver, date |
    /// |---|---|---|---|
    /// | type V `m = 16` seed 0 | `details/details_V_20150403.html` | `91b17742511b284f8d698e1022c4da80f1816c361ef805810cc143e7116f2ea3` | J.-C. Faugère, 2015/4/3 |
    /// | type VI `m = 16` seed 0 | `details/details_VI_20150401.html` | `deac13ac0cc087da92e3adc4a84b27e60a0408505f98967995542b3aeb03be11` | J.-C. Faugère, 2015/4/1 |
    ///
    /// Both read 2026-11-09. This asserts the *import*, not a solve: the point is supplied rather
    /// than found, and #197 claims no solving result.
    #[test]
    #[ignore = "needs tools/fetch-mq-challenge.sh; the instance data is not redistributable"]
    fn test_the_real_m16_challenges_vanish_at_their_published_answers() {
        let directory =
            std::env::var("ZEEBRA_MQ_DIR").unwrap_or_else(|_| "research/instances/mq".to_string());
        let read = |name: &str| {
            let path = format!("{}/{}", directory, name);
            std::fs::read_to_string(&path).unwrap_or_else(|e| {
                panic!("run tools/fetch-mq-challenge.sh first: {}: {}", path, e)
            })
        };

        // Type VI over GF(31), written in decimal on the detail page.
        let six = MqInstance::parse(&read("challenge-6-16-0")).expect("type VI parses");
        assert_eq!(
            (six.field, six.variables, six.polynomials),
            (MqField::Gf31, 24, 16)
        );
        let answer: [u64; 24] = [
            3, 4, 16, 4, 1, 0, 11, 2, 6, 23, 16, 26, 6, 23, 2, 1, 17, 30, 21, 5, 17, 0, 24, 9,
        ];
        let point: Vec<F> = answer
            .iter()
            .map(|&t| six.element(t).expect("a GF(31) residue"))
            .collect();
        let system = six.system::<24, F>().expect("n = 24 over GF(31)");
        assert_eq!(system.len(), 16);
        for (index, p) in system.iter().enumerate() {
            assert!(
                p.eval(&point).is_zero(),
                "type VI m = 16 polynomial {} does not vanish at the published answer",
                index
            );
        }

        // Type V over GF(2^8), written in hex on the detail page — transcribed as the bytes it
        // spells, and read at the challenge's own modulus.
        let five = MqInstance::parse(&read("challenge-5-16-0")).expect("type V parses");
        assert_eq!(
            (five.field, five.variables, five.polynomials),
            (MqField::Gf256, 24, 16)
        );
        let answer: [u64; 24] = [
            0x73, 0, 0, 0, 0, 0, 0, 0, 0, 0x98, 0xF6, 0xDC, 0xCB, 0x42, 0x52, 0x01, 0xA3, 0xA5,
            0xB2, 0x62, 0xEC, 0x89, 0x8F, 0xD6,
        ];
        let point: Vec<Gf256Mq> = answer
            .iter()
            .map(|&t| five.element(t).expect("a GF(2^8) byte"))
            .collect();
        let system = five.system::<24, Gf256Mq>().expect("n = 24 over GF(2^8)");
        assert_eq!(system.len(), 16);
        for (index, p) in system.iter().enumerate() {
            assert!(
                p.eval(&point).is_zero(),
                "type V m = 16 polynomial {} does not vanish at the published answer",
                index
            );
        }
    }

    /// The published GF(2^8) answer vanishes under the challenge's `0x11D` and under no other.
    ///
    /// **`#[ignore]`d for the reason [`test_a_published_instance_is_reproduced`] gives.**
    ///
    /// ```sh
    /// tools/fetch-mq-challenge.sh
    /// cargo test --release --lib -- --ignored --exact \
    ///     grobner::research::mq::tests::test_the_published_answer_vanishes_only_under_the_challenges_modulus
    /// ```
    ///
    /// This is the test #197 asked for in place of an argument. `Gf256` and `Gf256Mq` are both
    /// GF(2^8) and are isomorphic, so no shape check and no order check can tell them apart — the
    /// *only* thing that distinguishes a correct import from a silently wrong one is whether the
    /// challenge's own answer file is a root of the system the import builds. Type II `n = 10`
    /// seed 0: **all 20** polynomials vanish under the challenge modulus and **none of the 20** do
    /// under the AES one. The AES system is built by hand through [`MqInstance::element`] rather
    /// than through [`MqInstance::system`], because `system` refuses it — which is the point, and
    /// is asserted here too.
    #[test]
    #[ignore = "needs tools/fetch-mq-challenge.sh; the instance data is not redistributable"]
    fn test_the_published_answer_vanishes_only_under_the_challenges_modulus() {
        let directory =
            std::env::var("ZEEBRA_MQ_DIR").unwrap_or_else(|_| "research/instances/mq".to_string());
        let stem = format!("{}/ToyExample-type2-n10-seed0", directory);
        let text = std::fs::read_to_string(&stem)
            .unwrap_or_else(|e| panic!("run tools/fetch-mq-challenge.sh first: {}: {}", stem, e));
        let answer_text =
            std::fs::read_to_string(format!("{}-answer", stem)).expect("the companion answer file");

        let instance = MqInstance::parse(&text).expect("a published instance parses");
        assert_eq!(instance.field, MqField::Gf256);
        assert_eq!(instance.modulus, Some(MqField::PUBLISHED_GF256_MODULUS));
        assert_eq!((instance.variables, instance.polynomials), (10, 20));
        let tokens = instance
            .parse_answer(&answer_text)
            .expect("the published answer parses base 16");
        assert_eq!(tokens.len(), 10);

        // Under the challenge's own modulus, through the checked path.
        let right: Vec<Gf256Mq> = tokens
            .iter()
            .map(|&t| instance.element(t).expect("a GF(2^8) byte"))
            .collect();
        let system = instance.system::<10, Gf256Mq>().expect("0x11D is accepted");
        assert_eq!(system.len(), 20);
        assert_eq!(
            system.iter().filter(|p| p.eval(&right).is_zero()).count(),
            20,
            "the published answer must be a root of every polynomial under 0x11D"
        );

        // Under the AES modulus the checked path refuses, so the comparison is built by hand.
        assert!(
            instance.check_coefficient_field::<Gf256>().is_err(),
            "the AES modulus is not the challenge's and must be refused"
        );
        let layout = MqInstance::monomial_layout::<10>();
        let wrong: Vec<Gf256> = tokens
            .iter()
            .map(|&t| instance.element(t).expect("a GF(2^8) byte"))
            .collect();
        let aes: Vec<MultivariatePolynomial<10, Gf256>> = instance
            .coefficients
            .iter()
            .map(|row| {
                let terms: Vec<(Monomial<10>, Gf256)> = layout
                    .iter()
                    .zip(row)
                    .map(|(m, &c)| (*m, instance.element(c).expect("a GF(2^8) byte")))
                    .collect();
                MultivariatePolynomial::new(&terms)
            })
            .collect();
        assert_eq!(
            aes.iter().filter(|p| p.eval(&wrong).is_zero()).count(),
            0,
            "reading the same bytes under the AES modulus must destroy the root — a nonzero count \
             here would mean the two moduli are not distinguishable by this oracle"
        );
    }

    /// The GF(2) families import: both type I and type IV toys vanish at their published answers.
    ///
    /// **`#[ignore]`d for the reason [`test_a_published_instance_is_reproduced`] gives.**
    ///
    /// ```sh
    /// tools/fetch-mq-challenge.sh
    /// cargo test --release --lib -- --ignored --exact \
    ///     grobner::research::mq::tests::test_the_published_gf2_instances_import
    /// ```
    ///
    /// Type I `n = 10` seed 0 is the encryption shape (`m = 2n = 20`) and type IV `n = 5` seed 0
    /// the signature shape (`m = 3`), so both GF(2) families and both of their toy dimensions are
    /// covered — `n = 5` is the size [`SUPPORTED_DIMENSIONS`] gained for them. Not solved: #197
    /// claims no solving result.
    #[test]
    #[ignore = "needs tools/fetch-mq-challenge.sh; the instance data is not redistributable"]
    fn test_the_published_gf2_instances_import() {
        let directory =
            std::env::var("ZEEBRA_MQ_DIR").unwrap_or_else(|_| "research/instances/mq".to_string());
        let read = |name: &str| {
            let path = format!("{}/{}", directory, name);
            std::fs::read_to_string(&path).unwrap_or_else(|e| {
                panic!("run tools/fetch-mq-challenge.sh first: {}: {}", path, e)
            })
        };

        // Type I: encryption, m = 2n, the toy at the smallest size type I publishes.
        let one = MqInstance::parse(&read("ToyExample-type1-n10-seed0")).expect("type I parses");
        assert_eq!(one.field, MqField::Gf2);
        assert_eq!(
            one.modulus, None,
            "GF(2) states no modulus; its order is one"
        );
        assert_eq!((one.variables, one.polynomials), (10, 20));
        let answer = one
            .parse_answer(&read("ToyExample-type1-n10-seed0-answer"))
            .expect("the published answer parses base 10");
        let point: Vec<Zp2> = answer
            .iter()
            .map(|&t| one.element(t).expect("a GF(2) bit"))
            .collect();
        let system = one.system::<10, Zp2>().expect("GF(2) at n = 10 over Zp2");
        for (index, p) in system.iter().enumerate() {
            assert!(
                p.eval(&point).is_zero(),
                "type I polynomial {} does not vanish at the published answer",
                index
            );
        }

        // Type IV: signature, and n = 5 is the dimension added for it.
        let four = MqInstance::parse(&read("ToyExample-type4-n5-seed0")).expect("type IV parses");
        assert_eq!(four.field, MqField::Gf2);
        assert_eq!((four.variables, four.polynomials), (5, 3));
        let answer = four
            .parse_answer(&read("ToyExample-type4-n5-seed0-answer"))
            .expect("the published answer parses");
        let point: Vec<Zp2> = answer
            .iter()
            .map(|&t| four.element(t).expect("a GF(2) bit"))
            .collect();
        let system = four.system::<5, Zp2>().expect("GF(2) at n = 5 over Zp2");
        for (index, p) in system.iter().enumerate() {
            assert!(
                p.eval(&point).is_zero(),
                "type IV polynomial {} does not vanish at the published answer",
                index
            );
        }
    }

    /// An instance header with no coefficients, for the answer parser's sake.
    fn header_only(field: MqField, variables: usize) -> MqInstance {
        MqInstance {
            field,
            modulus: None,
            variables,
            polynomials: 2 * variables,
            seed: Some(0),
            order: "graded reverse lex order".to_string(),
            coefficients: Vec::new(),
        }
    }

    /// The published answer file parses to the coordinates it names.
    #[test]
    fn test_parsing_an_answer_file() {
        assert_eq!(
            header_only(MqField::Gf31, 10).parse_answer("[22, 22, 28, 12, 9, 2, 1, 18, 11, 25]"),
            Ok(vec![22, 22, 28, 12, 9, 2, 1, 18, 11, 25])
        );
        // Whitespace and line breaks are immaterial.
        assert_eq!(
            header_only(MqField::Gf31, 3).parse_answer("[1,\n 2,\n 3]\n"),
            Ok(vec![1, 2, 3])
        );
    }

    /// A GF(2^8) answer is read base 16: ten bytes, not nine wrong decimal ones.
    ///
    /// `ToyExample-type2-n10-seed0-answer` verbatim. Under the old digits-only split this returned
    /// `[3, 67, 64, 5, 81, 4, 6, 5, 8]` — nine values, every one wrong, with no error: `a3` gave
    /// `3`, `ab` gave nothing, `4f` gave `4`. Note `67`, `64` and `81` are the tokens that parse
    /// "successfully" as decimal and still denote different field elements.
    #[test]
    fn test_a_hex_answer_vector_is_read_base_sixteen() {
        assert_eq!(
            header_only(MqField::Gf256, 10)
                .parse_answer("[a3, 67, 64, 5c, ab, 81, 4f, e6, f5, b8]"),
            Ok(vec![
                0xa3, 0x67, 0x64, 0x5c, 0xab, 0x81, 0x4f, 0xe6, 0xf5, 0xb8
            ])
        );
    }

    /// The parsed answer has exactly the instance's `n` coordinates, and a short file is an error.
    #[test]
    fn test_a_truncated_answer_file_is_an_error_and_not_a_shorter_vector() {
        let instance = header_only(MqField::Gf31, 10);
        assert_eq!(
            instance.parse_answer("[22, 22, 28]"),
            Err(MqError::WrongAnswerCount {
                found: 3,
                expected: 10
            })
        );
        assert_eq!(
            instance
                .parse_answer("[22, 22, 28, 12, 9, 2, 1, 18, 11, 25]")
                .map(|a| a.len()),
            Ok(instance.variables)
        );
    }

    /// A token that is not a field element is named rather than dropped.
    #[test]
    fn test_an_unreadable_answer_token_is_named() {
        // Decimal over GF(31), so a hex letter is not a digit here.
        assert_eq!(
            header_only(MqField::Gf31, 3).parse_answer("[22, 1a, 28]"),
            Err(MqError::BadAnswerValue {
                position: 1,
                token: "1a".to_string()
            })
        );
        // Readable in the base, and still not an element of GF(31).
        assert_eq!(
            header_only(MqField::Gf31, 3).parse_answer("[22, 31, 28]"),
            Err(MqError::BadAnswerValue {
                position: 1,
                token: "31".to_string()
            })
        );
        // The field's whole range is admitted: 0xff is an element of GF(2^8), 256 would not be.
        assert_eq!(
            header_only(MqField::Gf256, 2).parse_answer("[ff, 00]"),
            Ok(vec![255, 0])
        );
    }
}
