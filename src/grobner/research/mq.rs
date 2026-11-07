//! Importing Fukuoka MQ Challenge instances, exactly as published.
//!
//! <https://www.mqchallenge.org/>. Six problem types: GF(2), GF(2^8) and GF(31), each as an
//! encryption family (`m = 2n`, overdetermined) and a signature family (`n ≈ 1.5m`,
//! underdetermined). Only the GF(31) types are importable here — see [`MqField`] for why — and
//! GF(31) needs no new arithmetic, since `PrimeFieldElement64<31>` already exists.
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
    /// Types I and IV. **Not importable yet** — but no longer for want of a field.
    ///
    /// `fields::Zp2` is `PrimeFieldElement32<2>` and `fields::BinaryFieldElement` has been
    /// publicly exported since `8757b4a`; what is missing is the import path itself, the toy
    /// dimensions these families publish (which differ from type III's and type VI's), and a
    /// recorded decision between the two representations of GF(2). See #197.
    Gf2,

    /// Types II and V. **Not importable yet** — and the reason is a modulus, not an export.
    ///
    /// `fields::ExtensionFieldElement` has been publicly exported since `8757b4a`, and the
    /// challenge's own GF(2^8) — `x^8 + x^4 + x^3 + x^2 + 1`, which is **not** the AES modulus
    /// `fields::Gf256` uses — is declared as `fields::Gf256Mq`. Reading these coefficient bytes
    /// under the wrong one of the two would build a different system from the published one, so
    /// the import waits on a test against a published answer file. See #197.
    Gf256,

    /// Types III and VI. `PrimeFieldElement64<31>`, which already exists — no new arithmetic is a
    /// prerequisite for this importer, and a compact 32-bit field is an independent optimization.
    Gf31,
}

impl MqField {
    /// The field's order.
    pub fn order(&self) -> u64 {
        match self {
            Self::Gf2 => 2,
            Self::Gf256 => 256,
            Self::Gf31 => 31,
        }
    }

    /// The base an answer file's elements are written in.
    ///
    /// GF(2^8) publishes its answer vectors as two-digit hex bytes — `[a3, 67, 64, ...]` — and the
    /// prime-field types publish decimal. `format.html` and every `-answer` file agree; the hex is
    /// not a rendering choice this crate makes, so it is not optional to read.
    ///
    /// GF(2) is 10 only because `0` and `1` are the same in every base.
    pub fn answer_radix(&self) -> u32 {
        match self {
            Self::Gf2 | Self::Gf31 => 10,
            Self::Gf256 => 16,
        }
    }

    /// The `Galois Field :` header value this parses from.
    fn parse(value: &str) -> Option<Self> {
        match value.trim() {
            "GF(2)" => Some(Self::Gf2),
            "GF(256)" | "GF(2^8)" => Some(Self::Gf256),
            "GF(31)" => Some(Self::Gf31),
            _ => None,
        }
    }
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

    /// The base field is one this crate cannot yet express as a coefficient type.
    UnsupportedField {
        field: MqField,
        because: &'static str,
    },

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
            Self::UnsupportedField { field, because } => {
                write!(f, "{} is not importable yet: {}", field, because)
            }
            Self::WrongCoefficientField {
                declared,
                coefficient_field,
            } => write!(
                f,
                "the instance is over GF({}) and the coefficient type has order {:?}",
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
/// The toy-example sizes. The published challenges run from `n = 55` to `n = 100`, which is far
/// beyond what the solvers reach — adding them here would compile code that cannot be used, and
/// the honest statement is this list plus
/// [`MqError::UnsupportedDimension`](MqError::UnsupportedDimension).
pub const SUPPORTED_DIMENSIONS: &[usize] = &[10, 15, 20];

/// A parsed instance, before a compile-time dimension is chosen.
///
/// Holds exactly what the file says, with the coefficients **unreduced and in file order**. Nothing
/// is interpreted until [`Self::system`] or [`Self::dispatch`], so a round-trip through this type
/// is lossless against the source and a checksum over it means something.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MqInstance {
    /// The base field.
    pub field: MqField,

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
                let order_of_field = field
                    .ok_or(MqError::MissingHeader {
                        key: "Galois Field",
                    })?
                    .order();
                for (position, token) in body.split_whitespace().enumerate() {
                    // `0..=q` rather than `0..q`: `31` occurs in the published GF(31) files and is
                    // congruent to zero. See the module docs.
                    let value: u64 = token.parse().map_err(|_| MqError::BadCoefficient {
                        polynomial: index,
                        position,
                        token: token.to_string(),
                    })?;
                    if value > order_of_field {
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
                    field = Some(MqField::parse(value).ok_or_else(|| MqError::BadHeader {
                        key: "Galois Field",
                        value: value.trim().to_string(),
                    })?)
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
        let radix = self.field.answer_radix();
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
    /// Two separate questions, and both have to be answered before a single coefficient is
    /// converted. First, whether this crate can express the field at all — GF(2) and GF(2^8)
    /// cannot be, for reasons of module visibility rather than mathematics. Second, whether the
    /// coefficient type the caller supplied *is* that field, which is the one a generic
    /// `F: FiniteField` signature cannot ask and so cannot enforce.
    ///
    /// Compared as limb slices rather than as integers, because a field order need not fit a
    /// `u64` — the comparison has to be correct for the wide fields M20 added, not only for the
    /// ones this importer currently reaches.
    ///
    /// # Errors
    /// [`MqError::UnsupportedField`] or [`MqError::WrongCoefficientField`].
    pub fn check_coefficient_field<F: KnownOrder>(&self) -> Result<(), MqError> {
        match self.field {
            MqField::Gf31 => {}
            MqField::Gf2 => {
                return Err(MqError::UnsupportedField {
                    field: self.field,
                    because: "the GF(2) import path is unwritten; the field exists as fields::Zp2",
                })
            }
            MqField::Gf256 => {
                return Err(MqError::UnsupportedField {
                    field: self.field,
                    because: "the GF(2^8) import path is unwritten; the challenge's modulus, \
                              which is not the AES one, exists as fields::Gf256Mq",
                })
            }
        }

        let declared = self.field.order();
        if F::order_limbs() != [declared] {
            return Err(MqError::WrongCoefficientField {
                declared,
                coefficient_field: F::order_limbs().to_vec(),
            });
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
    /// [`MqError::UnsupportedField`] if the field is not yet expressible at all;
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
        Ok(self
            .coefficients
            .iter()
            .map(|row| {
                let terms: Vec<(Monomial<N>, F)> = layout
                    .iter()
                    .zip(row)
                    .map(|(monomial, coefficient)| (*monomial, F::new(*coefficient)))
                    .collect();
                // Through `new`, which drops the terms whose coefficients reduced to zero — and
                // `31` over GF(31) is one of those.
                MultivariatePolynomial::new(&terms)
            })
            .collect())
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
            10 => Ok(visitor.visit(&self.system::<10, F>()?)),
            15 => Ok(visitor.visit(&self.system::<15, F>()?)),
            20 => Ok(visitor.visit(&self.system::<20, F>()?)),
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
    use super::{MqError, MqField, MqInstance, MqVisitor, SUPPORTED_DIMENSIONS};
    use crate::{
        fields::PrimeFieldElement64, FiniteField, Monomial, MonomialOrder, MultivariatePolynomial,
        Zero,
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

    /// The fields this crate cannot express yet say so, naming what is missing.
    #[test]
    fn test_the_binary_and_extension_fields_are_refused_by_name() {
        for field in [MqField::Gf2, MqField::Gf256] {
            // Built rather than parsed: the fixture's coefficients are out of range for GF(2), and
            // what is under test is `system`'s refusal rather than the parse. Note this is
            // reported *before* the coefficient-field mismatch that `F` also has — "there is no
            // import path for GF(2^8)" is the more useful fact than "GF(31) is not GF(2^8)".
            let instance = MqInstance {
                field,
                variables: 3,
                polynomials: 1,
                seed: None,
                order: "graded reverse lex order".to_string(),
                coefficients: vec![vec![0; MqInstance::coefficients_per_polynomial(3)]],
            };
            match instance.system::<3, F>() {
                Err(MqError::UnsupportedField { field: f, because }) => {
                    assert_eq!(f, field);
                    // The reason used to be "`src/fields/binary_field.rs` is not publicly
                    // exported". That export landed in `8757b4a`, so asserting on it would now
                    // pin a false claim; what remains missing is the import path itself.
                    assert!(because.contains("import path is unwritten"), "{}", because);
                    assert!(
                        !because.contains("not publicly exported"),
                        "both field modules are public since 8757b4a: {}",
                        because
                    );
                }
                other => panic!("expected an unsupported field, got {:?}", other),
            }
        }
    }

    /// The coefficient range follows the declared field, so GF(2) refuses a GF(31) coefficient.
    ///
    /// Worth its own test because it is the check that catches a file whose header and body
    /// disagree — a mis-filed download, which is otherwise indistinguishable from valid data.
    #[test]
    fn test_the_coefficient_range_follows_the_declared_field() {
        // 30 is legal over GF(31) and GF(256), and not over GF(2).
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
            variables: n,
            polynomials: 2,
            seed: None,
            order: "graded reverse lex order".to_string(),
            coefficients: vec![row.clone(), row],
        };
        assert_eq!(instance.dispatch::<F, _>(Count), Ok((10, 2)));
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

    /// An instance header with no coefficients, for the answer parser's sake.
    fn header_only(field: MqField, variables: usize) -> MqInstance {
        MqInstance {
            field,
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
