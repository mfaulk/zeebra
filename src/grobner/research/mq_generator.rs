//! The Fukuoka MQ Challenge's own coefficient generator, as a function of `(type, n, m, seed)`.
//!
//! An instance's coefficients are a deterministic walk over `PI` — 200 000 000 ASCII `0`/`1`
//! characters the challenge publishes under `utility/` — and nothing else. The recipe is
//! `docs/research/fukuoka-mq.md` §7.1: `start = type * n`, `interval = (seed + n) * 10 + type`, one
//! coefficient per stride at the field's own width, `pos` carrying across polynomials.
//!
//! # Three published classes, not one
//!
//! §7.2 established the walk against the toy examples and §7.3 reported the shipped verifiers as
//! **broken** in two ways. Running this implementation against the real challenges showed that both
//! "defects" are instead **parameters**, and that the published data falls into three classes whose
//! differences are measured rather than inferred ([`ThirtyOne`], [`ConstantColumn`]):
//!
//! | class | reads per polynomial | the value `31` | the constant column |
//! |---|---|---|---|
//! | toy examples, all six types | `mon - 1` | kept | **not** from the stream |
//! | real encryption, types I–III | `mon - 1` | **resampled** | **not** from the stream |
//! | real signature, types IV–VI | **`mon`** | resampled | **from the stream** |
//!
//! Each row is zero mismatches against genuine files, every coefficient compared. The practical
//! consequence is the one #420 was filed to get and did not expect to get in full: **a real
//! signature challenge is reproducible from `(type, m, seed)` alone** — constants included, nothing
//! to download but `PI`. A real encryption challenge is reproducible except for its constant
//! column, which `YDHTS15` Algorithm 1 Step 4 computes from the secret planted answer, so that
//! column is the one thing no walk can produce; [`GeneratedMq::into_instance_with_constants`] takes
//! it from the caller rather than inventing it.
//!
//! `PI` is "All Rights Reserved" like the instance files, so it is not committed. `tools/fetch-pi.sh`
//! fetches and checksums it, and every test that needs it is `#[ignore]`d; the arithmetic is tested
//! against a synthetic stream instead, which is what makes the walk itself checkable offline.

use super::mq::{MqField, MqInstance};

/// The published length of `PI`, and the modulus the walk wraps at.
pub const PI_LENGTH: usize = 200_000_000;

/// The SHA-256 of the published `PI`, as hex.
///
/// Recorded so a fetched copy can be checked rather than trusted. Both `utility/` archives ship the
/// same bytes.
pub const PI_SHA256: &str = "58f55ded23d13c56178dbcae8803acfff03c09db4a6ae142fbcb2e31acdfbe98";

/// One of the six published families.
///
/// The discriminant is the challenge's own type number, which is not decoration: it appears in both
/// `start` and `interval`, so the walk differs between two types at the same dimension.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum MqType {
    /// GF(2), encryption.
    I = 1,
    /// GF(2^8), encryption.
    II = 2,
    /// GF(31), encryption.
    III = 3,
    /// GF(2), signature.
    IV = 4,
    /// GF(2^8), signature.
    V = 5,
    /// GF(31), signature.
    VI = 6,
}

impl MqType {
    /// The type number, as it appears in `start` and `interval`.
    pub fn number(self) -> u64 {
        self as u64
    }

    /// The base field, which is a property of the type and not of the dimension.
    pub fn field(self) -> MqField {
        match self {
            Self::I | Self::IV => MqField::Gf2,
            Self::II | Self::V => MqField::Gf256,
            Self::III | Self::VI => MqField::Gf31,
        }
    }

    /// Whether the family is a signature scheme (`n > m`) rather than an encryption one (`m = 2n`).
    pub fn is_signature(self) -> bool {
        matches!(self, Self::IV | Self::V | Self::VI)
    }

    /// The type for a challenge type number, or `None` outside `1..=6`.
    pub fn from_number(number: u64) -> Option<Self> {
        Some(match number {
            1 => Self::I,
            2 => Self::II,
            3 => Self::III,
            4 => Self::IV,
            5 => Self::V,
            6 => Self::VI,
            _ => return None,
        })
    }
}

/// What an instance is a function of.
///
/// `n` **and** `m` are both carried rather than one being derived from the other. The published
/// challenge does obey its own rule — `m = 2n` for the encryption types and `n = floor(3m/2)` for
/// the signature ones — but the **toy examples do not**: type IV–VI publish `n = 5, 10, 15`, and the
/// `n = 5` file carries `m = 3`, where `floor(1.5 * 3)` is 4. The pair is what the file's header
/// states and what the walk was run with, so it is what this type stores.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct MqParameters {
    /// Which family.
    pub mq_type: MqType,
    /// `n`, the number of variables. **This is what `start` and `interval` are computed from.**
    pub variables: usize,
    /// `m`, the number of polynomials.
    pub polynomials: usize,
    /// The published seed, `0..=4` for every family the challenge ships.
    pub seed: u64,
    /// What the file does with the out-of-range fifth-bit value `31`. GF(31) only.
    pub thirty_one: ThirtyOne,
    /// Whether the walk supplies each polynomial's constant term.
    pub constant_column: ConstantColumn,
}

/// Whether the constant term of each polynomial comes out of the digit stream.
///
/// The second of the two differences between the published classes, and the one with the larger
/// consequence. `guidance` says a signature instance's coefficients "are all chosen from PI digits",
/// `YDHTS15` Algorithm 2 says they are random, and §7.4 recorded the question as **not established**
/// because the toy examples rule out the natural reading: their constants are not the next value of
/// the stream.
///
/// Measured against the real files, both statements are right about different things. The **real**
/// signature challenges take `mon` reads per polynomial and the last one *is* the constant — zero
/// mismatches on all 325 coefficients of `challenge-6-16-0` (GF(31)) and `challenge-5-16-0`
/// (GF(2^8)). The toy examples take `mon - 1` and their constants come from elsewhere. So
/// `guidance` describes the challenge and §7.4's counter-evidence describes the toy examples.
///
/// For the encryption types it is [`Self::External`] everywhere, including the real
/// `challenge-3-34-0` at `n = 34`: `YDHTS15` Algorithm 1 Step 4 chooses those constants so that a
/// secret point is a root, which is why `site`'s rule 4 bars the challenge team from competing in
/// types I–III and why the shipped encryption verifier prints a literal `0` there.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum ConstantColumn {
    /// `mon - 1` reads per polynomial; the constant is the caller's to supply.
    ///
    /// Every toy example, and every real encryption instance.
    #[default]
    External,

    /// `mon` reads per polynomial, the last of which is the constant.
    ///
    /// The real signature challenges. This is the case in which a published instance is
    /// reproducible in full.
    FromStream,
}

/// What a GF(31) file does with the value `31`, which five raw bits can produce and the field cannot.
///
/// **A property of the file, not of the type.** `docs/research/fukuoka-mq.md` §7.3 established from
/// the toy examples that the shipped generator's `while (coef == 31)` rejection loop must be
/// *removed* to reproduce them — `31` occurs 40 times in type VI `n = 15` seed 0 and 310 times in
/// type III `n = 20` seed 0, and is congruent to zero — and reported the loop as a defect. The real
/// challenges say otherwise: `challenge-6-16-0` contains `31` **zero times in 5 200 coefficients**
/// where the rate would put ~168 there, and so does `challenge-3-34-0` in 42 840. Both reproduce
/// exactly **with** the loop. So the loop is a parameter, every published class is reproducible, and
/// no single policy reproduces two of them.
///
/// Inert for the other two fields: one bit cannot be out of range for GF(2), and eight bits are a
/// byte, so every value GF(2^8) can read is a field element.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum ThirtyOne {
    /// The raw five bits, `31` included. **Every published toy example.**
    #[default]
    Kept,

    /// Resampled until it is not `31`, advancing the position each time. **The real challenges.**
    ///
    /// The advance is why the difference is not a 40-coefficient correction: a rejection shifts
    /// every later read, so applying the wrong policy disagrees with 1 214 of 1 300 coefficients
    /// rather than with 40.
    Rejected,
}

impl MqParameters {
    /// A **toy example**: `31` kept, constants external. `n` and `m` as the file's header states.
    ///
    /// Both are taken rather than derived because the toy examples do not all obey their type's
    /// rule: types IV–VI publish `n = 5, 10, 15`, and the `n = 5` file carries `m = 3` where
    /// `floor(1.5 * 3)` is 4.
    pub fn toy_example(mq_type: MqType, variables: usize, polynomials: usize, seed: u64) -> Self {
        Self {
            mq_type,
            variables,
            polynomials,
            seed,
            thirty_one: ThirtyOne::Kept,
            constant_column: ConstantColumn::External,
        }
    }

    /// A **real published challenge**, indexed the way the challenge indexes it.
    ///
    /// `index` is `n` for the encryption types and `m` for the signature ones, which is how `site`
    /// names the files: `challenge-3-34-0` is type III at `n = 34`, and `challenge-6-16-0` is type
    /// VI at `m = 16` — whose header then says `n = 24`. The rest follows from the type: `m = 2n`
    /// or `n = floor(3m/2)`, `31` resampled, and the constant column from the stream for a
    /// signature family and external for an encryption one.
    pub fn challenge(mq_type: MqType, index: usize, seed: u64) -> Self {
        let (variables, polynomials) = if mq_type.is_signature() {
            (3 * index / 2, index)
        } else {
            (index, 2 * index)
        };
        Self {
            mq_type,
            variables,
            polynomials,
            seed,
            thirty_one: ThirtyOne::Rejected,
            constant_column: if mq_type.is_signature() {
                ConstantColumn::FromStream
            } else {
                ConstantColumn::External
            },
        }
    }

    /// An encryption instance (types I–III), where `m = 2n`, in the toy examples' convention.
    pub fn encryption(mq_type: MqType, variables: usize, seed: u64) -> Self {
        Self::toy_example(mq_type, variables, 2 * variables, seed)
    }

    /// A signature instance (types IV–VI), where `n = floor(3m/2)`, in the toy examples' convention.
    ///
    /// The truncation is the generator's `n = m * 1.5` assigned to an `int`, so `m = 17` gives
    /// `n = 25` and not 26. For the one toy example this disagrees with — type IV–VI at `n = 5`,
    /// `m = 3` — use [`Self::toy_example`], which takes both.
    pub fn signature(mq_type: MqType, polynomials: usize, seed: u64) -> Self {
        Self::toy_example(mq_type, 3 * polynomials / 2, polynomials, seed)
    }

    /// The same parameters with `31` resampled, which is what every real challenge does.
    pub fn rejecting_thirty_one(mut self) -> Self {
        self.thirty_one = ThirtyOne::Rejected;
        self
    }

    /// The same parameters with the constant column taken from the stream.
    pub fn with_constants_from_stream(mut self) -> Self {
        self.constant_column = ConstantColumn::FromStream;
        self
    }

    /// How many values the walk reads per polynomial: `mon`, or `mon - 1` without the constant.
    pub fn reads_per_polynomial(&self) -> usize {
        match self.constant_column {
            ConstantColumn::FromStream => self.coefficients_per_polynomial(),
            ConstantColumn::External => self.coefficients_per_polynomial() - 1,
        }
    }

    /// The offset into `PI` the first coefficient is read from: `type * n`.
    pub fn start(&self) -> usize {
        (self.mq_type.number() as usize) * self.variables
    }

    /// The stride between consecutive coefficients: `(seed + n) * 10 + type`.
    ///
    /// Note that it is a stride in *stream positions*, not in bits consumed: a GF(2^8) coefficient
    /// reads eight bits — two nibbles, at `pos` and `pos + 4` — and still advances by one interval.
    pub fn interval(&self) -> usize {
        ((self.seed as usize) + self.variables) * 10 + (self.mq_type.number() as usize)
    }

    /// Coefficients per polynomial, constant included: every monomial of degree at most two.
    pub fn coefficients_per_polynomial(&self) -> usize {
        MqInstance::coefficients_per_polynomial(self.variables)
    }
}

/// Why a generated instance could not be produced.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum MqGeneratorError {
    /// The digit source is empty, so there is nothing to walk.
    EmptySource,

    /// A character in the digit source is neither `0` nor `1`.
    ///
    /// The shipped `readPI` treats every non-`'0'` byte as a one bit, which would read a corrupted
    /// or truncated download as plausible coefficients. Refused rather than imitated: a stream this
    /// cannot account for is one to report.
    NotABit { position: usize, byte: u8 },

    /// The caller supplied a different number of constant terms than there are polynomials.
    WrongConstantCount { found: usize, expected: usize },

    /// A constant term is not a legal coefficient token for the field.
    BadConstant { polynomial: usize, value: u64 },

    /// The instance's class does not generate its constant column, so there is none to use.
    ///
    /// Every toy example and every real encryption instance. Supply the column with
    /// [`GeneratedMq::into_instance_with_constants`]; for an encryption type that means reading it
    /// out of the published file, because it encodes the planted answer.
    ConstantColumnNotGenerated,
}

impl std::fmt::Display for MqGeneratorError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::EmptySource => write!(f, "the digit source is empty"),
            Self::NotABit { position, byte } => write!(
                f,
                "the digit source holds {:?} at position {}, which is neither '0' nor '1'",
                *byte as char, position
            ),
            Self::WrongConstantCount { found, expected } => {
                write!(f, "{} constant terms for {} polynomials", found, expected)
            }
            Self::BadConstant { polynomial, value } => write!(
                f,
                "polynomial {}'s constant {} is not a coefficient of this field",
                polynomial, value
            ),
            Self::ConstantColumnNotGenerated => write!(
                f,
                "this class does not take its constant column from the digit stream; supply it"
            ),
        }
    }
}

impl std::error::Error for MqGeneratorError {}

/// The `0`/`1` character stream coefficients are read from.
///
/// Borrowed rather than owned because the published stream is 200 MB and a test's is a dozen bytes;
/// neither wants a copy. Validated on construction, so a read cannot fail later.
#[derive(Clone, Copy, Debug)]
pub struct DigitSource<'a> {
    digits: &'a [u8],
}

impl<'a> DigitSource<'a> {
    /// A source over ASCII `0`/`1` characters.
    ///
    /// # Errors
    /// [`MqGeneratorError::EmptySource`] or [`MqGeneratorError::NotABit`].
    pub fn new(digits: &'a [u8]) -> Result<Self, MqGeneratorError> {
        if digits.is_empty() {
            return Err(MqGeneratorError::EmptySource);
        }
        if let Some((position, &byte)) = digits
            .iter()
            .enumerate()
            .find(|(_, &b)| b != b'0' && b != b'1')
        {
            return Err(MqGeneratorError::NotABit { position, byte });
        }
        Ok(Self { digits })
    }

    /// How many characters the walk wraps at.
    ///
    /// The published `PI` is [`PI_LENGTH`] characters and that is the modulus the challenge's own
    /// generator uses. A synthetic source wraps at its own length, which is what makes the walk
    /// testable at a dozen bytes instead of two hundred million.
    pub fn len(&self) -> usize {
        self.digits.len()
    }

    /// Whether the source is empty, which [`Self::new`] has already refused.
    pub fn is_empty(&self) -> bool {
        self.digits.is_empty()
    }

    /// `bits` characters from `position`, most significant first, wrapping at the end.
    ///
    /// The shipped `readPI` indexes a flat array and does not wrap; it cannot, because the only
    /// positions it is called at are below the length. A GF(2^8) coefficient reads at `pos + 4`,
    /// which can cross the end for the last three positions of the stream — one position in
    /// 50 million, and what the C program would read there is whatever follows its buffer. Wrapping
    /// is the defined choice, recorded here so a divergence at that boundary is explainable rather
    /// than mysterious.
    fn read(&self, position: usize, bits: u32) -> u64 {
        let mut value = 0u64;
        for offset in 0..bits as usize {
            let index = (position + offset) % self.digits.len();
            value = (value << 1) | u64::from(self.digits[index] == b'1');
        }
        value
    }
}

/// An instance as the generator produces it.
///
/// Complete for a real signature challenge, and one column per polynomial short otherwise. The
/// missing column is not an omission to be filled in with a zero: for the encryption types it **is**
/// the planted answer (`YDHTS15` Algorithm 1 Step 4 chooses the constants so a secret point is a
/// root), and a system built with zeros there is a different system with different solutions and
/// different Gröbner behaviour.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct GeneratedMq {
    /// What it was generated from.
    pub parameters: MqParameters,

    /// `m` rows of `coefficients_per_polynomial() - 1` values, in file order, **unreduced**.
    ///
    /// Unreduced for the same reason [`MqInstance`] keeps file order and raw values: a GF(31)
    /// coefficient is five raw bits of the stream, so `31` occurs and is congruent to zero, and
    /// normalizing here would hide a real bias in the published instances.
    pub non_constant: Vec<Vec<u64>>,

    /// One constant per polynomial, when [`ConstantColumn::FromStream`] generated them.
    ///
    /// `None` under [`ConstantColumn::External`], which is the API saying the thing §7.4 says in
    /// prose: for those classes the column is not derivable and a caller has to bring it.
    pub constants: Option<Vec<u64>>,
}

impl GeneratedMq {
    /// Walk the digit stream for this instance's coefficients.
    pub fn new(parameters: MqParameters, pi: DigitSource<'_>) -> Self {
        let field = parameters.mq_type.field();
        let interval = parameters.interval();
        let reads = parameters.reads_per_polynomial();
        let mut position = parameters.start() % pi.len();

        let mut non_constant = Vec::with_capacity(parameters.polynomials);
        let mut constants = Vec::with_capacity(parameters.polynomials);
        for _ in 0..parameters.polynomials {
            let mut row = Vec::with_capacity(reads);
            for _ in 0..reads {
                row.push(next_coefficient(
                    field,
                    parameters.thirty_one,
                    pi,
                    &mut position,
                    interval,
                ));
            }
            // The constant monomial is last in descending grevlex, so when the stream supplies it,
            // it is the last read of the polynomial.
            if parameters.constant_column == ConstantColumn::FromStream {
                constants.push(row.pop().expect("mon >= 1 reads"));
            }
            non_constant.push(row);
        }
        Self {
            parameters,
            non_constant,
            constants: (parameters.constant_column == ConstantColumn::FromStream)
                .then_some(constants),
        }
    }

    /// The instance, using the constants the stream supplied.
    ///
    /// # Errors
    /// [`MqGeneratorError::ConstantColumnNotGenerated`] under [`ConstantColumn::External`], where
    /// the column does not exist to use — [`Self::into_instance_with_constants`] is the way in.
    pub fn into_instance(self) -> Result<MqInstance, MqGeneratorError> {
        let constants = self
            .constants
            .clone()
            .ok_or(MqGeneratorError::ConstantColumnNotGenerated)?;
        self.into_instance_with_constants(&constants)
    }

    /// The same instance as an [`MqInstance`], with the constant column supplied by the caller.
    ///
    /// One constant per polynomial, appended in file order — the constant monomial is **last** in
    /// descending grevlex, which is the layout `docs/research/fukuoka-mq.md` §2.1 establishes from
    /// the challenge's own `format` page and `util.m`.
    ///
    /// The resulting instance declares the field with no modulus, exactly as a GF(31) or GF(2) file
    /// does. A GF(2^8) one carries the published modulus, because a file naming the field without
    /// naming its polynomial can still only mean that one, and
    /// [`MqInstance::check_coefficient_field`] is what compares it against a coefficient type.
    ///
    /// # Errors
    /// [`MqGeneratorError::WrongConstantCount`] or [`MqGeneratorError::BadConstant`].
    pub fn into_instance_with_constants(
        self,
        constants: &[u64],
    ) -> Result<MqInstance, MqGeneratorError> {
        if constants.len() != self.parameters.polynomials {
            return Err(MqGeneratorError::WrongConstantCount {
                found: constants.len(),
                expected: self.parameters.polynomials,
            });
        }
        let field = self.parameters.mq_type.field();
        let coefficients = self
            .non_constant
            .into_iter()
            .zip(constants)
            .enumerate()
            .map(|(polynomial, (mut row, &constant))| {
                if constant > field.max_coefficient() {
                    return Err(MqGeneratorError::BadConstant {
                        polynomial,
                        value: constant,
                    });
                }
                row.push(constant);
                Ok(row)
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(MqInstance {
            field,
            modulus: match field {
                MqField::Gf256 => Some(MqField::PUBLISHED_GF256_MODULUS),
                MqField::Gf2 | MqField::Gf31 => None,
            },
            variables: self.parameters.variables,
            polynomials: self.parameters.polynomials,
            seed: Some(self.parameters.seed),
            order: "graded reverse lex order".to_string(),
            coefficients,
        })
    }

    /// Where a parsed instance disagrees with the generated coefficients, as `(polynomial, index)`.
    ///
    /// The constant column is compared **exactly when it was generated**: under
    /// [`ConstantColumn::FromStream`] a disagreement there is as real as any other, and under
    /// [`ConstantColumn::External`] there is nothing to compare it against. Empty means every
    /// coefficient this class can produce agrees, which is the check
    /// `docs/research/fukuoka-mq.md` §7.2 and §7.3 ran across all six types and three classes.
    ///
    /// A shape mismatch — a different `n`, `m`, or coefficient count — is reported as a
    /// disagreement at the first index that does not exist rather than silently compared pairwise.
    pub fn disagreements(&self, instance: &MqInstance) -> Vec<(usize, usize)> {
        let mut out = Vec::new();
        if instance.variables != self.parameters.variables
            || instance.polynomials != self.parameters.polynomials
        {
            return vec![(0, 0)];
        }
        let constant_index = self.parameters.coefficients_per_polynomial() - 1;
        for (polynomial, (generated, parsed)) in self
            .non_constant
            .iter()
            .zip(&instance.coefficients)
            .enumerate()
        {
            for (index, value) in generated.iter().enumerate() {
                if parsed.get(index) != Some(value) {
                    out.push((polynomial, index));
                }
            }
            if let Some(constants) = &self.constants {
                if parsed.get(constant_index) != constants.get(polynomial) {
                    out.push((polynomial, constant_index));
                }
            }
        }
        out
    }
}

/// One coefficient, advancing `position` by `interval` for every read it consumes.
///
/// Under [`ThirtyOne::Rejected`] a GF(31) read of `31` is discarded and retried, and **the discarded
/// read still advances the position** — which is what makes the two policies differ in every later
/// coefficient rather than only in the rejected ones.
///
/// The retry is bounded by the stream length because stepping by a fixed interval modulo that
/// length cycles within it: a stream where every reachable position reads `31` would spin forever,
/// as the shipped C program does, and returning the value is the defined alternative. No published
/// instance comes near it — `31` is one value in thirty-two.
fn next_coefficient(
    field: MqField,
    thirty_one: ThirtyOne,
    pi: DigitSource<'_>,
    position: &mut usize,
    interval: usize,
) -> u64 {
    for _ in 0..pi.len() {
        let value = coefficient_at(field, pi, *position);
        *position = (*position + interval) % pi.len();
        let rejected = thirty_one == ThirtyOne::Rejected && field == MqField::Gf31 && value == 31;
        if !rejected {
            return value;
        }
    }
    coefficient_at(field, pi, *position)
}

/// One coefficient, read at `position` in the field's own width.
///
/// | field | read | value |
/// |---|---|---|
/// | GF(2) | 1 bit | the bit |
/// | GF(2^8) | two 4-bit nibbles, at `pos` and `pos + 4` | `hi * 16 + lo`, which is the hex byte the file prints |
/// | GF(31) | 5 bits | `0..=31`, **unreduced**, because `31` occurs in the published data |
fn coefficient_at(field: MqField, pi: DigitSource<'_>, position: usize) -> u64 {
    match field {
        MqField::Gf2 => pi.read(position, 1),
        MqField::Gf256 => pi.read(position, 4) * 16 + pi.read(position + 4, 4),
        MqField::Gf31 => pi.read(position, 5),
    }
}

/// Load a digit stream from a file, checking its length against [`PI_LENGTH`].
///
/// Separate from the checksum, which `tools/fetch-pi.sh` verifies on download: a 200 MB SHA-256 per
/// test run would dominate the test, and the length catches the failure that actually happens,
/// which is a truncated or partial fetch.
///
/// # Errors
/// The `io::Error` of reading the path.
pub fn read_pi(path: impl AsRef<std::path::Path>) -> std::io::Result<Vec<u8>> {
    let bytes = std::fs::read(path)?;
    let digits: Vec<u8> = bytes
        .into_iter()
        .filter(|b| !b.is_ascii_whitespace())
        .collect();
    if digits.len() != PI_LENGTH {
        return Err(std::io::Error::new(
            std::io::ErrorKind::InvalidData,
            format!(
                "PI holds {} digits, not the published {}; re-run tools/fetch-pi.sh",
                digits.len(),
                PI_LENGTH
            ),
        ));
    }
    Ok(digits)
}

/// Where `tools/fetch-pi.sh` puts `PI`, and where the ignored tests look for it.
pub fn pi_path() -> std::path::PathBuf {
    std::path::PathBuf::from(
        std::env::var("ZEEBRA_MQ_DIR").unwrap_or_else(|_| "research/instances/mq".to_string()),
    )
    .join("PI")
}

/// What a generated instance can and cannot replace, as a value rather than as prose.
///
/// Returned by nothing; it exists so the fact that bounds this module is in the API surface and not
/// only in a doc comment.
pub const WHAT_THE_WALK_CANNOT_PRODUCE: &str =
    "an encryption instance's constant column, which YDHTS15 Algorithm 1 Step 4 computes from the \
     secret planted answer; a real signature challenge has no such gap and is reproducible in full";

#[cfg(test)]
mod tests {
    use super::{
        coefficient_at, ConstantColumn, DigitSource, GeneratedMq, MqGeneratorError, MqParameters,
        MqType, ThirtyOne, PI_LENGTH, PI_SHA256,
    };
    use crate::grobner::research::mq::{MqField, MqInstance};

    /// A synthetic stream: `len` characters whose `i`th is `1` exactly when `i` is in `ones`.
    fn source(len: usize, ones: &[usize]) -> Vec<u8> {
        let mut digits = vec![b'0'; len];
        for &i in ones {
            digits[i] = b'1';
        }
        digits
    }

    /// `start` and `interval` are the challenge's own formulas, type number included.
    #[test]
    fn test_the_walk_parameters_are_the_published_formulas() {
        let third = MqParameters::encryption(MqType::III, 10, 0);
        assert_eq!(third.start(), 30, "type * n");
        assert_eq!(third.interval(), 103, "(seed + n) * 10 + type");
        assert_eq!(third.polynomials, 20, "m = 2n for an encryption type");

        let sixth = MqParameters::signature(MqType::VI, 16, 0);
        assert_eq!(sixth.variables, 24, "floor(1.5 * 16)");
        assert_eq!(sixth.start(), 144);
        assert_eq!(sixth.interval(), 246);

        // The seed moves the stride and nothing else, which is why one instance's walk says nothing
        // about another's.
        let seeded = MqParameters::encryption(MqType::III, 10, 3);
        assert_eq!(seeded.start(), 30);
        assert_eq!(seeded.interval(), 133);
    }

    /// `n = m * 1.5` truncates, so `m = 17` is 25 variables and not 26.
    #[test]
    fn test_the_signature_variable_count_truncates() {
        assert_eq!(MqParameters::signature(MqType::VI, 17, 0).variables, 25);
        assert_eq!(MqParameters::signature(MqType::VI, 16, 0).variables, 24);
        assert_eq!(MqParameters::signature(MqType::V, 35, 0).variables, 52);
    }

    /// A GF(31) coefficient is five raw bits, so `31` is produced rather than rejected.
    ///
    /// The first of §7.3's two corrections to the shipped generator: its `while (coef == 31)` loop
    /// both substitutes a different value *and* advances the position, which is why removing it
    /// changes 1 214 of 1 300 coefficients rather than 40.
    #[test]
    fn test_a_gf31_coefficient_is_five_unreduced_bits() {
        let digits = source(64, &[0, 1, 2, 3, 4]);
        let pi = DigitSource::new(&digits).expect("a valid stream");
        assert_eq!(
            coefficient_at(MqField::Gf31, pi, 0),
            31,
            "five one bits, and 31 is congruent to zero rather than out of range"
        );
        assert_eq!(
            coefficient_at(MqField::Gf31, pi, 4),
            16,
            "1 followed by 0000"
        );
        assert_eq!(coefficient_at(MqField::Gf31, pi, 8), 0);
    }

    /// A GF(2) coefficient is one bit and a GF(2^8) one is two nibbles read as a hex byte.
    #[test]
    fn test_the_other_two_fields_read_their_own_widths() {
        // 0xA3 = 1010 0011.
        let digits = source(32, &[0, 2, 6, 7]);
        let pi = DigitSource::new(&digits).expect("a valid stream");
        assert_eq!(coefficient_at(MqField::Gf256, pi, 0), 0xA3);
        assert_eq!(coefficient_at(MqField::Gf2, pi, 0), 1);
        assert_eq!(coefficient_at(MqField::Gf2, pi, 1), 0);
    }

    /// The position advances by one interval per coefficient, not by the bits the field consumed.
    ///
    /// A GF(2^8) coefficient reads eight bits and still steps once, which is the detail that
    /// desynchronizes a reimplementation reading `pos += 8` and makes every later coefficient wrong.
    #[test]
    fn test_a_binary_field_coefficient_advances_by_one_interval_not_eight_bits() {
        let parameters = MqParameters {
            mq_type: MqType::V,
            variables: 1,
            polynomials: 2,
            seed: 0,
            thirty_one: ThirtyOne::Kept,
            constant_column: ConstantColumn::External,
        };
        assert_eq!(parameters.interval(), 15, "(0 + 1) * 10 + 5");
        // Three coefficients per polynomial at n = 1: x^2, x, 1 — so two reads each.
        let digits = source(64, &[5, 20, 35, 50]);
        let pi = DigitSource::new(&digits).expect("a valid stream");
        let generated = GeneratedMq::new(parameters, pi);
        assert_eq!(generated.non_constant.len(), 2);
        assert_eq!(
            generated.non_constant[0].len(),
            2,
            "mon - 1 reads: the constant is not generated"
        );
        // start = 5, then 20, 35, 50 — each a single one bit in the high nibble's top position.
        assert_eq!(generated.non_constant[0], vec![0x80, 0x80]);
        assert_eq!(generated.non_constant[1], vec![0x80, 0x80]);
    }

    /// The walk carries across polynomials rather than restarting at `start` for each.
    #[test]
    fn test_the_position_carries_across_polynomials() {
        let parameters = MqParameters {
            mq_type: MqType::VI,
            variables: 1,
            polynomials: 2,
            seed: 0,
            thirty_one: ThirtyOne::Kept,
            constant_column: ConstantColumn::External,
        };
        assert_eq!(parameters.start(), 6);
        assert_eq!(parameters.interval(), 16);
        // One bit at the start of each of the first four strides: 6, 22, 38, 54.
        let digits = source(128, &[22, 54]);
        let pi = DigitSource::new(&digits).expect("a valid stream");
        let generated = GeneratedMq::new(parameters, pi);
        assert_eq!(
            (&generated.non_constant[0], &generated.non_constant[1]),
            (&vec![0, 16], &vec![0, 16]),
            "positions 6, 22 for the first polynomial and 38, 54 for the second"
        );
    }

    /// The walk wraps at the source length, so a stride past the end continues from the beginning.
    #[test]
    fn test_the_walk_wraps_at_the_end_of_the_stream() {
        let parameters = MqParameters {
            mq_type: MqType::VI,
            variables: 1,
            polynomials: 1,
            seed: 0,
            thirty_one: ThirtyOne::Kept,
            constant_column: ConstantColumn::External,
        };
        // start 6, interval 16, length 20: the second read is at 22 % 20 = 2.
        let digits = source(20, &[2, 3, 4, 5, 6]);
        let pi = DigitSource::new(&digits).expect("a valid stream");
        let generated = GeneratedMq::new(parameters, pi);
        assert_eq!(
            generated.non_constant[0][0], 0b10000,
            "positions 6..=10, of which only 6 is set"
        );
        assert_eq!(
            generated.non_constant[0][1], 0b11111,
            "the stride lands on 22, which wraps to 2, where all five are set"
        );
    }

    /// Every polynomial is one coefficient short of a complete instance, by construction.
    #[test]
    fn test_a_generated_instance_is_one_column_short_per_polynomial() {
        let parameters = MqParameters::encryption(MqType::III, 10, 0);
        let digits = source(4096, &[7, 11, 13]);
        let pi = DigitSource::new(&digits).expect("a valid stream");
        let generated = GeneratedMq::new(parameters, pi);
        assert_eq!(generated.non_constant.len(), 20);
        for row in &generated.non_constant {
            assert_eq!(row.len(), MqInstance::coefficients_per_polynomial(10) - 1);
            assert_eq!(row.len(), 65, "66 monomials at n = 10, less the constant");
        }
    }

    /// Supplying the constants completes the instance, and it parses as the file format it imitates.
    #[test]
    fn test_the_caller_supplied_constants_complete_the_instance() {
        let parameters = MqParameters {
            mq_type: MqType::VI,
            variables: 2,
            polynomials: 2,
            seed: 0,
            thirty_one: ThirtyOne::Kept,
            constant_column: ConstantColumn::External,
        };
        let digits = source(256, &[1, 2, 3]);
        let pi = DigitSource::new(&digits).expect("a valid stream");
        let generated = GeneratedMq::new(parameters, pi);
        let instance = generated
            .into_instance_with_constants(&[7, 11])
            .expect("two constants for two polynomials");
        assert_eq!(instance.field, MqField::Gf31);
        assert_eq!(instance.seed, Some(0));
        assert_eq!(instance.coefficients.len(), 2);
        for (row, constant) in instance.coefficients.iter().zip([7, 11]) {
            assert_eq!(row.len(), MqInstance::coefficients_per_polynomial(2));
            assert_eq!(
                row.last().copied(),
                Some(constant),
                "the constant monomial is last in descending grevlex"
            );
        }
    }

    /// The wrong number of constants is refused rather than padded or truncated.
    #[test]
    fn test_a_constant_count_that_does_not_match_m_is_refused() {
        let parameters = MqParameters::encryption(MqType::III, 10, 0);
        let digits = source(4096, &[7]);
        let pi = DigitSource::new(&digits).expect("a valid stream");
        let generated = GeneratedMq::new(parameters, pi);
        match generated.into_instance_with_constants(&[0; 19]) {
            Err(MqGeneratorError::WrongConstantCount { found, expected }) => {
                assert_eq!((found, expected), (19, 20));
            }
            other => panic!("expected a count refusal, got {:?}", other),
        }
    }

    /// A constant outside the field's token range is refused, `31` over GF(31) excepted.
    #[test]
    fn test_a_constant_outside_the_fields_range_is_refused() {
        let parameters = MqParameters {
            mq_type: MqType::VI,
            variables: 2,
            polynomials: 1,
            seed: 0,
            thirty_one: ThirtyOne::Kept,
            constant_column: ConstantColumn::External,
        };
        let digits = source(256, &[1]);
        let pi = DigitSource::new(&digits).expect("a valid stream");
        let generated = GeneratedMq::new(parameters, pi);
        assert!(
            generated
                .clone()
                .into_instance_with_constants(&[31])
                .is_ok(),
            "31 occurs in the published GF(31) files and is congruent to zero"
        );
        match generated.into_instance_with_constants(&[32]) {
            Err(MqGeneratorError::BadConstant { polynomial, value }) => {
                assert_eq!((polynomial, value), (0, 32));
            }
            other => panic!("expected a bad constant, got {:?}", other),
        }
    }

    /// A stream holding anything but `0` and `1` is reported rather than read as one bits.
    ///
    /// The shipped `readPI` treats every non-`'0'` byte as a one, so a truncated download or a file
    /// with a trailing newline inside it would produce plausible coefficients from nothing.
    #[test]
    fn test_a_stream_that_is_not_bits_is_refused_with_its_position() {
        match DigitSource::new(b"0101x1") {
            Err(MqGeneratorError::NotABit { position, byte }) => {
                assert_eq!((position, byte), (4, b'x'));
            }
            other => panic!("expected a non-bit refusal, got {:?}", other),
        }
        assert_eq!(
            DigitSource::new(b"").err(),
            Some(MqGeneratorError::EmptySource)
        );
    }

    /// `disagreements` compares every non-constant coefficient and ignores the constant column.
    #[test]
    fn test_disagreements_ignores_the_constant_and_finds_everything_else() {
        let parameters = MqParameters {
            mq_type: MqType::VI,
            variables: 2,
            polynomials: 1,
            seed: 0,
            thirty_one: ThirtyOne::Kept,
            constant_column: ConstantColumn::External,
        };
        let digits = source(256, &[1, 2, 3]);
        let pi = DigitSource::new(&digits).expect("a valid stream");
        let generated = GeneratedMq::new(parameters, pi);

        let mut instance = generated
            .clone()
            .into_instance_with_constants(&[0])
            .expect("one constant");
        assert!(
            generated.disagreements(&instance).is_empty(),
            "a generated instance agrees with itself"
        );

        // A different constant is not a disagreement; a different coefficient is.
        let last = instance.coefficients[0].len() - 1;
        instance.coefficients[0][last] = 29;
        assert!(generated.disagreements(&instance).is_empty());
        instance.coefficients[0][2] += 1;
        assert_eq!(generated.disagreements(&instance), vec![(0, 2)]);
    }

    /// A shape mismatch is a disagreement rather than a pairwise comparison of unequal rows.
    #[test]
    fn test_a_different_dimension_is_a_disagreement_and_not_a_short_comparison() {
        let digits = source(4096, &[7, 11]);
        let pi = DigitSource::new(&digits).expect("a valid stream");
        let generated = GeneratedMq::new(MqParameters::encryption(MqType::III, 10, 0), pi);
        let other = GeneratedMq::new(MqParameters::encryption(MqType::III, 15, 0), pi)
            .into_instance_with_constants(&[0; 30])
            .expect("thirty constants");
        assert_eq!(generated.disagreements(&other), vec![(0, 0)]);
    }

    /// The type number is the one the challenge uses, and it round-trips.
    #[test]
    fn test_the_type_numbers_are_the_challenges_own() {
        for (number, mq_type, field, signature) in [
            (1, MqType::I, MqField::Gf2, false),
            (2, MqType::II, MqField::Gf256, false),
            (3, MqType::III, MqField::Gf31, false),
            (4, MqType::IV, MqField::Gf2, true),
            (5, MqType::V, MqField::Gf256, true),
            (6, MqType::VI, MqField::Gf31, true),
        ] {
            assert_eq!(mq_type.number(), number);
            assert_eq!(MqType::from_number(number), Some(mq_type));
            assert_eq!(mq_type.field(), field);
            assert_eq!(mq_type.is_signature(), signature);
        }
        assert_eq!(MqType::from_number(0), None);
        assert_eq!(MqType::from_number(7), None);
    }

    /// A published file is reproduced, coefficient for coefficient, from `(type, n, m, seed)`.
    ///
    /// The claim this module exists to make, against the data rather than against a synthetic
    /// stream: "exact" means every coefficient, not a distributional match. All three classes of
    /// §7.3's table, both GF(31) and GF(2^8), both shapes, and five seeds at the smallest size.
    ///
    /// The real signature rows are the strongest of them, because their constant column is compared
    /// too — so a pass there is the whole file reproduced from three integers.
    ///
    /// `#[ignore]`d because it needs `PI` and the instance files, neither of which is
    /// redistributable:
    ///
    /// ```text
    /// tools/fetch-pi.sh && tools/fetch-mq-challenge.sh
    /// cargo test --release -- --ignored a_published_instance_is_generated
    /// ```
    #[test]
    #[ignore = "needs tools/fetch-pi.sh and tools/fetch-mq-challenge.sh"]
    fn test_a_published_instance_is_generated_coefficient_for_coefficient() {
        let directory = super::pi_path()
            .parent()
            .expect("the instance directory")
            .to_path_buf();
        let digits =
            super::read_pi(super::pi_path()).expect("PI, fetched and the published length");
        let pi = DigitSource::new(&digits).expect("200 million zeros and ones");

        // Which class each file belongs to is measured, not derived from the type: see `ThirtyOne`
        // and `ConstantColumn`. Toy examples keep `31` and bring their own constants; the real
        // challenges resample it, and the signature ones also generate the constant column.
        let toy = |mq_type, seed| (mq_type, seed, ThirtyOne::Kept, ConstantColumn::External);
        let real_encryption =
            |mq_type| (mq_type, 0u64, ThirtyOne::Rejected, ConstantColumn::External);
        let real_signature = |mq_type| {
            (
                mq_type,
                0u64,
                ThirtyOne::Rejected,
                ConstantColumn::FromStream,
            )
        };
        let files = [
            ("ToyExample-type3-n10-seed0", toy(MqType::III, 0)),
            ("ToyExample-type3-n10-seed1", toy(MqType::III, 1)),
            ("ToyExample-type3-n10-seed2", toy(MqType::III, 2)),
            ("ToyExample-type3-n10-seed3", toy(MqType::III, 3)),
            ("ToyExample-type3-n10-seed4", toy(MqType::III, 4)),
            ("ToyExample-type3-n15-seed0", toy(MqType::III, 0)),
            ("ToyExample-type3-n20-seed0", toy(MqType::III, 0)),
            ("ToyExample-type6-n10-seed0", toy(MqType::VI, 0)),
            ("ToyExample-type6-n15-seed0", toy(MqType::VI, 0)),
            ("challenge-6-16-0", real_signature(MqType::VI)),
            ("challenge-5-16-0", real_signature(MqType::V)),
            ("challenge-3-34-0", real_encryption(MqType::III)),
        ];

        let mut checked = 0usize;
        let mut constants_checked = 0usize;
        for (name, (mq_type, seed, thirty_one, constant_column)) in files {
            let path = directory.join(name);
            let text = match std::fs::read_to_string(&path) {
                Ok(text) => text,
                Err(error) => panic!("{}: {error}; run the two fetch scripts", path.display()),
            };
            let instance = MqInstance::parse(&text).expect("a published file parses");
            assert_eq!(
                instance.field,
                mq_type.field(),
                "{name}: the header's field must be the type's"
            );
            assert_eq!(instance.seed, Some(seed), "{name}: the header's seed");

            // `n` and `m` from the header rather than from the type's rule: the published challenge
            // obeys `n = floor(1.5m)` and the type IV-VI toy examples at `n = 5` do not.
            let parameters = MqParameters {
                mq_type,
                variables: instance.variables,
                polynomials: instance.polynomials,
                seed,
                thirty_one,
                constant_column,
            };
            let generated = GeneratedMq::new(parameters, pi);
            let comparable = instance.polynomials * parameters.reads_per_polynomial();
            let disagreements = generated.disagreements(&instance);
            assert!(
                disagreements.is_empty(),
                "{name}: {} of {comparable} coefficients disagree, first at {:?}",
                disagreements.len(),
                disagreements.first()
            );
            if constant_column == ConstantColumn::FromStream {
                // The whole file, from three integers: nothing was taken from it but `n` and `m`.
                let rebuilt = generated
                    .clone()
                    .into_instance()
                    .expect("the stream supplied the constants");
                assert_eq!(
                    rebuilt.coefficients, instance.coefficients,
                    "{name}: a real signature challenge is reproducible in full"
                );
                constants_checked += instance.polynomials;
            }
            checked += comparable;
        }
        assert!(
            checked > 27_000,
            "only {checked} coefficients compared; §7.2 of the note covers 27 530"
        );
        assert_eq!(
            constants_checked, 32,
            "both real signature challenges' constant columns, 16 polynomials each"
        );
    }

    /// The real challenges' parameters follow from `(type, index, seed)` and the type's own rule.
    #[test]
    fn test_a_challenges_parameters_follow_from_its_published_index() {
        // Type III is indexed by `n`, and the challenge publishes `n = 34..=53`.
        let encryption = MqParameters::challenge(MqType::III, 34, 0);
        assert_eq!((encryption.variables, encryption.polynomials), (34, 68));
        assert_eq!(encryption.thirty_one, ThirtyOne::Rejected);
        assert_eq!(
            encryption.constant_column,
            ConstantColumn::External,
            "YDHTS15 Algorithm 1 Step 4 computes an encryption constant from the planted answer"
        );

        // Type VI is indexed by `m`, and `m = 16` is the `n = 24` instance #454 imported.
        let signature = MqParameters::challenge(MqType::VI, 16, 0);
        assert_eq!((signature.variables, signature.polynomials), (24, 16));
        assert_eq!(signature.thirty_one, ThirtyOne::Rejected);
        assert_eq!(signature.constant_column, ConstantColumn::FromStream);
        assert_eq!(
            signature.reads_per_polynomial(),
            signature.coefficients_per_polynomial(),
            "the constant is the last read rather than a column to supply"
        );
    }

    /// Without a generated constant column, `into_instance` refuses rather than defaulting one.
    #[test]
    fn test_an_external_constant_column_cannot_be_invented() {
        let digits = source(4096, &[7, 11]);
        let pi = DigitSource::new(&digits).expect("a valid stream");
        let generated = GeneratedMq::new(MqParameters::challenge(MqType::III, 10, 0), pi);
        assert_eq!(generated.constants, None);
        assert_eq!(
            generated.into_instance().err(),
            Some(MqGeneratorError::ConstantColumnNotGenerated)
        );
    }

    /// A stream-supplied constant column is the last read of each polynomial, not an extra stride.
    #[test]
    fn test_a_generated_constant_column_is_the_last_read_of_the_polynomial() {
        let external = MqParameters {
            mq_type: MqType::VI,
            variables: 2,
            polynomials: 2,
            seed: 0,
            thirty_one: ThirtyOne::Rejected,
            constant_column: ConstantColumn::External,
        };
        let from_stream = external.with_constants_from_stream();
        assert_eq!(external.reads_per_polynomial(), 5, "mon - 1 at n = 2");
        assert_eq!(from_stream.reads_per_polynomial(), 6, "mon at n = 2");

        // Dense and aperiodic against the stride: every seventh digit is a one, the stride is 26,
        // and 26 is coprime to 7 — so two walks one read apart read different values rather than
        // coinciding on a sparse stream.
        let ones: Vec<usize> = (0..512).filter(|i| i % 7 == 0).collect();
        let digits = source(512, &ones);
        let pi = DigitSource::new(&digits).expect("a valid stream");
        let generated = GeneratedMq::new(from_stream, pi);
        let constants = generated.constants.clone().expect("generated");
        assert_eq!(constants.len(), 2);

        // The walk is one read longer per polynomial, so the second polynomial's coefficients are
        // *not* the external variant's — this is the difference that showed up at (1, 0) against
        // `challenge-6-16-0`.
        let shorter = GeneratedMq::new(external, pi);
        assert_eq!(
            shorter.non_constant[0], generated.non_constant[0],
            "the first polynomial is unaffected"
        );
        assert_ne!(
            shorter.non_constant[1], generated.non_constant[1],
            "every later polynomial is shifted by the extra read"
        );

        let instance = generated.into_instance().expect("constants were generated");
        for (row, constant) in instance.coefficients.iter().zip(constants) {
            assert_eq!(row.last().copied(), Some(constant));
        }
    }

    /// Rejecting `31` substitutes the *next* read and shifts every coefficient after it.
    ///
    /// Both halves matter. The value changes, and because the discarded read also advances the
    /// position, so does everything downstream — which is why the two policies disagree on almost
    /// every coefficient rather than only on the rejected ones.
    #[test]
    fn test_rejecting_thirty_one_resamples_and_advances() {
        let parameters = MqParameters {
            mq_type: MqType::VI,
            variables: 1,
            polynomials: 1,
            seed: 0,
            thirty_one: ThirtyOne::Kept,
            constant_column: ConstantColumn::External,
        };
        assert_eq!((parameters.start(), parameters.interval()), (6, 16));
        // Five ones at 6..=10 make the first read 31; the next stride, at 22, reads 0.
        let digits = source(64, &[6, 7, 8, 9, 10]);
        let pi = DigitSource::new(&digits).expect("a valid stream");

        let kept = GeneratedMq::new(parameters, pi);
        assert_eq!(kept.non_constant[0], vec![31, 0], "31 is a legal token");

        let rejected = GeneratedMq::new(parameters.rejecting_thirty_one(), pi);
        assert_eq!(
            rejected.non_constant[0],
            vec![0, 0],
            "the 31 is discarded, its stride is still taken, and the walk is one read further on"
        );
    }

    /// The policy is inert for the two fields with no out-of-range value.
    #[test]
    fn test_the_rejection_policy_does_not_touch_the_binary_fields() {
        for mq_type in [MqType::I, MqType::II, MqType::IV, MqType::V] {
            let parameters = MqParameters {
                mq_type,
                variables: 2,
                polynomials: 2,
                seed: 0,
                thirty_one: ThirtyOne::Kept,
                constant_column: ConstantColumn::External,
            };
            let digits = source(512, &[3, 5, 7, 11, 13, 17, 19, 23]);
            let pi = DigitSource::new(&digits).expect("a valid stream");
            assert_eq!(
                GeneratedMq::new(parameters, pi).non_constant,
                GeneratedMq::new(parameters.rejecting_thirty_one(), pi).non_constant,
                "{:?}: a byte and a bit are always in range",
                mq_type
            );
        }
    }

    /// The published constants are what this module records about `PI` itself.
    #[test]
    fn test_the_published_stream_constants_are_recorded() {
        assert_eq!(PI_LENGTH, 200_000_000);
        assert_eq!(PI_SHA256.len(), 64);
        assert!(PI_SHA256.chars().all(|c| c.is_ascii_hexdigit()));
    }
}
