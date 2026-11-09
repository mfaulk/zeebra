//! Rescue-Prime over `p = 2^64 − 59`, the 2021–2022 EF ZK Hash bounty instances.
//!
//! Specified in Aly, Ashur, Ben-Sasson, Dhooghe and Szepieniec, *Design of Symmetric-Key Primitives
//! for Advanced Cryptographic Protocols*, ToSC 2020 №3. The *instances* are the Ethereum
//! Foundation's bounty set, whose reference implementation is `krypto/zkfriendlyhashzoo` at commit
//! `b9c09d5a6302725a65ff59e4219d1beb4c524154` (MIT), read 2026-11-09 from
//! <https://extgit.iaik.tugraz.at/krypto/zkfriendlyhashzoo>. The parameter table and the published
//! records are `docs/research/ef-cryptanalysis.md` §4.2.
//!
//! # Three of the five instances are `m = 2`
//!
//! #203 and #71 both record Rescue-Prime as `m = 3`. The reference says otherwise: `EASY1` and
//! `HARD1` are `t = 3`, and `EASY2`, `MEDIUM` and `HARD2` are `t = 2`. All five are carried here,
//! because an `m = 3` claim measured on an `m = 2` instance would be the #197 failure again.
//!
//! # The inverse S-box exponent is computed, not transcribed
//!
//! A Rescue round is `x^α` then an affine layer then `x^{1/α}` then another affine layer, and
//! `1/α` means `α^{-1} mod (p − 1)` — an exponent in the *multiplicative group's* order, not in
//! `p`. [`RescuePrime::alpha_inverse`] derives it from the field's own order and a test checks that
//! `x^α` and `x^{α^{-1}}` are mutually inverse on actual field elements, rather than trusting a
//! copied constant. For `α = 3` and `p = 2^64 − 59` it is `12297829382473034371`, which differs in
//! its low digits from Anemoi's `12297829382473034175` at `p = 2^64 − 353` — two numbers a glance
//! cannot tell apart.
//!
//! # Why the constants are transcribed here and derived in `feistel_mimc`
//!
//! The reference *tabulates* Rescue-Prime's MDS matrices and round constants and *derives*
//! Feistel-MiMC's. Neither choice is this crate's; each module follows its primitive. The
//! transcription lives in `research/rescue-prime/bounty-constants.txt` with the source file's
//! SHA-256 in its header, and the check that it is right is the reference's own known-answer tests,
//! reproduced for all five instances.

use std::fmt::{Display, Formatter};

use crate::{integers::mod_inverse_u128, FiniteField, KnownOrder};

/// `2^64 - 59`, the prime every 2021–2022 bounty instance is over.
pub const RESCUE_PRIME_PRIME: u64 = 18_446_744_073_709_551_557;

/// The transcribed MDS matrices and round constants.
pub const BOUNTY_CONSTANTS: &str =
    include_str!("../../../research/rescue-prime/bounty-constants.txt");

/// One of the five bounty instances.
///
/// Named rather than described by `(t, N)` because `(t, N)` does not determine the constants: the
/// two `t = 3` instances share `MDS3` and have different round-constant tables.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum BountyInstance {
    /// `t = 3`, `N = 4`. The only instance in the 2021 programme with a published **executed**
    /// attack: `2^43`, four days.
    Easy1,

    /// `t = 2`, `N = 6`.
    Easy2,

    /// `t = 2`, `N = 7`.
    Medium,

    /// `t = 3`, `N = 5`.
    Hard1,

    /// `t = 2`, `N = 8`.
    Hard2,
}

/// Every bounty instance, in the reference's order.
pub const BOUNTY_INSTANCES: [BountyInstance; 5] = [
    BountyInstance::Easy1,
    BountyInstance::Easy2,
    BountyInstance::Medium,
    BountyInstance::Hard1,
    BountyInstance::Hard2,
];

impl BountyInstance {
    /// The stable tag.
    pub fn tag(&self) -> &'static str {
        match self {
            Self::Easy1 => "easy1",
            Self::Easy2 => "easy2",
            Self::Medium => "medium",
            Self::Hard1 => "hard1",
            Self::Hard2 => "hard2",
        }
    }

    /// The state width `t`, which the specification calls `m`.
    pub fn t(&self) -> usize {
        match self {
            Self::Easy1 | Self::Hard1 => 3,
            Self::Easy2 | Self::Medium | Self::Hard2 => 2,
        }
    }

    /// The specified round count `N`.
    pub fn rounds(&self) -> usize {
        match self {
            Self::Easy1 => 4,
            Self::Easy2 => 6,
            Self::Medium => 7,
            Self::Hard1 => 5,
            Self::Hard2 => 8,
        }
    }

    /// The names of this instance's MDS and round-constant tables in [`BOUNTY_CONSTANTS`].
    fn tables(&self) -> (&'static str, &'static str) {
        match self {
            Self::Easy1 => ("MDS3", "RC_EASY1"),
            Self::Easy2 => ("MDS2", "RC_EASY2"),
            Self::Medium => ("MDS2", "RC_MEDIUM"),
            Self::Hard1 => ("MDS3", "RC_HARD1"),
            Self::Hard2 => ("MDS2", "RC_HARD2"),
        }
    }
}

impl Display for BountyInstance {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.tag())
    }
}

/// The parameters of a Rescue-Prime instance.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct RescuePrimeParameters {
    /// The field modulus.
    pub prime: u64,

    /// The S-box exponent `α = d`. The reference implements 3 and 5; every bounty instance is 3.
    pub alpha: u32,

    /// Which bounty instance the constants come from.
    pub instance: BountyInstance,

    /// The number of rounds `N` to run, at most the instance's own.
    ///
    /// A reduced-round rung truncates the constant table: round `r` consumes rows `2r` and
    /// `2r + 1`, so the first `N` rounds of a longer instance are exactly a shorter run of the same
    /// tables. It is **not** the specified instance, and `is_specified` says so.
    pub rounds: usize,
}

impl RescuePrimeParameters {
    /// The instance as specified.
    pub fn bounty(instance: BountyInstance) -> Self {
        Self {
            prime: RESCUE_PRIME_PRIME,
            alpha: 3,
            instance,
            rounds: instance.rounds(),
        }
    }

    /// The instance truncated to `rounds` rounds.
    pub fn reduced(instance: BountyInstance, rounds: usize) -> Self {
        Self {
            rounds,
            ..Self::bounty(instance)
        }
    }

    /// The state width `t`.
    pub fn t(&self) -> usize {
        self.instance.t()
    }

    /// Whether this is the specified instance rather than a reduced-round rung.
    pub fn is_specified(&self) -> bool {
        self.rounds == self.instance.rounds()
    }
}

impl Display for RescuePrimeParameters {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "p = {}, alpha = {}, t = {}, N = {} ({})",
            self.prime,
            self.alpha,
            self.t(),
            self.rounds,
            self.instance
        )
    }
}

/// Why a Rescue-Prime instance could not be built.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum RescuePrimeError {
    /// The coefficient type's order is not the parameters' prime.
    FieldMismatch {
        /// The prime the parameters name.
        expected: u64,
        /// The field the coefficient type actually is.
        found: String,
    },

    /// An S-box exponent the reference does not implement.
    UnsupportedAlpha {
        /// The requested exponent.
        alpha: u32,
    },

    /// `gcd(α, p − 1) ≠ 1`, so neither `x^α` nor its inverse is a permutation.
    AlphaNotCoprime {
        /// The requested exponent.
        alpha: u32,
        /// The modulus.
        prime: u64,
    },

    /// More rounds than the instance's constant table has rows for.
    ///
    /// Refused rather than extended: there is no published rule for continuing the table, so a
    /// longer run would be a primitive of this module's invention.
    TooManyRounds {
        /// The requested count.
        requested: usize,
        /// The count the table supports.
        available: usize,
    },

    /// A zero-round instance, which is the identity.
    NoRounds,

    /// The fixture could not be read, with the reason.
    Fixture(String),

    /// The requested `const N` is not the model's variable count.
    WrongDimension {
        /// Variables the system has.
        needed: usize,
        /// The dimension it was requested at.
        requested: usize,
    },
}

impl Display for RescuePrimeError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::FieldMismatch { expected, found } => write!(
                f,
                "the parameters are over GF({}) and the coefficient type is {}",
                expected, found
            ),
            Self::UnsupportedAlpha { alpha } => write!(
                f,
                "the reference implements alpha = 3 and alpha = 5; alpha = {} is neither",
                alpha
            ),
            Self::AlphaNotCoprime { alpha, prime } => write!(
                f,
                "alpha = {} is not coprime with {} - 1, so x^alpha is not a permutation",
                alpha, prime
            ),
            Self::TooManyRounds {
                requested,
                available,
            } => write!(
                f,
                "{} rounds were requested and the published constant table supports {}; there is \
                 no published rule for extending it",
                requested, available
            ),
            Self::NoRounds => write!(f, "a Rescue-Prime instance needs at least one round"),
            Self::Fixture(reason) => {
                write!(f, "the bounty constants could not be read: {}", reason)
            }
            Self::WrongDimension { needed, requested } => write!(
                f,
                "the system has {} variables and was requested at {}; spare positions would be \
                 unconstrained variables",
                needed, requested
            ),
        }
    }
}

impl std::error::Error for RescuePrimeError {}

/// A Rescue-Prime permutation with its constants fixed.
#[derive(Clone, Debug)]
pub struct RescuePrime<F: KnownOrder> {
    /// The parameters.
    pub parameters: RescuePrimeParameters,

    /// The `t × t` MDS matrix, row-major.
    pub mds: Vec<Vec<F>>,

    /// `2N` round-constant rows of width `t`: row `2r` follows round `r`'s forward S-box and row
    /// `2r + 1` follows its inverse S-box.
    pub round_constants: Vec<Vec<F>>,

    /// `α^{-1} mod (p − 1)`, the exponent of the inverse S-box.
    pub alpha_inverse: u64,
}

impl<F: KnownOrder> RescuePrime<F> {
    /// Read the instance's constants and derive the inverse exponent.
    ///
    /// # Errors
    /// [`RescuePrimeError`] for a field, exponent, round count or fixture that does not match.
    pub fn new(parameters: RescuePrimeParameters) -> Result<Self, RescuePrimeError> {
        if F::order_limbs() != [parameters.prime] {
            return Err(RescuePrimeError::FieldMismatch {
                expected: parameters.prime,
                found: format!("a field of order {:?}", F::order_limbs()),
            });
        }
        if parameters.alpha != 3 && parameters.alpha != 5 {
            return Err(RescuePrimeError::UnsupportedAlpha {
                alpha: parameters.alpha,
            });
        }
        if parameters.rounds == 0 {
            return Err(RescuePrimeError::NoRounds);
        }
        let group_order = u128::from(parameters.prime - 1);
        let alpha_inverse = mod_inverse_u128(u128::from(parameters.alpha), group_order).ok_or(
            RescuePrimeError::AlphaNotCoprime {
                alpha: parameters.alpha,
                prime: parameters.prime,
            },
        )?;

        let (mds_name, rc_name) = parameters.instance.tables();
        let mds = table::<F>(BOUNTY_CONSTANTS, mds_name)?;
        let all_constants = table::<F>(BOUNTY_CONSTANTS, rc_name)?;
        let available = all_constants.len() / 2;
        if parameters.rounds > available {
            return Err(RescuePrimeError::TooManyRounds {
                requested: parameters.rounds,
                available,
            });
        }
        if mds.len() != parameters.t() || mds.iter().any(|row| row.len() != parameters.t()) {
            return Err(RescuePrimeError::Fixture(format!(
                "{} is not {t} x {t}",
                mds_name,
                t = parameters.t()
            )));
        }
        if all_constants.iter().any(|row| row.len() != parameters.t()) {
            return Err(RescuePrimeError::Fixture(format!(
                "a {} row is not {} wide",
                rc_name,
                parameters.t()
            )));
        }

        Ok(Self {
            parameters,
            mds,
            round_constants: all_constants[..2 * parameters.rounds].to_vec(),
            alpha_inverse: alpha_inverse as u64,
        })
    }

    /// The forward S-box, `x^α`, applied word-wise.
    pub fn sbox(&self, state: &[F]) -> Vec<F> {
        state
            .iter()
            .map(|x| x.pow(u128::from(self.parameters.alpha)))
            .collect()
    }

    /// The inverse S-box, `x^{α^{-1} mod (p−1)}`, applied word-wise.
    ///
    /// The *expensive* direction to evaluate and the reason the polynomial model writes the round
    /// relation backwards: `y^α = x` is degree `α`, while `y = x^{α^{-1}}` is a polynomial of
    /// degree about `p/α`.
    pub fn sbox_inverse(&self, state: &[F]) -> Vec<F> {
        state
            .iter()
            .map(|x| x.pow(u128::from(self.alpha_inverse)))
            .collect()
    }

    /// `M·x + c_row`.
    pub fn affine(&self, state: &[F], row: usize) -> Vec<F> {
        let t = self.parameters.t();
        (0..t)
            .map(|i| {
                let mut accumulator = self.round_constants[row][i];
                for (j, x) in state.iter().enumerate().take(t) {
                    accumulator += self.mds[i][j] * *x;
                }
                accumulator
            })
            .collect()
    }

    /// The state at every half-round boundary: `4N + 1` entries.
    ///
    /// Index `4r` is the input to round `r`, then `4r + 1` after its forward S-box, `4r + 2` after
    /// the first affine layer, `4r + 3` after the inverse S-box, and `4r + 4` after the second
    /// affine layer. Every variable of the polynomial model is one of these words, which is what
    /// makes the faithfulness check mechanical.
    pub fn trace(&self, input: &[F]) -> Vec<Vec<F>> {
        let mut state = input.to_vec();
        let mut trace = Vec::with_capacity(4 * self.parameters.rounds + 1);
        trace.push(state.clone());
        for round in 0..self.parameters.rounds {
            state = self.sbox(&state);
            trace.push(state.clone());
            state = self.affine(&state, 2 * round);
            trace.push(state.clone());
            state = self.sbox_inverse(&state);
            trace.push(state.clone());
            state = self.affine(&state, 2 * round + 1);
            trace.push(state.clone());
        }
        trace
    }

    /// The permutation.
    pub fn permutation(&self, input: &[F]) -> Vec<F> {
        self.trace(input)
            .pop()
            .expect("a trace always holds its input")
    }

    /// Whether `(free…, 0)` is a CICO solution: the permutation's **last** output word is zero.
    ///
    /// The reference's own verifier, `bounties/examples/rescue/rescue_easy1.rs`: it builds
    /// `[solution1, solution2, zero]` and tests `output[output.len() - 1] == zero`. The trailing
    /// word at both ends, so `k = 1` and the objective is CICO(1).
    pub fn is_cico_solution(&self, free: &[F]) -> bool {
        let mut input = free.to_vec();
        input.push(F::zero());
        self.permutation(&input)
            .last()
            .expect("a non-empty state")
            .is_zero()
    }
}

/// Parse one named table out of the fixture.
fn table<F: FiniteField>(text: &str, name: &str) -> Result<Vec<Vec<F>>, RescuePrimeError> {
    let mut lines = text
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty() && !line.starts_with('#'));
    let header = loop {
        let line = lines
            .next()
            .ok_or_else(|| RescuePrimeError::Fixture(format!("no table named {}", name)))?;
        let mut fields = line.split_whitespace();
        if fields.next() != Some("table") {
            continue;
        }
        if fields.next() == Some(name) {
            break fields.collect::<Vec<_>>();
        }
    };
    let rows: usize = header
        .first()
        .and_then(|n| n.parse().ok())
        .ok_or_else(|| RescuePrimeError::Fixture(format!("{} has no row count", name)))?;
    let columns: usize = header
        .get(1)
        .and_then(|n| n.parse().ok())
        .ok_or_else(|| RescuePrimeError::Fixture(format!("{} has no column count", name)))?;

    let mut table = Vec::with_capacity(rows);
    for _ in 0..rows {
        let line = lines
            .next()
            .ok_or_else(|| RescuePrimeError::Fixture(format!("{} is short", name)))?;
        let row: Result<Vec<F>, RescuePrimeError> = line
            .split_whitespace()
            .map(|value| {
                value
                    .parse::<u64>()
                    .map(F::new)
                    .map_err(|_| RescuePrimeError::Fixture(format!("{}: {:?}", name, value)))
            })
            .collect();
        let row = row?;
        if row.len() != columns {
            return Err(RescuePrimeError::Fixture(format!(
                "{} row is {} wide and should be {}",
                name,
                row.len(),
                columns
            )));
        }
        table.push(row);
    }
    Ok(table)
}

#[cfg(test)]
mod tests {
    use super::{
        BountyInstance, RescuePrime, RescuePrimeError, RescuePrimeParameters, BOUNTY_INSTANCES,
        RESCUE_PRIME_PRIME,
    };
    use crate::{
        fields::{PrimeFieldElement64, Zp18446744073709551557},
        identities::Zero,
        FiniteField,
    };

    type F = Zp18446744073709551557;

    /// The reference's own known-answer tests, one per instance: `permutation([0, 1, 2, …])`.
    ///
    /// `zkfriendlyhashzoo` `bounties/src/rescue_prime/rescue_prime.rs`, module
    /// `rescue_prime_kats`, at commit `b9c09d5a6302725a65ff59e4219d1beb4c524154`. The third-party
    /// oracle for the transcription: each output depends on every MDS entry, every round constant
    /// and the inverse exponent, so reproducing all five is a check on the whole table rather than
    /// a spot check.
    const REFERENCE_KATS: [(BountyInstance, &[u64]); 5] = [
        (
            BountyInstance::Easy1,
            &[
                0xeb3c_8886_55db_7d7d,
                0xc76f_cb22_1ca5_a1f5,
                0xfb46_c8a3_f0d5_8087,
            ],
        ),
        (
            BountyInstance::Easy2,
            &[0x8bc0_3c0e_0c1e_9eb3, 0x8056_ff81_5059_0045],
        ),
        (
            BountyInstance::Medium,
            &[0x14ba_297b_fe1c_a063, 0xdaa7_2951_b79b_c857],
        ),
        (
            BountyInstance::Hard1,
            &[
                0x6cb9_703b_238c_9c2b,
                0x3607_8bff_ce60_2399,
                0x809e_9567_e030_37ed,
            ],
        ),
        (
            BountyInstance::Hard2,
            &[0x3a4f_c00d_47d1_8c87, 0x53b8_3111_7922_eb0b],
        ),
    ];

    /// The permutation reproduces the reference implementation's published test vectors for all
    /// five bounty instances.
    #[test]
    fn test_the_permutation_matches_the_reference_test_vectors() {
        for (instance, expected) in REFERENCE_KATS {
            let rescue =
                RescuePrime::<F>::new(RescuePrimeParameters::bounty(instance)).expect("builds");
            let input: Vec<F> = (0..instance.t() as u64).map(F::new).collect();
            let output: Vec<u64> = rescue
                .permutation(&input)
                .iter()
                .map(|x| x.value())
                .collect();
            assert_eq!(output, expected, "{instance} disagrees with the reference");
        }
    }

    /// `α` and `α^{-1} mod (p − 1)` are mutually inverse exponents on actual field elements.
    ///
    /// Checked by evaluation over the real field rather than by comparing against a transcribed
    /// constant: the exponent lives modulo `p − 1`, and a value correct for a neighbouring prime
    /// would be indistinguishable by inspection.
    #[test]
    fn test_the_two_sbox_exponents_are_mutually_inverse() {
        let rescue = RescuePrime::<F>::new(RescuePrimeParameters::bounty(BountyInstance::Easy1))
            .expect("builds");
        assert_eq!(rescue.alpha_inverse, 12_297_829_382_473_034_371);
        assert_eq!(
            (3u128 * u128::from(rescue.alpha_inverse)) % u128::from(RESCUE_PRIME_PRIME - 1),
            1
        );
        for seed in 1u64..40 {
            let x = F::new(seed * 7_919 + 13);
            let forward = rescue.sbox(&[x]);
            assert_eq!(rescue.sbox_inverse(&forward), vec![x], "seed {seed}");
            let backward = rescue.sbox_inverse(&[x]);
            assert_eq!(rescue.sbox(&backward), vec![x], "seed {seed}");
        }
    }

    /// `y^α = x` is the relation the polynomial model uses in place of `y = x^{α^{-1}}`, and it
    /// holds on the permutation's own trace.
    ///
    /// The deliberate formulation choice of #203, checked against the primitive: index `4r + 3` of
    /// the trace is the inverse S-box's output and `4r + 2` its input, so cubing the former must
    /// give the latter.
    #[test]
    fn test_the_inverse_sbox_relation_holds_on_the_trace() {
        let rescue = RescuePrime::<F>::new(RescuePrimeParameters::bounty(BountyInstance::Hard1))
            .expect("builds");
        let trace = rescue.trace(&[F::new(11), F::new(22), F::new(33)]);
        for round in 0..rescue.parameters.rounds {
            let before = &trace[4 * round + 2];
            let after = &trace[4 * round + 3];
            assert_eq!(rescue.sbox(after), *before, "round {round}");
        }
    }

    /// The widths are the reference's: two of the five instances are `t = 3` and three are `t = 2`.
    #[test]
    fn test_three_of_the_five_instances_are_width_two() {
        let widths: Vec<usize> = BOUNTY_INSTANCES.iter().map(|i| i.t()).collect();
        assert_eq!(widths, vec![3, 2, 2, 3, 2]);
        let rounds: Vec<usize> = BOUNTY_INSTANCES.iter().map(|i| i.rounds()).collect();
        assert_eq!(rounds, vec![4, 6, 7, 5, 8]);
    }

    /// Each instance's round-constant table has exactly `2N` rows of width `t`, and the MDS is
    /// `t × t`.
    ///
    /// The shape cross-check `docs/research/ef-cryptanalysis.md` §4.2 records: 8×3, 12×2, 14×2,
    /// 10×3, 16×2.
    #[test]
    fn test_the_constant_tables_have_the_published_shapes() {
        for instance in BOUNTY_INSTANCES {
            let rescue =
                RescuePrime::<F>::new(RescuePrimeParameters::bounty(instance)).expect("builds");
            assert_eq!(
                rescue.round_constants.len(),
                2 * instance.rounds(),
                "{instance}"
            );
            assert!(rescue
                .round_constants
                .iter()
                .all(|row| row.len() == instance.t()));
            assert_eq!(rescue.mds.len(), instance.t(), "{instance}");
            assert!(rescue.mds.iter().all(|row| row.len() == instance.t()));
        }
    }

    /// The trace has `4N + 1` entries and ends at the permutation's output.
    #[test]
    fn test_the_trace_records_every_half_round() {
        let rescue = RescuePrime::<F>::new(RescuePrimeParameters::bounty(BountyInstance::Easy1))
            .expect("builds");
        let input = vec![F::new(1), F::new(2), F::new(3)];
        let trace = rescue.trace(&input);
        assert_eq!(trace.len(), 17);
        assert_eq!(trace[0], input);
        assert_eq!(
            *trace.last().expect("non-empty"),
            rescue.permutation(&input)
        );
    }

    /// A reduced-round rung is the specified instance's tables truncated, and says it is not the
    /// specified instance.
    #[test]
    fn test_a_reduced_rung_truncates_the_published_tables() {
        let full = RescuePrime::<F>::new(RescuePrimeParameters::bounty(BountyInstance::Hard1))
            .expect("builds");
        for rounds in 1..5 {
            let parameters = RescuePrimeParameters::reduced(BountyInstance::Hard1, rounds);
            assert!(!parameters.is_specified());
            let reduced = RescuePrime::<F>::new(parameters).expect("builds");
            assert_eq!(reduced.round_constants, full.round_constants[..2 * rounds]);
            assert_eq!(reduced.mds, full.mds);
        }
        assert!(RescuePrimeParameters::bounty(BountyInstance::Hard1).is_specified());
    }

    /// The CICO condition is on the trailing word, as the reference's verifier writes it, and a
    /// non-solution is rejected.
    #[test]
    fn test_the_cico_condition_is_on_the_trailing_word() {
        let rescue = RescuePrime::<F>::new(RescuePrimeParameters::bounty(BountyInstance::Easy2))
            .expect("builds");
        let free = [F::new(5)];
        let mut input = free.to_vec();
        input.push(F::zero());
        let output = rescue.permutation(&input);
        assert_eq!(
            rescue.is_cico_solution(&free),
            output[1].is_zero(),
            "is_cico_solution must read the same word the verifier does"
        );
        assert!(!rescue.is_cico_solution(&free));
    }

    /// A coefficient type that is not the parameters' field is refused rather than used.
    #[test]
    fn test_the_field_is_enforced() {
        let wrong = RescuePrime::<PrimeFieldElement64<31>>::new(RescuePrimeParameters::bounty(
            BountyInstance::Easy1,
        ));
        assert!(matches!(wrong, Err(RescuePrimeError::FieldMismatch { .. })));
    }

    /// Parameters the published tables do not support are refused by name rather than extrapolated.
    #[test]
    fn test_unsupported_parameters_are_refused_by_name() {
        assert_eq!(
            RescuePrime::<F>::new(RescuePrimeParameters::reduced(BountyInstance::Easy1, 0)).err(),
            Some(RescuePrimeError::NoRounds)
        );
        assert_eq!(
            RescuePrime::<F>::new(RescuePrimeParameters::reduced(BountyInstance::Easy1, 5)).err(),
            Some(RescuePrimeError::TooManyRounds {
                requested: 5,
                available: 4
            })
        );
        let alpha_seven = RescuePrimeParameters {
            alpha: 7,
            ..RescuePrimeParameters::bounty(BountyInstance::Easy1)
        };
        assert_eq!(
            RescuePrime::<F>::new(alpha_seven).err(),
            Some(RescuePrimeError::UnsupportedAlpha { alpha: 7 })
        );
    }
}
