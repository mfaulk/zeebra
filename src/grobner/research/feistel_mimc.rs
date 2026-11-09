//! Feistel-MiMC over `p = 2^64 − 59`, with its round constants derived rather than copied.
//!
//! The primitive is MiMC in Feistel mode — Albrecht, Grassi, Rechberger, Roy and Tiessen, *MiMC:
//! Efficient Encryption and Cryptographic Hashing with Minimal Multiplicative Complexity*,
//! Asiacrypt 2016 — and the *instances* are the Ethereum Foundation's 2021–2022 ZK Hash
//! Cryptanalysis Bounties, whose reference implementation is
//! `krypto/zkfriendlyhashzoo` at commit `b9c09d5a6302725a65ff59e4219d1beb4c524154` (MIT), read from
//! <https://extgit.iaik.tugraz.at/krypto/zkfriendlyhashzoo> on 2026-11-09. The parameters, the two
//! ladders and the published records are `docs/research/ef-cryptanalysis.md` §4.4; this module is
//! the executable half.
//!
//! # Why nothing here is a constant table
//!
//! The reference *derives* the round constants: `FeistelMimcParams::instantiate_rc` seeds a
//! SHAKE128 with the ASCII string `"FeistelMimc"` followed by the field characteristic and reads
//! field elements out of the squeeze stream by rejection sampling. A committed table would be a
//! second copy of something the parameters already determine, so [`FeistelMimc::new`] recomputes
//! it and [`FeistelMimc::derived_digest`] is the regression pin — the argument
//! [`anemoi`](super::anemoi) makes for the digits of π.
//!
//! # The seed absorbs a limb this crate's characteristic does not have
//!
//! The reference absorbs `F::char().as_ref()` one `u64` at a time, and its `Fp64` is an `ff`
//! `PrimeField` whose `FrRepr` is **two** limbs wide for a 64-bit modulus — `ff` needs a spare bit
//! for its Montgomery arithmetic. So the seed is `p` as eight little-endian bytes **followed by
//! eight zero bytes**, while [`KnownOrder::characteristic_limbs`] is canonical and reports a single
//! limb. [`SEED_LIMBS`] therefore states the reference's representation width rather than reading
//! it off the field, and the whole construction is pinned by the reference's own test vectors — the
//! #197 lesson, where two fields of the same order and different moduli were indistinguishable by
//! any shape check.
//!
//! # The ladder is a prefix, not a schedule
//!
//! The SHAKE is seeded with the string and the characteristic alone — **not** with the round count.
//! The constants of a `r`-round instance are therefore the first `r` of any longer instance's, so a
//! reduced-round rung is the authoritative instance truncated rather than a different primitive. A
//! test asserts it.

use std::fmt::{Display, Formatter};

use crate::{util::Shake128, FiniteField, KnownOrder};

/// `2^64 - 59`, the prime every 2021–2022 bounty instance is over.
pub const FEISTEL_MIMC_PRIME: u64 = 18_446_744_073_709_551_557;

/// The domain string the reference seeds its SHAKE128 with.
pub const INIT_SHAKE: &str = "FeistelMimc";

/// Limbs of the characteristic the reference absorbs into the seed.
///
/// Two, not one: see the module docs. Changing this changes every round constant, which is why it
/// is named and pinned rather than inlined.
pub const SEED_LIMBS: usize = 2;

/// The authoritative round counts: the replacement ladder, `bounties21`'s `easy1 … hard2`.
///
/// `zkfriendlyhashzoo` commit `e69d08f612f8534ef60651cb01fc326b67230ec1`, 2021-12-20, "update the
/// feistel-mimc instances", replaced [`WITHDRAWN_ROUNDS`] with these.
pub const BOUNTY_ROUNDS: [usize; 5] = [22, 25, 30, 35, 40];

/// The **withdrawn** round counts: the ladder that was broken and replaced.
///
/// `bounties21` says only "The initial parameters were broken and were replaced"; the two that
/// fell are `r = 14` (`2^33`, 3 minutes) and `r = 18` (`2^40`, 6 hours), and the whole original
/// ladder comes from the reference's git history. Carried so that a result against one of these can
/// be *labelled* as a reproduction of a break of a retired instance, which is the only honest
/// statement available about it.
pub const WITHDRAWN_ROUNDS: [usize; 5] = [6, 10, 14, 18, 22];

/// The parameters of a Feistel-MiMC instance.
///
/// The state is always two words and the round constants are always derived, so `α` and the round
/// count are the whole of it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct FeistelMimcParameters {
    /// The field modulus.
    pub prime: u64,

    /// The S-box exponent `α = d`. The reference implements 3 and 5; every bounty instance is 3.
    pub alpha: u32,

    /// The number of rounds `r`.
    pub rounds: usize,
}

impl FeistelMimcParameters {
    /// The bounty parameters at `rounds` rounds: `α = 3` over `2^64 − 59`.
    ///
    /// Any `rounds` is accepted, because the reduced-round ladder is the point; which counts are
    /// the *specified* instances is [`BOUNTY_ROUNDS`] and [`WITHDRAWN_ROUNDS`].
    pub fn bounty(rounds: usize) -> Self {
        Self {
            prime: FEISTEL_MIMC_PRIME,
            alpha: 3,
            rounds,
        }
    }

    /// Whether `rounds` is one of the authoritative specified instances.
    pub fn is_specified(&self) -> bool {
        BOUNTY_ROUNDS.contains(&self.rounds)
    }

    /// Whether `rounds` is one of the withdrawn instances.
    pub fn is_withdrawn(&self) -> bool {
        WITHDRAWN_ROUNDS.contains(&self.rounds)
    }
}

impl Display for FeistelMimcParameters {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "p = {}, alpha = {}, r = {}",
            self.prime, self.alpha, self.rounds
        )
    }
}

/// Why a Feistel-MiMC instance could not be built.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum FeistelMimcError {
    /// The coefficient type's order is not the parameters' prime.
    ///
    /// Checked because a mismatch produces the primitive over the wrong field, which says nothing
    /// and looks like nothing.
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

    /// `gcd(α, p − 1) ≠ 1`, so `x ↦ x^α` is not a permutation.
    AlphaNotCoprime {
        /// The requested exponent.
        alpha: u32,
        /// The modulus.
        prime: u64,
    },

    /// A zero-round instance, which is the identity and not a permutation family.
    NoRounds,

    /// The requested `const N` is not the model's variable count.
    ///
    /// Exact rather than "at least": a spare position is an unconstrained variable, so the ideal
    /// gains a free coordinate and the zero-dimensional solvers refuse a system that was meant to
    /// be solvable.
    WrongDimension {
        /// Variables the system has.
        needed: usize,
        /// The dimension it was requested at.
        requested: usize,
    },
}

impl Display for FeistelMimcError {
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
            Self::NoRounds => write!(f, "a Feistel-MiMC instance needs at least one round"),
            Self::WrongDimension { needed, requested } => write!(
                f,
                "the system has {} variables and was requested at {}; spare positions would be \
                 unconstrained variables",
                needed, requested
            ),
        }
    }
}

impl std::error::Error for FeistelMimcError {}

/// A Feistel-MiMC permutation with its round constants fixed.
///
/// Constructible only through [`FeistelMimc::new`], which checks that `F` is the field the
/// parameters name, so a value of this type is the primitive over the right field by construction.
#[derive(Clone, Debug)]
pub struct FeistelMimc<F: KnownOrder> {
    /// The parameters.
    pub parameters: FeistelMimcParameters,

    /// `c_0 … c_{r−1}`, in round order, derived from the SHAKE128 stream.
    pub round_constants: Vec<F>,
}

impl<F: KnownOrder> FeistelMimc<F> {
    /// Derive the round constants from the parameters, as the reference does.
    ///
    /// # Errors
    /// [`FeistelMimcError::FieldMismatch`] if `F` is not the field `parameters.prime` names,
    /// [`FeistelMimcError::UnsupportedAlpha`] for an `α` the reference does not implement,
    /// [`FeistelMimcError::AlphaNotCoprime`] if `x ↦ x^α` is not a permutation, and
    /// [`FeistelMimcError::NoRounds`] for `r = 0`.
    pub fn new(parameters: FeistelMimcParameters) -> Result<Self, FeistelMimcError> {
        if F::order_limbs() != [parameters.prime] {
            return Err(FeistelMimcError::FieldMismatch {
                expected: parameters.prime,
                found: format!("a field of order {:?}", F::order_limbs()),
            });
        }
        if parameters.alpha != 3 && parameters.alpha != 5 {
            return Err(FeistelMimcError::UnsupportedAlpha {
                alpha: parameters.alpha,
            });
        }
        if gcd(u64::from(parameters.alpha), parameters.prime - 1) != 1 {
            return Err(FeistelMimcError::AlphaNotCoprime {
                alpha: parameters.alpha,
                prime: parameters.prime,
            });
        }
        if parameters.rounds == 0 {
            return Err(FeistelMimcError::NoRounds);
        }

        Ok(Self {
            round_constants: round_constants(parameters.prime, parameters.rounds),
            parameters,
        })
    }

    /// The round function's S-box, `(x + c_round)^α`.
    pub fn sbox(&self, x: F, round: usize) -> F {
        (x + self.round_constants[round]).pow(u128::from(self.parameters.alpha))
    }

    /// The state after each round: `r + 1` entries, the input and then each round's output.
    ///
    /// A round is `(x, y) ↦ (y + S(x), x)` — the Feistel swap is **after** the S-box — except the
    /// last, which omits the swap and is `(x, y) ↦ (x, y + S(x))`. That asymmetry is the
    /// reference's, and it is why the final CICO condition lands on the second word.
    pub fn trace(&self, x: F, y: F) -> Vec<[F; 2]> {
        let mut state = [x, y];
        let mut trace = Vec::with_capacity(self.parameters.rounds + 1);
        trace.push(state);
        for round in 0..self.parameters.rounds - 1 {
            state = [state[1] + self.sbox(state[0], round), state[0]];
            trace.push(state);
        }
        let last = self.parameters.rounds - 1;
        state = [state[0], state[1] + self.sbox(state[0], last)];
        trace.push(state);
        trace
    }

    /// The permutation.
    pub fn permutation(&self, x: F, y: F) -> [F; 2] {
        *self
            .trace(x, y)
            .last()
            .expect("a trace always holds its input")
    }

    /// Whether `(x, 0)` is a CICO solution: the permutation's **second** output word is zero.
    ///
    /// The trailing word at both ends, which is what the reference's own verifier checks —
    /// `bounties/examples/feistel_mimc/feistel_mimc_easy1.rs` builds `[solution, zero]` and tests
    /// `output[output.len() - 1] == zero`. Not the leading word, which is the convention
    /// [`AnemoiCico`](super::AnemoiCico) uses, and not the same problem.
    pub fn is_cico_solution(&self, x: F) -> bool {
        self.permutation(x, F::zero())[1].is_zero()
    }

    /// A digest of the derived round constants, lowercase hex, truncated to 16 digits.
    ///
    /// **Not** an identity: the parameters determine these. It is a regression pin on the
    /// derivation, and specifically on [`SEED_LIMBS`] and the rejection rule — neither of which a
    /// checksum over `p`, `α` and `r` could notice changing.
    pub fn derived_digest(&self) -> String {
        let text: String = self
            .round_constants
            .iter()
            .map(|c| format!("{}\n", c))
            .collect();
        crate::util::sha256_hex(text.as_bytes())[..16].to_string()
    }
}

/// `rounds` round constants from the reference's SHAKE128 stream.
///
/// Rejection sampling on eight-byte little-endian words, discarding any that is not a canonical
/// field representative. The reference's `field_element_from_shake` masks the top byte to
/// `NUM_BITS mod 8` bits, which is a no-op at exactly 64 bits, and retries on a value its
/// `from_repr` refuses — that refusal is `value >= p`.
fn round_constants<F: FiniteField>(prime: u64, rounds: usize) -> Vec<F> {
    let mut shake = Shake128::new();
    shake.update(INIT_SHAKE.as_bytes());
    // The reference absorbs the characteristic as its own repr's limbs, which is two u64 wide.
    shake.update(&prime.to_le_bytes());
    for _ in 1..SEED_LIMBS {
        shake.update(&0u64.to_le_bytes());
    }

    let mut constants = Vec::with_capacity(rounds);
    let mut word = [0u8; 8];
    while constants.len() < rounds {
        shake.read(&mut word);
        let value = u64::from_le_bytes(word);
        if value < prime {
            constants.push(F::new(value));
        }
    }
    constants
}

/// `gcd(a, b)`, by Euclid.
fn gcd(a: u64, b: u64) -> u64 {
    if b == 0 {
        a
    } else {
        gcd(b, a % b)
    }
}

#[cfg(test)]
mod tests {
    use super::{
        FeistelMimc, FeistelMimcError, FeistelMimcParameters, BOUNTY_ROUNDS, FEISTEL_MIMC_PRIME,
        WITHDRAWN_ROUNDS,
    };
    use crate::{
        fields::{PrimeFieldElement64, Zp18446744073709551557},
        identities::{One, Zero},
        FiniteField,
    };

    type F = Zp18446744073709551557;

    /// The reference's own known-answer tests, one per authoritative instance.
    ///
    /// `zkfriendlyhashzoo` `bounties/src/feistel_mimc/feistel_mimc.rs`, module
    /// `feistel_mimc_kats`, at commit `b9c09d5a6302725a65ff59e4219d1beb4c524154`. Each is
    /// `permutation([0, 1])`. These are the third-party oracle: they depend on every round constant
    /// the derivation produces, on the seed width, on the rejection rule and on the placement of
    /// the Feistel swap, so a system generated over a permutation that reproduces all five is the
    /// published primitive and not something isomorphic to it.
    const REFERENCE_KATS: [(usize, u64, u64); 5] = [
        (22, 0xf874_e35b_baf9_2376, 0x72af_6f65_901a_c3f1),
        (25, 0x85bd_8eb1_f92b_fb9a, 0x49d9_875c_885a_962c),
        (30, 0x6f06_9da7_d13e_eac0, 0xf992_0910_2b0f_4e3b),
        (35, 0x1017_818e_ae88_1aee, 0x7e70_2522_1ea1_92b6),
        (40, 0x095c_8119_5f93_fa60, 0x41c4_5da5_e165_5eb6),
    ];

    /// The permutation reproduces the reference implementation's published test vectors at every
    /// one of the five authoritative round counts.
    #[test]
    fn test_the_permutation_matches_the_reference_test_vectors() {
        for (rounds, first, second) in REFERENCE_KATS {
            let mimc =
                FeistelMimc::<F>::new(FeistelMimcParameters::bounty(rounds)).expect("builds");
            let output = mimc.permutation(F::zero(), F::one());
            assert_eq!(
                (output[0].value(), output[1].value()),
                (first, second),
                "r = {rounds}: Feistel-MiMC([0, 1]) disagrees with the reference"
            );
        }
    }

    /// The round constants are a prefix of any longer instance's, so a reduced-round rung is the
    /// specified instance truncated.
    #[test]
    fn test_the_round_constants_are_a_prefix() {
        let longest = FeistelMimc::<F>::new(FeistelMimcParameters::bounty(40)).expect("builds");
        for rounds in [1, 6, 14, 22, 39] {
            let shorter =
                FeistelMimc::<F>::new(FeistelMimcParameters::bounty(rounds)).expect("builds");
            assert_eq!(
                shorter.round_constants,
                longest.round_constants[..rounds],
                "r = {rounds}"
            );
        }
    }

    /// The first round constants have their recorded values, in decimal.
    ///
    /// Pinned separately from [`REFERENCE_KATS`] so that a derivation failure is readable as a
    /// wrong *constant* rather than only as a wrong permutation output.
    #[test]
    fn test_the_first_round_constants_are_pinned() {
        let mimc = FeistelMimc::<F>::new(FeistelMimcParameters::bounty(5)).expect("builds");
        let values: Vec<u64> = mimc.round_constants.iter().map(|c| c.value()).collect();
        assert_eq!(
            values,
            vec![
                2_680_981_119_477_473_210,
                13_663_675_832_691_398_692,
                15_246_687_758_243_821_825,
                13_703_510_567_441_123_449,
                15_714_050_528_204_401_657,
            ]
        );
    }

    /// The derived constants are pinned, so a changed seed width or rejection rule cannot pass as
    /// the same instance.
    ///
    /// This is the check a parameter digest cannot make: `p`, `α` and `r` would be unchanged if the
    /// seed stopped absorbing its zero high limb, and every constant would move.
    #[test]
    fn test_the_derived_constants_are_pinned() {
        for (rounds, digest) in [
            (6, "f45af9dbf35aadf9"),
            (22, "8d52a882efde458b"),
            (40, "d1a97b7391e61728"),
        ] {
            let mimc =
                FeistelMimc::<F>::new(FeistelMimcParameters::bounty(rounds)).expect("builds");
            assert_eq!(mimc.derived_digest(), digest, "r = {rounds}");
        }
    }

    /// The trace has `r + 1` states, starts at the input, ends at the permutation's output, and its
    /// last step omits the Feistel swap.
    #[test]
    fn test_the_trace_ends_without_a_swap() {
        let mimc = FeistelMimc::<F>::new(FeistelMimcParameters::bounty(4)).expect("builds");
        let (x, y) = (F::new(3), F::new(5));
        let trace = mimc.trace(x, y);
        assert_eq!(trace.len(), 5);
        assert_eq!(trace[0], [x, y]);
        assert_eq!(trace[4], mimc.permutation(x, y));
        // Rounds 0..2 swap: the new second word is the old first word.
        for round in 0..3 {
            assert_eq!(trace[round + 1][1], trace[round][0], "round {round}");
        }
        // The last does not: the first word is carried through unchanged.
        assert_eq!(trace[4][0], trace[3][0]);
        assert_eq!(trace[4][1], trace[3][1] + mimc.sbox(trace[3][0], 3));
    }

    /// The CICO condition is on the trailing word at both ends, as the reference's verifier writes
    /// it.
    ///
    /// At `r = 1` the condition is solvable in closed form — `(x + c_0)^3 = 0` forces `x = −c_0` —
    /// which makes it the one round count where the witness can be checked without solving
    /// anything.
    #[test]
    fn test_the_cico_condition_is_on_the_trailing_word() {
        let mimc = FeistelMimc::<F>::new(FeistelMimcParameters::bounty(1)).expect("builds");
        let witness = -mimc.round_constants[0];
        assert!(mimc.is_cico_solution(witness));
        assert_eq!(mimc.permutation(witness, F::zero())[1], F::zero());
        assert!(!mimc.is_cico_solution(witness + F::one()));
    }

    /// The two published ladders are recorded, and the withdrawn ladder's hardest rung is the
    /// authoritative ladder's easiest.
    #[test]
    fn test_both_ladders_are_recorded() {
        assert_eq!(BOUNTY_ROUNDS, [22, 25, 30, 35, 40]);
        assert_eq!(WITHDRAWN_ROUNDS, [6, 10, 14, 18, 22]);
        assert_eq!(WITHDRAWN_ROUNDS[4], BOUNTY_ROUNDS[0]);
        let specified = FeistelMimcParameters::bounty(22);
        assert!(specified.is_specified() && specified.is_withdrawn());
        let retired = FeistelMimcParameters::bounty(18);
        assert!(!retired.is_specified() && retired.is_withdrawn());
        let neither = FeistelMimcParameters::bounty(7);
        assert!(!neither.is_specified() && !neither.is_withdrawn());
    }

    /// A coefficient type that is not the parameters' field is refused rather than used.
    #[test]
    fn test_the_field_is_enforced() {
        let wrong = FeistelMimc::<PrimeFieldElement64<31>>::new(FeistelMimcParameters::bounty(4));
        assert!(matches!(wrong, Err(FeistelMimcError::FieldMismatch { .. })));
    }

    /// Parameters the reference does not implement are refused by name.
    #[test]
    fn test_unsupported_parameters_are_refused_by_name() {
        assert_eq!(
            FeistelMimc::<F>::new(FeistelMimcParameters::bounty(0)).err(),
            Some(FeistelMimcError::NoRounds)
        );
        let alpha_seven = FeistelMimcParameters {
            alpha: 7,
            ..FeistelMimcParameters::bounty(4)
        };
        assert_eq!(
            FeistelMimc::<F>::new(alpha_seven).err(),
            Some(FeistelMimcError::UnsupportedAlpha { alpha: 7 })
        );
        // 2^64 - 60 = 2^2 * 3 * ... , so alpha = 3 is the coprimality case worth checking holds.
        assert_eq!((FEISTEL_MIMC_PRIME - 1) % 3, 1);
    }
}
