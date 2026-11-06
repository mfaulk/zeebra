//! Anemoi at `ℓ = 1` over an odd prime field, with its round constants derived rather than copied.
//!
//! Specified in Bouvier, Briaud, Chaidos, Perrin, Salen, Velichkov and Willems, *New Design
//! Techniques for Efficient Arithmetization-Oriented Hash Functions: Anemoi Permutations and Jive
//! Compression Mode*, CRYPTO 2023 — read from <https://hal.science/hal-04276646/document>, because
//! eprint PDF paths return HTTP 403 from this environment. The round function, the open Flystel and
//! the π-derived constants were checked line by line against the designers' reference
//! implementation, <https://github.com/anemoi-hash/anemoi-hash> at commit `3e86ff0c` (MIT).
//!
//! # Why nothing here is a constant table
//!
//! Anemoi's constants are **fully derived in the paper** from the first two hundred digits of π, so
//! a committed table would be a second copy of something the parameters already determine — the
//! same argument [`poseidon`](super::poseidon) makes for its Grain LFSR. [`Anemoi::new`] recomputes
//! them, and [`Anemoi::derived_digest`] is the regression pin.
//!
//! # The one reconstruction dependency
//!
//! `g` is "a generator of the multiplicative subgroup", and the paper names no particular one. The
//! reference implementation takes Sage's `F.multiplicative_generator()`, which is the **smallest
//! primitive root** — deterministic, and reproduced here by [`smallest_primitive_root`], but a
//! convention rather than a specification. That is a reconstruction dependency and not a gap: `g`
//! is not a free parameter once the convention is named, and `g = 5` for `p = 2^64 - 353` is
//! confirmed against committed reference data (`docs/research/anemoi.md` §3).
//!
//! It is also exactly why [`Anemoi::derived_digest`] exists. A parameter checksum covers `p`, `α`,
//! `ℓ` and the round count; it cannot notice a changed *generator*, which would silently replace
//! every constant while leaving the parameters alone.

use std::fmt::{Display, Formatter};

use rand::{rngs::StdRng, SeedableRng};

use crate::{
    integers::{big_uint::BigUInt, factor},
    util::sha256_hex,
    KnownOrder,
};

/// `2^64 - 353`, the 64-bit prime the Six Worlds Anemoi experiments are over.
pub const ANEMOI_64_PRIME: u64 = 18_446_744_073_709_551_263;

/// The first hundred decimal digits of π after the leading 3.
const PI_0: &str = "1415926535897932384626433832795028841971693993751058209749445923078164062862089986280348253421170679";

/// The hundred decimal digits of π after those.
///
/// Unused at `ℓ = 1` — the constants take `π₁^j` with `j` the column index, so `j = 0` and
/// `π₁^0 = 1` — and carried anyway, because its absence from the arithmetic is a *consequence* of
/// `ℓ = 1` rather than a simplification of the specification.
const PI_1: &str = "8214808651328230664709384460955058223172535940812848111745028410270193852110555964462294895493038196";

/// The parameters of an Anemoi instance.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct AnemoiParameters {
    /// The field modulus.
    pub prime: u64,

    /// The S-box exponent `α`.
    pub alpha: u32,

    /// The number of columns `ℓ`; the state is `2ℓ` words wide.
    pub l: usize,

    /// The number of rounds `N`.
    pub rounds: usize,
}

impl AnemoiParameters {
    /// The Six Worlds parameters: `α = 3`, `ℓ = 1`, `p = 2^64 - 353`, at `rounds` rounds.
    pub fn six_worlds(rounds: usize) -> Self {
        Self {
            prime: ANEMOI_64_PRIME,
            alpha: 3,
            l: 1,
            rounds,
        }
    }

    /// The number of open Flystel evaluations, `ℓ·N`.
    pub fn sboxes(&self) -> usize {
        self.l * self.rounds
    }
}

impl Display for AnemoiParameters {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "p = {}, alpha = {}, l = {}, N = {}",
            self.prime, self.alpha, self.l, self.rounds
        )
    }
}

/// Why an Anemoi instance could not be built.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum AnemoiError {
    /// The coefficient type's order is not the parameters' prime.
    ///
    /// Checked for the reason [`PoseidonError::FieldMismatch`](super::PoseidonError) is: a
    /// mismatch produces Anemoi over the wrong field, which says nothing and looks like nothing.
    FieldMismatch {
        /// The prime the parameters name.
        expected: u64,
        /// The field the coefficient type actually is.
        found: String,
    },

    /// A column count this module does not implement.
    ///
    /// `ℓ > 1` needs the reference's `M_2`/`M_3`/`M_4` and circulant MDS constructions, which are
    /// a different linear layer rather than a wider one.
    UnsupportedColumns {
        /// The requested `ℓ`.
        l: usize,
    },

    /// `gcd(α, p − 1) ≠ 1`, so `x ↦ x^α` is not a permutation and the Flystel has no inverse.
    AlphaNotCoprime {
        /// The requested exponent.
        alpha: u32,
        /// The modulus.
        prime: u64,
    },

    /// A zero-round instance, which is the linear layer and not a permutation family.
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

impl Display for AnemoiError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::FieldMismatch { expected, found } => write!(
                f,
                "the parameters are over GF({}) and the coefficient type is {}",
                expected, found
            ),
            Self::UnsupportedColumns { l } => write!(
                f,
                "only l = 1 is implemented here; l = {} needs the reference's wider MDS layer",
                l
            ),
            Self::AlphaNotCoprime { alpha, prime } => write!(
                f,
                "alpha = {} is not coprime with {} - 1, so x^alpha is not a permutation",
                alpha, prime
            ),
            Self::NoRounds => write!(f, "an Anemoi instance needs at least one round"),
            Self::WrongDimension { needed, requested } => write!(
                f,
                "the system has {} variables and was requested at {}; spare positions would be \
                 unconstrained variables",
                needed, requested
            ),
        }
    }
}

impl std::error::Error for AnemoiError {}

/// An Anemoi permutation at `ℓ = 1` with its constants fixed.
///
/// Constructible only through [`Anemoi::new`], which checks that `F` is the field the parameters
/// name, so a value of this type is Anemoi over the right field by construction.
#[derive(Clone, Debug)]
pub struct Anemoi<F: KnownOrder> {
    /// The parameters.
    pub parameters: AnemoiParameters,

    /// The multiplicative generator the constants were derived with, as an integer.
    ///
    /// Carried as the integer rather than only as [`Self::beta`] because it is the one
    /// reconstruction dependency and a reader needs to be able to read it off.
    pub generator: u64,

    /// `β = g`, the coefficient of the Flystel's quadratic subfunctions.
    pub beta: F,

    /// `δ = g^{-1}`, the constant the Flystel's second quadratic subfunction adds.
    pub delta: F,

    /// `c_i` for `i = 1 … N`, in round order.
    pub c: Vec<F>,

    /// `d_i` for `i = 1 … N`, in round order.
    pub d: Vec<F>,

    /// `α^{-1} mod (p − 1)`, the exponent the open Flystel's inverse power map uses.
    inverse_alpha: u64,
}

impl<F: KnownOrder> Anemoi<F> {
    /// Derive the constants from the parameters, as the reference does.
    ///
    /// # Errors
    /// [`AnemoiError::FieldMismatch`] if `F` is not the field `parameters.prime` names,
    /// [`AnemoiError::UnsupportedColumns`] for `ℓ ≠ 1`, [`AnemoiError::AlphaNotCoprime`] if
    /// `x ↦ x^α` is not a permutation, and [`AnemoiError::NoRounds`] for `N = 0`.
    pub fn new(parameters: AnemoiParameters) -> Result<Self, AnemoiError> {
        if F::order_limbs() != [parameters.prime] {
            return Err(AnemoiError::FieldMismatch {
                expected: parameters.prime,
                found: format!("a field of order {:?}", F::order_limbs()),
            });
        }
        if parameters.l != 1 {
            return Err(AnemoiError::UnsupportedColumns { l: parameters.l });
        }
        if parameters.rounds == 0 {
            return Err(AnemoiError::NoRounds);
        }
        let group_order = parameters.prime - 1;
        let inverse_alpha = modular_inverse(u64::from(parameters.alpha), group_order).ok_or(
            AnemoiError::AlphaNotCoprime {
                alpha: parameters.alpha,
                prime: parameters.prime,
            },
        )?;

        let generator = smallest_primitive_root(parameters.prime);
        let beta = F::new(generator);
        let delta = beta.inverse();

        // pi_1 contributes only through pi_1^j with j the column index, so j = 0 at l = 1.
        let pi_0 = from_decimal::<F>(PI_0);
        let pi_1 = from_decimal::<F>(PI_1);
        let (mut c, mut d) = (Vec::new(), Vec::new());
        for round in 0..parameters.rounds {
            let pi_0_r = pi_0.pow(round as u128);
            let pi_1_j = pi_1.pow(0);
            let powered = (pi_0_r + pi_1_j).pow(u128::from(parameters.alpha));
            c.push(beta * pi_0_r * pi_0_r + powered);
            d.push(beta * pi_1_j * pi_1_j + powered + delta);
        }

        Ok(Self {
            parameters,
            generator,
            beta,
            delta,
            c,
            d,
            inverse_alpha,
        })
    }

    /// The open Flystel `H`, which is the round's S-box.
    ///
    /// `H(x, y) = (u, v)` with `x' = x − βy²`, `v = y − (x')^{1/α}` and `u = x' + βv² + δ`. The
    /// relation the polynomial models use is this one read backwards — `x = βy² + (y − v)^α` and
    /// `u = βv² + δ + (y − v)^α`, which is degree `α` rather than degree `α^{-1}` — and that
    /// equivalence is why Anemoi is cheap to arithmetize at all.
    pub fn open_flystel(&self, x: F, y: F) -> (F, F) {
        let reduced = x - self.beta * y * y;
        let v = y - reduced.pow(u128::from(self.inverse_alpha));
        (reduced + self.beta * v * v + self.delta, v)
    }

    /// The linear layer `M(x, y) = (2x + y, x + y)`.
    ///
    /// The reference builds this as the identity matrix (at `ℓ = 1`) followed by a pseudo-Hadamard
    /// transform; at one column the matrix drops out and the transform is the whole map.
    pub fn linear_layer(x: F, y: F) -> (F, F) {
        let y = y + x;
        (x + y, y)
    }

    /// The inverse of [`Self::linear_layer`].
    pub fn inverse_linear_layer(x: F, y: F) -> (F, F) {
        let x = x - y;
        (x, y - x)
    }

    /// The state after each round, `N + 2` entries: the input, each round's output, and the output
    /// of the final linear layer.
    ///
    /// `Anemoi = M ∘ R_N ∘ … ∘ R_1` with `R_i = H ∘ M ∘ (+c_i, +d_i)`, so the last entry is the
    /// permutation's output and the one before it is the last Flystel's.
    pub fn trace(&self, x: F, y: F) -> Vec<(F, F)> {
        let mut state = (x, y);
        let mut trace = Vec::with_capacity(self.parameters.rounds + 2);
        trace.push(state);
        for round in 0..self.parameters.rounds {
            let (x, y) = (state.0 + self.c[round], state.1 + self.d[round]);
            let (x, y) = Self::linear_layer(x, y);
            state = self.open_flystel(x, y);
            trace.push(state);
        }
        trace.push(Self::linear_layer(state.0, state.1));
        trace
    }

    /// The permutation.
    pub fn permutation(&self, x: F, y: F) -> (F, F) {
        *self
            .trace(x, y)
            .last()
            .expect("a trace always holds its input")
    }

    /// Whether `(0, y)` is a CICO solution: the permutation's first output word is zero.
    ///
    /// The check goes through the permutation rather than through any polynomial system, which is
    /// what makes it usable as a verifier for a claimed witness.
    pub fn is_cico_solution(&self, y: F) -> bool {
        self.permutation(F::zero(), y).0.is_zero()
    }

    /// A digest of the generator and the derived constants, lowercase hex, truncated to 16 digits.
    ///
    /// **Not** an identity: the parameters determine these. It is a regression pin on the
    /// derivation, and specifically on `g` — see the module docs.
    pub fn derived_digest(&self) -> String {
        let mut text = format!(
            "g {}\nbeta {}\ndelta {}\n",
            self.generator, self.beta, self.delta
        );
        for (c, d) in self.c.iter().zip(&self.d) {
            text.push_str(&format!("{} {}\n", c, d));
        }
        sha256_hex(text.as_bytes())[..16].to_string()
    }
}

/// A decimal string as a field element, by Horner's rule in the field itself.
///
/// The digits of π are three hundred and thirty-odd bits wide, so they cannot be reduced as a
/// `u64` or even a `u128`; folding them through the field's own arithmetic needs no wide integer
/// type and works unchanged over a 256-bit field.
///
/// # Panics
/// Panics on a character that is not a decimal digit. The two inputs are module constants.
fn from_decimal<F: KnownOrder>(digits: &str) -> F {
    let ten = F::new(10);
    digits.bytes().fold(F::zero(), |accumulator, byte| {
        assert!(byte.is_ascii_digit(), "pi is written in decimal digits");
        accumulator * ten + F::new(u64::from(byte - b'0'))
    })
}

/// `a^{-1} mod m`, or `None` when `gcd(a, m) ≠ 1`.
///
/// The extended Euclidean algorithm over `i128`, which is wide enough for a 64-bit modulus and
/// spares the caller a field with the wrong characteristic: the exponent lives modulo `p − 1`, not
/// modulo `p`.
fn modular_inverse(a: u64, m: u64) -> Option<u64> {
    let (mut old_r, mut r) = (a as i128, m as i128);
    let (mut old_s, mut s) = (1i128, 0i128);
    while r != 0 {
        let quotient = old_r / r;
        (old_r, r) = (r, old_r - quotient * r);
        (old_s, s) = (s, old_s - quotient * s);
    }
    if old_r != 1 {
        return None;
    }
    Some(old_s.rem_euclid(m as i128) as u64)
}

/// The smallest primitive root modulo a prime `p`, which is what Sage's
/// `F.multiplicative_generator()` returns.
///
/// Reproduced rather than tabulated because the generator is the single implementation-defined
/// input to Anemoi's constants, and a tabulated value could not be checked against the convention
/// it is supposed to follow. An element fails to generate exactly when its order divides
/// `(p − 1) / r` for some prime `r | p − 1`, so those quotients are the only exponents to test.
///
/// # Panics
/// Panics if `p < 3`, or if no primitive root is found below `p`, which cannot happen for a prime.
pub fn smallest_primitive_root(prime: u64) -> u64 {
    assert!(prime >= 3, "an odd prime modulus");
    let group_order = prime - 1;
    // The factorization is deterministic; the seed only fixes Pollard's rho's cycle choice.
    let mut rng = StdRng::seed_from_u64(0);
    let (prime_factors, _powers) = factor(&BigUInt::new_from_u64(group_order), &mut rng);
    let quotients: Vec<u64> = prime_factors
        .iter()
        .map(|r| group_order / u64_of(r))
        .collect();
    for candidate in 2..prime {
        if quotients
            .iter()
            .all(|e| power_mod(candidate, *e, prime) != 1)
        {
            return candidate;
        }
    }
    panic!("a prime field has a primitive root")
}

/// A `BigUInt` that is known to fit in a `u64`.
///
/// # Panics
/// Panics if it does not. Every caller here passes a prime factor of a `u64`.
fn u64_of(value: &BigUInt) -> u64 {
    let words = value.as_le_words();
    assert!(words.len() <= 1, "{:?} does not fit in a u64", value);
    *words.first().unwrap_or(&0)
}

/// `base^exponent mod modulus`, by square and multiply in 128 bits.
fn power_mod(base: u64, exponent: u64, modulus: u64) -> u64 {
    let mut result: u128 = 1;
    let mut square = u128::from(base % modulus);
    let modulus = u128::from(modulus);
    let mut exponent = exponent;
    while exponent > 0 {
        if exponent & 1 == 1 {
            result = result * square % modulus;
        }
        square = square * square % modulus;
        exponent >>= 1;
    }
    result as u64
}

#[cfg(test)]
mod tests {
    use super::{
        modular_inverse, smallest_primitive_root, Anemoi, AnemoiError, AnemoiParameters,
        ANEMOI_64_PRIME,
    };
    use crate::{
        fields::{PrimeFieldElement64, Zp18446744073709551263},
        identities::Zero,
        FiniteField,
    };

    type A = Zp18446744073709551263;

    /// CICO witnesses determined by committed reference data. `(rounds, input y, output y)`.
    ///
    /// Each one was extracted from the committed Magma logs of
    /// <https://github.com/IAIK/six-worlds-anemoi> at `fa056e6f`, file
    /// `results/anemoi_p18446744073709551263_n1_l1_a3_mFCICO_o1.txt`: the lexicographic Gröbner
    /// basis that file prints after its FGLM step is rooted, and each root is read back through the
    /// basis into the permutation's own input coordinates. The counts match the logs' own `nsols`
    /// line — two at `N = 1`, one at `N = 2`, none at `N = 3`, one at `N = 4` — so the extraction
    /// is checked against the reference as well as derived from it. See `docs/research/anemoi.md`.
    const REFERENCE_WITNESSES: [(usize, u64, u64); 4] = [
        (1, 8_431_162_935_045_355_170, 8_504_299_942_464_173_430),
        (1, 16_536_366_872_043_122_313, 10_906_135_472_056_154_455),
        (2, 1_761_853_426_583_392_112, 503_324_230_923_223_481),
        (4, 8_251_407_552_160_637_060, 17_265_183_214_956_306_941),
    ];

    /// The permutation reproduces the CICO witnesses the committed reference data determines.
    #[test]
    fn test_the_permutation_matches_the_reference_witnesses() {
        for (rounds, input, output) in REFERENCE_WITNESSES {
            let anemoi = Anemoi::<A>::new(AnemoiParameters::six_worlds(rounds)).expect("builds");
            let (x, y) = anemoi.permutation(A::zero(), A::new(input));
            assert_eq!(
                (x.value(), y.value()),
                (0, output),
                "N = {rounds}: Anemoi(0, {input}) disagrees with the reference"
            );
            assert!(anemoi.is_cico_solution(A::new(input)), "N = {rounds}");
        }
    }

    /// `g = 5` is the smallest primitive root modulo `2^64 - 353`, which is the generator the
    /// reference's `F.multiplicative_generator()` picks.
    #[test]
    fn test_the_generator_is_the_smallest_primitive_root() {
        assert_eq!(smallest_primitive_root(ANEMOI_64_PRIME), 5);
        // A few small primes, where the answer can be checked by hand.
        assert_eq!(smallest_primitive_root(7), 3);
        assert_eq!(smallest_primitive_root(13), 2);
        assert_eq!(smallest_primitive_root(41), 6);
    }

    /// The round constants recomputed from the digits of π match their recorded values.
    ///
    /// Recorded rather than derived a second way: these are the numbers the reference produces, and
    /// the first pair is checkable in closed form — `π₀^0 = π₁^0 = 1`, so `c_1 = g + 2^α = 13` and
    /// `d_1 = g + 2^α + g^{-1}`.
    #[test]
    fn test_the_round_constants_are_pinned() {
        let anemoi = Anemoi::<A>::new(AnemoiParameters::six_worlds(5)).expect("builds");
        let c: Vec<u64> = anemoi.c.iter().map(|v| v.value()).collect();
        let d: Vec<u64> = anemoi.d.iter().map(|v| v.value()).collect();
        assert_eq!(
            c,
            vec![
                13,
                14_287_774_856_857_954_554,
                8_999_056_095_094_019_761,
                12_899_385_816_367_507_875,
                2_270_561_764_904_420_494
            ]
        );
        assert_eq!(
            d,
            vec![
                11_068_046_444_225_730_771,
                15_959_905_577_595_835_109,
                11_084_673_350_989_441_074,
                5_232_356_167_390_961_010,
                13_624_654_174_387_339_041
            ]
        );
        // c_1 = g + 2^alpha and d_1 = c_1 + g^{-1}, both in closed form at round one.
        assert_eq!(c[0], anemoi.generator + 8);
        assert_eq!(A::new(d[0]), A::new(c[0]) + anemoi.delta);
        // A shorter instance is the same instance truncated: the constants depend on the round
        // index alone, so a ladder's rungs share a prefix rather than each having its own schedule.
        let shorter = Anemoi::<A>::new(AnemoiParameters::six_worlds(2)).expect("builds");
        assert_eq!(shorter.c, anemoi.c[..2]);
        assert_eq!(shorter.d, anemoi.d[..2]);
    }

    /// The derived constants are pinned, so a changed generator cannot pass as the same instance.
    ///
    /// This is the check a parameter digest cannot make: `p`, `α`, `ℓ` and `N` would be unchanged
    /// if `smallest_primitive_root` started returning something else, and every constant would
    /// move.
    #[test]
    fn test_the_derived_constants_are_pinned() {
        for (rounds, digest) in [
            (1, "3f2d4387eb09c4a9"),
            (3, "d8c8c56669d10e61"),
            (5, "2273108e11bbbeae"),
        ] {
            let anemoi = Anemoi::<A>::new(AnemoiParameters::six_worlds(rounds)).expect("builds");
            assert_eq!(anemoi.derived_digest(), digest, "N = {rounds}");
        }
    }

    /// The open Flystel is a permutation of the state, and its inverse is the degree-`α` relation
    /// the polynomial models use.
    #[test]
    fn test_the_open_flystel_inverts_as_the_models_assume() {
        let anemoi = Anemoi::<A>::new(AnemoiParameters::six_worlds(1)).expect("builds");
        for seed in 1u64..20 {
            let (x, y) = (A::new(seed * 7 + 1), A::new(seed * 13 + 5));
            let (u, v) = anemoi.open_flystel(x, y);
            // x = beta*y^2 + (y - v)^alpha and u = beta*v^2 + delta + (y - v)^alpha.
            let powered = (y - v).pow(3);
            assert_eq!(anemoi.beta * y * y + powered, x);
            assert_eq!(anemoi.beta * v * v + anemoi.delta + powered, u);
        }
    }

    /// The linear layer is `(2x + y, x + y)` and its stated inverse really inverts it.
    #[test]
    fn test_the_linear_layer_and_its_inverse_agree() {
        for seed in 0u64..10 {
            let (x, y) = (A::new(seed * 3 + 2), A::new(seed * 11 + 7));
            let forward = Anemoi::<A>::linear_layer(x, y);
            assert_eq!(forward, (x + x + y, x + y));
            assert_eq!(
                Anemoi::<A>::inverse_linear_layer(forward.0, forward.1),
                (x, y)
            );
        }
    }

    /// The trace has `N + 2` states, ends at the permutation's output, and its last two entries
    /// differ by exactly the final linear layer.
    #[test]
    fn test_the_trace_ends_with_the_final_linear_layer() {
        let anemoi = Anemoi::<A>::new(AnemoiParameters::six_worlds(4)).expect("builds");
        let (x, y) = (A::new(3), A::new(5));
        let trace = anemoi.trace(x, y);
        assert_eq!(trace.len(), 6);
        assert_eq!(trace[0], (x, y));
        assert_eq!(trace[5], anemoi.permutation(x, y));
        let last_flystel = trace[4];
        assert_eq!(
            Anemoi::<A>::linear_layer(last_flystel.0, last_flystel.1),
            trace[5]
        );
    }

    /// A coefficient type that is not the parameters' field is refused rather than used.
    #[test]
    fn test_the_field_is_enforced() {
        let wrong = Anemoi::<PrimeFieldElement64<31>>::new(AnemoiParameters::six_worlds(3));
        assert!(matches!(wrong, Err(AnemoiError::FieldMismatch { .. })));
    }

    /// Parameters this module does not implement are refused by name.
    #[test]
    fn test_unsupported_parameters_are_refused_by_name() {
        let two_columns = AnemoiParameters {
            l: 2,
            ..AnemoiParameters::six_worlds(3)
        };
        assert_eq!(
            Anemoi::<A>::new(two_columns).err(),
            Some(AnemoiError::UnsupportedColumns { l: 2 })
        );
        assert_eq!(
            Anemoi::<A>::new(AnemoiParameters::six_worlds(0)).err(),
            Some(AnemoiError::NoRounds)
        );
        // 2^64 - 354 is divisible by 13, so alpha = 13 has no inverse modulo the group order.
        let bad_alpha = AnemoiParameters {
            alpha: 13,
            ..AnemoiParameters::six_worlds(3)
        };
        assert_eq!(
            Anemoi::<A>::new(bad_alpha).err(),
            Some(AnemoiError::AlphaNotCoprime {
                alpha: 13,
                prime: ANEMOI_64_PRIME
            })
        );
    }

    /// `alpha^{-1} mod (p - 1)` is the exponent the Flystel's inverse power map needs.
    #[test]
    fn test_the_inverse_exponent_is_a_group_order_inverse() {
        let group_order = ANEMOI_64_PRIME - 1;
        let inverse = modular_inverse(3, group_order).expect("3 is coprime with p - 1");
        assert_eq!(inverse, 12_297_829_382_473_034_175);
        assert_eq!((3u128 * u128::from(inverse)) % u128::from(group_order), 1);
        assert_eq!(modular_inverse(13, group_order), None);
    }
}
