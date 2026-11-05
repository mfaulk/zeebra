//! Poseidon, and polynomial systems that provably represent it.
//!
//! Ported from the official cryptanalysis tooling,
//! <https://github.com/khovratovich/poseidon-tools> at commit
//! `60075da7c0521d9493749a035b1f30d4eda37138` (Apache-2.0): the Grain LFSR round constants, the
//! Cauchy MDS construction, and the round schedule. The parameters are the 2026 initiative's own —
//! KoalaBear, `alpha = 3`, `t = 16` — rather than toy substitutes, which is the difference between
//! "a Poseidon-shaped system" and this challenge's system.
//!
//! # What makes the system faithful, and how it is checked
//!
//! The S-box is `y = x^alpha`. If each state word were carried as a polynomial in the inputs, the
//! degree would be `alpha^rounds` and the system would be unusable by the third round. So **every
//! S-box output is a fresh variable**: with `L` the linear form reaching an S-box, the equation is
//! `y - L^alpha = 0`, degree `alpha` and no more, and the next round's words are linear forms in
//! the new variables. The round constants and the MDS layer contribute no equations at all — they
//! are affine, and affine maps compose into the linear forms.
//!
//! That is the standard formulation, and it is also the one that can be *checked*: a trace of the
//! real permutation assigns every variable, and a faithful system vanishes at that assignment.
//! [`verify_against_trace`] does exactly that, and a system that merely looked right would fail it.
//!
//! Vanishing at one point is necessary and not sufficient — the zero system vanishes everywhere —
//! so the tests also **corrupt** individual trace values and assert that the expected equations
//! stop vanishing, and that the ones that should not care still do.
//!
//! # Exact constraints, not the relaxed verifier
//!
//! The bounty ships a relaxed CICO verifier accepting any output whose low `m` bits match the
//! target. That condition is on the **canonical integer representative** of a field element, and
//! it is not a polynomial equation over the field — `(y - c) & mask == 0` is a statement about
//! `y - c` as an integer in `[0, p)`, which no polynomial identity expresses. Nothing here models
//! it as one. The systems generated are the **exact** reduced-round constraints; the relaxed
//! verifier is a thing to run against the reference implementation, not to hand to F4.
//!
//! # Reduced-round is reduced, and so is reduced-width
//!
//! A system small enough to solve needs fewer rounds *and* a narrower state than the bounty's
//! `t = 16`, which already costs 16 variables per full round. Both are reductions and both are
//! recorded in [`CicoInstance`]. **No result on a reduced instance says anything about the full
//! one**, and nothing in this module should be quoted as if it did.
//!
//! # What is not ported
//!
//! `verify_mds_matrix` — the reference's subspace-trail and invariant-subspace checks on the MDS
//! matrix. Those validate a *parameter choice*; they are not part of the round function, and the
//! Cauchy matrix this generates is the same one the reference generates, which the tests pin
//! against recorded values. Re-deriving its security criteria here would be reimplementing the
//! reference's job.

use std::fmt::{Display, Formatter};

use crate::{FiniteField, KnownOrder, Monomial, MultivariatePolynomial};

/// KoalaBear: `2^31 - 2^24 + 1`. Every 2026 initiative challenge is over this field.
pub const KOALABEAR_PRIME: u64 = 2_130_706_433;

/// The 80-bit Grain LFSR that derives Poseidon's round constants.
///
/// Feedback polynomial `x^80 + x^62 + x^51 + x^38 + x^23 + x^13 + 1`. `state[0]` is the output
/// bit; after each clock the state shifts left and the feedback bit enters at the end.
///
/// A direct port, bit layout included, because the constants are only the challenge's constants if
/// they come out identical — and "identical" is checked against recorded values rather than
/// reasoned about.
pub struct GrainLfsr {
    state: [u8; 80],
    prime_bits: u32,
}

impl GrainLfsr {
    /// Seed from the Poseidon parameters.
    ///
    /// Bits 0-1 are the field type (`10`, prime field); bit 2 the S-box type; bits 3-7 `alpha` in
    /// five bits; then `prime_bits`, `t`, `r_f`, `r_p` in ten bits each, MSB first; bits 48-79 all
    /// ones. 160 output bits are then discarded.
    pub fn new(prime_bits: u32, alpha: i64, t: usize, r_f: usize, r_p: usize) -> Self {
        let mut lfsr = Self {
            state: [0; 80],
            prime_bits,
        };

        lfsr.state[0] = 1;
        lfsr.state[1] = 0;
        // The inverse S-box is `alpha == -1`, and contributes a zero exponent field.
        lfsr.state[2] = u8::from(alpha == -1);
        let exponent = if alpha == -1 { 0 } else { alpha as u64 };
        lfsr.set_bits(3, exponent, 5);
        lfsr.set_bits(8, prime_bits as u64, 10);
        lfsr.set_bits(18, t as u64, 10);
        lfsr.set_bits(28, r_f as u64, 10);
        lfsr.set_bits(38, r_p as u64, 10);
        for bit in lfsr.state.iter_mut().skip(48) {
            *bit = 1;
        }

        for _ in 0..160 {
            lfsr.clock();
        }
        lfsr
    }

    /// Store `value` in `bits` cells from `offset`, most significant first.
    fn set_bits(&mut self, offset: usize, value: u64, bits: u32) {
        for i in 0..bits {
            self.state[offset + i as usize] = ((value >> (bits - 1 - i)) & 1) as u8;
        }
    }

    /// Advance one step, returning the bit clocked out.
    fn clock(&mut self) -> u8 {
        let feedback = self.state[0]
            ^ self.state[13]
            ^ self.state[23]
            ^ self.state[38]
            ^ self.state[51]
            ^ self.state[62];
        let output = self.state[0];
        self.state.rotate_left(1);
        self.state[79] = feedback;
        output
    }

    /// The next element of `GF(prime)`, by rejection sampling.
    ///
    /// `prime_bits` bits are taken MSB first and the value discarded if it is at least `prime`, so
    /// the distribution is uniform. The rejected bits are consumed, which is why this cannot be
    /// reordered against other draws.
    pub fn next_element(&mut self, prime: u64) -> u64 {
        loop {
            let mut value: u64 = 0;
            for _ in 0..self.prime_bits {
                value = (value << 1) | u64::from(self.clock());
            }
            if value < prime {
                return value;
            }
        }
    }
}

/// A Poseidon instance's parameters.
///
/// No security-level selection: these are taken as given, as the reference does, because a
/// generator that chose its own parameters could not be said to reproduce anyone else's.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct PoseidonParameters {
    /// The field modulus. Must match the coefficient type.
    pub prime: u64,

    /// The S-box exponent. Only positive exponents are supported here; the reference's inverse
    /// S-box has no polynomial form of bounded degree and is out of scope.
    pub alpha: u32,

    /// State width.
    pub t: usize,

    /// Full rounds. Must be even, split half before and half after the partial rounds.
    pub r_f: usize,

    /// Partial rounds, each applying the S-box to word 0 only.
    pub r_p: usize,
}

impl PoseidonParameters {
    /// The 2026 initiative's CICO parameters: KoalaBear, `alpha = 3`, `t = 16`, `R_F = 6`.
    ///
    /// `R_P` is the bounty's hardest offered value, 8. These are the real parameters and they are
    /// **far** beyond what the solvers reach — `t * R_F + R_P = 104` S-box variables before the
    /// free inputs. Provided so that a reduced instance can state exactly what it reduced *from*.
    pub fn bounty_cico() -> Self {
        Self {
            prime: KOALABEAR_PRIME,
            alpha: 3,
            t: 16,
            r_f: 6,
            r_p: 8,
        }
    }

    /// S-box applications, which is the number of nonlinear equations a system needs.
    pub fn sboxes(&self) -> usize {
        self.t * self.r_f + self.r_p
    }

    /// Rounds in total.
    pub fn rounds(&self) -> usize {
        self.r_f + self.r_p
    }
}

impl Display for PoseidonParameters {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "p = {}, alpha = {}, t = {}, R_F = {}, R_P = {}",
            self.prime, self.alpha, self.t, self.r_f, self.r_p
        )
    }
}

/// Why a Poseidon instance or system could not be built.
///
/// Not `Copy`: [`Self::FieldMismatch`] names the field it found, and naming it is the point.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PoseidonError {
    /// `r_f` is odd, which the round schedule cannot split.
    OddFullRounds { r_f: usize },

    /// The coefficient type's order is not the parameters' prime.
    ///
    /// Checked, because a mismatch produces a system that is Poseidon over the wrong field and
    /// says nothing — and is otherwise silent.
    FieldMismatch { expected: u64, found: String },

    /// A state of the wrong width was supplied.
    WrongStateWidth { expected: usize, found: usize },

    /// The requested `const N` is not the system's variable count.
    ///
    /// Exact rather than "at least": a spare position is an **unconstrained variable**, which makes
    /// the ideal positive-dimensional and the zero-dimensional solvers refuse it. See
    /// [`CicoInstance::system`].
    WrongDimension { needed: usize, requested: usize },

    /// More constrained words than the state has.
    TooManyConstraints { k: usize, t: usize },

    /// `constants` is not `2k` long: `k` input constants then `k` output targets.
    WrongConstantCount { expected: usize, found: usize },
}

impl Display for PoseidonError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::OddFullRounds { r_f } => {
                write!(f, "R_F must be even to split the schedule, got {}", r_f)
            }
            Self::FieldMismatch { expected, found } => write!(
                f,
                "the parameters are over GF({}) and the coefficient type is {}",
                expected, found
            ),
            Self::WrongStateWidth { expected, found } => {
                write!(f, "the state must have {} words, got {}", expected, found)
            }
            Self::WrongDimension { needed, requested } => write!(
                f,
                "the system has {} variables and was requested at {}; spare positions would be \
                 unconstrained variables",
                needed, requested
            ),
            Self::WrongConstantCount { expected, found } => write!(
                f,
                "a CICO instance needs exactly {} constants (k inputs then k targets), got {}",
                expected, found
            ),
            Self::TooManyConstraints { k, t } => {
                write!(
                    f,
                    "k = {} constrained words exceeds the state width {}",
                    k, t
                )
            }
        }
    }
}

impl std::error::Error for PoseidonError {}

/// A Poseidon permutation with its constants and matrix fixed.
///
/// Constructible only through [`Poseidon::new`], which checks that `F` really is the field the
/// parameters name — so a value of this type is a permutation over the right field by
/// construction.
#[derive(Clone, Debug)]
pub struct Poseidon<F: KnownOrder> {
    /// The parameters.
    pub parameters: PoseidonParameters,

    /// `rounds * t` constants, one row per round.
    pub round_constants: Vec<Vec<F>>,

    /// The `t x t` MDS matrix.
    pub mds: Vec<Vec<F>>,
}

impl<F: KnownOrder> Poseidon<F> {
    /// Derive the constants and matrix from the parameters, as the reference does.
    ///
    /// `F: KnownOrder` rather than `F: FiniteField`, and the bound is load-bearing: the field
    /// identity is **enforced here** rather than left to a separate check a caller must remember.
    /// A mismatched coefficient type produces a completely different permutation while retaining
    /// the Poseidon parameter metadata, and nothing about the result looks wrong.
    ///
    /// # Errors
    /// [`PoseidonError::OddFullRounds`] if `r_f` is odd, or
    /// [`PoseidonError::FieldMismatch`] if `F` is not the field `parameters.prime` names.
    pub fn new(parameters: PoseidonParameters) -> Result<Self, PoseidonError> {
        if !parameters.r_f.is_multiple_of(2) {
            return Err(PoseidonError::OddFullRounds {
                r_f: parameters.r_f,
            });
        }
        // Compared as limb slices, so the check is right for a field whose order exceeds a `u64`
        // even though no Poseidon parameter set here needs one.
        if F::order_limbs() != [parameters.prime] {
            return Err(PoseidonError::FieldMismatch {
                expected: parameters.prime,
                found: format!("a field of order {:?}", F::order_limbs()),
            });
        }

        let prime = parameters.prime;
        let prime_bits = 64 - prime.leading_zeros();
        let mut lfsr = GrainLfsr::new(
            prime_bits,
            parameters.alpha as i64,
            parameters.t,
            parameters.r_f,
            parameters.r_p,
        );
        let round_constants = (0..parameters.rounds())
            .map(|_| {
                (0..parameters.t)
                    .map(|_| F::new(lfsr.next_element(prime)))
                    .collect()
            })
            .collect();

        Ok(Self {
            parameters,
            round_constants,
            mds: Self::cauchy_mds(parameters.t, prime),
        })
    }

    /// The Cauchy MDS matrix: `M[i][j] = (i - t - j)^{-1} mod p`.
    ///
    /// `x_i = i` and `y_j = t + j`, so `x_i - y_j` is never zero for `p > 2t`.
    fn cauchy_mds(t: usize, prime: u64) -> Vec<Vec<F>> {
        (0..t)
            .map(|i| {
                (0..t)
                    .map(|j| {
                        // `i - t - j` as a residue, computed in the integers to avoid a negative
                        // intermediate.
                        let difference = (prime as i128 + i as i128 - t as i128 - j as i128)
                            .rem_euclid(prime as i128)
                            as u64;
                        F::new(difference).inverse()
                    })
                    .collect()
            })
            .collect()
    }

    /// `M * state`.
    fn apply_mds(&self, state: &[F]) -> Vec<F> {
        self.mds
            .iter()
            .map(|row| {
                row.iter()
                    .zip(state)
                    .fold(F::zero(), |acc, (m, s)| acc + *m * *s)
            })
            .collect()
    }

    /// `x^alpha`.
    fn sbox(&self, x: F) -> F {
        x.pow(self.parameters.alpha as u128)
    }

    /// The permutation, with an initial linear layer.
    ///
    /// The variant the CICO verifier uses: `permutation_plus_linear` in the reference.
    ///
    /// # Errors
    /// [`PoseidonError::WrongStateWidth`].
    pub fn permutation_plus_linear(&self, state: &[F]) -> Result<Vec<F>, PoseidonError> {
        self.run(state, true).map(|trace| trace.output)
    }

    /// The permutation, without an initial linear layer.
    ///
    /// # Errors
    /// [`PoseidonError::WrongStateWidth`].
    pub fn permutation(&self, state: &[F]) -> Result<Vec<F>, PoseidonError> {
        self.run(state, false).map(|trace| trace.output)
    }

    /// Run the permutation, recording every S-box output.
    ///
    /// The trace is what makes independent verification possible: it assigns every variable a
    /// generated system has, so a faithful system vanishes at it.
    ///
    /// # Errors
    /// [`PoseidonError::WrongStateWidth`].
    pub fn run(
        &self,
        state: &[F],
        initial_linear: bool,
    ) -> Result<PoseidonTrace<F>, PoseidonError> {
        let t = self.parameters.t;
        if state.len() != t {
            return Err(PoseidonError::WrongStateWidth {
                expected: t,
                found: state.len(),
            });
        }

        let mut current: Vec<F> = state.to_vec();
        if initial_linear {
            current = self.apply_mds(&current);
        }

        // Recorded in the order the generator introduces its variables, which is what lets a trace
        // be zipped straight onto an assignment.
        let mut sbox_outputs: Vec<F> = Vec::with_capacity(self.parameters.sboxes());
        let half = self.parameters.r_f / 2;
        let mut round = 0;

        let full_round = |current: &mut Vec<F>, round: usize, outputs: &mut Vec<F>| {
            for (word, constant) in current.iter_mut().zip(&self.round_constants[round]) {
                *word += *constant;
            }
            for word in current.iter_mut() {
                *word = self.sbox(*word);
                outputs.push(*word);
            }
            *current = self.apply_mds(current);
        };

        for _ in 0..half {
            full_round(&mut current, round, &mut sbox_outputs);
            round += 1;
        }
        for _ in 0..self.parameters.r_p {
            for (word, constant) in current.iter_mut().zip(&self.round_constants[round]) {
                *word += *constant;
            }
            current[0] = self.sbox(current[0]);
            sbox_outputs.push(current[0]);
            current = self.apply_mds(&current);
            round += 1;
        }
        for _ in 0..half {
            full_round(&mut current, round, &mut sbox_outputs);
            round += 1;
        }

        Ok(PoseidonTrace {
            input: state.to_vec(),
            sbox_outputs,
            output: current,
        })
    }
}

/// Everything a run of the permutation computed, in the order a generated system names it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PoseidonTrace<F: KnownOrder> {
    /// The input state.
    pub input: Vec<F>,

    /// Every S-box output, in round order and within a round in word order.
    ///
    /// Length [`PoseidonParameters::sboxes`]. This is the assignment to a generated system's
    /// S-box variables.
    pub sbox_outputs: Vec<F>,

    /// The output state.
    pub output: Vec<F>,
}

/// A CICO instance: fix `k` input words and `k` output words, solve for the rest.
///
/// `P(C_1, …, C_k, x_{k+1}, …, x_t)[i] = C_{k+1+i}` for `i < k`, with the remaining output words
/// unconstrained. The bounty's instance is `k = 2`, `t = 16`, KoalaBear,
/// `C_1 = 0xc09de4`, `C_2 = 0xee6282`, `C_3 = C_4 = 0`.
#[derive(Clone, Debug)]
pub struct CicoInstance<F: KnownOrder> {
    /// The permutation.
    pub poseidon: Poseidon<F>,

    /// Constrained words at each end.
    pub k: usize,

    /// `[C_1, …, C_k, C_{k+1}, …, C_{2k}]`: the input constants then the output targets.
    pub constants: Vec<F>,

    /// What this instance reduced from, if it is a reduction.
    ///
    /// Carried so that a result cannot be quoted without it. `None` means the parameters *are* the
    /// full ones.
    pub reduced_from: Option<PoseidonParameters>,
}

impl<F: KnownOrder> CicoInstance<F> {
    /// An instance over the given permutation.
    ///
    /// `constants` must be exactly `2k` long: the `k` input constants then the `k` output targets.
    /// Checked rather than assumed, because `system` and `is_solution` index `constants[k + i]` —
    /// so a short vector returned `Ok` here and panicked later, which is the worst place for a
    /// caller to find out.
    ///
    /// # Errors
    /// [`PoseidonError::TooManyConstraints`] if `k > t`, or
    /// [`PoseidonError::WrongConstantCount`] if `constants.len() != 2 * k`.
    pub fn new(
        poseidon: Poseidon<F>,
        k: usize,
        constants: Vec<F>,
        reduced_from: Option<PoseidonParameters>,
    ) -> Result<Self, PoseidonError> {
        if k > poseidon.parameters.t {
            return Err(PoseidonError::TooManyConstraints {
                k,
                t: poseidon.parameters.t,
            });
        }
        if constants.len() != 2 * k {
            return Err(PoseidonError::WrongConstantCount {
                expected: 2 * k,
                found: constants.len(),
            });
        }
        Ok(Self {
            poseidon,
            k,
            constants,
            reduced_from,
        })
    }

    /// An instance whose target output is the one a chosen input actually produces.
    ///
    /// The analogue of the `planted` benchmark family, and it exists because **a CICO instance
    /// with an arbitrary target may simply have no base-field solution.** With `k = 1`, `t = 2`,
    /// `R_F = 2` and target zero, the reduced instance measured for this module returns
    /// `NoBaseFieldPoint` — a correct answer, and useless as a demonstration, because a solver
    /// that found nothing and a solver that was broken look identical.
    ///
    /// Planting removes that ambiguity: the permutation is run on `[C_1, …, C_k, free…]` and the
    /// first `k` output words become the targets, so `free` **is** a solution and the solver must
    /// find it or another one. The planted value appears nowhere in the generated system.
    ///
    /// # Errors
    /// [`PoseidonError::WrongStateWidth`] if `free` is not `t - k` long, and
    /// [`PoseidonError::TooManyConstraints`] as [`Self::new`].
    pub fn planted(
        poseidon: Poseidon<F>,
        k: usize,
        inputs: &[F],
        free: &[F],
        reduced_from: Option<PoseidonParameters>,
    ) -> Result<Self, PoseidonError> {
        let t = poseidon.parameters.t;
        // Before `t - k`, which would underflow. In release mode that wraps to a vast number and
        // the width check below then passes for almost any input, so the documented error path was
        // unreachable exactly when it was needed.
        if k > t {
            return Err(PoseidonError::TooManyConstraints { k, t });
        }
        if inputs.len() != k || free.len() != t - k {
            return Err(PoseidonError::WrongStateWidth {
                expected: t,
                found: inputs.len() + free.len(),
            });
        }
        let mut state = inputs.to_vec();
        state.extend_from_slice(free);
        let output = poseidon.permutation_plus_linear(&state)?;

        let mut constants = inputs.to_vec();
        constants.extend_from_slice(&output[..k]);
        Self::new(poseidon, k, constants, reduced_from)
    }

    /// Whether `free` solves this instance, checked by running the permutation.
    ///
    /// **The verification that matters**, and the one the plan asks for: it goes through the
    /// permutation rather than through the polynomial system, so it is independent of every step
    /// between the two. A bug in the generator cannot make this pass.
    ///
    /// # Errors
    /// [`PoseidonError::WrongStateWidth`] if `free` is not `t - k` long.
    pub fn is_solution(&self, free: &[F]) -> Result<bool, PoseidonError> {
        let t = self.poseidon.parameters.t;
        if free.len() != t - self.k {
            return Err(PoseidonError::WrongStateWidth {
                expected: t - self.k,
                found: free.len(),
            });
        }
        let mut state = self.constants[..self.k].to_vec();
        state.extend_from_slice(free);
        let output = self.poseidon.permutation_plus_linear(&state)?;
        Ok(output[..self.k] == self.constants[self.k..2 * self.k])
    }

    /// Free input words: `t - k`.
    pub fn free_inputs(&self) -> usize {
        self.poseidon.parameters.t - self.k
    }

    /// Variables the system needs: free inputs, then one per S-box.
    ///
    /// Free inputs first so that the ones a caller specializes are the low indices, which is also
    /// the order a trace's assignment is built in.
    pub fn variables(&self) -> usize {
        self.free_inputs() + self.poseidon.parameters.sboxes()
    }

    /// Equations the system has: one per S-box, plus `k` output constraints.
    pub fn equations(&self) -> usize {
        self.poseidon.parameters.sboxes() + self.k
    }

    /// The polynomial system, at a compile-time dimension.
    ///
    /// Every equation has degree exactly `alpha` except the `k` output constraints, which are
    /// affine. See the module docs for why the degree does not compound.
    ///
    /// # `N` must be exactly [`Self::variables`]
    ///
    /// An earlier version permitted `N` larger, on the reasoning that spare positions are simply
    /// unused. They are not harmless: a variable appearing in no equation is **unconstrained**, so
    /// the ideal gains a free coordinate per spare position and becomes positive-dimensional — and
    /// the zero-dimensional solvers then refuse a system that was meant to be solvable. That is
    /// the same trap `Specialization::apply` fell into with its pinning equations, and exact
    /// dimensions are the safer contract for a research-import API.
    ///
    /// # Errors
    /// [`PoseidonError::WrongDimension`] if `N` is not [`Self::variables`]. The field is not
    /// checked here because it cannot be wrong: [`Poseidon::new`] enforces it.
    pub fn system<const N: usize>(
        &self,
    ) -> Result<Vec<MultivariatePolynomial<N, F>>, PoseidonError> {
        let needed = self.variables();
        if N != needed {
            return Err(PoseidonError::WrongDimension {
                needed,
                requested: N,
            });
        }

        let t = self.poseidon.parameters.t;
        let alpha = self.poseidon.parameters.alpha;
        let mut equations: Vec<MultivariatePolynomial<N, F>> = Vec::with_capacity(self.equations());

        // The state, each word an affine polynomial in the variables introduced so far. Round
        // constants and the MDS layer keep it affine, which is why they contribute no equations.
        let mut state: Vec<MultivariatePolynomial<N, F>> = (0..t)
            .map(|i| {
                if i < self.k {
                    constant_poly(self.constants[i])
                } else {
                    variable_poly(i - self.k)
                }
            })
            .collect();

        // The CICO verifier applies the MDS before the first round.
        state = self.mds_of(&state);

        let mut next_variable = self.free_inputs();
        let half = self.poseidon.parameters.r_f / 2;
        let mut round = 0;

        for _ in 0..half {
            self.full_round(&mut state, round, &mut next_variable, &mut equations, alpha);
            round += 1;
        }
        for _ in 0..self.poseidon.parameters.r_p {
            self.add_constants(&mut state, round);
            // Word 0 only.
            let fresh = variable_poly(next_variable);
            equations.push(fresh.clone() - power(&state[0], alpha));
            state[0] = fresh;
            next_variable += 1;
            state = self.mds_of(&state);
            round += 1;
        }
        for _ in 0..half {
            self.full_round(&mut state, round, &mut next_variable, &mut equations, alpha);
            round += 1;
        }

        // The output constraints: affine, one per constrained word.
        for i in 0..self.k {
            equations.push(state[i].clone() - constant_poly(self.constants[self.k + i]));
        }

        debug_assert_eq!(next_variable, needed);
        debug_assert_eq!(equations.len(), self.equations());
        Ok(equations)
    }

    /// One full round: constants, then an S-box per word, then the MDS layer.
    fn full_round<const N: usize>(
        &self,
        state: &mut Vec<MultivariatePolynomial<N, F>>,
        round: usize,
        next_variable: &mut usize,
        equations: &mut Vec<MultivariatePolynomial<N, F>>,
        alpha: u32,
    ) {
        self.add_constants(state, round);
        for word in state.iter_mut() {
            let fresh = variable_poly(*next_variable);
            equations.push(fresh.clone() - power(word, alpha));
            *word = fresh;
            *next_variable += 1;
        }
        *state = self.mds_of(state);
    }

    /// Add round `round`'s constants to the state.
    fn add_constants<const N: usize>(
        &self,
        state: &mut [MultivariatePolynomial<N, F>],
        round: usize,
    ) {
        for (word, constant) in state.iter_mut().zip(&self.poseidon.round_constants[round]) {
            *word = word.clone() + constant_poly(*constant);
        }
    }

    /// `M * state`, over polynomials.
    fn mds_of<const N: usize>(
        &self,
        state: &[MultivariatePolynomial<N, F>],
    ) -> Vec<MultivariatePolynomial<N, F>> {
        self.poseidon
            .mds
            .iter()
            .map(|row| {
                row.iter()
                    .zip(state)
                    .fold(MultivariatePolynomial::zero(), |acc, (m, word)| {
                        acc + word.scale(m)
                    })
            })
            .collect()
    }

    /// The assignment a trace gives to the system's variables.
    ///
    /// Free inputs then S-box outputs, matching [`Self::variables`]'s order. The free inputs come
    /// from the trace's *input* state, after the constrained prefix.
    pub fn assignment<const N: usize>(&self, trace: &PoseidonTrace<F>) -> [F; N] {
        let mut point = [F::zero(); N];
        for (i, value) in trace.input.iter().skip(self.k).enumerate() {
            point[i] = *value;
        }
        for (i, value) in trace.sbox_outputs.iter().enumerate() {
            point[self.free_inputs() + i] = *value;
        }
        point
    }

    /// Whether the coefficient type's order is the parameters' prime.
    ///
    /// Not folded into [`Self::system`], which is generic over `F: FiniteField` and so has no
    /// order to read. A caller with a [`KnownOrder`](crate::KnownOrder) type should check once.
    pub fn check_field(prime: u64, order: &[u64]) -> Result<(), PoseidonError> {
        if order == [prime] {
            Ok(())
        } else {
            Err(PoseidonError::FieldMismatch {
                expected: prime,
                found: format!("a field of order {:?}", order),
            })
        }
    }
}

/// The constant polynomial `c`.
fn constant_poly<const N: usize, F: FiniteField>(c: F) -> MultivariatePolynomial<N, F> {
    MultivariatePolynomial::new(&[(Monomial::one(), c)])
}

/// The polynomial `x_index`.
fn variable_poly<const N: usize, F: FiniteField>(index: usize) -> MultivariatePolynomial<N, F> {
    MultivariatePolynomial::new(&[(Monomial::univariate(index, 1), F::one())])
}

/// `p^alpha`, by repeated multiplication.
///
/// `alpha` is 3 or 5 in practice, so this is two or four multiplications and squaring tricks would
/// be noise.
fn power<const N: usize, F: FiniteField>(
    p: &MultivariatePolynomial<N, F>,
    alpha: u32,
) -> MultivariatePolynomial<N, F> {
    let mut acc = MultivariatePolynomial::one();
    for _ in 0..alpha {
        acc *= p.clone();
    }
    acc
}

/// Whether every equation of `system` vanishes at `trace`'s assignment.
///
/// The faithfulness check. `system` must be what `instance.system::<N>()` returned, and the trace
/// must come from the same [`Poseidon`] — otherwise this is comparing two different things and
/// will say so by failing.
///
/// Returns the indices of the equations that did **not** vanish, so a failure says which part of
/// the round schedule is wrong rather than only that something is.
pub fn verify_against_trace<const N: usize, F: KnownOrder>(
    instance: &CicoInstance<F>,
    system: &[MultivariatePolynomial<N, F>],
    trace: &PoseidonTrace<F>,
) -> Vec<usize> {
    let point: [F; N] = instance.assignment(trace);
    system
        .iter()
        .enumerate()
        .filter(|(_, p)| !p.eval(&point).is_zero())
        .map(|(i, _)| i)
        .collect()
}

#[cfg(test)]
mod tests {
    use super::{
        verify_against_trace, CicoInstance, GrainLfsr, Poseidon, PoseidonError, PoseidonParameters,
        KOALABEAR_PRIME,
    };
    use crate::{
        fields::PrimeFieldElement64, FiniteField, Monomial, MultivariatePolynomial, One, Zero,
    };

    /// KoalaBear, the field every 2026 initiative challenge is over.
    type K = PrimeFieldElement64<KOALABEAR_PRIME>;

    /// The reference's own `t = 16, R_F = 8, R_P = 20` instance, whose outputs its README records.
    fn reference_instance() -> Poseidon<K> {
        Poseidon::new(PoseidonParameters {
            prime: KOALABEAR_PRIME,
            alpha: 3,
            t: 16,
            r_f: 8,
            r_p: 20,
        })
        .expect("R_F is even")
    }

    /// A permutation output recorded from the Python reference, not from this port.
    ///
    /// Generated by `poseidon-tools` at commit `60075da7` and pasted here. The independence is the
    /// point: the port and the polynomial generator live in one Rust module, so a shared mistake
    /// in the round schedule would be invisible to any test comparing them against each other.
    struct ReferenceVector {
        t: usize,
        r_f: usize,
        r_p: usize,
        input: &'static [u64],
        permutation: &'static [u64],
        plus_linear: &'static [u64],
    }

    const REFERENCE_VECTORS: &[ReferenceVector] = &[
        ReferenceVector {
            t: 2,
            r_f: 2,
            r_p: 0,
            input: &[1, 2],
            permutation: &[1643460181, 843134410],
            plus_linear: &[123910189, 305195254],
        },
        ReferenceVector {
            t: 2,
            r_f: 2,
            r_p: 2,
            input: &[1, 2],
            permutation: &[1685544799, 272405440],
            plus_linear: &[1071399478, 873013929],
        },
        ReferenceVector {
            t: 2,
            r_f: 4,
            r_p: 0,
            input: &[1, 2],
            permutation: &[482980007, 1262246948],
            plus_linear: &[785241854, 1412087590],
        },
        ReferenceVector {
            t: 3,
            r_f: 2,
            r_p: 1,
            input: &[1, 2, 3],
            permutation: &[1240799317, 524228644, 1160214436],
            plus_linear: &[1839887910, 151575598, 1133040925],
        },
        ReferenceVector {
            t: 3,
            r_f: 2,
            r_p: 4,
            input: &[1, 2, 3],
            permutation: &[1159154145, 1418446944, 1843454195],
            plus_linear: &[987024761, 1016835068, 906476019],
        },
        ReferenceVector {
            t: 4,
            r_f: 2,
            r_p: 1,
            input: &[1, 2, 3, 4],
            permutation: &[1729421455, 220410883, 1691497445, 1637178618],
            plus_linear: &[399443726, 1480683317, 2051238669, 452563097],
        },
        ReferenceVector {
            t: 16,
            r_f: 6,
            r_p: 8,
            input: &[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16],
            permutation: &[
                1675596044, 2071591735, 893939762, 1457543839, 1738610167, 1470509871, 1488227572,
                100614730, 383809519, 1741980696, 1911930087, 1507250983, 808756953, 1952710605,
                459497948, 850222012,
            ],
            plus_linear: &[
                1264215087, 1812947419, 1923648690, 1425492691, 187386851, 732355129, 120352285,
                1793464890, 426184177, 1912111279, 1386119311, 1091588568, 510277251, 1842470399,
                210692784, 1616485437,
            ],
        },
    ];

    /// Every reduced configuration the corpus uses agrees with the Python reference, in full.
    ///
    /// Review follow-up. The published `permutation([0]*16)[0] = 1393439926` anchors the port at
    /// one configuration and one coordinate; a reduced instance could in principle differ while
    /// that still matched, because the round *schedule* changes with `R_F` and `R_P` and the
    /// constants come from an LFSR seeded with them.
    ///
    /// So every configuration the corpus uses is checked against externally generated vectors, on
    /// a nonzero input, across the **whole output state**, in both permutation variants. The input
    /// is a ramp rather than zeros because the MDS layer maps zero to zero — which would make the
    /// two variants agree and test one thing less, and the test asserts they differ.
    #[test]
    fn test_every_reduced_configuration_matches_the_reference() {
        assert!(
            REFERENCE_VECTORS.len() >= 7,
            "every configuration the corpus uses needs a vector"
        );

        for v in REFERENCE_VECTORS {
            assert_eq!(v.input.len(), v.t);
            assert_eq!(v.permutation.len(), v.t);
            assert_eq!(v.plus_linear.len(), v.t);
            assert_ne!(
                v.permutation, v.plus_linear,
                "t={} R_F={} R_P={}: the initial linear layer did nothing, so the vector tests \
                 one thing less than it should",
                v.t, v.r_f, v.r_p
            );

            let poseidon = Poseidon::<K>::new(PoseidonParameters {
                prime: KOALABEAR_PRIME,
                alpha: 3,
                t: v.t,
                r_f: v.r_f,
                r_p: v.r_p,
            })
            .expect("valid parameters");
            let input: Vec<K> = v.input.iter().copied().map(K::new).collect();

            let expected: Vec<K> = v.permutation.iter().copied().map(K::new).collect();
            assert_eq!(
                poseidon.permutation(&input).expect("the right width"),
                expected,
                "permutation disagrees at t={} R_F={} R_P={}",
                v.t,
                v.r_f,
                v.r_p
            );

            let expected: Vec<K> = v.plus_linear.iter().copied().map(K::new).collect();
            assert_eq!(
                poseidon
                    .permutation_plus_linear(&input)
                    .expect("the right width"),
                expected,
                "permutation_plus_linear disagrees at t={} R_F={} R_P={}",
                v.t,
                v.r_f,
                v.r_p
            );
        }

        // Every configuration the examples and docs actually use has a vector.
        for (t, r_f, r_p) in [(2, 2, 0), (2, 2, 2), (2, 4, 0), (3, 2, 1), (16, 6, 8)] {
            assert!(
                REFERENCE_VECTORS
                    .iter()
                    .any(|v| v.t == t && v.r_f == r_f && v.r_p == r_p),
                "no reference vector for t={} R_F={} R_P={}",
                t,
                r_f,
                r_p
            );
        }
    }

    /// The permutation reproduces the reference implementation's published output.
    ///
    /// `poseidon-tools`' README records `pos.permutation([0] * 16)[0] == 1393439926` for
    /// `Poseidon(prime=2130706433, alpha=3, t=16, r_f=8, r_p=20)`. That one number exercises the
    /// Grain LFSR's bit layout, its rejection sampling, all 448 round constants, the Cauchy MDS
    /// construction, and the round schedule — any of which being wrong changes it.
    #[test]
    fn test_the_permutation_matches_the_published_vector() {
        let poseidon = reference_instance();
        let output = poseidon
            .permutation(&[K::zero(); 16])
            .expect("the right width");
        assert_eq!(
            output[0],
            K::new(1_393_439_926),
            "the permutation disagrees with poseidon-tools"
        );
    }

    /// The round constants and MDS matrix are the shape the parameters imply.
    #[test]
    fn test_the_constants_and_matrix_have_the_right_shape() {
        let poseidon = reference_instance();
        assert_eq!(poseidon.round_constants.len(), 8 + 20);
        assert!(poseidon.round_constants.iter().all(|row| row.len() == 16));
        assert_eq!(poseidon.mds.len(), 16);
        assert!(poseidon.mds.iter().all(|row| row.len() == 16));

        // Cauchy: M[i][j] * (i - t - j) = 1.
        let t = 16i128;
        let p = KOALABEAR_PRIME as i128;
        for i in 0..16usize {
            for j in 0..16usize {
                let difference = (p + i as i128 - t - j as i128).rem_euclid(p) as u64;
                assert_eq!(poseidon.mds[i][j] * K::new(difference), K::one());
            }
        }
    }

    /// The LFSR's elements are field elements, and the stream is deterministic.
    #[test]
    fn test_the_lfsr_is_deterministic_and_in_range() {
        let draw = || {
            let mut lfsr = GrainLfsr::new(31, 3, 16, 8, 20);
            (0..32)
                .map(|_| lfsr.next_element(KOALABEAR_PRIME))
                .collect::<Vec<u64>>()
        };
        let first = draw();
        assert_eq!(
            first,
            draw(),
            "the same parameters must give the same stream"
        );
        assert!(first.iter().all(|&v| v < KOALABEAR_PRIME));
        // Different parameters, different stream — so the parameters really are in the seed.
        let mut other = GrainLfsr::new(31, 3, 16, 6, 8);
        let other: Vec<u64> = (0..32)
            .map(|_| other.next_element(KOALABEAR_PRIME))
            .collect();
        assert_ne!(first, other);
    }

    /// An odd `R_F` is refused rather than silently mis-split.
    #[test]
    fn test_an_odd_full_round_count_is_refused() {
        assert_eq!(
            Poseidon::<K>::new(PoseidonParameters {
                prime: KOALABEAR_PRIME,
                alpha: 3,
                t: 4,
                r_f: 3,
                r_p: 1,
            })
            .err(),
            Some(PoseidonError::OddFullRounds { r_f: 3 })
        );
    }

    /// A small reduced instance, for the system tests. `t = 3, R_F = 2, R_P = 1, k = 1`.
    fn reduced() -> CicoInstance<K> {
        let poseidon = Poseidon::new(PoseidonParameters {
            prime: KOALABEAR_PRIME,
            alpha: 3,
            t: 3,
            r_f: 2,
            r_p: 1,
        })
        .expect("R_F is even");
        // One constrained word at each end: C_1 = 0xc09de4 as the bounty uses, target 0.
        CicoInstance::new(
            poseidon,
            1,
            vec![K::new(0xC0_9DE4), K::zero()],
            Some(PoseidonParameters::bounty_cico()),
        )
        .expect("k <= t")
    }

    /// The system's shape is what the round schedule implies.
    #[test]
    fn test_the_system_has_one_equation_per_sbox_plus_the_constraints() {
        let instance = reduced();
        // t * R_F + R_P = 3*2 + 1 = 7 S-boxes.
        assert_eq!(instance.poseidon.parameters.sboxes(), 7);
        // (t - k) free inputs + 7 S-box variables.
        assert_eq!(instance.variables(), 2 + 7);
        assert_eq!(instance.equations(), 7 + 1);

        let system = instance.system::<9>().expect("nine variables");
        assert_eq!(system.len(), 8);

        // Every S-box equation has degree alpha, and no more: the degree does not compound.
        for (index, p) in system.iter().take(7).enumerate() {
            assert_eq!(
                p.degree(),
                3,
                "equation {} has the wrong degree: {}",
                index,
                p
            );
        }
        // The output constraint is affine.
        assert_eq!(system[7].degree(), 1);
    }

    /// The system vanishes at a real trace of the permutation. The faithfulness check.
    ///
    /// Not a claim about the generator's internals: a trace is produced by the permutation, which
    /// is itself pinned against the reference's published vector, and the system is evaluated at
    /// the assignment that trace induces. A generator that built the wrong equations fails this.
    #[test]
    fn test_the_system_vanishes_at_a_real_trace() {
        let instance = reduced();
        let t = instance.poseidon.parameters.t;

        // Several deterministic inputs, not one: a single trace could be hit by an equation that
        // is wrong elsewhere.
        for seed in 1..6u64 {
            let free: Vec<K> = (0..t - instance.k)
                .map(|i| K::new(seed * 1_000 + i as u64 + 1))
                .collect();
            let mut state = vec![instance.constants[0]];
            state.extend(free);
            let trace = instance
                .poseidon
                .run(&state, true)
                .expect("the right width");

            // The output constraint only holds when the output really matches, so build the
            // instance whose target *is* this trace's output.
            let matched = CicoInstance::new(
                instance.poseidon.clone(),
                instance.k,
                vec![instance.constants[0], trace.output[0]],
                instance.reduced_from,
            )
            .expect("k <= t");

            let system = matched.system::<9>().expect("nine variables");
            let failures = verify_against_trace(&matched, &system, &trace);
            assert!(
                failures.is_empty(),
                "seed {}: equations {:?} do not vanish at a real trace",
                seed,
                failures
            );
        }
    }

    /// Corrupting a trace value breaks the equations that depend on it, and only those.
    ///
    /// Vanishing at one point is necessary and not sufficient — the zero system vanishes
    /// everywhere — so this is the other half. Each S-box variable appears in its own equation and
    /// in the linear forms of the next round, so corrupting output `i` must break equation `i` and
    /// may break later ones; it must **not** break anything earlier.
    #[test]
    fn test_corrupting_a_trace_value_breaks_the_expected_equations() {
        let instance = reduced();
        let t = instance.poseidon.parameters.t;
        let free: Vec<K> = (0..t - instance.k).map(|i| K::new(i as u64 + 7)).collect();
        let mut state = vec![instance.constants[0]];
        state.extend(free);
        let trace = instance
            .poseidon
            .run(&state, true)
            .expect("the right width");

        let matched = CicoInstance::new(
            instance.poseidon.clone(),
            instance.k,
            vec![instance.constants[0], trace.output[0]],
            instance.reduced_from,
        )
        .expect("k <= t");
        let system = matched.system::<9>().expect("nine variables");
        assert!(verify_against_trace(&matched, &system, &trace).is_empty());

        for corrupted in 0..trace.sbox_outputs.len() {
            let mut broken = trace.clone();
            broken.sbox_outputs[corrupted] += K::one();
            let failures = verify_against_trace(&matched, &system, &broken);

            assert!(
                !failures.is_empty(),
                "corrupting S-box output {} broke nothing, so the system does not depend on it",
                corrupted
            );
            assert!(
                failures.contains(&corrupted),
                "corrupting S-box output {} did not break its own equation {}; broke {:?}",
                corrupted,
                corrupted,
                failures
            );
            assert!(
                failures.iter().all(|&f| f >= corrupted),
                "corrupting S-box output {} broke an earlier equation {:?}, which cannot depend \
                 on it",
                corrupted,
                failures
            );
        }

        // And corrupting a free input breaks the first round, which every later equation is
        // downstream of.
        let mut broken = trace.clone();
        broken.input[instance.k] += K::one();
        let failures = verify_against_trace(&matched, &system, &broken);
        assert!(!failures.is_empty(), "the system ignores its free inputs");
        assert!(failures.contains(&0), "the first S-box did not notice");
    }

    /// The output constraint is the thing that makes it a CICO instance, and it bites.
    #[test]
    fn test_the_output_constraint_fails_on_the_wrong_target() {
        let instance = reduced();
        let t = instance.poseidon.parameters.t;
        let free: Vec<K> = (0..t - instance.k).map(|i| K::new(i as u64 + 3)).collect();
        let mut state = vec![instance.constants[0]];
        state.extend(free);
        let trace = instance
            .poseidon
            .run(&state, true)
            .expect("the right width");

        // The target is 0 and the trace's output almost certainly is not, so the S-box equations
        // vanish and the output constraint does not.
        let system = instance.system::<9>().expect("nine variables");
        let failures = verify_against_trace(&instance, &system, &trace);
        assert_eq!(
            failures,
            vec![7],
            "only the output constraint should fail at an arbitrary trace"
        );
    }

    /// `N` must be exactly the variable count, in both directions.
    ///
    /// An earlier version permitted `N` larger, reasoning that spare positions are simply unused.
    /// They are not harmless: a variable appearing in no equation is unconstrained, so each spare
    /// position adds a free coordinate and the ideal becomes positive-dimensional — and the
    /// zero-dimensional solvers then refuse a system that was meant to be solvable.
    ///
    /// Demonstrated on a one-line system rather than on the Poseidon one, because the point is
    /// about the *ring* and not about Poseidon: `x^2 - 1` is zero-dimensional in one variable and
    /// a pair of lines in two. Computing a basis for a padded nine-variable degree-3 system would
    /// make this test minutes long in a debug build to say the same thing.
    #[test]
    fn test_the_dimension_must_be_exact() {
        use crate::{
            grobner::{classify_ideal, f4},
            MonomialOrder,
        };

        let instance = reduced();
        assert_eq!(
            instance.system::<8>().err(),
            Some(PoseidonError::WrongDimension {
                needed: 9,
                requested: 8
            })
        );
        assert_eq!(
            instance.system::<12>().err(),
            Some(PoseidonError::WrongDimension {
                needed: 9,
                requested: 12
            })
        );
        assert!(instance.system::<9>().is_ok());

        // Why "at least" was the wrong contract. The same equation in one variable and in two.
        let grevlex = MonomialOrder::GradedReverseLexicographic;
        let exact: Vec<MultivariatePolynomial<1, K>> = vec![MultivariatePolynomial::new(&[
            (Monomial::new(&[2]), K::one()),
            (Monomial::one(), -K::one()),
        ])];
        let basis = f4(&exact, grevlex).expect("within limits");
        assert!(classify_ideal(&basis, grevlex).is_finite_dimensional());

        let padded: Vec<MultivariatePolynomial<2, K>> = vec![MultivariatePolynomial::new(&[
            (Monomial::new(&[2, 0]), K::one()),
            (Monomial::one(), -K::one()),
        ])];
        let basis = f4(&padded, grevlex).expect("within limits");
        assert!(
            !classify_ideal(&basis, grevlex).is_finite_dimensional(),
            "one spare position makes the ideal positive-dimensional"
        );
    }

    /// A coefficient type that is not the parameters' field is refused at construction.
    ///
    /// The field identity is a precondition of *having* a `Poseidon`, not a check a caller must
    /// remember: a mismatched type produces a completely different permutation while retaining the
    /// Poseidon parameter metadata, and nothing about the result looks wrong.
    #[test]
    fn test_a_mismatched_field_is_refused_at_construction() {
        let parameters = PoseidonParameters {
            prime: KOALABEAR_PRIME,
            alpha: 3,
            t: 2,
            r_f: 2,
            r_p: 0,
        };
        assert!(Poseidon::<K>::new(parameters).is_ok());

        match Poseidon::<crate::fields::Zp2147483647>::new(parameters) {
            Err(PoseidonError::FieldMismatch { expected, found }) => {
                assert_eq!(expected, KOALABEAR_PRIME);
                assert!(found.contains("2147483647"), "{}", found);
            }
            other => panic!("expected a field mismatch, got {:?}", other),
        }
        assert!(matches!(
            Poseidon::<crate::fields::Zp13>::new(parameters),
            Err(PoseidonError::FieldMismatch { .. })
        ));

        // The odd-round check still fires, independently of the field.
        assert!(matches!(
            Poseidon::<K>::new(PoseidonParameters {
                r_f: 3,
                ..parameters
            }),
            Err(PoseidonError::OddFullRounds { r_f: 3 })
        ));
    }

    /// A CICO instance needs exactly `2k` constants, checked rather than indexed into.
    ///
    /// A short vector returned `Ok` and panicked later inside `system` or `is_solution`, which is
    /// the worst place for a caller to find out.
    #[test]
    fn test_the_constant_count_is_validated() {
        let poseidon = Poseidon::<K>::new(PoseidonParameters {
            prime: KOALABEAR_PRIME,
            alpha: 3,
            t: 3,
            r_f: 2,
            r_p: 1,
        })
        .expect("valid");

        for count in [0usize, 1, 3, 4] {
            assert_eq!(
                CicoInstance::new(poseidon.clone(), 1, vec![K::zero(); count], None).err(),
                Some(PoseidonError::WrongConstantCount {
                    expected: 2,
                    found: count
                }),
                "k = 1 with {} constants should be refused",
                count
            );
        }
        assert!(CicoInstance::new(poseidon.clone(), 1, vec![K::zero(); 2], None).is_ok());
        // k = 2 needs four, not two.
        assert!(CicoInstance::new(poseidon.clone(), 2, vec![K::zero(); 4], None).is_ok());
        assert!(CicoInstance::new(poseidon, 2, vec![K::zero(); 2], None).is_err());
    }

    /// `k > t` is refused before `t - k` is evaluated.
    ///
    /// `planted` computed `t - k` first, which underflows — and in release mode wraps to a vast
    /// number, so the width check then passed for almost any input and the documented error path
    /// was unreachable exactly when it was needed.
    #[test]
    fn test_too_many_constraints_is_refused_before_subtracting() {
        let poseidon = Poseidon::<K>::new(PoseidonParameters {
            prime: KOALABEAR_PRIME,
            alpha: 3,
            t: 2,
            r_f: 2,
            r_p: 0,
        })
        .expect("valid");

        assert_eq!(
            CicoInstance::planted(poseidon.clone(), 5, &[K::zero(); 5], &[], None).err(),
            Some(PoseidonError::TooManyConstraints { k: 5, t: 2 })
        );
        assert_eq!(
            CicoInstance::new(poseidon, 5, vec![K::zero(); 10], None).err(),
            Some(PoseidonError::TooManyConstraints { k: 5, t: 2 })
        );
    }

    /// The bounty's own parameters are stated, and they are far out of reach.
    ///
    /// Recorded as a number rather than a remark: 104 S-box variables before the free inputs, so
    /// nothing in this module is a step toward solving it.
    #[test]
    fn test_the_bounty_parameters_are_out_of_reach() {
        let parameters = PoseidonParameters::bounty_cico();
        assert_eq!(parameters.prime, KOALABEAR_PRIME);
        assert_eq!(parameters.alpha, 3);
        assert_eq!(parameters.t, 16);
        assert_eq!(parameters.sboxes(), 16 * 6 + 8);
        assert_eq!(parameters.sboxes(), 104);

        let poseidon = Poseidon::<K>::new(parameters).expect("R_F is even");
        let instance = CicoInstance::new(
            poseidon,
            2,
            vec![K::new(0xC0_9DE4), K::new(0xEE_6282), K::zero(), K::zero()],
            None,
        )
        .expect("k <= t");
        assert_eq!(instance.variables(), 14 + 104);
        assert_eq!(instance.equations(), 104 + 2);

        // And a reduced instance records what it reduced from, so a result cannot be quoted
        // without it.
        assert_eq!(reduced().reduced_from, Some(parameters));
    }

    /// A planted instance is solved by the value it was planted with, checked through the
    /// permutation.
    #[test]
    fn test_a_planted_instance_is_solved_by_its_plant() {
        let poseidon = Poseidon::<K>::new(PoseidonParameters {
            prime: KOALABEAR_PRIME,
            alpha: 3,
            t: 3,
            r_f: 2,
            r_p: 1,
        })
        .expect("R_F is even");
        let free = [K::new(1_000), K::new(1_001)];
        let instance = CicoInstance::planted(
            poseidon,
            1,
            &[K::new(0xC0_9DE4)],
            &free,
            Some(PoseidonParameters::bounty_cico()),
        )
        .expect("the right widths");

        assert!(
            instance.is_solution(&free).expect("the right width"),
            "the planted value must solve the instance it was planted into"
        );
        // And a different value almost certainly does not.
        assert!(!instance
            .is_solution(&[K::new(1_000), K::new(1_002)])
            .expect("the right width"));

        // The plant appears nowhere in the system's coefficients: the targets are the permutation's
        // output, not its input.
        assert_eq!(instance.constants.len(), 2);
        assert_ne!(instance.constants[1], free[0]);
        assert_ne!(instance.constants[1], free[1]);

        // The system vanishes at the planted trace, which ties the two checks together.
        let mut state = vec![K::new(0xC0_9DE4)];
        state.extend_from_slice(&free);
        let trace = instance
            .poseidon
            .run(&state, true)
            .expect("the right width");
        let system = instance.system::<9>().expect("nine variables");
        assert!(verify_against_trace(&instance, &system, &trace).is_empty());
    }

    /// A mis-sized plant or solution candidate is refused.
    #[test]
    fn test_wrong_widths_are_refused() {
        let poseidon = Poseidon::<K>::new(PoseidonParameters {
            prime: KOALABEAR_PRIME,
            alpha: 3,
            t: 3,
            r_f: 2,
            r_p: 1,
        })
        .expect("R_F is even");
        assert!(matches!(
            CicoInstance::planted(poseidon.clone(), 1, &[K::zero()], &[K::zero()], None),
            Err(PoseidonError::WrongStateWidth { .. })
        ));
        let instance = reduced();
        assert!(matches!(
            instance.is_solution(&[K::zero()]),
            Err(PoseidonError::WrongStateWidth {
                expected: 2,
                found: 1
            })
        ));
        assert!(matches!(
            instance.poseidon.permutation(&[K::zero(); 2]),
            Err(PoseidonError::WrongStateWidth {
                expected: 3,
                found: 2
            })
        ));
    }

    /// A trace's assignment lands the free inputs and S-box outputs where the system expects them.
    #[test]
    fn test_the_assignment_matches_the_variable_order() {
        let instance = reduced();
        let state = vec![instance.constants[0], K::new(11), K::new(13)];
        let trace = instance
            .poseidon
            .run(&state, true)
            .expect("the right width");

        let point: [K; 9] = instance.assignment(&trace);
        // Free inputs first, in input order after the constrained prefix.
        assert_eq!(point[0], K::new(11));
        assert_eq!(point[1], K::new(13));
        // Then the S-box outputs, in trace order.
        for (i, value) in trace.sbox_outputs.iter().enumerate() {
            assert_eq!(point[2 + i], *value, "S-box output {} is misplaced", i);
        }
    }

    /// The generated system is in the variables it says and no others.
    ///
    /// At the exact dimension, which is now the only one `system` accepts — so "no others" means
    /// every declared variable is used and the count is right, rather than the weaker claim that
    /// spare positions stay empty.
    #[test]
    fn test_the_system_uses_exactly_its_declared_variables() {
        let instance = reduced();
        assert_eq!(instance.variables(), 9);
        let system: Vec<MultivariatePolynomial<9, K>> =
            instance.system::<9>().expect("nine variables");

        let mut used = [false; 9];
        for p in &system {
            for monomial in p.terms().keys() {
                for (i, &exponent) in monomial.exponents().iter().enumerate() {
                    if exponent > 0 {
                        used[i] = true;
                    }
                }
            }
        }
        assert!(
            used.iter().all(|&u| u),
            "every declared variable must appear: {:?}",
            used
        );
    }
}
