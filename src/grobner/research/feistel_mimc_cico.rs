//! The two algebraic models of Feistel-MiMC CICO, which differ in **kind**.
//!
//! #203's third research question, and the one place in this crate where two formulations of one
//! problem are not two shapes of the same kind of object: [`FeistelMimcModel::PerRound`] is a
//! square multivariate system of `r` cubics, and [`FeistelMimcModel::Univariate`] is a *single*
//! polynomial in one variable of degree `α^r`. The first is F4's problem; the second is univariate
//! root-finding, which is `poly::univariate::roots`' problem and not a Gröbner computation at all.
//!
//! # Why Feistel-MiMC has a univariate route and Poseidon does not
//!
//! Each round touches one branch with one `x^α` and adds it into the other. There is **no MDS
//! layer**, so nothing mixes the branches and nothing forces a fresh variable per round to keep the
//! degree down: `A_{j+1} = A_{j−1} + (A_j + c_j)^α` is a one-term recurrence in a single unknown,
//! and composing it `r` times is a polynomial in the input alone. `docs/research/poseidon.md` §6
//! identifies the dense MDS layer as "the structural obstacle, not the variable count"; this is
//! what the problem looks like with that obstacle removed.
//!
//! The trade is explicit and it is why both models are carried. Eliminating the `r − 1`
//! intermediate variables costs degree exponentially: `α^r` is 729 at `r = 6` and about `3.1 × 10^10`
//! at the easiest *specified* instance, `r = 22`. The univariate route is therefore a real
//! alternative at small `r` and hopeless at the specified round counts, which is a statement about
//! the formulation rather than about either solver.
//!
//! # The CICO conditions are on the trailing word
//!
//! `Perm(X, 0) = (Y, 0)`, as the reference's own verifier writes it — see
//! [`FeistelMimc::is_cico_solution`]. One free input word and one output constraint, so
//! `N − E = t − 2k = 0` in `docs/research/structure-experiments.md` §1's bookkeeping: both models
//! are zero-dimensional without a slice, which is **not** true of the `t = 3` Rescue-Prime
//! instances.

use rand::{rngs::StdRng, SeedableRng};

use crate::{
    grobner::research::feistel_mimc::{FeistelMimc, FeistelMimcError},
    poly::{roots, Polynomial, UnivariatePolynomial},
    FiniteField, KnownOrder, Monomial, MultivariatePolynomial,
};

/// Which algebraic model of Feistel-MiMC CICO.
///
/// Part of a registered problem's identity, for the reason
/// [`AnemoiModel`](super::AnemoiModel) is: they are not the same problem to solve, so two rows
/// keyed on the same digest would compare a Gröbner basis computation against a root-finding one.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum FeistelMimcModel {
    /// One variable per round, every generator of degree `α`. `r` variables, `r` equations.
    PerRound,

    /// The intermediate variables eliminated: one polynomial of degree `α^r` in the input alone.
    Univariate,
}

impl FeistelMimcModel {
    /// The stable tag the identity digest covers.
    pub fn tag(&self) -> &'static str {
        match self {
            Self::PerRound => "per-round",
            Self::Univariate => "univariate",
        }
    }

    /// The number of variables at `r` rounds.
    pub fn variables(&self, rounds: usize) -> usize {
        match self {
            Self::PerRound => rounds,
            Self::Univariate => 1,
        }
    }

    /// The number of generators at `r` rounds.
    pub fn equations(&self, rounds: usize) -> usize {
        match self {
            Self::PerRound => rounds,
            Self::Univariate => 1,
        }
    }

    /// The generator degrees, in the order the system is emitted.
    ///
    /// Stated rather than measured, so a row's shape can be read without building it, and asserted
    /// against the built system by a test.
    pub fn generator_degrees(&self, rounds: usize, alpha: u32) -> Vec<u64> {
        let alpha = u64::from(alpha);
        match self {
            Self::PerRound => vec![alpha; rounds],
            Self::Univariate => vec![alpha.pow(rounds as u32)],
        }
    }
}

/// The input the planted ladder plants its target from.
///
/// Part of a planted instance's identity, because the target **is** a function of the plant: two
/// plants are two different problems. Named once here so the registry's planted rows and
/// `examples/feistel_mimc_cico.rs` cannot disagree — a row whose plant differed from the example's
/// would be a row nothing was ever measured against.
pub const LADDER_PLANT: u64 = 0x5eed_1234_5678_9abc;

/// A Feistel-MiMC CICO instance: a permutation, a model, and a target.
///
/// The bounty objective is `Perm(X, 0) = (Y, 0)` with `Y` unconstrained — CICO(1) on the
/// **trailing** word, which is
/// [`Objective::CicoExactTrailing`](super::Objective::CicoExactTrailing).
#[derive(Clone, Debug)]
pub struct FeistelMimcCico<F: KnownOrder> {
    /// The permutation.
    pub mimc: FeistelMimc<F>,

    /// Which model.
    pub model: FeistelMimcModel,

    /// The value the trailing output word must take: zero for the stated bounty objective.
    pub target: F,

    /// The input the target was planted from, if it was planted.
    ///
    /// Recorded because a planted instance's target **is** a function of the plant: two runs
    /// choosing different plants are measuring two different problems, which is the argument
    /// [`CicoTarget::PlantedFrom`](super::CicoTarget::PlantedFrom) makes.
    pub planted_from: Option<F>,
}

impl<F: KnownOrder> FeistelMimcCico<F> {
    /// The **stated** bounty instance: the trailing output word must be zero.
    ///
    /// Whether a solution exists over the base field is then a property of the instance. It need
    /// not — the degree-`α^r` univariate does not have to split — and an empty solution set is a
    /// fact about that round count rather than a failure of anything.
    pub fn new(mimc: FeistelMimc<F>, model: FeistelMimcModel) -> Self {
        Self {
            mimc,
            model,
            target: F::zero(),
            planted_from: None,
        }
    }

    /// A **planted** surrogate: the target is whatever `(x, 0)` actually produces.
    ///
    /// Not the bounty objective, and must never be reported as it. What it buys is that a solution
    /// provably exists, so "the solver found nothing" is unambiguously about the solver — which is
    /// what makes a round-count ladder a measurement rather than a mixture of two different
    /// failures.
    pub fn planted(mimc: FeistelMimc<F>, model: FeistelMimcModel, x: F) -> Self {
        let target = mimc.permutation(x, F::zero())[1];
        Self {
            mimc,
            model,
            target,
            planted_from: Some(x),
        }
    }

    /// The number of variables.
    pub fn variables(&self) -> usize {
        self.model.variables(self.mimc.parameters.rounds)
    }

    /// The number of generators.
    pub fn equations(&self) -> usize {
        self.model.equations(self.mimc.parameters.rounds)
    }

    /// The multivariate system, at a compile-time dimension.
    ///
    /// Available for both models: [`FeistelMimcModel::Univariate`] is emitted as a one-variable
    /// multivariate so that the two can be compared by the same machinery, while
    /// [`Self::univariate`] gives the form a root-finder wants.
    ///
    /// # `N` must be exactly [`Self::variables`]
    ///
    /// A spare position is an unconstrained variable, which makes the ideal positive-dimensional
    /// and the zero-dimensional solvers refuse it.
    ///
    /// # Errors
    /// [`FeistelMimcError::WrongDimension`] if `N` is not [`Self::variables`].
    pub fn system<const N: usize>(
        &self,
    ) -> Result<Vec<MultivariatePolynomial<N, F>>, FeistelMimcError> {
        let needed = self.variables();
        if N != needed {
            return Err(FeistelMimcError::WrongDimension {
                needed,
                requested: N,
            });
        }
        Ok(match self.model {
            FeistelMimcModel::PerRound => self.per_round_system(),
            FeistelMimcModel::Univariate => {
                vec![lift(&self.univariate())]
            }
        })
    }

    /// Model `PerRound`, in round order: `x_j` is the first state word entering round `j`.
    ///
    /// `x_0` is the free input word `X`; the second input word is the CICO condition `0` and is
    /// substituted rather than carried. The Feistel swap makes the second word of the state
    /// entering round `j` equal to `x_{j−1}`, so one variable per round suffices and every
    /// generator is `x_{j+1} − x_{j−1} − (x_j + c_j)^α` — degree `α`, with no compounding.
    ///
    /// Zeebra's degrevlex is induced by the variable indices, so this assignment *is* the ordering:
    /// `x_0 > x_1 > … > x_{r−1}`, the input word largest.
    fn per_round_system<const N: usize>(&self) -> Vec<MultivariatePolynomial<N, F>> {
        let rounds = self.mimc.parameters.rounds;
        let alpha = self.mimc.parameters.alpha;
        // The second word entering round `j`, which the swap sets to `x_{j-1}`, and to the CICO
        // condition `0` at round zero.
        let second = |round: usize| -> MultivariatePolynomial<N, F> {
            if round == 0 {
                MultivariatePolynomial::zero()
            } else {
                variable(round - 1)
            }
        };

        let mut equations = Vec::with_capacity(rounds);
        for round in 0..rounds - 1 {
            let sbox = power(
                &(variable(round) + constant(self.mimc.round_constants[round])),
                alpha,
            );
            equations.push(variable::<N, F>(round + 1) - second(round) - sbox);
        }
        // The last round omits the swap, so the CICO condition lands on `x_{r-2} + S_{r-1}(x_{r-1})`,
        // which must equal the target.
        let last = rounds - 1;
        let sbox = power(
            &(variable(last) + constant(self.mimc.round_constants[last])),
            alpha,
        );
        equations.push(second(last) + sbox - constant(self.target));
        equations
    }

    /// Model `Univariate`: the degree-`α^r` polynomial whose roots are the CICO solutions.
    ///
    /// Built by composing the round recurrence symbolically — the intermediate variables of
    /// [`Self::per_round_system`] eliminated by substitution rather than by a Gröbner computation,
    /// which is exact and is the whole point of the comparison.
    ///
    /// # Cost
    ///
    /// The result has `α^r + 1` coefficients, so this is only reasonable for small `r`. At the
    /// easiest specified instance, `r = 22`, it would be about `3.1 × 10^10` of them.
    pub fn univariate(&self) -> UnivariatePolynomial<F> {
        let rounds = self.mimc.parameters.rounds;
        let alpha = self.mimc.parameters.alpha;
        // `previous` is `A_{j-1}` and `current` is `A_j`, as polynomials in the input `X`.
        let mut previous = UnivariatePolynomial::zero();
        let mut current = UnivariatePolynomial::new(&[F::zero(), F::one()]);
        for round in 0..rounds - 1 {
            let sbox = (&current + &UnivariatePolynomial::lift(&self.mimc.round_constants[round]))
                .pow(alpha);
            let next = &previous + &sbox;
            previous = current;
            current = next;
        }
        let last = rounds - 1;
        let sbox =
            (&current + &UnivariatePolynomial::lift(&self.mimc.round_constants[last])).pow(alpha);
        &(&previous + &sbox) - &UnivariatePolynomial::lift(&self.target)
    }

    /// Every CICO solution, by root-finding on [`Self::univariate`].
    ///
    /// Exhaustive over the base field: `roots` keeps exactly the distinct roots lying in `F`, so
    /// this is the **complete** solution set and not a witness. Only usable at small `r`.
    pub fn solutions(&self) -> Vec<F> {
        let mut rng = StdRng::seed_from_u64(0);
        let polynomial = self.univariate();
        if polynomial.is_zero() {
            return Vec::new();
        }
        roots(&polynomial, &mut rng)
    }

    /// The assignment a trace of the permutation gives this model's variables.
    ///
    /// The faithfulness check's other half: a system that merely looked right would not vanish
    /// here. Returns `None` if `N` is not [`Self::variables`].
    pub fn assignment<const N: usize>(&self, x: F) -> Option<[F; N]> {
        if N != self.variables() {
            return None;
        }
        let mut point = [F::zero(); N];
        match self.model {
            FeistelMimcModel::PerRound => {
                let trace = self.mimc.trace(x, F::zero());
                for (round, slot) in point.iter_mut().enumerate() {
                    *slot = trace[round][0];
                }
            }
            FeistelMimcModel::Univariate => point[0] = x,
        }
        Some(point)
    }

    /// Whether `(x, 0)` solves this instance, checked through the permutation.
    ///
    /// Through the permutation and against [`Self::target`], so it is a verifier for a claimed
    /// witness and not a restatement of the polynomial system. At the stated target this is
    /// [`FeistelMimc::is_cico_solution`], which is the reference's own check.
    pub fn is_solution(&self, x: F) -> bool {
        self.mimc.permutation(x, F::zero())[1] == self.target
    }
}

/// Whether every generator of `system` vanishes at the trace of `(x, 0)`.
///
/// Returns the indices that did **not** vanish, so a failure says which round is wrong rather than
/// only that something is.
///
/// # An arbitrary `x` is expected to fail on the last generator
///
/// The per-round system's first `r − 1` generators are trace relations and hold at any input; its
/// last one is the CICO objective and holds only at a *solution*. So an empty return means `x`
/// solves the instance, and `[r − 1]` means the model is faithful and `x` is not a solution. Only a
/// non-empty return that includes an earlier index is evidence of an unfaithful model.
pub fn verify_against_feistel_mimc_trace<const N: usize, F: KnownOrder>(
    instance: &FeistelMimcCico<F>,
    system: &[MultivariatePolynomial<N, F>],
    x: F,
) -> Vec<usize> {
    let Some(point) = instance.assignment::<N>(x) else {
        return (0..system.len()).collect();
    };
    system
        .iter()
        .enumerate()
        .filter(|(_, p)| !p.eval(&point).is_zero())
        .map(|(i, _)| i)
        .collect()
}

/// Something to do with a Feistel-MiMC CICO system once its dimension is known.
///
/// The `const N` bridge, as [`AnemoiCicoVisitor`](super::AnemoiCicoVisitor) is: a function cannot
/// return `Vec<MultivariatePolynomial<N, F>>` for an `N` chosen at runtime.
pub trait FeistelMimcCicoVisitor<F: KnownOrder> {
    /// What the visit produces. Must not mention the dimension.
    type Output;

    /// Called once, with the system at its own dimension.
    fn visit<const N: usize>(self, system: &[MultivariatePolynomial<N, F>]) -> Self::Output;
}

/// Build `instance`'s system and hand it to `visitor` at its own dimension.
///
/// # Errors
/// [`FeistelMimcError::WrongDimension`] if the instance's variable count has no compiled
/// dimension. The `PerRound` model needs one per round count on the ladder; `Univariate` always
/// needs 1.
pub fn dispatch_feistel_mimc_cico<F: KnownOrder, V: FeistelMimcCicoVisitor<F>>(
    instance: &FeistelMimcCico<F>,
    visitor: V,
) -> Result<V::Output, FeistelMimcError> {
    let variables = instance.variables();

    // The reduced-round ladder, one dimension per rung. A spare `N` monomorphizes the whole
    // pipeline again, so these are the counts the ladder actually walks and no others.
    macro_rules! dispatch {
        ($($n:literal),+ $(,)?) => {
            match variables {
                $($n => Ok(visitor.visit(&instance.system::<$n>()?)),)+
                variables => Err(FeistelMimcError::WrongDimension {
                    needed: variables,
                    requested: 0,
                }),
            }
        };
    }
    dispatch!(1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14)
}

/// A univariate as a one-variable multivariate.
fn lift<const N: usize, F: FiniteField>(
    p: &UnivariatePolynomial<F>,
) -> MultivariatePolynomial<N, F> {
    let terms: Vec<(Monomial<N>, F)> = p
        .coefficients()
        .iter()
        .enumerate()
        .filter(|(_, c)| !c.is_zero())
        .map(|(degree, c)| (Monomial::univariate(0, degree as u32), *c))
        .collect();
    MultivariatePolynomial::new(&terms)
}

/// The constant polynomial `c`.
fn constant<const N: usize, F: FiniteField>(c: F) -> MultivariatePolynomial<N, F> {
    MultivariatePolynomial::new(&[(Monomial::one(), c)])
}

/// The polynomial `x_index`.
fn variable<const N: usize, F: FiniteField>(index: usize) -> MultivariatePolynomial<N, F> {
    MultivariatePolynomial::new(&[(Monomial::univariate(index, 1), F::one())])
}

/// `p^alpha`, by repeated multiplication; `alpha` is 3 in every bounty instance.
fn power<const N: usize, F: FiniteField>(
    p: &MultivariatePolynomial<N, F>,
    alpha: u32,
) -> MultivariatePolynomial<N, F> {
    let mut accumulator = MultivariatePolynomial::one();
    for _ in 0..alpha {
        accumulator *= p.clone();
    }
    accumulator
}

#[cfg(test)]
mod tests {
    use super::{verify_against_feistel_mimc_trace, FeistelMimcCico, FeistelMimcModel};
    use crate::{
        fields::Zp18446744073709551557,
        grobner::research::feistel_mimc::{FeistelMimc, FeistelMimcError, FeistelMimcParameters},
        identities::Zero,
        poly::Polynomial,
        FiniteField, MonomialOrder,
    };

    type F = Zp18446744073709551557;

    fn instance(rounds: usize, model: FeistelMimcModel) -> FeistelMimcCico<F> {
        FeistelMimcCico::new(
            FeistelMimc::new(FeistelMimcParameters::bounty(rounds)).expect("builds"),
            model,
        )
    }

    /// Both models reproduce the permutation's own arithmetic at an arbitrary input, generator by
    /// generator, at every round count up to six.
    ///
    /// The strong form of #203's assertion (b), and it has to distinguish two kinds of generator.
    /// The per-round system's first `r − 1` are **trace relations**: they hold at *any* input, so
    /// they must vanish at every trace. Its last is the **objective**, which holds only at a
    /// solution — and the sharper statement available for it is that it evaluates to exactly the
    /// permutation's trailing output word, which is also what the univariate model evaluates to.
    /// Checking that pins both models to the primitive at every input rather than at the handful of
    /// points where the system happens to vanish.
    ///
    /// Faithfulness checked against the primitive — whose permutation reproduces the reference's
    /// published test vectors — rather than against the other model: a shared mistake in the round
    /// schedule would be invisible to a test comparing the two systems with each other.
    #[test]
    fn test_both_models_reproduce_the_permutation_at_any_input() {
        macro_rules! check {
            ($rounds:literal) => {{
                let per_round = instance($rounds, FeistelMimcModel::PerRound);
                let system = per_round.system::<$rounds>().expect("right dimension");
                assert_eq!(system.len(), $rounds);
                let univariate = instance($rounds, FeistelMimcModel::Univariate);
                for seed in 1u64..5 {
                    let x = F::new(seed * 1_000_003 + 7);
                    let point = per_round.assignment::<$rounds>(x).expect("right dimension");
                    let trailing = per_round.mimc.permutation(x, F::zero())[1];
                    // The round relations hold at any input.
                    for (index, generator) in system[..$rounds - 1].iter().enumerate() {
                        assert!(
                            generator.eval(&point).is_zero(),
                            "per-round, r = {}, seed {}: round relation {} does not hold",
                            $rounds,
                            seed,
                            index
                        );
                    }
                    // The last generator *is* the objective: it equals the trailing output word.
                    assert_eq!(
                        system[$rounds - 1].eval(&point),
                        trailing,
                        "per-round, r = {}, seed {}: the objective is not the trailing word",
                        $rounds,
                        seed
                    );
                    // And the univariate is the same function of the input, by construction.
                    assert_eq!(
                        univariate.univariate().eval(&x),
                        trailing,
                        "univariate, r = {}, seed {}",
                        $rounds,
                        seed
                    );
                }
            }};
        }
        check!(1);
        check!(2);
        check!(3);
        check!(4);
        check!(5);
        check!(6);
    }

    /// Every generator of both models vanishes at the trace of a genuine CICO solution.
    ///
    /// #203's assertion (b) in the form the generator contract states, which the objective
    /// generator only satisfies at a solution. The solutions come from the univariate route, so
    /// they are found independently of the system being checked.
    ///
    /// A round count with **no** solution over the base field is a fact about that instance and not
    /// a failure — the degree-`α^r` univariate need not split — so the test skips those and asserts
    /// instead that enough rungs did have one for the check to mean something.
    #[test]
    fn test_both_models_vanish_at_the_trace_of_a_solution() {
        let mut checked = 0;
        macro_rules! check {
            ($rounds:literal) => {{
                let per_round = instance($rounds, FeistelMimcModel::PerRound);
                let system = per_round.system::<$rounds>().expect("right dimension");
                let univariate = instance($rounds, FeistelMimcModel::Univariate);
                let single = univariate.system::<1>().expect("right dimension");
                for x in univariate.solutions() {
                    assert_eq!(
                        verify_against_feistel_mimc_trace(&per_round, &system, x),
                        Vec::<usize>::new(),
                        "per-round, r = {}, solution {}",
                        $rounds,
                        x
                    );
                    assert_eq!(
                        verify_against_feistel_mimc_trace(&univariate, &single, x),
                        Vec::<usize>::new(),
                        "univariate, r = {}, solution {}",
                        $rounds,
                        x
                    );
                    checked += 1;
                }
            }};
        }
        check!(1);
        check!(2);
        check!(3);
        check!(4);
        check!(5);
        check!(6);
        check!(7);
        assert!(
            checked >= 2,
            "only {checked} solutions were found over r = 1..7; the check is vacuous"
        );
    }

    /// The two formulations have the **same solution set**, which is what makes them two models of
    /// one problem rather than two problems.
    ///
    /// The univariate's roots are exhaustive over the base field, so the comparison is a set
    /// equality and not a witness match: every root is checked through the permutation, and the
    /// per-round system is checked to vanish at each root's trace. #203's assertion (d).
    #[test]
    fn test_the_two_formulations_have_the_same_solution_set() {
        macro_rules! check {
            ($rounds:literal) => {{
                let univariate = instance($rounds, FeistelMimcModel::Univariate);
                let mut solutions = univariate.solutions();
                solutions.sort_by_key(|x| x.value());
                // Every root is a genuine CICO solution of the permutation: assertion (c).
                for x in &solutions {
                    assert!(
                        univariate.is_solution(*x),
                        "r = {}: a root of the univariate is not a CICO solution",
                        $rounds
                    );
                }
                // And the per-round system vanishes at each one's trace, so the two models agree
                // on the whole set rather than on one point.
                let per_round = instance($rounds, FeistelMimcModel::PerRound);
                let system = per_round.system::<$rounds>().expect("right dimension");
                for x in &solutions {
                    assert_eq!(
                        verify_against_feistel_mimc_trace(&per_round, &system, *x),
                        Vec::<usize>::new(),
                        "r = {}: the per-round system misses a solution the univariate found",
                        $rounds
                    );
                }
                solutions
            }};
        }
        // At r = 1 the solution is in closed form: (X + c_0)^3 = 0 has the single root -c_0.
        let one = check!(1);
        let mimc = instance(1, FeistelMimcModel::Univariate);
        assert_eq!(one, vec![-mimc.mimc.round_constants[0]]);
        for rounds in [2, 3, 4, 5] {
            let _ = match rounds {
                2 => check!(2),
                3 => check!(3),
                4 => check!(4),
                _ => check!(5),
            };
        }
    }

    /// The models' stated shapes match the systems they build: `r` cubics against one degree-`α^r`
    /// generator.
    #[test]
    fn test_the_stated_shapes_match_the_built_systems() {
        let per_round = instance(5, FeistelMimcModel::PerRound);
        assert_eq!(per_round.variables(), 5);
        assert_eq!(per_round.equations(), 5);
        let system = per_round.system::<5>().expect("right dimension");
        let degrees: Vec<u64> = system
            .iter()
            .map(|p| {
                p.leading_monomial(MonomialOrder::GradedReverseLexicographic)
                    .degree()
            })
            .collect();
        assert_eq!(degrees, FeistelMimcModel::PerRound.generator_degrees(5, 3));
        assert_eq!(degrees, vec![3; 5]);

        let univariate = instance(5, FeistelMimcModel::Univariate);
        assert_eq!(univariate.variables(), 1);
        assert_eq!(univariate.equations(), 1);
        assert_eq!(u64::from(univariate.univariate().degree()), 3u64.pow(5));
        assert_eq!(
            FeistelMimcModel::Univariate.generator_degrees(5, 3),
            vec![243]
        );
    }

    /// The per-round system is square, which is the `N − E = t − 2k = 0` of a width-two CICO(1).
    ///
    /// Recorded as a property rather than a coincidence: it is why neither Feistel-MiMC model needs
    /// a slice, unlike the `t = 3` Rescue-Prime instances.
    #[test]
    fn test_the_system_is_square_at_every_round_count() {
        for rounds in 1..15 {
            let per_round = instance(rounds, FeistelMimcModel::PerRound);
            assert_eq!(per_round.variables(), per_round.equations(), "r = {rounds}");
        }
    }

    /// A dimension that is not the model's variable count is refused rather than padded.
    #[test]
    fn test_the_dimension_is_enforced() {
        let per_round = instance(4, FeistelMimcModel::PerRound);
        assert_eq!(
            per_round.system::<5>().err(),
            Some(FeistelMimcError::WrongDimension {
                needed: 4,
                requested: 5
            })
        );
        assert!(per_round.assignment::<5>(F::new(7)).is_none());
    }

    /// A planted instance is solved by its own plant, in both models, and records what it was
    /// planted from.
    ///
    /// The plant is what makes the round-count ladder a measurement: a solution provably exists, so
    /// a solver that finds nothing has failed rather than met an empty variety. The planted target
    /// is **not** the bounty objective and the instance says so by carrying `planted_from`.
    #[test]
    fn test_a_planted_instance_is_solved_by_its_plant() {
        macro_rules! check {
            ($rounds:literal) => {{
                let x = F::new(987_654_321);
                let mimc =
                    FeistelMimc::new(FeistelMimcParameters::bounty($rounds)).expect("builds");
                let per_round =
                    FeistelMimcCico::planted(mimc.clone(), FeistelMimcModel::PerRound, x);
                assert_eq!(per_round.planted_from, Some(x));
                assert!(per_round.is_solution(x));
                let system = per_round.system::<$rounds>().expect("right dimension");
                assert_eq!(
                    verify_against_feistel_mimc_trace(&per_round, &system, x),
                    Vec::<usize>::new(),
                    "per-round, r = {}",
                    $rounds
                );
                // The plant is a root of the planted univariate, and the two targets agree.
                let univariate = FeistelMimcCico::planted(mimc, FeistelMimcModel::Univariate, x);
                assert_eq!(univariate.target, per_round.target);
                assert!(
                    univariate.univariate().eval(&x).is_zero(),
                    "r = {}",
                    $rounds
                );
                assert!(
                    univariate.solutions().contains(&x),
                    "r = {}: root-finding missed the plant",
                    $rounds
                );
            }};
        }
        check!(2);
        check!(3);
        check!(4);
        check!(5);
    }

    /// The stated instance's target is zero, which is the reference verifier's own condition.
    #[test]
    fn test_the_stated_target_is_the_reference_condition() {
        let cico = instance(4, FeistelMimcModel::PerRound);
        assert!(cico.target.is_zero());
        assert_eq!(cico.planted_from, None);
        for seed in 1u64..6 {
            let x = F::new(seed * 31 + 2);
            assert_eq!(cico.is_solution(x), cico.mimc.is_cico_solution(x));
        }
    }

    /// The model tags are stable, since they sit inside a registered problem's identity.
    #[test]
    fn test_the_model_tags_are_stable() {
        assert_eq!(FeistelMimcModel::PerRound.tag(), "per-round");
        assert_eq!(FeistelMimcModel::Univariate.tag(), "univariate");
    }
}
