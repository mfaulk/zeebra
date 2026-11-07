//! The two published algebraic models of Anemoi CICO: `FCICO` and `PCICO`.
//!
//! From Koschatko, Lüftenegger and Rechberger, *Exploring the Six Worlds of Gröbner Basis
//! Cryptanalysis: Application to Anemoi*, ToSC 2024 №4, pp. 138–190, DOI
//! `10.46586/tosc.v2024.i4.138-190` — read from `tosc.iacr.org`, which is open access. The
//! construction and the variable orderings were taken from that work's own `models.sage`
//! (<https://github.com/IAIK/six-worlds-anemoi>, MIT, commit `fa056e6f`).
//!
//! # Why two models of one primitive
//!
//! They have the same solutions and they are not the same problem to solve. At `N = 5`, `ℓ = 1`:
//! `FCICO` is ten generators of degree three in ten variables; `PCICO` is six generators of degrees
//! `3, 4, 6, 8, 10` and `N + 1` in six variables. A solver meets those completely differently —
//! which is why [`ChallengeParameters::AnemoiCico`](super::ChallengeParameters::AnemoiCico) carries
//! the model **inside** the identity digest, and why two rows at the same `N` are two problems
//! rather than one problem measured twice.
//!
//! # The variable order is the published one
//!
//! Both models are emitted in the Six Worlds `o1` ordering, which that paper reports as the good
//! one and which every committed log in `results/.../..._o1.txt` was produced under. Zeebra's
//! degrevlex order is induced by the variable *indices*, so the index assignment here is the
//! ordering, and matching it is what makes the published per-row figures comparable at all.
//!
//! # The final linear layer
//!
//! Anemoi ends with a degenerate round that is a linear layer alone, so the CICO condition applies
//! to the state *after* it. `FCICO` keeps its last state variables in the permutation's output
//! coordinates and inverts that layer inside the last round's equations — which is what the logs'
//! `Use final LL: True.` header records. `PCICO` applies it forward before taking the output
//! constraint. Both conventions are the reference's; neither is a choice made here.

use crate::{
    grobner::research::anemoi::{Anemoi, AnemoiError},
    FiniteField, KnownOrder, Monomial, MultivariatePolynomial,
};

/// Which algebraic model of Anemoi CICO.
///
/// Part of a registered problem's identity, so the tag is stable and the variants are not
/// interchangeable.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum AnemoiModel {
    /// Model `F`: one state variable per word per round, every generator of degree `α`.
    ///
    /// `2ℓ(N + 1)` variables before the CICO conditions remove `2ℓ` of them, so `2ℓN` after.
    Fcico,

    /// Model `P`: one variable per Flystel plus the free input, with degrees growing to `2N`.
    ///
    /// `ℓ(N + 2)` variables before the CICO condition removes `ℓ`, so `ℓ(N + 1)` after.
    Pcico,
}

impl AnemoiModel {
    /// The stable tag the identity digest covers.
    pub fn tag(&self) -> &'static str {
        match self {
            Self::Fcico => "fcico",
            Self::Pcico => "pcico",
        }
    }

    /// The number of variables at `N` rounds and `ℓ` columns, after the CICO conditions.
    pub fn variables(&self, rounds: usize, l: usize) -> usize {
        match self {
            Self::Fcico => 2 * l * rounds,
            Self::Pcico => l * (rounds + 1),
        }
    }

    /// The number of generators at `N` rounds and `ℓ` columns.
    ///
    /// Square in both models, and for different reasons: `FCICO` has two equations per Flystel and
    /// folds the CICO conditions into them by substitution, while `PCICO` has one per Flystel and
    /// `ℓ` separate output constraints.
    pub fn equations(&self, rounds: usize, l: usize) -> usize {
        match self {
            Self::Fcico => 2 * l * rounds,
            Self::Pcico => l * rounds + l,
        }
    }

    /// The generator degrees, in the order [`AnemoiCico::system`] emits them.
    ///
    /// Stated rather than measured so that a registered row's shape can be read without building
    /// it, and asserted against the built system by a test.
    pub fn generator_degrees(&self, rounds: usize, alpha: u32) -> Vec<u64> {
        let alpha = u64::from(alpha);
        match self {
            // Every generator is `β·y² + (y − v)^α − x` or `β·v² + δ + (y − v)^α − u` in affine
            // arguments, so degree `α` throughout and no compounding. That is the whole point of
            // the model.
            Self::Fcico => vec![alpha; 2 * rounds],
            Self::Pcico => {
                // Round one is `s^α − x + βy²` in the input variables, degree `α`. From round two
                // the round input is itself of degree `r − 1`, and the `βy²` term doubles it.
                let mut degrees = vec![alpha];
                for round in 2..=rounds {
                    degrees.push(2 * round as u64);
                }
                // The output constraint, after the final linear layer.
                degrees.push(rounds as u64 + 1);
                degrees
            }
        }
    }
}

/// An Anemoi CICO instance: a permutation, a model, and the CICO conditions.
///
/// The conditions are `x_in = 0` and `x_out = 0` — the **leading** word of a `2ℓ`-word state at
/// each end, which is [`Objective::CicoExact`](super::Objective::CicoExact) as that tag is
/// written. There is no stated target beyond the zeros: Anemoi CICO is the zero-to-zero problem,
/// not a problem against published constants.
#[derive(Clone, Debug)]
pub struct AnemoiCico<F: KnownOrder> {
    /// The permutation.
    pub anemoi: Anemoi<F>,

    /// Which model.
    pub model: AnemoiModel,
}

impl<F: KnownOrder> AnemoiCico<F> {
    /// A CICO instance over this permutation.
    pub fn new(anemoi: Anemoi<F>, model: AnemoiModel) -> Self {
        Self { anemoi, model }
    }

    /// The number of variables.
    pub fn variables(&self) -> usize {
        self.model
            .variables(self.anemoi.parameters.rounds, self.anemoi.parameters.l)
    }

    /// The number of generators.
    pub fn equations(&self) -> usize {
        self.model
            .equations(self.anemoi.parameters.rounds, self.anemoi.parameters.l)
    }

    /// The polynomial system, at a compile-time dimension.
    ///
    /// # `N` must be exactly [`Self::variables`]
    ///
    /// A spare position is an **unconstrained variable**, which makes the ideal
    /// positive-dimensional and the zero-dimensional solvers refuse it — the same contract
    /// [`CicoInstance::system`](super::CicoInstance::system) states and for the same reason.
    ///
    /// # Errors
    /// [`AnemoiError::WrongDimension`] if `N` is not [`Self::variables`].
    pub fn system<const N: usize>(&self) -> Result<Vec<MultivariatePolynomial<N, F>>, AnemoiError> {
        let needed = self.variables();
        if N != needed {
            return Err(AnemoiError::WrongDimension {
                needed,
                requested: N,
            });
        }
        Ok(match self.model {
            AnemoiModel::Fcico => self.full_state_system(),
            AnemoiModel::Pcico => self.partial_state_system(),
        })
    }

    /// Model `F`, in the `o1` variable order.
    ///
    /// `x_1 > y_0 > x_2 > y_1 > … > x_{N−1} > y_{N−2} > y_{N−1} > y_N`, which at `N = 1` degenerates
    /// to `y_0 > y_1`. `x_0` and `x_N` do not appear: they are the CICO conditions, substituted
    /// rather than carried as pinning equations.
    fn full_state_system<const N: usize>(&self) -> Vec<MultivariatePolynomial<N, F>> {
        let rounds = self.anemoi.parameters.rounds;
        let x = |round: usize| -> MultivariatePolynomial<N, F> {
            if round == 0 || round == rounds {
                // The CICO conditions.
                MultivariatePolynomial::zero()
            } else {
                variable(2 * (round - 1))
            }
        };
        let y = |round: usize| -> MultivariatePolynomial<N, F> {
            if round + 2 <= rounds {
                variable(2 * round + 1)
            } else {
                // The last two, which sit after every `x` in the ordering.
                variable(2 * (rounds - 1) + (round + 2 - rounds) - 1)
            }
        };

        let alpha = self.anemoi.parameters.alpha;
        let mut equations = Vec::with_capacity(2 * rounds);
        for round in 0..rounds {
            let before = (
                x(round) + constant(self.anemoi.c[round]),
                y(round) + constant(self.anemoi.d[round]),
            );
            let (state_x, state_y) = linear_layer(before);
            let output = (x(round + 1), y(round + 1));
            // The last round's output variables are in the permutation's output coordinates, so
            // the final linear layer is undone here rather than applied to them.
            let (u, v) = if round + 1 == rounds {
                inverse_linear_layer(output)
            } else {
                output
            };
            let difference = power(&(state_y.clone() - v.clone()), alpha);
            equations.push(
                square(&state_y).scale(&self.anemoi.beta) + difference.clone() - state_x.clone(),
            );
            equations.push(
                square(&v).scale(&self.anemoi.beta) + constant(self.anemoi.delta) + difference - u,
            );
        }
        equations
    }

    /// Model `P`, in the `o1` variable order `y_0 > s_N > … > s_1`.
    ///
    /// One variable per Flystel. The state words stay polynomials, so their degree compounds — that
    /// is the trade the model makes, and the reason its generator degrees reach `2N`.
    fn partial_state_system<const N: usize>(&self) -> Vec<MultivariatePolynomial<N, F>> {
        let rounds = self.anemoi.parameters.rounds;
        let alpha = self.anemoi.parameters.alpha;
        // `y_0` first, then `s_N` down to `s_1`.
        let s = |round: usize| -> MultivariatePolynomial<N, F> { variable(rounds - round + 1) };

        // `x_0 = 0` is the CICO condition on the input.
        let mut state = (MultivariatePolynomial::zero(), variable(0));
        let mut equations = Vec::with_capacity(rounds + 1);
        for round in 1..=rounds {
            let before = (
                state.0 + constant(self.anemoi.c[round - 1]),
                state.1 + constant(self.anemoi.d[round - 1]),
            );
            let (state_x, state_y) = linear_layer(before);
            let quadratic = square(&state_y).scale(&self.anemoi.beta);
            equations.push(power(&s(round), alpha) - state_x.clone() + quadratic.clone());
            // The open Flystel's output, expressed through the state variable just introduced.
            let v = state_y - s(round);
            state = (
                state_x - quadratic
                    + square(&v).scale(&self.anemoi.beta)
                    + constant(self.anemoi.delta),
                v,
            );
        }
        // The CICO condition on the output, after the final linear layer.
        let (output_x, _) = linear_layer(state);
        equations.push(output_x);
        equations
    }

    /// The assignment a trace of the permutation gives this model's variables.
    ///
    /// The faithfulness check's other half: a system that merely looked right would not vanish
    /// here. Returns `None` if `N` is not [`Self::variables`].
    pub fn assignment<const N: usize>(&self, y: F) -> Option<[F; N]> {
        if N != self.variables() {
            return None;
        }
        let rounds = self.anemoi.parameters.rounds;
        let trace = self.anemoi.trace(F::zero(), y);
        let mut point = [F::zero(); N];
        match self.model {
            AnemoiModel::Fcico => {
                // `trace[r]` is the state after round `r`, and `trace[rounds + 1]` is the output
                // of the final linear layer — which is what `x_N`, `y_N` denote.
                for round in 1..rounds {
                    point[2 * (round - 1)] = trace[round].0;
                    point[2 * (round - 1) + 1] = trace[round - 1].1;
                }
                point[2 * (rounds - 1)] = trace[rounds - 1].1;
                point[2 * (rounds - 1) + 1] = trace[rounds + 1].1;
            }
            AnemoiModel::Pcico => {
                point[0] = y;
                // `s_r` is the Flystel's inverse power map at round `r`: the difference between
                // the round's `y` input and its `v` output.
                for round in 1..=rounds {
                    let before = (
                        trace[round - 1].0 + self.anemoi.c[round - 1],
                        trace[round - 1].1 + self.anemoi.d[round - 1],
                    );
                    let (_, state_y) = Anemoi::<F>::linear_layer(before.0, before.1);
                    point[rounds - round + 1] = state_y - trace[round].1;
                }
            }
        }
        Some(point)
    }

    /// Whether `(0, y)` solves this instance, checked through the permutation.
    pub fn is_solution(&self, y: F) -> bool {
        self.anemoi.is_cico_solution(y)
    }
}

/// Whether every generator of `system` vanishes at the trace of `(0, y)`.
///
/// Returns the indices that did **not** vanish, so a failure says which round is wrong rather than
/// only that something is.
pub fn verify_against_anemoi_trace<const N: usize, F: KnownOrder>(
    instance: &AnemoiCico<F>,
    system: &[MultivariatePolynomial<N, F>],
    y: F,
) -> Vec<usize> {
    let Some(point) = instance.assignment::<N>(y) else {
        return (0..system.len()).collect();
    };
    system
        .iter()
        .enumerate()
        .filter(|(_, p)| !p.eval(&point).is_zero())
        .map(|(i, _)| i)
        .collect()
}

/// Something to do with an Anemoi CICO system once its dimension is known.
///
/// The `const N` bridge, as [`CicoVisitor`](super::CicoVisitor) is for Poseidon: a function cannot
/// return `Vec<MultivariatePolynomial<N, F>>` for an `N` chosen at runtime, and the registry's ten
/// Anemoi rows have nine distinct `N`.
pub trait AnemoiCicoVisitor<F: KnownOrder> {
    /// What the visit produces. Must not mention the dimension.
    type Output;

    /// Called once, with the system at its own dimension.
    fn visit<const N: usize>(self, system: &[MultivariatePolynomial<N, F>]) -> Self::Output;
}

/// Build `instance`'s system and hand it to `visitor` at its own dimension.
///
/// # Errors
/// [`AnemoiError::WrongDimension`] if the instance's variable count has no compiled dimension.
/// Every count the registry needs is compiled, which a test asserts.
pub fn dispatch_anemoi_cico<F: KnownOrder, V: AnemoiCicoVisitor<F>>(
    instance: &AnemoiCico<F>,
    visitor: V,
) -> Result<V::Output, AnemoiError> {
    let variables = instance.variables();

    // Every dimension the registry needs, and no others: a spare `N` monomorphizes the whole
    // pipeline again. FCICO at N = 1..6 needs 2, 4, 6, 8, 10, 12; PCICO needs 2, 3, 4, 5, 6, 7.
    macro_rules! dispatch {
        ($($n:literal),+ $(,)?) => {
            match variables {
                $($n => Ok(visitor.visit(&instance.system::<$n>()?)),)+
                variables => Err(AnemoiError::WrongDimension {
                    needed: variables,
                    requested: 0,
                }),
            }
        };
    }
    dispatch!(2, 3, 4, 5, 6, 7, 8, 10, 12)
}

/// `M(x, y) = (2x + y, x + y)`, over polynomials.
fn linear_layer<const N: usize, F: FiniteField>(
    state: (MultivariatePolynomial<N, F>, MultivariatePolynomial<N, F>),
) -> (MultivariatePolynomial<N, F>, MultivariatePolynomial<N, F>) {
    let y = state.1 + state.0.clone();
    (state.0 + y.clone(), y)
}

/// The inverse of [`linear_layer`], over polynomials.
fn inverse_linear_layer<const N: usize, F: FiniteField>(
    state: (MultivariatePolynomial<N, F>, MultivariatePolynomial<N, F>),
) -> (MultivariatePolynomial<N, F>, MultivariatePolynomial<N, F>) {
    let x = state.0 - state.1.clone();
    (x.clone(), state.1 - x)
}

/// The constant polynomial `c`.
fn constant<const N: usize, F: FiniteField>(c: F) -> MultivariatePolynomial<N, F> {
    MultivariatePolynomial::new(&[(Monomial::one(), c)])
}

/// The polynomial `x_index`.
fn variable<const N: usize, F: FiniteField>(index: usize) -> MultivariatePolynomial<N, F> {
    MultivariatePolynomial::new(&[(Monomial::univariate(index, 1), F::one())])
}

/// `p²`.
fn square<const N: usize, F: FiniteField>(
    p: &MultivariatePolynomial<N, F>,
) -> MultivariatePolynomial<N, F> {
    let mut accumulator = p.clone();
    accumulator *= p.clone();
    accumulator
}

/// `p^alpha`, by repeated multiplication; `alpha` is 3 in every registered row.
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
    use super::{verify_against_anemoi_trace, AnemoiCico, AnemoiModel};
    use crate::{
        fields::Zp18446744073709551263,
        grobner::{
            f4_reported,
            research::{
                anemoi::{Anemoi, AnemoiError, AnemoiParameters},
                published_quotient_dimension,
            },
            F4Options, HilbertSeries,
        },
        FiniteField, MonomialOrder,
    };

    type A = Zp18446744073709551263;

    fn instance(rounds: usize, model: AnemoiModel) -> AnemoiCico<A> {
        AnemoiCico::new(
            Anemoi::new(AnemoiParameters::six_worlds(rounds)).expect("builds"),
            model,
        )
    }

    /// Both models vanish at a trace of the permutation, at every round count the ladder covers.
    ///
    /// Faithfulness checked against the primitive rather than against the other model: a shared
    /// mistake in the round schedule would be invisible to a test comparing the two systems with
    /// each other.
    #[test]
    fn test_both_models_vanish_at_a_trace_of_the_permutation() {
        macro_rules! check {
            ($($rounds:literal => $fcico:literal, $pcico:literal;)+) => {$(
                let f = instance($rounds, AnemoiModel::Fcico);
                let point = A::new(7 * $rounds as u64 + 11);
                // FCICO substitutes x_0 = 0 and x_N = 0 rather than carrying them as equations,
                // and x_N = 0 holds only at a witness -- so at an arbitrary input exactly the
                // last round's two equations must fail, and every earlier one must not.
                assert_eq!(
                    verify_against_anemoi_trace(&f, &f.system::<$fcico>().expect("the right N"), point),
                    vec![2 * $rounds - 2, 2 * $rounds - 1],
                    "FCICO at N = {}", $rounds
                );
                let p = instance($rounds, AnemoiModel::Pcico);
                let system = p.system::<$pcico>().expect("the right N");
                // The output constraint is the last generator and must **not** vanish at an
                // arbitrary input: it is the only one that expresses the CICO condition, so a
                // model whose last equation vanished everywhere would be a model of nothing.
                assert_eq!(
                    verify_against_anemoi_trace(&p, &system, point),
                    vec![system.len() - 1],
                    "PCICO at N = {}", $rounds
                );
            )+};
        }
        // FCICO has 2N variables, PCICO has N + 1.
        check! {
            1 => 2, 2;
            2 => 4, 3;
            3 => 6, 4;
            4 => 8, 5;
            5 => 10, 6;
        }
    }

    /// `FCICO` vanishes entirely at a real CICO solution, output constraint included.
    ///
    /// `FCICO` folds the CICO conditions into its equations by substitution rather than carrying
    /// them separately, so every generator vanishing is the statement that the point is a witness.
    #[test]
    fn test_the_models_vanish_everywhere_at_a_reference_witness() {
        // From the committed Six Worlds lex basis at N = 2; see `anemoi.rs`.
        let witness = A::new(1_761_853_426_583_392_112);
        let f = instance(2, AnemoiModel::Fcico);
        assert!(f.is_solution(witness));
        assert_eq!(
            verify_against_anemoi_trace(&f, &f.system::<4>().expect("N = 4"), witness),
            Vec::<usize>::new()
        );
        let p = instance(2, AnemoiModel::Pcico);
        assert_eq!(
            verify_against_anemoi_trace(&p, &p.system::<3>().expect("N = 3"), witness),
            Vec::<usize>::new(),
            "the output constraint vanishes exactly at a witness"
        );
    }

    /// The built systems have the shapes the published model descriptions state.
    #[test]
    fn test_the_generator_degrees_are_the_published_shapes() {
        let f = instance(5, AnemoiModel::Fcico);
        let system = f.system::<10>().expect("N = 10");
        let degrees: Vec<u64> = system.iter().map(|p| p.degree()).collect();
        assert_eq!(
            degrees,
            vec![3; 10],
            "FCICO is every generator of degree alpha"
        );
        assert_eq!(degrees, AnemoiModel::Fcico.generator_degrees(5, 3));

        let p = instance(5, AnemoiModel::Pcico);
        let system = p.system::<6>().expect("N = 6");
        let degrees: Vec<u64> = system.iter().map(|p| p.degree()).collect();
        assert_eq!(
            degrees,
            vec![3, 4, 6, 8, 10, 6],
            "PCICO grows to 2N, and its output constraint is degree N + 1"
        );
        assert_eq!(degrees, AnemoiModel::Pcico.generator_degrees(5, 3));
    }

    /// The published variable and equation counts, at every rung of the ladder.
    ///
    /// These are the `n_v` and `n_e` the Six Worlds logs print per round count.
    #[test]
    fn test_the_sizes_match_the_published_logs() {
        for (rounds, fcico, pcico) in [(1, 2, 2), (2, 4, 3), (3, 6, 4), (4, 8, 5), (5, 10, 6)] {
            assert_eq!(AnemoiModel::Fcico.variables(rounds, 1), fcico);
            assert_eq!(AnemoiModel::Fcico.equations(rounds, 1), fcico);
            assert_eq!(AnemoiModel::Pcico.variables(rounds, 1), pcico);
            assert_eq!(AnemoiModel::Pcico.equations(rounds, 1), pcico);
        }
    }

    /// A dimension that is not the variable count is refused rather than padded.
    #[test]
    fn test_a_wrong_dimension_is_refused() {
        let f = instance(3, AnemoiModel::Fcico);
        assert_eq!(
            f.system::<7>().err(),
            Some(AnemoiError::WrongDimension {
                needed: 6,
                requested: 7
            })
        );
        assert!(f.assignment::<7>(A::new(1)).is_none());
    }

    /// Zeebra's own quotient dimension is the published `(α + 2)^N`, in both models.
    ///
    /// **The gate on the whole workstream.** `dim F_p[x]/I` does not depend on the machine, the
    /// library or the wall clock, so a disagreement here is a defect in Zeebra or in the model and
    /// not a performance difference. Computed from the leading-term ideal of the grevlex basis,
    /// which is combinatorial and needs no linear algebra past F4 — the published Magma F4 times
    /// for these rows are 0.017 s and 0.28 s, so this is cheap and single-threaded on purpose.
    #[test]
    fn test_the_quotient_dimension_is_the_published_power() {
        macro_rules! check {
            ($($rounds:literal => $fcico:literal, $pcico:literal;)+) => {$(
                for (model, variables) in
                    [(AnemoiModel::Fcico, $fcico), (AnemoiModel::Pcico, $pcico)]
                {
                    let system = match model {
                        AnemoiModel::Fcico => dimension_of(
                            &instance($rounds, model).system::<$fcico>().expect("the right N"),
                        ),
                        AnemoiModel::Pcico => dimension_of(
                            &instance($rounds, model).system::<$pcico>().expect("the right N"),
                        ),
                    };
                    assert_eq!(
                        i128::from(system),
                        *published_quotient_dimension(3, $rounds).value() as i128,
                        "N = {}, {} in {} variables: the quotient dimension disagrees with \
                         (alpha + 2)^N, which is a defect and not a timing",
                        $rounds, model.tag(), variables
                    );
                }
            )+};
        }
        check! {
            1 => 2, 2;
            2 => 4, 3;
            3 => 6, 4;
            4 => 8, 5;
        }
    }

    /// `dim F_p[x]/I` from the leading-term ideal of the degrevlex basis.
    fn dimension_of<const N: usize>(system: &[crate::MultivariatePolynomial<N, A>]) -> i64 {
        let (basis, _) = f4_reported(
            system,
            MonomialOrder::GradedReverseLexicographic,
            &F4Options::default(),
        );
        let basis = basis.expect("the basis completes at these round counts");
        let series = HilbertSeries::of_basis(&basis, MonomialOrder::GradedReverseLexicographic)
            .expect("a monomial ideal");
        series
            .quotient_dimension(
                &basis
                    .iter()
                    .map(|p| p.leading_monomial(MonomialOrder::GradedReverseLexicographic))
                    .collect::<Vec<_>>(),
            )
            .expect("within budget")
            .expect("zero-dimensional") as i64
    }

    /// The two models at one round count are different systems in different numbers of variables.
    #[test]
    fn test_the_two_models_are_not_the_same_system() {
        let f = instance(5, AnemoiModel::Fcico);
        let p = instance(5, AnemoiModel::Pcico);
        assert_eq!((f.variables(), p.variables()), (10, 6));
        assert_ne!(
            AnemoiModel::Fcico.generator_degrees(5, 3),
            AnemoiModel::Pcico.generator_degrees(5, 3)
        );
        assert_ne!(AnemoiModel::Fcico.tag(), AnemoiModel::Pcico.tag());
    }
}
