//! Fixing some variables, so that a positive-dimensional system has a zero-dimensional slice.
//!
//! The reason M21 needs this: the interesting cryptanalytic systems are underdetermined. A
//! Poseidon CICO instance may constrain two outputs and leave fourteen inputs free, so the
//! unspecialized ideal generally has positive dimension and **classical FGLM does not apply to it
//! at all**. Fixing `x_i = a_i` for `i ∈ S` gives `I_a`, which may be zero-dimensional, and a
//! point of `I_a` combined with the fixed assignments is a candidate point of `I`.
//!
//! # Two rules, and they are the whole module
//!
//! 1. **A candidate is verified against every original generator**, after lifting. Not against the
//!    specialized system, not against any basis derived from it. [`SliceOutcome::Witness`] is
//!    constructed only after that check.
//!
//! 2. **An empty slice proves nothing about the original system.** A hyperplane section of a
//!    nonempty variety can be empty over `F_q` while the variety is not, and a *sequence* of empty
//!    slices is still not a proof — only `q^|S|` of them would be, which is not a computation.
//!    [`SliceOutcome`] is shaped so that this is hard to misread: see
//!    [`SliceOutcome::is_evidence_about_the_original_system`].
//!
//! The second rule is the one that gets broken. `solve_one` on a slice returning "no solution" is
//! a fact about the slice, and reporting it as a fact about the system would be a wrong answer
//! rather than a missing one.
//!
//! # What this does not do
//!
//! It does not choose `S`, and it does not choose `|S|`. How many variables to fix is a decision
//! the caller makes and the report records — never one inferred from the number of equations,
//! because the number of equations does not determine the dimension (cyclic-4 is four in four and
//! positive-dimensional). [`SystemShape::specialization_candidates`](crate::grobner::SystemShape::specialization_candidates)
//! ranks variables by how few equations constrain them, and that is a ranking and not a
//! recommendation.
//!
//! Specialized variables stay as **inactive positions in the same `N`-variable ring**. `const N`
//! is not replaced and no second polynomial representation is introduced; a fixed variable simply
//! appears in no monomial after substitution.

use std::fmt::{Display, Formatter};

use rand::{rngs::StdRng, SeedableRng};

use crate::{FiniteField, Monomial, MultivariatePolynomial};

/// Why a set of assignments is not a usable specialization.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SpecializationError {
    /// A variable index is not one of the ring's `N`.
    VariableOutOfRange { index: usize, variables: usize },

    /// The same variable was assigned twice.
    ///
    /// Refused rather than resolved by last-write-wins: two assignments to one variable is a
    /// caller bug, and silently keeping one of them would make the recorded specialization
    /// disagree with what was computed.
    DuplicateVariable { index: usize },
}

impl Display for SpecializationError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::VariableOutOfRange { index, variables } => write!(
                f,
                "variable {} is not one of the {} in the ring",
                index, variables
            ),
            Self::DuplicateVariable { index } => {
                write!(f, "variable {} was assigned more than once", index)
            }
        }
    }
}

impl std::error::Error for SpecializationError {}

/// Which variables are fixed, to what, and how they were chosen.
///
/// The record a reproducible experiment needs. Everything that decided the slice is here, so an
/// experiment report can be replayed exactly: the variables, the values, and the seed if the
/// values came from one.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Specialization<const N: usize, F: FiniteField> {
    /// `(variable, value)`, ascending by variable. Sorted on construction so that two
    /// specializations with the same content compare equal whatever order they were given in.
    fixed: Vec<(usize, F)>,

    /// The seed the values were drawn from, if they were.
    ///
    /// Present only when [`Self::seeded`] produced them, and then it really does reproduce them.
    seed: Option<u64>,
}

impl<const N: usize, F: FiniteField> Specialization<N, F> {
    /// Fix the named variables to the named values.
    ///
    /// # Errors
    /// [`SpecializationError`] if an index is out of range or a variable appears twice.
    pub fn new(assignments: &[(usize, F)]) -> Result<Self, SpecializationError> {
        let mut fixed = assignments.to_vec();
        fixed.sort_by_key(|(index, _)| *index);
        for window in fixed.windows(2) {
            if window[0].0 == window[1].0 {
                return Err(SpecializationError::DuplicateVariable { index: window[0].0 });
            }
        }
        if let Some((index, _)) = fixed.iter().find(|(index, _)| *index >= N) {
            return Err(SpecializationError::VariableOutOfRange {
                index: *index,
                variables: N,
            });
        }
        Ok(Self { fixed, seed: None })
    }

    /// Fix the named variables to values drawn from `seed`, and record the seed.
    ///
    /// **The seed determines the slice.** An RNG is constructed from it here rather than taken as
    /// a parameter, because the first version did take one — recording the seed beside values it
    /// had not produced, so the recorded seed did not reproduce the recorded slice. A field named
    /// `seed` that does not reproduce anything is worse than no field.
    ///
    /// The values are still recorded in full, so a slice replays either way; what this adds is
    /// that the seed alone suffices, which is what an experiment record wants to carry.
    ///
    /// A caller who wants slices from its own stream should draw the values and use
    /// [`Self::new`], which records no seed and claims none.
    ///
    /// # Errors
    /// As [`Self::new`].
    pub fn seeded(variables: &[usize], seed: u64) -> Result<Self, SpecializationError> {
        let mut rng = StdRng::seed_from_u64(seed);
        let assignments: Vec<(usize, F)> = variables
            .iter()
            .map(|&i| (i, F::random(&mut rng)))
            .collect();
        let mut specialization = Self::new(&assignments)?;
        specialization.seed = Some(seed);
        Ok(specialization)
    }

    /// Nothing fixed. The identity, useful as the zeroth slice of a campaign.
    pub fn none() -> Self {
        Self {
            fixed: Vec::new(),
            seed: None,
        }
    }

    /// The assignments, ascending by variable.
    pub fn fixed(&self) -> &[(usize, F)] {
        &self.fixed
    }

    /// How many variables are fixed.
    pub fn len(&self) -> usize {
        self.fixed.len()
    }

    /// Whether nothing is fixed.
    pub fn is_empty(&self) -> bool {
        self.fixed.is_empty()
    }

    /// The seed the values were drawn from, if they were drawn from one.
    ///
    /// `Some(s)` is a promise: `Specialization::seeded(variables, s)` reconstructs this slice.
    pub fn seed(&self) -> Option<u64> {
        self.seed
    }

    /// The value `index` is fixed to, if it is.
    pub fn value_of(&self, index: usize) -> Option<F> {
        self.fixed
            .iter()
            .find(|(i, _)| *i == index)
            .map(|(_, v)| *v)
    }

    /// The generators of `I_a = I + <x_i - a_i : i ∈ S>`.
    ///
    /// # Substitution alone is not the slice, and this is the module's one subtlety
    ///
    /// The result lives in the same `N`-variable ring, because `const N` is not replaced. So a
    /// fixed variable does not *leave* — substitution only removes it from every monomial, and a
    /// variable that appears in no generator is **unconstrained**, which makes the ideal
    /// positive-dimensional however many equations are left.
    ///
    /// Concretely: `x*y - 6` at `x = 2` substitutes to `2y - 6`, whose zero set in `F[x, y]` is
    /// the *line* `{(x, 3)}`. The zero-dimensional solvers refuse it, correctly, and the first
    /// draft of this module hit exactly that.
    ///
    /// So the pinning equations `x_i - a_i` are appended. They generate the same ideal as the
    /// substitution — reducing a generator modulo `x_i - a_i` is what substituting *is* — and
    /// together the two give `I_a`, whose variety is the slice. Substituting as well as pinning is
    /// not redundant work but a better generating set: the substituted generators are smaller, and
    /// the linear forms make the fixed coordinates part of the answer rather than something to
    /// patch in afterwards.
    ///
    /// A substituted generator can become zero or a nonzero constant, and both are meaningful: the
    /// first says that generator is satisfied by the assignment, the second that it is contradicted
    /// by it.
    pub fn apply(
        &self,
        system: &[MultivariatePolynomial<N, F>],
    ) -> Vec<MultivariatePolynomial<N, F>> {
        let mut sliced: Vec<MultivariatePolynomial<N, F>> = system
            .iter()
            .map(|p| {
                self.fixed
                    .iter()
                    .fold(p.clone(), |q, (index, value)| q.substitute(*index, *value))
            })
            .collect();
        sliced.extend(
            self.fixed
                .iter()
                .map(|(index, value)| self.pin(*index, *value)),
        );
        sliced
    }

    /// `x_index - value`, the equation that pins a fixed variable.
    fn pin(&self, index: usize, value: F) -> MultivariatePolynomial<N, F> {
        MultivariatePolynomial::new(&[
            (Monomial::univariate(index, 1), F::one()),
            (Monomial::one(), -value),
        ])
    }

    /// A point of the slice, completed with the fixed assignments.
    ///
    /// The coordinates of fixed variables in `partial` are **overwritten**, not read.
    ///
    /// Note what this is *not* needed for. [`Self::apply`] appends the pinning equations, so a
    /// point of `I_a` already has `x_i = a_i` and `solve_slice` asserts that rather than patching
    /// it — a disagreement there would be a defect, and overwriting would hide it. This is for a
    /// caller who solved the substituted generators *without* the pins, in which case the fixed
    /// coordinates are whatever the search happened to assign and have to be replaced.
    pub fn lift(&self, partial: &[F; N]) -> [F; N] {
        let mut point = *partial;
        for (index, value) in &self.fixed {
            point[*index] = *value;
        }
        point
    }
}

impl<const N: usize, F: FiniteField> Display for Specialization<N, F> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if self.fixed.is_empty() {
            return write!(f, "nothing fixed");
        }
        let assignments: Vec<String> = self
            .fixed
            .iter()
            .map(|(index, value)| format!("x{} = {}", index, value))
            .collect();
        write!(f, "{}", assignments.join(", "))?;
        if let Some(seed) = self.seed {
            write!(f, " (seed {})", seed)?;
        }
        Ok(())
    }
}

/// `system` with `specialization` applied. See [`Specialization::apply`].
pub fn specialize<const N: usize, F: FiniteField>(
    system: &[MultivariatePolynomial<N, F>],
    specialization: &Specialization<N, F>,
) -> Vec<MultivariatePolynomial<N, F>> {
    specialization.apply(system)
}

/// Whether `point` satisfies every generator of `system`.
///
/// The only check that licenses calling something a witness. Evaluates the **original** generators,
/// so it is independent of every transformation between them and the point — specialization,
/// Gröbner basis, conversion, back-substitution.
pub fn satisfies<const N: usize, F: FiniteField>(
    system: &[MultivariatePolynomial<N, F>],
    point: &[F; N],
) -> bool {
    system.iter().all(|p| p.eval(point).is_zero())
}

#[cfg(test)]
mod tests {
    use super::{satisfies, specialize, Specialization, SpecializationError};
    use crate::{fields::Zp2147483647, FiniteField, MultivariatePolynomial, Zero};

    type F = Zp2147483647;

    fn parse<const N: usize>(
        strings: &[&str],
        vars: [&str; N],
    ) -> Vec<MultivariatePolynomial<N, F>> {
        strings
            .iter()
            .map(|s| MultivariatePolynomial::parse(s, vars).expect("parses"))
            .collect()
    }

    /// The slice is the substituted generators **plus** the pinning equations.
    ///
    /// Hand-derived, and the pins are the part that is easy to leave out: without `x - 3` the
    /// variable is absent from every generator and therefore unconstrained, which makes the ideal
    /// positive-dimensional and the zero-dimensional solvers refuse it.
    #[test]
    fn test_the_slice_is_the_substitution_plus_the_pins() {
        let vars = ["x", "y", "z"];
        let system = parse(&["x*y + z - 1", "x^2 - y"], vars);

        // x = 3: the first becomes 3y + z - 1, the second 9 - y, and x is pinned.
        let at_three =
            Specialization::<3, F>::new(&[(0, F::new(3))]).expect("a valid specialization");
        let sliced = specialize(&system, &at_three);
        assert_eq!(sliced, parse(&["3*y + z - 1", "9 - y", "x - 3"], vars));

        // Two variables fixed gives two pins, appended in ascending index order.
        let at_two = Specialization::<3, F>::new(&[(2, F::new(5)), (0, F::new(3))]).expect("valid");
        let sliced = specialize(&system, &at_two);
        assert_eq!(
            sliced,
            parse(&["3*y + 4", "9 - y", "x - 3", "z - 5"], vars),
            "the pins follow the substituted generators, ascending by variable"
        );
    }

    /// Without the pins the slice would be positive-dimensional, which is why `apply` adds them.
    ///
    /// Pinned directly rather than left to the solver tests, because it is the one place the
    /// "inactive positions in the same ring" design decision could have gone wrong silently.
    #[test]
    fn test_substitution_alone_leaves_the_fixed_variable_unconstrained() {
        use crate::{
            grobner::{classify_ideal, f4},
            MonomialOrder,
        };

        let vars = ["x", "y"];
        let system = parse(&["x*y - 6"], vars);
        let grevlex = MonomialOrder::GradedReverseLexicographic;

        // Substitution alone: `2y - 6`, whose zero set in F[x, y] is the line {(x, 3)}.
        let substituted = parse(&["2*y - 6"], vars);
        let basis = f4(&substituted, grevlex).expect("within limits");
        assert!(
            !classify_ideal(&basis, grevlex).is_finite_dimensional(),
            "x is unconstrained, so the substituted system is positive-dimensional"
        );

        // With the pin, the ideal is the single point (2, 3).
        let slice = Specialization::<2, F>::new(&[(0, F::new(2))]).expect("valid");
        let basis = f4(&specialize(&system, &slice), grevlex).expect("within limits");
        assert!(classify_ideal(&basis, grevlex).is_finite_dimensional());
    }

    /// A generator can vanish, or become a nonzero constant, and both are meaningful.
    #[test]
    fn test_substitution_can_vanish_or_contradict() {
        let vars = ["x", "y"];

        // x = 0 satisfies `x*y` identically: the generator becomes zero.
        let system = parse(&["x*y", "y - 1"], vars);
        let at_zero = Specialization::<2, F>::new(&[(0, F::zero())]).expect("valid");
        let sliced = specialize(&system, &at_zero);
        assert!(sliced[0].is_zero(), "x*y vanishes at x = 0");

        // x = 5 contradicts `x - 1`: the generator becomes the nonzero constant 4.
        let system = parse(&["x - 1", "y"], vars);
        let at_five = Specialization::<2, F>::new(&[(0, F::new(5))]).expect("valid");
        let sliced = specialize(&system, &at_five);
        assert!(sliced[0].is_constant() && !sliced[0].is_zero());
    }

    /// Lifting takes the fixed coordinates from the specialization, not from the solver's output.
    ///
    /// The bug this prevents: a solver handed the specialized system sees the fixed variables as
    /// unconstrained, and whatever it assigns them is not the value the slice was taken at.
    #[test]
    fn test_lifting_overwrites_whatever_the_solver_assigned() {
        let specialization =
            Specialization::<3, F>::new(&[(0, F::new(7)), (2, F::new(11))]).expect("valid");

        // A "solution" of the slice in which the fixed coordinates are junk.
        let partial = [F::new(999), F::new(4), F::new(999)];
        let lifted = specialization.lift(&partial);

        assert_eq!(lifted, [F::new(7), F::new(4), F::new(11)]);
    }

    /// Assignments are sorted and deduplicated, and out-of-range indices are refused.
    #[test]
    fn test_construction_validates_and_canonicalizes() {
        // Given out of order, stored ascending — so equal content compares equal.
        let a = Specialization::<3, F>::new(&[(2, F::new(1)), (0, F::new(2))]).expect("valid");
        let b = Specialization::<3, F>::new(&[(0, F::new(2)), (2, F::new(1))]).expect("valid");
        assert_eq!(a, b);
        assert_eq!(a.fixed()[0].0, 0);
        assert_eq!(a.len(), 2);
        assert_eq!(a.value_of(2), Some(F::new(1)));
        assert_eq!(a.value_of(1), None);

        assert_eq!(
            Specialization::<3, F>::new(&[(1, F::new(1)), (1, F::new(2))]),
            Err(SpecializationError::DuplicateVariable { index: 1 })
        );
        assert_eq!(
            Specialization::<3, F>::new(&[(3, F::new(1))]),
            Err(SpecializationError::VariableOutOfRange {
                index: 3,
                variables: 3
            })
        );

        let nothing = Specialization::<3, F>::none();
        assert!(nothing.is_empty());
        assert_eq!(nothing.seed(), None);
        assert_eq!(nothing.to_string(), "nothing fixed");
    }

    /// Nothing fixed leaves the system alone.
    #[test]
    fn test_the_empty_specialization_is_the_identity() {
        let vars = ["x", "y"];
        let system = parse(&["x*y - 1", "x^2 - y"], vars);
        assert_eq!(specialize(&system, &Specialization::none()), system);
    }

    /// The seed reproduces the slice, which is the whole claim the field makes.
    ///
    /// The first version took an RNG *and* a seed, and recorded the seed beside values it had not
    /// produced — so `seed()` named something that reproduced nothing. This asserts the promise
    /// the accessor's documentation now makes.
    #[test]
    fn test_the_seed_reproduces_the_slice() {
        let variables = [0, 2];
        let first = Specialization::<3, F>::seeded(&variables, 42).expect("valid");
        let again = Specialization::<3, F>::seeded(&variables, 42).expect("valid");
        assert_eq!(first, again, "the same seed must give the same slice");
        assert_eq!(first.seed(), Some(42));
        assert_eq!(first.len(), 2);
        assert!(first.to_string().contains("seed 42"));

        // From the seed alone, with nothing else carried over.
        let from_seed = Specialization::<3, F>::seeded(&variables, first.seed().expect("recorded"))
            .expect("valid");
        assert_eq!(from_seed.fixed(), first.fixed());

        let different = Specialization::<3, F>::seeded(&variables, 43).expect("valid");
        assert_ne!(
            first.fixed(),
            different.fixed(),
            "a different seed should give a different slice"
        );

        // Values chosen rather than drawn claim no seed, so nothing promises to reproduce them.
        let chosen = Specialization::<3, F>::new(&[(0, F::new(5))]).expect("valid");
        assert_eq!(chosen.seed(), None);
        assert!(!chosen.to_string().contains("seed"));
    }

    /// `satisfies` checks the original generators, and rejects a point that misses one.
    #[test]
    fn test_satisfies_checks_every_generator() {
        let vars = ["x", "y"];
        let system = parse(&["x^2 - 4", "y - x"], vars);
        assert!(satisfies(&system, &[F::new(2), F::new(2)]));
        // Satisfies the first and not the second.
        assert!(!satisfies(&system, &[F::new(2), F::new(3)]));
        // Satisfies the second and not the first.
        assert!(!satisfies(&system, &[F::new(3), F::new(3)]));
    }
}
