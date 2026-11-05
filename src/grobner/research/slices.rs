//! Solving a slice, lifting the result, and saying exactly what that does and does not establish.
//!
//! The half of M21-E that is about epistemics rather than algebra. [`specialize`] is a
//! substitution; this is where the answer gets a truth value.

use std::fmt::{Display, Formatter};

use rand::{CryptoRng, RngCore};

use crate::{
    grobner::{
        research::specialization::{satisfies, Specialization},
        solve_one_planned, PlannedSolveOptions, SolveError, SolveOutcome, SolvePlan,
    },
    KnownOrder, MultivariatePolynomial,
};

/// What solving one slice established.
///
/// **Only [`Self::Witness`] says anything about the original system.** The other two are facts
/// about the slice, and the whole point of giving them their own variants rather than collapsing
/// them into "no solution" is that a slice's emptiness is not the system's.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SliceOutcome<const N: usize, F: KnownOrder> {
    /// A point of the **original** system, lifted and checked against every original generator.
    ///
    /// Constructed only after that check. An unverified candidate never reaches this variant.
    Witness([F; N]),

    /// The slice is zero-dimensional and has no point over the base field.
    ///
    /// **Not evidence about the original system.** A hyperplane section of a nonempty variety can
    /// be empty over `F_q` while the variety is not, so this bounds nothing. Even a long run of
    /// these bounds nothing: only exhausting all `q^|S|` slices would, which is not a computation
    /// for the fields M20 added.
    EmptySlice,

    /// The slice is inconsistent: `1` is in `I_a`.
    ///
    /// **Not evidence about the original system either**, and for the same reason — fixing a
    /// variable to a value no solution uses makes the remaining equations contradict each other,
    /// which says nothing about the solutions that use a different value.
    SliceInconsistent,
}

impl<const N: usize, F: KnownOrder> SliceOutcome<N, F> {
    /// Whether this outcome says anything at all about the **original** system.
    ///
    /// True only for [`Self::Witness`]. Written as a method so that a caller reporting results has
    /// to pass through it rather than reason about the variants, because the reasoning is exactly
    /// what goes wrong: "the solver said no solution" is a true statement about a slice and a
    /// false one about a system.
    pub fn is_evidence_about_the_original_system(&self) -> bool {
        matches!(self, Self::Witness(_))
    }

    /// The witness, if there is one.
    pub fn witness(&self) -> Option<[F; N]> {
        match self {
            Self::Witness(point) => Some(*point),
            _ => None,
        }
    }
}

impl<const N: usize, F: KnownOrder> Display for SliceOutcome<N, F> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Witness(_) => write!(f, "a verified witness for the original system"),
            Self::EmptySlice => write!(
                f,
                "this slice has no base-field point — no evidence about the original system"
            ),
            Self::SliceInconsistent => write!(
                f,
                "this slice is inconsistent — no evidence about the original system"
            ),
        }
    }
}

/// One slice, run end to end: specialize, solve, lift, verify.
///
/// The verification is against `system` — the generators as passed, not the slice and not any
/// basis derived from it — and it happens before a [`SliceOutcome::Witness`] can be constructed.
/// So a witness returned here satisfies the original equations by construction, and the nearest
/// thing to a bug this can have is returning `EmptySlice` when it should have found a point.
///
/// # Errors
/// Whatever the solver reports. An `Err` means **inconclusive about the slice**, which is two
/// steps removed from any statement about the original system.
///
/// # Panics
/// If a point of the slice lifts to something that does not satisfy the original system. That
/// would mean specialization and lifting disagree — a defect in this module, not a solver failure
/// — and it is an assertion rather than an error for the same reason the solvers assert their own
/// verification: there is no correct way to continue.
///
/// ```
/// use rand::{prelude::StdRng, SeedableRng};
/// use zeebra::{
///     fields::Zp2147483647,
///     grobner::{
///         research::{solve_slice, SliceOutcome, Specialization},
///         PlannedSolveOptions,
///     },
///     FiniteField, MultivariatePolynomial,
/// };
///
/// type F = Zp2147483647;
/// // One equation in two unknowns: a curve, so positive-dimensional and out of scope for the
/// // zero-dimensional solvers.
/// let curve: Vec<MultivariatePolynomial<2, F>> =
///     vec![MultivariatePolynomial::parse("x*y - 6", ["x", "y"]).unwrap()];
///
/// // Fix x = 2 and the slice is zero-dimensional: y = 3.
/// let slice = Specialization::new(&[(0, F::new(2))]).unwrap();
/// let (outcome, _plan) = solve_slice(
///     &curve,
///     &slice,
///     &PlannedSolveOptions::default(),
///     &mut StdRng::seed_from_u64(1),
/// );
///
/// let point = outcome.unwrap().witness().expect("x = 2, y = 3");
/// assert_eq!(point, [F::new(2), F::new(3)]);
/// ```
#[allow(clippy::type_complexity)]
pub fn solve_slice<const N: usize, F: KnownOrder, R: RngCore + CryptoRng>(
    system: &[MultivariatePolynomial<N, F>],
    specialization: &Specialization<N, F>,
    options: &PlannedSolveOptions,
    rng: &mut R,
) -> (Result<SliceOutcome<N, F>, SolveError>, SolvePlan) {
    let sliced = specialization.apply(system);
    let (outcome, plan) = solve_one_planned(&sliced, rng, options);

    let outcome = outcome.map(|outcome| match outcome {
        SolveOutcome::Point(point) => {
            // `Specialization::apply` appends the pinning equations `x_i - a_i`, so a point of the
            // slice already carries the fixed values. Asserted rather than patched with
            // `Specialization::lift`: a disagreement here would mean the pins were not in the
            // system the solver saw, and overwriting would hide that rather than report it.
            for (index, value) in specialization.fixed() {
                assert_eq!(
                    point[*index], *value,
                    "the solver returned x{} = {} where the slice fixes it to {}",
                    index, point[*index], value
                );
            }
            // The check that makes it a witness. Against `system`, so it is independent of every
            // transformation between the generators and the point.
            assert!(
                satisfies(system, &point),
                "a point of the slice is {:?}, which does not satisfy the original system",
                point
            );
            SliceOutcome::Witness(point)
        }
        SolveOutcome::NoBaseFieldPoint => SliceOutcome::EmptySlice,
        SolveOutcome::Inconsistent => SliceOutcome::SliceInconsistent,
    });

    (outcome, plan)
}

#[cfg(test)]
mod tests {
    use rand::{prelude::StdRng, SeedableRng};

    use super::{solve_slice, SliceOutcome};
    use crate::{
        fields::Zp2147483647,
        grobner::{
            research::specialization::Specialization, solve_one, PlannedSolveOptions, SolveError,
            SolvePolicy,
        },
        FiniteField, MultivariatePolynomial, Zero,
    };

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

    fn solve<const N: usize>(
        system: &[MultivariatePolynomial<N, F>],
        slice: &Specialization<N, F>,
        seed: u64,
    ) -> Result<SliceOutcome<N, F>, SolveError> {
        let options = PlannedSolveOptions::with_policy(SolvePolicy::AutoWithFallback);
        solve_slice(system, slice, &options, &mut StdRng::seed_from_u64(seed)).0
    }

    /// A positive-dimensional system the solvers refuse becomes solvable once sliced.
    ///
    /// M21-E's reason to exist, in the smallest possible instance. `x*y - 6` is a curve: refused
    /// outright by `solve_one`. Fixed at `x = 2` it is `2y - 6`, with the point `y = 3`, and the
    /// lift `(2, 3)` satisfies the original equation.
    #[test]
    fn test_a_slice_makes_an_underdetermined_system_solvable() {
        let vars = ["x", "y"];
        let curve = parse(&["x*y - 6"], vars);

        // Unspecialized, it is out of scope — not a budget failure, a property of the ideal.
        let mut rng = StdRng::seed_from_u64(1);
        assert_eq!(
            solve_one(&curve, &mut rng),
            Err(SolveError::PositiveDimensional)
        );

        let slice = Specialization::new(&[(0, F::new(2))]).expect("valid");
        let outcome = solve(&curve, &slice, 1).expect("the slice is solvable");
        assert_eq!(
            outcome,
            SliceOutcome::Witness([F::new(2), F::new(3)]),
            "x = 2 forces y = 3"
        );
        assert!(outcome.is_evidence_about_the_original_system());
    }

    /// An empty slice is not evidence about a system that *does* have solutions.
    ///
    /// The rule that gets broken. `x*y - 6` has plenty of points; the slice at `x = 0` has none,
    /// because `0 * y = 6` is unsatisfiable. A report that turned this into "no solution" would be
    /// a wrong answer rather than a missing one, and the method name is the guard.
    #[test]
    fn test_an_empty_slice_is_not_evidence_about_the_original_system() {
        let vars = ["x", "y"];
        let curve = parse(&["x*y - 6"], vars);

        // x = 0 makes the equation `-6 = 0`: inconsistent as a slice.
        let dead = Specialization::new(&[(0, F::zero())]).expect("valid");
        let outcome = solve(&curve, &dead, 2).expect("within limits");
        assert_eq!(outcome, SliceOutcome::SliceInconsistent);
        assert!(
            !outcome.is_evidence_about_the_original_system(),
            "an inconsistent slice says nothing about the system"
        );
        assert_eq!(outcome.witness(), None);

        // And the system is satisfiable, which a different slice shows immediately.
        let alive = Specialization::new(&[(0, F::new(3))]).expect("valid");
        assert!(solve(&curve, &alive, 3)
            .expect("within limits")
            .is_evidence_about_the_original_system());
    }

    /// A slice with no *base-field* point is also not evidence, and is a different fact.
    ///
    /// `x - y^2` over GF(2^31 - 1): fixing `x` to a non-square leaves `y^2 = c` with no root,
    /// which is `EmptySlice` rather than `SliceInconsistent` — the variety is nonempty over an
    /// extension. Both are "no solution here" and neither is "no solution".
    #[test]
    fn test_a_slice_with_no_base_field_point_is_its_own_outcome() {
        let vars = ["x", "y"];
        let parabola = parse(&["x - y^2"], vars);

        // Found by search rather than assumed: which small integers are squares differs by field.
        let non_square = (2u64..200)
            .find(|&c| {
                let slice = Specialization::new(&[(0, F::new(c))]).expect("valid");
                matches!(solve(&parabola, &slice, 4), Ok(SliceOutcome::EmptySlice))
            })
            .expect("some small integer is a non-square");

        let slice = Specialization::new(&[(0, F::new(non_square))]).expect("valid");
        let outcome = solve(&parabola, &slice, 4).expect("within limits");
        assert_eq!(outcome, SliceOutcome::EmptySlice);
        assert!(!outcome.is_evidence_about_the_original_system());

        // The companion: a square *is* solvable, so the above is about this value and not about
        // the solver failing on every parabola slice.
        let square = F::new(non_square) * F::new(non_square);
        let slice = Specialization::new(&[(0, square)]).expect("valid");
        let point = solve(&parabola, &slice, 5)
            .expect("within limits")
            .witness()
            .expect("y^2 = c^2 has a root");
        assert_eq!(point[1] * point[1], square);
    }

    /// A sequence of empty slices is still not a proof, and the API offers no way to say it is.
    ///
    /// Four dead slices in a row on a system that is satisfiable. The point of the test is the
    /// final assertion: nothing accumulated across the attempts, because nothing could.
    #[test]
    fn test_a_run_of_empty_slices_proves_nothing() {
        let vars = ["x", "y"];
        // y = 0 forces x*0 = 6, unsatisfiable, so every slice fixing y to 0 is dead — and the
        // system still has a point for every nonzero y.
        let curve = parse(&["x*y - 6"], vars);

        let mut dead = 0;
        for _ in 0..4 {
            let slice = Specialization::new(&[(1, F::zero())]).expect("valid");
            let outcome = solve(&curve, &slice, 6).expect("within limits");
            assert!(!outcome.is_evidence_about_the_original_system());
            dead += 1;
        }
        assert_eq!(dead, 4);

        // And the system is satisfiable, which the run of four did not and could not detect.
        let alive = Specialization::new(&[(1, F::new(2))]).expect("valid");
        assert_eq!(
            solve(&curve, &alive, 7).expect("within limits").witness(),
            Some([F::new(3), F::new(2)])
        );
    }

    /// An underdetermined quadratic system yields a witness verified against the original.
    ///
    /// Closer to the MQ shape: six variables, three quadratics, so positive-dimensional. Fixing
    /// three of them leaves a zero-dimensional slice.
    #[test]
    fn test_an_underdetermined_quadratic_system() {
        let vars = ["a", "b", "c", "d", "e", "f"];
        let system = parse(
            &[
                "a*b + c*d - e - 1",
                "b*c + d*e - f - 2",
                "c*d + e*f - a - 3",
            ],
            vars,
        );

        // Not zero-dimensional as given: three equations, six unknowns.
        let mut rng = StdRng::seed_from_u64(8);
        assert_eq!(
            solve_one(&system, &mut rng),
            Err(SolveError::PositiveDimensional)
        );

        // Fix three variables and try slices until one has a point. How many to fix is this test's
        // decision, not something inferred from `3 equations, 6 unknowns`.
        let free = [0, 1, 2];
        let mut found = None;
        for seed in 0..12u64 {
            let slice = Specialization::<6, F>::seeded(&free, seed).expect("valid indices");
            if let Ok(outcome) = solve(&system, &slice, 10 + seed) {
                if let Some(point) = outcome.witness() {
                    // Already asserted inside `solve_slice`; asserted again here because this is
                    // the claim the whole sub-milestone makes.
                    for p in &system {
                        assert!(p.eval(&point).is_zero(), "{} is not satisfied", p);
                    }
                    // And the fixed coordinates really are the ones the slice named.
                    for (index, value) in slice.fixed() {
                        assert_eq!(point[*index], *value);
                    }
                    found = Some((point, slice));
                    break;
                }
            }
        }
        assert!(
            found.is_some(),
            "twelve seeded slices of a satisfiable system found no witness"
        );
    }

    /// The plan beside the outcome describes the slice, not the original system.
    #[test]
    fn test_the_plan_describes_the_slice() {
        let vars = ["x", "y"];
        let curve = parse(&["x*y - 6"], vars);
        let slice = Specialization::new(&[(0, F::new(2))]).expect("valid");

        let (outcome, plan) = solve_slice(
            &curve,
            &slice,
            &PlannedSolveOptions::default(),
            &mut StdRng::seed_from_u64(11),
        );
        assert!(outcome.is_ok());
        // Two variables in the ring either way — a fixed variable stays an inactive position —
        // but the slice's generator has lost a term, so the shapes differ.
        assert_eq!(plan.shape.variables, 2);
        assert_eq!(plan.shape.max_degree, 1, "x*y - 6 became 2*y - 6");
        assert!(!plan.attempts.is_empty());
    }
}
