//! Eliminating the variables an affine generator determines, and putting them back.
//!
//! A CICO system's `k` output constraints are affine, and so is nothing else in it — the S-box
//! equations are `v - s^alpha`. An affine generator `c + Σ a_i x_i` with some `a_j` invertible
//! determines `x_j` as an affine function of the others, so the system has `k` variables it does
//! not really need. Removing them is M22-E's §10.3, and it is bounded on purpose: this is
//! **Gaussian elimination on the affine part of a generating set**, not a general preprocessor and
//! not nonlinear elimination.
//!
//! # Why this is not just reducing modulo the affine generator
//!
//! F4 already reduces by an affine basis element: symbolic preprocessing will cover any monomial
//! divisible by `x_j` with a multiple of that generator. What it cannot do is make `x_j` *stop
//! existing*. The variable keeps a column in every matrix, keeps its share of the monomial order,
//! and keeps generating critical pairs. [`AffineElimination::project`] removes it from the ring, at
//! a smaller compile-time dimension, which is the part that changes the matrices.
//!
//! # What has to be true for a point to come back
//!
//! Projection is only sound with a reconstruction, and the reconstruction has to be exact rather
//! than approximate or search-based. Two things make it so:
//!
//! - Every eliminated variable is recorded as an affine expression in the **kept** variables only.
//!   That is maintained by back-substituting each new expression into the ones already recorded, so
//!   no recorded expression ever mentions a variable that was eliminated later.
//! - [`AffineElimination::reconstruct`] evaluates those expressions, and the caller then checks the
//!   result against the **original** generators. `examples/cryptanalysis_ladder.rs` additionally
//!   re-runs the Poseidon permutation, which is independent of every step here.
//!
//! An elimination with no reconstruction would be a different mathematical problem reported as the
//! original one, which is the failure mode this whole `research` module exists to prevent.

use std::fmt::{Display, Formatter};

use crate::{FiniteField, Monomial, MultivariatePolynomial};

/// Why an affine elimination could not be performed or undone.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum LinearError {
    /// The target dimension does not match the number of variables that survive.
    WrongProjectedDimension { kept: usize, requested: usize },

    /// A point of the projected system had the wrong length.
    WrongPointLength { expected: usize, found: usize },
}

impl Display for LinearError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::WrongProjectedDimension { kept, requested } => write!(
                f,
                "{} variables survive the elimination, but the projection was asked for {}",
                kept, requested
            ),
            Self::WrongPointLength { expected, found } => write!(
                f,
                "a projected point must have {} coordinates, not {}",
                expected, found
            ),
        }
    }
}

impl std::error::Error for LinearError {}

/// One eliminated variable and the affine expression that determines it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Elimination<const N: usize, F: FiniteField> {
    /// The variable removed.
    pub variable: usize,

    /// An affine polynomial in the **kept** variables, equal to it.
    pub expression: MultivariatePolynomial<N, F>,
}

/// Variables determined by affine generators, and how to put them back.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AffineElimination<const N: usize, F: FiniteField> {
    /// In the order they were eliminated. Every expression mentions kept variables only.
    steps: Vec<Elimination<N, F>>,

    /// `kept[i]` is true if variable `i` survives.
    kept: [bool; N],
}

impl<const N: usize, F: FiniteField> AffineElimination<N, F> {
    /// The elimination that removes nothing.
    pub fn none() -> Self {
        Self {
            steps: Vec::new(),
            kept: [true; N],
        }
    }

    /// The eliminations performed, in order.
    pub fn steps(&self) -> &[Elimination<N, F>] {
        &self.steps
    }

    /// How many variables were eliminated.
    pub fn len(&self) -> usize {
        self.steps.len()
    }

    /// True if nothing was eliminated.
    pub fn is_empty(&self) -> bool {
        self.steps.is_empty()
    }

    /// The surviving variables, ascending.
    pub fn kept(&self) -> Vec<usize> {
        (0..N).filter(|index| self.kept[*index]).collect()
    }

    /// True if `variable` survives.
    pub fn keeps(&self, variable: usize) -> bool {
        self.kept[variable]
    }

    /// A full point of the original ring, from an assignment to the kept variables.
    ///
    /// `point` is indexed by the original variable numbering; the eliminated coordinates are
    /// **overwritten** with what the recorded expressions give, and the kept ones are left alone.
    /// Evaluated in reverse elimination order, which is not strictly necessary — every expression
    /// involves kept variables only — and is done anyway so that the invariant failing would show
    /// up as a wrong answer here rather than silently.
    pub fn reconstruct(&self, point: &[F; N]) -> [F; N] {
        let mut full = *point;
        for step in self.steps.iter().rev() {
            full[step.variable] = step.expression.eval(&full);
        }
        full
    }

    /// `system` at the smaller dimension `M`, with the eliminated variables gone from the ring.
    ///
    /// **This is the part that changes the matrices.** Substituting an affine generator makes the
    /// other generators smaller; it does not make the variable stop existing, so it keeps a column
    /// in every Macaulay matrix and a place in the monomial order. Projecting removes it.
    ///
    /// The kept variables are renumbered to `0..M` in ascending original order, so `kept()[j]` is
    /// the original index of the projected `x_j`.
    ///
    /// # Errors
    /// [`LinearError::WrongProjectedDimension`] unless `M` is exactly the number of survivors.
    /// Exact rather than "at least": a variable that appears in no generator is unconstrained, so a
    /// too-large `M` silently makes the ideal positive-dimensional.
    ///
    /// # Panics
    /// If a generator mentions an eliminated variable, which the sweep makes impossible.
    pub fn project<const M: usize>(
        &self,
        system: &[MultivariatePolynomial<N, F>],
    ) -> Result<Vec<MultivariatePolynomial<M, F>>, LinearError> {
        let kept = self.kept();
        if kept.len() != M {
            return Err(LinearError::WrongProjectedDimension {
                kept: kept.len(),
                requested: M,
            });
        }

        let mut position = [usize::MAX; N];
        for (new, old) in kept.iter().enumerate() {
            position[*old] = new;
        }

        Ok(system
            .iter()
            .map(|polynomial| {
                let terms: Vec<(Monomial<M>, F)> = polynomial
                    .terms()
                    .iter()
                    .map(|(monomial, coefficient)| {
                        let mut exponents = [0u32; M];
                        for (old, power) in monomial.exponents().iter().enumerate() {
                            if *power == 0 {
                                continue;
                            }
                            assert_ne!(
                                position[old],
                                usize::MAX,
                                "a reduced generator mentions the eliminated variable x{}",
                                old
                            );
                            exponents[position[old]] = *power;
                        }
                        (Monomial::new(&exponents), *coefficient)
                    })
                    .collect();
                MultivariatePolynomial::new(&terms)
            })
            .collect())
    }

    /// A point of the projected system, as a point of the original ring.
    ///
    /// Places each projected coordinate at its original index and then reconstructs the eliminated
    /// ones. The inverse of [`AffineElimination::project`] on points, and the only sound way to
    /// report a projected solve's answer.
    ///
    /// # Errors
    /// [`LinearError::WrongPointLength`] unless `M` is the number of survivors.
    pub fn lift<const M: usize>(&self, projected: &[F; M]) -> Result<[F; N], LinearError> {
        let kept = self.kept();
        if kept.len() != M {
            return Err(LinearError::WrongPointLength {
                expected: kept.len(),
                found: M,
            });
        }
        let mut point = [F::zero(); N];
        for (new, old) in kept.iter().enumerate() {
            point[*old] = projected[new];
        }
        Ok(self.reconstruct(&point))
    }
}

/// Eliminate every variable an affine generator determines, as far as the obvious sweep goes.
///
/// Returns the reduced generating set and the record needed to put the eliminated variables back.
/// The reduced set generates an ideal whose solutions, extended by
/// [`AffineElimination::reconstruct`], are exactly the original's.
///
/// # The sweep
///
/// Repeatedly: find the first affine generator that mentions a still-kept variable, solve it for
/// the **highest-indexed** such variable, substitute into every other generator **and** into every
/// expression recorded so far, and drop the generator. Over a field every nonzero coefficient is
/// invertible, so "mentions a variable" is the whole condition.
///
/// Highest-indexed rather than arbitrary because the layouts this is applied to put derived
/// variables last: a CICO instance is free inputs then S-box outputs, so eliminating from the top
/// removes S-box outputs and keeps the free inputs — which are the coordinates a recovered witness
/// is read from.
///
/// It is a sweep and not a complete affine reduction: an affine relation that only appears after
/// some nonlinear cancellation is not found, and nothing here looks for one. That is the scope
/// M22-E's §10.3 asks for — "transformations whose equivalence can be proved and whose inverse
/// mapping is straightforward".
///
/// A generator that substitutes to a nonzero constant means the system is inconsistent. It is kept
/// rather than dropped, so that the solver reports `{1}` as it would have; silently discarding it
/// would turn an unsatisfiable system into a satisfiable one.
pub fn eliminate_affine<const N: usize, F: FiniteField>(
    system: &[MultivariatePolynomial<N, F>],
) -> (Vec<MultivariatePolynomial<N, F>>, AffineElimination<N, F>) {
    let mut remaining: Vec<MultivariatePolynomial<N, F>> =
        system.iter().filter(|p| !p.is_zero()).cloned().collect();
    let mut record = AffineElimination::<N, F>::none();

    loop {
        // An affine generator that mentions a still-kept variable.
        let found = remaining
            .iter()
            .enumerate()
            .find_map(|(index, polynomial)| {
                if polynomial.degree() != 1 {
                    return None;
                }
                // The **highest-indexed** eligible variable. Deterministic, and chosen that way rather
                // than arbitrarily: every research layout in this module puts the variables a caller
                // reads off first — a CICO instance's free inputs, a specialization's targets — and the
                // derived ones last, so eliminating from the top removes derived variables and leaves
                // the interesting coordinates in the projected system.
                let variable = (0..N).rev().find(|variable| {
                    record.kept[*variable] && !coefficient_of(polynomial, *variable).is_zero()
                })?;
                Some((index, variable))
            });
        let Some((index, variable)) = found else {
            break;
        };

        let generator = remaining.remove(index);
        let expression = solve_for(&generator, variable);

        // Substitute into the other generators, and into the expressions already recorded, so that
        // every recorded expression mentions kept variables only.
        for polynomial in &mut remaining {
            *polynomial = substitute_polynomial(polynomial, variable, &expression);
        }
        for step in &mut record.steps {
            step.expression = substitute_polynomial(&step.expression, variable, &expression);
        }

        record.kept[variable] = false;
        record.steps.push(Elimination {
            variable,
            expression,
        });
    }

    (remaining, record)
}

/// The coefficient of `x_variable` in a polynomial, or zero.
fn coefficient_of<const N: usize, F: FiniteField>(
    polynomial: &MultivariatePolynomial<N, F>,
    variable: usize,
) -> F {
    let mut exponents = [0u32; N];
    exponents[variable] = 1;
    polynomial
        .terms()
        .get(&Monomial::new(&exponents))
        .copied()
        .unwrap_or_else(F::zero)
}

/// `x_variable` as an affine polynomial, from an affine `generator` whose coefficient there is
/// nonzero.
///
/// `generator = a * x_v + rest`, so `x_v = -rest / a`.
fn solve_for<const N: usize, F: FiniteField>(
    generator: &MultivariatePolynomial<N, F>,
    variable: usize,
) -> MultivariatePolynomial<N, F> {
    let mut exponents = [0u32; N];
    exponents[variable] = 1;
    let pivot = Monomial::new(&exponents);
    let scale = coefficient_of(generator, variable).inverse();

    let terms: Vec<(Monomial<N>, F)> = generator
        .terms()
        .iter()
        .filter(|(monomial, _)| **monomial != pivot)
        .map(|(monomial, coefficient)| (*monomial, -(*coefficient * scale)))
        .collect();
    MultivariatePolynomial::new(&terms)
}

/// `polynomial` with every occurrence of `x_variable` replaced by `expression`.
///
/// `expression` must not mention `x_variable`, which [`solve_for`] guarantees. Done term by term:
/// a term `c * m` with `x_variable^e | m` becomes `c * (m / x_variable^e) * expression^e`.
fn substitute_polynomial<const N: usize, F: FiniteField>(
    polynomial: &MultivariatePolynomial<N, F>,
    variable: usize,
    expression: &MultivariatePolynomial<N, F>,
) -> MultivariatePolynomial<N, F> {
    let mut total = MultivariatePolynomial::<N, F>::zero();
    for (monomial, coefficient) in polynomial.terms() {
        let power = monomial.exponents()[variable];
        if power == 0 {
            total += MultivariatePolynomial::new(&[(*monomial, *coefficient)]);
            continue;
        }

        let mut exponents = [0u32; N];
        exponents.copy_from_slice(monomial.exponents());
        exponents[variable] = 0;
        let rest = MultivariatePolynomial::new(&[(Monomial::new(&exponents), *coefficient)]);

        // `expression^power`, by repeated multiplication: `power` is a monomial exponent and is
        // small in every system this is applied to.
        let mut raised = MultivariatePolynomial::<N, F>::new(&[(Monomial::one(), F::new(1))]);
        for _ in 0..power {
            raised *= expression.clone();
        }
        total += rest * raised;
    }
    total
}

#[cfg(test)]
mod tests {
    use super::{eliminate_affine, AffineElimination, LinearError};
    use crate::{
        fields::Zp2147483647,
        grobner::{benchmark_systems::planted, f4, solve_one, transform::satisfies},
        FiniteField, MonomialOrder, MultivariatePolynomial, One, Zero,
    };
    use rand::{prelude::StdRng, SeedableRng};

    type F = Zp2147483647;
    const GREVLEX: MonomialOrder = MonomialOrder::GradedReverseLexicographic;

    fn parse<const N: usize>(s: &str, vars: [&str; N]) -> MultivariatePolynomial<N, F> {
        MultivariatePolynomial::parse(s, vars).expect("parses")
    }

    /// A system with no affine generator is returned unchanged.
    #[test]
    fn test_nothing_to_eliminate() {
        let system = vec![
            parse("x^2 + y^2 - 1", ["x", "y", "z"]),
            parse("x*y - z^2", ["x", "y", "z"]),
        ];
        let (reduced, record) = eliminate_affine(&system);
        assert_eq!(reduced, system);
        assert!(record.is_empty());
        assert_eq!(record.kept(), vec![0, 1, 2]);
    }

    /// One affine generator eliminates one variable, and the reconstruction puts it back.
    #[test]
    fn test_one_elimination() {
        // z = x + y, substituted into x*z - 1 giving x^2 + x*y - 1.
        let system = vec![
            parse("z - x - y", ["x", "y", "z"]),
            parse("x*z - 1", ["x", "y", "z"]),
        ];
        let (reduced, record) = eliminate_affine(&system);

        assert_eq!(record.len(), 1);
        assert_eq!(record.steps()[0].variable, 2);
        assert_eq!(record.kept(), vec![0, 1]);
        assert!(!record.keeps(2));
        assert_eq!(reduced.len(), 1);
        assert_eq!(reduced[0], parse("x^2 + x*y - 1", ["x", "y", "z"]));

        // A solution of the reduced system, extended, solves the original.
        let mut partial = [F::new(1), F::zero(), F::zero()];
        partial[1] = F::zero();
        // x = 1, y = 0 gives x^2 + x*y - 1 = 0.
        assert!(reduced[0].eval(&partial).is_zero());
        let full = record.reconstruct(&partial);
        assert_eq!(full[2], F::new(1), "z = x + y = 1");
        assert!(satisfies(&system, &full));
    }

    /// Several eliminations chain, and no recorded expression mentions an eliminated variable.
    ///
    /// The invariant the reconstruction rests on. Checked directly rather than through its
    /// consequences.
    #[test]
    fn test_chained_eliminations_mention_kept_variables_only() {
        // w = z + 1, z = y + x, so after both, w must be expressed as y + x + 1 and not as z + 1.
        let system = vec![
            parse("w - z - 1", ["x", "y", "z", "w"]),
            parse("z - y - x", ["x", "y", "z", "w"]),
            parse("x*w - y^2", ["x", "y", "z", "w"]),
        ];
        let (reduced, record) = eliminate_affine(&system);

        assert_eq!(record.len(), 2);
        assert_eq!(record.kept(), vec![0, 1]);
        for step in record.steps() {
            for monomial in step.expression.terms().keys() {
                for eliminated in record.steps().iter().map(|other| other.variable) {
                    assert_eq!(
                        monomial.exponents()[eliminated],
                        0,
                        "the expression for x{} mentions the eliminated x{}",
                        step.variable,
                        eliminated
                    );
                }
            }
        }
        assert_eq!(reduced.len(), 1, "two affine generators were consumed");
    }

    /// A projected solution, reconstructed, satisfies the original system — on planted systems
    /// whose solutions are known.
    ///
    /// The end-to-end property. The reduced system is solved from scratch, so nothing about the
    /// elimination is trusted; the point is then evaluated against the **original** generators.
    #[test]
    fn test_a_reduced_solution_reconstructs() {
        let point = [F::new(7), F::new(11), F::new(13)];
        let mut system = planted::<3, F>(&point);
        // An affine generator that the plant satisfies: z - 13.
        system.push(parse("z - 13", ["x", "y", "z"]));
        assert!(satisfies(&system, &point));

        let (reduced, record) = eliminate_affine(&system);
        assert_eq!(record.len(), 1, "one affine generator");
        assert!(!reduced.is_empty());

        // The reduced system still lives in three variables, and the eliminated one now appears in
        // no generator — so it is *unconstrained* and the ideal is positive-dimensional. That is the
        // same trap `Specialization::apply` documents, and the reason `project` exists: solving has
        // to happen at the smaller dimension.
        assert_eq!(
            crate::grobner::classify_ideal(&f4(&reduced, GREVLEX).unwrap(), GREVLEX),
            crate::grobner::IdealClass::PositiveDimensional,
            "substitution alone leaves a free coordinate"
        );

        let projected = record.project::<2>(&reduced).expect("two survive");
        let mut rng = StdRng::seed_from_u64(1);
        let solution = solve_one(&projected, &mut rng)
            .expect("zero-dimensional after projection")
            .expect("the plant survives the elimination");
        let full = record.lift::<2>(&solution).expect("two survive");
        assert!(
            satisfies(&system, &full),
            "the lifted point does not satisfy the original system"
        );
    }

    /// Elimination does not change the ideal: the reduced system plus the affine relations has the
    /// same Gröbner basis as the original.
    ///
    /// Checked by adding the recorded relations back as `x_v - expression` and comparing reduced
    /// bases, which are unique for an ideal and an order.
    #[test]
    fn test_elimination_preserves_the_ideal() {
        let cases: Vec<Vec<&str>> = vec![
            vec!["z - x - y", "x*z - 1"],
            vec!["w - z - 1", "z - y - x", "x*w - y^2"],
            vec!["x + y + z + w", "x*y - z*w", "x^2 - 1"],
            vec!["2*x - 3*y + 1", "y^2 + x*z - 5", "z^2 - w", "w - 2"],
        ];

        for strings in cases {
            let system: Vec<MultivariatePolynomial<4, F>> = strings
                .iter()
                .map(|s| parse(s, ["x", "y", "z", "w"]))
                .collect();
            let reference = f4(&system, GREVLEX).expect("within limits");

            let (reduced, record) = eliminate_affine(&system);
            let mut restored = reduced.clone();
            for step in record.steps() {
                let mut exponents = [0u32; 4];
                exponents[step.variable] = 1;
                restored.push(
                    MultivariatePolynomial::new(&[(crate::Monomial::new(&exponents), F::one())])
                        - step.expression.clone(),
                );
            }

            assert_eq!(
                f4(&restored, GREVLEX).expect("within limits"),
                reference,
                "{:?}: the elimination changed the ideal",
                strings
            );
        }
    }

    /// An inconsistent system stays inconsistent: the contradictory constant is kept.
    #[test]
    fn test_an_inconsistent_system_stays_inconsistent() {
        // x = 1 and x = 2 at once.
        let system = vec![
            parse("x - 1", ["x", "y"]),
            parse("x - 2", ["x", "y"]),
            parse("y^2 - 1", ["x", "y"]),
        ];
        let (reduced, record) = eliminate_affine(&system);
        assert_eq!(record.len(), 1);
        // Substituting x = 1 into x - 2 gives the nonzero constant -1, which must survive.
        assert!(
            reduced.iter().any(|p| p.is_constant() && !p.is_zero()),
            "the contradiction was dropped: {:?}",
            reduced
        );
        assert_eq!(
            f4(&reduced, GREVLEX).expect("within limits").len(),
            1,
            "an inconsistent system has basis {{1}}"
        );
    }

    /// Substituting into a higher power of the eliminated variable is handled.
    #[test]
    fn test_substitution_into_a_power() {
        // y = x + 1, substituted into y^3 - 8.
        let system = vec![parse("y - x - 1", ["x", "y"]), parse("y^3 - 8", ["x", "y"])];
        let (reduced, record) = eliminate_affine(&system);
        assert_eq!(record.len(), 1);
        assert_eq!(reduced.len(), 1);
        // (x + 1)^3 - 8 = x^3 + 3x^2 + 3x - 7.
        assert_eq!(
            reduced[0],
            parse("x^3 + 3*x^2 + 3*x - 7", ["x", "y"]),
            "got {}",
            reduced[0]
        );
    }

    /// Projection removes the eliminated variables from the ring, and lifting puts them back.
    ///
    /// The round trip that licenses a projected solve. The projected system is solved from scratch
    /// at the smaller dimension, and its point is checked against the **original** generators.
    #[test]
    fn test_projection_and_lifting() {
        // Four variables, two affine generators, so two survive.
        let system = vec![
            parse("w - z - 1", ["x", "y", "z", "w"]),
            parse("z - y - x", ["x", "y", "z", "w"]),
            parse("x*w - y^2 - 3", ["x", "y", "z", "w"]),
            parse("x^2 + y^2 - 5", ["x", "y", "z", "w"]),
        ];
        let (reduced, record) = eliminate_affine(&system);
        assert_eq!(record.kept(), vec![0, 1]);

        let projected = record
            .project::<2>(&reduced)
            .expect("two variables survive");
        assert_eq!(projected.len(), reduced.len());
        // Every projected generator is a genuine two-variable polynomial.
        for polynomial in &projected {
            assert!(!polynomial.is_zero());
        }

        // The wrong target dimension is refused rather than padded.
        assert_eq!(
            record.project::<3>(&reduced),
            Err(LinearError::WrongProjectedDimension {
                kept: 2,
                requested: 3
            })
        );

        let mut rng = StdRng::seed_from_u64(7);
        match solve_one(&projected, &mut rng).expect("zero-dimensional") {
            Some(point) => {
                let full = record.lift::<2>(&point).expect("two survivors");
                assert!(
                    satisfies(&system, &full),
                    "the lifted point does not satisfy the original system"
                );
            }
            None => {
                // No base-field point is a legitimate answer, and then there is nothing to lift.
                // Asserted explicitly so a silently empty test cannot pass for a passing one.
                let mut rng = StdRng::seed_from_u64(7);
                assert!(solve_one(&system, &mut rng)
                    .expect("zero-dimensional")
                    .is_none());
            }
        }
    }

    /// Projecting a system whose solution is known recovers exactly that solution.
    #[test]
    fn test_projection_preserves_a_planted_point() {
        let point = [F::new(7), F::new(11), F::new(13)];
        let mut system = planted::<3, F>(&point);
        system.push(parse("z - 13", ["x", "y", "z"]));

        let (reduced, record) = eliminate_affine(&system);
        let projected = record.project::<2>(&reduced).expect("two survive");

        // The plant, restricted to the kept coordinates, solves the projected system.
        let restricted = [point[0], point[1]];
        for polynomial in &projected {
            assert!(
                polynomial.eval(&restricted).is_zero(),
                "the plant does not solve the projected {}",
                polynomial
            );
        }
        // And lifting it gives the plant back, including the eliminated coordinate.
        assert_eq!(record.lift::<2>(&restricted).expect("two survive"), point);
    }

    /// The empty elimination reconstructs the point it was given.
    #[test]
    fn test_reconstruct_of_nothing() {
        let record = AffineElimination::<3, F>::none();
        let point = [F::new(1), F::new(2), F::new(3)];
        assert_eq!(record.reconstruct(&point), point);
        assert_eq!(record.kept(), vec![0, 1, 2]);
    }
}
