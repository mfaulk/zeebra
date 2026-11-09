//! Relabelling the variables of a system, and getting a solution back.
//!
//! A monomial order ranks monomials by their exponent vectors, so **which variable is `x_0`
//! changes the Gröbner basis**, the matrices, and the cost — while changing nothing about the
//! mathematical problem. That makes variable order a free parameter of any solving experiment.
//!
//! The whole content of this module is making that exploration *honest*. A permutation of variables
//! is a ring isomorphism, so a point of the relabelled system corresponds to a point of the
//! original — but only if the correspondence is applied, and applied the right way round. An
//! inverse permutation used in place of its forward form produces a point that satisfies nothing,
//! and on a system whose solution is not known in advance that is indistinguishable from a solver
//! that found nothing.
//!
//! So [`VariableOrder`] is constructed only from a checked bijection, [`VariableOrder::apply`] is
//! the only way to relabel a system, and [`VariableOrder::recover`] is the only way to map a point
//! back. The tests assert the round trip on systems whose solutions are known.

use std::fmt::{Display, Formatter};

use crate::{FiniteField, Monomial, MultivariatePolynomial};

/// Why a variable order could not be built.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ReorderError {
    /// The permutation is not a bijection of `0..N`.
    ///
    /// Carries the offending entry, or `None` when an index simply never appeared. Both are the
    /// same defect — a map that is not a bijection is not a relabelling — and both are rejected
    /// rather than tolerated, because a non-bijective "permutation" silently identifies two
    /// variables and changes the problem.
    NotAPermutation {
        length: usize,
        offender: Option<usize>,
    },
}

impl Display for ReorderError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NotAPermutation { length, offender } => match offender {
                Some(index) => write!(
                    f,
                    "the given map is not a permutation of 0..{}: {} is out of range or repeated",
                    length, index
                ),
                None => write!(
                    f,
                    "the given map is not a permutation of 0..{}: some index is missing",
                    length
                ),
            },
        }
    }
}

impl std::error::Error for ReorderError {}

/// A bijective relabelling of the `N` variables.
///
/// Stored as `sources`, where `sources[j]` is the **old** index that becomes the new `x_j`. That
/// direction is the one `apply` needs, and naming it rather than leaving it implicit is the point:
/// the other reading — "variable `j` moves to position `sources[j]`" — is the inverse, and the two
/// differ on every permutation that is not an involution.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VariableOrder<const N: usize> {
    /// `sources[new] = old`.
    sources: [usize; N],

    /// `targets[old] = new`, the inverse. Stored rather than searched, so that `recover` is linear.
    targets: [usize; N],

    /// A short name, for a table column.
    name: String,
}

impl<const N: usize> VariableOrder<N> {
    /// The order whose new `x_j` is the old `x_{sources[j]}`.
    ///
    /// # Errors
    /// [`ReorderError::NotAPermutation`] unless `sources` is a bijection of `0..N`.
    pub fn new(name: impl Into<String>, sources: &[usize]) -> Result<Self, ReorderError> {
        if sources.len() != N {
            return Err(ReorderError::NotAPermutation {
                length: N,
                offender: None,
            });
        }

        let mut targets = [usize::MAX; N];
        for (new, old) in sources.iter().enumerate() {
            if *old >= N || targets[*old] != usize::MAX {
                return Err(ReorderError::NotAPermutation {
                    length: N,
                    offender: Some(*old),
                });
            }
            targets[*old] = new;
        }
        // Surjectivity follows from injectivity on a finite set of the same size, but the check is
        // cheap and the failure is silent otherwise.
        if targets.contains(&usize::MAX) {
            return Err(ReorderError::NotAPermutation {
                length: N,
                offender: None,
            });
        }

        let mut fixed = [0usize; N];
        fixed.copy_from_slice(sources);
        Ok(Self {
            sources: fixed,
            targets,
            name: name.into(),
        })
    }

    /// The order that changes nothing.
    pub fn identity() -> Self {
        let mut sources = [0usize; N];
        for (index, slot) in sources.iter_mut().enumerate() {
            *slot = index;
        }
        Self::new("identity", &sources).expect("the identity is a permutation")
    }

    /// The order that reverses the variables.
    pub fn reversed() -> Self {
        let sources: Vec<usize> = (0..N).rev().collect();
        Self::new("reversed", &sources).expect("reversal is a permutation")
    }

    /// `prefix` first, in the order given, then every remaining index ascending.
    ///
    /// For moving a chosen set of variables to the front — the free inputs of a parametrized system, or
    /// the variables a specialization is going to fix.
    ///
    /// # Errors
    /// [`ReorderError::NotAPermutation`] if `prefix` repeats an index or names one out of range.
    pub fn prefixed(name: impl Into<String>, prefix: &[usize]) -> Result<Self, ReorderError> {
        let mut seen = [false; N];
        let mut sources = Vec::with_capacity(N);
        for index in prefix {
            if *index >= N || seen[*index] {
                return Err(ReorderError::NotAPermutation {
                    length: N,
                    offender: Some(*index),
                });
            }
            seen[*index] = true;
            sources.push(*index);
        }
        for index in 0..N {
            if !seen[index] {
                sources.push(index);
            }
        }
        Self::new(name, &sources)
    }

    /// The order's name.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// `sources[new] = old`.
    pub fn sources(&self) -> &[usize; N] {
        &self.sources
    }

    /// True if nothing moves.
    pub fn is_identity(&self) -> bool {
        (0..N).all(|index| self.sources[index] == index)
    }

    /// `system` with its variables relabelled.
    ///
    /// The new system's `x_j` plays the role the old `x_{sources[j]}` did, so the two systems are
    /// the same system up to a ring isomorphism: they have the same number of generators, each with
    /// the same coefficients on corresponding monomials, and their solution sets correspond under
    /// [`VariableOrder::recover`].
    pub fn apply<F: FiniteField>(
        &self,
        system: &[MultivariatePolynomial<N, F>],
    ) -> Vec<MultivariatePolynomial<N, F>> {
        system
            .iter()
            .map(|polynomial| {
                let terms: Vec<(Monomial<N>, F)> = polynomial
                    .terms()
                    .iter()
                    .map(|(monomial, coefficient)| {
                        let old = monomial.exponents();
                        let mut new = [0u32; N];
                        for (position, slot) in new.iter_mut().enumerate() {
                            *slot = old[self.sources[position]];
                        }
                        (Monomial::new(&new), *coefficient)
                    })
                    .collect();
                MultivariatePolynomial::new(&terms)
            })
            .collect()
    }

    /// A point of the relabelled system, as a point of the original.
    ///
    /// The inverse of [`VariableOrder::apply`] on points: the relabelled system's `x_j` was the
    /// original's `x_{sources[j]}`, so the original's coordinate `sources[j]` takes the relabelled
    /// point's coordinate `j`.
    pub fn recover<F: FiniteField>(&self, point: &[F; N]) -> [F; N] {
        let mut original = *point;
        for (new, old) in self.sources.iter().enumerate() {
            original[*old] = point[new];
        }
        original
    }

    /// A point of the original system, as a point of the relabelled one.
    ///
    /// The forward direction, for checking the round trip and for mapping a known plant into the
    /// relabelled coordinates.
    pub fn forward<F: FiniteField>(&self, point: &[F; N]) -> [F; N] {
        let mut relabelled = *point;
        for (old, new) in self.targets.iter().enumerate() {
            relabelled[*new] = point[old];
        }
        relabelled
    }

    /// The inverse order, which undoes this one.
    pub fn inverse(&self) -> Self {
        Self {
            sources: self.targets,
            targets: self.sources,
            name: format!("{}⁻¹", self.name),
        }
    }
}

impl<const N: usize> Display for VariableOrder<N> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} {:?}", self.name, self.sources)
    }
}

#[cfg(test)]
mod tests {
    use super::{ReorderError, VariableOrder};
    use crate::{
        fields::Zp2147483647,
        grobner::{benchmark_systems::planted, f4, transform::satisfies},
        FiniteField, MonomialOrder, MultivariatePolynomial,
    };

    type F = Zp2147483647;
    const GREVLEX: MonomialOrder = MonomialOrder::GradedReverseLexicographic;

    fn parse<const N: usize>(s: &str, vars: [&str; N]) -> MultivariatePolynomial<N, F> {
        MultivariatePolynomial::parse(s, vars).expect("parses")
    }

    /// A map that repeats an index, names one out of range, or is the wrong length is rejected.
    #[test]
    fn test_only_a_bijection_is_accepted() {
        assert!(VariableOrder::<3>::new("ok", &[2, 0, 1]).is_ok());
        assert_eq!(
            VariableOrder::<3>::new("repeat", &[0, 0, 1]),
            Err(ReorderError::NotAPermutation {
                length: 3,
                offender: Some(0)
            })
        );
        assert_eq!(
            VariableOrder::<3>::new("range", &[0, 1, 3]),
            Err(ReorderError::NotAPermutation {
                length: 3,
                offender: Some(3)
            })
        );
        assert_eq!(
            VariableOrder::<3>::new("short", &[0, 1]),
            Err(ReorderError::NotAPermutation {
                length: 3,
                offender: None
            })
        );
    }

    /// The identity relabels nothing.
    #[test]
    fn test_the_identity_is_inert() {
        let order = VariableOrder::<3>::identity();
        assert!(order.is_identity());
        let system = vec![
            parse("x^2 + y*z - 1", ["x", "y", "z"]),
            parse("x*y - z", ["x", "y", "z"]),
        ];
        assert_eq!(order.apply(&system), system);
    }

    /// Relabelling moves the exponents the way `sources` says, on a hand-checkable case.
    #[test]
    fn test_apply_moves_the_exponents() {
        // sources = [2, 0, 1]: new x_0 is old x_2, new x_1 is old x_0, new x_2 is old x_1.
        let order = VariableOrder::<3>::new("cycle", &[2, 0, 1]).expect("a permutation");
        // x^2 * y, i.e. exponents [2, 1, 0] in the old labels. New exponents: new[0] = old[2] = 0,
        // new[1] = old[0] = 2, new[2] = old[1] = 1 — so y^2 * z.
        let system = vec![parse("x^2*y", ["x", "y", "z"])];
        assert_eq!(order.apply(&system), vec![parse("y^2*z", ["x", "y", "z"])]);
    }

    /// `forward` and `recover` are inverse on points, and `inverse` undoes `apply` on systems.
    #[test]
    fn test_the_round_trip() {
        let order = VariableOrder::<4>::new("shuffle", &[3, 1, 0, 2]).expect("a permutation");
        let point = [F::new(10), F::new(20), F::new(30), F::new(40)];

        assert_eq!(order.recover(&order.forward(&point)), point);
        assert_eq!(order.forward(&order.recover(&point)), point);

        let system = vec![
            parse("x^2 + y - 1", ["x", "y", "z", "w"]),
            parse("z*w - x", ["x", "y", "z", "w"]),
        ];
        assert_eq!(order.inverse().apply(&order.apply(&system)), system);
    }

    /// A relabelled system's solutions are the original's, mapped back — on a planted system whose
    /// solution is known.
    ///
    /// The property the whole module exists for. The relabelled system is solved from scratch; its
    /// point is mapped back with `recover`; and the recovered point is evaluated against the
    /// **original** generators, so no step of the relabelling is trusted.
    #[test]
    fn test_a_relabelled_solution_recovers() {
        let point = [F::new(7), F::new(11), F::new(13)];
        let system = planted::<3, F>(&point);
        assert!(satisfies(&system, &point));

        for sources in [[0, 1, 2], [2, 1, 0], [1, 2, 0], [2, 0, 1]] {
            let order = VariableOrder::<3>::new("case", &sources).expect("a permutation");
            let relabelled = order.apply(&system);

            // The plant, in the relabelled coordinates, solves the relabelled system.
            let moved = order.forward(&point);
            assert!(
                satisfies(&relabelled, &moved),
                "{:?}: the plant does not solve the relabelled system",
                sources
            );

            // And mapping it back gives the original plant.
            assert_eq!(order.recover(&moved), point, "{:?}", sources);
        }
    }

    /// Relabelling changes the Gröbner basis without changing the ideal's structure.
    ///
    /// The reason variable order is worth exploring at all: the computation differs. Asserted both
    /// ways — the bases are generally *not* equal, and the quotient dimension is, because that is
    /// an invariant of the ideal under a ring isomorphism.
    #[test]
    fn test_relabelling_changes_the_basis_but_not_the_dimension() {
        use crate::grobner::fglm::QuotientBasis;

        let point = [F::new(3), F::new(5), F::new(8), F::new(13)];
        let system = planted::<4, F>(&point);
        let reference = f4(&system, GREVLEX).expect("within limits");
        let dimension = QuotientBasis::new(&reference, GREVLEX, usize::MAX)
            .expect("zero-dimensional")
            .dimension();

        let mut any_differed = false;
        for sources in [[1, 0, 3, 2], [3, 2, 1, 0], [2, 3, 0, 1]] {
            let order = VariableOrder::<4>::new("case", &sources).expect("a permutation");
            let basis = f4(&order.apply(&system), GREVLEX).expect("within limits");

            assert_eq!(
                QuotientBasis::new(&basis, GREVLEX, usize::MAX)
                    .expect("zero-dimensional")
                    .dimension(),
                dimension,
                "{:?}: the quotient dimension is an isomorphism invariant",
                sources
            );
            if basis != reference {
                any_differed = true;
            }
        }
        assert!(
            any_differed,
            "no relabelling changed the basis, so the experiment measures nothing"
        );
    }

    /// `prefixed` puts the named variables first and keeps the rest ascending.
    #[test]
    fn test_prefixed() {
        let order = VariableOrder::<5>::prefixed("front", &[3, 1]).expect("a permutation");
        assert_eq!(order.sources(), &[3, 1, 0, 2, 4]);
        assert!(VariableOrder::<5>::prefixed("dup", &[1, 1]).is_err());
        assert!(VariableOrder::<5>::prefixed("range", &[7]).is_err());
    }

    /// Reversal is its own inverse.
    #[test]
    fn test_reversed() {
        let order = VariableOrder::<4>::reversed();
        assert_eq!(order.sources(), &[3, 2, 1, 0]);
        let point = [F::new(1), F::new(2), F::new(3), F::new(4)];
        assert_eq!(order.recover(&point), order.forward(&point));
    }
}
