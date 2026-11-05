//! What can be said about a polynomial system without computing a Gröbner basis.
//!
//! Every figure here is a property of the *input*, costs one pass over its terms, and is a
//! diagnostic. **None of them bounds the quotient dimension or the solving degree**, and the one
//! mathematical conclusion in the struct is [`SystemShape::constant_contradiction`], which is
//! sound because a nonzero constant generator puts 1 in the ideal by itself.
//!
//! The temptation this module exists to resist is inferring dimension from counts. cyclic-4 is
//! four equations in four variables and is positive-dimensional; `generators == variables` licenses
//! nothing, and §3.1 of `docs/MILESTONE-RESOURCE-AWARE-CRYPTANALYSIS.md` is the longer argument.

use std::collections::HashSet;

use crate::{FiniteField, MultivariatePolynomial};

/// The shape of a polynomial system, as read off its terms.
///
/// Diagnostics for a human and inputs to a planner's *cheap* first pass. See the module docs for
/// what none of this is.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct SystemShape {
    /// Variables in the ring, which is `N` and not the number actually used.
    pub variables: usize,

    /// Generators supplied, including any zero ones.
    pub generators: usize,

    /// Of those, generators that are identically zero.
    ///
    /// Reported rather than silently dropped: a system whose generators are mostly zero is
    /// usually a construction bug, and every other count here excludes them.
    pub zero_generators: usize,

    /// Nonzero terms, summed over the nonzero generators.
    pub terms: usize,

    /// The largest total degree of any nonzero generator. Zero if there are none.
    pub max_degree: u64,

    /// `(degree, generators of that degree)`, ascending by degree, nonzero generators only.
    pub degree_histogram: Vec<(u64, usize)>,

    /// Per variable, the number of nonzero generators it appears in with a positive exponent.
    ///
    /// Length `N`. A zero entry means the variable is not constrained by any equation, which is
    /// the clearest signal a system is underdetermined — though **not a proof**, since a variable
    /// absent from the generators is genuinely free and one present in all of them may still be.
    pub occurrences: Vec<usize>,

    /// Nonzero generators of total degree exactly one.
    pub linear_generators: usize,

    /// Nonzero generators of total degree exactly two.
    ///
    /// The count that says whether an instance is an MQ system in the usual sense.
    pub quadratic_generators: usize,

    /// Nonconstant generators involving exactly one variable.
    ///
    /// The explicit single-variable equations: each one pins its variable to the roots of a
    /// univariate polynomial without any elimination.
    pub univariate_generators: usize,

    /// Variables that have at least one univariate generator of their own.
    ///
    /// A system where this is `N` is triangular in the strongest sense and needs no Gröbner basis
    /// at all. Below `N` it says how much of the system is already solved.
    pub variables_with_univariate_generator: usize,

    /// Distinct unordered variable pairs that occur together in some monomial.
    ///
    /// The interaction structure, which is what decides how much elimination couples. At most
    /// `N (N - 1) / 2`; see [`Self::interaction_density`].
    pub interaction_pairs: usize,

    /// Some generator is a nonzero constant, so `1` is in the ideal.
    ///
    /// **The only sound mathematical conclusion in this struct.** It needs no basis: a unit is a
    /// unit.
    pub constant_contradiction: bool,
}

impl SystemShape {
    /// Occurring variable pairs as a fraction of all `N (N - 1) / 2` of them.
    ///
    /// Zero for `N < 2`. One means every pair of variables is coupled somewhere.
    pub fn interaction_density(&self) -> f64 {
        let possible = self
            .variables
            .saturating_mul(self.variables.saturating_sub(1))
            / 2;
        if possible == 0 {
            0.0
        } else {
            self.interaction_pairs as f64 / possible as f64
        }
    }

    /// Mean nonzero terms per nonzero generator. Zero if there are none.
    pub fn mean_terms_per_generator(&self) -> f64 {
        let nonzero = self.generators - self.zero_generators;
        if nonzero == 0 {
            0.0
        } else {
            self.terms as f64 / nonzero as f64
        }
    }

    /// Variables ranked by how few generators constrain them, least-constrained first.
    ///
    /// A **ranking, not a recommendation**, and in particular not a count: how many variables to
    /// fix is a decision the caller makes and records, never one inferred from the number of
    /// equations. Ties break by index, so the order is deterministic.
    ///
    /// The ranking is a heuristic about where structure is cheapest to give up — a variable in
    /// few equations is the least likely to be pinned by them — and nothing about it is proved.
    pub fn specialization_candidates(&self) -> Vec<usize> {
        let mut order: Vec<usize> = (0..self.occurrences.len()).collect();
        order.sort_by_key(|&i| (self.occurrences[i], i));
        order
    }
}

/// Read the shape of `system` off its terms.
///
/// One pass over every term of every generator. Computes no basis, and decides nothing about the
/// ideal beyond [`SystemShape::constant_contradiction`].
pub fn analyze<const N: usize, F: FiniteField>(
    system: &[MultivariatePolynomial<N, F>],
) -> SystemShape {
    let mut shape = SystemShape {
        variables: N,
        generators: system.len(),
        occurrences: vec![0; N],
        ..SystemShape::default()
    };

    let mut degrees: Vec<u64> = Vec::new();
    let mut pairs: HashSet<(usize, usize)> = HashSet::new();
    let mut univariate_in: HashSet<usize> = HashSet::new();

    for p in system {
        if p.is_zero() {
            shape.zero_generators += 1;
            continue;
        }
        if p.is_constant() {
            // Nonzero and constant: a unit, so the ideal is the whole ring.
            shape.constant_contradiction = true;
        }

        shape.terms += p.terms().len();
        let degree = p.degree();
        shape.max_degree = shape.max_degree.max(degree);
        degrees.push(degree);
        match degree {
            1 => shape.linear_generators += 1,
            2 => shape.quadratic_generators += 1,
            _ => {}
        }

        // Which variables this generator uses, and which pairs it couples. Pairs are collected per
        // *monomial* rather than per generator: two variables in different terms of one polynomial
        // are not multiplied together by it, and it is the products that drive fill-in.
        let mut used: HashSet<usize> = HashSet::new();
        for monomial in p.terms().keys() {
            let present: Vec<usize> = monomial
                .exponents()
                .iter()
                .enumerate()
                .filter(|(_, &e)| e > 0)
                .map(|(i, _)| i)
                .collect();
            used.extend(present.iter().copied());
            for (a, &i) in present.iter().enumerate() {
                for &j in &present[a + 1..] {
                    pairs.insert((i, j));
                }
            }
        }
        for &i in &used {
            shape.occurrences[i] += 1;
        }
        if used.len() == 1 {
            shape.univariate_generators += 1;
            univariate_in.extend(used.iter().copied());
        }
    }

    shape.interaction_pairs = pairs.len();
    shape.variables_with_univariate_generator = univariate_in.len();

    degrees.sort_unstable();
    for degree in degrees {
        match shape.degree_histogram.last_mut() {
            Some((d, count)) if *d == degree => *count += 1,
            _ => shape.degree_histogram.push((degree, 1)),
        }
    }

    shape
}

#[cfg(test)]
mod tests {
    use super::{analyze, SystemShape};
    use crate::{
        fields::Zp2147483647,
        grobner::{
            benchmark_systems::{cyclic, katsura},
            classify_ideal, f4,
        },
        MonomialOrder, MultivariatePolynomial,
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

    /// Counts, degrees and the degree histogram come off the terms as given.
    #[test]
    fn test_counts_and_degrees() {
        let shape = analyze(&parse(&["x^2*y + z", "y - 1", "z^3"], ["x", "y", "z"]));
        assert_eq!(shape.variables, 3);
        assert_eq!(shape.generators, 3);
        assert_eq!(shape.zero_generators, 0);
        assert_eq!(shape.terms, 2 + 2 + 1);
        assert_eq!(shape.max_degree, 3);
        // One generator each of degree 1, 3 and 3 — ascending, with equal degrees merged.
        assert_eq!(shape.degree_histogram, vec![(1, 1), (3, 2)]);
        assert_eq!(shape.linear_generators, 1);
        assert_eq!(shape.quadratic_generators, 0);
    }

    /// Zero generators are counted and then excluded from every other figure.
    #[test]
    fn test_zero_generators_are_reported_not_hidden() {
        let mut system = parse(&["x + y"], ["x", "y"]);
        system.push(MultivariatePolynomial::zero());
        let shape = analyze(&system);
        assert_eq!(shape.generators, 2);
        assert_eq!(shape.zero_generators, 1);
        assert_eq!(shape.terms, 2, "the zero generator contributes no terms");
        assert_eq!(shape.degree_histogram, vec![(1, 1)]);
        assert_eq!(shape.mean_terms_per_generator(), 2.0);
    }

    /// A nonzero constant generator is reported, and it is the one sound conclusion here.
    #[test]
    fn test_a_constant_generator_is_a_contradiction() {
        let contradictory = parse(&["x^2 - y", "1"], ["x", "y"]);
        assert!(analyze(&contradictory).constant_contradiction);

        // And the sound part: F4 agrees, returning the unit ideal.
        let basis = f4(&contradictory, MonomialOrder::Lexicographic).expect("within limits");
        assert!(basis.iter().any(|p| p.is_constant() && !p.is_zero()));

        // A system without one is not flagged, and in particular `0` is not a unit.
        let mut ordinary = parse(&["x^2 - y"], ["x", "y"]);
        ordinary.push(MultivariatePolynomial::zero());
        assert!(!analyze(&ordinary).constant_contradiction);
    }

    /// Occurrence counts are per generator, and an absent variable scores zero.
    #[test]
    fn test_occurrences_and_the_specialization_ranking() {
        //        x: both    y: one    z: none
        let shape = analyze(&parse(&["x*y + 1", "x^2"], ["x", "y", "z"]));
        assert_eq!(shape.occurrences, vec![2, 1, 0]);
        // Least-constrained first: z (0), then y (1), then x (2).
        assert_eq!(shape.specialization_candidates(), vec![2, 1, 0]);
    }

    /// The ranking is deterministic, breaking ties by index.
    #[test]
    fn test_the_specialization_ranking_breaks_ties_by_index() {
        let shape = analyze(&parse(&["x + y + z"], ["x", "y", "z"]));
        assert_eq!(shape.occurrences, vec![1, 1, 1]);
        assert_eq!(shape.specialization_candidates(), vec![0, 1, 2]);
    }

    /// Interaction pairs are collected per monomial, not per polynomial.
    ///
    /// `x + y` does not multiply x by y, so it couples nothing; `x*y` does.
    #[test]
    fn test_interaction_pairs_are_per_monomial() {
        assert_eq!(analyze(&parse(&["x + y"], ["x", "y"])).interaction_pairs, 0);
        assert_eq!(analyze(&parse(&["x*y"], ["x", "y"])).interaction_pairs, 1);
        // x*y*z contributes all three pairs from one monomial.
        let shape = analyze(&parse(&["x*y*z"], ["x", "y", "z"]));
        assert_eq!(shape.interaction_pairs, 3);
        assert_eq!(shape.interaction_density(), 1.0);
    }

    /// Univariate generators are counted, and so are the variables they pin.
    #[test]
    fn test_univariate_generators_and_triangularity() {
        // Triangular in the strongest sense: one univariate generator per variable.
        let shape = analyze(&parse(&["x^2 - 1", "y^3 - 2"], ["x", "y"]));
        assert_eq!(shape.univariate_generators, 2);
        assert_eq!(shape.variables_with_univariate_generator, 2);
        assert_eq!(shape.variables_with_univariate_generator, shape.variables);

        // Two univariate generators in the *same* variable pin one variable, not two.
        let shape = analyze(&parse(&["x^2 - 1", "x^3 - 1"], ["x", "y"]));
        assert_eq!(shape.univariate_generators, 2);
        assert_eq!(shape.variables_with_univariate_generator, 1);

        // A constant is not univariate: it involves no variable at all.
        let shape = analyze(&parse(&["1"], ["x", "y"]));
        assert_eq!(shape.univariate_generators, 0);
    }

    /// `generators == variables` is not a dimension claim, and cyclic-4 is why.
    ///
    /// The committed counterexample. Four equations in four variables, structurally
    /// indistinguishable by every figure here from katsura-4, which is zero-dimensional — and
    /// cyclic-4 is not. Nothing in `SystemShape` may be read as bounding the quotient dimension.
    #[test]
    fn test_no_structural_figure_decides_dimension() {
        let positive = cyclic::<4, F>();
        let finite = katsura::<4, F>();

        let (p, k) = (analyze(&positive), analyze(&finite));
        assert_eq!(p.generators, p.variables);
        assert_eq!(k.generators, k.variables);
        assert_eq!(p.generators, k.generators);
        assert_eq!(p.variables, k.variables);
        assert!(!p.constant_contradiction && !k.constant_contradiction);
        assert_eq!(p.occurrences, vec![4, 4, 4, 4]);
        assert_eq!(k.occurrences, vec![4, 4, 4, 4]);

        // Every variable is constrained by every equation in both, and the dimensions differ.
        let grevlex = MonomialOrder::GradedReverseLexicographic;
        let positive_basis = f4(&positive, grevlex).expect("within limits");
        let finite_basis = f4(&finite, grevlex).expect("within limits");
        assert!(
            !classify_ideal(&positive_basis, grevlex).is_finite_dimensional(),
            "cyclic-4 is positive-dimensional"
        );
        assert!(
            classify_ideal(&finite_basis, grevlex).is_finite_dimensional(),
            "katsura-4 is zero-dimensional"
        );
    }

    /// The empty system is described, not panicked on.
    #[test]
    fn test_the_empty_system() {
        let shape = analyze::<3, F>(&[]);
        assert_eq!(
            shape,
            SystemShape {
                variables: 3,
                occurrences: vec![0; 3],
                ..SystemShape::default()
            }
        );
        assert_eq!(shape.mean_terms_per_generator(), 0.0);
        assert_eq!(shape.interaction_density(), 0.0);
        assert_eq!(shape.specialization_candidates(), vec![0, 1, 2]);
    }

    /// An MQ system is recognizable by its quadratic count, which is the shape Fukuoka publishes.
    #[test]
    fn test_a_quadratic_system_is_recognizable() {
        let shape = analyze(&parse(
            &["x^2 + x*y - 1", "y^2 + 2*x*y + 3", "x*y + x + y"],
            ["x", "y"],
        ));
        assert_eq!(shape.quadratic_generators, 3);
        assert_eq!(shape.max_degree, 2);
        assert_eq!(shape.linear_generators, 0);
    }
}
