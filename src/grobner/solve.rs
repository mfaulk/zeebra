//! Solving systems of polynomial equations over a finite field.
//!
//! A lexicographic Grobner basis generates the same ideal as the system it came from, so the two
//! have the same solution set — but the basis is triangular. With x_0 > x_1 > ... > x_{N-1}, the
//! elimination property puts a polynomial in x_{N-1} alone into the basis, then one in the last
//! two variables, and so on.
//!
//! Variables are therefore assigned from the last backwards. At each step the basis polynomials
//! that have become univariate in the current variable are solved with [`roots`], so only their
//! common roots are tried — a handful of values rather than the whole field. A variable left
//! unconstrained by the basis is free, and the only way to cover a free variable is to enumerate
//! the field, which is what bounds the fields this can handle.
//!
//! # References
//! * Ideals, Varieties, and Algorithms by Cox, Little, and O'Shea, Sec 3.1

use rand::{CryptoRng, RngCore};

use crate::{
    grobner::buchberger,
    poly::{roots, MonomialOrder, Polynomial, UnivariatePolynomial},
    FiniteField, KnownOrder, MultivariatePolynomial,
};

/// The largest field whose elements this solver will enumerate.
///
/// Only reached for a system with a free variable, where the solution set itself grows with the
/// field and no algorithm could enumerate it. A system with finitely many solutions needs no
/// enumeration at all, so this limit does not apply to it.
const MAX_FIELD_ORDER: u128 = 1 << 20;

/// Every point of F^N at which all polynomials of `system` vanish.
///
/// The order of the returned points is unspecified.
///
/// # Panics
/// Panics if the system leaves a variable unconstrained and the field's order exceeds
/// `MAX_FIELD_ORDER`. A system with finitely many solutions has no such limit.
pub fn solve<const N: usize, F: KnownOrder, R: RngCore + CryptoRng>(
    system: &[MultivariatePolynomial<N, F>],
    rng: &mut R,
) -> Vec<[F; N]> {
    // An empty system constrains nothing, so every point is a solution. Handled separately
    // because `buchberger` has no generators to work with.
    if system.is_empty() || system.iter().all(|p| p.is_zero()) {
        let mut solutions = Vec::new();
        let mut assignment = [F::zero(); N];
        let elements = field_elements(rng);
        enumerate_all(&elements, N, &mut assignment, &mut solutions);
        return solutions;
    }

    let basis = buchberger(system, MonomialOrder::Lexicographic);

    // A basis containing a nonzero constant generates the whole ring: the ideal asserts 1 = 0,
    // so the system is inconsistent and has no solutions at all.
    if basis.iter().any(is_nonzero_constant) {
        return Vec::new();
    }

    let mut solutions = Vec::new();
    let mut assignment = [F::zero(); N];
    // Built only if a free variable turns up, since that is the only case needing it.
    let mut elements: Option<Vec<F>> = None;
    extend(
        &basis,
        N,
        &mut assignment,
        &mut solutions,
        &mut elements,
        rng,
    );
    solutions
}

/// Assign the variables below `remaining`, deepest first, collecting the points that satisfy the
/// whole basis.
///
/// `basis` always has the already-assigned variables substituted in, so at the deepest level
/// every polynomial is a constant.
fn extend<const N: usize, F: KnownOrder, R: RngCore + CryptoRng>(
    basis: &[MultivariatePolynomial<N, F>],
    remaining: usize,
    assignment: &mut [F; N],
    solutions: &mut Vec<[F; N]>,
    elements: &mut Option<Vec<F>>,
    rng: &mut R,
) {
    if remaining == 0 {
        if basis.iter().all(|p| p.is_zero()) {
            solutions.push(*assignment);
        }
        return;
    }

    let index = remaining - 1;
    let candidates = match candidate_values(basis, index, rng) {
        Some(values) => values,
        None => {
            // Nothing in the basis constrains this variable, so every element of the field has
            // to be tried. Cloned rather than borrowed so `elements` stays available to recurse
            // with.
            if elements.is_none() {
                assert!(
                    F::order_u128().is_some_and(|q| q <= MAX_FIELD_ORDER),
                    "variable {} is unconstrained, so covering it means enumerating the field, \
                     whose order {:?} exceeds the limit of {}",
                    index,
                    F::order_limbs(),
                    MAX_FIELD_ORDER
                );
                *elements = Some(field_elements(rng));
            }
            elements.as_ref().expect("just populated").clone()
        }
    };

    for value in candidates {
        assignment[index] = value;
        let substituted: Vec<MultivariatePolynomial<N, F>> =
            basis.iter().map(|p| p.substitute(index, value)).collect();

        // A nonzero constant says this partial assignment already contradicts the system.
        if substituted.iter().any(is_nonzero_constant) {
            continue;
        }

        extend(&substituted, index, assignment, solutions, elements, rng);
    }
}

/// The values of variable `index` worth trying, or `None` if the basis does not constrain it.
///
/// A lex basis is triangular, so once the deeper variables are substituted at least one
/// polynomial is usually univariate in this one. Its roots are the only possible values, which
/// replaces a sweep of the whole field with a handful of candidates.
///
/// Shared with [`super::solve_zero_dimensional`], which needs the same candidates under a stricter
/// contract: for a zero-dimensional ideal this never returns `None`. See that module for why.
pub(crate) fn candidate_values<const N: usize, F: KnownOrder, R: RngCore + CryptoRng>(
    basis: &[MultivariatePolynomial<N, F>],
    index: usize,
    rng: &mut R,
) -> Option<Vec<F>> {
    let constraints: Vec<UnivariatePolynomial<F>> = basis
        .iter()
        .filter_map(|p| as_univariate(p, index))
        // A constant carries no information about the variable: zero is satisfied by every value,
        // and a nonzero constant is caught by the contradiction check instead.
        .filter(|u| !u.is_zero() && u.degree() > 0)
        .collect();

    let (first, rest) = constraints.split_first()?;

    // Take the roots of one constraint and keep those satisfying the others. Equivalent to the
    // roots of their gcd, without needing to reason about a constant gcd separately.
    let mut candidates = roots(first, rng);
    for constraint in rest {
        candidates.retain(|value| constraint.eval(value).is_zero());
    }
    Some(candidates)
}

/// `p` as a polynomial in variable `index` alone, or `None` if another variable appears in it.
pub(crate) fn as_univariate<const N: usize, F: FiniteField>(
    p: &MultivariatePolynomial<N, F>,
    index: usize,
) -> Option<UnivariatePolynomial<F>> {
    let mut coefficients: Vec<F> = Vec::new();
    for (monomial, coefficient) in p.terms() {
        let exponents = monomial.exponents();
        if exponents
            .iter()
            .enumerate()
            .any(|(i, exponent)| i != index && *exponent != 0)
        {
            return None;
        }
        let degree = exponents[index] as usize;
        if coefficients.len() <= degree {
            coefficients.resize(degree + 1, F::zero());
        }
        coefficients[degree] = *coefficient;
    }
    Some(UnivariatePolynomial::new(&coefficients))
}

/// Every point of F^N, for a system that constrains nothing.
fn enumerate_all<const N: usize, F: FiniteField>(
    elements: &[F],
    remaining: usize,
    assignment: &mut [F; N],
    solutions: &mut Vec<[F; N]>,
) {
    if remaining == 0 {
        solutions.push(*assignment);
        return;
    }
    let index = remaining - 1;
    for value in elements {
        assignment[index] = *value;
        enumerate_all(elements, index, assignment, solutions);
    }
}

/// True if the polynomial is a constant other than zero, i.e. an unsatisfiable equation.
pub(crate) fn is_nonzero_constant<const N: usize, F: FiniteField>(
    p: &MultivariatePolynomial<N, F>,
) -> bool {
    p.is_constant() && !p.is_zero()
}

/// Every element of the field.
///
/// Built from a generator because `FiniteField` offers no way to enumerate elements directly:
/// `new` maps integers into the field, which reaches only the prime subfield of an extension.
/// The multiplicative group is cyclic of order q - 1, so its powers cover every nonzero element.
fn field_elements<F: KnownOrder, R: RngCore + CryptoRng>(rng: &mut R) -> Vec<F> {
    let order = F::order_u128().unwrap_or(u128::MAX);
    assert!(
        order <= MAX_FIELD_ORDER,
        "enumerating a field of order {:?} exceeds the limit of {}",
        F::order_limbs(),
        MAX_FIELD_ORDER
    );
    let mut elements = Vec::with_capacity(order as usize);
    elements.push(F::zero());

    let generator = F::primitive_element(rng);
    let mut power = F::one();
    for _ in 0..(order - 1) {
        elements.push(power);
        power *= generator;
    }
    elements
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use rand::{prelude::StdRng, SeedableRng};

    use super::{field_elements, solve};
    use crate::{
        fields::{PrimeFieldElement64, Zp18446744073709551557, Zp2147483647},
        identities::Zero,
        FiniteField, KnownOrder, MultivariatePolynomial,
    };

    /// Every point at which the system vanishes, found by trying all of them.
    ///
    /// Deliberately independent of `solve`: it computes no Grobner basis and does no pruning, so
    /// agreement between the two is evidence about the basis as well as the search.
    fn by_exhaustive_search<const N: usize, F: FiniteField>(
        system: &[MultivariatePolynomial<N, F>],
        elements: &[F],
    ) -> HashSet<[F; N]> {
        let mut found = HashSet::new();
        let mut point = [F::zero(); N];
        fn walk<const N: usize, F: FiniteField>(
            system: &[MultivariatePolynomial<N, F>],
            elements: &[F],
            remaining: usize,
            point: &mut [F; N],
            found: &mut HashSet<[F; N]>,
        ) {
            if remaining == 0 {
                if system.iter().all(|p| p.eval(point).is_zero()) {
                    found.insert(*point);
                }
                return;
            }
            let index = remaining - 1;
            for value in elements {
                point[index] = *value;
                walk(system, elements, index, point, found);
            }
        }
        walk(system, elements, N, &mut point, &mut found);
        found
    }

    /// `solve` agrees with exhaustive search on each system, over two different fields.
    #[test]
    fn test_solve_agrees_with_exhaustive_search() {
        let systems: Vec<Vec<&str>> = vec![
            // One isolated solution: x = y = 1.
            vec!["x - 1", "y - 1"],
            // Two variables pinned by a product and a sum.
            vec!["x + y", "x*y - 1"],
            // A conic meeting a line.
            vec!["x^2 + y^2 - 1", "x - y"],
            // A single curve, so many solutions rather than finitely many isolated ones.
            vec!["x*y - 1"],
            // One equation in two unknowns: positive-dimensional.
            vec!["x - y"],
            // Inconsistent: x cannot be both 0 and 1.
            vec!["x", "x - 1"],
            // Inconsistent in a less obvious way.
            vec!["x + y", "x + y - 1"],
            // A system with no solutions over this field but solutions over an extension.
            vec!["x^2 + 1", "y"],
            // The lone generator that used to make Buchberger panic.
            vec!["x^2 - y"],
            // Repeated roots.
            vec!["x^2", "y^2"],
            // A triangular system solved by back-substitution.
            vec!["x^3 - 1", "y - x^2"],
        ];

        fn check<const P: u64>(systems: &[Vec<&str>], seed: u64) {
            type Vars = [&'static str; 2];
            const VARS: Vars = ["x", "y"];
            let mut rng = StdRng::seed_from_u64(seed);
            let elements = field_elements::<PrimeFieldElement64<P>, _>(&mut rng);

            for system in systems {
                let f: Vec<MultivariatePolynomial<2, PrimeFieldElement64<P>>> = system
                    .iter()
                    .map(|s| MultivariatePolynomial::parse(s, VARS).unwrap())
                    .collect();

                let expected = by_exhaustive_search(&f, &elements);
                let found: HashSet<_> = solve(&f, &mut rng).into_iter().collect();
                assert_eq!(found, expected, "system {:?} over GF({})", system, P);

                // Whatever is returned must genuinely satisfy the original system, not merely
                // the basis derived from it.
                for point in &found {
                    for p in &f {
                        assert!(
                            p.eval(point).is_zero(),
                            "{:?} is not a root of {} in {:?}",
                            point,
                            p,
                            system
                        );
                    }
                }
            }
        }

        check::<5>(&systems, 1);
        check::<7>(&systems, 2);
        check::<13>(&systems, 3);
    }

    /// Three variables, where the triangular structure of a lex basis does real work.
    #[test]
    fn test_solve_three_variables() {
        type F = PrimeFieldElement64<7>;
        let vars = ["x", "y", "z"];
        let mut rng = StdRng::seed_from_u64(17);
        let elements = field_elements::<F, _>(&mut rng);

        let systems: Vec<Vec<&str>> = vec![
            vec!["x - 1", "y - 2", "z - 3"],
            vec!["x + y + z", "x*y + x*z + y*z", "x*y*z - 1"],
            vec!["x + y", "x^2 + z", "y*z - 1"],
            vec!["x*y*z - 1", "x - y", "y - z"],
        ];

        for system in &systems {
            let f: Vec<MultivariatePolynomial<3, F>> = system
                .iter()
                .map(|s| MultivariatePolynomial::parse(s, vars).unwrap())
                .collect();
            let expected = by_exhaustive_search(&f, &elements);
            let found: HashSet<_> = solve(&f, &mut rng).into_iter().collect();
            assert_eq!(found, expected, "system {:?}", system);
        }
    }

    /// An inconsistent system yields no solutions, detected from the basis being {1}.
    #[test]
    fn test_solve_inconsistent_system() {
        type F = PrimeFieldElement64<13>;
        let vars = ["x", "y"];
        let mut rng = StdRng::seed_from_u64(23);
        let f: Vec<MultivariatePolynomial<2, F>> = vec![
            MultivariatePolynomial::parse("x", vars).unwrap(),
            MultivariatePolynomial::parse("x - 1", vars).unwrap(),
        ];
        assert!(solve(&f, &mut rng).is_empty());
    }

    /// A system that constrains nothing is satisfied everywhere.
    #[test]
    fn test_solve_empty_system() {
        type F = PrimeFieldElement64<5>;
        let mut rng = StdRng::seed_from_u64(29);
        let empty: Vec<MultivariatePolynomial<2, F>> = vec![];
        assert_eq!(solve(&empty, &mut rng).len(), 25);

        // The zero polynomial constrains nothing either.
        let zeros: Vec<MultivariatePolynomial<2, F>> = vec![MultivariatePolynomial::zero()];
        assert_eq!(solve(&zeros, &mut rng).len(), 25);
    }

    /// The generated element list is exactly the field.
    #[test]
    fn test_field_elements_covers_the_field() {
        let mut rng = StdRng::seed_from_u64(31);
        let elements = field_elements::<PrimeFieldElement64<13>, _>(&mut rng);
        assert_eq!(elements.len(), 13);
        let distinct: HashSet<_> = elements.iter().collect();
        assert_eq!(distinct.len(), 13);
    }

    /// A system with finitely many solutions is solved over a field far too large to enumerate.
    ///
    /// The field-order assert is what makes this a proof rather than a timing observation: any
    /// attempt to enumerate GF(2^31 - 1) would panic, so passing means the roots of the
    /// univariate constraints were used instead.
    #[test]
    fn test_solve_over_a_field_too_large_to_enumerate() {
        type F = Zp2147483647; // 2^31 - 1, about two thousand times the enumeration limit
        let vars = ["x", "y"];
        let mut rng = StdRng::seed_from_u64(37);
        assert!(F::order_u128().unwrap() > super::MAX_FIELD_ORDER);

        // A single point.
        let f: Vec<MultivariatePolynomial<2, F>> = vec![
            MultivariatePolynomial::parse("x - 5", vars).unwrap(),
            MultivariatePolynomial::parse("y - 7", vars).unwrap(),
        ];
        let found: HashSet<_> = solve(&f, &mut rng).into_iter().collect();
        assert_eq!(found, HashSet::from([[F::new(5), F::new(7)]]));

        // Two points, reached through a quadratic constraint.
        let f: Vec<MultivariatePolynomial<2, F>> = vec![
            MultivariatePolynomial::parse("x^2 - 4", vars).unwrap(),
            MultivariatePolynomial::parse("y - x", vars).unwrap(),
        ];
        let found: HashSet<_> = solve(&f, &mut rng).into_iter().collect();
        let minus_two = F::zero() - F::new(2);
        assert_eq!(
            found,
            HashSet::from([[F::new(2), F::new(2)], [minus_two, minus_two],])
        );

        // Every reported point must satisfy the original system.
        for point in &found {
            for p in &f {
                assert!(p.eval(point).is_zero());
            }
        }
    }

    /// Three variables over the largest 64-bit prime.
    #[test]
    fn test_solve_three_variables_over_a_large_field() {
        type F = Zp18446744073709551557;
        let vars = ["x", "y", "z"];
        let mut rng = StdRng::seed_from_u64(41);

        let f: Vec<MultivariatePolynomial<3, F>> = vec![
            MultivariatePolynomial::parse("z - 3", vars).unwrap(),
            MultivariatePolynomial::parse("y - z^2", vars).unwrap(),
            MultivariatePolynomial::parse("x - y - z", vars).unwrap(),
        ];
        let found = solve(&f, &mut rng);
        // z = 3, y = 9, x = 12.
        assert_eq!(found, vec![[F::new(12), F::new(9), F::new(3)]]);
    }

    /// A free variable still forces enumeration, which a large field cannot support.
    ///
    /// The limit is a property of the answer, not of the method: the solution set of `x - y` over
    /// this field has 2^31 - 1 points, so no algorithm could list them.
    #[test]
    #[should_panic(expected = "unconstrained")]
    fn test_solve_refuses_a_free_variable_over_a_large_field() {
        type F = Zp2147483647;
        let vars = ["x", "y"];
        let mut rng = StdRng::seed_from_u64(43);
        let f: Vec<MultivariatePolynomial<2, F>> =
            vec![MultivariatePolynomial::parse("x - y", vars).unwrap()];
        let _ = solve(&f, &mut rng);
    }

    /// A free variable over a small field is still handled, by enumeration.
    #[test]
    fn test_solve_free_variable_over_a_small_field() {
        type F = PrimeFieldElement64<7>;
        let vars = ["x", "y"];
        let mut rng = StdRng::seed_from_u64(47);
        let f: Vec<MultivariatePolynomial<2, F>> =
            vec![MultivariatePolynomial::parse("x - y", vars).unwrap()];
        let found: HashSet<_> = solve(&f, &mut rng).into_iter().collect();
        // x = y, so seven points.
        assert_eq!(found.len(), 7);
        for point in &found {
            assert_eq!(point[0], point[1]);
        }
    }
}
