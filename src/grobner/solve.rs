//! Solving systems of polynomial equations over a finite field.
//!
//! A lexicographic Grobner basis generates the same ideal as the system it came from, so the two
//! have the same solution set — but the basis is triangular. With x_0 > x_1 > ... > x_{N-1}, the
//! elimination property puts a polynomial in x_{N-1} alone into the basis, then one in the last
//! two variables, and so on. Assigning variables from the last backwards therefore meets a
//! constraint at every step, which is what makes searching the field tractable.
//!
//! # References
//! * Ideals, Varieties, and Algorithms by Cox, Little, and O'Shea, Sec 3.1

use rand::{CryptoRng, RngCore};

use crate::{grobner::buchberger, poly::MonomialOrder, FiniteField, MultivariatePolynomial};

/// The largest field this solver will enumerate.
///
/// Every level of the search tries each element of the base field, so the cost grows with the
/// field's order. Rather than appearing to hang on a field it cannot handle, `solve` refuses.
const MAX_FIELD_ORDER: u128 = 1 << 20;

/// Every point of F^N at which all polynomials of `system` vanish.
///
/// The order of the returned points is unspecified.
///
/// # Panics
/// Panics if the field's order exceeds `MAX_FIELD_ORDER`. Solving over a large field needs
/// univariate root finding rather than enumeration; see the module documentation.
pub fn solve<const N: usize, F: FiniteField, R: RngCore + CryptoRng>(
    system: &[MultivariatePolynomial<N, F>],
    rng: &mut R,
) -> Vec<[F; N]> {
    assert!(
        F::order() <= MAX_FIELD_ORDER,
        "solve enumerates the base field, whose order {} exceeds the limit of {}",
        F::order(),
        MAX_FIELD_ORDER
    );

    let elements = field_elements(rng);

    // An empty system constrains nothing, so every point is a solution. Handled separately
    // because `buchberger` has no generators to work with.
    if system.is_empty() || system.iter().all(|p| p.is_zero()) {
        let mut solutions = Vec::new();
        let mut assignment = [F::zero(); N];
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
    extend(&basis, &elements, N, &mut assignment, &mut solutions);
    solutions
}

/// Assign the variables below `remaining`, deepest first, collecting the points that satisfy the
/// whole basis.
///
/// `basis` always has the already-assigned variables substituted in, so at the deepest level
/// every polynomial is a constant.
fn extend<const N: usize, F: FiniteField>(
    basis: &[MultivariatePolynomial<N, F>],
    elements: &[F],
    remaining: usize,
    assignment: &mut [F; N],
    solutions: &mut Vec<[F; N]>,
) {
    if remaining == 0 {
        if basis.iter().all(|p| p.is_zero()) {
            solutions.push(*assignment);
        }
        return;
    }

    let index = remaining - 1;
    for value in elements {
        assignment[index] = *value;
        let substituted: Vec<MultivariatePolynomial<N, F>> =
            basis.iter().map(|p| p.substitute(index, *value)).collect();

        // Abandon the branch as soon as any polynomial becomes a nonzero constant, which says
        // this partial assignment already contradicts the system. A lex basis is triangular, so
        // the constraint on the deepest variable is univariate and this prunes immediately.
        if substituted.iter().any(is_nonzero_constant) {
            continue;
        }

        extend(&substituted, elements, index, assignment, solutions);
    }
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
fn is_nonzero_constant<const N: usize, F: FiniteField>(p: &MultivariatePolynomial<N, F>) -> bool {
    p.is_constant() && !p.is_zero()
}

/// Every element of the field.
///
/// Built from a generator because `FiniteField` offers no way to enumerate elements directly:
/// `new` maps integers into the field, which reaches only the prime subfield of an extension.
/// The multiplicative group is cyclic of order q - 1, so its powers cover every nonzero element.
fn field_elements<F: FiniteField, R: RngCore + CryptoRng>(rng: &mut R) -> Vec<F> {
    let order = F::order();
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
        fields::PrimeFieldElement64, identities::Zero, FiniteField, MultivariatePolynomial,
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
}
