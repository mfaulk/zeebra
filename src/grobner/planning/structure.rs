//! Structural input features: which equations share variables, and what the linear part says.
//!
//! [`analysis`](super::analysis) counts terms, degrees and monomial co-occurrence. This module
//! adds the two structures it does not see, both computed before any basis:
//!
//! - [`incidence`]: the **equation–variable incidence** of the system. Two variables are joined
//!   when they occur anywhere in one generator, not only in one monomial, so `x² + y² − 1` joins
//!   `x` and `y` although `interaction_pairs` counts no pair for it. From it come the connected
//!   components, the generator arities, and a greedy elimination width with a hard work cap.
//! - [`linear_subsystem`]: the generators of degree at most one, their exact rank over the
//!   coefficient field and whether they are consistent, and [`scalar_substitutions`]: the
//!   generators `a·x_j + h` that solve for one variable outright.
//!
//! Two kinds of statement live here, and they must not be confused. The **exact** ones are
//! [`LinearSubsystem::consistent`] (`false` puts 1 in the ideal) and
//! [`IncidenceStructure::components`] (disjoint blocks have coprime leading monomials across
//! blocks, so the blocks' bases together are a basis of the whole). Everything else, the
//! elimination width and the substitution fill bound included, is a **presentation statistic**: a
//! predictor of cost, not a property of the ideal. `docs/research/input-features.md` gives the
//! definitions, costs and invariance of each.

use crate::{FiniteField, MultivariatePolynomial};

/// Work units [`incidence`] spends on the elimination width before giving up.
///
/// One unit is one adjacency check or update, so the cap bounds the width's cost whatever the
/// input. Its cost in time is not yet measured: #1009 waits on the #1006/#1007 pilot panel.
pub const DEFAULT_WIDTH_WORK: u64 = 1 << 20;

/// The equation–variable incidence of a system.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct IncidenceStructure {
    /// Connected components of the incidence graph, each with at least one variable.
    ///
    /// Ordered by smallest variable index; variables and generators ascending within each.
    /// Zero generators and nonzero constants belong to none (a constant is reported in
    /// [`Self::constant_generators`]). Variables in no generator are in
    /// [`Self::unused_variables`], not singleton components.
    pub components: Vec<IncidenceComponent>,

    /// Variables that occur in no generator, ascending. Free in every solution.
    pub unused_variables: Vec<usize>,

    /// Generators that are nonzero constants. Any one of them makes the ideal the unit ideal, and
    /// then the components describe the presentation and nothing about the solutions.
    pub constant_generators: usize,

    /// `(arity, generators with that many distinct variables)`, ascending, nonconstant generators
    /// only.
    pub arity_histogram: Vec<(usize, usize)>,

    /// The greedy min-degree elimination width of the primal graph, or `None` when the work cap
    /// ran out first.
    ///
    /// The primal graph has the variables as vertices and joins every two that share a
    /// generator. Eliminating vertices in min-degree order and recording each one's degree at
    /// elimination gives an **upper bound on the treewidth** of that graph, not the treewidth.
    /// Zero for a system with no two variables in one generator.
    pub elimination_width: Option<usize>,
}

impl IncidenceStructure {
    /// The largest component's variable count, zero if there is none.
    pub fn largest_component_variables(&self) -> usize {
        self.components
            .iter()
            .map(|c| c.variables.len())
            .max()
            .unwrap_or(0)
    }
}

/// One connected component of the incidence graph.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct IncidenceComponent {
    /// Variable indices, ascending.
    pub variables: Vec<usize>,
    /// Indices into the input slice of the generators that use these variables, ascending.
    pub generators: Vec<usize>,
}

/// The equation–variable incidence of `system`, with the elimination width capped at
/// `width_work` adjacency updates.
///
/// Components cost one union per variable occurrence, `O(T)` in the system's terms with a
/// near-constant factor. The width costs at most `width_work` further steps.
pub fn incidence<const N: usize, F: FiniteField>(
    system: &[MultivariatePolynomial<N, F>],
    width_work: u64,
) -> IncidenceStructure {
    let mut structure = IncidenceStructure::default();
    let mut forest = DisjointSets::new(N);
    let mut used = vec![false; N];
    // Per nonconstant generator, its input index and distinct variables.
    let mut scopes: Vec<(usize, Vec<usize>)> = Vec::new();

    for (index, p) in system.iter().enumerate() {
        if p.is_zero() {
            continue;
        }
        let scope = variables_of(p);
        if scope.is_empty() {
            structure.constant_generators += 1;
            continue;
        }
        for &v in &scope {
            used[v] = true;
            forest.union(scope[0], v);
        }
        scopes.push((index, scope));
    }

    let mut arities: Vec<usize> = scopes.iter().map(|(_, s)| s.len()).collect();
    arities.sort_unstable();
    for arity in arities {
        match structure.arity_histogram.last_mut() {
            Some((a, count)) if *a == arity => *count += 1,
            _ => structure.arity_histogram.push((arity, 1)),
        }
    }

    // Components in order of first variable: walking variables ascending meets each root's
    // smallest member first.
    let mut slot_of_root = vec![usize::MAX; N];
    for v in 0..N {
        if !used[v] {
            structure.unused_variables.push(v);
            continue;
        }
        let root = forest.find(v);
        if slot_of_root[root] == usize::MAX {
            slot_of_root[root] = structure.components.len();
            structure.components.push(IncidenceComponent::default());
        }
        structure.components[slot_of_root[root]].variables.push(v);
    }
    for (index, scope) in &scopes {
        let slot = slot_of_root[forest.find(scope[0])];
        structure.components[slot].generators.push(*index);
    }

    structure.elimination_width = elimination_width(N, &scopes, width_work);
    structure
}

/// Distinct variables of `p`, ascending.
fn variables_of<const N: usize, F: FiniteField>(p: &MultivariatePolynomial<N, F>) -> Vec<usize> {
    let mut present = [false; N];
    for monomial in p.terms().keys() {
        for (i, &e) in monomial.exponents().iter().enumerate() {
            if e > 0 {
                present[i] = true;
            }
        }
    }
    (0..N).filter(|&i| present[i]).collect()
}

/// Greedy min-degree elimination width of the primal graph, or `None` past `budget` steps.
///
/// Building the graph is charged to the same budget, so a dense high-arity system cannot spend
/// more than the cap here either.
fn elimination_width(
    variables: usize,
    scopes: &[(usize, Vec<usize>)],
    budget: u64,
) -> Option<usize> {
    let mut work: u64 = 0;
    let mut adjacent = vec![vec![false; variables]; variables];
    let mut degree = vec![0usize; variables];
    for (_, scope) in scopes {
        work = work.saturating_add((scope.len() * scope.len()) as u64);
        if work > budget {
            return None;
        }
        for (a, &i) in scope.iter().enumerate() {
            for &j in &scope[a + 1..] {
                if !adjacent[i][j] {
                    adjacent[i][j] = true;
                    adjacent[j][i] = true;
                    degree[i] += 1;
                    degree[j] += 1;
                }
            }
        }
    }

    let mut alive = vec![true; variables];
    let mut width = 0;
    for _ in 0..variables {
        // Min degree, ties by index, so the order and therefore the bound are deterministic.
        let v = (0..variables)
            .filter(|&v| alive[v])
            .min_by_key(|&v| (degree[v], v))?;
        let neighbours: Vec<usize> = (0..variables)
            .filter(|&u| alive[u] && adjacent[v][u])
            .collect();
        width = width.max(neighbours.len());
        work = work.saturating_add((variables + neighbours.len() * neighbours.len()) as u64);
        if work > budget {
            return None;
        }
        // Make the neighbourhood a clique, then drop v.
        for (a, &i) in neighbours.iter().enumerate() {
            for &j in &neighbours[a + 1..] {
                if !adjacent[i][j] {
                    adjacent[i][j] = true;
                    adjacent[j][i] = true;
                    degree[i] += 1;
                    degree[j] += 1;
                }
            }
            degree[i] -= 1;
        }
        alive[v] = false;
    }
    Some(width)
}

/// Union-find with path halving and union by size.
struct DisjointSets {
    parent: Vec<usize>,
    size: Vec<usize>,
}

impl DisjointSets {
    fn new(n: usize) -> Self {
        Self {
            parent: (0..n).collect(),
            size: vec![1; n],
        }
    }

    fn find(&mut self, mut x: usize) -> usize {
        while self.parent[x] != x {
            self.parent[x] = self.parent[self.parent[x]];
            x = self.parent[x];
        }
        x
    }

    fn union(&mut self, a: usize, b: usize) {
        let (mut a, mut b) = (self.find(a), self.find(b));
        if a == b {
            return;
        }
        if self.size[a] < self.size[b] {
            std::mem::swap(&mut a, &mut b);
        }
        self.parent[b] = a;
        self.size[a] += self.size[b];
    }
}

/// The affine-linear part of a system: its generators of total degree at most one.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct LinearSubsystem {
    /// Indices into the input of the nonzero generators of total degree at most one, ascending.
    /// Nonzero constants are included: as the equation `c = 0` they are the inconsistent row.
    pub generators: Vec<usize>,

    /// The rank of their coefficient matrix over the variables, exact over the coefficient field.
    ///
    /// The number of variables the linear part determines as affine functions of the rest. It
    /// depends on the field: `x + y` and `x − y` have rank 2 over every odd characteristic and 1
    /// over characteristic two.
    pub rank: usize,

    /// The linear equations have a common solution over the algebraic closure.
    ///
    /// **Exact.** `false` means the augmented matrix has larger rank than the coefficient matrix,
    /// so a linear combination of generators is a nonzero constant and the ideal is the unit
    /// ideal. `true` says nothing about the nonlinear generators.
    pub consistent: bool,
}

/// The affine-linear subsystem of `system`, by Gaussian elimination over `F`.
///
/// `O(m · N · min(m, N))` field operations for `m` linear generators: dense elimination on an
/// `m × (N + 1)` matrix.
pub fn linear_subsystem<const N: usize, F: FiniteField>(
    system: &[MultivariatePolynomial<N, F>],
) -> LinearSubsystem {
    let mut result = LinearSubsystem {
        consistent: true,
        ..LinearSubsystem::default()
    };
    // Row layout: coefficients of x_0..x_{N-1}, then the constant.
    let mut rows: Vec<Vec<F>> = Vec::new();
    for (index, p) in system.iter().enumerate() {
        if p.is_zero() || p.degree() > 1 {
            continue;
        }
        result.generators.push(index);
        let mut row = vec![F::zero(); N + 1];
        for (monomial, &c) in p.terms() {
            match monomial.exponents().iter().position(|&e| e > 0) {
                Some(v) => row[v] = c,
                None => row[N] = c,
            }
        }
        rows.push(row);
    }

    let mut pivot_row = 0;
    for column in 0..=N {
        let Some(found) = (pivot_row..rows.len()).find(|&r| !rows[r][column].is_zero()) else {
            continue;
        };
        if column == N {
            // A pivot in the constant column: some combination is `c = 0` with c nonzero.
            result.consistent = false;
            break;
        }
        rows.swap(pivot_row, found);
        let inverse = rows[pivot_row][column].inverse();
        for entry in rows[pivot_row].iter_mut() {
            *entry *= inverse;
        }
        let pivot = rows[pivot_row].clone();
        for (r, row) in rows.iter_mut().enumerate() {
            if r == pivot_row || row[column].is_zero() {
                continue;
            }
            let factor = row[column];
            for (entry, &p) in row.iter_mut().zip(&pivot) {
                *entry -= factor * p;
            }
        }
        pivot_row += 1;
        result.rank += 1;
    }
    result
}

/// A generator `a·x_j + h` with `a` a nonzero scalar and `x_j` absent from `h`.
///
/// Such a generator solves for `x_j = −h/a` in every solution, so `x_j` can be eliminated by
/// substitution without a basis. `h` may be nonlinear; what matters is that `x_j` occurs in exactly
/// one term of the generator and that term is `x_j` itself. A coefficient that is a polynomial,
/// as in `y·x + 1`, does not qualify.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ScalarSubstitution {
    /// Index into the input of the generator.
    pub generator: usize,
    /// The variable it solves for.
    pub variable: usize,
    /// Terms of `h`.
    pub rest_terms: usize,
    /// Total degree of `h`; zero when `h` is a constant or empty.
    pub rest_degree: u64,
    /// Other nonzero generators that contain `x_j`, which the substitution rewrites.
    pub rewritten_generators: usize,
    /// An upper bound on the terms of those generators after substituting, before merging and
    /// cancellation, saturating at `u64::MAX`.
    ///
    /// A term with `x_j^e` becomes at most `C(r + e − 1, e)` terms for `r = rest_terms`, the
    /// monomials of degree `e` in `r` symbols. Merging only lowers the count, so the true fill is
    /// at most this. It is an **estimate of cost**, and a loose one for large `e`.
    pub fill_bound: u64,
}

/// Every `(generator, variable)` pair in `system` that is a [`ScalarSubstitution`], ordered by
/// generator, then variable.
///
/// One pass over the terms per generator for detection, and one more over the generators per
/// substitution found for the fill bound.
pub fn scalar_substitutions<const N: usize, F: FiniteField>(
    system: &[MultivariatePolynomial<N, F>],
) -> Vec<ScalarSubstitution> {
    let mut found = Vec::new();
    for (index, p) in system.iter().enumerate() {
        // Per variable: terms containing it, and whether one of them is the bare x_j.
        let mut containing = [0usize; N];
        let mut bare = [false; N];
        for monomial in p.terms().keys() {
            let exponents = monomial.exponents();
            let mut present = exponents.iter().enumerate().filter(|(_, &e)| e > 0);
            if let (Some((v, &1)), None) = (present.next(), present.next()) {
                bare[v] = true;
            }
            for (v, &e) in exponents.iter().enumerate() {
                if e > 0 {
                    containing[v] += 1;
                }
            }
        }
        for variable in 0..N {
            if !(bare[variable] && containing[variable] == 1) {
                continue;
            }
            let rest = p.terms().keys().filter(|m| m.exponents()[variable] == 0);
            let (rest_terms, rest_degree) =
                rest.fold((0usize, 0u64), |(n, d), m| (n + 1, d.max(m.degree())));
            let mut rewritten_generators = 0;
            let mut fill_bound: u64 = 0;
            for (other, q) in system.iter().enumerate() {
                if other == index || q.is_zero() {
                    continue;
                }
                let mut touches = false;
                let mut terms: u64 = 0;
                for monomial in q.terms().keys() {
                    let e = monomial.exponents()[variable];
                    if e > 0 {
                        touches = true;
                    }
                    terms = terms.saturating_add(multisets(rest_terms as u64, u64::from(e)));
                }
                if touches {
                    rewritten_generators += 1;
                    fill_bound = fill_bound.saturating_add(terms);
                }
            }
            found.push(ScalarSubstitution {
                generator: index,
                variable,
                rest_terms,
                rest_degree,
                rewritten_generators,
                fill_bound,
            });
        }
    }
    found
}

/// Multisets of size `k` from `r` symbols, `C(r + k − 1, k)`, saturating. One for `k = 0`.
fn multisets(r: u64, k: u64) -> u64 {
    if k == 0 {
        return 1;
    }
    if r == 0 {
        return 0;
    }
    let mut count: u128 = 1;
    for i in 1..=u128::from(k) {
        count = count.saturating_mul(u128::from(r) + i - 1) / i;
        if count >= u128::from(u64::MAX) {
            return u64::MAX;
        }
    }
    count as u64
}

#[cfg(test)]
mod tests {
    use super::{
        incidence, linear_subsystem, multisets, scalar_substitutions, IncidenceComponent,
        DEFAULT_WIDTH_WORK,
    };
    use crate::{
        fields::{Zp2, Zp2147483647},
        grobner::{benchmark_systems::katsura, f4, planning::analyze},
        FiniteField, MonomialOrder, MultivariatePolynomial,
    };

    type F = Zp2147483647;

    fn parse<const N: usize, K: FiniteField>(
        strings: &[&str],
        vars: [&str; N],
    ) -> Vec<MultivariatePolynomial<N, K>> {
        strings
            .iter()
            .map(|s| MultivariatePolynomial::parse(s, vars).expect("parses"))
            .collect()
    }

    /// `x² + y² − 1` couples x and y in the incidence graph though no monomial holds both.
    #[test]
    fn test_incidence_is_not_monomial_co_occurrence() {
        let system = parse::<2, F>(&["x^2 + y^2 - 1"], ["x", "y"]);
        assert_eq!(analyze(&system).interaction_pairs, 0);
        let structure = incidence(&system, DEFAULT_WIDTH_WORK);
        assert_eq!(
            structure.components,
            vec![IncidenceComponent {
                variables: vec![0, 1],
                generators: vec![0],
            }]
        );
        assert_eq!(structure.elimination_width, Some(1));
    }

    /// Disjoint blocks are separate components, ordered by first variable, and unused variables,
    /// zero generators and constants are reported apart from them.
    #[test]
    fn test_components_unused_variables_and_constants() {
        let mut system = parse::<5, F>(
            &["v*z + 1", "w^2 - x", "z^3 - 2", "3"],
            ["v", "w", "x", "y", "z"],
        );
        system.insert(1, MultivariatePolynomial::zero());
        let structure = incidence(&system, DEFAULT_WIDTH_WORK);
        assert_eq!(
            structure.components,
            vec![
                IncidenceComponent {
                    variables: vec![0, 4],
                    generators: vec![0, 3],
                },
                IncidenceComponent {
                    variables: vec![1, 2],
                    generators: vec![2],
                },
            ]
        );
        assert_eq!(structure.unused_variables, vec![3]);
        assert_eq!(structure.constant_generators, 1);
        assert_eq!(structure.arity_histogram, vec![(1, 1), (2, 2)]);
        assert_eq!(structure.largest_component_variables(), 2);
    }

    /// The exact consequence: over disjoint blocks the reduced basis is the union of the blocks'
    /// reduced bases, because leading monomials from different blocks are coprime.
    #[test]
    fn test_disjoint_blocks_solve_separately() {
        let system = parse::<4, F>(
            &["a^2 + b - 1", "a*b - 2", "c^2 - d^2 + 3", "c*d + c - 1"],
            ["a", "b", "c", "d"],
        );
        let structure = incidence(&system, DEFAULT_WIDTH_WORK);
        assert_eq!(structure.components.len(), 2);

        let order = MonomialOrder::GradedReverseLexicographic;
        let mut whole = f4(&system, order).expect("within limits");
        let mut joined = Vec::new();
        for component in &structure.components {
            let block: Vec<_> = component
                .generators
                .iter()
                .map(|&g| system[g].clone())
                .collect();
            joined.extend(f4(&block, order).expect("within limits"));
        }
        let key = |p: &MultivariatePolynomial<4, F>| p.to_string();
        whole.sort_by_key(key);
        joined.sort_by_key(key);
        assert_eq!(whole, joined);
    }

    /// The width is an upper bound from greedy elimination: 1 on a path, `k − 1` on a k-clique,
    /// and `None` when the cap runs out.
    #[test]
    fn test_elimination_width() {
        let path = parse::<4, F>(&["a*b", "b + c", "c - d^2"], ["a", "b", "c", "d"]);
        assert_eq!(
            incidence(&path, DEFAULT_WIDTH_WORK).elimination_width,
            Some(1)
        );

        let katsura = katsura::<5, F>();
        let structure = incidence(&katsura, DEFAULT_WIDTH_WORK);
        assert_eq!(structure.components.len(), 1);
        assert_eq!(structure.elimination_width, Some(4));
        assert_eq!(incidence(&katsura, 10).elimination_width, None);

        let unary = parse::<3, F>(&["a^2 - 1", "b"], ["a", "b", "c"]);
        assert_eq!(
            incidence(&unary, DEFAULT_WIDTH_WORK).elimination_width,
            Some(0)
        );
    }

    /// A cycle of length five has treewidth 2, and min-degree elimination finds it.
    #[test]
    fn test_elimination_width_of_a_cycle() {
        let cycle = parse::<5, F>(
            &["a*b - 1", "b*c - 1", "c*d - 1", "d*e - 1", "e*a - 1"],
            ["a", "b", "c", "d", "e"],
        );
        let structure = incidence(&cycle, DEFAULT_WIDTH_WORK);
        assert_eq!(structure.elimination_width, Some(2));
        assert_eq!(structure.arity_histogram, vec![(2, 5)]);
    }

    /// Variable permutation relabels components but keeps their sizes, the arity histogram and
    /// the unused-variable count.
    #[test]
    fn test_incidence_under_variable_permutation() {
        let a = incidence(
            &parse::<4, F>(&["a*b + 1", "c - 1"], ["a", "b", "c", "d"]),
            DEFAULT_WIDTH_WORK,
        );
        let b = incidence(
            &parse::<4, F>(&["d*b + 1", "a - 1"], ["a", "b", "c", "d"]),
            DEFAULT_WIDTH_WORK,
        );
        let sizes = |s: &super::IncidenceStructure| {
            let mut v: Vec<usize> = s.components.iter().map(|c| c.variables.len()).collect();
            v.sort_unstable();
            v
        };
        assert_eq!(sizes(&a), sizes(&b));
        assert_eq!(a.arity_histogram, b.arity_histogram);
        assert_eq!(a.unused_variables.len(), b.unused_variables.len());
        assert_eq!(a.elimination_width, b.elimination_width);
    }

    /// Rank is exact over the field and nonlinear generators are ignored.
    #[test]
    fn test_linear_rank() {
        let system = parse::<3, F>(
            &["x + y - 1", "2*x + 2*y - 2", "y - z", "x^2 - 1"],
            ["x", "y", "z"],
        );
        let linear = linear_subsystem(&system);
        assert_eq!(linear.generators, vec![0, 1, 2]);
        assert_eq!(linear.rank, 2);
        assert!(linear.consistent);
    }

    /// `x + y` and `x − y` are independent in odd characteristic and equal in characteristic two.
    #[test]
    fn test_linear_rank_depends_on_the_field() {
        let odd = parse::<2, F>(&["x + y", "x - y"], ["x", "y"]);
        assert_eq!(linear_subsystem(&odd).rank, 2);
        let two = parse::<2, Zp2>(&["x + y", "x - y"], ["x", "y"]);
        assert_eq!(linear_subsystem(&two).rank, 1);
    }

    /// An inconsistent linear part is exact: F4 returns the unit ideal.
    #[test]
    fn test_inconsistent_linear_part_is_the_unit_ideal() {
        let system = parse::<3, F>(&["x + y - 1", "x + y - 2", "z^2 - x"], ["x", "y", "z"]);
        let linear = linear_subsystem(&system);
        assert!(!linear.consistent);
        let basis = f4(&system, MonomialOrder::GradedReverseLexicographic).expect("within limits");
        assert!(basis.iter().any(|p| p.is_constant() && !p.is_zero()));

        // A constant generator is itself the inconsistent row.
        assert!(!linear_subsystem(&parse::<1, F>(&["5"], ["x"])).consistent);
        // And no linear generators at all is consistent, with rank zero.
        let none = linear_subsystem(&parse::<2, F>(&["x*y - 1"], ["x", "y"]));
        assert!(none.consistent);
        assert_eq!(none.rank, 0);
        assert!(none.generators.is_empty());
    }

    /// `a·x + h` with x absent from h qualifies even when h is nonlinear; a polynomial coefficient
    /// or a second occurrence of x does not.
    #[test]
    fn test_scalar_substitutions() {
        let system = parse::<3, F>(
            &[
                "3*x + y^2 + z", // x qualifies; z qualifies too (h = 3x + y^2)
                "y*x + 1",       // polynomial coefficient: nothing
                "x + x^2",       // x occurs twice: nothing
                "x^2 + y*z - 1", // rewritten by substituting x
            ],
            ["x", "y", "z"],
        );
        let found = scalar_substitutions(&system);
        let pairs: Vec<(usize, usize)> = found.iter().map(|s| (s.generator, s.variable)).collect();
        assert_eq!(pairs, vec![(0, 0), (0, 2)]);

        let x = &found[0];
        assert_eq!(x.rest_terms, 2);
        assert_eq!(x.rest_degree, 2);
        // x appears in generators 1, 2 and 3.
        assert_eq!(x.rewritten_generators, 3);
        // y*x + 1 → 2 + 1; x + x^2 → 2 + 3; x^2 + y*z - 1 → 3 + 1 + 1.
        assert_eq!(x.fill_bound, 3 + 5 + 5);

        let z = &found[1];
        assert_eq!(z.rewritten_generators, 1);
        assert_eq!(z.rest_terms, 2);
    }

    /// Multisets of size k from r symbols, saturating.
    #[test]
    fn test_multisets() {
        assert_eq!(multisets(3, 0), 1);
        assert_eq!(multisets(0, 2), 0);
        assert_eq!(multisets(1, 5), 1);
        assert_eq!(multisets(3, 2), 6);
        assert_eq!(multisets(u64::MAX, 3), u64::MAX);
    }

    /// The empty system is described, not panicked on.
    #[test]
    fn test_the_empty_system() {
        let structure = incidence::<3, F>(&[], DEFAULT_WIDTH_WORK);
        assert!(structure.components.is_empty());
        assert_eq!(structure.unused_variables, vec![0, 1, 2]);
        assert_eq!(structure.elimination_width, Some(0));
        assert!(linear_subsystem::<3, F>(&[]).consistent);
        assert!(scalar_substitutions::<3, F>(&[]).is_empty());
    }
}
