//! What Berthomieu, Neiger and Safey El Din (ISSAC 2022, arXiv 2202.09226) need to know about a
//! staircase before multiplication by the last variable can be held as a `t × t` matrix over
//! `K[y]` instead of a `D × D` matrix over `K`.
//!
//! `y` is the last variable, the smallest under both grevlex and lex. Nothing here touches a
//! coefficient: every figure is a function of the leading monomials and the standard monomials.

use std::collections::HashMap;

use crate::Monomial;

/// The shape of the `K[y]`-module `I ∩ R_T` for `T` the standard monomials free of `y`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ModuleCensus {
    /// `D`, the number of standard monomials.
    pub dimension: usize,
    /// `t`, the order of the polynomial matrix: the standard monomials not divisible by `y`
    /// (the paper's Theorem 5.2).
    pub module_rank: usize,
    /// Minimal leading monomials divisible by `y`. Equal to `module_rank` when `stable`
    /// (Corollary 5.4), and then those basis elements are the matrix.
    pub last_variable_leaders: usize,
    /// The paper's `S(lt(I))`: for every leading monomial `μ` divisible by `y` and every other
    /// variable `x_i`, `x_i μ / y` is again a leading monomial of the ideal.
    pub stable: bool,
    /// Every variable but `y` is standard, which shape position needs for the lex basis to lie in
    /// the module (Lemma 5.1).
    pub other_variables_standard: bool,
    /// The matrix's column degrees `e_i`, ascending: the length of each `y`-chain of standard
    /// monomials. They sum to `D`.
    pub column_degrees: Vec<u32>,
}

impl ModuleCensus {
    /// The largest column degree, 0 for the unit ideal.
    pub fn max_column_degree(&self) -> u32 {
        self.column_degrees.last().copied().unwrap_or(0)
    }
}

fn divides<const N: usize>(a: &Monomial<N>, b: &Monomial<N>) -> bool {
    a.exponents().iter().zip(b.exponents()).all(|(x, y)| x <= y)
}

/// The census of the staircase with leading monomials `leading` and standard monomials `standard`.
///
/// `leading` may hold non-minimal generators; `standard` must be exactly the monomials no element
/// of `leading` divides, as [`super::QuotientBasis::monomials`] returns them.
pub fn module_census<const N: usize>(
    leading: &[Monomial<N>],
    standard: &[Monomial<N>],
) -> ModuleCensus {
    assert!(N > 0, "a census needs a last variable");
    let last = N - 1;
    let minimal: Vec<&Monomial<N>> = leading
        .iter()
        .enumerate()
        .filter(|(i, m)| {
            !leading
                .iter()
                .enumerate()
                .any(|(j, other)| j != *i && divides(other, m) && (other != *m || j < *i))
        })
        .map(|(_, m)| m)
        .collect();
    let leaders: Vec<&Monomial<N>> = minimal
        .iter()
        .copied()
        .filter(|m| m.exponents()[last] > 0)
        .collect();
    // Lemma 2.2: the statement holds for the whole monomial ideal exactly when it holds for the
    // minimal generators.
    let stable = leaders.iter().all(|m| {
        (0..last).all(|i| {
            let mut exponents = [0u32; N];
            exponents.copy_from_slice(m.exponents());
            exponents[last] -= 1;
            exponents[i] += 1;
            let swapped = Monomial::new(&exponents);
            minimal.iter().any(|g| divides(g, &swapped))
        })
    });
    let mut chains: HashMap<Monomial<N>, u32> = HashMap::new();
    for m in standard {
        let mut exponents = [0u32; N];
        exponents.copy_from_slice(m.exponents());
        exponents[last] = 0;
        *chains.entry(Monomial::new(&exponents)).or_insert(0) += 1;
    }
    let other_variables_standard =
        (0..last).all(|i| chains.contains_key(&Monomial::univariate(i, 1)));
    let mut column_degrees: Vec<u32> = chains.into_values().collect();
    column_degrees.sort_unstable();
    ModuleCensus {
        dimension: standard.len(),
        module_rank: column_degrees.len(),
        last_variable_leaders: leaders.len(),
        stable,
        other_variables_standard,
        column_degrees,
    }
}

#[cfg(test)]
mod tests {
    use super::{divides, module_census};
    use crate::Monomial;

    /// Every monomial of a box that no element of `leading` divides.
    fn standard<const N: usize>(leading: &[Monomial<N>], bound: u32) -> Vec<Monomial<N>> {
        let mut out = vec![];
        let mut exponents = [0u32; N];
        loop {
            let m = Monomial::new(&exponents);
            if !leading.iter().any(|g| divides(g, &m)) {
                out.push(m);
            }
            let Some(i) = (0..N).find(|i| exponents[*i] < bound) else {
                return out;
            };
            exponents[i] += 1;
            exponents[..i].fill(0);
        }
    }

    // The paper's Example 2.3 is stable with t = 3, D = 8 and column degrees (2, 2, 4).
    #[test]
    fn the_papers_example_is_stable_with_rank_three() {
        // (x1, x2, y): y^4, x2 y^2, x1 y^2, x2^2, x1 x2, x1^2.
        let leading: Vec<Monomial<3>> = [
            [0, 0, 4],
            [0, 1, 2],
            [1, 0, 2],
            [0, 2, 0],
            [1, 1, 0],
            [2, 0, 0],
        ]
        .iter()
        .map(|e| Monomial::new(e))
        .collect();
        let census = module_census(&leading, &standard(&leading, 4));
        assert_eq!(census.dimension, 8);
        assert_eq!(census.module_rank, 3);
        assert_eq!(census.last_variable_leaders, 3);
        assert!(census.stable);
        assert!(census.other_variables_standard);
        assert_eq!(census.column_degrees, vec![2, 2, 4]);
        assert_eq!(census.max_column_degree(), 4);
    }

    // A box staircase is not stable, and its rank is D / d although one leader is divisible by y.
    #[test]
    fn a_box_staircase_is_unstable_with_rank_d_over_degree() {
        let leading: Vec<Monomial<3>> = (0..3).map(|i| Monomial::univariate(i, 5)).collect();
        let census = module_census(&leading, &standard(&leading, 5));
        assert_eq!(census.dimension, 125);
        assert_eq!(census.module_rank, 25);
        assert_eq!(census.last_variable_leaders, 1);
        assert!(!census.stable);
        assert!(census.other_variables_standard);
        assert_eq!(census.column_degrees, vec![5; 25]);
    }

    // A lex-shaped staircase has rank 1 and reports that the other variables are not standard.
    #[test]
    fn a_shape_staircase_has_rank_one_and_no_standard_variables() {
        let leading = [Monomial::<2>::univariate(0, 1), Monomial::univariate(1, 7)];
        let census = module_census(&leading, &standard(&leading, 7));
        assert_eq!(census.dimension, 7);
        assert_eq!(census.module_rank, 1);
        assert!(census.stable);
        assert!(!census.other_variables_standard);
        assert_eq!(census.column_degrees, vec![7]);
    }

    // Non-minimal and repeated generators change nothing.
    #[test]
    fn redundant_generators_do_not_change_the_census() {
        let minimal: Vec<Monomial<2>> = [[2, 0], [1, 1], [0, 2]]
            .iter()
            .map(|e| Monomial::new(e))
            .collect();
        let mut redundant = minimal.clone();
        redundant.push(Monomial::new(&[1, 2]));
        redundant.push(Monomial::new(&[0, 2]));
        let cells = standard(&minimal, 2);
        assert_eq!(
            module_census(&minimal, &cells),
            module_census(&redundant, &cells)
        );
        assert_eq!(module_census(&redundant, &cells).last_variable_leaders, 2);
    }
}
