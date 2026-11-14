//! The bigraded Hilbert series of a monomial ideal, for systems whose variables split into two
//! blocks — bilinear and bihomogeneous systems, where the single grading loses the structure.
//!
//! The variables `x_0 … x_{k−1}` carry bidegree `(1, 0)` and `x_k … x_{N−1}` carry `(0, 1)`. For a
//! bihomogeneous ideal `I` the quotient splits into pieces `(R/I)_{(a, b)}`, and its series is
//!
//! ```text
//! HS(s, t) = numerator(s, t) / ((1 − s)^k · (1 − t)^(N − k))
//! ```
//!
//! with an integer numerator. It is computed by the parent module's recursion unchanged, with the
//! `z`-shifts replaced by `s`- or `t`-shifts according to the pivot's block: the exact sequence
//! `0 → R/(L : x) → R/L → R/(L + <x>) → 0` is bigraded as well as graded.
//!
//! Setting `s = t = z` recovers the single-graded series exactly ([`BigradedHilbertSeries::total`]).
//! The converse fails, which is why this object exists: `(1 − st)` and `(1 − s²)` both specialize to
//! `(1 − z²)`, so a bilinear and a quadratic generator are indistinguishable once the grading is
//! collapsed (#207).

use crate::{poly::MonomialOrder, FiniteField, Monomial, MultivariatePolynomial};

use super::{
    binomial, check_length, minimalize, pairwise_coprime, HilbertError, HilbertSeries,
    DEFAULT_COEFFICIENT_BUDGET, DEFAULT_NODE_BUDGET,
};

/// A dense polynomial in `s` and `t`: `coefficients[i * columns + j]` is the coefficient of
/// `s^i t^j`.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Bivariate {
    rows: usize,
    columns: usize,
    coefficients: Vec<i128>,
}

impl Bivariate {
    fn one() -> Self {
        Self {
            rows: 1,
            columns: 1,
            coefficients: vec![1],
        }
    }

    fn get(&self, i: usize, j: usize) -> i128 {
        if i < self.rows && j < self.columns {
            self.coefficients[i * self.columns + j]
        } else {
            0
        }
    }

    /// A zero polynomial with room for `s^(rows−1) t^(columns−1)`, refused past the budget before
    /// it is allocated.
    fn with_shape(rows: u64, columns: u64) -> Result<Self, HilbertError> {
        let cells = rows.checked_mul(columns).ok_or(HilbertError::Overflow)?;
        check_length(cells, DEFAULT_COEFFICIENT_BUDGET)?;
        Ok(Self {
            rows: rows as usize,
            columns: columns as usize,
            coefficients: vec![0; cells as usize],
        })
    }

    /// `self + sign · s^di t^dj · other`, into a polynomial large enough for both.
    fn add_shifted(
        &self,
        other: &Self,
        di: u64,
        dj: u64,
        sign: i128,
    ) -> Result<Self, HilbertError> {
        let rows = (self.rows as u64).max((other.rows as u64).saturating_add(di));
        let columns = (self.columns as u64).max((other.columns as u64).saturating_add(dj));
        let mut result = Self::with_shape(rows, columns)?;
        for i in 0..self.rows {
            for j in 0..self.columns {
                result.coefficients[i * result.columns + j] = self.get(i, j);
            }
        }
        let (di, dj) = (di as usize, dj as usize);
        for i in 0..other.rows {
            for j in 0..other.columns {
                let cell = &mut result.coefficients[(i + di) * result.columns + (j + dj)];
                *cell = other
                    .get(i, j)
                    .checked_mul(sign)
                    .and_then(|term| cell.checked_add(term))
                    .ok_or(HilbertError::Overflow)?;
            }
        }
        Ok(result)
    }

    /// `self · (1 − s^di t^dj)`.
    fn times_one_minus(&self, di: u64, dj: u64) -> Result<Self, HilbertError> {
        self.add_shifted(self, di, dj, -1)
    }
}

/// A bigraded Hilbert series `numerator(s, t) / ((1 − s)^first · (1 − t)^second)`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BigradedHilbertSeries {
    numerator: Bivariate,
    first: usize,
    second: usize,
}

impl BigradedHilbertSeries {
    /// The exact bigraded series of `R/<generators>` for a **monomial** ideal, where the first
    /// `split` variables have bidegree `(1, 0)` and the rest `(0, 1)`, under
    /// [`DEFAULT_NODE_BUDGET`].
    ///
    /// # Panics
    /// If `split > N`.
    ///
    /// # Errors
    /// As [`HilbertSeries::of_monomial_ideal`].
    pub fn of_monomial_ideal<const N: usize>(
        generators: &[Monomial<N>],
        split: usize,
    ) -> Result<Self, HilbertError> {
        Self::of_monomial_ideal_within(generators, split, DEFAULT_NODE_BUDGET)
    }

    /// As [`BigradedHilbertSeries::of_monomial_ideal`], under the given node budget.
    ///
    /// # Panics
    /// If `split > N`.
    pub fn of_monomial_ideal_within<const N: usize>(
        generators: &[Monomial<N>],
        split: usize,
        budget: usize,
    ) -> Result<Self, HilbertError> {
        assert!(split <= N, "split {} exceeds the {} variables", split, N);
        let minimal = minimalize(generators);
        let mut nodes = 0;
        let numerator = numerator_of(&minimal, split, budget, &mut nodes)?;
        Ok(Self {
            numerator,
            first: split,
            second: N - split,
        })
    }

    /// The bigraded series of the ideal a Gröbner basis generates, from its leading monomials.
    ///
    /// Correct for a **bihomogeneous** ideal under the given split, whose reduced basis is itself
    /// bihomogeneous. For any other ideal it is the series of the leading-term ideal, as with
    /// [`HilbertSeries::of_basis`].
    ///
    /// # Panics
    /// If `split > N`.
    ///
    /// # Errors
    /// As [`BigradedHilbertSeries::of_monomial_ideal`].
    pub fn of_basis<const N: usize, F: FiniteField>(
        basis: &[MultivariatePolynomial<N, F>],
        order: MonomialOrder,
        split: usize,
    ) -> Result<Self, HilbertError> {
        let leads: Vec<Monomial<N>> = basis
            .iter()
            .filter(|p| !p.is_zero())
            .map(|p| p.leading_monomial(order))
            .collect();
        Self::of_monomial_ideal(&leads, split)
    }

    /// The numerator's coefficient of `s^i t^j`.
    pub fn numerator_coefficient(&self, i: usize, j: usize) -> i128 {
        self.numerator.get(i, j)
    }

    /// The numbers of variables in each block, `(first, second)`.
    pub fn blocks(&self) -> (usize, usize) {
        (self.first, self.second)
    }

    /// `H(a, b) = dim_F (R/I)_{(a, b)}`.
    ///
    /// `Σ_{i,j} numerator[i][j] · M(first, a − i) · M(second, b − j)`, where `M(n, d)` is the
    /// number of degree-`d` monomials in `n` variables — the coefficients of the two denominators.
    ///
    /// # Errors
    /// [`HilbertError::Overflow`] if a product or the sum exceeds `i128`.
    pub fn function(&self, a: u64, b: u64) -> Result<i128, HilbertError> {
        let mut total: i128 = 0;
        for i in 0..self.numerator.rows.min(a.saturating_add(1) as usize) {
            for j in 0..self.numerator.columns.min(b.saturating_add(1) as usize) {
                let coefficient = self.numerator.get(i, j);
                if coefficient == 0 {
                    continue;
                }
                let weight = monomials(self.first, a - i as u64)?
                    .checked_mul(monomials(self.second, b - j as u64)?)
                    .ok_or(HilbertError::Overflow)?;
                total = coefficient
                    .checked_mul(weight)
                    .and_then(|term| total.checked_add(term))
                    .ok_or(HilbertError::Overflow)?;
            }
        }
        Ok(total)
    }

    /// The single-graded series, by setting `s = t = z`.
    ///
    /// # Errors
    /// [`HilbertError::Overflow`] if a collected coefficient exceeds `i128`.
    pub fn total(&self) -> Result<HilbertSeries, HilbertError> {
        let length = self.numerator.rows + self.numerator.columns - 1;
        let mut numerator = vec![0i128; length];
        for i in 0..self.numerator.rows {
            for j in 0..self.numerator.columns {
                numerator[i + j] = numerator[i + j]
                    .checked_add(self.numerator.get(i, j))
                    .ok_or(HilbertError::Overflow)?;
            }
        }
        // Trailing zeros are not part of the parent's canonical form, which is the recursion's
        // natural length; strip them so equal series compare equal.
        while numerator.len() > 1 && numerator.last() == Some(&0) {
            numerator.pop();
        }
        Ok(HilbertSeries {
            numerator,
            variables: self.first + self.second,
        })
    }
}

/// `M(n, d)`: degree-`d` monomials in `n` variables, with `F[]` having exactly one, in degree 0.
fn monomials(variables: usize, degree: u64) -> Result<i128, HilbertError> {
    if variables == 0 {
        return Ok(i128::from(degree == 0));
    }
    binomial(degree + variables as u64 - 1, variables as u64 - 1)
}

/// The bidegree of `m` under `split`.
fn bidegree<const N: usize>(m: &Monomial<N>, split: usize) -> (u64, u64) {
    let (left, right) = m.exponents().split_at(split);
    let sum = |e: &[u32]| e.iter().map(|x| *x as u64).sum();
    (sum(left), sum(right))
}

/// The bigraded analogue of the parent's `numerator_of`, with the same pivot and the same
/// termination argument: only the shifts are bigraded.
fn numerator_of<const N: usize>(
    minimal: &[Monomial<N>],
    split: usize,
    budget: usize,
    nodes: &mut usize,
) -> Result<Bivariate, HilbertError> {
    *nodes += 1;
    if *nodes > budget {
        return Err(HilbertError::TooManyNodes { limit: budget });
    }

    if minimal.is_empty() {
        return Ok(Bivariate::one());
    }

    if pairwise_coprime(minimal) {
        let mut numerator = Bivariate::one();
        for generator in minimal {
            let (di, dj) = bidegree(generator, split);
            numerator = numerator.times_one_minus(di, dj)?;
        }
        return Ok(numerator);
    }

    let mut occurrences = [0usize; N];
    for generator in minimal {
        for (variable, exponent) in generator.exponents().iter().enumerate() {
            if *exponent > 0 {
                occurrences[variable] += 1;
            }
        }
    }
    let pivot = (0..N)
        .max_by_key(|variable| occurrences[*variable])
        .expect("a non-empty generating set has a variable");
    let (di, dj) = if pivot < split { (1, 0) } else { (0, 1) };

    let untouched: Vec<Monomial<N>> = minimal
        .iter()
        .filter(|g| g.exponents()[pivot] == 0)
        .copied()
        .collect();
    let sum = numerator_of(&untouched, split, budget, nodes)?.times_one_minus(di, dj)?;

    let quotient: Vec<Monomial<N>> = minimal
        .iter()
        .map(|g| {
            let mut exponents = [0u32; N];
            exponents.copy_from_slice(g.exponents());
            exponents[pivot] = exponents[pivot].saturating_sub(1);
            Monomial::new(&exponents)
        })
        .collect();
    let colon = numerator_of(&minimalize(&quotient), split, budget, nodes)?;

    sum.add_shifted(&colon, di, dj, 1)
}

#[cfg(test)]
mod tests {
    use rand::{rngs::StdRng, SeedableRng};

    use super::BigradedHilbertSeries;
    use crate::{
        fields::Zp2147483647,
        grobner::{f4, hilbert::HilbertSeries},
        poly::MonomialOrder,
        FiniteField, Monomial, MultivariatePolynomial,
    };

    type F = Zp2147483647;

    fn monomials<const N: usize>(exponents: &[[u32; N]]) -> Vec<Monomial<N>> {
        exponents.iter().map(|e| Monomial::new(e)).collect()
    }

    /// Small monomial ideals in `F[x0, x1 | y0, y1]`, with enough shared variables to recurse.
    fn cases() -> Vec<Vec<[u32; 4]>> {
        vec![
            vec![],
            vec![[1, 0, 1, 0]],
            vec![[2, 0, 0, 0], [0, 0, 0, 3]],
            vec![[1, 0, 1, 0], [1, 0, 0, 1], [0, 1, 1, 0]],
            vec![[2, 1, 0, 0], [1, 0, 2, 0], [0, 1, 1, 1], [0, 0, 0, 2]],
            vec![[1, 1, 1, 1]],
            vec![
                [3, 0, 0, 0],
                [0, 3, 0, 0],
                [0, 0, 3, 0],
                [0, 0, 0, 3],
                [1, 1, 1, 1],
            ],
            vec![[1, 0, 0, 0], [0, 0, 1, 0]],
        ]
    }

    /// `H(a, b)` equals the count of standard monomials of bidegree `(a, b)`, found by enumeration.
    #[test]
    fn test_the_bigraded_function_agrees_with_enumeration() {
        for exponents in cases() {
            let generators = monomials::<4>(&exponents);
            let series =
                BigradedHilbertSeries::of_monomial_ideal(&generators, 2).expect("within budget");
            for a in 0..=6u32 {
                for b in 0..=6u32 {
                    let mut counted = 0i128;
                    for x0 in 0..=a {
                        for y0 in 0..=b {
                            let m = Monomial::<4>::new(&[x0, a - x0, y0, b - y0]);
                            if !generators.iter().any(|g| super::super::divides(g, &m)) {
                                counted += 1;
                            }
                        }
                    }
                    assert_eq!(
                        series.function(a as u64, b as u64).unwrap(),
                        counted,
                        "{:?} at bidegree ({}, {})",
                        exponents,
                        a,
                        b
                    );
                }
            }
        }
    }

    /// Setting `s = t = z` gives exactly the single-graded series, at every split.
    #[test]
    fn test_the_total_series_is_the_single_graded_one() {
        for exponents in cases() {
            let generators = monomials::<4>(&exponents);
            let single = HilbertSeries::of_monomial_ideal(&generators).unwrap();
            for split in 0..=4 {
                let bigraded =
                    BigradedHilbertSeries::of_monomial_ideal(&generators, split).unwrap();
                assert_eq!(
                    bigraded.total().unwrap(),
                    single,
                    "{:?} at split {}",
                    exponents,
                    split
                );
            }
        }
    }

    /// The bigrading separates `x·y` from `x²`, which the single grading cannot.
    #[test]
    fn test_the_bigrading_distinguishes_what_the_total_degree_conflates() {
        let bilinear = BigradedHilbertSeries::of_monomial_ideal(&monomials::<2>(&[[1, 1]]), 1)
            .expect("principal");
        let quadratic = BigradedHilbertSeries::of_monomial_ideal(&monomials::<2>(&[[2, 0]]), 1)
            .expect("principal");
        assert_eq!(bilinear.numerator_coefficient(1, 1), -1, "1 - st");
        assert_eq!(quadratic.numerator_coefficient(2, 0), -1, "1 - s^2");
        assert_ne!(bilinear, quadratic);
        assert_eq!(bilinear.total().unwrap(), quadratic.total().unwrap());
        assert_eq!(bilinear.blocks(), (1, 1));
    }

    /// Degenerate splits put every variable in one block, and the unit ideal gives zero.
    #[test]
    fn test_degenerate_splits_and_the_unit_ideal() {
        let whole = BigradedHilbertSeries::of_monomial_ideal::<3>(&[], 0).unwrap();
        assert_eq!(whole.function(0, 4).unwrap(), 15, "binomial(4 + 2, 2)");
        assert_eq!(whole.function(1, 4).unwrap(), 0, "no first-block variables");
        let unit =
            BigradedHilbertSeries::of_monomial_ideal(&[Monomial::<3>::new(&[0, 0, 0])], 2).unwrap();
        assert_eq!(unit.function(0, 0).unwrap(), 0);
        assert_eq!(unit.function(2, 1).unwrap(), 0);
    }

    /// The node budget is enforced, as in the single-graded recursion.
    #[test]
    fn test_the_node_budget_is_enforced() {
        let generators = monomials::<4>(&cases()[6]);
        assert_eq!(
            BigradedHilbertSeries::of_monomial_ideal_within(&generators, 2, 1),
            Err(super::HilbertError::TooManyNodes { limit: 1 })
        );
    }

    /// `m ≤ 3` generic bilinear forms in `F[x0..x2 | y0..y2]` form a regular sequence, so the
    /// computed basis must give the Koszul series `(1 − st)^m / ((1 − s)^3 (1 − t)^3)`.
    ///
    /// The independent derivation: the ideal has height `m`, because the components `x = 0` and
    /// `y = 0` of its cone have codimension 3, and a height-`m` ideal on `m` homogeneous
    /// generators is a complete intersection. The basis comes from F4, not from this module.
    #[test]
    fn test_a_generic_bilinear_regular_sequence_has_the_koszul_series() {
        let mut rng = StdRng::seed_from_u64(207);
        let mut coefficient = || F::random(&mut rng);
        for m in 1..=3usize {
            let system: Vec<MultivariatePolynomial<6, F>> = (0..m)
                .map(|_| {
                    let mut terms: Vec<(Monomial<6>, F)> = Vec::new();
                    for i in 0..3 {
                        for j in 3..6 {
                            let mut e = [0u32; 6];
                            e[i] = 1;
                            e[j] = 1;
                            terms.push((Monomial::new(&e), coefficient()));
                        }
                    }
                    MultivariatePolynomial::new(&terms)
                })
                .collect();
            let order = MonomialOrder::GradedReverseLexicographic;
            let basis = f4(&system, order).expect("within limits");
            let series = BigradedHilbertSeries::of_basis(&basis, order, 3).expect("within budget");

            // (1 - st)^m expanded: binomial(m, k) (-1)^k on the diagonal s^k t^k.
            let koszul = |a: u64, b: u64| -> i128 {
                (0..=m as u64)
                    .filter(|k| *k <= a && *k <= b)
                    .map(|k| {
                        let sign = if k % 2 == 0 { 1 } else { -1 };
                        sign * super::binomial(m as u64, k).unwrap()
                            * super::monomials(3, a - k).unwrap()
                            * super::monomials(3, b - k).unwrap()
                    })
                    .sum()
            };
            for a in 0..=5 {
                for b in 0..=5 {
                    assert_eq!(
                        series.function(a, b).unwrap(),
                        koszul(a, b),
                        "m = {} at bidegree ({}, {})",
                        m,
                        a,
                        b
                    );
                }
            }
        }
    }
}
