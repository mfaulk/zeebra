//! The balanced product tree of `prod (x - x_i)`, and the two algorithms built on it.
//!
//! #162 stage 2. Stage 1 took arbitrary-point interpolation from `O(n^3)` to `O(n^2)` by building
//! the numerator product once; this takes it below quadratic, and adds the multipoint evaluation
//! that `fft::evaluate` cannot do because its domain must be geometric.
//!
//! # Why this could not be written until #193
//!
//! Multipoint evaluation by simultaneous remaindering costs, summed over the tree's levels,
//!
//! ```text
//!   sum_k 2^k * D(n / 2^k)
//! ```
//!
//! where `D(d)` is the cost of dividing by a modulus of degree `d`. With `D(d) = d^2` that sum is
//! `n^2 * sum_k 2^-k = O(n^2)` — the top level alone is `(n/2)^2` twice — so the tree bought a
//! constant factor of about two over `n` Horner evaluations and **did not move the exponent at
//! all**. The whole construction was asymptotically pointless while division was long division.
//!
//! #193 made division `O(M(d))`, and `M` is Karatsuba since #231, so the sum telescopes to
//! `O(M(n)) = O(n^1.585)`. Every node's division is the balanced shape #193's crossover is read
//! off — a modulus of degree `d` into a remainder of degree below `2d` — so the top levels take the
//! Newton route and the small nodes near the leaves fall back to long division on their own.
//!
//! **The exponent this reaches is the multiplication exponent, not 1.** #162's acceptance asked for
//! "near 1", which needs the transform; the transform needs a `2^k`-th root of unity, hence
//! [`crate::KnownOrder`] and randomness, which the same issue's Scope rules out ("`KnownOrder` is
//! not required ... the bound should stay `FiniteField`"). #559 settled those competing
//! requirements in favour of the bound: the criterion now asks for the multiplication exponent,
//! which the measured ~1.6 meets. Everything here needs nothing of the field but a ring. #606 holds
//! the deferred `KnownOrder` specialization, which would have to sit beside this path rather than
//! replace it — Mersenne-31 has two-adicity 1, so Karatsuba is the only route that field has.
//!
//! # The three algorithms
//!
//! Writing `M_v` for the product at node `v`:
//!
//! - **Build.** Leaves are `x - x_i`; a node is the product of its children. `sum_k 2^k M(n/2^k)`
//!   is geometric in Karatsuba's exponent, so the whole build is `O(M(n))`.
//! - **Evaluation.** Push `f mod M_v` down: a child's remainder is the parent's remainder modulo
//!   the child's product, because `M_child` divides `M_parent`. At a leaf the modulus is linear, so
//!   the remainder is the constant `f(x_i)`.
//! - **Interpolation**, as the transposed form. With `c_i = y_i / M'(x_i)` — and `M'(x_i)` is
//!   `prod_{j != i} (x_i - x_j)`, so one evaluation of the derivative supplies every denominator —
//!   the interpolant is `sum_i c_i * M/(x - x_i)`, which the tree accumulates upward as
//!   `T_parent = T_left * M_right + T_right * M_left`.
//!
//! The derivative is the **formal** one, which matters when `n` reaches the characteristic: over
//! GF(7) with seven points `M` has degree 7 and `M'` loses its leading term. The identity survives
//! anyway, because `M'(x_i) = prod_{j != i}(x_i - x_j)` holds in any commutative ring — every other
//! term of `M' = sum_k prod_{j != k}(x - x_j)` carries the factor `(x_i - x_i)`.

use crate::{
    fields::batch_invert,
    poly::univariate::{div_with_remainder::div_with_remainder, Polynomial, UnivariatePolynomial},
    FiniteField,
};

/// Point count above which [`interpolate`] builds a tree, for an element of at most 4 bytes.
///
/// Measured by `examples/subproduct_crossover.rs`, not derived: the largest swept `n` at which the
/// tree does **not** win by more than 10%. The tree cannot pay at small `n` because it allocates
/// `O(n log n)` polynomial objects where the quadratic form works in two flat arrays — measured at
/// 37 bytes per point against 5 — and because its divisions only reach #193's Newton route once a
/// node's modulus passes *that* crossover, 1024 coefficients at this width.
pub(crate) const TREE_CROSSOVER_32_BIT: usize = 64;

/// The same, for an element of 5 to 8 bytes.
pub(crate) const TREE_CROSSOVER_64_BIT: usize = 128;

/// The same, for an element wider than 8 bytes. Measured over BN254 `Fr`; the 16-byte
/// `PrimeFieldElement128` is not separately measured and takes this figure.
pub(crate) const TREE_CROSSOVER_WIDE: usize = 128;

/// The measured crossover for `F`, the single source of truth for the dispatch.
///
/// Three tiers for the same reason `karatsuba_base_case` has three — but, unlike that base case's
/// 12x fall across these widths and #193's 8x, this crossover is **nearly flat**: 64 at 4 bytes
/// and 128 at every width above it. Both arms' cost is field multiplications in roughly the same
/// proportion, so widening the element scales the two sides together and the crossing barely
/// moves. The 4-byte tier is kept because it genuinely differs, not for symmetry with the others.
pub(crate) fn tree_crossover<F: FiniteField>() -> usize {
    match std::mem::size_of::<F>() {
        0..=4 => TREE_CROSSOVER_32_BIT,
        5..=8 => TREE_CROSSOVER_64_BIT,
        _ => TREE_CROSSOVER_WIDE,
    }
}

/// The balanced binary tree of the products of `x - x_i`.
///
/// Levels are stored leaves-first in one `Vec` per level rather than as nodes with child pointers:
/// both algorithms sweep a whole level at a time, and a node's children are at `2j` and `2j + 1` of
/// the level below, so the structure is the indexing and costs nothing to represent.
///
/// An odd node at some level is **carried up unchanged** rather than paired with a padding
/// polynomial. That keeps every node a product of exactly the leaves beneath it, which is the
/// invariant both algorithms rest on; the cost is that such a node's division is a no-op, which is
/// cheaper than multiplying by a padding factor would have been.
pub(crate) struct SubproductTree<F: FiniteField> {
    /// `levels[0][i]` is `x - x_i`; the last level holds the single node `M`.
    levels: Vec<Vec<UnivariatePolynomial<F>>>,
}

impl<F: FiniteField> SubproductTree<F> {
    /// Build the tree over the given abscissae.
    ///
    /// # Panics
    /// If `points` is empty. Duplicate abscissae are **not** rejected here: the tree is well
    /// defined over them and [`evaluate`](Self::evaluate) is still correct; it is interpolation
    /// that cannot proceed, and [`interpolate`] rejects them before reaching this.
    pub(crate) fn build(points: &[F]) -> Self {
        assert!(
            !points.is_empty(),
            "a subproduct tree needs at least one point"
        );

        let leaves: Vec<UnivariatePolynomial<F>> = points
            .iter()
            .map(|x| UnivariatePolynomial::new(&[x.neg(), F::one()]))
            .collect();
        let mut levels = vec![leaves];

        while levels.last().expect("the leaf level was just pushed").len() > 1 {
            let below = levels.last().expect("the loop condition read it");
            let mut above = Vec::with_capacity(below.len().div_ceil(2));
            let mut index = 0;
            while index < below.len() {
                match below.get(index + 1) {
                    Some(right) => above.push(&below[index] * right),
                    None => above.push(below[index].clone()),
                }
                index += 2;
            }
            levels.push(above);
        }

        Self { levels }
    }

    /// `M = prod (x - x_i)`, the root.
    pub(crate) fn root(&self) -> &UnivariatePolynomial<F> {
        &self.levels.last().expect("a tree always has a leaf level")[0]
    }

    /// `f` evaluated at every abscissa, in the order they were supplied.
    ///
    /// Simultaneous remaindering: a child's remainder is the parent's remainder modulo the child's
    /// product, which is sound because `M_child` divides `M_parent`. The initial reduction by `M`
    /// is what bounds every later division's dividend, and is a no-op when `deg f < n`.
    pub(crate) fn evaluate(&self, f: &UnivariatePolynomial<F>) -> Vec<F> {
        let top = self.levels.len() - 1;
        let mut current = vec![div_with_remainder(f, self.root()).1];

        for level in (0..top).rev() {
            let below = &self.levels[level];
            let mut next = Vec::with_capacity(below.len());
            for (node, remainder) in current.iter().enumerate() {
                let left = 2 * node;
                next.push(div_with_remainder(remainder, &below[left]).1);
                if let Some(right) = below.get(left + 1) {
                    next.push(div_with_remainder(remainder, right).1);
                }
            }
            current = next;
        }

        // Every leaf modulus is linear, so each remainder is a constant — and the zero polynomial
        // is stored as `[0]`, so `coefficients()[0]` is the value in every case.
        current
            .iter()
            .map(|remainder| remainder.coefficients()[0])
            .collect()
    }

    /// `sum_i c_i * M/(x - x_i)`, accumulated upward.
    ///
    /// `T_parent = T_left * M_right + T_right * M_left`, which at a pair of leaves is
    /// `c_j (x - x_{j+1}) + c_{j+1} (x - x_j)` and at the root is the whole sum.
    ///
    /// # Panics
    /// If `scaled` does not have one entry per leaf.
    pub(crate) fn combine(&self, scaled: &[F]) -> UnivariatePolynomial<F> {
        assert_eq!(
            scaled.len(),
            self.levels[0].len(),
            "the coefficient vector must have one entry per abscissa"
        );

        let mut current: Vec<UnivariatePolynomial<F>> = scaled
            .iter()
            .map(|c| UnivariatePolynomial::lift(c))
            .collect();

        for level in 0..(self.levels.len() - 1) {
            let below = &self.levels[level];
            let mut above = Vec::with_capacity(current.len().div_ceil(2));
            let mut index = 0;
            while index < current.len() {
                match current.get(index + 1) {
                    Some(right) => above
                        .push(&(&current[index] * &below[index + 1]) + &(right * &below[index])),
                    None => above.push(current[index].clone()),
                }
                index += 2;
            }
            current = above;
        }

        current
            .pop()
            .expect("the accumulation ends with the root's single node")
    }
}

/// The formal derivative.
///
/// Formal rather than "the derivative over a field of characteristic zero": a term's coefficient is
/// multiplied by its exponent *in `F`*, so over GF(7) the `x^7` term vanishes. That is the right
/// thing here — see the module comment on why `M'(x_i)` is still the product of differences.
pub(crate) fn derivative<F: FiniteField>(
    polynomial: &UnivariatePolynomial<F>,
) -> UnivariatePolynomial<F> {
    let coefficients = polynomial.coefficients();
    if coefficients.len() <= 1 {
        return UnivariatePolynomial::zero();
    }
    let derived: Vec<F> = coefficients
        .iter()
        .enumerate()
        .skip(1)
        .map(|(exponent, coefficient)| *coefficient * F::new(exponent as u64))
        .collect();
    UnivariatePolynomial::new(&derived)
}

/// `f` evaluated at every point of an arbitrary set, in `O(M(n) log n)` rather than `O(n^2)`.
///
/// This is what `fft::evaluate` cannot do: the transform's domain must be the geometric
/// `1, w, w^2, ...`, and an evaluation–interpolation resultant (#82) needs an arbitrary set.
///
/// Dispatches on the same measured crossover [`interpolate`] uses, since the cost that decides it
/// is the tree's; below it, Horner at each point.
///
/// # Panics
/// If `points` is empty.
pub fn multipoint_evaluate<F: FiniteField>(f: &UnivariatePolynomial<F>, points: &[F]) -> Vec<F> {
    assert!(!points.is_empty(), "nothing to evaluate at");
    if points.len() <= tree_crossover::<F>() {
        return points.iter().map(|x| f.eval(x)).collect();
    }
    SubproductTree::build(points).evaluate(f)
}

/// Interpolate through `points` using the tree. `O(M(n) log n)`.
///
/// Callers should reach this through [`super::lagrange_interpolation::interpolate`], which
/// dispatches on the measured crossover; this is the arm, exposed so the two can be
/// differentially tested at sizes the shipped dispatch would not send here.
///
/// # Panics
/// If `points` is empty, or if two points share an x coordinate.
pub(crate) fn interpolate<F: FiniteField>(points: &[(F, F)]) -> UnivariatePolynomial<F> {
    assert!(!points.is_empty(), "nothing to interpolate");
    super::lagrange_interpolation::assert_distinct_abscissae(points);

    let abscissae: Vec<F> = points.iter().map(|(x, _y)| *x).collect();
    let tree = SubproductTree::build(&abscissae);

    // One evaluation of M' supplies all n denominators, and `batch_invert` turns n inversions into
    // one — the same reason stage 1 forms the product rather than the quotient.
    let mut denominators = tree.evaluate(&derivative(tree.root()));
    // No entry is zero: `assert_distinct_abscissae` ruled that out, which is why `batch_invert`'s
    // leave-zeros-alone behaviour cannot silently produce a wrong answer here.
    batch_invert(&mut denominators);

    let scaled: Vec<F> = points
        .iter()
        .zip(&denominators)
        .map(|((_x, y), inverse)| *y * *inverse)
        .collect();
    tree.combine(&scaled)
}

/// [`interpolate`], reachable from an example binary so the crossover can be swept.
#[doc(hidden)]
pub fn subproduct_interpolate_unstable<F: FiniteField>(
    points: &[(F, F)],
) -> UnivariatePolynomial<F> {
    interpolate(points)
}

/// The tree arm of [`multipoint_evaluate`], with no dispatch, so the two routes can be measured
/// and differentially tested against each other at every size.
///
/// # Panics
/// If `points` is empty.
#[doc(hidden)]
pub fn subproduct_evaluate_unstable<F: FiniteField>(
    f: &UnivariatePolynomial<F>,
    points: &[F],
) -> Vec<F> {
    assert!(!points.is_empty(), "nothing to evaluate at");
    SubproductTree::build(points).evaluate(f)
}

/// [`tree_crossover`], reachable from an example binary.
#[doc(hidden)]
pub fn tree_crossover_unstable<F: FiniteField>() -> usize {
    tree_crossover::<F>()
}

#[cfg(test)]
mod tests {
    use super::{derivative, interpolate, multipoint_evaluate, tree_crossover, SubproductTree};
    use crate::{
        fields::{Bn254Fr, Mersenne31, PrimeFieldElement64, Zp7},
        identities::{One, Zero},
        poly::univariate::{
            lagrange_interpolation::interpolate_quadratic as quadratic, Polynomial,
            UnivariatePolynomial,
        },
        FiniteField,
    };
    use rand::{prelude::StdRng, SeedableRng};

    /// `n` distinct abscissae drawn from `rng`, shuffled out of order, with random ordinates.
    fn random_points<F: FiniteField>(n: usize, rng: &mut StdRng) -> Vec<(F, F)> {
        use rand::seq::SliceRandom;
        let mut xs: Vec<F> = Vec::with_capacity(n);
        let mut seen = std::collections::HashSet::new();
        while xs.len() < n {
            let x = F::random(rng);
            if seen.insert(x) {
                xs.push(x);
            }
        }
        xs.shuffle(rng);
        xs.into_iter().map(|x| (x, F::random(rng))).collect()
    }

    /// The root is the product of the linear factors, against `from_zeros`'s naive fold — which
    /// is left quadratic deliberately so that it stays an independent oracle here. #560 is the
    /// issue to make it use this tree.
    #[test]
    fn test_the_root_is_the_product_of_the_factors() {
        type F = PrimeFieldElement64<2_147_483_647>;
        let mut rng = StdRng::seed_from_u64(0x0016_2001);
        for n in 1..=40usize {
            let xs: Vec<F> = (0..n).map(|_| F::random(&mut rng)).collect();
            assert_eq!(
                *SubproductTree::build(&xs).root(),
                UnivariatePolynomial::<F>::from_zeros(&xs),
                "n = {}",
                n
            );
        }
    }

    /// Every node is the product of exactly the leaves beneath it, which is the invariant both
    /// algorithms rest on and the thing an odd-node carry could break.
    #[test]
    fn test_every_node_is_the_product_of_its_own_leaves() {
        type F = PrimeFieldElement64<2_147_483_647>;
        let mut rng = StdRng::seed_from_u64(0x0016_2002);
        // Odd sizes at several levels, where the carry happens.
        for n in [1usize, 2, 3, 5, 7, 9, 11, 13, 17, 23, 31, 33] {
            let xs: Vec<F> = (0..n).map(|_| F::random(&mut rng)).collect();
            let tree = SubproductTree::build(&xs);
            // A node at level k index j covers leaves [j * 2^k, min(n, (j+1) * 2^k)).
            for (level, nodes) in tree.levels.iter().enumerate() {
                let span = 1usize << level;
                for (index, node) in nodes.iter().enumerate() {
                    let start = index * span;
                    let end = (start + span).min(n);
                    let expected = UnivariatePolynomial::<F>::from_zeros(&xs[start..end]);
                    assert_eq!(
                        *node, expected,
                        "n = {}, level {}, node {}",
                        n, level, index
                    );
                }
            }
        }
    }

    /// Multipoint evaluation agrees with Horner at every point, over a narrow and a wide field.
    #[test]
    fn test_evaluation_agrees_with_horner() {
        fn check<F: FiniteField>(seed: u64, sizes: &[usize]) {
            let mut rng = StdRng::seed_from_u64(seed);
            for &n in sizes {
                let xs: Vec<F> = (0..n).map(|_| F::random(&mut rng)).collect();
                // Degrees above, at and below the point count, since the initial reduction by M is
                // a no-op in one case and real in another.
                for degree in [0u64, 1, (n as u64) / 2, n as u64, 2 * n as u64 + 3] {
                    let f = UnivariatePolynomial::<F>::rand(degree, &mut rng);
                    let tree = SubproductTree::build(&xs);
                    let actual = tree.evaluate(&f);
                    let expected: Vec<F> = xs.iter().map(|x| f.eval(x)).collect();
                    assert_eq!(actual, expected, "n = {}, degree = {}", n, degree);
                }
            }
        }
        check::<Mersenne31>(0x0016_2003, &[1, 2, 3, 5, 8, 13, 16, 31, 64]);
        check::<Bn254Fr>(0x0016_2004, &[1, 2, 3, 7, 16, 17]);
    }

    /// Evaluation handles repeated abscissae, which the tree is well defined over even though
    /// interpolation is not.
    #[test]
    fn test_evaluation_tolerates_repeated_abscissae() {
        type F = Zp7;
        let mut rng = StdRng::seed_from_u64(0x0016_2005);
        let xs: Vec<F> = vec![F::new(3), F::new(1), F::new(3), F::new(0), F::new(1)];
        let f = UnivariatePolynomial::<F>::rand(6, &mut rng);
        let actual = SubproductTree::build(&xs).evaluate(&f);
        let expected: Vec<F> = xs.iter().map(|x| f.eval(x)).collect();
        assert_eq!(actual, expected);
    }

    /// The formal derivative, against hand-computed cases including one where the characteristic
    /// kills the leading term.
    #[test]
    fn test_the_derivative_is_formal() {
        type F = Zp7;
        // 3 + 2x + 5x^2 -> 2 + 10x = 2 + 3x
        let p = UnivariatePolynomial::<F>::new(&[F::new(3), F::new(2), F::new(5)]);
        assert_eq!(
            derivative(&p),
            UnivariatePolynomial::new(&[F::new(2), F::new(3)])
        );
        // A constant differentiates to zero.
        assert_eq!(
            derivative(&UnivariatePolynomial::<F>::lift(&F::new(4))),
            UnivariatePolynomial::zero()
        );
        // x^7 over GF(7) differentiates to zero: 7 = 0 in F.
        let mut coefficients = vec![F::zero(); 8];
        coefficients[7] = F::one();
        assert_eq!(
            derivative(&UnivariatePolynomial::<F>::new(&coefficients)),
            UnivariatePolynomial::zero()
        );
    }

    /// `M'(x_i)` is the product of differences even when `n` reaches the characteristic, which is
    /// the case the formal derivative would be wrong for if the identity did not hold formally.
    #[test]
    fn test_the_derivative_gives_the_product_of_differences_at_the_characteristic() {
        type F = Zp7;
        // All seven elements of GF(7), so deg M = 7 and M' loses its leading term.
        let xs: Vec<F> = (0..7).map(F::new).collect();
        let tree = SubproductTree::build(&xs);
        let values = tree.evaluate(&derivative(tree.root()));
        for (i, x_i) in xs.iter().enumerate() {
            let expected = xs
                .iter()
                .enumerate()
                .filter(|(j, _)| *j != i)
                .fold(F::one(), |acc, (_, x_j)| acc * (*x_i - *x_j));
            assert_eq!(values[i], expected, "i = {}", i);
            assert!(!values[i].is_zero());
        }
    }

    /// The tree interpolation agrees with the shipped quadratic one, point for point, over a
    /// narrow field.
    #[test]
    fn test_agrees_with_the_quadratic_form_over_mersenne31() {
        let mut rng = StdRng::seed_from_u64(0x0016_2006);
        for n in 1..=64usize {
            let points = random_points::<Mersenne31>(n, &mut rng);
            assert_eq!(interpolate(&points), quadratic(points.clone()), "n = {}", n);
        }
    }

    /// And over the wide BN254 scalar field.
    #[test]
    fn test_agrees_with_the_quadratic_form_over_bn254() {
        let mut rng = StdRng::seed_from_u64(0x0016_2007);
        for n in 1..=40usize {
            let points = random_points::<Bn254Fr>(n, &mut rng);
            assert_eq!(interpolate(&points), quadratic(points.clone()), "n = {}", n);
        }
    }

    /// The interpolant passes through its points and has degree below n, which is the property
    /// rather than agreement with another implementation.
    #[test]
    fn test_the_interpolant_passes_through_its_points() {
        type F = PrimeFieldElement64<18_446_744_069_414_584_321>;
        let mut rng = StdRng::seed_from_u64(0x0016_2008);
        for n in 1..=48usize {
            let points = random_points::<F>(n, &mut rng);
            let p = interpolate(&points);
            assert!((p.degree() as usize) < n || p.is_zero(), "n = {}", n);
            for (x, y) in &points {
                assert_eq!(p.eval(x), *y, "n = {}", n);
            }
        }
    }

    /// Exhaustive over GF(7): every abscissa subset of size at most three, every ordinate
    /// assignment, agrees with the quadratic form.
    #[test]
    fn test_exhaustive_over_gf7() {
        const Q: u64 = 7;
        for mask in 1u64..(1 << Q) {
            let xs: Vec<Zp7> = (0..Q)
                .filter(|i| mask >> i & 1 == 1)
                .map(Zp7::new)
                .collect();
            let n = xs.len();
            if n > 3 {
                continue;
            }
            for code in 0..Q.pow(n as u32) {
                let points: Vec<(Zp7, Zp7)> = xs
                    .iter()
                    .enumerate()
                    .map(|(i, x)| (*x, Zp7::new(code / Q.pow(i as u32) % Q)))
                    .collect();
                assert_eq!(
                    interpolate(&points),
                    quadratic(points.clone()),
                    "mask {}, code {}",
                    mask,
                    code
                );
            }
        }
    }

    /// Duplicate abscissae are rejected deliberately, naming the repeated one — the same contract
    /// the quadratic form has, and the acceptance criterion #162 states for this stage.
    #[test]
    #[should_panic(expected = "distinct x coordinates")]
    fn test_interpolate_rejects_duplicate_abscissae() {
        type F = PrimeFieldElement64<13781>;
        let points: Vec<(F, F)> = [(0u64, 87u64), (1, 2), (1, 3)]
            .iter()
            .map(|(x, y)| (F::new(*x), F::new(*y)))
            .collect();
        let _p = interpolate(&points);
    }

    /// Rejected even when the ordinates agree, so the system is consistent and a laxer
    /// implementation would have returned an answer.
    #[test]
    #[should_panic(expected = "distinct x coordinates")]
    fn test_interpolate_rejects_a_consistent_duplicate() {
        type F = PrimeFieldElement64<13781>;
        let points: Vec<(F, F)> = [(0u64, 87u64), (1, 2), (1, 2), (4, 9)]
            .iter()
            .map(|(x, y)| (F::new(*x), F::new(*y)))
            .collect();
        let _p = interpolate(&points);
    }

    /// An empty point set panics rather than returning the zero polynomial.
    #[test]
    #[should_panic(expected = "nothing to interpolate")]
    fn test_interpolate_rejects_an_empty_point_set() {
        type F = Zp7;
        let _p = interpolate::<F>(&[]);
    }

    /// `multipoint_evaluate` agrees with Horner on both sides of its dispatch, at degrees chosen
    /// from the crossover so the test keeps covering both if the constant is re-measured.
    #[test]
    fn test_multipoint_evaluate_dispatches_to_agreeing_routes() {
        type F = PrimeFieldElement64<2_147_483_647>;
        let crossover = tree_crossover::<F>();
        let mut rng = StdRng::seed_from_u64(0x0016_2009);
        for n in [4usize, crossover, crossover + 1] {
            let xs: Vec<F> = (0..n).map(|_| F::random(&mut rng)).collect();
            let f = UnivariatePolynomial::<F>::rand(n as u64, &mut rng);
            let expected: Vec<F> = xs.iter().map(|x| f.eval(x)).collect();
            assert_eq!(multipoint_evaluate(&f, &xs), expected, "n = {}", n);
        }
    }

    /// The shipped dispatcher takes the tree above the crossover and the quadratic form below it,
    /// and both return the same interpolant. Degrees are derived from the constant, so this keeps
    /// covering both sides if it is re-measured.
    #[test]
    fn test_the_dispatcher_agrees_either_side_of_the_crossover() {
        use crate::poly::univariate::lagrange_interpolation::interpolate as dispatched;
        type F = PrimeFieldElement64<2_147_483_647>;
        let crossover = tree_crossover::<F>();
        let mut rng = StdRng::seed_from_u64(0x0016_200b);
        for n in [crossover / 2, crossover, crossover + 1, 2 * crossover] {
            let sample = random_points::<F>(n, &mut rng);
            let expected = quadratic(sample.clone());
            assert_eq!(dispatched(sample.clone()), expected, "n = {}", n);
            assert_eq!(interpolate(&sample), expected, "n = {}", n);
        }
    }

    /// All-zero ordinates give the zero polynomial, not a degree-(n-1) polynomial that is zero.
    #[test]
    fn test_all_zero_ordinates_give_the_zero_polynomial() {
        type F = PrimeFieldElement64<13781>;
        for n in 1..=12u64 {
            let points: Vec<(F, F)> = (0..n).map(|x| (F::new(x), F::zero())).collect();
            assert_eq!(interpolate(&points), UnivariatePolynomial::<F>::zero());
        }
    }

    /// A true degree far below n-1 is recovered exactly, not padded out.
    #[test]
    fn test_a_low_degree_interpolant_keeps_its_degree() {
        type F = PrimeFieldElement64<2_147_483_647>;
        let f = UnivariatePolynomial::<F>::new(&[F::new(3), F::zero(), F::new(7)]);
        let points: Vec<(F, F)> = (0..64u64)
            .map(|x| {
                let x = F::new(x);
                (x, f.eval(&x))
            })
            .collect();
        assert_eq!(interpolate(&points), f);
    }

    /// The result does not depend on the order the points are supplied in — which for a tree is a
    /// stronger statement than for the quadratic form, since the order decides the tree's shape.
    #[test]
    fn test_the_result_is_independent_of_input_order() {
        use rand::seq::SliceRandom;
        type F = PrimeFieldElement64<2_147_483_647>;
        let mut rng = StdRng::seed_from_u64(0x0016_200a);
        let mut points: Vec<(F, F)> = (0..41u64)
            .map(|x| (F::new(x), F::random(&mut rng)))
            .collect();
        let expected = interpolate(&points);
        for _ in 0..8 {
            points.shuffle(&mut rng);
            assert_eq!(interpolate(&points), expected);
        }
    }
}
