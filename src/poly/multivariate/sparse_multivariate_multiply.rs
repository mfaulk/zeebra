//! Multiplication routes for sparse multivariate polynomials, and the dispatch between them.
//!
//! The multiply this replaced pushed every pairwise term-product into one `Vec` and collected like
//! terms afterwards, so its transient was `O(|a|·|b|)` entries however few distinct monomials the
//! product had. `docs/research/resultant-elimination.md` §6.8 measured a six-round symbolic build
//! holding 57.0 GB to produce 4.3 MB of polynomial. The routes here collect *as they go*, so the
//! live set is bounded by the output instead.
//!
//! All of them end in the same drop-on-cancel step as [`SparseMultiPoly::new`]: a monomial whose
//! coefficients cancel is not a term of the product, and a surviving zero would make a polynomial
//! unequal to its own canonical form.

use std::collections::HashMap;

use crate::{
    poly::multivariate::sparse_multivariate_polynomial::SparseMultiPoly, FiniteField, Monomial,
};

/// Which route a product takes. Selected by [`route`]; a caller that wants a specific one for
/// measurement goes through [`multiply_by`].
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum MultiplyRoute {
    /// Materialise every product in one `Vec`, then collect like terms. The pre-#243 behaviour,
    /// kept because it is the fastest route on small operands and is the reference the differential
    /// test compares against.
    Materialize,
    /// Merge each product into a monomial-keyed map as it is formed. Live set `O(output)`.
    Accumulate,
    /// Materialise one block of the outer loop at a time and fold each block into the map. Live set
    /// `O(block)`; the block is `rows` terms of the left operand against all of the right.
    Chunked { rows: usize },
    /// Accumulate into a flat `Vec<F>` indexed by the bivariate total-degree triangle, so the inner
    /// loop hashes nothing. `N == 2` and a dense output only — see [`dense_triangle_profitable`].
    DenseTriangle,
}

/// Product count at or below which [`MultiplyRoute::Materialize`] is kept.
///
/// Measured by `examples/multivariate_mul.rs`: below this the `Vec` is one allocation and `push`
/// beats a hash lookup per product, and the transient it is being protected from is a few kilobytes.
/// Above it the collecting routes are both faster and bounded.
const MATERIALIZE_PRODUCT_LIMIT: u64 = 1 << 14;

/// Rows of the left operand per block in [`MultiplyRoute::Chunked`].
///
/// Swept in `examples/multivariate_mul.rs`. The figure is flat across two orders of magnitude
/// because the block buffer is reused and so costs one allocation whatever its size; what it buys
/// is a `push` loop the compiler can keep in registers, and 64 rows is enough for that.
const CHUNK_ROWS: usize = 64;

/// Bytes the flat triangle accumulator may reach before [`MultiplyRoute::DenseTriangle`] is refused.
///
/// A bound on the route's worst case rather than a performance threshold: the guard that makes the
/// route output-sized is a density test on the *operands*, and an operand pair that passes it can
/// still cancel almost everything. This caps what that costs.
const DENSE_TRIANGLE_BYTE_CAP: u64 = 64 * 1024 * 1024;

/// How sparse an operand may be and still be called dense, as a reciprocal: 4 is quarter-dense.
const DENSE_TRIANGLE_SPARSITY_LIMIT: u64 = 4;

/// Entries the accumulating routes will pre-size their map to, at most.
///
/// The estimate below is a genuine upper bound on the output's term count, but one of its two
/// halves is the product count — exactly the quantity this module exists to stop allocating. Past
/// this the map grows geometrically instead, which is bounded by the output it actually holds.
const ACCUMULATOR_CAPACITY_CAP: u64 = 1 << 20;

/// The product of two sparse multivariate polynomials, by the route [`route`] selects.
pub(crate) fn multiply<const N: usize, F: FiniteField>(
    a: &SparseMultiPoly<N, F>,
    b: &SparseMultiPoly<N, F>,
) -> SparseMultiPoly<N, F> {
    multiply_by(a, b, route(a, b))
}

/// The product by a named route. Every route returns the same polynomial; they differ in time and
/// in peak live heap.
pub(crate) fn multiply_by<const N: usize, F: FiniteField>(
    a: &SparseMultiPoly<N, F>,
    b: &SparseMultiPoly<N, F>,
    route: MultiplyRoute,
) -> SparseMultiPoly<N, F> {
    if a.terms.is_empty() || b.terms.is_empty() {
        return SparseMultiPoly::zero();
    }
    match route {
        MultiplyRoute::Materialize => multiply_materialize(a, b),
        MultiplyRoute::Accumulate => multiply_accumulate(a, b),
        MultiplyRoute::Chunked { rows } => multiply_chunked(a, b, rows),
        MultiplyRoute::DenseTriangle => multiply_dense_triangle(a, b),
    }
}

/// The route for this operand pair.
///
/// Three tiers, in the shape `multiply_dense` uses on the univariate side: keep the cheap path
/// where it is cheap, take the specialised one where it is both applicable and profitable, and
/// otherwise take the general collecting one.
pub(crate) fn route<const N: usize, F: FiniteField>(
    a: &SparseMultiPoly<N, F>,
    b: &SparseMultiPoly<N, F>,
) -> MultiplyRoute {
    let products = (a.terms.len() as u64).saturating_mul(b.terms.len() as u64);
    if products <= MATERIALIZE_PRODUCT_LIMIT {
        return MultiplyRoute::Materialize;
    }
    if dense_triangle_profitable(a, b) {
        return MultiplyRoute::DenseTriangle;
    }
    MultiplyRoute::Chunked { rows: CHUNK_ROWS }
}

/// Whether the flat triangle accumulator is applicable and output-sized for this pair.
///
/// Applicable needs `N == 2`: the index is a bivariate total-degree one.
///
/// Output-sized needs the *operands* to be dense in their own triangles, because the sumset of two
/// dense triangles is the dense triangle of the summed degree — so a dense pair's product fills the
/// accumulator and the accumulator is the output. This is a dense-**output** test, not an `N == 2`
/// one: `(x^1000 + 1) * (y^1000 + 1)` is bivariate with four output terms and a 2 003 001-slot
/// triangle, and the density test is what rejects it.
///
/// The failure mode it does not catch: a pair that is dense on both sides but whose product
/// cancels nearly everything. The flat accumulator is then triangle-sized for a tiny output. Over
/// a field that takes engineered coefficients rather than bad luck, and
/// [`DENSE_TRIANGLE_BYTE_CAP`] bounds what it costs when it happens.
fn dense_triangle_profitable<const N: usize, F: FiniteField>(
    a: &SparseMultiPoly<N, F>,
    b: &SparseMultiPoly<N, F>,
) -> bool {
    if N != 2 {
        return false;
    }
    let slots = triangle_len(a.degree().saturating_add(b.degree()));
    if slots.saturating_mul(std::mem::size_of::<F>() as u64) > DENSE_TRIANGLE_BYTE_CAP {
        return false;
    }
    is_dense(a) && is_dense(b)
}

/// Whether a bivariate polynomial fills at least `1 / DENSE_TRIANGLE_SPARSITY_LIMIT` of the
/// total-degree triangle it spans.
fn is_dense<const N: usize, F: FiniteField>(p: &SparseMultiPoly<N, F>) -> bool {
    (p.terms.len() as u64).saturating_mul(DENSE_TRIANGLE_SPARSITY_LIMIT) >= triangle_len(p.degree())
}

/// The pre-#243 route: one `Vec` of every product, collected by [`SparseMultiPoly::new`].
///
/// Kept reachable so that the differential test has an independent reference and the measurement
/// has a baseline arm. `with_capacity` is deliberately absent — this is the route as it was.
fn multiply_materialize<const N: usize, F: FiniteField>(
    a: &SparseMultiPoly<N, F>,
    b: &SparseMultiPoly<N, F>,
) -> SparseMultiPoly<N, F> {
    let mut terms: Vec<(Monomial<N>, F)> = Default::default();
    for (monomial_a, coefficient_a) in a.terms.iter() {
        for (monomial_b, coefficient_b) in b.terms.iter() {
            terms.push((monomial_a * monomial_b, *coefficient_a * *coefficient_b));
        }
    }

    SparseMultiPoly::new(&terms)
}

/// Merge every product into the accumulator as it is formed. Nothing of the product count is ever
/// resident.
fn multiply_accumulate<const N: usize, F: FiniteField>(
    a: &SparseMultiPoly<N, F>,
    b: &SparseMultiPoly<N, F>,
) -> SparseMultiPoly<N, F> {
    let mut accumulator = new_accumulator(a, b);
    for (monomial_a, coefficient_a) in a.terms.iter() {
        for (monomial_b, coefficient_b) in b.terms.iter() {
            merge(
                &mut accumulator,
                monomial_a * monomial_b,
                *coefficient_a * *coefficient_b,
            );
        }
    }
    finish(accumulator)
}

/// Materialise `rows` terms of `a` against all of `b`, fold that block into the accumulator, and
/// reuse the buffer. Transient `O(rows · |b|)`.
fn multiply_chunked<const N: usize, F: FiniteField>(
    a: &SparseMultiPoly<N, F>,
    b: &SparseMultiPoly<N, F>,
    rows: usize,
) -> SparseMultiPoly<N, F> {
    let rows = rows.max(1);
    let block = rows.saturating_mul(b.terms.len());
    let mut accumulator = new_accumulator(a, b);
    let mut buffer: Vec<(Monomial<N>, F)> = Vec::with_capacity(block);

    for (monomial_a, coefficient_a) in a.terms.iter() {
        for (monomial_b, coefficient_b) in b.terms.iter() {
            buffer.push((monomial_a * monomial_b, *coefficient_a * *coefficient_b));
        }
        if buffer.len() >= block {
            drain_into(&mut accumulator, &mut buffer);
        }
    }
    drain_into(&mut accumulator, &mut buffer);

    finish(accumulator)
}

/// Accumulate into a flat `Vec<F>` indexed by the bivariate total-degree triangle.
///
/// The inner loop is two additions and one indexed `+=`: no hashing, and no per-product branch on
/// whether the monomial has been seen. `README.md`'s F4 matrix path made the same trade — a
/// polynomial's hash map for integer column indices — and measured it a win.
///
/// Where the other routes check each exponent addition, this one establishes the same guarantee
/// once, before the loop: every exponent of the product sums to at most the summed total degree,
/// so a total degree inside `u32` makes per-product overflow impossible. That is strictly stronger
/// than the per-product check and costs nothing in the inner loop.
///
/// # Panics
/// Panics unless `N == 2`, and unless the summed total degree fits in a `u32` — which
/// [`dense_triangle_profitable`] already refuses long before, since the triangle of such a degree
/// could not be allocated.
fn multiply_dense_triangle<const N: usize, F: FiniteField>(
    a: &SparseMultiPoly<N, F>,
    b: &SparseMultiPoly<N, F>,
) -> SparseMultiPoly<N, F> {
    assert_eq!(N, 2, "the triangle index is bivariate");

    let degree = a.degree().saturating_add(b.degree());
    assert!(
        degree <= u32::MAX as u64,
        "monomial exponent overflow: total degree {degree} does not fit in a u32"
    );
    let mut slots = vec![F::zero(); triangle_len(degree) as usize];

    for (monomial_a, coefficient_a) in a.terms.iter() {
        let (left_x, left_y) = (monomial_a.exponents[0], monomial_a.exponents[1]);
        for (monomial_b, coefficient_b) in b.terms.iter() {
            let x = left_x + monomial_b.exponents[0];
            let y = left_y + monomial_b.exponents[1];
            slots[triangle_index(x, y)] += *coefficient_a * *coefficient_b;
        }
    }

    // Counted before the map is built so that it is sized once, which is the whole point of having
    // come this far without hashing.
    let occupied = slots.iter().filter(|c| !c.is_zero()).count();
    let mut terms: HashMap<Monomial<N>, F> = HashMap::with_capacity(occupied);
    for total in 0..=degree {
        let base = (total * (total + 1) / 2) as usize;
        for y in 0..=total {
            let coefficient = slots[base + y as usize];
            // Drop-on-cancel: an empty slot and a cancelled one are the same thing here.
            if coefficient.is_zero() {
                continue;
            }
            let x = (total - y) as u32;
            terms.insert(Monomial::new(&[x, y as u32]), coefficient);
        }
    }

    SparseMultiPoly { terms }
}

/// The accumulator, pre-sized from an upper bound on the output's term count.
fn new_accumulator<const N: usize, F: FiniteField>(
    a: &SparseMultiPoly<N, F>,
    b: &SparseMultiPoly<N, F>,
) -> HashMap<Monomial<N>, F> {
    HashMap::with_capacity(accumulator_capacity(a, b))
}

/// An upper bound on the number of distinct monomials in `a * b`, capped.
///
/// Two bounds, whichever is smaller: the product count, and the number of monomials of total
/// degree at most `deg a + deg b` in `N` variables. On the six-round bivariate build the second is
/// 266 815 against the first's 3.54 billion, and it is exact — the product is that whole triangle.
fn accumulator_capacity<const N: usize, F: FiniteField>(
    a: &SparseMultiPoly<N, F>,
    b: &SparseMultiPoly<N, F>,
) -> usize {
    let products = (a.terms.len() as u64).saturating_mul(b.terms.len() as u64);
    let support = monomial_count_bound::<N>(a.degree().saturating_add(b.degree()));
    products.min(support).min(ACCUMULATOR_CAPACITY_CAP) as usize
}

/// `C(degree + N, N)`, the number of monomials of total degree at most `degree` in `N` variables.
///
/// Saturating: the count overflows `u64` for a modest degree once `N` is large, and a saturated
/// bound is still a bound.
fn monomial_count_bound<const N: usize>(degree: u64) -> u64 {
    let mut count: u128 = 1;
    for i in 1..=(N as u128) {
        count = count.saturating_mul(degree as u128 + i) / i;
        if count > u64::MAX as u128 {
            return u64::MAX;
        }
    }
    count as u64
}

/// The number of monomials of total degree at most `degree` in two variables.
fn triangle_len(degree: u64) -> u64 {
    degree
        .saturating_add(1)
        .saturating_mul(degree.saturating_add(2))
        / 2
}

/// The index of `x^i y^j` in the total-degree triangle: the monomials of total degree `t = i + j`
/// occupy a contiguous run of `t + 1` slots starting at `t(t+1)/2`, ordered by `j`.
#[inline]
fn triangle_index(i: u32, j: u32) -> usize {
    let total = i as usize + j as usize;
    total * (total + 1) / 2 + j as usize
}

/// Add one term to the accumulator, merging it with a monomial already present.
#[inline]
fn merge<const N: usize, F: FiniteField>(
    accumulator: &mut HashMap<Monomial<N>, F>,
    monomial: Monomial<N>,
    coefficient: F,
) {
    match accumulator.get_mut(&monomial) {
        Some(c) => *c += coefficient,
        None => {
            accumulator.insert(monomial, coefficient);
        }
    }
}

/// Fold a block of products into the accumulator and empty the buffer, keeping its capacity.
fn drain_into<const N: usize, F: FiniteField>(
    accumulator: &mut HashMap<Monomial<N>, F>,
    buffer: &mut Vec<(Monomial<N>, F)>,
) {
    for (monomial, coefficient) in buffer.drain(..) {
        merge(accumulator, monomial, coefficient);
    }
}

/// Drop the monomials that cancelled and hand back a canonical polynomial.
fn finish<const N: usize, F: FiniteField>(
    mut accumulator: HashMap<Monomial<N>, F>,
) -> SparseMultiPoly<N, F> {
    accumulator.retain(|_monomial, c| !c.is_zero());
    SparseMultiPoly { terms: accumulator }
}

/// Every route, reachable from an example binary so that the dispatch can be re-measured.
#[doc(hidden)]
pub fn multiply_multivariate_unstable<const N: usize, F: FiniteField>(
    a: &SparseMultiPoly<N, F>,
    b: &SparseMultiPoly<N, F>,
    route: MultiplyRoute,
) -> SparseMultiPoly<N, F> {
    multiply_by(a, b, route)
}

/// [`route`], reachable from an example binary.
#[doc(hidden)]
pub fn multivariate_multiply_route_unstable<const N: usize, F: FiniteField>(
    a: &SparseMultiPoly<N, F>,
    b: &SparseMultiPoly<N, F>,
) -> MultiplyRoute {
    route(a, b)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{fields::PrimeFieldElement64, One, Zero};
    use proptest::{collection::vec, prelude::*, test_runner::TestRunner};

    /// Every route, with the chunk sizes the sweep covers.
    const ALL_ROUTES: [MultiplyRoute; 6] = [
        MultiplyRoute::Materialize,
        MultiplyRoute::Accumulate,
        MultiplyRoute::Chunked { rows: 1 },
        MultiplyRoute::Chunked { rows: 7 },
        MultiplyRoute::Chunked { rows: CHUNK_ROWS },
        MultiplyRoute::DenseTriangle,
    ];

    /// A strategy for a polynomial of at most `num_terms` distinct monomials over any field.
    fn poly_strategy<const N: usize, F: FiniteField>(
        num_terms: usize,
    ) -> impl Strategy<Value = SparseMultiPoly<N, F>> {
        (
            vec(any::<Monomial<N>>(), num_terms),
            vec(F::arbitrary(), num_terms),
        )
            .prop_map(|(monomials, coefficients)| {
                let terms: Vec<(Monomial<N>, F)> =
                    monomials.into_iter().zip(coefficients).collect();
                SparseMultiPoly::new(&terms)
            })
    }

    /// Each route agrees with [`multiply_materialize`], over `F` in `N` variables.
    fn assert_routes_agree<const N: usize, F: FiniteField>() {
        let strategy = (poly_strategy::<N, F>(5), poly_strategy::<N, F>(5));
        TestRunner::deterministic()
            .run(&strategy, |(a, b)| {
                let reference = multiply_by(&a, &b, MultiplyRoute::Materialize);
                for route in ALL_ROUTES {
                    if route == MultiplyRoute::DenseTriangle && N != 2 {
                        continue;
                    }
                    prop_assert_eq!(
                        multiply_by(&a, &b, route),
                        reference.clone(),
                        "{:?} disagrees with the materialising reference",
                        route
                    );
                }
                // And the dispatched operator is one of them.
                prop_assert_eq!(&a * &b, reference);
                Ok(())
            })
            .unwrap();
    }

    // Every route returns the materialising route's answer, over every field and at two arities.
    for_each_field!(
        fn the_routes_agree<F>() {
            assert_routes_agree::<2, F>();
            assert_routes_agree::<3, F>();
        }
    );

    /// The dense triangle of total degree `degree`, every coefficient nonzero.
    fn dense_triangle<F: FiniteField>(degree: u32, seed: u64) -> SparseMultiPoly<2, F> {
        let mut terms: Vec<(Monomial<2>, F)> = Vec::new();
        for x in 0..=degree {
            for y in 0..=(degree - x) {
                terms.push((
                    Monomial::<2>::new(&[x, y]),
                    F::new(1 + (seed + x as u64 * 31 + y as u64) % 97),
                ));
            }
        }
        SparseMultiPoly::new(&terms)
    }

    // The triangle index is a bijection onto `0..triangle_len(degree)`.
    #[test]
    fn test_triangle_index_is_a_bijection() {
        const DEGREE: u64 = 12;
        let mut seen = vec![false; triangle_len(DEGREE) as usize];
        for total in 0..=DEGREE as u32 {
            for y in 0..=total {
                let index = triangle_index(total - y, y);
                assert!(!seen[index], "index {index} is claimed twice");
                seen[index] = true;
            }
        }
        assert!(seen.iter().all(|s| *s), "the triangle has an unused slot");
    }

    // `monomial_count_bound` is the exact monomial count in one, two and three variables.
    #[test]
    fn test_monomial_count_bound_is_exact() {
        assert_eq!(monomial_count_bound::<1>(7), 8);
        assert_eq!(monomial_count_bound::<2>(7), 36);
        assert_eq!(monomial_count_bound::<2>(729), 266_815);
        assert_eq!(monomial_count_bound::<3>(4), 35);
        // Saturates rather than overflowing once the count leaves `u64`.
        assert_eq!(monomial_count_bound::<32>(u32::MAX as u64), u64::MAX);
    }

    // A dense bivariate pair is routed to the triangle; the general case is routed to the chunked
    // accumulator; a small product keeps the materialising route.
    #[test]
    fn test_route_selects_by_density_not_by_arity() {
        type F = PrimeFieldElement64<541>;

        let small: SparseMultiPoly<2, F> = dense_triangle(8, 1);
        assert_eq!(route(&small, &small), MultiplyRoute::Materialize);

        let dense: SparseMultiPoly<2, F> = dense_triangle(200, 1);
        assert_eq!(route(&dense, &dense), MultiplyRoute::DenseTriangle);

        // Bivariate, far past the materialising limit, and sparse: two terms spanning degree
        // 20 000, whose triangle would be 200 million slots for four output terms.
        let sparse: SparseMultiPoly<2, F> = SparseMultiPoly::new(&[
            (Monomial::<2>::new(&[20_000, 0]), F::one()),
            (Monomial::<2>::new(&[0, 20_000]), F::one()),
        ]);
        let wide = &sparse * &dense;
        assert_eq!(
            route(&wide, &wide),
            MultiplyRoute::Chunked { rows: CHUNK_ROWS },
            "a sparse bivariate pair must not be forced into a dense triangle"
        );

        // Arity alone does not select the triangle.
        let trivariate: SparseMultiPoly<3, F> = {
            let mut terms: Vec<(Monomial<3>, F)> = Vec::new();
            for x in 0..40u32 {
                for y in 0..40u32 {
                    terms.push((Monomial::<3>::new(&[x, y, 1]), F::new(1 + x as u64)));
                }
            }
            SparseMultiPoly::new(&terms)
        };
        assert_eq!(
            route(&trivariate, &trivariate),
            MultiplyRoute::Chunked { rows: CHUNK_ROWS }
        );
    }

    // The dense triangle route reproduces the `p*p` then `(p^2)*p` cube the six-round build runs,
    // agreeing with the materialising route at both steps.
    #[test]
    fn test_dense_triangle_cubes_a_bivariate() {
        type F = PrimeFieldElement64<541>;
        let p: SparseMultiPoly<2, F> = dense_triangle(24, 3);

        let square = multiply_by(&p, &p, MultiplyRoute::DenseTriangle);
        let reference_square = multiply_by(&p, &p, MultiplyRoute::Materialize);
        assert_eq!(square, reference_square);

        let cube = multiply_by(&square, &p, MultiplyRoute::DenseTriangle);
        assert_eq!(
            cube,
            multiply_by(&reference_square, &p, MultiplyRoute::Materialize)
        );
        assert_eq!(cube.degree(), 72);

        // Both steps land just short of the full triangle: a handful of monomials cancel over
        // GF(541), and the route must drop those rather than keep them as occupied slots.
        for (product, degree) in [(&square, 48u64), (&cube, 72)] {
            let slots = triangle_len(degree);
            let occupied = product.terms.len() as u64;
            assert!(occupied < slots, "nothing cancelled, so nothing is tested");
            assert!(
                occupied * 100 >= slots * 99,
                "{occupied} of {slots} slots is not the near-dense case being tested"
            );
            assert!(product.terms.values().all(|c| !c.is_zero()));
        }
    }

    // A product in which every term cancels is the zero polynomial on every route, with no zero
    // coefficient left behind.
    #[test]
    fn test_every_route_drops_cancelled_terms() {
        type F = PrimeFieldElement64<7>;
        // (x + y) * (x + y) over GF(7) does not cancel; (x + y)^7 = x^7 + y^7 does, by Frobenius.
        let p: SparseMultiPoly<2, F> = SparseMultiPoly::new(&[
            (Monomial::<2>::new(&[1, 0]), F::one()),
            (Monomial::<2>::new(&[0, 1]), F::one()),
        ]);
        let mut power = p.clone();
        for _ in 1..7 {
            power = &power * &p;
        }
        let expected: SparseMultiPoly<2, F> = SparseMultiPoly::new(&[
            (Monomial::<2>::new(&[7, 0]), F::one()),
            (Monomial::<2>::new(&[0, 7]), F::one()),
        ]);
        assert_eq!(power, expected);
        assert_eq!(power.terms.len(), 2, "a cancelled term survived");

        // Directly, on each route: multiplying p^6 by p must drop the five interior binomial
        // coefficients, all of which are 0 mod 7.
        let sixth = {
            let mut q = p.clone();
            for _ in 1..6 {
                q = &q * &p;
            }
            q
        };
        for route in ALL_ROUTES {
            let product = multiply_by(&sixth, &p, route);
            assert_eq!(product, expected, "{route:?} kept a cancelled term");
            assert!(product.terms.values().all(|c| !c.is_zero()));
        }
    }

    // Multiplying by the zero polynomial is zero on every route, including the specialised one.
    #[test]
    fn test_every_route_handles_zero() {
        type F = PrimeFieldElement64<541>;
        let p: SparseMultiPoly<2, F> = dense_triangle(5, 1);
        let zero: SparseMultiPoly<2, F> = SparseMultiPoly::zero();
        for route in ALL_ROUTES {
            assert_eq!(multiply_by(&p, &zero, route), SparseMultiPoly::zero());
            assert_eq!(multiply_by(&zero, &p, route), SparseMultiPoly::zero());
        }
    }

    // A degree whose triangle cannot be indexed is refused by the predicate, so the operator never
    // reaches the route that would have to allocate it.
    #[test]
    fn test_dense_triangle_refuses_an_unindexable_degree() {
        type F = PrimeFieldElement64<541>;
        let p: SparseMultiPoly<2, F> =
            SparseMultiPoly::new(&[(Monomial::<2>::new(&[u32::MAX, 0]), F::one())]);
        assert!(!dense_triangle_profitable(&p, &p));
        // And the operator still produces the right answer, by another route: squaring this one
        // term overflows the exponent, which is `Monomial`'s documented panic.
        assert_eq!(route(&p, &p), MultiplyRoute::Materialize);
    }
}
