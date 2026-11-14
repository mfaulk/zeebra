//! Multiplication routes for sparse multivariate polynomials, and the dispatch between them.
//!
//! The multiply this replaced pushed every pairwise term-product into one `Vec` and collected like
//! terms afterwards, so its transient was `O(|a|·|b|)` entries however few distinct monomials the
//! product had. `docs/research/resultant-elimination.md` §6.8 measured a six-round symbolic build
//! holding 57.0 GB to produce 4.3 MB of polynomial. The routes [`route`] selects collect *as they
//! go*, so the live set is bounded by the output instead; the materialising one is kept only as the
//! reference the differential test compares against and as the measurement's baseline arm.
//!
//! All of them end in the same drop-on-cancel step as [`SparseMultiPoly::new`]: a monomial whose
//! coefficients cancel is not a term of the product, and a surviving zero would make a polynomial
//! unequal to its own canonical form.
//!
//! [`multiply_sorted`] is the one exit that is not a `SparseMultiPoly`: a heap merge that emits the
//! product in monomial order. `docs/research/heap-multiply.md` measured it 2.2x–10x slower than
//! `Accumulate` as a multiply, faster as a multiply-then-sort only on collision-poor pairs, and
//! found no caller that sorts a product, so nothing dispatches to it.

use crate::{
    poly::multivariate::{
        dense_index::{
            box_cells, collect_box, collect_simplex, simplex_len, BoxIndex, SimplexIndex,
        },
        monomial_hash::{BuildMonomialHasher, MonomialMap},
        sparse_multivariate_polynomial::SparseMultiPoly,
    },
    FiniteField, Monomial, MonomialOrder,
};
use std::cmp::Ordering;

/// Which route a product takes. Selected by `route`; a caller that wants a specific one for
/// measurement goes through `multiply_by`.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum MultiplyRoute {
    /// Materialise every product in one `Vec`, then collect like terms. The pre-#243 behaviour,
    /// **never selected**: kept as the reference the differential test compares against and as the
    /// measurement's baseline arm.
    ///
    /// It cannot win, and not only by measurement: it *is* [`MultiplyRoute::Accumulate`] with a
    /// `Vec` of every product in front of it, because `SparseMultiPoly::new` performs the same
    /// monomial-keyed merge. `examples/multivariate_mul.rs` measures it slowest at every size,
    /// down to 36 term-products.
    Materialize,
    /// Merge each product into a monomial-keyed map as it is formed. Live set `O(output)`, and the
    /// general route.
    Accumulate,
    /// Materialise one block of the outer loop at a time and fold each block into the map. Live set
    /// `O(block)`; the block is `rows` terms of the left operand against all of the right.
    ///
    /// **Never selected** — a measured negative result, kept reachable so that it stays
    /// reproducible. #243 named this as the smaller change, and it is: a block buffer bounds the
    /// transient without touching the combine. But it bounds it at `O(rows · |b|)` where
    /// accumulating directly bounds it at `O(output)`, and the sweep in
    /// `examples/multivariate_mul.rs` finds its time *flat* in `rows` while its memory is linear in
    /// `rows` — so the best block is one row, which is direct accumulation with a redundant `Vec`
    /// round-trip, measured at 1.4x its time.
    Chunked { rows: usize },
    /// Accumulate into a flat `Vec<F>` indexed by the bivariate total-degree triangle, so the inner
    /// loop hashes nothing. `N == 2` and a dense output only — see `dense_triangle_profitable`.
    DenseTriangle,
    /// [`MultiplyRoute::DenseTriangle`] generalised to any `N`: a flat `Vec<F>` indexed by the
    /// total-degree simplex, `C(d + N, N)` cells. The tightest dense layout, and the one #362 names.
    ///
    /// Its rank is not separable, so it costs `2(N - 1)` table lookups and as many adds per product
    /// where the triangle costs three integer operations — which is why generalising the *layout*
    /// does not generalise the *win*. See `dense_simplex_profitable`.
    DenseSimplex,
    /// A flat `Vec<F>` indexed by a mixed-radix box over the per-variable degree bounds,
    /// `∏(d_i + 1)` cells.
    ///
    /// The index is separable, so the left operand's index hoists out of the inner loop and the
    /// per-product cost is one add at every arity — the triangle's property, kept. It pays about
    /// `N!` in cells for an operand pair dense in the total-degree sense, which is what
    /// `dense_box_profitable` and `DENSE_TRIANGLE_BYTE_CAP` govern.
    DenseBox,
    /// Monagan and Pearce's heap merge (#443): the products `a_i · b_j` merged in monomial order
    /// through a binary heap of at most `min(|a|, |b|)` entries, so the product comes out sorted
    /// and nothing is hashed until the output is stored. See `multiply_sorted`.
    ///
    /// **Never selected** — a measured negative result, kept reachable so that it stays
    /// reproducible. As a multiply it is 2.2x–8.3x slower than `Accumulate` on every sparse shape
    /// `examples/multivariate_mul.rs -- heap` sweeps: a pop costs `log₂ rows` unpacked monomial
    /// comparisons where `Accumulate` pays one hash. Its ordered output beats accumulate-then-sort
    /// by up to 1.9x on collision-poor pairs, but no caller sorts a product
    /// (`docs/research/heap-multiply.md` §1).
    Heap,
}

/// Bytes the flat triangle accumulator may reach before [`MultiplyRoute::DenseTriangle`] is refused.
///
/// A bound on the route's worst case rather than a performance threshold. The density test below is
/// an estimate, and this is what the estimate being wrong costs: bounded waste, never unbounded.
const DENSE_TRIANGLE_BYTE_CAP: u64 = 64 * 1024 * 1024;

/// How many triangle slots may be allocated per unit of the output's upper bound.
///
/// 4 rather than 1 because the bound is loose in the useful direction: a dense bivariate pair's
/// product fills its triangle exactly, while `|a|·|b|` overcounts that by the number of monomial
/// collisions — which for dense operands is almost all of them.
const DENSE_TRIANGLE_SLOT_RATIO: u64 = 4;

/// How many products there must be per monomial the output can hold, before a dense accumulator at
/// `N >= 3` is worth its index.
///
/// The thing a dense accumulator buys is **merging without a hash lookup**. Where the products do
/// not collide there is nothing to merge: one term against many produces exactly `|a|` monomials
/// from `|a|` products, and the dense route pays an index per product and a scan of every cell to
/// arrive at what the hash route reaches with `|a|` collision-free inserts.
///
/// At `N = 2` the triangle's index is three integer operations and it wins that case anyway —
/// measured 29.1 µs against the accumulator's 44.1 µs, which is why #243's predicate deliberately
/// admits it and why this factor does **not** apply to [`MultiplyRoute::DenseTriangle`]. At `N = 3`
/// the simplex's index is `2(N - 1)` table lookups and the same case **loses**: 55.4 µs against
/// 48.6 µs, with the box worse again at 73.5 µs. Generalising the layout does not generalise the
/// win, and this is where the difference shows.
///
/// 2 rather than 1 because a factor of exactly 1 is the no-collision case itself. Every shape
/// measured profitable in `examples/multivariate_mul.rs` clears it by 3x or more — the smallest is
/// 3.5 at five variables and degree 2 — so the threshold sits in a gap rather than on a slope.
const DENSE_MERGE_FACTOR: u64 = 2;

/// How many box cells are worth one simplex cell, choosing between the two dense layouts.
///
/// [`MultiplyRoute::DenseBox`]'s index is separable and so costs one add per product at any arity,
/// against the simplex's `2(N - 1)` lookups; it pays for that in cells, up to about `N!` for an
/// operand pair dense in the total-degree sense. So the choice is that saving against the extra
/// cells to allocate and scan, and 24 is `4!` — which is where the sweep in
/// `examples/multivariate_mul.rs` puts the crossover: the box is faster at `N = 3` (3.13 ms against
/// the simplex's 4.80 ms) and at `N = 4` (2.35 against 3.56), and the simplex is faster at `N = 5`
/// (151.5 µs against 271.3 µs).
///
/// It is a cell ratio rather than an arity test because the `N!` penalty is a property of the
/// *operands*, not of `N`: a trivariate pair dense in two variables and linear in the third has a
/// bounding box of 5 043 cells against a total-degree simplex of 317 750, and there the box is 8.4x
/// the accumulator where the simplex is 4.5x.
///
/// Known miss, stated rather than tuned away: at `N = 4` and degree 3 — 1 225 products, 18 µs — the
/// ratio is 11.4 and the box is selected, where the simplex measured 1.23x faster. One constant
/// with a derivation and a named exception, rather than a table fitted to the sweep.
const BOX_CELL_RATIO: u64 = 24;

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
        MultiplyRoute::DenseSimplex => multiply_dense_simplex(a, b),
        MultiplyRoute::DenseBox => multiply_dense_box(a, b),
        MultiplyRoute::Heap => multiply_heap(a, b),
    }
}

/// The route for this operand pair.
///
/// Two tiers, in the shape `multiply_dense` uses on the univariate side: the specialised route
/// where it is both applicable and profitable, otherwise the general one. There is deliberately no
/// small-operand tier — `examples/multivariate_mul.rs` measured for one and did not find it, for
/// the reason recorded on [`MultiplyRoute::Materialize`].
///
/// No size threshold also means the operand size does not change where the answer comes from, so
/// the small `mul/{arity}` Criterion arms and the six-round build exercise the same code.
pub(crate) fn route<const N: usize, F: FiniteField>(
    a: &SparseMultiPoly<N, F>,
    b: &SparseMultiPoly<N, F>,
) -> MultiplyRoute {
    if dense_triangle_profitable(a, b) {
        return MultiplyRoute::DenseTriangle;
    }
    // Past `N = 2` the index is no longer free, so a dense layout being *output-sized* is not
    // enough — the products also have to collide. See [`DENSE_MERGE_FACTOR`].
    if !dense_merging_is_worth_the_index(a, b) {
        return MultiplyRoute::Accumulate;
    }
    let simplex = dense_simplex_profitable(a, b);
    match dense_box_profitable(a, b) {
        // The box where its cells are close enough to the simplex's to pay for the separable
        // index, and wherever the simplex itself was refused.
        Some(bounds) if !simplex || box_is_worth_its_cells::<N, F>(&bounds, a, b) => {
            MultiplyRoute::DenseBox
        }
        _ if simplex => MultiplyRoute::DenseSimplex,
        _ => MultiplyRoute::Accumulate,
    }
}

/// Whether enough products collide for a dense accumulator at `N >= 3` to earn its index.
///
/// The denominator is the tighter of the two bounds on the output's monomial count — the product
/// count and the total-degree simplex — for the reason [`accumulator_capacity`] uses both: on a
/// dense pair the simplex is the exact output and the product count overstates it by orders of
/// magnitude, while on a sparse one the reverse holds.
fn dense_merging_is_worth_the_index<const N: usize, F: FiniteField>(
    a: &SparseMultiPoly<N, F>,
    b: &SparseMultiPoly<N, F>,
) -> bool {
    let products = (a.terms.len() as u64).saturating_mul(b.terms.len() as u64);
    let monomials = products.min(simplex_len::<N>(a.degree().saturating_add(b.degree())));
    products >= monomials.saturating_mul(DENSE_MERGE_FACTOR)
}

/// Whether the box's extra cells are worth its separable index, against the simplex.
fn box_is_worth_its_cells<const N: usize, F: FiniteField>(
    bounds: &[u32; N],
    a: &SparseMultiPoly<N, F>,
    b: &SparseMultiPoly<N, F>,
) -> bool {
    let simplex = simplex_len::<N>(a.degree().saturating_add(b.degree()));
    match box_cells::<N>(bounds) {
        Some(cells) => cells <= simplex.saturating_mul(BOX_CELL_RATIO),
        None => false,
    }
}

/// Whether the flat triangle accumulator is applicable and output-sized for this pair.
///
/// Applicable needs `N == 2`: the index is a bivariate total-degree one.
///
/// Output-sized has to be estimated, and the estimate is **the triangle against the output's upper
/// bound**: the product has at most `|a|·|b|` distinct monomials, so a triangle within a constant
/// factor of `|a|·|b|` is within that factor of being exactly the output. This is a
/// dense-**output** test, not an `N == 2` one, and not a test on the operands either —
/// `(x^20000 + 1) * (y^20000 + 1)` is bivariate, wants 800 million slots for four output terms, and
/// is rejected on four products.
///
/// # When the estimate is wrong, in each direction
///
/// *Too pessimistic* — a pair whose product really is dense goes to [`multiply_accumulate`] anyway.
/// Measured cost: the triangle is 3x to 6x faster than accumulating at every bivariate size swept
/// in `examples/multivariate_mul.rs`, so this direction loses time and nothing else. Both routes
/// are output-bounded in memory, which is the property §6.8 was about.
///
/// *Too optimistic* — a pair that passes the ratio but whose product cancels nearly everything
/// allocates a triangle far larger than its output. Over a field that takes engineered coefficients
/// rather than bad luck, and [`DENSE_TRIANGLE_BYTE_CAP`] caps the damage at 64 MiB however wrong
/// the estimate was.
///
/// The asymmetry is deliberate: the pessimistic direction costs unbounded *time*, the optimistic one
/// bounded *memory*. After §6.8 that is the right way round.
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
    let products = (a.terms.len() as u64).saturating_mul(b.terms.len() as u64);
    slots <= products.saturating_mul(DENSE_TRIANGLE_SLOT_RATIO)
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
/// whether the monomial has been seen. F4's matrix path made the same trade — a
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
    let mut terms: MonomialMap<N, F> =
        MonomialMap::with_capacity_and_hasher(occupied, BuildMonomialHasher);
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

/// Whether the total-degree simplex accumulator is output-sized for this pair.
///
/// Applicable at every `N`, unlike [`dense_triangle_profitable`]. The output-sized test is the
/// same one, for the same reason: the product has at most `|a|·|b|` distinct monomials, so a
/// simplex within a constant factor of that is within the factor of being exactly the output.
///
/// # When the estimate is wrong, in each direction
///
/// *Too pessimistic* — a genuinely dense pair goes to [`multiply_accumulate`] and loses whatever
/// the simplex would have saved, which at `N >= 3` is small and may be negative (see
/// `docs/research` and the arms in `examples/multivariate_mul.rs`). Time only; both routes are
/// output-bounded in memory.
///
/// *Too optimistic* — a pair that passes the ratio but cancels nearly everything allocates a
/// simplex far larger than its output, capped at [`DENSE_TRIANGLE_BYTE_CAP`].
///
/// #362 observed that the pessimistic direction matters *more* here than at `N = 2`, because
/// `C(d + N, N)` grows much faster in `N` than `(d+1)(d+2)/2` does — a predicate tuned at `N = 2`
/// admits, at `N = 4`, simplices whose cell count dwarfs the output. The ratio is nonetheless
/// carried over unchanged at 4: it is the output's own upper bound that is being tested, not a
/// property of the arity, and the cap is what bounds the damage either way.
fn dense_simplex_profitable<const N: usize, F: FiniteField>(
    a: &SparseMultiPoly<N, F>,
    b: &SparseMultiPoly<N, F>,
) -> bool {
    let degree = a.degree().saturating_add(b.degree());
    if degree > u32::MAX as u64 {
        return false;
    }
    let cells = simplex_len::<N>(degree);
    if cells.saturating_mul(std::mem::size_of::<F>() as u64) > DENSE_TRIANGLE_BYTE_CAP {
        return false;
    }
    let products = (a.terms.len() as u64).saturating_mul(b.terms.len() as u64);
    cells <= products.saturating_mul(DENSE_TRIANGLE_SLOT_RATIO)
}

/// Whether the mixed-radix box accumulator is output-sized for this pair, and its bounds.
///
/// The bounds are per variable — `deg_i(a) + deg_i(b)` — so a variable that appears to low degree
/// costs the box almost nothing, which is the case the total-degree simplex cannot exploit: the
/// simplex is cut by `Σ e_i <= d` and so is sized by the *total* degree however lopsided the
/// per-variable degrees are. The two failure directions are [`dense_simplex_profitable`]'s.
fn dense_box_profitable<const N: usize, F: FiniteField>(
    a: &SparseMultiPoly<N, F>,
    b: &SparseMultiPoly<N, F>,
) -> Option<[u32; N]> {
    let left = variable_degrees(a);
    let right = variable_degrees(b);
    let mut bounds = [0u32; N];
    for i in 0..N {
        bounds[i] = left[i].checked_add(right[i])?;
    }
    let cells = box_cells::<N>(&bounds)?;
    if cells.saturating_mul(std::mem::size_of::<F>() as u64) > DENSE_TRIANGLE_BYTE_CAP {
        return None;
    }
    let products = (a.terms.len() as u64).saturating_mul(b.terms.len() as u64);
    (cells <= products.saturating_mul(DENSE_TRIANGLE_SLOT_RATIO)).then_some(bounds)
}

/// The largest exponent of each variable over all terms. Linear in the operand, so negligible
/// beside the product it sizes.
fn variable_degrees<const N: usize, F: FiniteField>(p: &SparseMultiPoly<N, F>) -> [u32; N] {
    let mut degrees = [0u32; N];
    for monomial in p.terms.keys() {
        for i in 0..N {
            degrees[i] = degrees[i].max(monomial.exponents[i]);
        }
    }
    degrees
}

/// Accumulate into a flat `Vec<F>` indexed by the total-degree simplex. Any `N`.
///
/// The generalisation #362 asks for. Where [`multiply_dense_triangle`] hashes nothing and indexes
/// in three operations, this hashes nothing and indexes in `2(N - 1)` table lookups — so the
/// comparison against [`multiply_accumulate`] is table lookups against one `SipHash` of the
/// exponent array plus a probe, and which wins is a measurement rather than an argument.
///
/// # Panics
/// Panics unless the summed total degree fits in a `u32`, which [`dense_simplex_profitable`]
/// refuses long before — a simplex of such a degree could not be allocated.
fn multiply_dense_simplex<const N: usize, F: FiniteField>(
    a: &SparseMultiPoly<N, F>,
    b: &SparseMultiPoly<N, F>,
) -> SparseMultiPoly<N, F> {
    let degree = a.degree().saturating_add(b.degree());
    assert!(
        degree <= u32::MAX as u64,
        "monomial exponent overflow: total degree {degree} does not fit in a u32"
    );
    // Established once, before the loop, rather than per exponent addition: every exponent of the
    // product sums to at most the summed total degree, so a total degree inside `u32` makes
    // per-product overflow impossible. Strictly stronger than the per-product check, and free.
    let index = SimplexIndex::<N>::new(degree as u32);
    let mut slots = vec![F::zero(); simplex_len::<N>(degree) as usize];

    let mut exponents = [0u32; N];
    for (monomial_a, coefficient_a) in a.terms.iter() {
        for (monomial_b, coefficient_b) in b.terms.iter() {
            for i in 0..N {
                exponents[i] = monomial_a.exponents[i] + monomial_b.exponents[i];
            }
            slots[index.rank(&exponents)] += *coefficient_a * *coefficient_b;
        }
    }

    SparseMultiPoly {
        terms: collect_simplex::<N, F>(&slots, degree),
    }
}

/// Accumulate into a flat `Vec<F>` indexed by a mixed-radix box over the per-variable degrees.
///
/// The separable index is what this route is for: the left operand's index is computed once per
/// outer iteration and the inner loop is one add and one indexed `+=`, which is
/// [`multiply_dense_triangle`]'s inner loop at any arity rather than only at `N = 2`.
///
/// # Panics
/// Panics unless the bounds are the ones [`dense_box_profitable`] returned, whose box it has
/// already checked fits.
fn multiply_dense_box<const N: usize, F: FiniteField>(
    a: &SparseMultiPoly<N, F>,
    b: &SparseMultiPoly<N, F>,
) -> SparseMultiPoly<N, F> {
    let bounds = dense_box_bounds(a, b).expect("the box does not fit");
    let index = BoxIndex::<N>::new(bounds);
    let mut slots = vec![F::zero(); index.cells()];

    for (monomial_a, coefficient_a) in a.terms.iter() {
        let base = index.rank(&monomial_a.exponents);
        for (monomial_b, coefficient_b) in b.terms.iter() {
            slots[base + index.rank(&monomial_b.exponents)] += *coefficient_a * *coefficient_b;
        }
    }

    SparseMultiPoly {
        terms: collect_box::<N, F>(&slots, &index),
    }
}

/// The per-variable bounds of `a * b`, or `None` if the box they describe cannot be allocated.
///
/// Separate from [`dense_box_profitable`] because [`multiply_dense_box`] may be named directly for
/// measurement, where the profitability test is exactly what is being bypassed.
fn dense_box_bounds<const N: usize, F: FiniteField>(
    a: &SparseMultiPoly<N, F>,
    b: &SparseMultiPoly<N, F>,
) -> Option<[u32; N]> {
    let left = variable_degrees(a);
    let right = variable_degrees(b);
    let mut bounds = [0u32; N];
    for i in 0..N {
        bounds[i] = left[i].checked_add(right[i])?;
    }
    box_cells::<N>(&bounds).map(|_| bounds)
}

/// The accumulator, pre-sized from an upper bound on the output's term count.
fn new_accumulator<const N: usize, F: FiniteField>(
    a: &SparseMultiPoly<N, F>,
    b: &SparseMultiPoly<N, F>,
) -> MonomialMap<N, F> {
    MonomialMap::with_capacity_and_hasher(accumulator_capacity(a, b), BuildMonomialHasher)
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
    let support = simplex_len::<N>(a.degree().saturating_add(b.degree()));
    products.min(support).min(ACCUMULATOR_CAPACITY_CAP) as usize
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
    accumulator: &mut MonomialMap<N, F>,
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
    accumulator: &mut MonomialMap<N, F>,
    buffer: &mut Vec<(Monomial<N>, F)>,
) {
    for (monomial, coefficient) in buffer.drain(..) {
        merge(accumulator, monomial, coefficient);
    }
}

/// Drop the monomials that cancelled and hand back a canonical polynomial.
fn finish<const N: usize, F: FiniteField>(
    mut accumulator: MonomialMap<N, F>,
) -> SparseMultiPoly<N, F> {
    accumulator.retain(|_monomial, c| !c.is_zero());
    SparseMultiPoly { terms: accumulator }
}

/// [`MultiplyRoute::Heap`] as a `SparseMultiPoly`. The order is immaterial to the polynomial; grevlex
/// is the one F4 runs under, so it is the one measured.
fn multiply_heap<const N: usize, F: FiniteField>(
    a: &SparseMultiPoly<N, F>,
    b: &SparseMultiPoly<N, F>,
) -> SparseMultiPoly<N, F> {
    let sorted = multiply_sorted(a, b, MonomialOrder::GradedReverseLexicographic);
    let mut terms = MonomialMap::with_capacity_and_hasher(sorted.len(), BuildMonomialHasher);
    terms.extend(sorted);
    SparseMultiPoly { terms }
}

/// The terms of `a * b`, strictly descending under `order`, with cancelled monomials dropped.
///
/// The heap merge of Monagan and Pearce ("Polynomial division using dynamic arrays, heaps, and
/// packed exponent vectors", CASC 2007; "Parallel sparse polynomial multiplication using heaps",
/// ISSAC 2009), after Johnson (1974). Rows are the shorter operand's terms and columns the
/// longer's, both sorted descending; because a monomial order is multiplicative, row `i`'s
/// products `r_i · c_0 > r_i · c_1 > …` are already in order, and the heap merges the rows. Their
/// refinement is kept: row `i + 1` enters only when `(i, 0)` leaves, so the heap never holds more
/// than one entry per row. Their *chaining* of equal monomials inside the heap is not
/// implemented; equal monomials are instead merged as they are popped, which is the same output
/// for one comparison more per collision.
pub(crate) fn multiply_sorted<const N: usize, F: FiniteField>(
    a: &SparseMultiPoly<N, F>,
    b: &SparseMultiPoly<N, F>,
    order: MonomialOrder,
) -> Vec<(Monomial<N>, F)> {
    if a.terms.is_empty() || b.terms.is_empty() {
        return Vec::new();
    }
    // Matched once so that each built-in order's comparison inlines into the heap's sift loops
    // instead of being re-dispatched per comparison.
    match order {
        MonomialOrder::Lexicographic => {
            heap_product(a, b, |x, y| MonomialOrder::Lexicographic.cmp(x, y))
        }
        MonomialOrder::GradedLexicographic => {
            heap_product(a, b, |x, y| MonomialOrder::GradedLexicographic.cmp(x, y))
        }
        MonomialOrder::GradedReverseLexicographic => heap_product(a, b, |x, y| {
            MonomialOrder::GradedReverseLexicographic.cmp(x, y)
        }),
        other => heap_product(a, b, move |x, y| other.cmp(x, y)),
    }
}

/// One pending product in the heap: `rows[row] · cols[col]`, with its monomial formed once.
struct HeapEntry<const N: usize> {
    monomial: Monomial<N>,
    row: usize,
    col: usize,
}

/// A binary max-heap of [`HeapEntry`] under a runtime monomial order, which `BinaryHeap` cannot
/// take without an `Ord` wrapper carrying the order in every element.
struct ProductHeap<const N: usize, C> {
    entries: Vec<HeapEntry<N>>,
    cmp: C,
}

impl<const N: usize, C: Fn(&Monomial<N>, &Monomial<N>) -> Ordering> ProductHeap<N, C> {
    #[inline]
    fn greater(&self, i: usize, j: usize) -> bool {
        (self.cmp)(&self.entries[i].monomial, &self.entries[j].monomial) == Ordering::Greater
    }

    fn push(&mut self, entry: HeapEntry<N>) {
        self.entries.push(entry);
        let mut child = self.entries.len() - 1;
        while child > 0 {
            let parent = (child - 1) / 2;
            if !self.greater(child, parent) {
                break;
            }
            self.entries.swap(child, parent);
            child = parent;
        }
    }

    fn pop(&mut self) -> Option<HeapEntry<N>> {
        let last = self.entries.len().checked_sub(1)?;
        self.entries.swap(0, last);
        let top = self.entries.pop();
        let len = self.entries.len();
        let mut parent = 0;
        loop {
            let left = 2 * parent + 1;
            if left >= len {
                break;
            }
            let right = left + 1;
            let larger = if right < len && self.greater(right, left) {
                right
            } else {
                left
            };
            if !self.greater(larger, parent) {
                break;
            }
            self.entries.swap(parent, larger);
            parent = larger;
        }
        top
    }

    fn top(&self) -> Option<&Monomial<N>> {
        self.entries.first().map(|e| &e.monomial)
    }
}

/// The heap merge itself, under a comparison `cmp` that must be a monomial order.
fn heap_product<const N: usize, F: FiniteField, C>(
    a: &SparseMultiPoly<N, F>,
    b: &SparseMultiPoly<N, F>,
    cmp: C,
) -> Vec<(Monomial<N>, F)>
where
    C: Fn(&Monomial<N>, &Monomial<N>) -> Ordering,
{
    let (shorter, longer) = if a.terms.len() <= b.terms.len() {
        (a, b)
    } else {
        (b, a)
    };
    let rows = descending(shorter, &cmp);
    let cols = descending(longer, &cmp);
    let mut heap = ProductHeap {
        entries: Vec::with_capacity(rows.len()),
        cmp,
    };
    let entry = |row: usize, col: usize| HeapEntry {
        monomial: &rows[row].0 * &cols[col].0,
        row,
        col,
    };
    heap.push(entry(0, 0));

    let mut out: Vec<(Monomial<N>, F)> = Vec::new();
    while let Some(&monomial) = heap.top() {
        let mut coefficient = F::zero();
        while heap.top() == Some(&monomial) {
            let HeapEntry { row, col, .. } = heap.pop().expect("the top was just read");
            coefficient += rows[row].1 * cols[col].1;
            // Both successors are strictly below `monomial`, so the equal entries still waiting
            // stay on top.
            if col == 0 && row + 1 < rows.len() {
                heap.push(entry(row + 1, 0));
            }
            if col + 1 < cols.len() {
                heap.push(entry(row, col + 1));
            }
        }
        if !coefficient.is_zero() {
            out.push((monomial, coefficient));
        }
    }
    out
}

/// The terms of `p`, sorted descending by `cmp`.
fn descending<const N: usize, F: FiniteField, C>(
    p: &SparseMultiPoly<N, F>,
    cmp: &C,
) -> Vec<(Monomial<N>, F)>
where
    C: Fn(&Monomial<N>, &Monomial<N>) -> Ordering,
{
    let mut terms: Vec<(Monomial<N>, F)> = p.terms.iter().map(|(m, c)| (*m, *c)).collect();
    terms.sort_unstable_by(|x, y| cmp(&y.0, &x.0));
    terms
}

/// `multiply_sorted`, reachable from an example binary so that the ordered output can be
/// measured against accumulating and then sorting.
#[doc(hidden)]
pub fn multiply_multivariate_sorted_unstable<const N: usize, F: FiniteField>(
    a: &SparseMultiPoly<N, F>,
    b: &SparseMultiPoly<N, F>,
    order: MonomialOrder,
) -> Vec<(Monomial<N>, F)> {
    multiply_sorted(a, b, order)
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
    use crate::{
        fields::PrimeFieldElement64, BlockOrder, BlockOrderKind, MonomialOrder, One,
        WeightedTieBreak, Zero,
    };
    use proptest::{collection::vec, prelude::*, test_runner::TestRunner};

    /// Every route, with the chunk sizes the sweep covers.
    const ALL_ROUTES: [MultiplyRoute; 7] = [
        MultiplyRoute::Materialize,
        MultiplyRoute::Accumulate,
        MultiplyRoute::Chunked { rows: 1 },
        MultiplyRoute::Chunked { rows: 7 },
        MultiplyRoute::Chunked { rows: 64 },
        MultiplyRoute::DenseTriangle,
        MultiplyRoute::Heap,
    ];

    /// A strategy for a polynomial of at most `num_terms` distinct monomials over any field.
    fn poly_strategy<const N: usize, F: FiniteField + Arbitrary>(
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
    fn assert_routes_agree<const N: usize, F: FiniteField + Arbitrary>() {
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

    // `simplex_len` is the exact monomial count in one, two and three variables.
    #[test]
    fn test_monomial_count_bound_is_exact() {
        assert_eq!(simplex_len::<1>(7), 8);
        assert_eq!(simplex_len::<2>(7), 36);
        assert_eq!(simplex_len::<2>(729), 266_815);
        assert_eq!(simplex_len::<3>(4), 35);
        // Saturates rather than overflowing once the count leaves `u64`.
        assert_eq!(simplex_len::<32>(u32::MAX as u64), u64::MAX);
    }

    // A dense bivariate pair is routed to the triangle; the general case is routed to the chunked
    // accumulator; a small product keeps the materialising route.
    #[test]
    fn test_route_selects_by_density_not_by_arity() {
        type F = PrimeFieldElement64<541>;

        // A dense bivariate pair takes the triangle at every size, small included: there is no
        // small-operand tier to fall into.
        let small: SparseMultiPoly<2, F> = dense_triangle(8, 1);
        assert_eq!(route(&small, &small), MultiplyRoute::DenseTriangle);

        let dense: SparseMultiPoly<2, F> = dense_triangle(200, 1);
        assert_eq!(route(&dense, &dense), MultiplyRoute::DenseTriangle);

        // Bivariate and sparse: two terms spanning degree 20 000, whose triangle would be
        // hundreds of millions of slots for a handful of output terms.
        let sparse: SparseMultiPoly<2, F> = SparseMultiPoly::new(&[
            (Monomial::<2>::new(&[20_000, 0]), F::one()),
            (Monomial::<2>::new(&[0, 20_000]), F::one()),
        ]);
        let wide = &sparse * &dense;
        assert_eq!(
            route(&wide, &wide),
            MultiplyRoute::Accumulate,
            "a sparse bivariate pair must not be forced into a dense triangle"
        );

        // One term against many — the reduction inner step. The output is exactly `|a|` terms and
        // the triangle is 20 910 slots for 20 301 of them, so the triangle is the right accumulator
        // even though the single term is dense in nothing. An earlier predicate tested each operand
        // for density and sent this to the accumulator, at 1.5x the time.
        let single: SparseMultiPoly<2, F> =
            SparseMultiPoly::new(&[(Monomial::<2>::new(&[2, 1]), F::new(7))]);
        assert_eq!(route(&dense, &single), MultiplyRoute::DenseTriangle);
        assert_eq!(
            multiply_by(&dense, &single, MultiplyRoute::DenseTriangle),
            multiply_by(&dense, &single, MultiplyRoute::Materialize)
        );

        // Two lone terms, though, are not worth a triangle: 1 product against 66 slots.
        let other: SparseMultiPoly<2, F> =
            SparseMultiPoly::new(&[(Monomial::<2>::new(&[3, 4]), F::new(2))]);
        assert_eq!(route(&single, &other), MultiplyRoute::Accumulate);

        // Arity alone does not select the triangle: the index is bivariate, so a trivariate pair
        // cannot reach it however dense it is. #362 then gave this pair a dense route of its own —
        // it is dense in x and y and linear in z, so its bounding box is 79 * 79 * 3 cells for 2.56
        // million products — which is the point of asserting the negative rather than `Accumulate`.
        let trivariate: SparseMultiPoly<3, F> = {
            let mut terms: Vec<(Monomial<3>, F)> = Vec::new();
            for x in 0..40u32 {
                for y in 0..40u32 {
                    terms.push((Monomial::<3>::new(&[x, y, 1]), F::new(1 + x as u64)));
                }
            }
            SparseMultiPoly::new(&terms)
        };
        assert_ne!(
            route(&trivariate, &trivariate),
            MultiplyRoute::DenseTriangle
        );
        assert_eq!(route(&trivariate, &trivariate), MultiplyRoute::DenseBox);
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

    // === the dense accumulator past N = 2 (#362) ===

    /// A strategy for a polynomial of at most `num_terms` monomials with exponents at most
    /// `max_exponent`.
    ///
    /// Bounded, where [`poly_strategy`] draws exponents up to 16: a dense route's cell count is
    /// `C(2·16·N + N, N)` for the simplex, which at `N = 4` is 12.6 million cells for a four-term
    /// operand. The differential test is about agreement, not about size, so the size is capped
    /// and the arity varied instead.
    fn bounded_poly_strategy<const N: usize, F: FiniteField + Arbitrary>(
        num_terms: usize,
        max_exponent: u32,
    ) -> impl Strategy<Value = SparseMultiPoly<N, F>> {
        (
            vec(vec(0u32..=max_exponent, N), num_terms),
            vec(F::arbitrary(), num_terms),
        )
            .prop_map(|(exponents, coefficients)| {
                let terms: Vec<(Monomial<N>, F)> = exponents
                    .into_iter()
                    .map(|e| Monomial::<N>::new(&e))
                    .zip(coefficients)
                    .collect();
                SparseMultiPoly::new(&terms)
            })
    }

    /// The dense routes agree with [`multiply_materialize`] over `F` in `N` variables.
    fn assert_dense_routes_agree<const N: usize, F: FiniteField + Arbitrary>(max_exponent: u32) {
        let strategy = (
            bounded_poly_strategy::<N, F>(5, max_exponent),
            bounded_poly_strategy::<N, F>(5, max_exponent),
        );
        TestRunner::deterministic()
            .run(&strategy, |(a, b)| {
                let reference = multiply_by(&a, &b, MultiplyRoute::Materialize);
                for route in [
                    MultiplyRoute::Accumulate,
                    MultiplyRoute::DenseSimplex,
                    MultiplyRoute::DenseBox,
                    MultiplyRoute::Heap,
                ] {
                    let product = multiply_by(&a, &b, route);
                    prop_assert_eq!(
                        &product,
                        &reference,
                        "{:?} disagrees with the materialising reference at N = {}",
                        route,
                        N
                    );
                    // And the canonical invariant: no cell that cancelled is kept at zero.
                    prop_assert!(product.terms.values().all(|c| !c.is_zero()));
                }
                Ok(())
            })
            .unwrap();
    }

    // The simplex and the box agree with the materialising route and with the accumulator, over
    // every field, at four arities including the N = 3 and N = 4 #362 names.
    for_each_field!(
        fn the_dense_routes_agree_at_every_arity<F>() {
            assert_dense_routes_agree::<1, F>(8);
            assert_dense_routes_agree::<2, F>(6);
            assert_dense_routes_agree::<3, F>(4);
            assert_dense_routes_agree::<4, F>(3);
        }
    );

    /// The dense trivariate simplex of total degree `degree`, every coefficient nonzero.
    fn dense_simplex_3<F: FiniteField>(degree: u32, seed: u64) -> SparseMultiPoly<3, F> {
        let mut terms: Vec<(Monomial<3>, F)> = Vec::new();
        for x in 0..=degree {
            for y in 0..=(degree - x) {
                for z in 0..=(degree - x - y) {
                    terms.push((
                        Monomial::<3>::new(&[x, y, z]),
                        F::new(1 + (seed + x as u64 * 31 + y as u64 * 7 + z as u64) % 97),
                    ));
                }
            }
        }
        SparseMultiPoly::new(&terms)
    }

    // Both dense predicates refuse a sparse high-degree pair and accept a dense one: the two
    // failure directions, at N = 3 where the cell count grows as the cube rather than the square.
    #[test]
    fn test_the_dense_predicates_refuse_a_sparse_pair_and_accept_a_dense_one() {
        type F = PrimeFieldElement64<541>;

        // Three lone terms spanning degree 20 000. The simplex would be C(40 003, 3) — about
        // 1.1e13 cells — for at most 6 distinct output monomials, and the box 20 001^3.
        let sparse: SparseMultiPoly<3, F> = SparseMultiPoly::new(&[
            (Monomial::<3>::new(&[20_000, 0, 0]), F::one()),
            (Monomial::<3>::new(&[0, 20_000, 0]), F::one()),
            (Monomial::<3>::new(&[0, 0, 20_000]), F::one()),
        ]);
        assert!(!dense_simplex_profitable(&sparse, &sparse));
        assert!(dense_box_profitable(&sparse, &sparse).is_none());

        // A dense trivariate pair: 1 771 terms a side, and the product fills the simplex of
        // degree 40 exactly, so the estimate is not merely close but right.
        let dense: SparseMultiPoly<3, F> = dense_simplex_3(20, 1);
        assert_eq!(dense.terms.len(), 1771);
        assert!(dense_simplex_profitable(&dense, &dense));
        assert!(dense_box_profitable(&dense, &dense).is_some());
    }

    // One term against many — the reduction inner step — is where the two layouts part company.
    #[test]
    fn test_the_box_refuses_the_reduction_inner_step_the_simplex_accepts() {
        type F = PrimeFieldElement64<541>;
        let dense: SparseMultiPoly<3, F> = dense_simplex_3(20, 1);
        let single: SparseMultiPoly<3, F> =
            SparseMultiPoly::new(&[(Monomial::<3>::new(&[1, 1, 1]), F::new(7))]);

        // The output is exactly `|dense|` terms. The simplex of degree 23 is C(26, 3) = 2 600 cells
        // against 1 771 products, inside the 4x ratio — the same case #243 found its first
        // predicate rejecting at N = 2, for 1.5x.
        assert_eq!(simplex_len::<3>(23), 2600);
        assert!(dense_simplex_profitable(&dense, &single));

        // The box is bounded per variable at 21 each, so 22^3 = 10 648 cells for the same 1 771
        // products — outside the ratio, and refused. This is the `N!` the box pays made concrete:
        // a total-degree-dense operand occupies a sixth of its own bounding box at N = 3, so the
        // box's separable index is unavailable exactly where the simplex's cell count is tight.
        assert_eq!(box_cells::<3>(&[21, 21, 21]), Some(10648));
        assert!(dense_box_profitable(&dense, &single).is_none());

        // And the dispatcher sends it to neither, because the products do not collide: 1 771
        // products produce exactly 1 771 monomials, so there is nothing for a dense accumulator to
        // merge. Measured at N = 3: 48.6 us accumulating against the simplex's 55.4 us and the
        // box's 73.5 us — the one shape where generalising the triangle's layout loses, and the
        // Groebner reduction inner step, so it is the one that had to be caught.
        assert_eq!(route(&dense, &single), MultiplyRoute::Accumulate);
        assert!(!dense_merging_is_worth_the_index(&dense, &single));

        // Where the products do collide, the same operands take a dense route: squaring the dense
        // operand is 3.1 million products for 12 341 monomials.
        assert!(dense_merging_is_worth_the_index(&dense, &dense));
        assert_eq!(route(&dense, &dense), MultiplyRoute::DenseBox);

        // At N = 2 the same shape keeps its dense route, because the triangle's index is three
        // integer operations and it wins anyway: 29.1 us against the accumulator's 44.1 us.
        let bivariate: SparseMultiPoly<2, F> = dense_triangle(56, 1);
        let bivariate_term: SparseMultiPoly<2, F> =
            SparseMultiPoly::new(&[(Monomial::<2>::new(&[2, 1]), F::new(7))]);
        assert_eq!(
            route(&bivariate, &bivariate_term),
            MultiplyRoute::DenseTriangle
        );

        // Both still compute the right answer when named directly.
        let reference = multiply_by(&dense, &single, MultiplyRoute::Accumulate);
        assert_eq!(
            multiply_by(&dense, &single, MultiplyRoute::DenseSimplex),
            reference
        );
        assert_eq!(
            multiply_by(&dense, &single, MultiplyRoute::DenseBox),
            reference
        );
    }

    // The box exploits a lopsided per-variable degree that the total-degree simplex cannot.
    #[test]
    fn test_the_box_is_tighter_than_the_simplex_when_one_variable_is_low_degree() {
        type F = PrimeFieldElement64<541>;
        // Dense in x and y to degree 30, linear in z — the shape a symbolic CICO build has when
        // one state word enters only linearly.
        let mut terms: Vec<(Monomial<3>, F)> = Vec::new();
        for x in 0..=30u32 {
            for y in 0..=30u32 {
                for z in 0..=1u32 {
                    terms.push((Monomial::<3>::new(&[x, y, z]), F::new(1 + x as u64)));
                }
            }
        }
        let lopsided: SparseMultiPoly<3, F> = SparseMultiPoly::new(&terms);

        // The product's total degree is 122, so the simplex is C(125, 3) = 317 750 cells for an
        // output of at most 61 * 61 * 3 = 11 163 monomials: the simplex is sized by the total
        // degree however lopsided the per-variable degrees are.
        assert_eq!(simplex_len::<3>(122), 317_750);
        // The box is 61 * 61 * 3, which is the output exactly.
        assert_eq!(box_cells::<3>(&[60, 60, 2]), Some(11_163));
        assert!(dense_box_profitable(&lopsided, &lopsided).is_some());

        let reference = multiply_by(&lopsided, &lopsided, MultiplyRoute::Accumulate);
        assert_eq!(
            multiply_by(&lopsided, &lopsided, MultiplyRoute::DenseBox),
            reference
        );
    }

    // A degree whose triangle cannot be indexed is refused by the predicate, so the operator never
    // reaches the route that would have to allocate it.
    #[test]
    fn test_dense_triangle_refuses_an_unindexable_degree() {
        type F = PrimeFieldElement64<541>;
        let p: SparseMultiPoly<2, F> =
            SparseMultiPoly::new(&[(Monomial::<2>::new(&[u32::MAX, 0]), F::one())]);
        assert!(!dense_triangle_profitable(&p, &p));
        assert_eq!(route(&p, &p), MultiplyRoute::Accumulate);
    }

    // === the heap route (#443) ===

    /// The orders the sorted product is checked under at arity `N`: the three built-ins, a
    /// weighted order and, past one variable, a block order.
    fn orders<const N: usize>() -> Vec<MonomialOrder> {
        let weights: Vec<u32> = (1..=N as u32).collect();
        let mut orders = vec![
            MonomialOrder::Lexicographic,
            MonomialOrder::GradedLexicographic,
            MonomialOrder::GradedReverseLexicographic,
            MonomialOrder::weighted(&weights, WeightedTieBreak::ReverseLexicographic).unwrap(),
        ];
        if N >= 2 {
            orders.push(MonomialOrder::Block(
                BlockOrder::checked(
                    N,
                    N / 2,
                    BlockOrderKind::GradedReverseLexicographic,
                    BlockOrderKind::Lexicographic,
                )
                .unwrap(),
            ));
        }
        orders
    }

    /// Whether `terms` is strictly descending under `order`.
    fn strictly_descending<const N: usize, F: FiniteField>(
        terms: &[(Monomial<N>, F)],
        order: MonomialOrder,
    ) -> bool {
        terms
            .windows(2)
            .all(|w| order.cmp(&w[0].0, &w[1].0) == std::cmp::Ordering::Greater)
    }

    /// The sorted product is the reference product's terms, strictly descending under each order.
    fn assert_sorted_product<const N: usize, F: FiniteField + Arbitrary>(
        strategy: impl Strategy<Value = (SparseMultiPoly<N, F>, SparseMultiPoly<N, F>)>,
    ) {
        TestRunner::deterministic()
            .run(&strategy, |(a, b)| {
                let reference = multiply_by(&a, &b, MultiplyRoute::Materialize);
                for order in orders::<N>() {
                    let sorted = multiply_sorted(&a, &b, order);
                    prop_assert!(
                        strictly_descending(&sorted, order),
                        "not strictly descending under {:?}",
                        order
                    );
                    prop_assert!(sorted.iter().all(|(_, c)| !c.is_zero()));
                    prop_assert_eq!(sorted.len(), reference.terms.len());
                    prop_assert_eq!(SparseMultiPoly::new(&sorted), reference.clone());
                }
                Ok(())
            })
            .unwrap();
    }

    // The heap's sorted product is the materialising product in strictly descending order, under
    // every order kind, over every field, at arities 1 to 6, on sparse and on collision-heavy
    // operands.
    for_each_field!(
        fn the_heap_emits_the_product_in_order<F>() {
            assert_sorted_product::<1, F>((poly_strategy(6), poly_strategy(6)));
            assert_sorted_product::<2, F>((poly_strategy(6), poly_strategy(6)));
            assert_sorted_product::<3, F>((
                bounded_poly_strategy(8, 2),
                bounded_poly_strategy(8, 2),
            ));
            assert_sorted_product::<4, F>((poly_strategy(5), poly_strategy(7)));
            assert_sorted_product::<6, F>((
                bounded_poly_strategy(6, 1),
                bounded_poly_strategy(9, 3),
            ));
        }
    );

    // Zero, constant and single-term operands on either side give the reference product on the
    // heap route, sorted, at an arity no dense route is selected for.
    #[test]
    fn test_the_heap_handles_zero_constant_and_monomial_operands() {
        type F = PrimeFieldElement64<541>;
        let p: SparseMultiPoly<5, F> = SparseMultiPoly::new(&[
            (Monomial::<5>::new(&[3, 0, 1, 0, 9]), F::new(4)),
            (Monomial::<5>::new(&[0, 7, 0, 2, 0]), F::new(540)),
            (Monomial::<5>::new(&[1, 1, 1, 1, 1]), F::new(2)),
        ]);
        let zero: SparseMultiPoly<5, F> = SparseMultiPoly::zero();
        let constant: SparseMultiPoly<5, F> =
            SparseMultiPoly::new(&[(Monomial::<5>::one(), F::new(3))]);
        let monomial: SparseMultiPoly<5, F> =
            SparseMultiPoly::new(&[(Monomial::<5>::new(&[0, 2, 0, 0, 1]), F::one())]);
        let order = MonomialOrder::GradedReverseLexicographic;
        for other in [&zero, &constant, &monomial, &p] {
            for (left, right) in [(&p, other), (other, &p)] {
                let reference = multiply_by(left, right, MultiplyRoute::Materialize);
                assert_eq!(multiply_by(left, right, MultiplyRoute::Heap), reference);
                let sorted = multiply_sorted(left, right, order);
                assert_eq!(SparseMultiPoly::new(&sorted), reference);
                assert!(strictly_descending(&sorted, order));
            }
        }
        assert!(multiply_sorted(&zero, &zero, order).is_empty());
    }

    // The sorted product's cancellation is the canonical one: a monomial whose coefficients cancel
    // is absent, not present at zero, so (x + y)^6 * (x + y) over GF(7) is two terms.
    #[test]
    fn test_the_sorted_product_drops_cancelled_terms() {
        type F = PrimeFieldElement64<7>;
        let p: SparseMultiPoly<2, F> = SparseMultiPoly::new(&[
            (Monomial::<2>::new(&[1, 0]), F::one()),
            (Monomial::<2>::new(&[0, 1]), F::one()),
        ]);
        let mut sixth = p.clone();
        for _ in 1..6 {
            sixth = &sixth * &p;
        }
        let sorted = multiply_sorted(&sixth, &p, MonomialOrder::Lexicographic);
        assert_eq!(
            sorted,
            vec![
                (Monomial::<2>::new(&[7, 0]), F::one()),
                (Monomial::<2>::new(&[0, 7]), F::one()),
            ]
        );
    }

    // The heap is not what `route` selects on the sparse high-arity shape it was measured on: it
    // stays reachable by name only.
    #[test]
    fn test_route_does_not_select_the_heap() {
        type F = PrimeFieldElement64<541>;
        let sparse: SparseMultiPoly<6, F> = SparseMultiPoly::new(&[
            (Monomial::<6>::new(&[9, 0, 0, 0, 0, 1]), F::one()),
            (Monomial::<6>::new(&[0, 9, 0, 0, 1, 0]), F::one()),
            (Monomial::<6>::new(&[0, 0, 9, 1, 0, 0]), F::one()),
        ]);
        assert_eq!(route(&sparse, &sparse), MultiplyRoute::Accumulate);
    }
}
