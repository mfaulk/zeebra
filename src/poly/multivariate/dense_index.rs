//! Flat indices for the dense accumulators, and the enumerations that invert them.
//!
//! #243's bivariate route won by doing **no hashing at all**: where the product fills the
//! total-degree triangle, `slots[index(i, j)] += a * b` needs no monomial key, and that was 3x–6x
//! faster than one hash lookup per product. Generalising it past `N = 2` (#362) is a question about
//! the index, because at `N = 2` the index is three integer operations and nothing else in the
//! inner loop. Two generalisations are offered here and they trade against each other:
//!
//! - [`SimplexIndex`] ranks the monomials of total degree at most `d` — `C(d + N, N)` cells, the
//!   tightest dense layout there is. Its rank is **not separable**: the index of `a·b` cannot be
//!   derived from the indices of `a` and `b`, so it costs `2(N - 1)` table lookups and as many adds
//!   per product. A precomputed Pascal table is what keeps that from being `O(N^2)` multiplies.
//! - [`BoxIndex`] is a mixed-radix index over the per-variable degree bounds — `∏(d_i + 1)` cells.
//!   It is **separable**, `index(a·b) = index(a) + index(b)`, so the left operand's index hoists out
//!   of the inner loop and the per-product cost is one add, independent of `N`. It pays for that in
//!   cells: for an operand pair dense in the total-degree sense the box is about `N!` times the
//!   simplex, since the simplex is the corner of the box cut by `Σ e_i <= d`.
//!
//! So neither dominates, and which one — if either — beats hashing at a given arity is a
//! measurement. Both enumerate their cells in exactly index order, which is what lets the output
//! pass read the slots with a counter instead of inverting the rank.

use std::collections::HashMap;

use crate::{FiniteField, Monomial};

/// `C(m, k)` for every `m <= max_m` and every `k <= N`, by Pascal's rule.
///
/// The simplex rank needs `C(m, k)` at `N` different `k` and a different `m` per product, which as
/// a formula is a product of `k` terms — `O(N^2)` multiplies per product once the loop over
/// variables is counted. Tabulated it is a load. The table is `(max_m + 1)(N + 1)` words, a few
/// kilobytes at the degrees the route is ever selected for, so it stays in cache alongside the
/// slots it indexes.
pub(crate) struct Pascal {
    row_len: usize,
    values: Vec<u64>,
}

impl Pascal {
    /// `C(m, k)` for `0 <= m <= max_m`, `0 <= k <= max_k`.
    pub(crate) fn new(max_m: usize, max_k: usize) -> Self {
        let row_len = max_m + 1;
        let mut values = vec![0u64; row_len * (max_k + 1)];
        // C(m, 0) = 1.
        for m in 0..row_len {
            values[m] = 1;
        }
        for k in 1..=max_k {
            for m in k..row_len {
                values[k * row_len + m] =
                    values[(k - 1) * row_len + m - 1] + values[k * row_len + m - 1];
            }
        }
        Self { row_len, values }
    }

    #[inline]
    fn get(&self, m: usize, k: usize) -> u64 {
        self.values[k * self.row_len + m]
    }
}

/// Ranks the monomials of total degree at most `degree` in `N` variables onto `0..C(degree + N, N)`.
///
/// Graded first, then by `e_0` ascending, then recursively: exactly the order
/// [`walk_simplex`] enumerates, so a dense output can be read back with a counter.
pub(crate) struct SimplexIndex<const N: usize> {
    pascal: Pascal,
}

impl<const N: usize> SimplexIndex<N> {
    pub(crate) fn new(degree: u32) -> Self {
        Self {
            // `degree + N` is the largest first argument `rank` asks for, from the block base
            // `C(t - 1 + N, N)` at `t = degree`.
            pascal: Pascal::new(degree as usize + N, N),
        }
    }

    /// The rank of the monomial with these exponents.
    ///
    /// The block of total degree `t` starts at `C(t - 1 + N, N)`, the count of monomials below it.
    /// Within the block, fixing `e_i` skips the compositions with a smaller `e_i`, and by the
    /// hockey-stick identity that count is a difference of two binomials rather than a sum over
    /// them. The last exponent is determined by the others, so the loop stops one short.
    #[inline]
    pub(crate) fn rank(&self, exponents: &[u32; N]) -> usize {
        let mut remaining: usize = exponents.iter().map(|e| *e as usize).sum();
        // `C(t - 1 + N, N)`, which is 0 at `t = 0` because `N - 1 < N`.
        let mut rank = self.pascal.get(remaining + N - 1, N);
        for i in 0..N - 1 {
            let k = N - i - 1;
            let exponent = exponents[i] as usize;
            rank +=
                self.pascal.get(remaining + k, k) - self.pascal.get(remaining - exponent + k, k);
            remaining -= exponent;
        }
        rank as usize
    }
}

/// `C(degree + N, N)`, the number of monomials of total degree at most `degree` in `N` variables.
///
/// Saturating: the count leaves `u64` for a modest degree once `N` is large, and a saturated bound
/// is still a bound.
pub(crate) fn simplex_len<const N: usize>(degree: u64) -> u64 {
    let mut count: u128 = 1;
    for i in 1..=(N as u128) {
        count = count.saturating_mul(degree as u128 + i) / i;
        if count > u64::MAX as u128 {
            return u64::MAX;
        }
    }
    count as u64
}

/// A mixed-radix index over per-variable exponent bounds, row-major with the last variable fastest.
///
/// Separable by construction — `rank` is `Σ e_i · stride_i` and the strides do not depend on the
/// other exponents — so the index of a product is the sum of the indices of its factors and the
/// left operand's can be hoisted out of the inner loop.
pub(crate) struct BoxIndex<const N: usize> {
    bounds: [u32; N],
    strides: [usize; N],
    cells: usize,
}

impl<const N: usize> BoxIndex<N> {
    /// # Panics
    /// Panics unless `∏(bounds[i] + 1)` fits in a `usize`; [`box_cells`] is the test the callers
    /// make first.
    pub(crate) fn new(bounds: [u32; N]) -> Self {
        let mut strides = [0usize; N];
        let mut stride: usize = 1;
        for i in (0..N).rev() {
            strides[i] = stride;
            stride = stride
                .checked_mul(bounds[i] as usize + 1)
                .expect("the box does not fit in a usize");
        }
        Self {
            bounds,
            strides,
            cells: stride,
        }
    }

    pub(crate) fn cells(&self) -> usize {
        self.cells
    }

    /// The index of these exponents — valid for a *factor* as much as for a product, which is the
    /// point: `rank(a) + rank(b) == rank(a + b)`.
    #[inline]
    pub(crate) fn rank(&self, exponents: &[u32; N]) -> usize {
        let mut index = 0usize;
        for i in 0..N {
            index += exponents[i] as usize * self.strides[i];
        }
        index
    }
}

/// `∏(bounds[i] + 1)`, or `None` if that leaves `u64`.
pub(crate) fn box_cells<const N: usize>(bounds: &[u32; N]) -> Option<u64> {
    let mut cells: u64 = 1;
    for bound in bounds.iter() {
        cells = cells.checked_mul(*bound as u64 + 1)?;
    }
    Some(cells)
}

/// Read the simplex's slots back as terms, dropping the cells that are zero.
///
/// A counter rather than an inverse rank: the enumeration below visits the cells in exactly the
/// order [`SimplexIndex::rank`] assigns, so position in the walk *is* the index.
pub(crate) fn collect_simplex<const N: usize, F: FiniteField>(
    slots: &[F],
    degree: u64,
) -> HashMap<Monomial<N>, F> {
    // Counted first so the map is sized once, which is the whole point of having come this far
    // without hashing.
    let occupied = slots.iter().filter(|c| !c.is_zero()).count();
    let mut terms: HashMap<Monomial<N>, F> = HashMap::with_capacity(occupied);
    let mut exponents = [0u32; N];
    let mut cursor = 0usize;
    for total in 0..=degree {
        walk_simplex(
            0,
            total as u32,
            &mut exponents,
            &mut cursor,
            slots,
            &mut terms,
        );
    }
    debug_assert_eq!(cursor, slots.len(), "the walk did not visit every cell");
    terms
}

/// Visit the exponent vectors of total degree exactly `remaining` over variables `index..N`.
fn walk_simplex<const N: usize, F: FiniteField>(
    index: usize,
    remaining: u32,
    exponents: &mut [u32; N],
    cursor: &mut usize,
    slots: &[F],
    terms: &mut HashMap<Monomial<N>, F>,
) {
    if index == N - 1 {
        exponents[index] = remaining;
        let coefficient = slots[*cursor];
        *cursor += 1;
        // Drop-on-cancel: an untouched cell and a cancelled one are the same thing here.
        if !coefficient.is_zero() {
            terms.insert(Monomial::new(exponents), coefficient);
        }
        exponents[index] = 0;
        return;
    }
    for exponent in 0..=remaining {
        exponents[index] = exponent;
        walk_simplex(
            index + 1,
            remaining - exponent,
            exponents,
            cursor,
            slots,
            terms,
        );
    }
    exponents[index] = 0;
}

/// Read the box's slots back as terms, dropping the cells that are zero.
pub(crate) fn collect_box<const N: usize, F: FiniteField>(
    slots: &[F],
    index: &BoxIndex<N>,
) -> HashMap<Monomial<N>, F> {
    let occupied = slots.iter().filter(|c| !c.is_zero()).count();
    let mut terms: HashMap<Monomial<N>, F> = HashMap::with_capacity(occupied);
    let mut exponents = [0u32; N];
    let mut cursor = 0usize;
    walk_box(
        0,
        &index.bounds,
        &mut exponents,
        &mut cursor,
        slots,
        &mut terms,
    );
    debug_assert_eq!(cursor, slots.len(), "the walk did not visit every cell");
    terms
}

/// Visit the exponent vectors of the box over variables `index..N`, last variable fastest.
fn walk_box<const N: usize, F: FiniteField>(
    index: usize,
    bounds: &[u32; N],
    exponents: &mut [u32; N],
    cursor: &mut usize,
    slots: &[F],
    terms: &mut HashMap<Monomial<N>, F>,
) {
    if index == N {
        let coefficient = slots[*cursor];
        *cursor += 1;
        if !coefficient.is_zero() {
            terms.insert(Monomial::new(exponents), coefficient);
        }
        return;
    }
    for exponent in 0..=bounds[index] {
        exponents[index] = exponent;
        walk_box(index + 1, bounds, exponents, cursor, slots, terms);
    }
    exponents[index] = 0;
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `Pascal` is the binomial coefficient, including the zeros above the diagonal.
    #[test]
    fn test_pascal_is_the_binomial_coefficient() {
        let pascal = Pascal::new(12, 5);
        assert_eq!(pascal.get(0, 0), 1);
        assert_eq!(pascal.get(5, 1), 5);
        assert_eq!(pascal.get(5, 2), 10);
        assert_eq!(pascal.get(12, 5), 792);
        // `C(m, k) = 0` for `k > m`.
        assert_eq!(pascal.get(2, 5), 0);
        assert_eq!(pascal.get(4, 5), 0);
    }

    /// The simplex rank is a bijection onto `0..simplex_len(degree)`, at four arities.
    #[test]
    fn test_simplex_rank_is_a_bijection() {
        fn check<const N: usize>(degree: u32) {
            let index = SimplexIndex::<N>::new(degree);
            let len = simplex_len::<N>(degree as u64) as usize;
            let mut seen = vec![false; len];
            let mut exponents = [0u32; N];
            enumerate::<N>(0, degree, &mut exponents, &mut |e| {
                let rank = index.rank(e);
                assert!(rank < len, "rank {rank} for {e:?} is outside 0..{len}");
                assert!(!seen[rank], "rank {rank} is claimed twice");
                seen[rank] = true;
            });
            assert!(
                seen.iter().all(|s| *s),
                "the simplex at N = {N} has an unused cell"
            );
        }

        /// Every exponent vector of total degree at most `remaining` over variables `index..N`.
        fn enumerate<const N: usize>(
            index: usize,
            remaining: u32,
            exponents: &mut [u32; N],
            visit: &mut impl FnMut(&[u32; N]),
        ) {
            if index == N {
                visit(exponents);
                return;
            }
            for exponent in 0..=remaining {
                exponents[index] = exponent;
                enumerate::<N>(index + 1, remaining - exponent, exponents, visit);
            }
            exponents[index] = 0;
        }

        check::<1>(20);
        check::<2>(14);
        check::<3>(10);
        check::<4>(7);
        check::<5>(5);
    }

    /// The simplex rank agrees with #243's bivariate triangle on its slot count.
    #[test]
    fn test_simplex_len_matches_the_bivariate_triangle() {
        for degree in [0u64, 1, 7, 90, 729] {
            assert_eq!(
                simplex_len::<2>(degree),
                (degree + 1) * (degree + 2) / 2,
                "degree {degree}"
            );
        }
        assert_eq!(simplex_len::<3>(4), 35);
        // Saturates rather than overflowing once the count leaves `u64`.
        assert_eq!(simplex_len::<32>(u32::MAX as u64), u64::MAX);
    }

    /// The box index is separable: the index of a product is the sum of its factors' indices.
    #[test]
    fn test_box_index_is_separable() {
        let index = BoxIndex::<3>::new([6, 4, 9]);
        assert_eq!(index.cells(), 7 * 5 * 10);
        for a in [[0u32, 0, 0], [1, 2, 3], [3, 0, 4], [2, 2, 2]] {
            for b in [[0u32, 0, 0], [2, 1, 5], [1, 0, 0], [3, 2, 1]] {
                let sum = [a[0] + b[0], a[1] + b[1], a[2] + b[2]];
                assert_eq!(
                    index.rank(&a) + index.rank(&b),
                    index.rank(&sum),
                    "{a:?} + {b:?}"
                );
            }
        }
    }

    /// The box index is a bijection onto `0..cells`, and `box_cells` is that count.
    #[test]
    fn test_box_index_is_a_bijection() {
        let bounds = [3u32, 2, 4];
        let index = BoxIndex::<3>::new(bounds);
        assert_eq!(box_cells::<3>(&bounds), Some(index.cells() as u64));
        let mut seen = vec![false; index.cells()];
        for i in 0..=bounds[0] {
            for j in 0..=bounds[1] {
                for k in 0..=bounds[2] {
                    let rank = index.rank(&[i, j, k]);
                    assert!(!seen[rank], "rank {rank} is claimed twice");
                    seen[rank] = true;
                }
            }
        }
        assert!(seen.iter().all(|s| *s), "the box has an unused cell");
        // Refuses a product that would not fit rather than wrapping.
        assert_eq!(box_cells::<2>(&[u32::MAX, u32::MAX]), None);
    }
}
