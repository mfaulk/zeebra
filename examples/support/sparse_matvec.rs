// Research-only kernels for #87. Arithmetic is held fixed: every product is one field `*` and one
// field `+=`, exactly as `MultiplicationOperator::apply` does, so a format or block-width effect is
// a traversal effect and never a reduction-strategy effect.
use std::{
    ops::Range,
    sync::Barrier,
    thread,
    time::{Duration, Instant},
};

use zeebra::{linalg::sparse::SparseMatrix, FiniteField};

/// Compressed sparse rows with 32-bit offsets and column indices.
///
/// Holding the transpose turns the same arrays into compressed sparse columns, which is how
/// [`scatter`] uses it.
pub struct Csr<F> {
    pub n: usize,
    pub row_ptr: Vec<u32>,
    pub cols: Vec<u32>,
    pub values: Vec<F>,
}

impl<F: FiniteField> Csr<F> {
    /// An `n x n` matrix from per-row `(column, value)` lists. Zero values are dropped.
    ///
    /// # Panics
    /// If the entry count or a column does not fit 32 bits.
    pub fn from_rows(n: usize, rows: &[Vec<(usize, F)>]) -> Self {
        assert_eq!(rows.len(), n);
        let mut row_ptr = Vec::with_capacity(n + 1);
        let mut cols = Vec::new();
        let mut values = Vec::new();
        row_ptr.push(0);
        for row in rows {
            for &(column, value) in row {
                assert!(column < n);
                if !value.is_zero() {
                    cols.push(u32::try_from(column).expect("32-bit column"));
                    values.push(value);
                }
            }
            row_ptr.push(u32::try_from(cols.len()).expect("32-bit entry count"));
        }
        Self {
            n,
            row_ptr,
            cols,
            values,
        }
    }

    /// The matrix from its columns' `(row, value)` lists, i.e. from a column-major operator.
    pub fn from_columns(n: usize, columns: &[Vec<(usize, F)>]) -> Self {
        let mut rows = vec![Vec::new(); n];
        for (j, column) in columns.iter().enumerate() {
            for &(i, value) in column {
                rows[i].push((j, value));
            }
        }
        Self::from_rows(n, &rows)
    }

    /// The transpose, i.e. the same matrix in compressed sparse columns.
    pub fn transpose(&self) -> Self {
        let mut columns = vec![Vec::new(); self.n];
        for i in 0..self.n {
            for (column, value) in self.row(i) {
                columns[column].push((i, value));
            }
        }
        Self::from_rows(self.n, &columns)
    }

    pub fn nnz(&self) -> usize {
        self.cols.len()
    }

    /// Bytes the three arrays hold.
    pub fn bytes(&self) -> usize {
        4 * self.row_ptr.len() + 4 * self.cols.len() + std::mem::size_of::<F>() * self.values.len()
    }

    pub fn row(&self, i: usize) -> impl Iterator<Item = (usize, F)> + '_ {
        let range = self.row_ptr[i] as usize..self.row_ptr[i + 1] as usize;
        self.cols[range.clone()]
            .iter()
            .zip(&self.values[range])
            .map(|(&c, &v)| (c as usize, v))
    }

    /// Rows split into `parts` contiguous ranges of roughly equal entries-plus-rows work.
    pub fn partition(&self, parts: usize) -> Vec<Range<usize>> {
        let total = self.nnz() + self.n;
        let mut ranges = Vec::with_capacity(parts);
        let mut start = 0;
        for part in 1..=parts {
            let target = total * part / parts;
            let mut end = start;
            while end < self.n && (self.row_ptr[end] as usize + end) < target {
                end += 1;
            }
            if part == parts {
                end = self.n;
            }
            ranges.push(start..end);
            start = end;
        }
        ranges
    }
}

/// `Y[rows] = A[rows] X` for `W` interleaved vectors: `X[k * W + b]` is coordinate `k` of vector
/// `b`, and `y` holds only the rows in `rows`. Each matrix entry is read once and used `W` times.
pub fn gather<F: FiniteField, const W: usize>(
    a: &Csr<F>,
    rows: Range<usize>,
    x: &[F],
    y: &mut [F],
) {
    debug_assert_eq!(y.len(), rows.len() * W);
    for (i, out) in rows.zip(y.as_chunks_mut::<W>().0) {
        let mut acc = [F::zero(); W];
        let range = a.row_ptr[i] as usize..a.row_ptr[i + 1] as usize;
        for (&c, &value) in a.cols[range.clone()].iter().zip(&a.values[range]) {
            let xs = &x[c as usize * W..][..W];
            for b in 0..W {
                acc[b] += value * xs[b];
            }
        }
        *out = acc;
    }
}

/// `Y = A X` from `A` held column-major (`at` is `A`'s transpose in CSR): the scatter shape of
/// `MultiplicationOperator::apply`, without its per-column enum and with zero inputs not skipped.
pub fn scatter<F: FiniteField, const W: usize>(at: &Csr<F>, x: &[F], y: &mut [F]) {
    y.fill(F::zero());
    for j in 0..at.n {
        let xs: [F; W] = x[j * W..][..W].try_into().expect("W coordinates");
        let range = at.row_ptr[j] as usize..at.row_ptr[j + 1] as usize;
        for (&k, &value) in at.cols[range.clone()].iter().zip(&at.values[range]) {
            let out = &mut y[k as usize * W..][..W];
            for b in 0..W {
                out[b] += value * xs[b];
            }
        }
    }
}

/// `y = A x` over the crate's own row-of-`(usize, F)` sparse matrix.
pub fn gather_rows<F: FiniteField>(a: &SparseMatrix<F>, x: &[F], y: &mut [F]) {
    for (row, out) in a.rows().iter().zip(y.iter_mut()) {
        let mut acc = F::zero();
        for &(c, value) in row.entries() {
            acc += value * x[c];
        }
        *out = acc;
    }
}

/// GF(2) with 64 vectors bit-packed into one word: `Y[i] = XOR over A[i][k] = 1 of X[k]`.
///
/// The minimal research alternative for GF(2) only. `a` is read for its pattern; its values are
/// all one, since every nonzero of GF(2) is.
pub fn gather_bits<F>(a: &Csr<F>, x: &[u64], y: &mut [u64]) {
    for (i, out) in y.iter_mut().enumerate() {
        let range = a.row_ptr[i] as usize..a.row_ptr[i + 1] as usize;
        *out = a.cols[range].iter().fold(0, |acc, &c| acc ^ x[c as usize]);
    }
}

/// `steps` dependent applications `X_{t+1} = A X_t` on one thread; returns `X_steps`.
#[cfg(test)]
pub fn krylov<F: FiniteField, const W: usize>(a: &Csr<F>, x0: &[F], steps: usize) -> Vec<F> {
    let mut x = x0.to_vec();
    let mut y = vec![F::zero(); x.len()];
    for _ in 0..steps {
        gather::<F, W>(a, 0..a.n, &x, &mut y);
        std::mem::swap(&mut x, &mut y);
    }
    x
}

struct SharedBuffers<F> {
    buffers: [*mut F; 2],
    len: usize,
}

// SAFETY: threads only ever form a shared slice of one buffer and a mutable slice of a disjoint
// row range of the other, and a barrier separates every step, so no two threads alias mutably
// and no read overlaps a write.
unsafe impl<F: Send> Sync for SharedBuffers<F> {}

/// As [`krylov`], over `threads` scoped workers that each own a contiguous row range and meet at a
/// barrier after every step, since step `t + 1` reads all of step `t`'s output.
///
/// Returns the final block and the wall time thread 0 saw between the first and last barrier, so
/// thread start-up is excluded and per-step synchronization is included.
pub fn krylov_parallel<F: FiniteField + Send + Sync, const W: usize>(
    a: &Csr<F>,
    x0: &[F],
    steps: usize,
    threads: usize,
) -> (Vec<F>, Duration) {
    let mut x = x0.to_vec();
    let mut y = vec![F::zero(); x.len()];
    let shared = SharedBuffers {
        buffers: [x.as_mut_ptr(), y.as_mut_ptr()],
        len: x.len(),
    };
    let parts = a.partition(threads);
    let barrier = Barrier::new(threads);
    let mut elapsed = Duration::ZERO;
    thread::scope(|scope| {
        let handles: Vec<_> = parts
            .iter()
            .map(|rows| {
                let (shared, barrier, rows) = (&shared, &barrier, rows.clone());
                scope.spawn(move || {
                    barrier.wait();
                    let start = Instant::now();
                    for step in 0..steps {
                        let (src, dst) = (shared.buffers[step % 2], shared.buffers[1 - step % 2]);
                        // SAFETY: see `SharedBuffers`.
                        let (src, dst) = unsafe {
                            (
                                std::slice::from_raw_parts(src, shared.len),
                                std::slice::from_raw_parts_mut(
                                    dst.add(rows.start * W),
                                    rows.len() * W,
                                ),
                            )
                        };
                        gather::<F, W>(a, rows.clone(), src, dst);
                        barrier.wait();
                    }
                    start.elapsed()
                })
            })
            .collect();
        let times: Vec<Duration> = handles.into_iter().map(|h| h.join().unwrap()).collect();
        elapsed = times[0];
    });
    let result = if steps.is_multiple_of(2) { x } else { y };
    (result, elapsed)
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::{rngs::StdRng, Rng, SeedableRng};
    use zeebra::{
        fields::{Zp2, Zp2147483647},
        linalg::sparse::SparseRow,
        One, Zero,
    };

    type F = Zp2147483647;

    fn random_rows<G: FiniteField>(n: usize, per_row: usize, seed: u64) -> Vec<Vec<(usize, G)>> {
        let mut rng = StdRng::seed_from_u64(seed);
        (0..n)
            .map(|_| {
                let mut row: Vec<(usize, G)> = (0..per_row)
                    .map(|_| (rng.gen_range(0..n), G::random(&mut rng)))
                    .collect();
                row.sort_by_key(|e| e.0);
                row.dedup_by_key(|e| e.0);
                row
            })
            .collect()
    }

    fn dense_product(rows: &[Vec<(usize, F)>], x: &[F]) -> Vec<F> {
        rows.iter()
            .map(|row| row.iter().fold(F::zero(), |acc, &(c, v)| acc + v * x[c]))
            .collect()
    }

    fn random_vector<G: FiniteField>(len: usize, seed: u64) -> Vec<G> {
        let mut rng = StdRng::seed_from_u64(seed);
        (0..len).map(|_| G::random(&mut rng)).collect()
    }

    /// Interleave `W` vectors coordinate-major, as the block kernels expect.
    fn interleave(vectors: &[Vec<F>]) -> Vec<F> {
        let n = vectors[0].len();
        (0..n * vectors.len())
            .map(|i| vectors[i % vectors.len()][i / vectors.len()])
            .collect()
    }

    /// The scalar gather equals the textbook row-by-row product.
    #[test]
    fn test_gather_matches_reference_product() {
        let rows = random_rows::<F>(50, 4, 1);
        let a = Csr::from_rows(50, &rows);
        let x = random_vector::<F>(50, 2);
        let mut y = vec![F::zero(); 50];
        gather::<F, 1>(&a, 0..50, &x, &mut y);
        assert_eq!(y, dense_product(&rows, &x));
    }

    /// A width-4 block gather equals four independent scalar gathers, lane by lane.
    #[test]
    fn test_block_gather_matches_scalar_per_lane() {
        let rows = random_rows::<F>(40, 5, 3);
        let a = Csr::from_rows(40, &rows);
        let vectors: Vec<Vec<F>> = (0..4).map(|b| random_vector(40, 10 + b)).collect();
        let mut y = vec![F::zero(); 40 * 4];
        gather::<F, 4>(&a, 0..40, &interleave(&vectors), &mut y);
        let expected: Vec<Vec<F>> = vectors.iter().map(|v| dense_product(&rows, v)).collect();
        assert_eq!(y, interleave(&expected));
    }

    /// The column-major scatter over the transpose equals the row gather.
    #[test]
    fn test_scatter_over_transpose_matches_gather() {
        let rows = random_rows::<F>(30, 3, 4);
        let a = Csr::from_rows(30, &rows);
        let vectors: Vec<Vec<F>> = (0..2).map(|b| random_vector(30, 20 + b)).collect();
        let x = interleave(&vectors);
        let (mut by_rows, mut by_columns) = (vec![F::zero(); 60], vec![F::one(); 60]);
        gather::<F, 2>(&a, 0..30, &x, &mut by_rows);
        scatter::<F, 2>(&a.transpose(), &x, &mut by_columns);
        assert_eq!(by_rows, by_columns);
    }

    /// Building from columns yields the same matrix as building from rows.
    #[test]
    fn test_from_columns_is_the_transpose_view() {
        let rows = random_rows::<F>(25, 3, 5);
        let a = Csr::from_rows(25, &rows);
        let columns: Vec<Vec<(usize, F)>> = (0..25)
            .map(|j| {
                (0..25)
                    .flat_map(|i| rows[i].iter().filter(|e| e.0 == j).map(move |e| (i, e.1)))
                    .collect()
            })
            .collect();
        let b = Csr::from_columns(25, &columns);
        assert_eq!((a.row_ptr, a.cols, a.values), (b.row_ptr, b.cols, b.values));
    }

    /// The crate's row format gives the same product as the CSR gather.
    #[test]
    fn test_crate_sparse_matrix_gather_matches_csr() {
        let rows = random_rows::<F>(30, 4, 6);
        let a = Csr::from_rows(30, &rows);
        let m = SparseMatrix::new(30, rows.iter().map(|r| SparseRow::new(r)).collect());
        let x = random_vector::<F>(30, 7);
        let (mut expected, mut actual) = (vec![F::zero(); 30], vec![F::zero(); 30]);
        gather::<F, 1>(&a, 0..30, &x, &mut expected);
        gather_rows(&m, &x, &mut actual);
        assert_eq!(actual, expected);
    }

    /// Bit-packed GF(2) lanes equal 64 scalar GF(2) gathers, one per bit.
    #[test]
    fn test_bit_packed_gf2_matches_scalar_lanes() {
        let rows: Vec<Vec<(usize, Zp2)>> = random_rows::<F>(40, 3, 8)
            .into_iter()
            .map(|r| r.into_iter().map(|(c, _)| (c, Zp2::one())).collect())
            .collect();
        let a = Csr::from_rows(40, &rows);
        let mut rng = StdRng::seed_from_u64(9);
        let x: Vec<u64> = (0..40).map(|_| rng.gen()).collect();
        let mut y = vec![0u64; 40];
        gather_bits(&a, &x, &mut y);
        for bit in 0..64 {
            let lane: Vec<Zp2> = x
                .iter()
                .map(|w| {
                    if w >> bit & 1 == 1 {
                        Zp2::one()
                    } else {
                        Zp2::zero()
                    }
                })
                .collect();
            let mut scalar = vec![Zp2::zero(); 40];
            gather::<Zp2, 1>(&a, 0..40, &lane, &mut scalar);
            for i in 0..40 {
                assert_eq!(
                    y[i] >> bit & 1 == 1,
                    scalar[i] == Zp2::one(),
                    "row {i} bit {bit}"
                );
            }
        }
    }

    /// Every thread count reproduces the single-thread Krylov sequence, odd and even step counts.
    #[test]
    fn test_parallel_krylov_matches_serial() {
        let rows = random_rows::<F>(97, 4, 11);
        let a = Csr::from_rows(97, &rows);
        let x0 = random_vector::<F>(97 * 2, 12);
        for steps in [3, 4] {
            let expected = krylov::<F, 2>(&a, &x0, steps);
            for threads in [1, 2, 3, 8] {
                let (actual, _) = krylov_parallel::<F, 2>(&a, &x0, steps, threads);
                assert_eq!(actual, expected, "{threads} threads, {steps} steps");
            }
        }
    }

    /// Partitions cover every row exactly once, in order, with the requested part count.
    #[test]
    fn test_partition_covers_rows() {
        let a = Csr::from_rows(53, &random_rows::<F>(53, 6, 13));
        for parts in [1, 2, 7, 64] {
            let ranges = a.partition(parts);
            assert_eq!(ranges.len(), parts);
            assert_eq!(ranges.first().unwrap().start, 0);
            assert_eq!(ranges.last().unwrap().end, 53);
            assert!(ranges.windows(2).all(|w| w[0].end == w[1].start));
        }
    }
}
