//! Blocked dense reduced echelon form over a word-size prime field (#1193). A research prototype:
//! nothing in F4 or the signature engine calls it.
//!
//! The echelon is recursive on rows, in the style of FFPACK's rank-profile eliminations: the top
//! half is echelonized, the bottom half is reduced against it by one matrix product, the
//! remainder is echelonized on the columns the top half left free, and the top half is cleared on
//! the remainder's pivots by a second product. Every product runs through one kernel, classical
//! below a crossover and Strassen–Winograd above it.
//!
//! Residues are `f64` integers in `[0, p)`. The classical kernel accumulates up to
//! [`Modulus::depth`] products before it reduces, which keeps every intermediate value an integer
//! at most 2^52 and therefore exact in a double; Winograd's additions are reduced at every level,
//! so its products see only reduced operands. The proof is in
//! `docs/research/blocked-dense-elimination.md` §3.
//!
//! The result is the reduced row echelon form, which is unique, so it is compared entry for entry
//! with the shipped routes rather than by row space.

use crate::{
    linalg::{
        lane::Lane,
        sparse::{SparseMatrix, SparseRow},
    },
    FiniteField,
};

/// Primes must lie below this, so that `(p - 1) + (p - 1)^2 <= 2^52`.
pub const PRIME_LIMIT: u32 = 1 << 26;

/// 2^52: the largest value an accumulator may reach. One bit below a double's 2^53 integer range,
/// so that the quotient times `p` in [`Modulus::reduce`] is exact too.
const CEILING: u64 = 1 << 52;

/// Micro-kernel rows.
const MR: usize = 4;
/// Micro-kernel columns, and the width of a packed strip of the right operand.
const NR: usize = 8;
/// Depth of one packed block of the right operand.
const KC: usize = 256;
/// Width of one packed block of the right operand.
const NC: usize = 1024;

/// A prime below [`PRIME_LIMIT`], with what reduction in doubles needs.
#[derive(Clone, Copy, Debug)]
pub struct Modulus {
    prime: u32,
    p: f64,
    inverse: f64,
    depth: usize,
}

impl Modulus {
    /// The modulus `prime`, or `None` outside `[2, PRIME_LIMIT)`. Primality is the caller's.
    pub fn new(prime: u32) -> Option<Self> {
        if !(2..PRIME_LIMIT).contains(&prime) {
            return None;
        }
        let p = u64::from(prime);
        let square = (p - 1) * (p - 1);
        let depth = ((CEILING - (p - 1)) / square).min(usize::MAX as u64) as usize;
        Some(Self {
            prime,
            p: p as f64,
            inverse: 1.0 / p as f64,
            depth,
        })
    }

    /// The prime.
    pub fn prime(&self) -> u32 {
        self.prime
    }

    /// The most products of two residues an accumulator holding a residue can add before it
    /// must reduce: the largest `λ` with `(p - 1) + λ (p - 1)^2 <= 2^52`.
    pub fn depth(&self) -> usize {
        self.depth
    }

    /// `s mod p` for an integer `0 <= s <= 2^52`.
    ///
    /// `s * fl(1/p)` is within `s / p * 2^-52 <= 1/2` of `s / p`, so the floor is off by at most
    /// one. `q p <= s + p < 2^53` is exact, and so is `s - q p`, which lies in `(-p, 2p)`.
    #[inline(always)]
    fn reduce(self, s: f64) -> f64 {
        let q = (s * self.inverse).floor();
        let r = s - q * self.p;
        let r = if r < 0.0 { r + self.p } else { r };
        if r >= self.p {
            r - self.p
        } else {
            r
        }
    }

    #[inline(always)]
    fn add(self, a: f64, b: f64) -> f64 {
        let s = a + b;
        if s >= self.p {
            s - self.p
        } else {
            s
        }
    }

    #[inline(always)]
    fn sub(self, a: f64, b: f64) -> f64 {
        let s = a - b;
        if s < 0.0 {
            s + self.p
        } else {
            s
        }
    }

    /// The same prime with a smaller depth, so tests reach the mid-accumulation reductions.
    #[cfg(test)]
    fn with_depth(prime: u32, depth: usize) -> Self {
        let modulus = Self::new(prime).unwrap();
        assert!(depth >= 1 && depth <= modulus.depth);
        Self { depth, ..modulus }
    }

    fn inverse_of(self, a: f64) -> f64 {
        let p = u64::from(self.prime);
        let mut base = a as u64;
        let mut exponent = p - 2;
        let mut result = 1u64;
        while exponent > 0 {
            if exponent & 1 == 1 {
                result = result * base % p;
            }
            base = base * base % p;
            exponent >>= 1;
        }
        result as f64
    }
}

/// Which kernel a product uses, and where the echelon's recursion stops.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct BlockedOptions {
    /// Row count at or below which the echelon is the row-at-a-time leaf.
    pub leaf_rows: usize,
    /// A product splits by Winograd while all three of its dimensions are at least this. `usize::MAX`
    /// keeps every product classical.
    pub winograd_from: usize,
}

impl Default for BlockedOptions {
    fn default() -> Self {
        Self {
            leaf_rows: 64,
            winograd_from: usize::MAX,
        }
    }
}

/// Deterministic operation counts: a function of the input and the options alone.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct BlockedCounts {
    /// Scalar multiply-adds, in the classical kernel and the leaf.
    pub products: u64,
    /// Reductions of an accumulator to a residue.
    pub reductions: u64,
    /// Modular additions and subtractions of residues, Winograd's and the updates'.
    pub additions: u64,
    /// Products that split by Winograd, counting every level.
    pub winograd_splits: u64,
    /// Products that ran in the classical kernel.
    pub classical_products: u64,
    /// Pivots normalized by an inverse.
    pub inversions: u64,
}

/// A dense row-major matrix of residues.
#[derive(Clone, Debug, PartialEq)]
pub struct DenseMatrix {
    rows: usize,
    columns: usize,
    cells: Vec<f64>,
}

impl DenseMatrix {
    /// The zero matrix.
    pub fn zero(rows: usize, columns: usize) -> Self {
        Self {
            rows,
            columns,
            cells: vec![0.0; rows * columns],
        }
    }

    /// From row-major residues, each below `modulus`.
    ///
    /// # Panics
    /// If `residues` is not `rows * columns` long or holds a value not below the prime.
    pub fn from_residues(modulus: Modulus, rows: usize, columns: usize, residues: &[u32]) -> Self {
        assert_eq!(
            residues.len(),
            rows * columns,
            "a {rows} x {columns} matrix"
        );
        assert!(
            residues.iter().all(|&r| r < modulus.prime),
            "a residue not below {}",
            modulus.prime
        );
        Self {
            rows,
            columns,
            cells: residues.iter().map(|&r| f64::from(r)).collect(),
        }
    }

    pub fn rows(&self) -> usize {
        self.rows
    }

    pub fn columns(&self) -> usize {
        self.columns
    }

    /// The residue at `(row, column)`.
    pub fn residue(&self, row: usize, column: usize) -> u32 {
        self.cells[row * self.columns + column] as u32
    }

    /// Row-major residues.
    pub fn residues(&self) -> Vec<u32> {
        self.cells.iter().map(|&c| c as u32).collect()
    }

    /// Nonzero cells.
    pub fn nonzeros(&self) -> usize {
        self.cells.iter().filter(|&&c| c != 0.0).count()
    }

    /// Drops the zero rows, keeping the others in order.
    pub fn retain_nonzero_rows(&mut self) {
        let columns = self.columns;
        let mut kept = 0;
        for i in 0..self.rows {
            if self.row(i).iter().any(|&c| c != 0.0) {
                self.cells
                    .copy_within(i * columns..(i + 1) * columns, kept * columns);
                kept += 1;
            }
        }
        self.rows = kept;
        self.cells.truncate(kept * columns);
        self.cells.shrink_to_fit();
    }

    fn view(&self) -> View<'_> {
        View {
            rows: self.rows,
            columns: self.columns,
            stride: self.columns,
            cells: &self.cells,
        }
    }

    fn row(&self, row: usize) -> &[f64] {
        &self.cells[row * self.columns..(row + 1) * self.columns]
    }

    fn row_mut(&mut self, row: usize) -> &mut [f64] {
        &mut self.cells[row * self.columns..(row + 1) * self.columns]
    }

    /// The columns `columns` of every row, in that order.
    fn gather(&self, columns: &[usize]) -> Self {
        let mut out = Self::zero(self.rows, columns.len());
        for i in 0..self.rows {
            let (from, to) = (self.row(i), out.row_mut(i));
            for (t, &c) in to.iter_mut().zip(columns) {
                *t = from[c];
            }
        }
        out
    }

    /// `self - other`, entrywise, into `self`.
    fn subtract(&mut self, modulus: Modulus, other: &Self, counts: &mut BlockedCounts) {
        debug_assert_eq!((self.rows, self.columns), (other.rows, other.columns));
        for (a, &b) in self.cells.iter_mut().zip(&other.cells) {
            *a = modulus.sub(*a, b);
        }
        counts.additions += self.cells.len() as u64;
    }
}

/// A read-only rectangular window with a row stride.
#[derive(Clone, Copy)]
struct View<'a> {
    rows: usize,
    columns: usize,
    stride: usize,
    cells: &'a [f64],
}

impl<'a> View<'a> {
    fn block(self, row: usize, column: usize, rows: usize, columns: usize) -> View<'a> {
        debug_assert!(row + rows <= self.rows && column + columns <= self.columns);
        if rows == 0 || columns == 0 {
            return View {
                rows,
                columns,
                stride: self.stride,
                cells: &[],
            };
        }
        let start = row * self.stride + column;
        let end = (row + rows - 1) * self.stride + column + columns;
        View {
            rows,
            columns,
            stride: self.stride,
            cells: &self.cells[start..end],
        }
    }

    #[inline(always)]
    fn row(&self, row: usize) -> &'a [f64] {
        let start = row * self.stride;
        &self.cells[start..start + self.columns]
    }
}

/// `a * b` reduced, through the kernel the options select.
///
/// # Panics
/// If the inner dimensions differ.
pub fn multiply(
    modulus: Modulus,
    a: &DenseMatrix,
    b: &DenseMatrix,
    options: BlockedOptions,
    counts: &mut BlockedCounts,
) -> DenseMatrix {
    assert_eq!(a.columns, b.rows, "inner dimensions differ");
    product(modulus, a.view(), b.view(), options, counts)
}

fn product(
    modulus: Modulus,
    a: View<'_>,
    b: View<'_>,
    options: BlockedOptions,
    counts: &mut BlockedCounts,
) -> DenseMatrix {
    let smallest = a.rows.min(a.columns).min(b.columns);
    if smallest >= options.winograd_from.max(2) {
        winograd(modulus, a, b, options, counts)
    } else {
        classical(modulus, a, b, counts)
    }
}

/// `a + b` or `a - b` of two views, reduced.
fn combine(
    modulus: Modulus,
    a: View<'_>,
    b: View<'_>,
    subtract: bool,
    counts: &mut BlockedCounts,
) -> DenseMatrix {
    debug_assert_eq!((a.rows, a.columns), (b.rows, b.columns));
    let mut out = DenseMatrix::zero(a.rows, a.columns);
    for i in 0..a.rows {
        let (x, y, to) = (a.row(i), b.row(i), out.row_mut(i));
        for ((t, &u), &v) in to.iter_mut().zip(x).zip(y) {
            *t = if subtract {
                modulus.sub(u, v)
            } else {
                modulus.add(u, v)
            };
        }
    }
    counts.additions += (a.rows * a.columns) as u64;
    out
}

/// `target += other` (or `-=`) on a block of `target` at `(row, column)`.
fn accumulate_into(
    modulus: Modulus,
    target: &mut DenseMatrix,
    row: usize,
    column: usize,
    other: &DenseMatrix,
    subtract: bool,
    counts: &mut BlockedCounts,
) {
    for i in 0..other.rows {
        let to = &mut target.row_mut(row + i)[column..column + other.columns];
        for (t, &v) in to.iter_mut().zip(other.row(i)) {
            *t = if subtract {
                modulus.sub(*t, v)
            } else {
                modulus.add(*t, v)
            };
        }
    }
    counts.additions += (other.rows * other.columns) as u64;
}

/// Strassen–Winograd: seven half-size products and fifteen additions, in the order of Boyer,
/// Dumas, Pernet and Zhou (ISSAC 2009) §2, with odd dimensions peeled into classical products.
fn winograd(
    modulus: Modulus,
    a: View<'_>,
    b: View<'_>,
    options: BlockedOptions,
    counts: &mut BlockedCounts,
) -> DenseMatrix {
    counts.winograd_splits += 1;
    let (m, k, n) = (a.rows, a.columns, b.columns);
    let (m2, k2, n2) = (m / 2, k / 2, n / 2);
    let a11 = a.block(0, 0, m2, k2);
    let a12 = a.block(0, k2, m2, k2);
    let a21 = a.block(m2, 0, m2, k2);
    let a22 = a.block(m2, k2, m2, k2);
    let b11 = b.block(0, 0, k2, n2);
    let b12 = b.block(0, n2, k2, n2);
    let b21 = b.block(k2, 0, k2, n2);
    let b22 = b.block(k2, n2, k2, n2);

    let mut c = DenseMatrix::zero(m, n);
    let s1 = combine(modulus, a21, a22, false, counts);
    let s2 = combine(modulus, s1.view(), a11, true, counts);
    let t1 = combine(modulus, b12, b11, true, counts);
    let t2 = combine(modulus, b22, t1.view(), true, counts);

    // U2 = P1 + P6 accumulates in `x`; C11 = P1 + P2.
    let mut x = product(modulus, a11, b11, options, counts);
    let p2 = product(modulus, a12, b21, options, counts);
    let mut c11 = x.clone();
    c11.add_assign(modulus, &p2, counts);
    drop(p2);
    let p6 = product(modulus, s2.view(), t2.view(), options, counts);
    x.add_assign(modulus, &p6, counts);
    drop(p6);
    // U3 = U2 + P7 in `y`.
    let s3 = combine(modulus, a11, a21, true, counts);
    let t3 = combine(modulus, b22, b12, true, counts);
    let mut y = product(modulus, s3.view(), t3.view(), options, counts);
    drop((s3, t3));
    y.add_assign(modulus, &x, counts);
    // U4 = U2 + P5 in `x`; C22 = U7 = U3 + P5.
    let p5 = product(modulus, s1.view(), t1.view(), options, counts);
    x.add_assign(modulus, &p5, counts);
    let mut c22 = y.clone();
    c22.add_assign(modulus, &p5, counts);
    drop(p5);
    // C12 = U5 = U4 + P3.
    let s4 = combine(modulus, a12, s2.view(), true, counts);
    drop(s2);
    let p3 = product(modulus, s4.view(), b22, options, counts);
    drop(s4);
    x.add_assign(modulus, &p3, counts);
    drop(p3);
    // C21 = U6 = U3 - P4.
    let t4 = combine(modulus, t2.view(), b21, true, counts);
    drop((t1, t2, s1));
    let p4 = product(modulus, a22, t4.view(), options, counts);
    drop(t4);
    y.subtract(modulus, &p4, counts);
    drop(p4);

    store(&mut c, 0, 0, &c11);
    store(&mut c, 0, n2, &x);
    store(&mut c, m2, 0, &y);
    store(&mut c, m2, n2, &c22);

    // Peeling: the odd inner index, then the odd last column and row.
    if k % 2 == 1 {
        let tail = classical(
            modulus,
            a.block(0, k - 1, 2 * m2, 1),
            b.block(k - 1, 0, 1, 2 * n2),
            counts,
        );
        accumulate_into(modulus, &mut c, 0, 0, &tail, false, counts);
    }
    if n % 2 == 1 {
        let column = classical(
            modulus,
            a.block(0, 0, 2 * m2, k),
            b.block(0, n - 1, k, 1),
            counts,
        );
        store(&mut c, 0, n - 1, &column);
    }
    if m % 2 == 1 {
        let row = classical(modulus, a.block(m - 1, 0, 1, k), b, counts);
        store(&mut c, m - 1, 0, &row);
    }
    c
}

impl DenseMatrix {
    fn add_assign(&mut self, modulus: Modulus, other: &Self, counts: &mut BlockedCounts) {
        debug_assert_eq!((self.rows, self.columns), (other.rows, other.columns));
        for (a, &b) in self.cells.iter_mut().zip(&other.cells) {
            *a = modulus.add(*a, b);
        }
        counts.additions += self.cells.len() as u64;
    }
}

fn store(target: &mut DenseMatrix, row: usize, column: usize, block: &DenseMatrix) {
    for i in 0..block.rows {
        target.row_mut(row + i)[column..column + block.columns].copy_from_slice(block.row(i));
    }
}

#[inline(always)]
fn multiply_add(a: f64, b: f64, c: f64) -> f64 {
    // Exact either way: every operand and result is an integer of at most 2^52.
    if cfg!(any(target_arch = "aarch64", target_feature = "fma")) {
        a.mul_add(b, c)
    } else {
        a * b + c
    }
}

/// The classical product with delayed reduction: accumulators reduce once per [`Modulus::depth`]
/// products and once at the end.
fn classical(
    modulus: Modulus,
    a: View<'_>,
    b: View<'_>,
    counts: &mut BlockedCounts,
) -> DenseMatrix {
    let (m, k, n) = (a.rows, a.columns, b.columns);
    debug_assert_eq!(k, b.rows);
    counts.classical_products += 1;
    counts.products += (m * k * n) as u64;
    let mut acc = DenseMatrix::zero(m, n);
    if m == 0 || n == 0 || k == 0 {
        return acc;
    }
    let depth = KC.min(modulus.depth.max(1));
    let mut held = 0usize;
    let mut packed = vec![0.0f64; depth * NC.min(n.div_ceil(NR) * NR)];
    for pc in (0..k).step_by(depth) {
        let kc = depth.min(k - pc);
        if held + kc > modulus.depth {
            for cell in &mut acc.cells {
                *cell = modulus.reduce(*cell);
            }
            counts.reductions += (m * n) as u64;
            held = 0;
        }
        for jc in (0..n).step_by(NC) {
            let nc = NC.min(n - jc);
            let strips = nc.div_ceil(NR);
            // Pack b[pc..pc+kc, jc..jc+nc] as strips of NR columns, each kc x NR, zero-padded.
            for s in 0..strips {
                let width = NR.min(nc - s * NR);
                let strip = &mut packed[s * kc * NR..(s + 1) * kc * NR];
                for kk in 0..kc {
                    let from = &b.row(pc + kk)[jc + s * NR..jc + s * NR + width];
                    let to = &mut strip[kk * NR..kk * NR + NR];
                    to[..width].copy_from_slice(from);
                    to[width..].fill(0.0);
                }
            }
            let mut i = 0;
            while i < m {
                let rows = MR.min(m - i);
                for s in 0..strips {
                    let width = NR.min(nc - s * NR);
                    let strip = &packed[s * kc * NR..(s + 1) * kc * NR];
                    let column = jc + s * NR;
                    if rows == MR {
                        micro4(&mut acc, a, i, pc, kc, strip, column, width);
                    } else {
                        for r in i..i + rows {
                            micro1(&mut acc, a, r, pc, kc, strip, column, width);
                        }
                    }
                }
                i += rows;
            }
        }
        held += kc;
    }
    for cell in &mut acc.cells {
        *cell = modulus.reduce(*cell);
    }
    counts.reductions += (m * n) as u64;
    acc
}

#[allow(clippy::too_many_arguments)]
#[inline(always)]
fn micro4(
    acc: &mut DenseMatrix,
    a: View<'_>,
    i: usize,
    pc: usize,
    kc: usize,
    strip: &[f64],
    column: usize,
    width: usize,
) {
    let n = acc.columns;
    let mut c0 = [0.0f64; NR];
    let mut c1 = [0.0f64; NR];
    let mut c2 = [0.0f64; NR];
    let mut c3 = [0.0f64; NR];
    c0[..width].copy_from_slice(&acc.cells[i * n + column..i * n + column + width]);
    c1[..width].copy_from_slice(&acc.cells[(i + 1) * n + column..(i + 1) * n + column + width]);
    c2[..width].copy_from_slice(&acc.cells[(i + 2) * n + column..(i + 2) * n + column + width]);
    c3[..width].copy_from_slice(&acc.cells[(i + 3) * n + column..(i + 3) * n + column + width]);
    let a0 = &a.row(i)[pc..pc + kc];
    let a1 = &a.row(i + 1)[pc..pc + kc];
    let a2 = &a.row(i + 2)[pc..pc + kc];
    let a3 = &a.row(i + 3)[pc..pc + kc];
    for (kk, bk) in strip.chunks_exact(NR).enumerate().take(kc) {
        let bk: &[f64; NR] = bk.try_into().unwrap();
        let (x0, x1, x2, x3) = (a0[kk], a1[kk], a2[kk], a3[kk]);
        for t in 0..NR {
            c0[t] = multiply_add(x0, bk[t], c0[t]);
            c1[t] = multiply_add(x1, bk[t], c1[t]);
            c2[t] = multiply_add(x2, bk[t], c2[t]);
            c3[t] = multiply_add(x3, bk[t], c3[t]);
        }
    }
    acc.cells[i * n + column..i * n + column + width].copy_from_slice(&c0[..width]);
    acc.cells[(i + 1) * n + column..(i + 1) * n + column + width].copy_from_slice(&c1[..width]);
    acc.cells[(i + 2) * n + column..(i + 2) * n + column + width].copy_from_slice(&c2[..width]);
    acc.cells[(i + 3) * n + column..(i + 3) * n + column + width].copy_from_slice(&c3[..width]);
}

#[allow(clippy::too_many_arguments)]
#[inline(always)]
fn micro1(
    acc: &mut DenseMatrix,
    a: View<'_>,
    i: usize,
    pc: usize,
    kc: usize,
    strip: &[f64],
    column: usize,
    width: usize,
) {
    let n = acc.columns;
    let mut c0 = [0.0f64; NR];
    c0[..width].copy_from_slice(&acc.cells[i * n + column..i * n + column + width]);
    let a0 = &a.row(i)[pc..pc + kc];
    for (kk, bk) in strip.chunks_exact(NR).enumerate().take(kc) {
        let x0 = a0[kk];
        for t in 0..NR {
            c0[t] = multiply_add(x0, bk[t], c0[t]);
        }
    }
    acc.cells[i * n + column..i * n + column + width].copy_from_slice(&c0[..width]);
}

/// The reduced row echelon form of `matrix` and its pivot columns, ascending.
///
/// The result has one row per pivot. Zero rows are dropped, so it is the unique reduced basis of
/// the row space and does not depend on the row order of the input.
pub fn reduced_echelon(
    modulus: Modulus,
    matrix: DenseMatrix,
    options: BlockedOptions,
    counts: &mut BlockedCounts,
) -> (DenseMatrix, Vec<usize>) {
    if matrix.rows <= options.leaf_rows.max(1) || matrix.columns == 0 {
        return leaf(modulus, matrix, counts);
    }
    let columns = matrix.columns;
    let top = matrix.rows / 2;
    let mut upper = matrix;
    let lower = DenseMatrix {
        rows: upper.rows - top,
        columns,
        cells: upper.cells.split_off(top * columns),
    };
    upper.rows = top;
    upper.cells.shrink_to_fit();

    let (upper, pivots) = reduced_echelon(modulus, upper, options, counts);
    if pivots.is_empty() {
        return reduced_echelon(modulus, lower, options, counts);
    }
    let free = complement(&pivots, columns);
    if free.is_empty() {
        return (upper, pivots);
    }
    // Lower rows lose the upper pivot columns: G = A2[:, free] - A2[:, P1] E1[:, free].
    let mut free_upper = upper.gather(&free);
    drop(upper);
    let mut residual = {
        let multipliers = lower.gather(&pivots);
        let mut residual = lower.gather(&free);
        drop(lower);
        let update = product(
            modulus,
            multipliers.view(),
            free_upper.view(),
            options,
            counts,
        );
        residual.subtract(modulus, &update, counts);
        residual
    };
    let (lower, lower_free_pivots) = reduced_echelon(
        modulus,
        std::mem::replace(&mut residual, DenseMatrix::zero(0, 0)),
        options,
        counts,
    );
    // Upper rows lose the lower pivot columns: F1 -= F1[:, P2] E2.
    if !lower_free_pivots.is_empty() {
        let multipliers = free_upper.gather(&lower_free_pivots);
        let update = product(modulus, multipliers.view(), lower.view(), options, counts);
        free_upper.subtract(modulus, &update, counts);
    }

    // Merge by pivot column, back to the full width.
    let lower_pivots: Vec<usize> = lower_free_pivots.iter().map(|&q| free[q]).collect();
    let rank = pivots.len() + lower_pivots.len();
    let mut out = DenseMatrix::zero(rank, columns);
    let mut all = Vec::with_capacity(rank);
    let (mut u, mut l) = (0, 0);
    for r in 0..rank {
        let to = out.row_mut(r);
        if l == lower_pivots.len() || (u < pivots.len() && pivots[u] < lower_pivots[l]) {
            to[pivots[u]] = 1.0;
            for (&c, &v) in free.iter().zip(free_upper.row(u)) {
                to[c] = v;
            }
            all.push(pivots[u]);
            u += 1;
        } else {
            for (&c, &v) in free.iter().zip(lower.row(l)) {
                to[c] = v;
            }
            all.push(lower_pivots[l]);
            l += 1;
        }
    }
    (out, all)
}

/// The columns of `0..columns` not in the ascending `pivots`.
fn complement(pivots: &[usize], columns: usize) -> Vec<usize> {
    let mut free = Vec::with_capacity(columns - pivots.len());
    let mut next = pivots.iter().peekable();
    for c in 0..columns {
        if next.peek() == Some(&&c) {
            next.next();
        } else {
            free.push(c);
        }
    }
    free
}

/// Row-at-a-time Gauss–Jordan, with the working row's reduction delayed.
fn leaf(
    modulus: Modulus,
    matrix: DenseMatrix,
    counts: &mut BlockedCounts,
) -> (DenseMatrix, Vec<usize>) {
    let columns = matrix.columns;
    let mut basis: Vec<(usize, Vec<f64>)> = Vec::new();
    let mut work = vec![0.0f64; columns];
    for i in 0..matrix.rows {
        work.copy_from_slice(matrix.row(i));
        let mut held = 0usize;
        // Against every pivot so far, ascending: the basis is reduced, so each clears only its own
        // column.
        for (lead, pivot) in &basis {
            if held == modulus.depth {
                for w in work[*lead..].iter_mut() {
                    *w = modulus.reduce(*w);
                }
                counts.reductions += (columns - lead) as u64;
                held = 0;
            }
            let x = modulus.reduce(work[*lead]);
            work[*lead] = 0.0;
            if x != 0.0 {
                let negated = modulus.p - x;
                for (w, &v) in work[lead + 1..].iter_mut().zip(&pivot[lead + 1..]) {
                    *w = multiply_add(negated, v, *w);
                }
                counts.products += (columns - lead - 1) as u64;
                held += 1;
            }
        }
        for w in work.iter_mut() {
            *w = modulus.reduce(*w);
        }
        counts.reductions += columns as u64;
        let Some(lead) = work.iter().position(|&w| w != 0.0) else {
            continue;
        };
        let scale = work[lead];
        if scale != 1.0 {
            counts.inversions += 1;
            let inverse = modulus.inverse_of(scale);
            for w in work[lead..].iter_mut() {
                *w = modulus.reduce(*w * inverse);
            }
            counts.products += (columns - lead) as u64;
            counts.reductions += (columns - lead) as u64;
        }
        for (_, row) in basis.iter_mut() {
            let x = row[lead];
            if x != 0.0 {
                let negated = modulus.p - x;
                row[lead] = 0.0;
                for (r, &v) in row[lead + 1..].iter_mut().zip(&work[lead + 1..]) {
                    *r = modulus.reduce(multiply_add(negated, v, *r));
                }
                counts.products += (columns - lead - 1) as u64;
                counts.reductions += (columns - lead - 1) as u64;
            }
        }
        let at = basis.partition_point(|(l, _)| *l < lead);
        basis.insert(at, (lead, work.clone()));
    }
    let mut out = DenseMatrix::zero(basis.len(), columns);
    let mut pivots = Vec::with_capacity(basis.len());
    for (r, (lead, row)) in basis.into_iter().enumerate() {
        out.row_mut(r).copy_from_slice(&row);
        pivots.push(lead);
    }
    (out, pivots)
}

/// The reduced row echelon form of a sparse matrix over a lane field, as sparse rows sorted by
/// lead. `columns` restricts the dense form to those columns, ascending; every other column must
/// be zero in every row.
///
/// # Panics
/// If the prime is not below [`PRIME_LIMIT`], or a row has an entry outside `columns`.
pub fn reduced_echelon_of_sparse<F: FiniteField>(
    lane: &Lane<F>,
    matrix: &SparseMatrix<F>,
    columns: &[usize],
    options: BlockedOptions,
    counts: &mut BlockedCounts,
) -> SparseMatrix<F> {
    let modulus = Modulus::new(lane.modulus()).expect("a prime below 2^26");
    let mut position = vec![usize::MAX; matrix.num_columns()];
    for (i, &c) in columns.iter().enumerate() {
        position[c] = i;
    }
    let mut dense = DenseMatrix::zero(matrix.num_rows(), columns.len());
    for (i, row) in matrix.rows().iter().enumerate() {
        let to = dense.row_mut(i);
        for (c, v) in row.entries() {
            let at = position[*c];
            assert!(at != usize::MAX, "row {i} has an entry in column {c}");
            to[at] = f64::from(lane.canonical(v));
        }
    }
    let (echelon, _) = reduced_echelon(modulus, dense, options, counts);
    to_sparse(&echelon, columns, matrix.num_columns())
}

/// Dense rows back to sparse ones of `width` columns, column `j` of `dense` being `columns[j]`.
pub fn to_sparse<F: FiniteField>(
    dense: &DenseMatrix,
    columns: &[usize],
    width: usize,
) -> SparseMatrix<F> {
    let rows = (0..dense.rows)
        .map(|r| {
            let entries = dense
                .row(r)
                .iter()
                .zip(columns)
                .filter(|(v, _)| **v != 0.0)
                .map(|(&v, &c)| (c, F::new(v as u64)))
                .collect();
            SparseRow::from_sorted(entries).expect("ascending and nonzero")
        })
        .collect();
    SparseMatrix::new(width, rows)
}

/// One reducer row, its unit lead omitted.
enum Reducer {
    Sparse { columns: Vec<u32>, values: Vec<f64> },
    Dense { start: usize, values: Vec<f64> },
}

/// The sparse top of a reducers-first batch: every row from `split` on swept against the reducer
/// rows `[..split]`, as the dense `D' = D - C A^-1 B` on the columns no reducer leads.
///
/// The working row is a row of `f64` accumulators, reduced only when a reducer's lead is reached
/// or after [`Modulus::depth`] applications, as in the classical kernel. A reducer is stored dense
/// over its span when at least a quarter of the span is nonzero, as the lane kernel does.
///
/// Returns `D'` (one row per lower row, zero rows kept) and its columns, ascending.
///
/// # Panics
/// If the prime is not below [`PRIME_LIMIT`], or the reducer rows are not monic with distinct
/// leads.
pub fn sweep_to_dense<F: FiniteField>(
    lane: &Lane<F>,
    matrix: &SparseMatrix<F>,
    split: usize,
    counts: &mut BlockedCounts,
) -> (DenseMatrix, Vec<usize>) {
    let modulus = Modulus::new(lane.modulus()).expect("a prime below 2^26");
    sweep(modulus, lane, matrix, split, counts)
}

fn sweep<F: FiniteField>(
    modulus: Modulus,
    lane: &Lane<F>,
    matrix: &SparseMatrix<F>,
    split: usize,
    counts: &mut BlockedCounts,
) -> (DenseMatrix, Vec<usize>) {
    let width = matrix.num_columns();
    let mut reducer_at = vec![usize::MAX; width];
    let mut reducers = Vec::with_capacity(split);
    for (index, row) in matrix.rows()[..split].iter().enumerate() {
        let lead = row.leading_column().expect("a reducer row is nonzero");
        assert_eq!(
            row.leading_coefficient(),
            Some(F::ONE),
            "reducer {index} is not monic"
        );
        assert_eq!(
            reducer_at[lead],
            usize::MAX,
            "two reducers lead with {lead}"
        );
        reducer_at[lead] = reducers.len();
        let body = &row.entries()[1..];
        let reducer = match body.last() {
            Some(&(last, _)) if body.len() * 4 >= last - lead => {
                let mut values = vec![0.0; last - lead];
                for (c, v) in body {
                    values[c - lead - 1] = f64::from(lane.canonical(v));
                }
                Reducer::Dense {
                    start: lead + 1,
                    values,
                }
            }
            _ => Reducer::Sparse {
                columns: body.iter().map(|(c, _)| *c as u32).collect(),
                values: body
                    .iter()
                    .map(|(_, v)| f64::from(lane.canonical(v)))
                    .collect(),
            },
        };
        reducers.push(reducer);
    }
    let free: Vec<usize> = (0..width)
        .filter(|&c| reducer_at[c] == usize::MAX)
        .collect();
    let lower = &matrix.rows()[split..];
    let mut out = DenseMatrix::zero(lower.len(), free.len());
    let mut work = vec![0.0f64; width];
    for (i, row) in lower.iter().enumerate() {
        let (Some(lead), Some(last)) = (row.leading_column(), row.trailing_column()) else {
            continue;
        };
        for (c, v) in row.entries() {
            work[*c] = f64::from(lane.canonical(v));
        }
        let mut tail = last + 1;
        let mut held = 0usize;
        for column in lead..width {
            if column >= tail {
                break;
            }
            let slot = reducer_at[column];
            if slot == usize::MAX || work[column] == 0.0 {
                continue;
            }
            let x = modulus.reduce(work[column]);
            work[column] = 0.0;
            if x == 0.0 {
                continue;
            }
            if held == modulus.depth {
                for w in work[column..tail].iter_mut() {
                    *w = modulus.reduce(*w);
                }
                counts.reductions += (tail - column) as u64;
                held = 0;
            }
            let negated = modulus.p - x;
            match &reducers[slot] {
                Reducer::Dense { start, values } => {
                    for (w, &v) in work[*start..*start + values.len()].iter_mut().zip(values) {
                        *w = multiply_add(negated, v, *w);
                    }
                    counts.products += values.len() as u64;
                    tail = tail.max(start + values.len());
                }
                Reducer::Sparse { columns, values } => {
                    for (&c, &v) in columns.iter().zip(values) {
                        let w = &mut work[c as usize];
                        *w = multiply_add(negated, v, *w);
                    }
                    counts.products += values.len() as u64;
                    if let Some(&c) = columns.last() {
                        tail = tail.max(c as usize + 1);
                    }
                }
            }
            held += 1;
        }
        let to = out.row_mut(i);
        for (t, &c) in to.iter_mut().zip(&free) {
            if c >= lead && c < tail {
                *t = modulus.reduce(work[c]);
            }
        }
        counts.reductions += free.len() as u64;
        work[lead..tail].fill(0.0);
    }
    (out, free)
}

/// The reduced row echelon form of `D'`, the dense residual of a reducers-first batch: the sweep of
/// [`sweep_to_dense`], then [`reduced_echelon`]. Its rows, in the batch's own columns, are exactly
/// the rows of the whole batch's reduced echelon form that lead outside the reducer block.
pub fn residual_reduced_echelon<F: FiniteField>(
    lane: &Lane<F>,
    matrix: &SparseMatrix<F>,
    split: usize,
    options: BlockedOptions,
    counts: &mut BlockedCounts,
) -> SparseMatrix<F> {
    let modulus = Modulus::new(lane.modulus()).expect("a prime below 2^26");
    let (residual, free) = sweep_to_dense(lane, matrix, split, counts);
    let (echelon, _) = reduced_echelon(modulus, residual, options, counts);
    to_sparse(&echelon, &free, matrix.num_columns())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        fields::{Zp31, Zp32003, Zp65537},
        linalg::{
            echelon::sweep_rows_against_pivots, lane::LaneKernel, reduce_rows_against_pivots_with,
            row_echelon_with, sparse::back_substitute_pivots_within, Backend,
        },
    };
    use rand::{rngs::StdRng, Rng, SeedableRng};

    const PRIMES: [u32; 6] = [2, 3, 31, 32003, 65537, 67_108_859];

    fn random(rng: &mut StdRng, p: u32, rows: usize, columns: usize) -> Vec<u32> {
        (0..rows * columns).map(|_| rng.gen_range(0..p)).collect()
    }

    fn naive_product(p: u32, a: &[u32], b: &[u32], m: usize, k: usize, n: usize) -> Vec<u32> {
        let p = u128::from(p);
        let mut c = vec![0u32; m * n];
        for i in 0..m {
            for j in 0..n {
                let s: u128 = (0..k)
                    .map(|t| u128::from(a[i * k + t]) * u128::from(b[t * n + j]))
                    .sum();
                c[i * n + j] = (s % p) as u32;
            }
        }
        c
    }

    /// Textbook Gauss–Jordan in u64, rows sorted by lead.
    fn naive_reduced(p: u32, cells: &[u32], rows: usize, columns: usize) -> (Vec<u32>, Vec<usize>) {
        let p = u64::from(p);
        let mut m: Vec<Vec<u64>> = (0..rows)
            .map(|i| {
                cells[i * columns..(i + 1) * columns]
                    .iter()
                    .map(|&v| u64::from(v))
                    .collect()
            })
            .collect();
        let inverse = |a: u64| {
            let (mut base, mut e, mut r) = (a, p - 2, 1u64);
            while e > 0 {
                if e & 1 == 1 {
                    r = r * base % p;
                }
                base = base * base % p;
                e >>= 1;
            }
            r
        };
        let mut pivots = Vec::new();
        let mut rank = 0;
        for c in 0..columns {
            let Some(found) = (rank..rows).find(|&r| m[r][c] != 0) else {
                continue;
            };
            m.swap(rank, found);
            let s = inverse(m[rank][c]);
            for v in m[rank].iter_mut() {
                *v = *v * s % p;
            }
            for r in 0..rows {
                if r != rank && m[r][c] != 0 {
                    let f = m[r][c];
                    for j in 0..columns {
                        m[r][j] = (m[r][j] + (p - f) * m[rank][j]) % p;
                    }
                }
            }
            pivots.push(c);
            rank += 1;
        }
        let out = m[..rank].iter().flatten().map(|&v| v as u32).collect();
        (out, pivots)
    }

    #[test]
    fn test_depth_is_the_largest_safe_product_count() {
        for p in PRIMES {
            let modulus = Modulus::new(p).unwrap();
            let (q, square) = (u128::from(p - 1), u128::from(p - 1).pow(2));
            let depth = modulus.depth() as u128;
            assert!(q + depth * square <= 1 << 52, "p = {p}");
            assert!(q + (depth + 1) * square > 1 << 52, "p = {p}");
        }
        assert_eq!(Modulus::new(32003).unwrap().depth(), 4_397_496);
        assert_eq!(Modulus::new(67_108_859).unwrap().depth(), 1);
        assert!(Modulus::new(1 << 26).is_none());
        assert!(Modulus::new(1).is_none());
    }

    #[test]
    fn test_reduce_is_exact_across_its_whole_range() {
        let mut rng = StdRng::seed_from_u64(7);
        for p in PRIMES {
            let modulus = Modulus::new(p).unwrap();
            let edges = [0, 1, u64::from(p) - 1, u64::from(p), CEILING - 1, CEILING];
            let samples = edges
                .into_iter()
                .chain((0..10_000).map(|_| rng.gen_range(0..=CEILING)));
            for s in samples {
                assert_eq!(
                    modulus.reduce(s as f64) as u64,
                    s % u64::from(p),
                    "{s} mod {p}"
                );
            }
        }
    }

    #[test]
    fn test_products_match_the_textbook_sum() {
        let mut rng = StdRng::seed_from_u64(1193);
        let shapes = [
            (1, 1, 1),
            (3, 5, 7),
            (9, 8, 17),
            (16, 16, 16),
            (33, 70, 41),
            (5, 300, 9),
        ];
        for p in PRIMES {
            let modulus = Modulus::new(p).unwrap();
            for &(m, k, n) in &shapes {
                let (a, b) = (random(&mut rng, p, m, k), random(&mut rng, p, k, n));
                let expected = naive_product(p, &a, &b, m, k, n);
                let a = DenseMatrix::from_residues(modulus, m, k, &a);
                let b = DenseMatrix::from_residues(modulus, k, n, &b);
                for winograd_from in [usize::MAX, 2, 3, 8] {
                    let options = BlockedOptions {
                        winograd_from,
                        ..Default::default()
                    };
                    let mut counts = BlockedCounts::default();
                    let c = multiply(modulus, &a, &b, options, &mut counts);
                    assert_eq!(
                        c.residues(),
                        expected,
                        "p {p} {m}x{k}x{n} from {winograd_from}"
                    );
                    if winograd_from == usize::MAX {
                        assert_eq!(counts.products, (m * k * n) as u64);
                        assert_eq!(counts.winograd_splits, 0);
                    }
                }
            }
        }
    }

    #[test]
    fn test_the_largest_residues_stay_exact_at_the_full_depth() {
        // Every entry p - 1: each accumulator reaches (p - 1)^2 per product, the bound's worst case.
        for p in [32003, 65537, 67_108_859] {
            let modulus = Modulus::new(p).unwrap();
            let k = 600;
            let a = DenseMatrix::from_residues(modulus, 5, k, &vec![p - 1; 5 * k]);
            let b = DenseMatrix::from_residues(modulus, k, 11, &vec![p - 1; k * 11]);
            let expected = ((u128::from(p - 1).pow(2) * k as u128) % u128::from(p)) as u32;
            for winograd_from in [usize::MAX, 4] {
                let options = BlockedOptions {
                    winograd_from,
                    ..Default::default()
                };
                let c = multiply(modulus, &a, &b, options, &mut BlockedCounts::default());
                assert!(c.residues().iter().all(|&v| v == expected), "p {p}");
            }
        }
    }

    fn low_rank(rng: &mut StdRng, p: u32, rows: usize, columns: usize, rank: usize) -> Vec<u32> {
        let left = random(rng, p, rows, rank);
        let right = random(rng, p, rank, columns);
        naive_product(p, &left, &right, rows, rank, columns)
    }

    /// Random, low-rank, and structured rank-deficient inputs.
    fn cases(rng: &mut StdRng, p: u32) -> Vec<(usize, usize, Vec<u32>)> {
        let mut cases = vec![
            (0, 5, vec![]),
            (4, 0, vec![]),
            (7, 9, vec![0; 63]),
            (40, 30, random(rng, p, 40, 30)),
            (30, 70, random(rng, p, 30, 70)),
            (90, 40, low_rank(rng, p, 90, 40, 7)),
            (65, 65, low_rank(rng, p, 65, 65, 64)),
            (130, 90, low_rank(rng, p, 130, 90, 1)),
            (200, 150, random(rng, p, 200, 150)),
        ];
        // The same row repeated, and zero columns between.
        let row: Vec<u32> = (0..50)
            .map(|c| if c % 3 == 0 { 0 } else { rng.gen_range(0..p) })
            .collect();
        cases.push((80, 50, row.iter().cycle().take(80 * 50).copied().collect()));
        // A staircase whose later rows depend on earlier ones, pivots far right.
        let mut stairs = low_rank(rng, p, 100, 120, 20);
        for (i, cell) in stairs.iter_mut().enumerate() {
            if i % 120 < 60 {
                *cell = 0;
            }
        }
        cases.push((100, 120, stairs));
        // All p - 1.
        cases.push((70, 33, vec![p - 1; 70 * 33]));
        cases
    }

    #[test]
    fn test_reduced_echelon_matches_textbook_gauss_jordan() {
        let mut rng = StdRng::seed_from_u64(26);
        for p in PRIMES {
            let modulus = Modulus::new(p).unwrap();
            for (rows, columns, cells) in cases(&mut rng, p) {
                let expected = naive_reduced(p, &cells, rows, columns);
                for (leaf_rows, winograd_from) in [
                    (1, usize::MAX),
                    (4, 2),
                    (16, 5),
                    (64, usize::MAX),
                    (1000, 2),
                ] {
                    let options = BlockedOptions {
                        leaf_rows,
                        winograd_from,
                    };
                    let matrix = DenseMatrix::from_residues(modulus, rows, columns, &cells);
                    let mut counts = BlockedCounts::default();
                    let (echelon, pivots) = reduced_echelon(modulus, matrix, options, &mut counts);
                    assert_eq!(
                        (echelon.residues(), pivots),
                        expected,
                        "p {p} {rows}x{columns} leaf {leaf_rows} from {winograd_from}"
                    );
                }
            }
        }
    }

    #[test]
    fn test_counts_are_deterministic() {
        let mut rng = StdRng::seed_from_u64(3);
        let modulus = Modulus::new(31).unwrap();
        let cells = low_rank(&mut rng, 31, 300, 200, 120);
        let options = BlockedOptions {
            leaf_rows: 16,
            winograd_from: 8,
        };
        let run = || {
            let mut counts = BlockedCounts::default();
            let matrix = DenseMatrix::from_residues(modulus, 300, 200, &cells);
            reduced_echelon(modulus, matrix, options, &mut counts);
            counts
        };
        let first = run();
        assert_eq!(first, run());
        assert!(first.winograd_splits > 0 && first.products > 0);
    }

    /// The shipped route's reduced echelon form: the dense backend's echelon, the sparse
    /// back-substitution, zero rows dropped and the rest sorted by lead.
    fn shipped<F: FiniteField>(
        matrix: &SparseMatrix<F>,
        backend: Backend,
        split: usize,
    ) -> SparseMatrix<F> {
        let mut m = matrix.clone();
        let mut statistics = if split == 0 {
            row_echelon_with(backend, &mut m, usize::MAX).unwrap()
        } else {
            reduce_rows_against_pivots_with(backend, &mut m, split, usize::MAX).unwrap()
        };
        back_substitute_pivots_within(&mut m, usize::MAX, &mut statistics).unwrap();
        let mut rows: Vec<SparseRow<F>> =
            m.rows().iter().filter(|r| !r.is_zero()).cloned().collect();
        rows.sort_by_key(|r| r.leading_column());
        SparseMatrix::new(m.num_columns(), rows)
    }

    fn sparse_of<F: FiniteField>(rows: usize, columns: usize, cells: &[u32]) -> SparseMatrix<F> {
        let rows = (0..rows)
            .map(|i| {
                let entries: Vec<(usize, F)> = (0..columns)
                    .filter(|&c| cells[i * columns + c] != 0)
                    .map(|c| (c, F::new(u64::from(cells[i * columns + c]))))
                    .collect();
                SparseRow::from_sorted(entries).unwrap()
            })
            .collect();
        SparseMatrix::new(columns, rows)
    }

    fn agrees_with_the_shipped_routes<F: FiniteField>(p: u32) {
        let lane = F::small_prime_lane().or_else(F::prime31_lane).unwrap();
        let mut rng = StdRng::seed_from_u64(u64::from(p));
        for (rows, columns, cells) in cases(&mut rng, p) {
            let matrix = sparse_of::<F>(rows, columns, &cells);
            let everything: Vec<usize> = (0..columns).collect();
            let options = BlockedOptions {
                leaf_rows: 8,
                winograd_from: 4,
            };
            let ours = reduced_echelon_of_sparse(
                &lane,
                &matrix,
                &everything,
                options,
                &mut BlockedCounts::default(),
            );
            for backend in [Backend::Dense, Backend::Sparse, Backend::Adaptive] {
                assert_eq!(
                    ours,
                    shipped(&matrix, backend, 0),
                    "p {p} {rows}x{columns} {backend:?}"
                );
            }
        }
    }

    #[test]
    fn test_reduced_echelon_matches_the_shipped_backends_over_gf31() {
        agrees_with_the_shipped_routes::<Zp31>(31);
    }

    #[test]
    fn test_reduced_echelon_matches_the_shipped_backends_over_gf32003() {
        agrees_with_the_shipped_routes::<Zp32003>(32003);
    }

    #[test]
    fn test_reduced_echelon_matches_the_shipped_backends_over_gf65537() {
        agrees_with_the_shipped_routes::<Zp65537>(65537);
    }

    #[test]
    fn test_restricted_columns_keep_their_indices() {
        let lane = Zp31::small_prime_lane().unwrap();
        let rows = vec![
            SparseRow::new(&[(2, Zp31::new(3)), (7, Zp31::new(5))]),
            SparseRow::new(&[(2, Zp31::new(6)), (5, Zp31::new(1)), (7, Zp31::new(10))]),
        ];
        let matrix = SparseMatrix::new(9, rows);
        let ours = reduced_echelon_of_sparse(
            &lane,
            &matrix,
            &[2, 5, 7],
            BlockedOptions::default(),
            &mut BlockedCounts::default(),
        );
        assert_eq!(ours, shipped(&matrix, Backend::Sparse, 0));
    }

    #[test]
    fn test_a_shallow_depth_reduces_mid_accumulation_and_stays_exact() {
        let mut rng = StdRng::seed_from_u64(5);
        for depth in [1, 2, 3, 7] {
            let modulus = Modulus::with_depth(31, depth);
            let (a, b) = (random(&mut rng, 31, 13, 300), random(&mut rng, 31, 300, 11));
            let expected = naive_product(31, &a, &b, 13, 300, 11);
            let a = DenseMatrix::from_residues(modulus, 13, 300, &a);
            let b = DenseMatrix::from_residues(modulus, 300, 11, &b);
            let mut counts = BlockedCounts::default();
            let c = multiply(modulus, &a, &b, BlockedOptions::default(), &mut counts);
            assert_eq!(c.residues(), expected, "depth {depth}");
            assert!(
                counts.reductions > (13 * 11) as u64,
                "depth {depth} reduced only at the end"
            );
            for (rows, columns, cells) in cases(&mut rng, 31) {
                let matrix = DenseMatrix::from_residues(modulus, rows, columns, &cells);
                let options = BlockedOptions {
                    leaf_rows: 8,
                    winograd_from: 4,
                };
                let (echelon, pivots) =
                    reduced_echelon(modulus, matrix, options, &mut BlockedCounts::default());
                assert_eq!(
                    (echelon.residues(), pivots),
                    naive_reduced(31, &cells, rows, columns),
                    "depth {depth} {rows}x{columns}"
                );
            }
        }
    }

    /// A reducers-first batch: monic reducers with distinct leads, then lower rows, some dependent
    /// on the reducers, some repeated, some zero.
    fn batch<F: FiniteField>(
        rng: &mut StdRng,
        p: u32,
        columns: usize,
        reducers: usize,
        lower: usize,
    ) -> (SparseMatrix<F>, usize) {
        let mut leads: Vec<usize> = (0..columns).collect();
        for i in (1..leads.len()).rev() {
            leads.swap(i, rng.gen_range(0..=i));
        }
        leads.truncate(reducers);
        leads.sort_unstable();
        let mut rows = Vec::new();
        for (r, &lead) in leads.iter().enumerate() {
            // Alternate sparse and dense reducers so both storage forms are swept.
            let keep = if r % 2 == 0 { 2 } else { 9 };
            let mut entries = vec![(lead, F::ONE)];
            for c in lead + 1..columns {
                if rng.gen_range(0..10) < keep {
                    entries.push((c, F::new(u64::from(rng.gen_range(1..p)))));
                }
            }
            rows.push(SparseRow::from_sorted(entries).unwrap());
        }
        let mut lower_rows: Vec<SparseRow<F>> = Vec::new();
        for i in 0..lower {
            let row = match i % 5 {
                3 if i > 0 => lower_rows[i - 1].clone(),
                4 => {
                    // A combination of two reducers: sweeps to zero.
                    let mut combined = rows[i % reducers].clone();
                    let mut scratch = Vec::new();
                    combined.subtract_scaled(&rows[(i + 1) % reducers], &F::new(3), &mut scratch);
                    combined
                }
                _ => {
                    let density = rng.gen_range(1..10);
                    let mut entries: Vec<(usize, F)> = Vec::new();
                    for c in 0..columns {
                        if rng.gen_range(0..10) < density {
                            entries.push((c, F::new(u64::from(rng.gen_range(1..p)))));
                        }
                    }
                    SparseRow::from_sorted(entries).unwrap()
                }
            };
            lower_rows.push(row);
        }
        lower_rows.push(SparseRow::zero());
        rows.extend(lower_rows);
        (SparseMatrix::new(columns, rows), reducers)
    }

    fn sweeps_and_residuals_agree<F: FiniteField>(p: u32) {
        let lane = F::small_prime_lane().or_else(F::prime31_lane).unwrap();
        let mut rng = StdRng::seed_from_u64(u64::from(p) + 1);
        let depths = [Modulus::new(p).unwrap().depth(), 1, 2];
        for (columns, reducers, lower) in [(40, 15, 30), (120, 70, 90), (90, 5, 140), (60, 59, 20)]
        {
            let (matrix, split) = batch::<F>(&mut rng, p, columns, reducers, lower);
            let mut reference = matrix.clone();
            sweep_rows_against_pivots(&mut reference, split, usize::MAX).unwrap();
            for depth in depths {
                let modulus = Modulus::with_depth(p, depth);
                let (residual, free) = sweep(
                    modulus,
                    &lane,
                    &matrix,
                    split,
                    &mut BlockedCounts::default(),
                );
                let swept: SparseMatrix<F> = to_sparse(&residual, &free, columns);
                assert_eq!(
                    swept.rows(),
                    &reference.rows()[split..],
                    "p {p} {columns} columns depth {depth}"
                );
            }
            let ours = residual_reduced_echelon(
                &lane,
                &matrix,
                split,
                BlockedOptions {
                    leaf_rows: 8,
                    winograd_from: 4,
                },
                &mut BlockedCounts::default(),
            );
            let mut reducer_lead = vec![false; columns];
            for row in &matrix.rows()[..split] {
                reducer_lead[row.leading_column().unwrap()] = true;
            }
            for backend in [Backend::Sparse, Backend::Adaptive] {
                let whole = shipped(&matrix, backend, split);
                let outside: Vec<SparseRow<F>> = whole
                    .rows()
                    .iter()
                    .filter(|r| !reducer_lead[r.leading_column().unwrap()])
                    .cloned()
                    .collect();
                assert_eq!(
                    ours.rows(),
                    &outside[..],
                    "p {p} {columns} columns {backend:?}"
                );
            }
            // The lane kernel's forward pass, then the shipped back-substitution.
            let mut forward = matrix.clone();
            let mut statistics = LaneKernel::default()
                .reduce_rows_against_pivots(&lane, &mut forward, split, usize::MAX)
                .unwrap();
            back_substitute_pivots_within(&mut forward, usize::MAX, &mut statistics).unwrap();
            let outside: Vec<SparseRow<F>> = sorted_rows(&forward)
                .into_iter()
                .filter(|r| !reducer_lead[r.leading_column().unwrap()])
                .collect();
            assert_eq!(ours.rows(), &outside[..], "p {p} {columns} columns lane");
        }
    }

    fn sorted_rows<F: FiniteField>(matrix: &SparseMatrix<F>) -> Vec<SparseRow<F>> {
        let mut rows: Vec<SparseRow<F>> = matrix
            .rows()
            .iter()
            .filter(|r| !r.is_zero())
            .cloned()
            .collect();
        rows.sort_by_key(|r| r.leading_column());
        rows
    }

    #[test]
    fn test_sweep_and_residual_echelon_match_the_shipped_routes_over_gf31() {
        sweeps_and_residuals_agree::<Zp31>(31);
    }

    #[test]
    fn test_sweep_and_residual_echelon_match_the_shipped_routes_over_gf32003() {
        sweeps_and_residuals_agree::<Zp32003>(32003);
    }

    #[test]
    fn test_sweep_and_residual_echelon_match_the_shipped_routes_over_gf65537() {
        sweeps_and_residuals_agree::<Zp65537>(65537);
    }
}
