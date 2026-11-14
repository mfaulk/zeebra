# Linear algebra

Dense and sparse matrices over a finite field, and the echelon backends F4 selects between.

`linalg::Matrix<T>` is a dense matrix over any `T: Ring`, stored row-major, with the `matrix!`
macro for small literals and `zero`, `identity`, `from_diag` and `new` for the rest. Rows are
reachable by `row`, `row_mut`, `rows` and `rows_mut`; columns by `column` and `columns`, which walk
the buffer at a stride of `num_columns` rather than materializing a `transpose()`. Over a
`FiniteField` there are also `rank`, `inverse` and `determinant`.

```rust
use zeebra::{fields::Zp541, linalg::Matrix, matrix, FiniteField};

type F = Zp541;

let a = matrix![
    F::new(1), F::new(2);
    F::new(3), F::new(4)
];
assert_eq!(
    a.column(1).copied().collect::<Vec<F>>(),
    vec![F::new(2), F::new(4)]
);
assert_eq!(a.columns().count(), 2);

// [A | I], the augmented matrix an inversion reduces.
let augmented = a.hconcat(&Matrix::identity(2)).unwrap();
assert_eq!(augmented.shape(), (2, 4));

// The other dimension has to agree, and the error reports both shapes when it does not.
assert!(a.vconcat(&Matrix::identity(3)).is_err());

// The transfer matrix of the Fibonacci recurrence: its nth power holds F(n+1) and F(n).
let fibonacci = matrix![
    F::new(1), F::new(1);
    F::new(1), F::new(0)
];
assert_eq!(fibonacci.pow(10).unwrap()[[0, 1]], F::new(55));
```

`pow` is repeated squaring, so a large exponent costs log-many multiplications; it returns
`Err(NotSquare)` for a non-square matrix, including at exponent zero, where there is no size the
identity could take. `hconcat` and `vconcat` return `Err(IncompatibleShapes)` carrying both shapes.

The product is a **2-by-8 register tile over `i` and `j`**, not the textbook `ijk` and not the `ikj`
with `k` unrolled four deep that preceded it. Row-major storage makes `ijk`'s innermost loop stride
the right operand by `num_columns`, a cache line per multiplication; `ikj`'s is an axpy over
contiguous spans, but it reads and writes a whole row of the product per group of `k`, and that
traffic is what the tile removes — a tile's entries stay put until `k` is exhausted, and two rows of
the left operand share every span of the right operand that gets loaded.
`benches/linear_algebra.rs` measures this two ways: square sizes, and a family of `m x k` times
`k x n` shapes holding the multiplication count at 2^26 so the only thing that varies is the right
operand's footprint.

Over a 31-bit prime, pinned to one core, three interleaved reps under `tools/benchlock.sh`, the tile
is faster than `ikj` at **every** arm — 1.07-1.11x at square n=32 through n=256, 1.06-1.11x while
the right operand is in cache, 1.01-1.03x once it is past L3 — and it closes the one regression
`ikj` carried, where `ijk` had been 8% faster at square n=128. **The shape is tuned, not derived,
and the tuning is most of the result:** 2x16 and 2x32 give back 26% and 16% on the 128 MiB arm, and
a `j` tile with no `i` tile wins nowhere, widths 4 and 8 being slower at every square size and 16
reaching parity in cache only to lose 7-11% out of it. Eight elements is exactly one 64-byte cache
line at 8 bytes apiece, which is the obvious reading of why the wider tiles fall off and not one
these measurements establish.

**The `i` dimension is exhausted at 2.** Hand-written 4x8 and 4x4 tiles were measured against the
shipped kernel and both lose: 4x8 by 0.977-1.012x in cache and **0.497x on the 128 MiB arm**, where
32 live accumulators against 16 general-purpose registers spill and the halved right-operand traffic
does not pay for it, and 4x4 by 0.969-1.015x — parity at best, 2.4% behind at square n=128. 4x4
holds the row count and the operand walk fixed while halving the accumulators, so it is the control
that pins the collapse on register pressure rather than on the extra rows.
[`docs/research/matmul-register-tiling.md`](../research/matmul-register-tiling.md) collects every
tile shape ever swept for this operator in one table, with the load each figure was taken under; it
also records why a figure taken from a generically-indexed template measures the template and not
the shape.

The kernel is **ALU-bound at every footprint** — the §8.2 signature in
[`docs/MILESTONE-SIMD-PARALLELISM.md`](../MILESTONE-SIMD-PARALLELISM.md), reached from the other
side — though less perfectly than `ikj` was: 117-127 ms across a working set spanning three orders
of magnitude, a 6-8% spread where `ikj` held 1-2% and `ijk` spread 42-56% (150 ms → 178 ms →
229 ms). Nothing is traded for that; the tile's in-cache gain is simply larger than its
out-of-cache one. `Matrix::pow` remains the only caller in the crate, which is why this is a
low-priority operator however it is written.

Two gaps are deliberate. There is no mutable column iterator — handing out disjoint `&mut` down a
strided column of a row-major buffer is where the borrow checker stops being free, and nothing in
the crate needs it yet. And `Matrix<T>` does not implement `Ring`, so a matrix cannot yet be a
polynomial coefficient: `Ring` has no fallible operations, and only *square* matrices form one, so
that wants a `SquareMatrix<T>` type carrying the invariant rather than a runtime check inside
`mul`. [#132](https://github.com/mfaulk/zeebra/issues/132) has the discussion.

## Bit-packed GF(2)

`linalg::gf2::BitMatrix` stores a `GF(2)` matrix at one bit per coefficient, rows packed into `u64`
words, and converts to and from `SparseMatrix<Zp2>`. `reduced_row_echelon_packed` is plain
Gauss-Jordan by row `xor`; `reduced_row_echelon_four_russians(matrix, k)` clears `k` pivots per
`xor` from Gray-code tables (`1 <= k <= MAX_TABLE_BITS`). Both return the RREF with the nonzero rows
first in pivot order, equal to the generic kernel's. It is a research prototype (#272) and is
**not** used by F4; [`docs/research/characteristic-two-linear-algebra.md`](../research/characteristic-two-linear-algebra.md)
has the measurements.

```rust
use zeebra::{
    fields::Zp2,
    linalg::{gf2::{reduced_row_echelon_four_russians, BitMatrix}, sparse::{SparseMatrix, SparseRow}},
    One,
};

let rows = vec![
    SparseRow::new(&[(0, Zp2::one()), (1, Zp2::one())]),
    SparseRow::new(&[(1, Zp2::one()), (2, Zp2::one())]),
    SparseRow::new(&[(0, Zp2::one()), (2, Zp2::one())]), // the sum of the first two
];
let mut packed = BitMatrix::from_sparse(&SparseMatrix::new(3, rows));
let statistics = reduced_row_echelon_four_russians(&mut packed, 8);
assert_eq!(statistics.rank, 2);
assert!(packed.get(0, 0) && packed.get(0, 2) && !packed.get(0, 1));
```
