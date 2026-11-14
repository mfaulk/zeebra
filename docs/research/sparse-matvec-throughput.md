# Sparse matvec throughput per field: the CPU baseline

**Measured at:** `55a7af25`, 2026-11-14, one `tools/benchlock.sh` run (`zb-87`, START load 1.51,
END `end=exited` after 1 030 s, load 6.42; per-arm load over the sweep min 2.02, median 3.80, max
7.12). Instrument `examples/sparse_matvec_throughput.rs` with kernels in
`examples/support/sparse_matvec.rs`. Raw rows: `research/sparse-matvec/rows-55a7af25.csv`; full
printed tables: `research/sparse-matvec/sweep-55a7af25.txt`.

Machine: AMD Threadripper PRO 5995WX (64 cores, SMT siblings `n` and `n+64`, 8 CCDs of 8 cores
with 32 MiB L3 each, 512 KiB L2 per core), one NUMA node. Release profile, fat LTO, one codegen
unit, repository `x86-64-v3` (AVX2) flags; `CARGO_TARGET_DIR=/buildcache/cargo-target/zeebra-87`,
`RUSTC_WRAPPER=''`. The whole process ran under `taskset -c 0-63` (physical cores only); worker
threads were not individually pinned. Five repetitions, arm order rotated per repetition, each
arm timing a fixed calibrated step count of at least 40 ms. Peak RSS 44 GiB, because every arm's
matrices and vectors were built before the first timing.

Answers #87 (E2, workstream M28-E, `docs/MILESTONE-MULTICORE-COMPETITIVENESS.md` §7.6) for #731
and #76. It measures the kernel only. A fast block multiply is not a conversion result: Krylov
steps stay sequentially dependent, and this document makes no GPU claim (§7).

## 1. Method

**Every arm runs dependent Krylov steps** `X_{t+1} = A X_t`. A step cannot start until the
previous one has finished, as in a Wiedemann sequence. Multithreaded arms partition rows into
contiguous ranges balanced by entries, and all workers meet at a `Barrier` after every step, so
per-step synchronization is included in the time. Thread start-up is excluded.

**Arithmetic is held fixed.** Every product is one field `*` and one field `+=`, exactly as in
`MultiplicationOperator::apply`. Nothing uses lazy reduction or a field-specific trick, except the
bit-packed GF(2) arm, which is labelled as such.

**Fields.** One type per class the issue names:

| class | type | element bytes |
|---|---|---:|
| GF(2) | `Zp2` (`PrimeFieldElement32<2>`) | 4 |
| GF(2^8) | `Gf256` | 8 |
| 31-bit prime | `BabyBear` | 4 |
| 64-bit prime | `Zp18446744069414584321` (Goldilocks) | 8 |
| 254-bit prime | `Bn254Fr` (Montgomery, 4 limbs) | 32 |

The crate has no bit-packed GF(2) storage; that layout belongs to #272. The research-only
`gf2 bit-packed pattern` arm packs 64 vectors into one `u64` per coordinate, which is the minimal
alternative the issue asks for. All four classes are therefore measured.

**Real operators.** These are the lex-last multiplication operators `T_{x_{N-1}}` of the
digest-pinned family in `examples/wiedemann_conversion.rs`, `x_i^5 - x_{i+1}`,
`x_{N-1}^5 - x_0 - 1`, at `N = 5, 6, 7` (`D = 3125, 15625, 78125`). They are built by
`QuotientAlgebra::new` over each field and re-packed through the new
`MultiplicationOperator::column_entries`. **Matched synthetic** keeps each real operator's per-row
nonzero counts but draws columns uniformly at random, which discards locality. **Synthetic** has
8 nonzeros per row, sized so the arrays are 256 KiB (L2), 16 MiB (one CCD's L3) or 512 MiB (twice
the whole chip's L3).

**Formats.**

| format | what it is |
|---|---|
| `operator.apply` | the crate's column-major operator (unit / sparse / dense column enum), scatter, allocates its output |
| `crate SparseMatrix rows` | the crate's `SparseMatrix` of `SparseRow` (`(usize, F)` entries), row gather written in the harness |
| `csc-u32 scatter` | research column-major packed arrays, 32-bit indices; widths 1 and 8 |
| `csr-u32 gather` | research CSR, 32-bit indices; widths 1, 2, 4, 8, 16; threads 1 to 64 |
| `gf2 bit-packed pattern` | CSR pattern only, `Y[i] = XOR X[c]` over 64-lane words |

Block vectors are interleaved (`X[k*W + b]`), so one matrix entry is loaded once and used `W`
times.

**Paired references, measured in every repetition.**

- `arith`: independent `y[i] += a[i] * x[i]` over 1 024 L1-resident elements on one core. This is
  the field's multiply-add ceiling. For GF(2) and BabyBear the loop auto-vectorizes, so it is a
  SIMD ceiling.
- `bw`: a streaming `u64` read of a 2 GiB buffer, split across the same thread count.

`arith%` is a row's rate divided by `T x arith`. `bw%` divides **logical** compulsory traffic
(matrix arrays, plus each vector read once and written once) by `bw`. Hardware counters are
unavailable here (no `perf`, `perf_event_paranoid=2`), so physical DRAM and line traffic is
**not measured**. A random gather fetches a 64-byte line for 1 to 32 useful bytes, so `bw%`
understates physical traffic. Above 100% it simply means the working set is cache-resident.

Each table entry is a median of five; ratios are medians of per-repetition ratios. Spread
(max/min over repetitions) is at most 1.3x for most single-thread rows. It is up to 1.7x for
DRAM-scale rows and up to 4x for real-operator rows at 32 to 64 threads. Quote those rows as
"collapses", not as precise numbers.

## 2. Baselines

| reference | T=1 | 2 | 4 | 8 | 16 | 32 | 64 |
|---|---:|---:|---:|---:|---:|---:|---:|
| streaming read, GB/s | 26.3 | 46.1 | 63.6 | 101.1 | 112.1 | 126.6 | 136.9 |

| field | arith, M mul-add/s per core |
|---|---:|
| GF(2) (`Zp2`, vectorized) | 14 200.6 |
| GF(2^8) | 162.8 |
| 31-bit BabyBear (vectorized) | 3 076.9 |
| 64-bit Goldilocks | 461.7 |
| 254-bit BN254 Fr | 42.2 |

These are the four different kernels the issue predicted. GF(2^8) multiplication here is slower
than the 64-bit prime multiply. BN254 is 11x slower than Goldilocks.

## 3. The real operators

| D | nnz | nnz/row | max row | unit columns | `stored_bytes` (BN254) | build s (BN254) |
|---:|---:|---:|---:|---:|---:|---:|
| 3 125 | 3 750 | 1.20 | 2 | 2 500 | 125 000 | 0.003 |
| 15 625 | 18 750 | 1.20 | 2 | 12 500 | 625 000 | 0.019 |
| 78 125 | 93 750 | 1.20 | 2 | 62 500 | 3 125 000 | 0.162 |

Each figure is the same for every field except bytes. Build time is a single unpaired snapshot.

**The realistic operator is tiny and cache-resident.** 80% of its columns are unit vectors. At
D = 78 125 the whole operator is 3.1 MB even over BN254, so no realistic operator in this family
is a DRAM-bandwidth problem. The vectors are larger than the operator (2.5 MB per BN254 vector at
this D).

## 4. Single core, width 1: format and field

M mul-add/s, median of five; real `T_x6`, D = 78 125:

| field | `operator.apply` | `SparseMatrix` rows | CSC scatter | CSR gather | arith% (CSR) | matched synthetic CSR |
|---|---:|---:|---:|---:|---:|---:|
| GF(2) | 4 581.9 | 829.7 | 642.8 | 683.2 | 5% | 488.3 |
| GF(2^8) | 287.8 | 151.6 | 137.2 | 140.0 | 86% | 102.2 |
| BabyBear | 778.5 | 454.4 | 527.9 | 472.8 | 15% | 331.8 |
| Goldilocks | 531.7 | 392.5 | 386.8 | 371.5 | 81% | 201.0 |
| BN254 | 115.0 | 50.0 | 53.1 | 51.7 | 122% | 24.7 |

`operator.apply` counts each unit column as one entry, but it does an addition there and no
multiplication. That shortcut is why it beats every packed format by 1.4x to 6.7x on these
operators: **the crate's native format is already the best scalar format here**, and any packed
or block kernel has to beat it, not CSR at width 1. Among the general formats, the choice
(`(usize, F)` rows, u32 CSR, u32 CSC) moves throughput by at most 1.3x on cache-resident
operators. Structure is worth 1.4x to 2.1x: real versus matched synthetic at the same density.

Synthetic, CSR gather, width 1 (M mul-add/s; `bw%` logical):

| field | L2 | L3 | DRAM 512 MiB | DRAM bw% |
|---|---:|---:|---:|---:|
| GF(2) | 1 019.6 | 577.1 | 136.5 | 5% |
| GF(2^8) | 163.7 | 129.1 | 26.3 | 1% |
| BabyBear | 663.6 | 298.8 | 89.3 | 3% |
| Goldilocks | 443.2 | 229.9 | 53.5 | 3% |
| BN254 | 45.8 | 30.8 | 8.6 | 2% |

## 5. Block width: the reuse lever

Per-vector-entry throughput relative to width 1, same matrix, format and repetition:

| field | real D=78 125, w=2 / 4 / 8 / 16 | DRAM synthetic, w=2 / 4 / 8 / 16 |
|---|---|---|
| GF(2) | 1.78 / 3.97 / 8.04 / 12.04 | 1.61 / 3.58 / 5.99 / 8.85 |
| GF(2^8) | 1.10 / 1.17 / 1.19 / 1.19 | 1.10 / 1.17 / 1.97 / 2.84 |
| BabyBear | 1.13 / 3.92 / 5.86 / 6.85 | 0.86 / 2.62 / 3.76 / 4.15 |
| Goldilocks | 1.42 / 1.21 / 1.42 / 1.55 | 1.10 / 1.15 / 1.13 / 1.92 |
| BN254 | 0.94 / 0.92 / 0.88 / 0.90 | 1.50 / 2.28 / 3.01 / 3.26 |

The bit-packed GF(2) arm (64 vectors) reaches 73 140 M vector-entries/s on the real D = 78 125
operator. That is 16x `operator.apply` and 107x the `Zp2` CSR at width 1. On DRAM synthetic it
reaches 12 194 M/s, 89x the `Zp2` width-1 CSR.

What the width buys depends on the field:

- **GF(2) and BabyBear:** the block becomes SIMD lanes. Width 8 to 16 brings the kernel near the
  vectorized `arith` ceiling (BabyBear width 16 on the real operator: 107% `arith`).
- **GF(2^8), Goldilocks, BN254 on cache-resident operators:** the kernel is already at 80% to
  120% of the scalar multiply ceiling at width 1, so the block buys at most 1.6x, and nothing
  for BN254.
- **On DRAM-scale matrices,** blocks of 8 to 16 help even the multiply-bound fields 2x to 3x,
  because one miss on a matrix entry is amortized over the block. Only there is the classic reuse
  argument visible.

Per vector, the best block CSR against the native `operator.apply` on the real D = 78 125
operator:

| field | best | ratio |
|---|---|---:|
| GF(2) | bit-packed | 16x |
| BabyBear | w=16 | 4.2x |
| Goldilocks | w=16 | 1.07x |
| GF(2^8) | w=16 | 0.59x |
| BN254 | w=1 | 0.45x |

## 6. Threads

CSR gather, `T` threads, speedup over `T = 1` at the same width (median of paired ratios):

| field, matrix, w | 2 | 4 | 8 | 16 | 32 | 64 |
|---|---:|---:|---:|---:|---:|---:|
| GF(2), real 78 125, w=1 | 1.65 | 2.77 | 4.02 | 4.67 | 3.42 | 1.21 |
| BabyBear, real, w=8 | 1.48 | 2.23 | 2.96 | 2.78 | 2.44 | 1.28 |
| Goldilocks, real, w=1 | 1.74 | 2.90 | 4.30 | 6.66 | 5.03 | 1.67 |
| BN254, real, w=1 | 1.62 | 2.83 | 4.53 | 4.96 | 11.50 | 4.26 |
| BN254, real, w=8 | 1.70 | 2.80 | 5.48 | 6.51 | 8.79 | 8.67 |
| GF(2), DRAM, w=1 | 1.88 | 3.71 | 7.49 | 12.82 | 24.38 | 28.48 |
| BabyBear, DRAM, w=1 | 1.86 | 3.96 | 8.60 | 14.57 | 28.18 | 35.73 |
| Goldilocks, DRAM, w=1 | 1.84 | 3.79 | 7.69 | 13.39 | 25.32 | 31.02 |
| BN254, DRAM, w=1 | 1.80 | 3.39 | 7.10 | 15.07 | 28.42 | 35.89 |
| BN254, DRAM, w=8 | 1.94 | 3.61 | 6.93 | 13.32 | 26.06 | 33.06 |

On the real operator, a step is only 93 750 entries: 0.8 ms for BN254 and well under 0.2 ms for
the small fields on one core. Per-step barrier synchronization therefore caps scaling at 8 to
32 workers, and **64 workers are slower than 16** for every field except BN254 at width 8.
At DRAM scale, scaling continues to 64 threads at 28x to 36x, yet logical traffic peaks at 35 GB/s
(GF(2), w=1, T=64), 26% of the 137 GB/s streaming read. The random gather is latency- and
line-bound, not stream-bound.

## 7. Bound classification, and what a GPU would have to beat

| field | real operator (cache-resident) | DRAM-scale synthetic |
|---|---|---|
| GF(2) | `Zp2` CSR is index/latency-bound (5% of SIMD arith); bit-packed moves 22 to 26 GB/s logical (84% to 96% of one core's DRAM read) while resident in L2/L3, so it is gather-bound, not arithmetic-bound | latency-bound (5% bw, w=1); bit-packed 5% bw |
| GF(2^8) | arithmetic-bound: 86% of a slow `Gf256` multiply | latency-bound at w=1 (16% arith, 1% bw); blocks move it toward arithmetic |
| BabyBear | index/latency-bound at w=1; arithmetic-bound (SIMD) at w=16 | latency-bound |
| Goldilocks | arithmetic-bound (81%; `operator.apply` 115% via unit columns) | latency-bound (12% arith, 3% bw) |
| BN254 | arithmetic-bound (122% of the arith loop) | latency-bound at w=1; arithmetic-bound with blocks |

No row is streaming-bandwidth-bound. That includes the 64-thread DRAM rows, whose logical traffic
stays at or below 26% of measured read bandwidth. At D ≤ 78 125, the multithreaded real-operator
kernel is **synchronization-bound** above 16 to 32 workers.

**GPU.** No GPU was measured and no feasibility claim is made. Per #87's go/no-go and the
2026-11-13 rescope, this section only states the bar any GPU result must meet:

- **The bar, per field.** A GPU must beat this table's best CPU per-step time for the same
  operator, arithmetic and output. On the real D = 78 125 operator that is `operator.apply` or
  the best threaded CSR row: e.g. BN254 600.7 M mul-add/s (T=32, w=1) and Goldilocks
  2 394 M/s (T=16, w=1). For GF(2) it is the bit-packed 73 140 M/s on one core, not the `Zp2`
  rows.
- **Device memory and transfer.** The realistic operator is 3.1 MB over BN254, so the "operator
  does not fit in device memory" no-go cannot trigger at these sizes. With PCIe 4.0 x16 at its
  nominal ~32 GB/s per direction (a specification figure, not measured here), one-time transfer
  is about 0.1 ms. Per step, only the projections need to cross, provided the sequence stays on
  the device.
- **What decides it.** On CPU the obstacles are a dependent step of under 1 ms and arithmetic
  for the wide fields, not bandwidth. Whether a GPU wins is therefore a question of launch and
  synchronization latency per Krylov step against the per-field rates above. Bandwidth alone
  settles nothing, as the rescope says.

**Does communication dominate at realistic sizes?** Memory traffic does not: the realistic
operator is cache-resident, and every single-thread real-operator kernel is arithmetic- or
index-bound. Inter-core communication, meaning the per-step barrier, does dominate beyond 16 to
32 workers on the realistic operators.

## 8. Conclusion for #731 and #76

1. **Matvec throughput is a reason for blocks only over GF(2) and SIMD-friendly small primes.**
   Bit-packed GF(2) gains 16x per vector over the native scalar apply on the real operator, and
   BabyBear at width 8 to 16 gains about 4x. For Goldilocks, GF(2^8) and BN254, a block CSR does
   not beat `operator.apply` (0.45x to 1.07x per vector). There, a block-Wiedemann case has to
   rest on what blocks change elsewhere: sequence length about `2D/m`, independent work for
   threads, and polynomial-matrix cost (#731's scope). It cannot rest on per-vector matvec
   throughput.
2. **Keep the unit-column shortcut.** 80% of the real operator's columns are unit vectors, and
   `operator.apply` exploits that. A block kernel for #731 should take the native layout and a
   permutation for unit columns, not plain CSR. Plain CSR gives up 1.4x to 6.7x before any block
   gain.
3. **Predeclared widths 1/2/4/8 are enough to see the effect.** Width 16 adds at most 1.5x more
   on real operators, and it loses at L3 scale (GF(2), BabyBear) once the block outgrows cache.
4. **Threads per step.** Use at most 16 to 32 workers on operators of this size. 64 is
   counterproductive. Block width and worker count are separate axes, and the best
   real-operator rows came from threads at width 1 for the wide fields.
5. **Scale of the kernel's share.** Scalar Wiedemann needs about `2D` dependent steps. At
   D = 78 125, the native apply's per-step time implies roughly 128 s of matvec for BN254 and
   roughly 28 s for Goldilocks. That is derived from §4 and not measured end to end. Operator
   construction is 0.16 s. So at this D, the matvec sequence, not construction, is the cost a
   block method would attack. #731 must still compare complete certified conversion.

## 9. Not measured

- Physical DRAM or memory-controller traffic, cache-miss counts and allocations (no counters
  available). Only logical traffic and process peak RSS were recorded.
- Complete conversion, Berlekamp–Massey or matrix BM, projection dot products and certification
  share; see `certified-wiedemann.md`. Only the matvec kernel was measured.
- Denser real operators (e.g. katsura's reduced columns at 79% fill) and D beyond 78 125. The
  DRAM-scale behaviour is synthetic only.
- Per-thread core pinning, SMT siblings (CPUs 64 to 127), and 128 threads.
- ELL or blocked formats, and lazy-reduction or field-specialized block kernels (deliberately
  excluded: arithmetic held fixed).
- Any GPU.

## 10. Reproduce

```text
cargo build --release --example sparse_matvec_throughput
tools/benchlock.sh <owner> timeout --signal=INT --kill-after=60s 3600 \
  taskset -c 0-63 target/release/examples/sparse_matvec_throughput --csv rows.csv
cargo run --release --example sparse_matvec_throughput -- --quick   # smoke test, seconds
cargo test --example sparse_matvec_throughput                       # kernels against references
```

Flags: `--reps`, `--min-ms`, `--threads 1,2,...`, `--widths 1,2,...` (1, 2, 4, 8 and 16 are
instantiated), `--max-variables 5..7`, `--l2-kib`, `--l3-mib`, `--dram-mib`, `--per-row`,
`--bandwidth-mib`, `--csv PATH`.
