# Characteristic-two linear algebra: bit-packed GF(2) elimination and Four Russians

**Measured at:** `30f24f6f` (release, `RUSTC_WRAPPER=""`, `CARGO_INCREMENTAL=0`), one core
(`taskset -c 37`), serialized through `tools/benchlock.sh` (tag `272`; 1-minute load 4.2–4.4 at
START and END of both runs on this 128-core machine). Each cell is the minimum of 5 repetitions,
arms interleaved with a rotating order.

Reference for #272 (H16), scoped to the **kernel** only — representation and solving route stay
with #218 and #196. The instrument is `examples/gf2_packed_elimination.rs`; the kernel is
`src/linalg/gf2.rs` (`BitMatrix`, `reduced_row_echelon_packed`,
`reduced_row_echelon_four_russians`), written independently of M4RI (GPL; read for the published
figures only, not the source).

## Decision

- **Adopt the bit-packed representation for GF(2) — as a follow-up, not in this PR.** On the
  matrices F4 itself builds for dense Boolean systems, packed RREF is **27x–132x** faster than the
  generic sparse RREF of the same matrices, and faster than F4's own (structured, partial)
  elimination stage by enough to project a **1.4x–3.4x** end-to-end gain. It is *not* uniformly a
  win: on sparse systems (cyclic, sparse MQ) the projected end-to-end effect is **0.77x–0.96x**, a
  regression. Wiring it into F4 therefore needs a dispatch rule, and that is filed as a follow-up
  rather than done here (#777, §6).
- **Four Russians is in range.** Its crossover against plain packed Gauss-Jordan is between
  **n = 64 and n = 128** on dense random square matrices, and every non-trivial F4 matrix measured
  here is above it; on the dense-MQ matrices Four Russians (`k = 8`) is **2.2x–3.1x** faster than
  plain packed Gauss-Jordan. Plain bit-packing alone is not the whole answer.
- **Defer GF(2^e) / M4RIE slicing.** Not measured: it stays blocked on the defining-polynomial
  convention (#272's comments; `Gf256` is `0x11B`, `Gf256Mq` is `0x11D`).

## 1. The current kernel, per nonzero

A generic sparse entry is `(usize, Zp2)`, **16 bytes for one bit** of information — 128x the floor
(`examples/boolean_density.rs`, `docs/research/boolean-solving.md` §9). A packed row stores every
column at one bit, so per *nonzero* it costs `1 / (8 d)` bytes at density `d`; it is smaller than the
sparse entry whenever `d > 1/128 ≈ 0.8%`, which every F4 matrix measured here exceeds.

Measured cost of the generic `reduced_row_echelon` over `Zp2` on F4's own matrices: **76–1236 ns
per row operation**, rising with the matrix (the merge length grows with fill-in). Peak live bytes of
the generic kernel against the packed widest matrix, same instance: 6168 against 551 KiB for
`mq-13` (11x), 8379 against 2718 KiB for `overdetermined-mq-16` (3.1x).

## 2. Kernel on characteristic-two F4 matrices

Every matrix F4 eliminates (`F4Options::default()`, grevlex, field equations adjoined), collected
through `BatchObserver::matrix`, then reduced by each arm. Times are summed over the instance's
matrices; packed arms include `SparseMatrix -> BitMatrix -> SparseMatrix` conversion, with the
kernel-only time in parentheses. **Every packed RREF is asserted equal, row for row, to the generic
kernel's RREF** (nonzero rows in pivot order), so bases computed through either kernel would be
identical; rank is asserted equal too.

Families: dense random MQ (`n` quadratics in `n` variables, each quadratic monomial present with
probability 0.3, planted root — the `boolean_density` construction), sparse MQ (probability 0.05),
overdetermined MQ (`2n` equations), and `cyclic-n` over `GF(2)`. `katsura-n` over `GF(2)` was
dropped: its largest matrix is 18x13 and every arm is under 10 µs, a measurement of nothing.
mfaulk/cryptanalysis#9's ANF instances live in a private repository and were not available here.

| instance | basis | matrices | widest | entries | generic row ops | generic ns/op | generic RREF ms | plain ms (kernel) | 4R k=4 ms (kernel) | 4R k=8 ms (kernel) | best packed vs generic |
| --- | ---: | ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| mq-8 | 8 | 5 | 197x142 | 4058 | 8366 | 113 | 0.94 | 0.20 (0.17) | 0.15 (0.12) | 0.17 (0.15) | 6.4x |
| mq-10 | 10 | 5 | 1094x706 | 28172 | 104961 | 321 | 33.69 | 2.76 (2.65) | 1.37 (1.27) | 1.25 (1.15) | 27.0x |
| mq-12 | 13 | 6 | 1817x1353 | 84753 | 383982 | 620 | 237.91 | 9.03 (8.75) | 4.10 (3.86) | 3.50 (3.27) | 67.9x |
| mq-13 | 16 | 6 | 2350x1906 | 134825 | 727138 | 811 | 589.96 | 15.94 (15.54) | 6.81 (6.47) | 5.48 (5.14) | 107.6x |
| sparse-mq-12 | 12 | 6 | 443x311 | 3619 | 7569 | 76 | 0.58 | 0.40 (0.37) | 0.28 (0.25) | 0.31 (0.29) | 2.1x |
| overdetermined-mq-14 | 14 | 5 | 1036x564 | 50747 | 172293 | 354 | 61.01 | 3.39 (3.19) | 1.61 (1.42) | 1.47 (1.29) | 41.4x |
| overdetermined-mq-16 | 16 | 5 | 6958x3146 | 469339 | 2692643 | 1236 | 3326.98 | 76.80 (75.52) | 34.71 (33.63) | 25.12 (24.06) | 132.4x |
| cyclic-8 | 8 | 14 | 258x277 | 9576 | 15458 | 93 | 1.43 | 0.75 (0.66) | 0.57 (0.48) | 0.70 (0.61) | 2.5x |
| cyclic-9 | 1 | 12 | 561x581 | 35919 | 82076 | 159 | 13.07 | 4.10 (3.77) | 2.56 (2.24) | 2.73 (2.43) | 5.1x |

The "best packed vs generic" column compares like with like (full RREF against full RREF), and it is
**not** the end-to-end gain: F4's production elimination is structured (pivot/non-pivot split,
selective back substitution) and does much less than a full RREF — on `mq-13` the generic RREF
takes 590 ms where F4's entire run takes 57 ms. §3 makes the honest comparison.

## 3. End-to-end: what it would do to the solve

The kernel is not wired into F4, so the end-to-end figure is a **projection, not a measured solve**:
F4's own measured elimination stage (`measure_stages`) is replaced by the best packed full RREF of
the same matrices, conversion included, and everything else is held fixed. It is conservative in
one direction (F4 needs less than a full RREF, so a packed structured elimination would do better)
and optimistic in none that we know of, because the packed time already includes conversion.

| instance | F4 total ms | F4 elimination ms | elimination share | best packed RREF ms | projected end-to-end |
| --- | ---: | ---: | ---: | ---: | ---: |
| mq-8 | 1.2 | 0.22 | 19% | 0.15 | 1.07x |
| mq-10 | 6.3 | 2.90 | 46% | 1.25 | 1.36x |
| mq-12 | 26.7 | 14.78 | 55% | 3.50 | 1.73x |
| mq-13 | 56.8 | 34.84 | 61% | 5.48 | 2.07x |
| sparse-mq-12 | 1.8 | 0.21 | 11% | 0.28 | 0.96x |
| overdetermined-mq-14 | 17.0 | 7.43 | 44% | 1.47 | 1.54x |
| overdetermined-mq-16 | 233.6 | 190.31 | 81% | 25.12 | 3.41x |
| cyclic-8 | 1.3 | 0.27 | 21% | 0.57 | 0.81x |
| cyclic-9 | 4.3 | 1.28 | 30% | 2.56 | 0.77x |

This answers the owner's Amdahl question on #272 directly: in characteristic two the elimination
share is **not** where it sits over prime fields (7%–22%). On dense Boolean MQ it is 46%–81% and
grows with the instance, so the issue does not inherit #269's verdict. On sparse systems the share
is 11%–30% and the dense packed kernel loses to the sparse one, because a dense bit row walks every
column while the sparse merge walks only the nonzeros.

## 4. The Four Russians crossover

Dense random square matrices (density 0.5, full rank or nearly), kernel only:

| n | plain ms | k=4 ms | k=6 ms | k=8 ms | k=10 ms | best k | plain / best |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 64 | 0.009 | 0.012 | 0.013 | 0.018 | 0.035 | 4 | 0.77x |
| 128 | 0.078 | 0.036 | 0.034 | 0.044 | 0.082 | 6 | 2.28x |
| 256 | 0.359 | 0.143 | 0.129 | 0.142 | 0.224 | 6 | 2.80x |
| 512 | 1.504 | 0.492 | 0.422 | 0.455 | 0.681 | 6 | 3.57x |
| 1024 | 6.318 | 1.832 | 1.501 | 1.530 | 2.135 | 6 | 4.21x |
| 2048 | 26.013 | 7.645 | 5.643 | 5.286 | 6.856 | 8 | 4.92x |
| 4096 | 139.381 | 41.672 | 31.293 | 27.338 | 32.874 | 8 | 5.10x |
| 8192 | 741.851 | 268.619 | 189.278 | 163.814 | 178.529 | 8 | 4.53x |

**Crossover: between n = 64 and n = 128.** At n = 64 one 64-column word holds the whole matrix and
the table build is pure overhead; from n = 128 Four Russians wins at every size, settling at about
5x. The best table width grows slowly with n (6 up to 1024, 8 beyond), consistent with M4RI's
published tuning, which is ⌊0.75 log2 n⌋ minus a small constant rather than the analytic log2 n
(Albrecht, Bard, Hart, arXiv:0811.1714, §3.1 and §5). M4RI's papers publish **no small-size
crossover against plain Gaussian elimination** — their comparisons start at n = 10 000 — and their
upper crossover is to recursive PLS/PLE elimination, which Albrecht and Pernet (arXiv:1006.1744,
Table 1) report as faster than M4RI at every listed size from n = 10 000, with a hybrid switching
from M4RI to PLS once density reaches 15% (§6). Zeebra's F4 matrices here are 300–7000 rows, far
below that upper range, so **asymptotically fast PLE is out of range and Four Russians is the
relevant algorithm.**

How the prototype differs from M4RI, so the figures are read correctly: pivots are searched one
aligned 64-column word at a time by Gauss-Jordan on that word alone (one machine word per row, not
the whole row); the word's pivot rows are then mutually reduced in full, and every other row is
cleared from `2^k`-entry Gray-code tables indexed by the row's own bits at the pivot columns. No
SIMD intrinsics, no cache blocking, no multithreading; the `xor` loop is left to the
autovectorizer. M4RI is faster in absolute terms — it is not a comparand here (#272's P2 comment
asks for it pinned as an external comparand later).

## 5. Correctness

`src/linalg/gf2.rs` tests, written before the kernel: pack/unpack round trip across word tails
(0, 1, 63, 64, 65, 127, 128, 130 columns) and empty shapes; RREF and rank equality against the
generic kernel on random matrices at three densities and eight shapes, on rank-deficient matrices
built as random sums of a few base rows, on zero and duplicated-row matrices, for plain
Gauss-Jordan and for every table width `k ∈ {1, 2, 3, 4, 6, 8, 10}`; the same equality on every
matrix F4 builds for `katsura-4` over `GF(2)` with field equations; a row-operation count showing
Four Russians performs fewer than half the `xor`s of plain Gauss-Jordan at n = 1024; and a refused
table width of 0. The harness re-asserts equality on every measured matrix and every repetition.

## 6. What is not done, and where it went

- **Wiring into F4.** Needs (a) a structured packed elimination matching F4's private
  candidate-output contract rather than a full RREF, (b) a dispatch rule by matrix density and
  shape — the sparse families above regress — and (c) a measured solve, not a projection.
  Filed as #777 (board #7, Priority Medium).
- **GF(2^e), M4RIE slicing.** Not attempted; blocked on the defining-polynomial convention.
- **Multicore XOR, cache blocking, M4RI/M4RIE as pinned external comparands** (#272's P2 comment):
  not attempted. The serial algorithmic factor measured here is the baseline those would be
  isolated against.
