# Characteristic-two linear algebra: bit-packed GF(2) elimination and Four Russians

**Measured at:** `30f24f6f` for §1–§4 (release, `RUSTC_WRAPPER=""`, `CARGO_INCREMENTAL=0`), one core
(`taskset -c 37`), serialized through `tools/benchlock.sh` (tag `272`; 1-minute load 4.2–4.4 at
START and END of both runs on this 128-core machine). Each cell is the minimum of 5 repetitions,
arms interleaved with a rotating order. §7 (#777) at `21acc4db` (per-batch table) and `db5c5c05`
(solves) — commits on `perf/777-gf2-f4-dispatch` before a rebase onto `2e95420c` that touched no
file they built from (the same trees are `760a9432` and `ad8b53ba`), squashed into the PR that closed #777 — same
core, same lock (tag `777`, load 7.5–14.0), release build with the repository's `.cargo/config.toml`.

Reference for #272 (H16), scoped to the **kernel** only — representation and solving route stay
with #218 and #196. The instrument is `examples/gf2_packed_elimination.rs`; the kernel is
`src/linalg/gf2.rs` (`BitMatrix`, `reduced_row_echelon_packed`,
`reduced_row_echelon_four_russians`), written independently of M4RI (GPL; read for the published
figures only, not the source).

## Decision

- **Adopted (#777, §7): F4 eliminates dense GF(2) batches bit-packed by default**, measured at
  **1.5x–3.9x end to end** on dense MQ with bases asserted equal, and 1.00x–1.16x on the sparse
  controls. The rest of this bullet is #272's original projection.
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

- **Wiring into F4.** Done in #777; see §7.
- **GF(2^e), M4RIE slicing.** Not attempted; blocked on the defining-polynomial convention.
- **Multicore XOR, cache blocking, M4RI/M4RIE as pinned external comparands** (#272's P2 comment):
  not attempted. The serial algorithmic factor measured here is the baseline those would be
  isolated against.

## 7. Wired into F4 (#777): measured solves

`F4Options::gf2_elimination` (`Gf2Elimination::{Generic, Auto, Packed}`, default `Auto`) routes a
batch through `src/grobner/f4/packed.rs` when F4 is structured with reduced batch rows, the field
has characteristic two, and every coefficient is one. The route keeps F4's contract rather than
running a full RREF:

1. **Reducer block untouched.** The reducer rows stay sparse and are never written; groups of up
   to 8 are copied out, made the identity on their own leads, and applied to the packed pair rows
   through a Gray-code table — or one pivot at a time when too few pair rows touch the group for
   the table to pay (`linalg::gf2::reduce_against_pivots`).
2. **Pair block by Four Russians**, `k` = 4/6/8 by pair-row count (§4's crossover), with
   **selective back substitution**: a pivot row is cleared by later words' tables only if its
   leading column is a candidate column (`reduced_row_echelon_four_russians_selected`). Unselected
   rows stay echelon, as in #749's candidate-only route.
3. **Write-back** of the pair rows to sparse form, row by row against the entry allowance and
   against `max_live_bytes` with the bit matrix still charged.

A candidate is the unique reduced row of the batch's row space at its column, so it equals the
generic route's candidate exactly. Every repetition below asserts that — per batch for the
candidates, per solve for the basis. Budgets: the packed working set (bit matrix, tables, indices,
selection mask) is added to the sparse matrix's bytes before anything is packed. If the total goes
over `max_live_bytes`, the batch is **declined** to the generic route, which then runs under its
own budget, so choosing packing never refuses a computation the generic route admits. A crossing
during write-back is refused as `TooManyNonzeros` or `TooManyLiveBytes`. Tests:
`grobner::f4::packed::tests` (identical bases across three orders on dense and sparse Boolean
systems; per-batch candidates including rank-deficient and candidate-free batches; empty and
all-pivot batches; fallback for odd characteristic, a non-binary `GF(2^8)` coefficient and echelon
output; byte decline at the exact admitted budget; entry refusal at exactly the reported peak; a
budget the generic route refuses stays refused; the dispatch rule) and `linalg::gf2::tests`.

### 7.1 Per batch: where the threshold comes from

`gf2_f4_dispatch batches 5`: every batch of each instance, replayed under both routes. The times are
F4's elimination stage (`measure_stages`), conversion included, minimum of 5 interleaved
repetitions. "auto picks" is the shipped rule applied to each row (recomputed from the row; the binary printed the first rule tried). The table was taken at `21acc4db`, whose
packed route is byte-identical to `db5c5c05`'s; only the rule changed between them.

| instance | batch | rows | reducer rows | pair rows | columns | entries | density ppm | generic us | packed us | generic/packed | auto picks |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | --- |
| mq-10 | 0 | 22 | 10 | 12 | 64 | 233 | 165483 | 3.5 | 2.6 | 1.33x | generic |
| mq-10 | 1 | 221 | 137 | 84 | 281 | 2620 | 42189 | 213.9 | 59.4 | 3.60x | packed |
| mq-10 | 2 | 1094 | 380 | 714 | 706 | 23380 | 30271 | 2521.4 | 840.8 | 3.00x | packed |
| mq-10 | 3 | 120 | 10 | 110 | 66 | 346 | 43687 | 8.7 | 19.2 | 0.45x | generic |
| mq-10 | 4 | 169 | 45 | 124 | 108 | 1593 | 87278 | 40.2 | 33.6 | 1.20x | generic |
| mq-12 | 0 | 27 | 9 | 18 | 83 | 377 | 168228 | 7.3 | 4.3 | 1.68x | generic |
| mq-12 | 1 | 315 | 211 | 104 | 447 | 5711 | 40560 | 528.9 | 112.5 | 4.70x | packed |
| mq-12 | 2 | 1817 | 861 | 956 | 1353 | 73183 | 29769 | 13930.8 | 2275.4 | 6.12x | packed |
| mq-12 | 3 | 163 | 13 | 150 | 91 | 721 | 48608 | 17.3 | 30.6 | 0.56x | generic |
| mq-12 | 4 | 550 | 66 | 484 | 243 | 4693 | 35114 | 327.4 | 181.0 | 1.81x | packed |
| mq-12 | 5 | 68 | 0 | 68 | 34 | 68 | 29412 | 2.6 | 7.1 | 0.36x | generic |
| mq-13 | 0 | 31 | 13 | 18 | 103 | 500 | 156593 | 8.9 | 5.0 | 1.76x | generic |
| mq-13 | 1 | 372 | 254 | 118 | 558 | 7495 | 36107 | 846.9 | 152.5 | 5.55x | packed |
| mq-13 | 2 | 2350 | 1230 | 1120 | 1906 | 117792 | 26298 | 34057.4 | 3853.1 | 8.84x | packed |
| mq-13 | 3 | 186 | 16 | 170 | 105 | 902 | 46185 | 22.2 | 37.9 | 0.59x | generic |
| mq-13 | 4 | 812 | 78 | 734 | 333 | 7770 | 28736 | 613.0 | 362.9 | 1.69x | packed |
| mq-13 | 5 | 176 | 4 | 172 | 94 | 366 | 22123 | 11.0 | 32.6 | 0.34x | generic |
| overdetermined-mq-14 | 0 | 62 | 12 | 50 | 120 | 1504 | 202151 | 47.3 | 14.6 | 3.25x | generic |
| overdetermined-mq-14 | 1 | 672 | 334 | 338 | 672 | 19194 | 42504 | 3939.3 | 501.4 | 7.86x | packed |
| overdetermined-mq-14 | 2 | 1036 | 252 | 784 | 564 | 27030 | 46260 | 4003.7 | 770.3 | 5.20x | packed |
| overdetermined-mq-14 | 3 | 224 | 14 | 210 | 120 | 2084 | 77530 | 83.1 | 53.4 | 1.56x | generic |
| overdetermined-mq-14 | 4 | 113 | 49 | 64 | 82 | 935 | 100907 | 15.0 | 16.6 | 0.91x | generic |
| overdetermined-mq-16 | 0 | 69 | 15 | 54 | 153 | 2189 | 207351 | 87.6 | 20.9 | 4.18x | packed |
| overdetermined-mq-16 | 1 | 874 | 466 | 408 | 965 | 32798 | 38887 | 9403.0 | 855.2 | 10.99x | packed |
| overdetermined-mq-16 | 2 | 6958 | 1298 | 5660 | 3146 | 416135 | 19010 | 207326.7 | 26361.1 | 7.86x | packed |
| overdetermined-mq-16 | 3 | 288 | 16 | 272 | 153 | 1993 | 45230 | 81.6 | 81.4 | 1.00x | packed |
| overdetermined-mq-16 | 4 | 608 | 104 | 504 | 357 | 16224 | 74746 | 743.8 | 291.9 | 2.55x | packed |
| sparse-mq-12 | 0 | 19 | 7 | 12 | 33 | 67 | 106858 | 2.0 | 2.1 | 0.96x | generic |
| sparse-mq-12 | 1 | 9 | 3 | 6 | 12 | 22 | 203704 | 0.8 | 1.0 | 0.76x | generic |
| sparse-mq-12 | 2 | 202 | 102 | 100 | 244 | 770 | 15622 | 43.4 | 44.2 | 0.98x | generic |
| sparse-mq-12 | 3 | 443 | 129 | 314 | 311 | 2239 | 16251 | 131.8 | 169.3 | 0.78x | generic |
| sparse-mq-12 | 4 | 135 | 13 | 122 | 76 | 304 | 29630 | 8.8 | 24.2 | 0.37x | generic |
| sparse-mq-12 | 5 | 90 | 36 | 54 | 64 | 217 | 37674 | 5.2 | 9.5 | 0.55x | generic |
| cyclic-8 | 0 | 18 | 14 | 4 | 44 | 96 | 121212 | 1.6 | 1.6 | 0.99x | generic |
| cyclic-8 | 1 | 44 | 38 | 6 | 86 | 214 | 56554 | 4.1 | 3.6 | 1.15x | generic |
| cyclic-8 | 2 | 153 | 125 | 28 | 192 | 936 | 31863 | 20.1 | 16.9 | 1.19x | packed |
| cyclic-8 | 3 | 168 | 112 | 56 | 179 | 1286 | 42764 | 37.8 | 27.0 | 1.40x | packed |
| cyclic-8 | 4 | 166 | 96 | 70 | 157 | 1094 | 41977 | 32.5 | 26.5 | 1.23x | packed |
| cyclic-8 | 5 | 145 | 63 | 82 | 119 | 860 | 49841 | 22.0 | 22.9 | 0.96x | generic |
| cyclic-8 | 6 | 236 | 214 | 22 | 246 | 1322 | 22771 | 19.9 | 23.4 | 0.85x | packed |
| cyclic-8 | 7 | 253 | 251 | 2 | 273 | 1212 | 17548 | 14.1 | 16.4 | 0.86x | generic |
| cyclic-8 | 8 | 258 | 256 | 2 | 277 | 1100 | 15392 | 14.0 | 16.4 | 0.86x | generic |
| cyclic-8 | 9 | 200 | 198 | 2 | 216 | 830 | 19213 | 12.8 | 12.1 | 1.06x | generic |
| cyclic-8 | 10 | 55 | 41 | 14 | 70 | 216 | 56104 | 4.4 | 5.0 | 0.88x | generic |
| cyclic-8 | 11 | 34 | 18 | 16 | 27 | 80 | 87146 | 2.0 | 3.1 | 0.66x | generic |
| cyclic-8 | 12 | 71 | 33 | 38 | 53 | 320 | 85039 | 6.7 | 7.5 | 0.89x | generic |
| cyclic-8 | 13 | 5 | 3 | 2 | 5 | 10 | 400000 | 0.4 | 0.6 | 0.62x | generic |
| cyclic-9 | 0 | 20 | 16 | 4 | 54 | 117 | 108333 | 1.8 | 1.8 | 1.00x | generic |
| cyclic-9 | 1 | 51 | 45 | 6 | 113 | 272 | 47198 | 5.0 | 4.0 | 1.25x | generic |
| cyclic-9 | 2 | 210 | 182 | 28 | 294 | 1486 | 24069 | 43.2 | 25.6 | 1.69x | packed |
| cyclic-9 | 3 | 561 | 425 | 136 | 581 | 6139 | 18835 | 407.9 | 183.4 | 2.22x | packed |
| cyclic-9 | 4 | 253 | 189 | 64 | 282 | 2664 | 37339 | 84.0 | 45.0 | 1.87x | packed |
| cyclic-9 | 5 | 289 | 161 | 128 | 270 | 3122 | 40010 | 157.3 | 78.3 | 2.01x | packed |
| cyclic-9 | 6 | 238 | 110 | 128 | 201 | 1706 | 35662 | 63.5 | 49.7 | 1.28x | packed |
| cyclic-9 | 7 | 577 | 323 | 254 | 447 | 6439 | 24965 | 392.4 | 218.3 | 1.80x | packed |
| cyclic-9 | 8 | 494 | 492 | 2 | 529 | 3878 | 14840 | 32.3 | 38.1 | 0.85x | generic |
| cyclic-9 | 9 | 551 | 549 | 2 | 586 | 3895 | 12063 | 35.0 | 41.8 | 0.84x | generic |
| cyclic-9 | 10 | 545 | 543 | 2 | 580 | 3666 | 11598 | 34.8 | 40.2 | 0.87x | generic |
| cyclic-9 | 11 | 411 | 409 | 2 | 446 | 2535 | 13829 | 30.3 | 28.1 | 1.08x | generic |

Density alone does not separate the two sides, and the first rule tried (2% density, 64 columns)
got both ends wrong. Every batch the packed route lost by more than 15% was either **under two
words wide** (66–105 columns, 0.34x–0.59x, under 25 µs each) or a **two-pair-row batch** against
hundreds of reducers (cyclic-8/9's late batches, 0.84x–0.87x), where the route is pure
conversion. The rule admits one measured loss: cyclic-8's batch 6 (22 pair rows, 0.85x, 3.5 µs). Overdetermined-MQ-16's 6958x3146 batch is only 1.9% dense and is the largest win
(7.9x, 181 ms saved). Shipped rule (`Gf2Elimination::prefers_packed`): **at least 128 columns, at
least 16 pair rows, and at least 18 000 ppm density.** The density margin is narrow and is stated
rather than hidden: sparse-MQ-12's two largest batches (1.56%, 1.63%) lose at 0.98x and 0.78x and stay
generic, while cyclic-9's 1.88% batch wins at 2.2x and packs. A family sitting between 1.6% and
1.9% could land on the wrong side.

### 7.2 End to end

`gf2_f4_dispatch solve 21`: whole F4 solves under each setting, minimum of 21 interleaved
repetitions, bases asserted equal to `Generic` in every one. "elim" is the summed elimination stage.
A 7-repetition run at the same commit agreed within 5% on every row (sparse-MQ-12 read 0.95x there
and 1.00x here, with no batch packed in either, so that gap is noise).

| instance | basis | batches | generic ms | generic elim ms | auto ms | auto packed batches | auto elim ms | packed ms | packed elim ms | generic/auto | generic/packed |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| mq-10 | 10 | 5 | 5.51 | 2.84 | 3.60 | 2 | 0.99 | 3.58 | 0.98 | **1.53x** | 1.54x |
| mq-12 | 13 | 6 | 25.39 | 14.69 | 13.01 | 3 | 2.60 | 13.06 | 2.59 | **1.95x** | 1.94x |
| mq-13 | 16 | 6 | 54.35 | 33.42 | 25.68 | 3 | 4.51 | 24.88 | 4.42 | **2.12x** | 2.18x |
| overdetermined-mq-14 | 14 | 5 | 18.43 | 8.02 | 11.66 | 2 | 1.48 | 10.64 | 1.33 | **1.58x** | 1.73x |
| overdetermined-mq-16 | 16 | 5 | 249.33 | 209.48 | 64.38 | 5 | 25.22 | 62.14 | 24.42 | **3.87x** | 4.01x |
| sparse-mq-12 | 12 | 6 | 1.97 | 0.22 | 1.96 | 0 | 0.22 | 1.97 | 0.28 | **1.00x** | 1.00x |
| cyclic-8 | 8 | 14 | 1.16 | 0.27 | 1.13 | 4 | 0.24 | 1.13 | 0.25 | **1.03x** | 1.02x |
| cyclic-9 | 1 | 12 | 4.51 | 1.40 | 3.89 | 6 | 0.84 | 3.89 | 0.87 | **1.16x** | 1.16x |

**Measured, not projected:** the dispatch is worth **1.5x–2.2x on dense MQ-10..13, 1.6x on
overdetermined MQ-14 and 3.9x on overdetermined MQ-16**, all above §3's projection (1.36x–3.41x),
because the structured route does less work than the full RREF the projection substituted. The
sparse controls do **not** regress: sparse-MQ-12 packs nothing (1.00x), and cyclic-8/9 pack 4 and 6
of their batches for 1.03x and 1.16x. `Packed` everywhere is close to `Auto` on these families
(within 9%), so the rule's job is protecting the sparse controls, not finding the wins. Hence
`Auto` is the default, and `F4Options::baseline()` keeps `Generic`.

Not measured here: the two-binary A/B of `main` against this branch at defaults. The `Generic` arm
runs the same code as before, with only the closure around it reshaped, and the in-binary arms
isolate the dispatch alone. Multicore XOR, cache blocking, GF(2^e) slicing and M4RI as a comparand
are still out of scope (§6).
