# Blocked dense elimination on F4's dense residual (#1193, laptop stage)

**Status:** laptop stage complete, 2026-11-27. Research prototype, opt-in by construction: nothing in
F4 or the signature engine calls it. **Measured at:** `3e1810b1` (§7, the campaign),
`efbc8a6c` (§6 tuning and square products, and the §5 verification runs; it differs from
`3e1810b1` only by a counter and the summary script) and `14424217` (§5 product counts,
`--features research-work`; they count only shipped kernels, which no commit here changes). The
three commits sit on `8abf1b4e`, before this branch was rebased, and are kept by the tag
`measured/1193-laptop-dev`. Binary SHA-256s are in `research/1193-blocked-dense/provenance.txt`. Release profile with **thin LTO and
16 codegen units** (`CARGO_PROFILE_RELEASE_LTO=thin CARGO_PROFILE_RELEASE_CODEGEN_UNITS=16`), not
the repository's fat LTO, for every binary. **Host: Apple M4 Pro laptop, macOS, unpinned**, one
thread per process, with four other agents building and testing on the same machine; the
1-minute load is recorded with every figure. **Every timing here is a development figure. None is
a deciding measurement**, and none satisfies a bench-host protocol. Read them as ratios between
arms of the same session.
**Data:** [`research/1193-blocked-dense/`](../../research/1193-blocked-dense/README.md).

## 1. Question

Dense MQ is where Zeebra is furthest behind grobx at one worker (18–24× in the M35 baseline, PR
#1175; about 30× in #1033). F4's elimination on those rows is one batch's forward pass, and 90–98%
of its products land on rows whose active span is at least half full
([`dense-small-prime-rebaseline.md`](dense-small-prime-rebaseline.md) §§4–5). #1193 asks whether a
blocked schedule, FFLAS-FFPACK style, changes the picture: split the batch into a sparse top and a
dense residual, and echelonize the residual by a recursive elimination whose inner step is a matrix
product, classical with delayed modular reduction below a crossover and Strassen–Winograd above it.

The issue's stop condition is a residual too small a share of the work. It does not trigger (§5).

## 2. What the tree has today (work item 1)

| Path | What it is | Blocked dense elimination? |
|---|---|---|
| `linalg::lane` (#945, #1183) | Row-at-a-time forward pass in `u32`/`u64` lanes with delayed reduction; a pivot is stored dense over its span when ≥ 25% full | No. The schedule is a sequence of row operations (rank-1 updates, one target row at a time). Dense storage is per pivot row, and there is no product of two blocks |
| `linalg::dense` (`DenseRows`, `DenseAccumulator`) | Dense storage under the sparse contract, or one dense working row | No. Same row-at-a-time schedule as the sparse backend |
| `Matrix` `Mul` ([`matmul-register-tiling.md`](matmul-register-tiling.md)) | A 2×8 register-tiled classical product over any `FiniteField`, reducing every product | A product kernel, but unused by elimination and without delayed reduction |
| Faugère–Lachartre order ([`residual-split.md`](residual-split.md), #816) | Sweep the pair rows against the reducer block first, then echelonize `D' = D - C A⁻¹ B` | The split, but `D'` is echelonized by the sparse/accumulator row-at-a-time backend |
| GF(2) Four Russians (`linalg::gf2`, [`gf2-residual-packing.md`](gf2-residual-packing.md)) | Bit-packed rows; M4RI-style tables of 2^k row combinations | Blocked in the Four Russians sense (k rows at a time through a table), and only over GF(2). Not a recursive product-based echelon |

So before this PR nothing in the tree computes an echelon form by block products. The new module
`src/linalg/blocked.rs` is the first.

## 3. The prototype

**Representation.** Residues are `f64` integers in `[0, p)`, for any prime `p < 2^26`. A matrix is
dense and row-major.

**Product kernel** (`blocked::multiply`). Classical: the right operand is packed into strips of 8
columns and depth 256, and a 4×8 register tile accumulates `f64` fused multiply-adds without
reducing. Accumulators reduce once at the end, or every `λ` products (§4) when the inner dimension
exceeds `λ`; at GF(31) and GF(32003) that never happens. Above the crossover, Strassen–Winograd:
seven half-size products and fifteen additions in the order of Boyer, Dumas, Pernet and Zhou
(ISSAC 2009, §2), odd dimensions peeled into classical border products, and recursion while every
dimension is at least `winograd_from` (default 1024, §6). On one M4 Pro core the classical kernel
runs at 50–54 GFLOP/s, which is 25–27 G multiply-adds per second (§6).

**Echelon** (`blocked::reduced_echelon`). Recursive on rows. This is the rank-profile-revealing
structure of Jeannerod, Pernet and Storjohann (JSC 2013), written for the reduced row echelon form:

1. Split `A = [A₁; A₂]` by rows. Recursively, `E₁ = RREF(A₁)` with pivot columns `P₁`.
2. `G = A₂[:, F] - A₂[:, P₁] · E₁[:, F]`, `F` the columns not in `P₁` (one product). `G` is `A₂`
   reduced against `E₁`, and is zero on `P₁`.
3. Recursively, `E₂ = RREF(G)` with pivots `Q ⊂ F`.
4. `E₁[:, F] -= E₁[:, Q] · E₂` (one product) clears `Q` from the upper rows.
5. Merge the rows of `E₁` and `E₂` by pivot column.

Each step keeps the invariant that every row has a unit pivot and zeros in every other pivot
column, and the rows of the merge span the row space of `A`. A row of `E₁` gains no entry left of
its pivot in step 4, because `E₁[i, q] ≠ 0` only for `q` right of row `i`'s pivot and `E₂`'s row for
`q` is zero left of `q`. So the result is the reduced row echelon form, which is unique. Below
`leaf_rows` rows (default 128) the leaf is row-at-a-time Gauss–Jordan with the working row's
reduction delayed in the same way.

**Sweep** (`blocked::sweep_to_dense`). The sparse top of a reducers-first batch, in the same
arithmetic: four pair rows at a time in `f64` accumulators interleaved by column, each reducer
applied when the scan reaches its lead, reducers stored dense over their span when at least 25%
full. The output is `D'` on the free columns, dense. `blocked::residual_reduced_echelon` composes
the two.

**Counts** (`BlockedCounts`): multiply-adds performed, accumulator reductions, modular additions,
Winograd splits, classical products, inversions. They are a function of the input and the options
only, so a second run reproduces them exactly (`test_counts_are_deterministic`). They count
operations performed, zeros included; the shipped kernels' `coefficient_products` count nonzero
products only, so the two are not the same unit.

Nothing here is FFLAS-FFPACK code. FFLAS-FFPACK is LGPL-2.1-or-later ("linking only" in
[`external-provenance-policy.md`](external-provenance-policy.md) §2, read there as not available),
and its source was not read for this work. The algorithms come from the cited papers, and the code
was written independently.

## 4. Overflow proof for the delayed accumulation

Let `p` be prime with `2 ≤ p < 2^26`, and define the depth

`λ = ⌊(2^52 − (p − 1)) / (p − 1)²⌋`

(`Modulus::depth`; λ = 5.0 × 10¹² at GF(31), 4,397,496 at GF(32003), 1 at 2^26 − 5). It is the
`f64` row of `research/1033-dense-rebaseline/bounds.py` with the ceiling 2^52 in place of 2^53. The
bit of headroom keeps the reduction step exact, below.

**Lemma 1 (accumulation is exact).** Let `s₀` be an integer in `[0, p − 1]` and
`s_t = s_{t−1} + a_t b_t` with integers `a_t, b_t ∈ [0, p − 1]`, for `t ≤ λ`. Then every `s_t` is
an integer in `[0, 2^52]`, and computing it in `f64`, as `a·b + s` or as a fused multiply-add,
gives it exactly.

*Proof.* `s_t ≤ (p − 1) + t (p − 1)² ≤ (p − 1) + λ (p − 1)² ≤ 2^52` by the choice of `λ`. Every
integer of magnitude at most 2^53 is a double. `a_t b_t ≤ (p − 1)² < 2^52`, so the rounded product
is the product, and the rounded sum of two such integers whose exact sum is at most 2^52 is the
sum. A fused multiply-add rounds the exact value `a_t b_t + s_{t−1}` once, and that value is a
double, so it is returned exactly. ∎

**Lemma 2 (reduction is exact).** For an integer `0 ≤ s ≤ 2^52`, `Modulus::reduce` returns `s mod p`.

*Proof.* With `u = 2^−53`, `fl(1/p) = (1/p)(1 + δ₁)` and `y = fl(s · fl(1/p)) = (s/p)(1 + δ₁)(1 + δ₂)`,
`|δᵢ| ≤ u`. So `|y − s/p| ≤ (s/p)(2u + u²) < (2^52/p) · 2^−52 · (1 + u) < 1`, hence
`q = ⌊y⌋ ∈ {⌊s/p⌋ − 1, ⌊s/p⌋, ⌊s/p⌋ + 1}` and `q ≥ 0`. Then `q p ≤ s + p ≤ 2^52 + 2^26 < 2^53` is a
double, so `fl(q p) = q p`; and `r = s − q p` is an integer in `(−p, 2p)`, a double, so its
rounded difference is exact. One conditional add of `p` (if `r < 0`) and one conditional subtract
(if `r ≥ p`) return `r` to `[0, p)`, where it is `s mod p`. ∎

**Where the lemmas are applied.** Each delayed site keeps a count of products added since the
operand was last a residue, and reduces before the count would pass `λ`:

- *Classical kernel.* Accumulators start at 0. The inner dimension is walked in chunks of at most
  `min(256, λ)`. Before a chunk that would take the count past `λ`, every accumulator is reduced
  (`held + kc > depth`). Each accumulator is therefore a residue plus at most `λ` products when it
  is reduced (Lemma 1), and the reduction is exact (Lemma 2).
- *Leaf and sweep.* The working row starts from residues. Each pivot or reducer application adds
  at most one product `(p − x) · v`, with `p − x, v ∈ [0, p − 1]`, to each cell. After `λ`
  applications the cells at and right of the current column are reduced. Cells left of it receive
  no further product, because a later pivot leads further right and is zero left of its lead. A
  cell is read only through `reduce`.
- *Normalization and upper clearing in the leaf* add one product to a residue and reduce at once.
- *Winograd.* Its additions take two residues to `(−p, 2p)`, exactly, and one conditional correction
  returns a residue. Every recursive product returns residues, by induction on the recursion with
  the classical kernel as the base. The seven-product identity holds over any commutative ring, so
  it holds mod `p`. FFLAS skips these intermediate reductions by bounding the growth of Winograd's
  intermediate values over the recursion levels (Dumas, Giorgi and Pernet, TOMS 2008). This
  prototype reduces at every level instead, which makes the proof the classical one at an `O(n²)`
  cost per level: the counts in §6 put the additions at 0.3% of the multiply-adds.

**Tests that hold the proof to the code.** `test_depth_is_the_largest_safe_product_count` checks
`λ` is the largest safe count for six primes. `test_reduce_is_exact_across_its_whole_range` checks
`reduce` against integer `%` at both ends of `[0, 2^52]` and on 10,000 random points per prime.
`test_the_largest_residues_stay_exact_at_the_full_depth` multiplies all-`(p − 1)` matrices, the
bound's worst case, at 32003, 65537 and 2^26 − 5 (where `λ = 1`, so every product is reduced).
`test_a_shallow_depth_reduces_mid_accumulation_and_stays_exact` forces `λ` to 1, 2, 3 and 7, so the
mid-accumulation reductions of the kernel, the leaf and the sweep all run.

## 5. Exactness and the dense residual (work item 2)

**Exactness, synthetic.** Fourteen tests in `src/linalg/blocked.rs`:

- products against a `u128` textbook sum, at primes 2, 3, 31, 32003, 65537 and 2^26 − 5, over
  shapes from 1×1×1 to 33×70×41 and 5×300×9, classical and with Winograd forced from 2, 3 and 8
  (deep recursion and every peeling case);
- the reduced echelon form against textbook Gauss–Jordan on random, low-rank (rank 1, 7, 64 of 65),
  zero, empty, repeated-row, staircase and all-`(p − 1)` matrices, at the same six primes and five
  leaf/crossover settings;
- the same matrices over `Zp31`, `Zp32003` and `Zp65537` against the shipped `Backend::Dense`,
  `Sparse` and `Adaptive` echelon followed by the shipped back-substitution, entry for entry;
- the sweep against the shipped `sweep_rows_against_pivots`, and the residual's reduced form
  against the rows of the whole batch's reduced form that lead outside the reducer block, through
  the shipped sparse and accumulator backends and through the lane kernel, on synthetic
  reducers-first batches (sparse and dense reducers, lower rows dependent on the reducers,
  repeated, and zero).

**Exactness, on the captured batches.** Every `split` run of §7 asserts that the blocked reduced
form of `D'` equals the lane kernel's forward pass on `D'` followed by the shipped
back-substitution, entry for entry. A `--verify` run on each n = 18 batch (b3 and b2, both fields;
`verify-efbc8a6c.jsonl`) also asserts that it equals the rows, leading outside the reducer block,
of the **whole batch's** lane forward pass followed by a full back-substitution. F4's candidates
are among those rows, in exactly that form. The same runs check the `f64` sweep's `D'` against the
shipped `sweep_rows_against_pivots`. Every assertion held on every run. The whole-batch check was
not run at n = 20, because its full back-substitution would take the process past the laptop's
memory allowance. n = 20 is checked against the lane route on `D'` only.

**Captures.** The four batches were rebuilt with the shipping `sig_f4_study --capture` at
`8abf1b4e` (origin/main at the start of this work). The GF(31) archives' SHA-256s equal the pins in
`research/1033-dense-rebaseline/captures.json`. The GF(32003) batches are new, with the same
dimensions and reducer counts as GF(31).

| Batch (degree 5) | Batch rows × columns | Reducers | `D'` rows × columns | `D'` density | span fraction | rank of `D'` |
|---|---|---|---|---|---|---|
| GF(31), n = 18 | 24,863 × 13,866 | 6,457 | 18,406 × 7,409 | 0.223 | 0.604 | 7,408 |
| GF(32003), n = 18 | 24,863 × 13,866 | 6,457 | 18,406 × 7,409 | 0.231 | 0.604 | 7,408 |
| GF(31), n = 20 | 37,240 × 24,262 | 12,654 | 24,586 × 11,608 | 0.342 | 0.668 | 11,607 |
| GF(32003), n = 20 | 37,240 × 24,262 | 12,654 | 24,586 × 11,608 | 0.353 | 0.668 | 11,607 |

`D'` rows are the pair rows that do not sweep to zero; its columns are those no reducer leads. Span
fraction is the share of `D'`'s cells at or right of each row's lead, and density is nonzeros over
all cells.

Nonzero coefficient products of the shipped kernels (`counts`, `--features research-work`,
binary `14424217`; deterministic):

| Batch | Shipped forward pass | of which against reducers | against discovered pivots | Sweep (`D'`) | Forward pass on `D'` | `D'` share of FL order |
|---|---|---|---|---|---|---|
| GF(31), n = 18 | 93.89 G | 34.19 G | 59.70 G (63.6%) | 31.20 G | 37.86 G | 54.8% |
| GF(32003), n = 18 | 100.31 G | 36.52 G | 63.79 G (63.6%) | 33.34 G | 40.43 G | 54.8% |
| GF(31), n = 20 | 451.09 G | 145.82 G | 305.27 G (67.7%) | 136.03 G | 186.42 G | 57.8% |
| GF(32003), n = 20 | 481.74 G | 155.69 G | 326.05 G (67.7%) | 145.28 G | 199.02 G | 57.8% |

**The residual is the bulk of the work, so the stop condition does not trigger.** Under the
shipped forward pass, products against pivots discovered among the pair rows are 64–68% of the
total. Under the Faugère–Lachartre order, the echelon of `D'` is 55–58% of the products and the
sweep the rest. The order alone saves 26–29% of the products: 69.1 G against 93.9 G at n = 18,
and 322.5 G against 451.1 G at n = 20.

**What the residual looks like.** `D'` is 22–35% full at intake. Its leads sit mostly at the left:
60–67% of its cells are at or right of their row's lead. Its rank is the column count minus one, at
both rows and both fields. So the residual is tall and **rank-saturated**: 53–60% of its rows are
dependent, and its reduced form is an identity block plus one column. A dense schedule pays for
every cell of that block. A row-at-a-time schedule pays only for the nonzeros it meets, and on
every dependent row it pays until the row is zero.

## 6. Crossover (work item 4)

**On square products.** `blocked_dense_study gemm`, binary `efbc8a6c`, three reps, load 2.2–3.3,
with one `counts` process running on another core.
Seconds, median of three. Every rep of every setting gave the same checksum.

| n | classical | Winograd from 512 | from 1024 | from 2048 | best / classical |
|---|---|---|---|---|---|
| 512 | 0.0053 s | 0.0053 s | 0.0052 s | 0.0052 s | 1.0 (no split) |
| 1024 | 0.0411 s | 0.0407 s | **0.0385 s** | 0.0403 s | 1.07 |
| 2048 | 0.322 s | 0.291 s | **0.288 s** | 0.297 s | 1.12 |
| 4096 | 2.544 s | 2.128 s | **2.063 s** | 2.130 s | 1.23 |
| 2048, GF(32003) | 0.324 s | 0.294 s | **0.287 s** | 0.297 s | 1.13 |
| 4096, GF(32003) | 2.544 s | 2.124 s | **2.074 s** | 2.126 s | 1.23 |

The classical kernel runs at 50–54 GFLOP/s, 25–27 G multiply-adds per second, at every size and
both primes. One Winograd level pays from n = 1024 on: the measured crossover is a split at 1024,
with 512-wide classical products at the base. Splitting further, to 256-wide bases ("from 512"), is
slower at every size, and the prime makes no difference.

**On the residual.** The blocked echelon of GF(31) n = 18's `D'`, under each leaf size and
crossover: three rounds in one process (`tune`), order rotated, every output checked equal. Load
2.7–4.5.

| Leaf rows | Winograd from | Median s | Min s | Multiply-adds |
|---|---|---|---|---|
| 32 | off | 12.70 s | 12.67 s | 315,289,900,163 |
| 32 | 1024 | 11.79 s | 11.77 s | 272,829,117,696 |
| 64 | off | 12.50 s | 12.49 s | 314,870,398,160 |
| 64 | 512 | 11.93 s | 11.91 s | 241,260,191,848 |
| 64 | 1024 | 11.65 s | 11.61 s | 272,409,615,693 |
| 64 | 2048 | 12.26 s | 12.22 s | 303,601,113,112 |
| 128 | off | 12.40 s | 12.37 s | 314,034,228,542 |
| 128 | 512 | 11.79 s | 11.77 s | 240,424,022,230 |
| **128** | **1024** | **11.53 s** | **11.50 s** | 271,573,446,075 |
| 128 | 2048 | 12.09 s | 12.08 s | 302,764,943,494 |

The full grid (32 rows with 512 and 2048 too) is in `tune-efbc8a6c.jsonl`.

- **Strassen–Winograd crosses over here, and buys 7%.** From 1024 it saves 14% of the
  multiply-adds and 7.0% of the time against classical (11.53 s against 12.40 s at 128-row
  leaves). Splitting from 512 saves more multiply-adds (240 G) and less time, because a 256-wide
  base product runs below the kernel's peak. From 2048 only the largest products split.
- **The leaf hardly matters:** 1–2% between 32 and 128 rows.
- **The defaults** (`BlockedOptions::default()`) are the best cell, 128 and 1024. That is a laptop
  tuning, not a decision.

## 7. Development timings (work item 3)

`research/1193-blocked-dense/run.sh`, three reps. Each arm is its own process, and the arm order is
rotated per rep. Binary `3e1810b1`, leaf 128, Winograd from 1024. Session 15:36–16:12, 1-minute
load 2.3–9.4. Seconds, median [min] over three reps:

| Batch | lane, whole batch | `f64` sweep | blocked RREF of `D'` | lane forward on `D'` | lane back-sub on `D'` | **kernel ratio** | **matrix ratio** |
|---|---|---|---|---|---|---|---|
| GF(31), n = 18 | 21.62 [21.45] s | 10.43 [10.34] s | 11.44 [11.39] s | 12.38 [12.32] s | 1.34 [1.31] s | **1.08** | **0.99** |
| GF(32003), n = 18 | 25.12 [24.72] s | 11.01 [11.00] s | 11.43 [11.39] s | 14.66 [14.66] s | 1.38 [1.37] s | **1.28** | **1.12** |
| GF(31), n = 20 | 92.71 [92.17] s | 41.65 [41.61] s | 36.24 [36.11] s | 52.78 [52.63] s | 7.01 [7.00] s | **1.46** | **1.19** |
| GF(32003), n = 20 | 107.08 [107.00] s | 42.40 [42.26] s | 36.25 [36.21] s | 59.50 [58.61] s | 7.32 [7.29] s | **1.64** | **1.36** |

- **Arms.**
  - *Lane, whole batch:* the shipped lane kernel's forward pass, reducers first: what F4's serial
    forward pass runs on these fields with the lane enabled. It does not include F4's candidate
    back-substitution, so it is a lower bound on the shipped batch.
  - *`f64` sweep, then blocked RREF of `D'`:* this prototype, the Faugère–Lachartre order. Its
    output is the reduced form of every new row, so no back-substitution follows.
  - *Lane forward and back-substitution on `D'`:* the same residual through the shipped kernels.
- **Kernel ratio** = lane forward on `D'` / blocked RREF of `D'`, from the medians. It is the
  dense residual alone, with the lane given the easier task: a forward pass, not a reduced form.
- **Matrix ratio** = lane on the whole batch / (`f64` sweep + blocked RREF), from the medians.
- **Spread.** Every arm's median is within 2% of its minimum.

What the table shows:

1. **The blocked residual is faster than the lane on the same residual, but by 1.1–1.6×, not by an
   exponent.** The ratio grows with size, from n = 18 to n = 20.
2. **The batch gains 1.0–1.4×.** The sweep is roughly half of the blocked route. It is
   bandwidth-bound in rank-1 updates, at about 8 G multiply-adds per second.
3. **The blocked arm does not depend on the prime** (11.43 s and 11.44 s at n = 18; 36.24 s and
   36.25 s at n = 20). The lane does: GF(32003) needs the conditional subtract that GF(31)
   compiles out (`docs/research/31-bit-lane.md`), so the ratios are larger at 32003.
4. **The `f64` kernel is already at its arithmetic ceiling.** The blocked arm does 271.6 G
   multiply-adds in 11.4 s at n = 18 (23.7 G/s) and 846.2 G in 36.2 s at n = 20 (23.3 G/s). The
   classical kernel's square-product peak is 25–27 G/s (§6). No tuning of this kernel moves the
   ratio much. Only less work would.
5. **The dense schedule does 7× the lane's useful work.** The lane's forward pass on `D'` makes
   37.9 G nonzero products at n = 18 (§5), 3.1 G per second. The blocked arm makes 271.6 G
   multiply-adds, 7.2× as many, at 23.7 G per second, 7.8× the rate. The two factors nearly
   cancel.

## 8. Go / no-go

**No-go for wiring the blocked echelon into F4 as the dense-MQ fix. Go for one bench-host
confirmation of the §7 ratios**, because the instrument already exists and the laptop decides
nothing. The issue's stop condition (a residual too small a share of the work) does not trigger;
the residual is too *saturated*, not too small.

The reasons, in order of weight:

1. **The gain is 1.1–1.6× on the residual and 1.0–1.4× on the batch** (development figures, §7).
   The gap this was meant to address is 18–24× at one worker.
2. **The arithmetic is already at its ceiling.** The `f64` kernel runs the residual at 23–24 G
   multiply-adds per second against a 25–27 G/s square-product peak. A better kernel cannot lift
   the ratio much, and Strassen–Winograd at these sizes buys 7% (§6).
3. **Even perfect arithmetic would not close the gap. Less work must.** At n = 18 the shipped
   forward pass makes 93.9 G nonzero products on this one batch (§5). At this core's 27 G/s dense
   peak, that alone is 3.5 s, and grobx's *whole* solve is 2.03 s on the bench host (#1033 §3).
   The argument holds unless that host's core runs dense `f64` products more than 1.7× faster than
   this laptop's, which is not expected of a Zen 3 core against an M4 Pro one. The remaining gap is
   in how much work there is, not in how fast each product runs: the zero-row work that M35's B
   (#1080) targets, and
   grobx's probabilistic reduction (`m35-baseline.md` §6, hypothesis 2). The data here agree:
   53–60% of `D'`'s rows are dependent.

**What would change the verdict.** These are recorded here, and not filed, because none of them
closes the gap on its own:

- *A non-reduced echelon (PLE with a triangular solve).* Clearing the upper rows is 29% of the
  blocked multiply-adds at n = 18 (`clearing_products`, b3; 38% on b2). F4 needs the reduced form
  of its candidates only.
- *An integer product kernel for p ≤ 46,337.* It would have twice the lanes of `f64` on NEON and
  AVX2, at the cost of a reduction every few products at 32003.
- *A sweep blocked over reducers.* It would turn the sweep's rank-1 updates into a product. The
  sweep is half the blocked route and runs at 8 G/s.

A rough estimate, not measured: together these might reach 2–3× on the batch. That is worth
revisiting only after B has removed
the dependent rows, because the rank-saturated residual is what makes the dense schedule pay for
cells the lane never touches.

**What the blocked schedule does well**, for whoever revisits it:

- Dependent rows are cheap once the rank saturates. The bottom half is reduced by one product
  whose width is the columns the top half left free, which here is one column.
- It is independent of the prime below 2^26.
- It is a natural unit for a GPU or multicore kernel (#69): every update is a product.

## 9. What remains for the bench host

- Pinned, interleaved timings of every §7 arm on the bench host, at fat LTO with the `x86-64-v3`
  floor, under `tools/bench-job`. The laptop figures decide nothing. AVX2 doubles both the `f64`
  and the `u32` lane counts over NEON, so the arithmetic ratio should carry over. The lane
  kernel's memory behaviour and the sweep's bandwidth will not, so the ratios must be measured
  there.
- Peak RSS. `D'` alone is 1.1 GB at n = 18 and 2.3 GB at n = 20 in `f64`, against a 512 MB shipping
  live budget; the n = 20 `split` process peaked at 8.4 GB on the laptop (`/usr/bin/time -l`, with
  the lane comparison's copies resident).
- The complete-solve ratio on dense MQ n = 18 with the sparse controls of #945 (Katsura-8, Cyclic-6,
  mq-random-10) unchanged. This needs an F4 hook and is not built (§8).

## 10. Reproduce

The commands are in [`research/1193-blocked-dense/README.md`](../../research/1193-blocked-dense/README.md).
