# Batched and block Krylov conversion over the scalar Wiedemann baseline

**Measured at:** `aa2638c2` (stage split, §2) and `2c005d63` (sequence arms, §3), 2026-11-16. The
two commits differ only in `examples/block_krylov_study.rs`; the library code that the stage split
times is identical. Both campaigns ran under `tools/benchlock.sh` (`zb-731`), START loads 1.63 and
2.13, END loads 3.59 and 2.28. The stage campaign's END reads `signalled-child(TERM)` because its
trailing sequence section was stopped by hand once a kernel defect was found (§3.1); every stage
row below completed before that and is retained. Raw output, scripts and lock lines:
[`research/block-krylov/`](../../research/block-krylov/).

Machine: Threadripper PRO 5995WX, `ZEEBRA_MACHINE=5995wx`. Stage runs are pinned to CPU 8
(`ZEEBRA_AFFINITY=8`). Sequence runs are pinned to CPUs 8-15, which are eight distinct physical
cores sharing one L3 (CCD 1). Release, fat LTO, one codegen unit, repository `x86-64-v3` flags,
`CARGO_TARGET_DIR=/buildcache/cargo-target/zeebra-731`, `RUSTC_WRAPPER=''`.

Answers #731 (parent #256). **Decision: reject a block Wiedemann prototype for now and defer batched
retries. Step 4 of the issue was not built.** The Krylov sequence is about 21% of a certified
conversion on the public shape family. Reconstruction is 71%. Even an idealized block recurrence,
with free block reconstruction on eight cores, bounds the whole conversion at 1.22x there. A
quadratic block Berlekamp–Massey grows the 71% term by roughly the block width. The follow-up that
the evidence does justify is filed as #806: subquadratic scalar reconstruction.

## 1. Method

The instrument is `examples/block_krylov_study.rs`. It is a research entry point that the library
never calls.

- **`--mode stages`** runs `fglm_to_lex_with_options` with `ConversionStrategy::Wiedemann` (or
  `classical`) and `measure_stages`. It reports the existing `FglmStageTimings` split: operator
  construction, `scalar_sequence`, `scalar_reconstruction`, `scalar_certificate`, the rest of
  `dependence` (classical fallback when it happens), and wall. Each process runs one route, so
  `process-peak-rss-bytes` is attributable. Repeats inside a process must produce the same output
  digest.
- **`--mode sequence`** re-packs `T_{x_{N-1}}` into a column-major mirror that keeps the native unit
  column shortcut. `MultiplicationOperator::apply_transpose` is crate-private. The mirror computes
  `s[b][i][k] = <(A^T)^k r_b, u_i>` exactly as the production recurrence does. Arms, at
  predeclared widths `w = 1, 2, 4, 8`:

| arm | what runs | total operator applications |
|---|---|---:|
| `scalar 1x2D` | one width-1 sweep of `2D` steps, the production recurrence | `2D` |
| `indep-serial wx2D` | `w` independent projections, one after another | `2wD` |
| `indep-batched wx2D` | the same `w` projections, one sweep over a lane-interleaved block (storage reused) | `2wD` |
| `indep-threads wx2D` | the same `w` projections, one thread each, no barrier | `2wD` |
| `block-batched wxL` | the sequence a `w x w` block recurrence needs: `L = 2 ceil(D/w)` steps of width `w`, sparse left block | `2D` |
| `block-threads wxL` | the same block sequence, its `w` columns on `w` threads, no barrier | `2D` |
| `native-apply 1x2D` | `2D` forward `MultiplicationOperator::apply` calls, a calibration arm | `2D` |

The left block holds the production moment classes (the class of 1 and each non-last variable),
padded with coordinate unit vectors. A dense random left block would cost `w^2 D` products per step.
On these operators that is more than the matvec itself, about `0.2D` products. Arm order rotates
every repetition; there are five repetitions. Every ratio is the median of per-repetition ratios
to that repetition's `scalar` arm.

**Correctness came first (Red–Green).** Four unit tests in the example pin the arms before any
timing. A width-3 transpose block must equal the forward-apply adjoint. Serial, batched (widths 1,
2, 3, 4, 8) and threaded sequences must equal `<r, A^k u>` computed independently with
`MultiplicationOperator::apply` on the cyclic, nonradical and dense families. Zero and zero-length
inputs must be exact. The block length must reduce to `2D` at width one. CI runs them through
`test = true`.

**Families** over `GF(65537)`. Each source is already a grevlex basis with pairwise coprime leading
monomials.

| family | generators | role | source SHA-256 at N = 5 |
|---|---|---|---|
| cyclic | `x_i^5 - x_{i+1}`, `x_{N-1}^5 - x_0 - 1` | the `certified-wiedemann.md` shape family | `ce36204a…` |
| dense | cyclic, with `-(c_k m_k)` for every monomial of degree 1 to 2 added to the last generator | density control, still shape (first projection certifies) | `4451edfe…` |
| powers | `x_i^5 - (i + 2)` | non-shape, radical (`x_{N-1}` has a degree-5 minimal polynomial) | `47821a0c…` |
| nonradical | `x_i^5 - x_{i+1}`, `x_{N-1}^5 - x_0^2` | non-shape, double point at the origin | `255f4b57…` |

**Larger pinned target:** cyclic at `N = 6`, `D = 15 625`, source `256c3bc7722eb671…80d506`,
output basis `4c6b58d90453aa17…fc05984`. That is five times the largest dimension in
`certified-wiedemann.md`. Cyclic at `N = 7`, `D = 78 125` (source `8bdfb811…f411`, basis
`9b0e28ba…80ec`), ran once as a scale check. Full digests are in the raw files.

## 2. Where a certified scalar conversion spends its time

Medians over in-process repetitions on one pinned core. Shares are of wall.

| family | D | reps | wall ms | operator | sequence | reconstruction | certificate | peak RSS |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| cyclic | 3 125 | 5 | 124.7 | 2.3% | 19.8% | 70.7% | 6.5% | 6.3 MB |
| cyclic | 15 625 | 5 | 2 888.9 | 0.6% | 21.2% | 71.1% | 6.8% | 14.6 MB |
| cyclic | 78 125 | 1 | 73 264.8 | 0.2% | 20.7% | 72.2% | 6.8% | 57.4 MB |
| dense | 3 125 | 5 | 307.1 | 1.9% | 37.3% | 28.8% | 29.8% | 6.6 MB |
| dense | 15 625 | 3 | 8 568.0 | 0.5% | 42.7% | 24.2% | 32.6% | 21.6 MB |

The operator for the dense family has 5.6 stored entries per row at `D = 15 625`, against 0.4 for
cyclic. Every shape conversion certified its first projection.

**Reconstruction, not the sequence, dominates the favourable family.** It covers Berlekamp–Massey
over `2D` terms, the per-series numerators, the xgcd inverse and `(numerator * inverse) mod p` for
every non-last variable. All of these are classical quadratic loops. Its share holds at 71-72% from
`D = 3 125` to `78 125`, as it should when every stage is `Theta(D^2)`. The sequence share stays
near 21%. The internal split of reconstruction is **not measured** here; that is #806's first step.
Only on the denser control does the sequence approach half the wall, and there the certificate's
`N D^2` axpys take another third.

Non-shape controls (`D = 3 125`, forced Wiedemann, three projections, then classical fallback):

| family | reps | wall ms | three failed sequences | failed reconstructions | classical remainder | peak RSS |
|---|---:|---:|---:|---:|---:|---:|
| powers | 5 | 88.9 | 58.9 ms (66%) | 0.13 ms | ~26 ms | 162.7 MB |
| nonradical | 3 | 142.6 | 58.6 ms (41%) | 53.2 ms (37%) | ~27 ms | 162.5 MB |

Classical control on cyclic `D = 3 125` (three reps): 2 087.1 ms and 162.5 MB, against 124.7 ms and
6.3 MB for the certified Wiedemann route. That 16.7x is between processes in one session, not
interleaved, and is consistent with the 23.75x on record at an older commit.

## 3. Batched projections and block sequences

### 3.1 A kernel defect, found and fixed before the numbers below

The first lane kernel took the block width at run time. At width 2 it was 3.2x a single sequence,
slower than two serial sweeps (1.9x to 2.0x), and so it measured loop overhead rather than reuse.
Those rows were discarded and are not retained. `2c005d63` gives widths 1,
2, 4 and 8 fixed-size lane arrays, with the same tests. All figures below come from that binary.

### 3.2 Results

Ratios to `scalar 1x2D`, median of five. `D = 15 625` cyclic unless stated otherwise.

| arm | GF(65537) | BabyBear | Goldilocks | dense GF(65537), D = 3 125 |
|---|---:|---:|---:|---:|
| `scalar 1x2D`, ms | 585.7 | 605.1 | 714.6 | 116.4 |
| `native-apply 1x2D` | 1.339 | 1.226 | 1.363 | 1.113 |
| `indep-serial 2/4/8` | 2.02 / 4.03 / 8.14 | 1.99 / 4.04 / 7.98 | 2.01 / 4.00 / 8.07 | 1.99 / 3.90 / 7.90 |
| `indep-batched 2/4/8` | 1.41 / 1.84 / 3.14 | 1.34 / 1.09 / 1.54 | 1.38 / 1.89 / 3.59 | 1.41 / 2.34 / 4.23 |
| `indep-threads 2/4/8` | 1.02 / 1.05 / 1.14 | 1.01 / 1.05 / 1.13 | 1.00 / 1.03 / 1.13 | 0.97 / 1.01 / 1.11 |
| `block-batched 2/4/8` | 0.715 / 0.482 / 0.432 | 0.686 / 0.284 / 0.216 | 0.686 / 0.483 / 0.483 | 0.706 / 0.625 / 0.595 |
| `block-threads 2/4/8` | 0.512 / 0.269 / 0.143 | 0.497 / 0.266 / 0.141 | 0.505 / 0.256 / 0.142 | 0.495 / 0.258 / 0.140 |

Repetition spread (max/min) is at most 1.14x on any arm, and at most 1.03x on the width-8 arms. The
`GF(65537)` cyclic run at `D = 3 125` shows the same ordering on every arm, with batching slightly
cheaper there (`indep-batched 8` 2.73, `block-batched 8` 0.392; raw file).

**Calibration.** The mirror's scalar sweep (585.7 ms) is within 5% of the production
`scalar_sequence` stage at the same `D` (613.0 ms, §2, a different process). The forward
`native-apply` is 1.1x to 1.4x slower than the mirror's transpose gather, because it allocates and
scatters. The mirror is therefore a fair, slightly favourable stand-in for the production
recurrence.

### 3.3 What is reduced and what is only concurrent

- **Batching independent projections reduces per-vector work.** One sweep reuses each operator entry
  and the unit-column copies across lanes. Per projection it costs 0.39 of a serial sweep at
  width 8 over `GF(65537)`, 0.19 over BabyBear and 0.45 over Goldilocks. This is a real single-core
  saving. It is consistent with #87, which saw BabyBear gain most and 64-bit fields least. The
  absolute factors differ from #87 because this kernel is a transpose gather with the unit shortcut
  retained, not CSR against a forward scatter.
- **Threading independent projections is only concurrent.** `indep-threads` keeps a single
  sequence's wall (1.0x to 1.14x) at `w` times the CPU. It does no less work.
- **A block recurrence shortens depth, not total work.** `block-*` performs the same `2D` operator
  applications as the scalar route, arranged as `2D/w` dependent steps. On one core,
  `block-batched` turns lane reuse into a 2.3x (`GF(65537)`) to 4.6x (BabyBear) shorter sequence
  stage at width 8. On `w` cores with one column per core and no barrier, `block-threads` is
  near-linear: 0.14 at width 8. That is the only arm here that scales with workers. It sidesteps
  #87's per-step barrier collapse because the block's columns never synchronize until the sequence
  is complete.

Memory is not a constraint. The block vectors are `2wD` elements: 10 MB at `D = 78 125`, `w = 8`,
over 8-byte elements, against a 57.4 MB scalar process peak. Sequence-mode processes peaked at
40.5 MB (`GF(65537)`) and 42.8 MB (Goldilocks) at `D = 15 625`, including every retained sequence.

## 4. Go/no-go for a block recurrence

An optimistic bound charges the block route only its sequence stage, at the measured ratio `r`. It
assumes reconstruction, certificate and operator construction cost exactly what the scalar route
spends. The full-conversion bound is `1/((1 - s) + s r)`, with `s` the measured sequence share
from §2.

| case | s | one core, `block-batched 8` | 8 cores, `block-threads 8` | ideal, r = 0 |
|---|---:|---:|---:|---:|
| cyclic, D = 15 625 | 0.212 | 1.14x | 1.22x | 1.27x |
| cyclic, D = 78 125 | 0.207 | 1.13x\* | 1.22x\* | 1.26x |
| dense, D = 15 625 | 0.427 | 1.21x\* | 1.58x\* | 1.75x |

\* `r` is taken from the nearest measured sequence row (`D = 15 625` cyclic, or `D = 3 125` dense).
These are not measured at that dimension.

That bound is not attainable, because block reconstruction is not free. A quadratic matrix
Berlekamp–Massey (Coppersmith's) on a `w x w` sequence of length `2D/w` costs on the order of
`(m + n) m n L^2 = 8 w D^2` products, against `8 D^2` in the same model at `w = 1`. Its cost
therefore grows about `w`-fold, and the shape numerators then come from a matrix generator rather
than a scalar recurrence. The break-even is when the extra reconstruction cost equals the sequence
saving:

- **cyclic, D = 15 625, 8 cores:** the saving is `613 x (1 - 0.143) = 525 ms`. That is 26% of the
  2 053 ms reconstruction. With a `w`-fold growth in even a quarter of reconstruction, the block
  route is slower than scalar.
- **dense, D = 15 625, 8 cores:** the saving is `3 659 x 0.86 = 3 147 ms`, or 152% of
  reconstruction. A block route can win here only if Berlekamp–Massey is a small part of
  reconstruction, and only with eight cores dedicated to one conversion.

Avoiding the `w`-fold growth needs polynomial-matrix (PM-basis) arithmetic, which is #689's
territory and excluded from this issue. **No-go**: the declared economic gate fails on the
favourable family before any block reconstruction is written. It is marginal at best on the denser
control. Rank-deficient blocks, block-specific certification and fallback were therefore not
prototyped. The existing independent certificate would apply unchanged to any future block output.
It costs 7% (cyclic) to 33% (dense) and is not reduced by a block sequence.

**Batched retries: defer.** On the non-shape `powers` control, three failed sequences are 66% of
the wall. One width-4 batched sweep costs about 1.57x of a single sweep at `D = 3 125`, against
3.0x serially. That would cut those 58.9 ms to about 31 ms, roughly 1.4x on the whole fallback.
On every measured shape input, though, the first projection certified. Speculatively batching
retries there costs +0.41 (width 2) to +0.84 (width 4) of a sequence: +8.8% to +18% of the wall on
cyclic `D = 15 625`. Without a cheap non-shape predictor the trade is negative on the inputs
adaptive routing is for. The nonradical control also spends 37% in three failed reconstructions.
That is a reconstruction-cost problem, and #806 owns it.

## 5. Decision, uncertainty and follow-ups

| question | verdict |
|---|---|
| block Wiedemann prototype (issue step 4) | **reject for now**: Amdahl bound of 1.22x at 8 cores on the shape family, eaten by quadratic block BM |
| batched independent projections for retries | **defer**: a 1.4x win on non-shape fallback, an 8.8-18% loss on shape inputs |
| threading independent projections | **reject**: concurrent only, no work reduction |
| scalar reconstruction (71% of conversion) | **follow up in #806**: subquadratic BM, numerators and products with the existing fast univariate arithmetic |

Revisit block Krylov only if #806 lands and reconstruction falls below the sequence. In that case
the §4 bound rises toward 1/(1 - s) with a larger `s`. The other trigger is a workload whose
sequence share is well above 43%: a denser operator, or a field like BabyBear where lanes pay most.

**Not measured, or weaker than the issue's contract:**

- Stage repetitions are within one process per family, not fresh processes. `D = 78 125` is a
  single run.
- Workers go only to 8, on one CCD, with threads equal to block width. The 1 to 64 worker sweep was
  not run because the gate failed on the ideal bound. #87 already shows the per-step-barrier form
  collapsing past 16 to 32.
- Only `GF(65537)` has a stage split. The other fields have sequence arms only.
- The block Berlekamp–Massey cost is a model, not a measurement, and reconstruction's internal
  split is unmeasured.
- The dense control is a synthetic generator added for this study. It is not a public benchmark.
- No msolve comparison; `certified-wiedemann.md` holds the last one.
- No GPU.

## Reproducing

```sh
export CARGO_TARGET_DIR=/buildcache/cargo-target/zeebra-731 RUSTC_WRAPPER=''
mkdir -p $CARGO_TARGET_DIR/tmp; export TMPDIR=$CARGO_TARGET_DIR/tmp
cargo test --example block_krylov_study
cargo build --locked --release -j24 --example block_krylov_study
tools/benchlock.sh zb-731 bash research/block-krylov/campaign-stages.sh    # §2, about 2 min
tools/benchlock.sh zb-731 bash research/block-krylov/campaign-sequence.sh  # §3, about 5 min
```

Single runs: `block_krylov_study --mode stages --family cyclic --variables 6 --repeats 5`, or
`--mode sequence --family dense --variables 5 --field babybear --widths 2,4,8`.
