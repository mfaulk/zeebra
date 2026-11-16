# The residual split: where an F4 batch's time goes, and a reordering that halves it

**Measured at:** `ca65b34d` (stock build of `examples/block_density.rs`, `split` mode), on an AMD
Ryzen Threadripper PRO 5995WX, pinned to one core (`taskset -c 8`) under `tools/benchlock.sh`, load
average 2.08 at the start of the run and 1.35 at the end, 2026-11-16. Five interleaved repetitions
per arm with rotated order; medians with [min, max]. Coefficient-product counts come from a
`--features research-work` build at `818e976b`, whose forward pass is unchanged at `ca65b34d`; its
times are not used. Raw output:
[`research/residual-split/split.md`](../../research/residual-split/split.md) and
[`research/residual-split/products.md`](../../research/residual-split/products.md).
§7 was measured at `8a68368f` (the corrected split) and `f9bf3e55` (whole runs); raw output in
[`split-corrected.md`](../../research/residual-split/split-corrected.md) and
[`whole-runs.md`](../../research/residual-split/whole-runs.md).
§8 was measured at `3077da88`; raw output in
[`parallel-fl.md`](../../research/residual-split/parallel-fl.md).

> **Correction (#816).** The "production batch" arm below finished every pivot row outside the
> reducer columns, including rows still leading at a pair lcm. F4 finishes only true candidates —
> columns no input row led with — so this arm overstated the production backward pass (417 ms
> against 6 ms on `mq-random-10`), and the 1.76–2.14× figures in §3, §4 and §6 are against that
> overstated arm. Against
> F4's own selection the Faugère–Lachartre order is **1.37×** on the `mq-random-10` batch, and
> **1.05–1.25×** on whole single-threaded runs; it loses to the shipped 16-worker forward pass.
> See §7. The tables above are kept as measured.

This is #803, the CPU phase split that `docs/research/gpu-f4.md` §5 step 1 asks for before any GPU
proposal: on the largest batch of `mq-random-14`, how much of the batch's elimination is the echelon
of the pair-row residual `D' = D - C A⁻¹ B`, the one block a device kernel could take.

---

## 1. Configuration

The batch is the pinned corpus entry `mq-random-14/grevlex/p31x64/default-64m` (75,091 × 76,194;
67,411 reducer rows; `D'` is 7,680 × 8,783 at 63.1% density, rank 3,504), with
`mq-random-10/grevlex/p31x64/default` (12,554 × 12,020; `D'` 1,468 × 934, rank 579) beside it as a
second size. Both run under `F4Options::recommended()`: `Backend::Adaptive`, the reducers-first
block, reduced batch rows.

#803 asks for the best multicore configuration. For a single batch's elimination that is one
thread: `linalg::concurrent` is not wired into F4's reduction and `reduce_batch_rows` documents that
"no parallel dispatch is enabled here", so the pinned single-core figure is the shipped
configuration, not a handicapped one.

The `mq-random-14` entry's elimination crosses its own capture budget (64,000,583 live entries
against 64,000,000) — `docs/research/f4-matrix-corpus.md` already notes that a capture does not
imply its elimination fits. `split` reports the refusal and then times every arm unbounded.

## 2. The arms

| arm | what it times |
|---|---|
| production batch | `eliminate_to(.., RowForm::Echelon, ..)` then `candidate::finish`, exactly the pair `reduction.rs` runs: the forward pass, then the backward pass over candidate rows only |
| full RREF | `eliminate_to(.., RowForm::Reduced, ..)`: the forward pass, then back-substitution over every row, reducer rows included |
| forward only | the forward pass alone |
| reference sweep | every pair row reduced against the whole reducer block, producing `D'` (`residual` in the example — reference code, not a shipped kernel) |
| echelon of `D'` | the shipped backend's echelon of `D'` alone |
| Faugère–Lachartre order | the sweep, then the echelon and the back-substitution of `D'` alone, never touching a reducer row |

The last arm is asserted, on both batches, to produce **the same candidate rows as production,
coefficient for coefficient** (579 and 3,504 rows). That is required rather than lucky: both are the
reduced row echelon form of the same row space restricted to the columns no reducer leads, which is
unique.

## 3. Results

Milliseconds, median [min, max].

| batch | production | full RREF | forward only | reference sweep | echelon of `D'` | Faugère–Lachartre order |
|---|---:|---:|---:|---:|---:|---:|
| `mq-random-10` | 1,067.2 [1,057.8, 1,079.4] | 1,392.9 [1,373.9, 1,462.8] | 650.2 [640.7, 661.3] | 370.0 [355.5, 374.7] | 74.5 [74.1, 77.8] | 499.2 [485.6, 509.8] |
| `mq-random-14` | 251,585.7 [245,754.2, 253,157.0] | 393,487.4 [391,910.9, 394,779.3] | 132,075.4 [131,998.6, 132,431.5] | 50,050.6 [49,951.2, 50,318.1] | 41,299.0 [41,222.2, 43,804.0] | 142,557.1 [142,495.1, 148,102.6] |

Derived, from the medians:

| batch | production backward pass | echelon of `D'` / production | `D'` back-substitution (FL − sweep − echelon) | `D'` work / FL order | FL order speedup |
|---|---:|---:|---:|---:|---:|
| `mq-random-10` | 417.0 ms (39%) | 7.0% | 54.7 ms | 26% | **2.14×** |
| `mq-random-14` | 119,510 ms (48%) | 16.4% | 51,207 ms | 65% | **1.76×** |

Coefficient products (research-work build): the forward pass performs 439.4 M on `mq-random-10`
(222.1 M against reducer pivots, 217.3 M against pivots discovered among the pair rows) and
89.02 G on `mq-random-14` (21.22 G and 67.80 G, 76% discovered). The full sweep of the pair rows
against the reducer block is 269.5 M and 34.94 G.

## 4. Findings

1. **The gate answers no for an echelon kernel.** The echelon of `D'` is 7.0% (`mq-random-10`) and
   16.4% (`mq-random-14`) of the production batch, well under the half that §5 step 1 of
   `gpu-f4.md` sets. A device that did that echelon in zero time would make the production batch at
   most 1.08× and 1.20× faster.
2. **A CPU reordering is worth more than that device.** Doing the batch in Faugère–Lachartre order —
   finish the whole reducer sweep first, then reduce only `D'` — gives the same candidates
   **1.76× to 2.14× faster than production** on one core, with no new hardware and no new kernel:
   the FL arm is built from the example's reference sweep plus two shipped sparse passes.
3. **Why, as far as the counts show.** Production reduces each pair row against reducer and
   discovered pivots alike in one forward pass that stops at the first unpivoted column, so a pair
   row that becomes a pivot keeps its entries in reducer-led columns to the right of its lead. Every
   later reduction by that pivot carries those entries along (67.80 G discovered-pivot products on
   `mq-random-14`, against a 34.94 G full sweep), and the backward pass then has to clear the same
   reducer columns out of the candidates (48% of the batch). The FL order clears every reducer-led
   column once, first, so all pair-against-pair work is confined to `D'`'s 8,783 free columns.
   This is consistent with the counts; it is not separately instrumented.
4. **Against the better CPU baseline, the GPU ceiling is thin.** Under FL order the `D'` work
   (echelon plus back-substitution) is 65% of the batch on `mq-random-14` and 26% on
   `mq-random-10`. A device doing all of it in zero time, with the CPU still owing the sweep, caps
   at 142,557 / 50,051 = **2.85×** on `mq-random-14` and 1.35× on `mq-random-10` — before either
   transfer of a 7,680 × 8,783 dense block. §5 step 3's ≤ 0.5× threshold is measured against the
   best CPU time, which is now the FL order, not production.
5. **Full RREF is the slowest route** at 1.31× and 1.56× production. It is not what F4 runs (the
   candidate-only backward pass replaced it), but it is what `eliminate_to(.., RowForm::Reduced, ..)`
   still does, and an earlier draft of this measurement mistook it for the shipped batch.

## 5. What this does not establish

- **Memory.** The FL arm runs unbounded and its peak live entries were not measured. `D'` alone is
  about 42.6 M entries on `mq-random-14`, and production already refuses that batch at 64 M. An FL
  route in F4 needs the live-entry and live-byte budgets (#490, #659) and a measured peak.
- **The sweep is reference code.** It is a dense accumulator per pair row, not a tuned kernel, so the
  FL figures are an upper bound on what the reordering costs.
- **Two batches.** Both are random MQ over a 31-bit prime. Whether the order wins on the rest of the
  corpus — structured systems, GF(2) where the packed route already runs, small batches where the
  sweep's per-row setup dominates — is not measured here.
- **Whole runs.** A faster batch is not yet a faster F4 run; the batch share of a run is #269's
  question and changes with the instance.

## 6. Position

**#803's GPU gate: no** for a dense echelon kernel on the production pipeline, and a ceiling of
2.85× before transfers for a device RREF of `D'` against the FL-order CPU baseline on
`mq-random-14`, falling to 1.35× one rung down. `gpu-f4.md`'s "defer" stands. The actionable
result is on the CPU: adopt the Faugère–Lachartre order for the batch reduction, budgeted and
measured across the corpus and on whole runs: #816. The existing note in
`docs/research/elimination-kernels.md` that revisiting Faugère–Lachartre "requires a measured
distinction" is answered by §3: the distinction is not the arrangement (production already puts
reducers first) but the order of the passes.

---

## 7. Correction, and the order as a shipped F4 route (#816)

### 7.1 What the production arm got wrong

`split`'s production arm selected the columns no reducer leads and finished every pivot row there
(`candidate::finish`). F4 selects the columns no *input* row leads: neither a reducer's lead nor a
pair's lcm (`src/grobner/f4/reduction.rs`, `candidate_columns`). After the forward pass, many pair
rows still lead at their lcm; F4 extracts no candidate from them and does not finish them, and the
harness did. On `mq-random-10` the harness finished 579 rows; F4 finishes 8.

`8a68368f` makes the harness select as F4 does, and compares only true candidates. Same batch, one
pinned core, five interleaved repetitions, medians [min, max] in ms:

| batch | production | full RREF | forward only | reference sweep | echelon of `D'` | Faugère–Lachartre order |
|---|---:|---:|---:|---:|---:|---:|
| `mq-random-10` | 752.1 [729.9, 756.9] | 1,481.6 [1,459.2, 1,499.7] | 746.1 [737.7, 751.2] | 393.0 [384.0, 396.0] | 87.1 [84.6, 87.5] | 548.3 [538.3, 549.5] |

The production backward pass is 6 ms, not 417 ms; the FL order is **1.37×** production, not 2.14×.
The load was 10.2 at the end of this run against 1.35 for §3, so absolute times are about 7% above
§3's; the ratio is what to read. `mq-random-14` was not re-measured.

### 7.2 Whole runs

`F4Options::batch_order = BatchOrder::FaugereLachartre` (`f9bf3e55`) ships the order: a dense-row
sweep kernel (`linalg::echelon::sweep_rows_against_pivots`), then the configured backend's echelon
of `D'` renumbered onto its own columns, then `candidate::finish` over `D'` alone, under the live
entry budget with the reducer block counted as resident. Whole F4 calls, `F4Options::default()`
otherwise, grevlex, cores 32–47 under `tools/benchlock.sh`, five interleaved rotated repetitions,
medians [min, max] in ms. Every run of an instance produced the same basis digest.

| instance | forward order, serial | FL order, serial | forward order, 16 workers (shipped) | FL / forward, serial |
|---|---:|---:|---:|---:|
| `mq-random-10`, p = 2³¹−1 | 1,138.6 [1,127.9, 1,221.4] | 991.9 [986.5, 1,086.3] | 291.2 [288.3, 292.8] | 1.15× |
| `katsura-11`, p = 2³¹−1 | 10,061.9 [9,980.2, 10,772.0] | 8,023.7 [7,985.1, 8,645.1] | 1,737.5 [1,724.0, 1,779.8] | 1.25× |
| `cyclic-7`, p = 32003 | 284.8 [276.5, 296.1] | 270.4 [264.8, 289.9] | 139.5 [138.5, 141.7] | 1.05× |

Peak live entries (`max_live_nonzeros`), deterministic: FL is 16% below the serial forward order on
`mq-random-10` (978,506 against 1,164,559) and 14% and 25% above it on `katsura-11` (3,680,865
against 3,225,484) and `cyclic-7` (267,878 against 213,585). Both stay below the 16-worker
route's peaks, which reserve worker space.

Load rose from 4.9 to 13.3 across the run; the serial pairs were interleaved, so their ratios are
the figures to trust.

### 7.3 Position

- **The order is a real single-threaded gain, 1.05–1.25× on whole runs**, smaller than §4 claimed
  because the backward pass it was to remove was mostly the harness's.
- **It is not the default.** The FL route is serial in both its sweep and its `D'` elimination, so
  it ignores `ParallelForward`, and the shipped 16-worker forward order is 1.9–4.6× faster than it.
  It stays selectable as `BatchOrder::FaugereLachartre`.
- **What would change that** is a parallel FL route: the sweep is row-independent and
  deterministic, and `D'` could take the concurrent kernel. Whether it beats the 16-worker forward
  order is unmeasured; it is #828.
- §4 finding 4's GPU ceiling was computed against the overstated production arm and should be
  re-derived before it is cited.

## 8. The order on workers, against the 16-worker forward pass (#828)

`3077da88` puts both passes of the FL route on workers. The sweep is a second entry on
`linalg::concurrent::Dispatch` (`concurrent::sweep`): lower rows are claimed in chunks and swept
in place against the read-only reducer block, with one full-width row reserved per active worker.
`D'` goes to the existing concurrent kernel (`concurrent::reduce`, `split = 0`). Both passes answer
to the forward order's gate (`f4::parallel::gate`, the same `ParallelForward` setting, the
`Adaptive` backend and a field with a concurrent handle) and fall back to their serial kernels when
the workers' reservation does not fit. A swept row's value does not depend on the thread count, and
every arm below produced one basis digest per instance.

Whole F4 calls, `F4Options::default()` but for the two named fields, grevlex, release build of
`3077da88` (on `da5b658c`), cores 32–47 under `tools/benchlock.sh`, five interleaved repetitions
with arm order rotated each repetition, load 3.4 at the start and 3.0 at the end. Medians [min,
max] in ms; `auto:W` is `ParallelForward::Auto { max_workers: W }`. Raw output:
[`parallel-fl.md`](../../research/residual-split/parallel-fl.md). One arm is one process:

```bash
tools/benchlock.sh <tag> taskset -c 32-47 target/release/examples/batch_order_study \
  --problem=katsura-11 --modulus=32003 --arm=fl/auto:16   # ORDER/{serial|auto:W|forced:W}
```

### 8.1 Against the shipped 16-worker forward order

| instance | forward, `auto:16` (shipped) | FL, `auto:16` | forward / FL | peak live entries, forward → FL | peak RSS, forward → FL |
|---|---:|---:|---:|---:|---:|
| `katsura-11`, p = 32003 | 1,721.2 [1,708.4, 1,737.4] | 1,357.8 [1,347.2, 1,376.8] | **1.27×** | 4.42 M → 4.26 M | 133 → 140 MiB |
| `katsura-11`, p = 2³¹−1 | 1,541.9 [1,520.0, 1,565.6] | 1,258.3 [1,237.4, 1,290.1] | **1.23×** | 4.43 M → 4.26 M | 143 → 153 MiB |
| `mq-random-10`, p = 32003 | 302.4 [296.6, 306.2] | 261.5 [257.5, 266.6] | 1.16× | 1.79 M → 1.22 M | 41 → 41 MiB |
| `mq-random-10`, p = 2³¹−1 | 277.1 [274.2, 282.2] | 250.4 [245.1, 253.3] | 1.11× | 1.79 M → 1.22 M | 42 → 42 MiB |
| `cyclic-8`, p = 32003 (held out) | 1,895.4 [1,884.4, 1,898.6] | 1,731.9 [1,723.9, 1,758.0] | 1.09× | 4.70 M → 5.27 M | 157 → 173 MiB |
| `cyclic-7`, p = 32003 | 135.1 [134.1, 136.9] | 139.1 [138.1, 144.3] | 0.97× | 307 K → 342 K | 18.8 → 19.8 MiB |
| `cyclic-7`, p = 2³¹−1 | 129.3 [127.7, 131.1] | 137.5 [135.7, 138.6] | **0.94×** | 306 K → 343 K | 21.3 → 22.2 MiB |
MQ14_ROW

Peak live entries are `max_live_nonzeros`, which under workers is the conservative reservation
(published entries plus full-width rows per active worker), so it varies slightly run to run; the
range is under 1% here. No arm fell back or refused.

### 8.2 The worker factorial

Same runs. Forward / FL ratio at each worker count, medians:

| instance | serial | `auto:4` | `auto:8` | `auto:16` |
|---|---:|---:|---:|---:|
| `katsura-11`, p = 32003 | 1.29× | 1.23× | 1.25× | 1.27× |
| `katsura-11`, p = 2³¹−1 | 1.26× | 1.23× | 1.22× | 1.23× |
| `mq-random-10`, p = 32003 | 1.16× | 1.13× | 1.16× | 1.16× |
| `mq-random-10`, p = 2³¹−1 | 1.12× | 1.10× | 1.13× | 1.11× |
| `cyclic-7`, p = 32003 | 1.03× | 0.99× | 0.98× | 0.97× |
| `cyclic-7`, p = 2³¹−1 | 1.01× | 0.98× | 0.97× | 0.94× |

The serial gain carries over to workers nearly unchanged on the two cases where it was large: the
FL route scales with workers as well as the forward route does. On `cyclic-7`, whose 26 batches are
small, the serial gain is within 3% and the parallel route is a little slower: each FL batch makes
two dispatches, sweep and `D'`, where the forward route makes one.

### 8.3 Against the M29-B stop/go gate

`docs/MILESTONE-COMPETITIVE-F4.md` §6:

- **≥15% complete-F4 improvement on one substantial case against the shipping parallel
  baseline — met.** `katsura-11` is 1.23–1.27× at both moduli, with non-overlapping ranges.
- **Held-out evidence that the gain is not specific to one MQ matrix — met in direction.**
  `katsura-11` is not MQ; `cyclic-8` gains 1.09× and `mq-random-10` 1.11–1.16×.
- **No material regression on small controls — not met.** `cyclic-7` is 3–6% slower at 16 workers,
  beyond the run-to-run spread at p = 2³¹−1. Smaller controls are untouched in practice, since the
  `Auto` gate leaves their batches serial, where FL is at least as fast (§7.2).
- **No new budget refusals or unsupported outcomes — met on these runs.** Every digest matched and
  no batch fell back; the fallback path is tested (`parallel_fl_falls_back_under_a_tight_budget`).
- **Peak RSS ≤ 1.25× baseline — met.** At most 1.10× (`cyclic-8`).
- **Not covered:** 64-bit fields, and Eco-12, which is not in the corpus `batch_order_study`
  reads.

### 8.4 Position

- **The parallel FL order is the fastest route measured on the two substantial cases**,
  1.23–1.27× over the shipped 16-worker forward order on `katsura-11` and 1.11–1.16× on
  `mq-random-10`, with lower peak live entries on both.
- **It stays opt-in** (`BatchOrder::FaugereLachartre`): the gate's small-control clause fails on
  `cyclic-7`, and 64-bit fields are unmeasured. Making it the default is a follow-up that should
  first remove the per-batch double dispatch (one gate decision and one thread scope for both
  passes, or the serial sweep below a size threshold) and re-measure `cyclic-7` and the 64-bit
  fields.
