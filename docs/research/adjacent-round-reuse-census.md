# Adjacent-round reuse of unreduced reducer rows (#1075)

**Measured at:** `9cf271a7` (§1–§5: `--features research-adjacent`, `examples/reuse_census.rs`,
binary sha256 prefix `c34be87888ab77af`), 2026-11-24; and `206d2bf8` (§6, the flat buffer: binary
sha256 prefix `7b1f65b4450abdd0`), 2026-11-27. Both on a 14-core macOS/arm64 laptop: one worker,
unpinned, one process at a time, peak RSS not recorded (macOS). §1–§5 ran with nothing else measured
on the machine; §6 ran while other agents' builds held the load average at 8–17. Evidence:
[`research/1075-adjacent-reuse/`](../../research/1075-adjacent-reuse/README.md) and
[`research/1075-flat-buffer/`](../../research/1075-flat-buffer/README.md).

**Across profiles:** §1–§5 use the default release profile. §6 uses the release profile with thin
LTO and 16 codegen units. Its ratios are within one binary, and its absolute times are not
comparable with §3's.

**Verdict (2026-11-27, §6): opt-in prototype; bench-host candidate on the hit-rich rows; not a
default.** The flat buffer, one arena of run-wide ids a batch found by lead column, makes the
hit-rich rows faster. On the five census development rows the symbolic stage falls to 0.64–0.86× and the solve
to 0.968–0.988×, and the adverse control Noon-8 no longer regresses (0.996×). By the rules fixed
before the run, Katsura-11 (0.969 [0.954, 0.974]) makes the flat buffer a candidate for a pinned
bench-host run. It is not a default. M35's symbolic-heavy rows do not gain. Grid-5×5 has **zero**
adjacent repeats under either buffer, so the buffer is pure upkeep there (solve 1.074×). Noon-9
repeats half its reducer rows but only a third of its terms, and comes out even (1.004×). A shipping
version would need a gate on the previous batch's **hit rate**. The symbolic share is the wrong
gate: grid-5×5 has the largest share and nothing to reuse.

**Earlier verdict (2026-11-24, §1–§5): defer.** Zeebra's signature engine repeats 41–67% of its
reducer rows from the batch immediately before, carrying 30–70% of all row terms. Serving those rows
from a one-batch buffer of run-wide monomial ids cuts the symbolic stage to 0.60–0.93× on eight of
nine rows. Because that stage is 1.7–26% of the solve, the solve improves by at most 2.3%. No
development row meets the pre-declared 0.98 bar, and the held-out Noon-8 row regresses (1.044×). The
buffer's upkeep, at 14–24% of the stage, costs as much as the saving there. The next step, if any,
is the issue's flat buffer, which removes per-row allocation. It is worth trying only where the
symbolic share is large (MQ10).

---

## 1. What was measured

The question is grobx's `kept` count asked of Zeebra: how often does a batch build exactly the same
row, `mult · source` unreduced, as the batch before it, and what would keeping it save? Every row is
keyed by `(source, mult)`, where the source is an input or a signature-basis element. Unlike #1031,
the buffer holds rows as built. #1031 held tail-reduced multiples, and the question there was
elimination products. Here the question is symbolic construction.

`research-adjacent` (`src/grobner/sigf4/adjacent.rs`) adds three modes to the signature engine's
symbolic stage, all from one binary:

- **off**: the shipping path, untouched.
- **count**: after each batch, the buffer keeps every row's run-wide monomial ids (#971's table)
  until the next batch. Every row is still built (a product, an additive hash and a probe per
  term), and each repeated row's fresh ids are checked against the stored ones. This arm pays the
  upkeep and the misses and saves nothing.
- **reuse**: a repeated row is served from the stored ids, with one table read per term
  (`MonomialTable::local`) and no product or probe. Misses are built as in `count`.

Both buffered paths append the same first-occurrence ids in the same order, so the matrix, and with
it the basis, is unchanged. `count` found **0 mismatches** on every row, which shows the stored ids
are the fresh ones (the source elements do not change between batches). All 243 runs agree on each
row's basis digest. A unit test (`adjacent::tests`) checks the same thing against shipping F4 on
Katsura-6 and Cyclic-5. A mutation that drops served rows from the buffer fails it.

The conventional F4 route has no run-wide monomial table, so it is not prototyped here. #1031's
ledger already counts its adjacent hits (the distance-1 bucket). On MQ10 the signature engine's
34,456 adjacent reducer hits here equal #1031's distance-1 count exactly.

Rows: the five pinned M29 rows #1031 censused, and Cyclic-7 / 2⁶⁴−353 as the upstream zero-reuse
control. Held out, named in `rows.txt` before any run: Noon-8 / 2⁶⁴−353 (a family not otherwise
studied), MQ12 / Goldilocks (a larger MQ scale) and #1030's dense `dmq-n14-m28-m31-s0`. There are
nine interleaved repetitions per arm, with the arm order rotated each repetition.

## 2. Census

From `tables.md`. The counts are the `count` arm's and are identical in every repetition.

| Row | Set | Reducer rows | Adjacent reducer hits | Hit terms / all terms | Peak buffer |
|---|---|---:|---:|---:|---:|
| MQ10 / 32003 | dev | 78,178 | 44.1% | 48.5% | 6.3 MiB |
| MQ10 / 2³¹−1 | dev | 78,178 | 44.1% | 48.5% | 6.3 MiB |
| Katsura-11 / 2³¹−1 | dev | 14,523 | 62.4% | 60.8% | 5.4 MiB |
| Eco-12 / 2⁶⁴−353 | dev | 76,936 | 67.3% | 53.1% | 7.9 MiB |
| MQ11 / Goldilocks | dev | 11,513 | 60.6% | 58.5% | 11.0 MiB |
| Cyclic-7 / 2⁶⁴−353 | control | 24,907 | 65.7% | 69.5% | 0.7 MiB |
| Noon-8 / 2⁶⁴−353 | held out | 91,323 | 40.8% | 30.1% | 3.3 MiB |
| MQ12 / Goldilocks | held out | 22,672 | 61.4% | 60.1% | 37.7 MiB |
| dense n14 m28 / 2³¹−1 | held out | 9,436 | 56.4% | 44.9% | 5.5 MiB |

- **The recurrence is real and adjacent.** On the pinned rows, grobx's `kept` share is 53–75% (from
  the issue). Zeebra's signature engine repeats 44–67% of its reducer rows from the immediately
  previous batch.
- **Cyclic-7 is not a zero-reuse control in Zeebra.** grobx reports 0 of 6,129. Zeebra's signature
  engine, over 436 small batches, repeats 65.7% of its reducer rows and 81% of its target rows
  (2,602 of 3,211) from the batch before. The engines batch differently, so the upstream control
  does not transfer.
- Target rows rarely repeat elsewhere (0–259 of up to 2,898).
- The buffer is small: 0.7–38 MiB at its peak.

## 3. Timed arms

Medians over nine repetitions. The ratios are paired per repetition against `off`, with 95% bootstrap
intervals.

| Row | Set | Solve ms | Symbolic share | Symbolic: count ÷ off | Symbolic: reuse ÷ off | Solve: reuse ÷ off |
|---|---|---:|---:|---:|---:|---:|
| MQ10 / 32003 | dev | 214 | 26.0% | 1.185 [1.172, 1.193] | 0.919 [0.908, 0.924] | 0.989 [0.984, 0.994] |
| MQ10 / 2³¹−1 | dev | 219 | 25.6% | 1.183 [1.179, 1.190] | 0.926 [0.920, 0.931] | 0.995 [0.981, 0.998] |
| Katsura-11 | dev | 422 | 8.6% | 1.217 [1.206, 1.228] | 0.704 [0.701, 0.715] | 0.980 [0.968, 0.995] |
| Eco-12 | dev | 1,477 | 8.0% | 1.243 [1.225, 1.250] | 0.831 [0.819, 0.837] | 0.992 [0.989, 0.997] |
| MQ11 | dev | 3,410 | 2.8% | 1.151 [1.139, 1.166] | 0.642 [0.629, 0.645] | 0.992 [0.991, 0.995] |
| Cyclic-7 | control | 293 | 9.8% | 1.201 [1.195, 1.203] | 0.753 [0.747, 0.768] | 0.977 [0.972, 0.987] |
| Noon-8 | held out | 128 | 37.2% | 1.177 [1.164, 1.183] | 1.103 [1.098, 1.115] | 1.044 [1.036, 1.048] |
| MQ12 | held out | 23,571 | 1.7% | 1.138 [1.132, 1.141] | 0.604 [0.602, 0.610] | 0.995 [0.993, 0.996] |
| dense n14 m28 | held out | 1,272 | 1.7% | 1.213 [1.196, 1.216] | 0.859 [0.836, 0.862] | 1.001 [0.995, 1.007] |

- **Remapping is much cheaper than building.** The gap between `count` and `reuse` is the hit rows'
  product and probe cost minus their remap cost, measured on the same rows. It is 0.26–0.53 of the
  shipping symbolic stage on every row except Noon-8 (0.07).
- **Upkeep is the binding cost.** Keeping the buffer, with one `Vec` and one map entry per row, adds
  14–24% to the stage before any hit is served. On Noon-8, with 91k short rows (about 24 terms
  each) and the fewest hit terms (30%), the upkeep exceeds the saving.
- **The solve gain is capped by the symbolic share.** That share is 1.7–9.8% of the solve on
  six of nine rows, and the best development upper bound is 0.995. Even with free upkeep, the
  `count`→`reuse` gap scaled by the symbolic share bounds the solve saving at about 0.6% (dense) to
  7% (MQ10) on this machine.

## 4. Decision

The rules were fixed in `summarize.py`'s docstring before any run was read:

- **adopt-candidate** needs reuse ÷ off with an upper bound < 0.98 on some development row. The best
  is Katsura-11 at 0.995, so this fails. Cyclic-7's 0.987 is the control, not a development row.
- **reject** needs every development row's upper bound ≥ 1.0. All five are below 1.0, so this fails
  too.
- So the verdict is **defer**. The held-out Noon-8 regression (lower bound 1.036 > 1.02) would also
  have blocked adoption.

The buffer stays behind `research-adjacent`, and no default changes. The flat buffer the issue
describes, with run-wide ids in one arena per batch and no per-row allocation or map entry, attacks
the measured upkeep. It is the only change that could move this verdict. Try it first on MQ10,
where the symbolic share (26%) leaves room for a solve gain of about 5–7%, and judge it against
Noon-8 before anything else.

## 5. Limits

- **Laptop, unpinned, one worker.** The paired intervals are tight (the arms interleave), but the
  absolute figures are not bench-host figures, and the symbolic share at 16 workers is larger
  (#888). A pinned re-run on the bench host would settle the multi-worker case.
- **Peak RSS was not recorded** (macOS). The buffer's own peak (above) is the memory a reuse arm adds
  beyond `off`, plus transient map growth.
- **Signature engine only.** Conventional F4 would need a run-wide table first.
- **Selection and reducer search are not saved.** Reducer search is already cached per run-wide id,
  and a served row still walks the closure, so new columns are searched as before.

## 6. The flat buffer (2026-11-27)

§4 named the upkeep as what blocks the map buffer: one `Vec` and one map entry for every row of every
batch. The flat buffer removes both. Two review findings shaped this run. M35's probe
(`docs/research/m35-baseline.md` §2) found two rows where the symbolic stage is a large share of the
solve, grid-5×5 (69%) and Noon-9 (32%). Applying §3's stage ratios to those shares predicted a 5–28%
and a 2–13% solve gain. The issue also asks that the flat buffer be tried first on MQ10 and judged
against Noon-8.

### 6.1 Mechanism

`AdjacentMode::Flat` (`src/grobner/sigf4/adjacent.rs`, under `research-adjacent`; no default changes):

- **One arena per batch.** Each row's run-wide ids are appended to one `Vec<u32>`, and the previous
  batch's arena is kept. The two arenas swap at the end of each batch, so steady state allocates
  nothing.
- **Lookup by lead column, not by hash.** A row `mult · source` is fixed by its lead column and its
  source, because `mult` is the column over the source's lead. So the lookup is one slot per run-wide
  id, `(batch, source, offset)`, read by array index. A reducer row's lead is the column the closure
  is processing. A target row's lead costs the one probe its build would pay anyway.
- **Validation.** A slot is used only if its batch is the previous one and its source is this row's.
  Ids are run-wide and never reused, and basis elements never change after insertion. A valid slot
  is therefore the same row, and `FlatCount` checks this directly: it builds every row and compares
  each with its stored copy. It found 0 mismatches on every row.
- **Collisions.** Targets are built before reducers, and two rows of one batch can share a lead.
  Target rows therefore write their slots after the batch, where no reducer row has taken them.
- **Budget.** The arena is capped (default 2²⁶ ids, 256 MiB). A row past the cap is built and not
  kept, and is counted in `unbuffered`. The cap was never reached on any row here.

Exactness. Every arm returns the same basis digest on every row, and the ten work counters the
summarizer checks are identical across all four arms on every row: batches, targets, reducer rows,
zero and singular rows, coefficient products, products on zero rows, matrix rows and columns, and
basis elements. The test `adjacent::tests` asserts the same for Katsura-6, Cyclic-5 and Noon-5
against shipping F4, and also checks an exhausted and an empty arena. With the slot's source check
removed, the test diverges instead of passing.

### 6.2 Counters

From `research/1075-flat-buffer/tables.md`. They are identical in every repetition. "Probes skipped"
counts the terms served from the buffer, each a product and a probe that is not paid.

| Row | Set | Reducer rows | Flat reducer hits | Probes skipped / all terms | Flat peak buffer |
|---|---|---:|---:|---:|---:|
| MQ10 / 32003 | dev | 46,443 | 51.1% | 51.8% | 12.4 MiB |
| MQ10 / 2³¹−1 | dev | 46,443 | 51.1% | 51.8% | 12.4 MiB |
| Katsura-11 / 2³¹−1 | dev | 14,174 | 63.4% | 60.7% | 16.1 MiB |
| Eco-12 / 2⁶⁴−353 | dev | 67,359 | 66.6% | 52.4% | 12.2 MiB |
| MQ11 / Goldilocks | dev | 11,513 | 60.6% | 58.4% | 32.1 MiB |
| grid-5×5 / 2³¹−1 | dev (M35) | 398,987 | **0.0%** | **0.0%** | 22.0 MiB |
| Noon-9 / 2³¹−1 | dev (M35) | 370,582 | 50.5% | 33.6% | 35.0 MiB |
| Cyclic-7 / 2⁶⁴−353 | control | 5,606 | 5.8% | 5.1% | 2.1 MiB |
| Noon-8 / 2⁶⁴−353 | adverse control | 79,917 | 47.0% | 30.2% | 4.8 MiB |
| MQ12 / Goldilocks | held out | 22,672 | 61.4% | 60.1% | 128.2 MiB |
| dense n14 m28 / 2³¹−1 | held out | 4,484 | 20.8% | 9.7% | 10.1 MiB |

- **The flat and map buffers find the same reducer hits** on every row.
- **Target rows almost never repeat.** The flat buffer serves 28 target rows in all, all on Eco-12.
- **Grid-5×5 repeats nothing.** Its 9 batches share no `(source, mult)` row with the batch before,
  under either buffer. Its 69% symbolic share is spent on rows that are built once, so no previous-batch
  buffer can serve them.
- **The engine changed under the census.** Between `9cf271a7` and `206d2bf8`, MQ10's reducer rows
  fell from 78,178 to 46,443, and Cyclic-7's from 24,907 to 5,606, with its adjacent hits falling from
  65.7% to 5.8%. The §2 census describes the older engine.
- **Memory.** The flat buffer's peak is two arenas plus the slot table, 2–128 MiB. That is about twice
  the map buffer's peak, which counts one batch.

### 6.3 Timed arms

Medians over nine repetitions. The ratios are paired per repetition against `off`, with 95% bootstrap
intervals. Unpinned laptop figures.

| Row | Set | Solve ms | Symbolic share | Symbolic: flat-count ÷ off | Symbolic: flat ÷ off | Symbolic: map reuse ÷ off | Solve: flat ÷ off | Solve: map reuse ÷ off |
|---|---|---:|---:|---:|---:|---:|---:|---:|
| MQ10 / 32003 | dev | 191 | 18.3% | 1.076 | 0.855 [0.840, 0.875] | 0.972 | **0.968 [0.950, 0.984]** | 1.007 |
| MQ10 / 2³¹−1 | dev | 197 | 17.9% | 1.079 | 0.853 [0.831, 0.860] | 0.945 | 0.988 [0.958, 0.999] | 1.004 |
| Katsura-11 | dev | 451 | 8.8% | 1.106 | 0.663 [0.608, 0.701] | 0.670 | **0.969 [0.954, 0.974]** | 0.972 |
| Eco-12 | dev | 1,467 | 8.0% | 1.264 | 0.810 [0.796, 0.820] | 0.902 | 0.981 [0.964, 0.988] | 1.002 |
| MQ11 | dev | 3,554 | 2.9% | 1.095 | 0.637 [0.615, 0.652] | 0.607 | 0.988 [0.977, 0.993] | 0.989 |
| grid-5×5 | dev (M35) | 636 | 67.3% | 1.086 | 1.102 [1.090, 1.169] | 1.216 | **1.074 [1.059, 1.167]** | 1.144 |
| Noon-9 | dev (M35) | 830 | 43.5% | 1.045 | 0.987 [0.974, 1.016] | 1.122 | 1.004 [0.985, 1.020] | 1.064 |
| Cyclic-7 | control | 61 | 11.1% | 1.107 | 1.085 [1.062, 1.092] | 1.176 | 1.014 [1.006, 1.046] | 1.024 |
| Noon-8 | adverse control | 119 | 40.0% | 1.058 | 0.989 [0.982, 0.998] | 1.182 | 0.996 [0.972, 1.007] | 1.088 |
| MQ12 | held out | 24,479 | 1.8% | 1.338 | 0.703 [0.690, 0.719] | 0.669 | 0.994 [0.986, 1.018] | 0.992 |
| dense n14 m28 | held out | 1,319 | 1.1% | 1.285 | 1.202 [1.174, 1.236] | 1.271 | 1.001 [0.993, 1.006] | 1.001 |

- **Upkeep fell.** Keeping the flat buffer (`flat-count`, which also compares every repeated row)
  adds 4.5–11% to the stage on eight of eleven rows, and 26–34% on Eco-12, MQ12 and the dense row. The map buffer's `reuse` arm, with the same hits
  served, is slower than `flat` on nine of eleven rows. The exceptions are MQ11 and MQ12, whose long
  rows the flat buffer copies between arenas, where the map buffer moves a `Vec`. On Noon-8 the upkeep
  no longer exceeds the saving: flat is 0.989× of the stage, against the map buffer's 1.182× here
  (1.103× in §3).
- **The gain is still capped by the share.** On the hit-rich census rows the stage falls to
  0.64–0.86×, and the solve to 0.968–0.988×. That is 1–3%.
- **M35's prediction does not hold.** It assumed §3's stage ratios would transfer to grid-5×5 and
  Noon-9. They do not: grid-5×5 has no hits, and Noon-9's hits carry only a third of its terms. The
  share says how much a hit could save; only the hit rate says whether there are any.

### 6.4 Decision

The rules were fixed in `research/1075-flat-buffer/summarize.py`'s docstring before any run was read.
A development row with an upper bound below 0.98, Noon-8's lower bound at most 1.02, and no held-out
row's lower bound above 1.02 make the mechanism a **bench-host candidate**. Katsura-11 at 0.974 meets
the first condition, Noon-8's lower bound is 0.972, and the held-out lower bounds are 0.986 and 0.993,
so the rule's outcome is **bench-host candidate**.

The disposition is narrower than the rule:

- **Opt-in prototype, not a default.** A development row, grid-5×5, regresses 7.4%, and the control
  regresses 1.4%. Both have at most 6% hits, so they pay the upkeep and have nothing to serve.
- **Gate on hit rate, not symbolic share.** The review note proposed gating on the previous batch's
  symbolic share. Grid-5×5 shows that this gate switches the buffer on exactly where it cannot help.
  The next prototype step is a hit-rate gate: stop keeping the buffer once a batch serves fewer than
  some fraction of its rows from it. On grid-5×5 that leaves two batches of upkeep, the first and the first with nothing to serve. `FlatCount`'s
  counters give the per-batch hit rate such a gate would read.
- **What the bench host must settle.** A pinned run of `rows.txt` at one worker, with peak RSS, and
  the 16-worker symbolic share. The 1–3% gains are near what pinning can move, and this machine was
  loaded throughout. The flat buffer's peak memory (up to 128 MiB on MQ12) must be judged against
  peak RSS, which macOS does not record.
