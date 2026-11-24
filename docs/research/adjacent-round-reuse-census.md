# Adjacent-round reuse of unreduced reducer rows (#1075)

**Measured at:** `9cf271a7` (`--features research-adjacent`, `examples/reuse_census.rs`, binary
sha256 prefix `c34be87888ab77af`), 2026-11-24, on a 14-core macOS/arm64 laptop: one worker,
unpinned, one process at a time, nothing else measured on the machine, peak RSS not recorded
(macOS). Evidence: [`research/1075-adjacent-reuse/`](../../research/1075-adjacent-reuse/README.md).

**Verdict: defer.** Zeebra's signature engine repeats 41–67% of its reducer rows from the batch
immediately before, carrying 30–70% of all row terms. Serving those rows from a one-batch buffer of
run-wide monomial ids cuts the symbolic stage to 0.60–0.93× on eight of nine rows. Because that stage
is 1.7–26% of the solve, the solve improves by at most 2.3%. No development row meets the
pre-declared 0.98 bar, and the held-out Noon-8 row regresses (1.044×). The buffer's upkeep, at
14–24% of the stage, costs as much as the saving there. The next step, if any, is the issue's flat
buffer, which removes per-row allocation. It is worth trying only where the symbolic share is large
(MQ10).

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
