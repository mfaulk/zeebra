# M33-G2: bounded wide-field one-worker experiments (#971)

**Status:** candidate 1 measured at Gate B, 2026-11-21. Candidate 2 not started (owner decision on #965).
**Plan:** [`MILESTONE-COMPETITIVE-BENCHMARKING.md`](../MILESTONE-COMPETITIVE-BENCHMARKING.md) §§9.6, 11, 12, 13.
**Attribution:** [`m33-grobx-attribution.md`](m33-grobx-attribution.md) §§5, 9–10 (Gate A record).
**Measured at:** merge base `261b17f1` against candidate `fa868367` (tag `measured/971-g2-1-table`),
both the `research-sigf4` `sig_f4_study` from `git archive`; grobx 0.155.1 `8005a2a1`
([`pins.json`](../../research/m33-baseline/pins.json)). One `tools/bench-job` dev-mode session, job
`2c4085807850`, 2026-11-21: n = 9 per arm and row, arms interleaved and rotated, fresh process per
attempt, CPU 8 of reserved CCDs 1–2, load 0.8–2.1. **Host:** Threadripper PRO 5995WX.
**Records:** [`research/m33-wide-experiments/`](../../research/m33-wide-experiments/README.md); every
figure below is in its generated [`tables.md`](../../research/m33-wide-experiments/tables.md).

## Outcome

| Candidate | Predicted (Gate A) | Measured, paired head ÷ base | Verdict |
|---|---|---|---|
| **G2-1** run-wide monomial table | Eco-12 wall −10.1%, symbolic ≤ 0.45; Katsura-11 −10.4%; MQ11 −4.6% | Eco-12 wall **0.906 [0.898, 0.915]** (−9.4%), symbolic **0.466 [0.454, 0.475]**; Katsura-11 0.904 [0.882, 0.911]; MQ11 0.945 [0.943, 0.949] | **Gate B pass criteria met; Gate A hypothesis falsified on its stage criterion** (0.466 > 0.45). Not advanced to Gate C; see §4 |
| G2-2 interreduction in column space | Eco-12 −5.2% (under 8%) | — | not started: no Gate A record; owner decision on #965 |

Exploratory, dev mode, same session: Eco-12 / 2⁶⁴−353 at 1 w goes from 1.550 [1.514, 1.571] × grobx
(base) to **1.410 [1.367, 1.427]** × grobx (candidate). This is not a competitive result (plan §11.2).

## 1. The change

`src/grobner/sigf4/table.rs` (new) and the symbolic stage of `src/grobner/sigf4/engine.rs`. The design is
Monagan & Pearce (2015) §2.1 and Faugère's F4 practice, as the Gate A record names. grobx was not read for
this change.

- **One table for the run.** Each monomial gets one id for the run. The table is open-addressed, uses
  linear probing and stays at most half full. It replaces the fresh `MonomialMap` built per batch, and also
  the separate run-wide reducer-cache map: the `(best, scanned)` cache now lives beside each id.
- **Additive hash.** The hash is `h(m) = Σ eᵢ·wᵢ mod 2⁶⁴`, with fixed odd weights. Every basis element and
  input keeps each term's hash. A product's hash is then `h(term) + h(mult)`, and a reducer row's
  multiplier hash is `h(column) − h(lead)`, so no product's exponent vector is hashed. The slot index is the
  top bits of an odd multiple of `h`. A slot also holds 32 bits of `h` as a tag, and every tag match
  compares the full exponent vector, so the table is exact.
- **Batch column in the entry.** Each entry records the batch it was last interned in and its
  first-occurrence id there. The columns of a batch therefore cost one probe per term, and handles are
  assigned in exactly the old first-occurrence order.

The rows, handles, column order and reducer choices are unchanged, so every batch matrix is the same matrix.
`test_batch_traces_are_pinned_across_families` pins every batch's rows and outcomes, the reduced basis and
the matrix shape. It covers Eco-7/8/9, Katsura-5/6/7/8, Cyclic-5, Noon-5 and Reimer-4 over GF(32003),
Goldilocks and 2⁶⁴−353, under both graded orders and the parallel cascade. The pins were taken from the
engine before the change. Net `src/` lines: about 230, with tests excluded.

## 2. Session

| Job | Attempts | ok | Clock rule, per cell (bench-job) | One session median | Per arm and cell | Foreign share, max |
|---|---:|---:|---:|---:|---:|---:|
| `2c4085807850` | 135 | 135 | 26/135, **not void** | 114/135, void | 13/135 | 1.1% |

Every flag is the 3% clock rule. As in #966 and #970, all ok attempts are used pending the owner's decision
on #965, and the thresholds are unchanged. The paired ratios are Zeebra against Zeebra and within-row, so
they do not depend on that reading.

## 3. Gate B (thresholds posted on #971 before measuring)

Medians in ms (RSS in MiB). Ratios are paired per repetition, head ÷ base, with a 95% percentile
bootstrap (20,000 draws).

| Row | wall | symbolic | elimination | interreduction | bookkeeping | peak RSS |
|---|---:|---:|---:|---:|---:|---:|
| **Eco-12 / 2⁶⁴−353** | 2,468 → 2,245, **0.906 [0.898, 0.915]** | 448 → 211, **0.466 [0.454, 0.475]** | 1.007 [0.994, 1.020] | 0.973 [0.958, 0.981] | 1.028 | 1.052 |
| Katsura-11 / 2⁶⁴−353 | 835 → 747, **0.904 [0.882, 0.911]** | 157 → 68, 0.433 | 0.991 | 0.989 | 1.050 | 0.999 |
| MQ11 / Goldilocks | 4,890 → 4,628, 0.945 [0.943, 0.949] | 442 → 188, 0.423 | 1.001 | 0.957 | 1.138 | 0.999 |
| Noon-8 / 2⁶⁴−353 | 479 → 449, 0.945 [0.931, 0.968] | 120 → 83, 0.687 | 1.200 | 1.009 | 1.017 | 1.007 |
| Cyclic-7 / 2⁶⁴−353 | 575 → 519, 0.897 [0.887, 0.931] | 117 → 62, 0.524 | 1.050 | 0.999 | 0.989 | 1.063 |

| Criterion | Threshold | Measured | Verdict |
|---|---|---|---|
| Eco-12 paired wall upper bound (Gate B) | ≤ 0.95 | 0.915 | pass |
| Precision rule, Eco-12 wall half-width | ≤ 0.025 | 0.008 | pass; no extension |
| Digests equal to base, every attempt | one per row | 1 per row (5 rows, 3 arms) | pass |
| Peak RSS (Gate B) | ≤ 1.25× | ≤ 1.063× (Cyclic-7) | pass |
| Eco-12 symbolic ratio (Gate A falsifier) | ≤ 0.45 | **0.466 [0.454, 0.475]** | **falsified** |
| Katsura-11 wall upper bound (Gate A falsifier) | ≤ 1.00 | 0.911 | holds |
| Eco-12, Katsura-11 elimination and interreduction move ≤ 3% | \|median − 1\| ≤ 0.03 | 0.973 to 1.007 | holds |

**Against the prediction.** The Eco-12 wall gain is −9.4% against −10.1% predicted. The prediction, 0.899, sits just inside the
interval's lower end. Katsura-11 gains −9.6% (−10.4% predicted) and MQ11 −5.5% (−4.6% predicted). The
symbolic stage falls to 2.37× grobx's 89 ms (#970 §2) on Eco-12, against the ≤ 2.0× the prediction
assumed. It falls to 3.4× on Katsura-11 and 4.1× on MQ11.

**Side effects.** Bookkeeping grows 3–14%, 3.4 ms on MQ11. Inserting an element now hashes its terms,
which is charged to bookkeeping rather than symbolic. That is the likely cause, but it is not separately
clocked. Noon-8's elimination grows 20%, from 23.6 to
28.4 ms. That row's wall still gains 5.5%, and the cause was not isolated. Eco-12's RSS grows 5.2% and
Cyclic-7's 6.3%, both under the 1.10× that would need an explanation.

## 4. Verdict

The Gate B pass criteria of plan §13 are met. The Gate A record also names falsifiers, and the thresholds
comment on #971 restated them: "falsified if any of these holds at Gate B". One of them holds. The symbolic
stage reached 0.466, and the hypothesis needed ≤ 0.45. On that wording the hypothesis is falsified, by 0.016
with an interval that excludes 0.45. That is despite a wall gain within 0.7 points of the prediction.

**This candidate was stopped here** rather than taken to Gate C. A corrective iteration would have had no
target except moving the stage the remaining 3.5% toward the threshold, and that is tuning toward a
threshold. It was not run.

Whether the gate's pass criteria or the hypothesis's stage falsifier governs the candidate is left to the
owner on #965. The code is the PR's head as measured. If it is allowed to proceed, the next step is
Gate C as posted: development and control rows at 1 w and 16 w, against the merge base, in one job.

## 5. What this does not show

- **No Gate C.** There are no 16 w figures, and no figures for Noon-7, Katsura-9 / 2⁶⁴−353,
  Katsura-11 / Goldilocks or Katsura-4.
- **The remaining symbolic time was not split by component** (no `research-sigf4-split` arm this session).
  The probe cost, the multiplications, the reducer search and the column sort are unattributed between them.
- **Noon-8's elimination growth is unexplained.** The matrices are identical by construction (§1).
- **Sessions:** 1 of the 8-session cap.
