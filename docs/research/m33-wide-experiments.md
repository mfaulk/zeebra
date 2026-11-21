# M33-G2: bounded wide-field one-worker experiments (#971)

**Status:** candidate 1 measured at Gate B and Gate C, 2026-11-21; Gate C fails on one cell (§6).
Candidate 1 merged as `2f8253f3` (owner, #965), with MQ11 at 1 w reported as no improvement. Candidate 2
measured at Gate B (Gate A stage criterion missed; the owner ruled the Gate B pass governs) and at Gate C,
where every cell passes (§7.1).
**Plan:** [`MILESTONE-COMPETITIVE-BENCHMARKING.md`](../MILESTONE-COMPETITIVE-BENCHMARKING.md) §§9.6, 11, 12, 13.
**Attribution:** [`m33-grobx-attribution.md`](m33-grobx-attribution.md) §§5, 9–10 (Gate A record).
**Measured at:** merge base `261b17f1` against candidate `fa868367` (tag `measured/971-g2-1-table`),
both the `research-sigf4` `sig_f4_study` from `git archive`; grobx 0.155.1 `8005a2a1`
([`pins.json`](../../research/m33-baseline/pins.json)). One `tools/bench-job` dev-mode session, job
`2c4085807850`, 2026-11-21: n = 9 per arm and row, arms interleaved and rotated, fresh process per
attempt, CPU 8 of reserved CCDs 1–2, load 0.8–2.1. **Gate C** (§6): merge base `93f2853a` against
candidate `32864419` (tag `measured/971-g2-1-gatec`), the same build recipe, jobs `e75ea88fcbc2` (main),
`1f41a1d157a3` (warm-call) and `478f0042939d` (loop-aligned placement control), 2026-11-21.
**G2-2 Gate B** (§7): #994's head
`32864419` against candidate `cba1ee89` (tag `measured/971-g2-2-columns`), job `b74ceab30185`.
**G2-2 Gate C** (§7.1): main `2f8253f3` against
candidate `6f5466b0` (tag `measured/971-g2-2-gatec`), jobs `d92fee9ebd98` (main) and `e95341beca7f`
(warm-call). **Host:** Threadripper PRO 5995WX.
**Records:** [`research/m33-wide-experiments/`](../../research/m33-wide-experiments/README.md); every
figure below is in its generated [`tables.md`](../../research/m33-wide-experiments/tables.md).

## Outcome

| Candidate | Predicted (Gate A) | Measured, paired head ÷ base | Verdict |
|---|---|---|---|
| **G2-1** run-wide monomial table | Eco-12 wall −10.1%, symbolic ≤ 0.45; Katsura-11 −10.4%; MQ11 −4.6% | Eco-12 wall **0.906 [0.898, 0.915]** (−9.4%), symbolic **0.466 [0.454, 0.475]**; Katsura-11 0.904 [0.882, 0.911]; MQ11 0.945 [0.943, 0.949] | Gate B pass criteria met; Gate A stage criterion missed (0.466 > 0.45). The owner ruled on #965 that the Gate B pass governs. **Gate C: 17 of 18 cells pass; MQ11 / Goldilocks at 1 w fails** (0.993 [0.977, 1.007] against ≤ 0.97). See §6 |
| G2-2 interreduction in column space | Katsura-11 −14.7% (−110 ms) against #994; interreduction ratio ≤ 0.30 | Katsura-11 wall **0.890 [0.873, 0.911]** (−82 ms); interreduction **0.368 [0.360, 0.407]**; Eco-12 0.888 [0.856, 0.905] | Gate B pass criteria met; Gate A stage criterion missed (0.368 > 0.30); the owner ruled the Gate B pass governs. **Gate C: 18 of 18 cells pass**; Katsura-11 0.880 [0.874, 0.891] at 1 w. See §7.1 |

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
28.4 ms. That row's wall still gains 5.5%; §6.2 attributes the growth. Eco-12's RSS grows 5.2% and
Cyclic-7's 6.3%, both under the 1.10× that would need an explanation.

## 4. Verdict

The Gate B pass criteria of plan §13 are met. The Gate A record also names falsifiers, and the thresholds
comment on #971 restated them: "falsified if any of these holds at Gate B". One of them holds. The symbolic
stage reached 0.466, and the hypothesis needed ≤ 0.45. On that wording the hypothesis is falsified, by 0.016
with an interval that excludes 0.45. That is despite a wall gain within 0.7 points of the prediction.

No corrective iteration was run at Gate B: it would have had no target except moving the stage the
remaining 3.5% toward the threshold, and that is tuning toward a threshold.

The owner ruled on #965 (comment 7063833537) that the Gate B pass governs, so the candidate went on to
Gate C (§6), with two added conditions: explain Noon-8's elimination growth and clock the bookkeeping
growth.

## 5. What this does not show

- **The remaining symbolic time was not split by component** (no `research-sigf4-split` arm this session).
  The probe cost, the multiplications, the reducer search and the column sort are unattributed between them.
- **Noon-8's elimination growth is attributed but not removed** (§6.2): the table is not freed per
  batch, and the fix (or not) is a separate change.
- **The MQ11 shortfall is attributed but not fixed** (§6.3): the shipped binary fails, and the
  loop-aligned control is a diagnostic build, not a candidate.
- **Sessions:** 4 of the 8-session cap (Gate B, Gate C main, warm-call, placement control).

## 6. Gate C (thresholds posted on #971 before measuring)

The owner ruled on #965 that the Gate B pass governs, so Gate C ran as posted: development and control rows
at 1 w and 16 w, against the merge base, after rebasing onto `origin/main` (`93f2853a`). The per-arm clock
rule (#965) groups by row, worker count and arm; no session is void (52/360, 52/372 and 6/81 attempts
contaminated). The figures below use every ok attempt (n = 9, or n = 31 for warm-call cells). The
clean-only reading is in `tables.md` §5 beside them: it agrees on every verdict it has the pairs for,
and many cells have fewer than 9 clean pairs. The four cells under 300 ms process wall (Noon-7 and
Katsura-9 / 2⁶⁴−353, at both worker counts) and Katsura-4 are read by the warm-call median (plan §11.6).

| Row | 1 w | 16 w |
|---|---:|---:|
| Eco-12 / 2⁶⁴−353 (dev, ≤ 0.97 at 1 w) | 0.896 [0.868, 0.923] | 0.893 [0.875, 0.904] |
| Katsura-11 / 2⁶⁴−353 (dev) | 0.906 [0.881, 0.932] | 0.849 [0.845, 0.859] |
| MQ11 / Goldilocks (dev) | **0.993 [0.977, 1.007] FAIL** | 0.899 [0.895, 0.916] |
| Noon-8 / 2⁶⁴−353 | 0.959 [0.916, 0.976] | 0.926 [0.899, 0.935] |
| Cyclic-7 / 2⁶⁴−353 | 0.904 [0.887, 0.919] | 0.899 [0.892, 0.902] |
| Katsura-11 / Goldilocks | 0.933 [0.914, 0.940] | 0.847 [0.831, 0.865] |
| Noon-7 / 2⁶⁴−353 (warm) | 0.897 [0.889, 0.917] | 0.908 [0.900, 0.915] |
| Katsura-9 / 2⁶⁴−353 (warm) | 0.839 [0.834, 0.849] | 0.821 [0.814, 0.825] |
| Katsura-4 / 2⁶⁴−353 (warm) | 0.904 [0.898, 0.904] | 0.983 [0.974, 1.008] |

Peak RSS is ≤ 1.07× everywhere (Cyclic-7 at 16 w is the largest; under the 1.10× that needs an
explanation). Digests: one `m33-basis-v1` digest per row across every arm, worker count and job.

### 6.1 Verdict

17 of 18 cells pass. **MQ11 / Goldilocks at 1 w fails**: its upper bound 1.007 is above 0.97, where Gate B
measured 0.945 [0.943, 0.949] on the pre-rebase pair. The verdict on the shipped binary stands as a fail.
No corrective iteration on the code was run; §6.3 is a diagnostic control and was not adopted.

**Owner decision (#965, comment 7065780153):** #994 is adopted and merged as `2f8253f3`. MQ11 / Goldilocks at
1 w is reported as no improvement, not as a gain.

### 6.2 Noon-8's elimination growth (the owner's condition)

It reproduces: at 1 w, elimination is 24.0 → 29.0 ms (1.196 [1.186, 1.216]) while the wall still gains 4%.
The matrices are identical by construction, so the extra time is not arithmetic. `noon8-probe.sh` (output in
`noon8-probe.txt`, CPU 41, untimed) attributes it to **page faults moving into elimination**:

- The base frees each batch's `MonomialMap` when symbolic preprocessing ends, and elimination's
  allocations reuse those already-faulted pages. The candidate's table persists across batches, so
  elimination's allocations fault fresh pages. Faults in `_int_malloc` go from 3,207 to 4,459, while the
  process total is flat (26,389 → 25,636).
- With `GLIBC_TUNABLES=glibc.malloc.hugetlb=1`, which removes most first-touch faults, the gap closes:
  elimination medians are 18.8 ms (base) and 19.7 ms (candidate), against 24.7 and 28.0 ms under the
  default allocator in the same probe.

So the growth is allocator layout, not a change to elimination. The row's wall gains despite it.

### 6.3 The MQ11 shortfall

On MQ11 at 1 w the candidate's elimination grew 5.9% (3,549 → 3,735 ms) with the same matrices.
`perf stat` on the Gate B head `fa868367` and the Gate C head `32864419` shows identical user-space
instruction counts (7.383 × 10¹⁰), the same branch and L1 misses, and about 5% more cycles in the Gate C
build. The hot loop is `Engine::eliminate`, which neither commit changed. That points to code placement:
the rebase and the element-hashing clock moved the loop.

Placement control (job `478f0042939d`): both arms rebuilt with `-C llvm-args=-align-loops=64`, so every
loop is aligned the same way, development rows at 1 w, n = 9. MQ11's elimination ratio becomes
1.000 [0.995, 1.054] and its wall 0.948 [0.942, 0.998], the Gate B median again. The interval is too wide
to clear 0.97, so even that build fails the precision rule. Eco-12 is 0.910 and Katsura-11 0.894 under
the control.

The shortfall therefore is placement in a loop outside the change, and the aligned build recovers the
median but not a passing interval. Adopting a loop-alignment flag to clear one threshold would be tuning
toward it, and it was not adopted.

### 6.4 Bookkeeping

Bookkeeping grows by 0–13%. Hashing new elements' terms is now clocked separately (`element_hashing`,
inside bookkeeping). It accounts for most of the growth where the growth is real:

| Row, 1 w | Base | Candidate | Ratio | `element_hashing` |
|---|---:|---:|---:|---:|
| MQ11 / Goldilocks | 26.5 ms | 30.0 ms | 1.132 [1.089, 1.159] | 3.1 ms |
| Katsura-11 / Goldilocks | 16.1 | 17.1 | 1.085 [1.046, 1.099] | 0.8 |
| Katsura-11 / 2⁶⁴−353 | 15.7 | 16.7 | 1.053 [1.025, 1.102] | 0.7 |
| Noon-8 / 2⁶⁴−353 | 84.5 | 87.1 | 1.028 [1.014, 1.034] | 0.7 |
| Eco-12 / 2⁶⁴−353 | 235.5 | 243.3 | 1.007 [0.970, 1.053] | 2.8 |

Noon-8's remaining 1.9 ms is not isolated.

## 7. G2-2: interreduction in the engine's column space (Gate B)

**The change.** The final interreduction no longer converts the signature basis to `MultivariatePolynomial`s
before reducing (`src/grobner/sigf4/interreduce.rs`):

- the minimal selection runs on the engine's own leads;
- the closure interns through the run-wide monomial table and reuses its reducer cache;
- a tails-only sweep runs in the engine's `Workspace`;
- only the reduced basis is materialized.

The F4 interreduction limits still apply. A refusal falls back to the old materialize-and-divide route, and a
test forces it. The reduced Gröbner basis is unique, so the result is bit-identical. The pinned batch traces
and `agrees_with_f4` checks over four families show it.

**Gate B, job `b74ceab30185`,** paired G2-2 ÷ #994's head, dev mode, n = 9, 1 w. The per-arm clock rule left
13/135 attempts contaminated, so the session is not void.

| Row | Wall | Interreduction stage (ms, base → head) | Peak RSS |
|---|---:|---:|---:|
| Katsura-11 / 2⁶⁴−353 (target) | **0.890 [0.873, 0.911]** | 116.7 → 43.8, **0.368 [0.360, 0.407]** | 0.835 |
| Eco-12 / 2⁶⁴−353 (control) | 0.888 [0.856, 0.905] | 275.2 → 95.6, 0.353 | 0.798 |
| MQ11 / Goldilocks | 0.893 [0.883, 0.904] | 536.1 → 290.4, 0.545 | 0.809 |
| Noon-8 / 2⁶⁴−353 | 0.765 [0.747, 0.779] | 128.3 → 47.1, 0.366 | 0.817 |
| Cyclic-7 / 2⁶⁴−353 | 0.891 [0.852, 0.903] | — | 0.575 |

The pass criteria hold:

- Katsura-11's wall upper bound is 0.911 (≤ 0.95);
- its half-width is 0.019 (≤ 0.025);
- there is one digest per row;
- RSS falls on every row.

The Eco-12 control is 0.888 (falsifier at > 1.00). Symbolic and elimination move ≤ 2.5% on both rows.

**Verdict: falsified.** The Gate A record names this falsifier: Katsura-11's interreduction-stage ratio
must be ≤ 0.30, and it is 0.368 with an interval above 0.30.

The wall gain is −82 ms against the predicted −110 ms. An untimed flat profile (CPU 41) puts most of the
remaining ~44 ms in materializing the reduced basis. `MultivariatePolynomial::new` re-sorts the terms
(the quicksort and merge over `(&Monomial, &coefficient)` pairs, plus `memcmp`), about 25 ms. The sweep
itself is a small part.

Per the stop rule, no corrective iteration was run. Materializing in the order the engine already holds
would be one, and it would aim at the stage threshold. The owner ruled on #965 (comment 7065780153) that
the Gate B pass governs, as for G2-1.

### 7.1 Gate C

Gate C ran against main `2f8253f3`, which contains #994. It used G2-1's rows, worker counts and thresholds,
and bench-job's per-arm clock rule (46/360 and 38/372 attempts contaminated; no session is void). The
figures below are paired head ÷ base on every ok attempt; the clean-only reading is in `tables.md` §7 and
agrees on every verdict it has the pairs for.

| Row | 1 w | 16 w |
|---|---:|---:|
| Eco-12 / 2⁶⁴−353 (dev, ≤ 0.97 at 1 w) | 0.894 [0.878, 0.907] | 0.864 [0.841, 0.866] |
| Katsura-11 / 2⁶⁴−353 (dev, target) | **0.880 [0.874, 0.891]** | 0.828 [0.817, 0.830] |
| MQ11 / Goldilocks (dev) | 0.943 [0.937, 0.960] | 0.855 [0.843, 0.864] |
| Noon-8 / 2⁶⁴−353 | 0.768 [0.750, 0.785] | 0.783 [0.772, 0.799] |
| Cyclic-7 / 2⁶⁴−353 | 0.911 [0.854, 0.938] | 0.897 [0.892, 0.904] |
| Katsura-11 / Goldilocks | 0.891 [0.853, 0.902] | 0.828 [0.821, 0.842] |
| Noon-7 / 2⁶⁴−353 (warm) | 0.666 [0.664, 0.671] | 0.715 [0.711, 0.721] |
| Katsura-9 / 2⁶⁴−353 (warm) | 0.781 [0.775, 0.785] | 0.717 [0.713, 0.723] |
| Katsura-4 / 2⁶⁴−353 (warm) | 0.826 [0.820, 0.831] | 0.980 [0.952, 1.018] |

**Verdict: 18 of 18 cells pass.** Peak RSS is ≤ 1.00× everywhere (0.53–0.91× where it changes), and there
is one `m33-basis-v1` digest per row. Two cells miss the precision rule but still pass: Cyclic-7 at 1 w and
Katsura-4 at 16 w.

**Exploratory, dev mode, same session (plan §11.2, not a competitive result):** Eco-12 / 2⁶⁴−353 at 1 w is
1.414 [1.358, 1.452] × grobx 0.155.1 on main and **1.264 [1.218, 1.292]** × with G2-2. Katsura-11 is 1.349
on main and 1.177 with G2-2. Confirmation is #975's.

**Sessions:** G2-2 used 3 of its 8 (Gate B, Gate C main, warm-call).
