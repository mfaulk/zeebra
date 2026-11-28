# #1123: M35 WP E, lane dispatch

**Measured at:** `135a76ed` (tag `measured/1123-lane-dispatch`). It is main `f77dc563` plus:
- `F4Options::small_prime_lane`, which now reaches Adaptive's signature route;
- `lane_min_entries`, the per-batch threshold, on `F4Options` and `SigF4Options`;
- `SigF4Statistics::lane_batches`;
- `m34_matrix --lane16 --lane-min-entries` and GF(31) / GF(7681) instantiations;
- GF(7681) rows from `sig_f4_study --generate`.

**Plan:** [`MILESTONE-FINITE-FIELD-COMPETITIVENESS.md`](../../docs/MILESTONE-FINITE-FIELD-COMPETITIVENESS.md) §7.5 and §9.5, Amendment 1. The kernel is #945's (`research/945-lane-kernel/`).

## The rule
A batch uses the lane only when its targets and reducers together hold at least `lane_min_entries` entries. The count is taken from the sparse rows before any row is converted, so the rule's own cost is one pass over row lengths. The threshold binds both lanes; a field has at most one.

## Development sweep (dev; decides nothing)
`sweep.py inputs|manifest|extract|table` writes, extracts and tabulates it. Bench-job `e4f4f895fe63`:
- 198 of 198 cells; digests agree on every row;
- shipping Adaptive at one worker, medians of 3, CCDs 1–2 reserved.

An earlier job, `82052fd245b2`, failed every cell on the input format (a missing `normalized_input_digest`) before any solve; it is discarded. Ratios are to the field route.

| Row | field (s) | lane forced | ≥ 1 k | ≥ 10 k | ≥ 100 k | ≥ 1 M |
|---|---:|---:|---:|---:|---:|---:|
| mq-dense-15-s15 @ GF(31) | 3.692 | 0.153 | 0.154 | 0.156 | 0.158 | 0.247 |
| mq-dense-15-s15 @ GF(32003) | 4.223 | 0.149 | 0.148 | 0.149 | 0.153 | 0.242 |
| mq-dense-18-s18 @ GF(31) | 65.06 | 0.157 | 0.157 | 0.158 | 0.157 | 0.158 |
| mq-dense-18-s18 @ GF(32003) | 75.16 | 0.149 | 0.149 | 0.149 | 0.149 | 0.149 |
| Katsura-8 @ GF(31) | 0.0036 | 0.830 | 0.832 | 0.870 | 1.001 | 0.998 |
| Katsura-8 @ GF(32003) | 0.0037 | 0.826 | 0.825 | 0.865 | 1.009 | 1.007 |
| Cyclic-6 @ GF(31) (F4 route) | 0.0039 | 1.000 | 0.997 | 0.996 | 0.996 | 0.997 |
| Cyclic-6 @ GF(32003) (F4 route) | 0.0039 | 0.996 | 1.001 | 1.003 | 1.000 | 1.004 |
| mq-random-10-s10 @ GF(31) | 0.245 | 0.768 | 0.763 | 0.757 | 0.783 | 1.017 |
| mq-random-10-s10 @ GF(32003) | 0.261 | 0.781 | 0.786 | 0.780 | 0.790 | 1.015 |
| Noon-6 @ GF(32003) | 0.0057 | **1.109** | 1.124 | 1.067 | 0.998 | 0.998 |

**What it shows:**
- **Regime:** at one worker the lane is a 6–7× complete-task gain on dense MQ, against #945's 2.8–3.0× at 16 workers.
- **Controls:** #945's specification controls do not regress at one worker; Katsura-8 and mq-random-10 gain. Noon-6 at GF(32003) loses 11% with the lane forced on, as #269 predicted.
- **The rule:** a threshold of 100,000 entries keeps the whole regime saving and takes Noon-6 back to the field route.

**Frozen on #1123:** `lane_min_entries = 100_000`. It is the smallest decade at which every development control is at most 1.01× of the field route and every regime row keeps at least 99% of the forced lane's saving.

## Held-out read (§9.5, rule applied): fails
`sweep.py heldout-inputs|heldout-manifest` and `decide.py heldout.jsonl` write and score it. Bench-job `0aacde10b19b`:
- publication mode, one worker, 9 interleaved repetitions, CCDs 1–2 reserved;
- 675 of 675 cells complete; 10 contaminated attempts dropped;
- digests agree on every row; rule RSS is at most 1.08× the field route.

Every row was generated after the rule and criteria were posted on #1123. `field` is F, `rule` is D, `lane` (forced) is L. Intervals are the 95% bootstrap of `rule / field` from `bench_stats.independent_ratio`.

| Row | role | F (s) | rule / field | lane / field | verdict |
|---|---|---:|---:|---:|---|
| mq-dense-16-s16 @ GF(31) | target | 9.830 | 0.154 (0.153–0.157) | 0.153 | pass |
| mq-dense-16-s16 @ GF(32003) | target | 10.57 | 0.162 (0.159–0.166) | 0.160 | pass |
| mq-dense-16-s16 @ GF(7681) | target | 10.50 | 0.162 (0.161–0.163) | 0.160 | pass |
| mq-dense-18-s18 @ GF(7681) | target | 75.34 | 0.150 (0.149–0.150) | 0.148 | pass |
| Katsura-7, Katsura-9, Cyclic-7, Noon-7, Eco-8 @ both | control | 0.001–0.24 | 0.986–1.004, hi ≤ 1.018 | 0.69–1.14 | pass |
| **Noon-8 @ GF(32003)** | control | 0.188 | **1.081 (1.072–1.099)** | 1.099 | **fail** |
| **Noon-8 @ GF(7681)** | control | 0.188 | **1.084 (1.067–1.110)** | 1.101 | **fail** |
| mq-random-9-s9 @ GF(32003) | control | 0.0001 | 1.002 (0.946–1.044) | 1.191 | pass |
| **mq-random-9-s9 @ GF(7681)** | control | 0.0001 | 1.018 (0.939–**1.057**) | 1.113 | **fail** |
| mq-random-11-s11 @ GF(32003) / GF(7681) | control | 19.4 / 20.0 | 0.757 / 0.695 | 0.760 / 0.701 | pass |
| Katsura-8, Cyclic-6 @ GF(31) / GF(32003); Noon-6 @ GF(32003) | specification | 0.004–0.006 | 0.997–1.004, hi ≤ 1.010 | 0.83–1.11 | pass |

**What it shows:**
- **Targets:** the rule keeps the forced lane's saving on every eligible dense target, including the unseen field GF(7681) and the unseen scale n = 16. D is within 2% of L everywhere.
- **Noon-8:** a genuine adverse miss. Its losing batches clear 100,000 entries: the rule fires and the loss is the forced lane's.
  - Noon-6 and Noon-7 are protected only because their batches are smaller.
  - The entry count does not separate Noon's batches from the dense regime's.
- **mq-random-9-s9 @ GF(7681):** a 100 µs solve with a rule median of 1.018 and an interval of 0.939–1.057; the miss is width on a tiny row. The harness does not report `lane_batches`, so this read cannot show whether the rule fired there. It is still a miss against the criterion as declared.
- **Larger random MQ:** mq-random-11 gains 24–31% under the rule, which no criterion scored.

**Decision:** E fails §9.5 as frozen. `small_prime_lane` stays off at every preset; the threshold and plumbing ship off, as research options. Tuning the threshold on these rows would make them development rows, so a second rule needs new held-out rows.
