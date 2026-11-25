# M34 Gate H: portfolio complementarity and selection headroom (#1012)

**Measured at:** harness `6c77117a` (tag `measured/1012-harness`, `src/` identical to Z0 `28df047f`),
`m34_matrix` SHA-256 `ee381510e63c0037d90fce74f9a2ff026d84f048dd7029980ca3eeb62c9a7683`; feature
costs with `feature_costs` at `3d21098c` (SHA-256 `2ecf48a1…`); S0 at `2db433b2` (tag
`measured/1012-s0`). Dev mode, 2026-11-25, CCDs 1–2 reserved. Data and scripts:
[`research/m34-gate-h/`](../../research/m34-gate-h/README.md).

Plan: [`docs/MILESTONE-GENERALIZABLE-SELECTION.md`](../MILESTONE-GENERALIZABLE-SELECTION.md) §5, §8,
§9.1, §12. Claim supported: none of C1–C3 (§5). Gate H decides whether a selector is worth
building (#1013). It is not a regime win and not a generalization result.

## 1. What was fixed before the matrix was read

All of these were posted on #1012 before the cell they affect ran:
- **Gate H thresholds:** the 2026-11-22 declaration, plan §9.1.
- **Judgement calls J1–J8:** [comment](https://github.com/mfaulk/zeebra/issues/1012#issuecomment-7151054452).
- **Two ladder-rule refinements:** [first](https://github.com/mfaulk/zeebra/issues/1012#issuecomment-7151135994) and [second](https://github.com/mfaulk/zeebra/issues/1012#issuecomment-7151235627).
- **The projection and top-up rule:** [comment](https://github.com/mfaulk/zeebra/issues/1012#issuecomment-7155901336).

No threshold was changed.

- **Corpus and cohort.**
  - The pilot as merged at `3d21098c`: 127 base problems in 36 families.
  - #1005 closed without sealing S0, so it was sealed under #1012 (J1) with #1005's own tool. The draw was S2, salt `m34-s0-v1`, over 34 groups: 10 untouched, 7 validation, and the rest development. The five M29–M33 ladders were exposed, so they were forced into development.
  - Two carve-outs went to untouched: the `zb/toric` p64 records (S5) and `sd-singular-schwarz-11` (S3).
  - **Gate H reads only the development cohort:** 122 records, 64 base problems, 17 families.
- **Arms.**
  - The eight #1011 arms as built at Z0, run as ten configurations: P1/P2/P3 conventional F4 at 1/4/16 workers, P4/P5/P6 signature F4 at 1/8/16, P7 cap16 at 1 and 16, and P8 adaptive at 1 and 16.
  - The harness `examples/m34_matrix.rs` sets exactly the options `m33_qualify` sets for #1011.
  - Contexts: W = 16 uses all ten configurations, and W = 1 uses P1, P4, P7-w1 and P8-w1.
- **Cells.**
  - Each attempt is one fresh process through `tools/bench-job`, with C = 300 s in-solver (330 s outer) and a 16 GiB `rss-guard`. Every attempt is pinned to the first *w* CPUs of 8–23, and the arms are rotated.
  - The charged cost is the process wall.
  - A completion counts only when its `reduced-basis-v1` digest equals the panel reference. For the nine oracle-frontier records, it counts when conventional and signature engines agree (J3).
  - Every other attempt costs 2C (PAR-2). Cell cost is the median over repetitions.
- **Repetitions.**
  - Pass 1 runs n = 1, tier by tier, so the ladder rule (§12.1) sees the rung below.
  - Pass 2 brings cells to n = 5 when under 60 s and n = 3 above. Censored cells are not repeated.
  - Pass 3 is §8.5's single top-up to n = 9, for cells under 60 s whose paired interval against the row's best spans 1.

## 2. Verdict: no-go

No context and no single-decision arm set meets every Go clause. Under plan §6.2, #1013 (selector) and #1014 close as not planned. The full read is in [`results/gate-h.md`](../../research/m34-gate-h/results/gate-h.md), and the machine-readable read is `results/gate-h.json`. Both come from `analyse.py`, with 20,000 grouped-bootstrap draws.

| Arm set | H | 95% interval | families ≤ 0.85 | H without largest contributor | split halves | Go clauses failed |
|---|---:|---|---:|---|---|---|
| W16 | **0.703** | [0.392, **0.942**] | 6 | **0.895** (`sd/ellipsoid`) | 0.702 / 0.701 | upper bound, drop-one |
| W1 | 0.767 | [0.446, 0.988] | 2 | 0.981 (`sd/ellipsoid`) | 0.765 / 0.764 | upper bound, families, drop-one |
| engine@16w | 0.845 | [0.399, 0.975] | 3 | 0.953 | 0.844 / 0.844 | H, upper bound, drop-one |
| workers@conv | 0.868 | [0.757, 0.953] | 4 | 0.926 (`katsura`) | 0.868 / 0.864 | all but families |

The other arm sets fail further from the thresholds (`results/gate-h.md`).

### Reading

- **The point estimate passes but is not robust.** At W16, H = 0.703 clears the 0.80 bar. Two families carry nearly all of it:
  - `sd/ellipsoid`, with a VBS⁺ ÷ BF of 0.120. Conventional F4 and adaptive exceed the 16 GiB ceiling on `sd-ellipsoid-m2`, while signature F4 completes it.
  - `sd/runge-kutta-order-conditions`, at 0.116.
- **Without those families there is little headroom.**
  - Removing `sd/ellipsoid` lifts H to 0.895.
  - The bootstrap's upper bound is 0.942, far above 0.87.
  - The remaining 15 families sit between 0.65 and 1.00, most of them above 0.9.
- **The best fixed arm is already close to the oracle.** Adaptive at one worker (P8-w1) is the leave-one-family-out best fixed arm in 16 of 17 families. Removing any single arm moves VBS⁺ by at most 1.1% at W16. At W1, removing signature F4 (P4) costs more (14%), because it is the only W1 arm that completes `sd-ellipsoid-m2`.
- **Completions differ by only a few cells.** On the 61 problems every arm completes, H is 0.898 at W16 and 0.980 at W1. PAR-10 changes the read little (0.681 and 0.743).

### Descriptive (does not decide)

Family-weighted geometric mean of PAR-2 cell cost, development cohort (`results/summary.md`, `summary.py`):

| Arm | ÷ P3 |
|---|---:|
| P8-w1 (adaptive, 1 worker) | 0.811 |
| P8-w16 | 0.863 |
| P4 (signature, 1 worker) | 0.908 |
| P3 (conventional, 16 workers) | 1.000 |
| P7 (cap16) | 1.42–1.44 |
| VBS⁺ (W16) | 0.645 |

- **Small problems dominate the cohort.** 56 of 64 development base problems (87.5%) finish under 300 ms on their best arm, and one is frontier: no arm completes it within C. That is the §8.2 composition this read was taken on. A corpus richer in frontier problems could read differently, but this gate is read as declared, on this cohort.

## 3. Execution record

| Pass | Window (UTC, 2026-11-25) | Machine-hours | Attempts |
|---|---|---:|---:|
| 1 (n = 1, ladder-gated) | 05:18–07:28 | 2.16 | 1,220 |
| 2 (to n = 5 / 3) + feature costs | 07:29–13:57 | 6.47 | 4,704 |
| 3 (§8.5 top-up to n = 9, 272 cells frozen in `results/topup.json`) | 13:57–15:18 | 1.35 | 1,088 |
| **Total** | | **9.98** of 40 | **7,012** |

- **Outcomes:** 6,558 completed-verified; 414 completed-unverified; 37 memory-refusal; 3 timeout; no incorrect output, so no arm was disqualified.
  - All 414 unverified completions are on the nine records with no panel reference. J3 then verifies a cell when a conventional and a signature arm agree on its digest, and it does so for every one of those cells except `gen-chandrasekhar-h-13`.
    - On `gen-chandrasekhar-h-13`, no signature arm completes, so nothing can be agreed. It costs 2C on every arm and is the cohort's one frontier problem.
  - Penalized cells, beyond that problem:
    - `sd-ellipsoid-m2`: memory refusal on conventional, cap16 and adaptive.
    - `zb-col-grid-5x5`: conventional and cap16.
- **Contamination:** `bench-job` flagged 173 attempts as contaminated. A cell's median uses its clean repetitions, and it falls back to all repetitions only when none is clean (`analyse.py`).
- **Feature costs:** 118 of 122 records were measured with #1009's `feature_costs`. The four `zb-col-grid-4x5`/`5x5` records could not be instantiated by that tool and take the declared J4 fallback, the largest measured cost.
