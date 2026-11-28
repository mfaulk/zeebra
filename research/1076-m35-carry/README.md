# #1076: M35 WP C, carrying signature work into conventional F4

**Measured at:**
- step 1: `37ffd88f` (tag `measured/1080-1076-harness`). Its `src/` is identical to Z0 `125658bb` (tag `measured/1162-z0`); it adds only `m34_matrix --research-envelope`.
- step 2: `66dd7d53` (tag `measured/1076-carry`), which adds `SigF4Options::carry` (research-sigf4) and `m34_matrix --carry`.
- step 3: `78d53497` (tag `measured/1076-lead-fall`), which adds `Boundary::LeadFall` and `m33_qualify`'s `reimer-N`.

**Plan:** [`MILESTONE-FINITE-FIELD-COMPETITIVENESS.md`](../../docs/MILESTONE-FINITE-FIELD-COMPETITIVENESS.md) §7.3, Amendment 1.

## Step 1: the limit check (predeclared on #1076)

`limit_check.py --binary BIN --commit SHA --inputs DIR` writes the dev-mode bench-job manifest. The inputs are #1200's per-record `record.json` files. It has three arms:

- `sig-research`: the forced signature engine under the research envelope;
- `f4`: shipping F4;
- `adaptive`: shipping Adaptive.

The job ran on the panel's two exposed sparse-MQ development rows, with 3 interleaved repetitions, CCDs 1–2 reserved, and a 900 s cap.

| Row | `sig-research` (s) | `f4` (s) | `adaptive` (s) | sig / min(f4, adaptive) | Peak RSS sig / f4 (MiB) |
|---|---:|---:|---:|---:|---|
| `mq-random-11-s11@m31` | 19.54 | 69.19 | 82.89 | 0.28 | 804 / 469 |
| `mq-random-12-s12@m31` | 19.81 | 53.12 | 68.50 | 0.37 | 1335 / 409 |

Bench-job `1902757da789`; library-call seconds, medians. Digests agree on all 18 attempts. Adaptive falls back on `TooManyRows { limit: 200000 }`, and the signature engine needs more than the 512 MB shipping live-byte budget.

**Decision, by the predeclared rule (≤ 1.15 × min):**
- The default limit is the cause on sparse MQ.
- Those rows move to #1186, as a dispatch and limit question.
- C continues on Cyclic-like inputs only.
- Raising a limit is not credited as an algorithmic improvement (plan §8.3).

## Step 2: carry versus restart at fixed boundaries (dev; decides nothing)

### The arms
`SigF4Options::carry` (`src/grobner/sigf4/carry.rs`, `research-sigf4`) stops the signature run once a given degree is finished and there is work left. Conventional F4 then finishes the run from one of two starts:
- **restart:** the original inputs only (plan arm 4);
- **continue:** the elements at minimal leads, plus the inputs (arm 5).

**Accounting:**
- The engine is dropped before F4 starts.
- F4 runs on the engine's workers under the remaining wall budget.
- `call_ns` charges both legs.
- Every ordinary pair obligation is rebuilt; none is dropped on the strength of a completed degree.

### The job
`carry_arms.py manifest|extract|table` writes, extracts and tabulates it. Bench-job `65ec1435b799`:
- 144 of 144 cells complete; digests agree across every arm on every row;
- one worker, shipping limits, medians of 3, CCDs 1–2 reserved.

Boundaries came from unrecorded probes of the same build. Ratios are against the best shipping arm, min(f4, adaptive).

| Row | f4 | adaptive | sig | best continue | its restart | restart ÷ continue |
|---|---:|---:|---:|---:|---:|---:|
| Cyclic-7 @ m31 | 0.225 s | 0.222 s | **0.37×** | 0.45× (14) | 1.19× | 2.7 |
| Cyclic-8 @ m31 | 4.931 s | 4.963 s | 0.55× | **0.30× (13)** | 1.16× | 3.8 |
| Eco-12 @ m31 (early-switch control) | 6.71× | 1.553 s | 1.00× | 4.92× (8) | 6.96× | 1.4 |
| Katsura-12 @ m31 (stay control) | 20.99× | 3.171 s | 1.00× | 21.72× (6) | 21.06× | 1.0 |

The full per-boundary table is in `carry_arms.py table` over `carry.jsonl.gz`.

**What it shows:**
1. **Carry has intrinsic value on Cyclic.** At the same boundary, continue beats restart by 2.7–3.8×. Restart is never better than shipping F4, because the prefix is discarded.
2. **There is a cliff.** On Cyclic-8, continue costs 1.00–1.06× up to boundary 12, then 0.30× at 13. On Cyclic-7 it is 1.02–1.10× up to 11, then 0.47× at 12. At the cliff, the number of elements at minimal leads *falls*: Cyclic-8 goes from 456 to 266, and Cyclic-7 from 200 to 142. Lower-degree leads arrive and dominate earlier ones, and F4's batch count drops from 38 to 22.
3. **The controls stay in signature.** Eco-12 and Katsura-12 lose 5–22× at every boundary, and their minimal-lead counts only grow.
4. **The baseline shifts on Cyclic.** Forced `sig` is the best qualified entry route there: Adaptive's `DegreeSpread` sends Cyclic to F4, where `sig` runs at 0.37–0.55×.
   - Against `sig`, carry gains 1.8× on Cyclic-8 and loses on Cyclic-7 (0.099 s against 0.082 s).
   - The dispatch finding is filed separately.

### Candidate online rule (development; not frozen)
Hand off after the first finished degree at which the count of minimal leads falls below its running maximum.

- **Development rows:** it fires at 13 on Cyclic-8 and at 12 on Cyclic-7, never on Eco-12 or Katsura-12. It is degree-free and costs one minimal-lead pass per degree.
- **What is needed next:**
  - implement it as a boundary mode;
  - declare two scales and fresh support, for example Cyclic-like rows from another lineage, and the plan §9.1 controls;
  - freeze it on #1076 before the held-out read.

## Step 3: the frozen lead-fall rule on held-out rows (§9.3)

### The rule
`Boundary::LeadFall` with `CarryMode::Continue` (`m34_matrix --engine sig --carry continue@fall`). The signature engine hands off after the first finished degree at which the minimal-lead count falls below its running maximum.

It was frozen on #1076 together with the held-out declaration, before any held-out row was generated.
- **Build:** `measured/1076-lead-fall` (`78d53497`), which adds the boundary and `m33_qualify`'s `reimer-N` rows.
- **Probe of the measured build on the development rows:** it fires at 12 on Cyclic-7 and at 13 on Cyclic-8, and never on Eco-12.

### The read
`heldout.py inputs|manifest|extract` writes, extracts and tabulates it. Bench-job `afc12893624d`:
- publication mode, one worker, 9 interleaved repetitions, CCDs 1–2;
- 270 of 270 attempts; 2 contaminated attempts excluded, one Cyclic-7 `f4` and one Cyclic-7 grobx;
- digests agree across every arm on every row.

Library-call seconds (grobx: its own `solve_ns`), medians. The baseline is min(f4, adaptive, sig) per row; each interval is `bench_stats.independent_ratio` on rule ÷ baseline.

| Row | role | f4 | adaptive | sig | rule (carried at) | rule ÷ baseline | gain | grobx | rule ÷ grobx |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|
| Cyclic-7 @ Goldilocks | scale | 0.281 | 0.283 | **0.090** | 0.124 (12) | 1.380 (1.369–1.408) | 0.72× | 0.096 | 1.29 |
| Cyclic-8 @ Goldilocks | scale | 6.790 | 6.787 | 3.186 | **1.903** (13) | 0.597 (0.596–0.604) | 1.67× | 1.596 | 1.19 |
| Reimer-6 @ m31 | fresh | 0.116 | **0.115** | 0.625 | 0.289 (13) | 2.519 (2.484–2.544) | 0.40× | 0.014 | 20.6 |
| Reimer-7 @ m31 | fresh | **2.994** | 2.999 | stopped: `TooManyLiveBytes` | 10.093 (14) | 3.371 (3.349–3.397) | 0.30× | 0.164 | 61.5 |
| Eco-12 @ Goldilocks | control | 14.071 | 1.765 | **1.757** | 1.761 (no handoff) | 1.002 (0.985–1.005) | 1.00× | 1.546 | 1.14 |
| Katsura-12 @ Goldilocks | control | 89.883 | 3.660 | **3.650** | 3.651 (no handoff) | 1.000 (0.996–1.004) | 1.00× | 3.606 | 1.01 |

**Peak RSS, rule / sig / f4 (MiB):**
- Cyclic-8: 104 / 171 / 146
- Reimer-7: 649 / 948 / 158
- Katsura-12: 442 / 444 / 547

### Decision
**C fails §9.3, and carry is not selected.**
1. **Declared scales:** only one of the two passes. Cyclic-8 gains 1.67× with the upper bound below 1. Cyclic-7 loses 0.72× to forced `sig`, as development predicted.
2. **Fresh family:** it does not confirm. On Reimer the signature prefix itself is the cost: forced `sig` is 5.4× slower than F4 on Reimer-6 and exceeds the live-byte budget on Reimer-7. Handing off at the lead fall recovers part of that, but stays 2.5–3.4× behind F4. Adaptive's `DegreeSpread` refusal is right for Reimer.
3. **Controls:** they pass. The rule never fires on Eco-12 or Katsura-12, and they stay at 1.00×.
4. **What remains:** carry has real intrinsic value where it applies (continue beats restart 2.7–3.8×, step 2), but on one family at one size. The rule-of-plan outcome is "switching does not help; carrying helps on Cyclic-8 only". `SigF4Options::carry` stays research-only, and the dispatcher is unchanged.

**For #1249:** Reimer shows that `DegreeSpread` is correct on part of the spread-degree shape. The Cyclic opportunity is narrower than that issue first suggested.
