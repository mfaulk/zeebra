# M31-0: baseline, protocol and signature-F4 performance model (#901)

**Status:** complete, 2026-11-18. One session of the four the plan allows (§8.5).
**Measured at:** `5919caaa` (source of every executable; the freeze `acbaf12c` plus a feature-gated
instrument that no timed binary contains), 2026-11-18, three `tools/bench-reserve.sh` sessions on
CCDs 1–2 under `benchlock` (`zb-901`). Executable SHA-256s, toolchain and options:
[`research/m31-baseline/identities.json`](../../research/m31-baseline/identities.json).
**Plan:** [`MILESTONE-COMPETITIVE-SIGNATURE-F4.md`](../MILESTONE-COMPETITIVE-SIGNATURE-F4.md) §7.1,
§10. **Records and generated tables:** [`research/m31-baseline/`](../../research/m31-baseline/),
[`tables.md`](../../research/m31-baseline/tables.md) (every figure below is from it).

## Summary

- **Eco-12 / 2⁶⁴−353 (primary):** design 1 ÷ F4-16 = **1.638** [1.603, 1.655]; design 2 ÷ F4-16 =
  **1.370** [1.356, 1.382]. In the same binary F4-16 is 2.416 s and design 1 3.976 s (M30 §15.4:
  2,338.6 and 3,625.5 ms, another session and commit; not compared, plan §10.1). The plan's 0.75
  target is 1.812 s here, a cut of **2.165 s** from design 1.
- **Katsura-11 / Goldilocks (second family):** design 1 **0.839** [0.827, 0.845]; design 2 **0.622**
  [0.617, 0.625]. Design 2 already meets §6.2 criterion 2 (median ≤ 0.90, interval excluding 1.0)
  at this freeze. Katsura-11 / 2⁶⁴−353: 0.853 and 0.640.
- **MQ11 / Goldilocks (reported):** design 1 1.253 [1.231, 1.268]; design 2 0.656 [0.644, 0.660].
- **Every complete output's basis digest equals shipping F4's** on every row (666 of 666 cohort
  children complete, 40 of 40 split children).
- **Design 1's process wall is fully accounted for** (named parts sum to process wall within 0.4%
  on every row). #857's 0.245 s "unaccounted" Eco-12 wall is, here, 0.297 s: 0.149 s rendering and
  hashing the basis in the example (paid equally by the F4 arm), 0.083 s of engine glue (0.065 s of
  it materializing basis polynomials), 0.046 s of input loading and 0.021 s exec and exit.
- **The cascade is 14.5% of design 1's Eco-12 products and 10.2% of Katsura-11's**, but the serial
  share of the elimination stage is far larger: setup (column index and sparse-row construction,
  serial in both designs) is 0.484 s of design 1's 1.831 s and 0.568 s of design 2's 1.170 s, and
  design 2's serial pass is 0.502 s against a 0.100 s parallel pass.
- **Consequence for Gate A:** a schedule that made the cascade free and left setup as it is caps
  the Eco-12 elimination stage at **2.74×–3.14×** design 1, below Gate A item 2's 3.5×. Re-derived
  §6.3: the "required shape" projects **0.717×** F4-16, above Gate A item 3's 0.70; reaching 0.70
  with the other stages at that shape needs elimination **≥ 3.79×**. Setup must be in #902's and
  #903's scope, or Gate A cannot pass on Eco-12.
- **eco-14 is dropped** under §10.3: shipping F4-16 stops at its live-nonzero limit.

## 1. Freeze

| Item | Value |
|---|---|
| Zeebra freeze | `acbaf12c` (`main` at the start of #901), which contains #896 (`9f904d08`), #897 (`4d8ea30c`) and #898 (`64363ab0`) |
| Measured source | `5919caaa`: the freeze plus `research-sigf4-split` (feature-gated, compiled out of every timed binary), three `sig_f4_study` instantiations (8, 9, 14 variables) and its in-process clocks. `git diff acbaf12c 5919caaa -- src/` is the instrument and its test only |
| Executables | `sig_f4_study`, `m29_cost_model`, `zeebra_driver`, `wide_corpus` (timed build, features `research-sigf4` + default) and the split build's `sig_f4_study`; SHA-256s in [`identities.json`](../../research/m31-baseline/identities.json) |
| Toolchain and profile | rustc 1.99.1 (`58cf8f9c3`); release, fat LTO, one codegen unit, `x86-64-v3`, `RUSTC_WRAPPER=""`, private `CARGO_TARGET_DIR`s under `/buildcache` |
| F4 options | `F4Options::default()`; forward and symbolic `Serial` at one worker, `Auto { max_workers: w }` otherwise (symbolic team = `w`, clamped to available parallelism by #895; the cpuset gives exactly `w`) |
| Signature options | `SigF4Options::default()`, `workers = 1` (design 1) or `16` (design 2: parallel pre-reduction of each batch's targets against its reducer block; symbolic, bookkeeping, the cascade and interreduction serial) |
| Inputs | the plan §10.3 corpus by canonical SHA-256, re-hashed from `research/wide-corpus/cases.json` into [`pins.json`](../../research/m31-baseline/pins.json); MQ10 is `m29_cost_model`'s own pinned generator |
| Held-out rows | katsura-9, noon-8, eco-14 at 2⁶⁴−353, committed in `956a5b17` before any timing (and before any S2/S3 timing) |
| Comparands | M30-0's identities reused unchanged (`research/m30-baseline/identities.json`, recorded by digest); #901 runs no comparand |
| Host and placement | 5995WX, governor `performance`, boost on; `tools/bench-reserve.sh` CCDs 1–2 (CPUs 8–23) reserved for each session and released at its end; each child `taskset` to CPUs 8..8+w−1; `tools/cpu-context.sh` before and after every child, frequency sampled every 25 ms |

## 2. Protocol and what deviated

Three sessions, each one `bench-reserve run zb-901 8-23` under `benchlock`
([`benchlock.log`](../../research/m31-baseline/benchlock.log)): `probe` (eco-14, one repetition),
`walls` (n = 9) and `split` (n = 5). Fresh process per child; rows in turn, arms rotated one place
per repetition, so every arm's repetition *r* sits beside every other arm's repetition *r*. Ratios
are **paired**: the median of the per-repetition ratios, with a 95% percentile bootstrap over
repetitions (20,000 draws). Process wall, measured by the controller around the whole child, is the
figure. Every attempt is in the records; none was rerun or dropped.

- **eco-14 is dropped (plan §10.3).** Shipping F4 at 16 workers stops at its default live-nonzero
  limit (37,152,044 needed against 32,000,000) after 8.4 s; at one worker it stops on the same limit
  after 74.6 s. Design 1 reached final interreduction and was stopped by the 180 s cap having reduced
  39 of 2,852 signature-basis elements (2.6 GiB peak). It is recorded, not replaced.
- **The memory guard did not attach in the probe and walls sessions.** The controller passed
  `--poll 0.2` to `tools/rss-guard.sh`, whose loop does integer arithmetic; it exited 1 ("not
  guarded") on every child. Each child's own peak RSS is in its record and the largest in the walls
  session is 393 MiB (MQ11, F4-16), so the 8 GiB cap was never approached. The split session ran with the fix.
- **The signature engine's stage clocks are always on**, so the wall cohort's design-1 and design-2
  records are themselves stage-clock records with no added instrumentation; §4 uses them. The
  separate n = 5 campaign (§5) is the `research-sigf4-split` binary, whose per-batch clocks are
  extra instrumentation; its walls are never compared with the cohort's.
- MQ10 has no `sig_f4_study` field, so its rows are shipping F4 only (`m29_cost_model`, in the
  same rotation). The signature path does not run MQ10, which plan §6.4 reports and does not score.

## 3. Wall cohort (n = 9, process wall, medians [95% bootstrap])

| Row | F4-1 | F4-4 | F4-8 | F4-16 | Design 1 | Design 2 (16w) | Peak RSS F4-16 / d1 / d2 MiB |
|---|---:|---:|---:|---:|---:|---:|---:|
| Eco-12 / 2⁶⁴−353 | 13.962 | 4.716 | 3.098 | 2.416 [2.400, 2.436] | 3.976 [3.875, 3.997] | 3.316 [3.279, 3.337] | 199 / 208 / 220 |
| Katsura-11 / Goldilocks | 11.215 | 3.274 | 1.964 | 1.400 [1.390, 1.409] | 1.172 [1.150, 1.187] | 0.872 [0.868, 0.875] | 148 / 106 / 110 |
| Katsura-11 / 2⁶⁴−353 | 10.013 | 3.122 | 1.884 | 1.351 [1.338, 1.358] | 1.154 [1.141, 1.157] | 0.859 [0.854, 0.867] | 149 / 106 / 110 |
| MQ11 / Goldilocks | 47.173 | 13.231 | 7.597 | 4.903 [4.883, 4.921] | 6.166 [5.995, 6.237] | 3.213 [3.168, 3.234] | 392 / 357 / 368 |
| MQ10 / GF(32003) | 1.189 | 0.397 | 0.270 | 0.239 [0.235, 0.242] | — | — | 42 |
| MQ10 / GF(2³¹−1) | 1.084 | 0.350 | 0.246 | 0.224 [0.223, 0.225] | — | — | 44 |
| Cyclic-7 / Goldilocks | 0.314 | 0.160 | 0.135 | 0.145 | 0.947 | 1.023 | 20 / 69 / 70 |
| Cyclic-7 / 2⁶⁴−353 | 0.290 | 0.157 | 0.133 | 0.143 | 0.951 | 1.019 | 21 / 69 / 71 |
| katsura-4 / Goldilocks, 2⁶⁴−353 | 0.006 | 0.006 | 0.006 | 0.006 | 0.006 | 0.006 | 5 / 5 / 5 |
| noon-7 / Goldilocks | 0.206 | 0.161 | 0.153 | 0.184 | 0.111 | 0.118 | 23 / 18 / 20 |
| katsura-9 / 2⁶⁴−353 (held out) | 0.170 | 0.084 | 0.070 | 0.073 | 0.052 | 0.051 | 13 / 10 / 11 |
| noon-8 / 2⁶⁴−353 (held out) | 1.457 | 1.000 | 0.906 | 0.948 | 0.692 | 0.709 | 114 / 88 / 94 |

Seconds. Intervals for every cell are in `tables.md`. katsura-4 is process startup at every arm.

### 3.1 Paired ratios (median of per-repetition ratios [95% bootstrap], n = 9)

| Row | d1 ÷ F4-16 | d2 ÷ F4-16 | d2 ÷ d1 | d1 ÷ F4-1 | F4-1 ÷ F4-16 |
|---|---:|---:|---:|---:|---:|
| **Eco-12 / 2⁶⁴−353** | **1.638** [1.603, 1.655] | **1.370** [1.356, 1.382] | 0.838 [0.829, 0.847] | 0.281 [0.280, 0.286] | 5.871 |
| **Katsura-11 / Goldilocks** | **0.839** [0.827, 0.845] | **0.622** [0.617, 0.625] | 0.742 [0.735, 0.758] | 0.105 [0.104, 0.106] | 7.984 |
| Katsura-11 / 2⁶⁴−353 | 0.853 [0.848, 0.856] | 0.640 [0.629, 0.642] | 0.750 [0.741, 0.752] | 0.115 [0.115, 0.119] | 7.421 |
| MQ11 / Goldilocks | 1.253 [1.231, 1.268] | 0.656 [0.644, 0.660] | 0.528 [0.515, 0.529] | 0.131 [0.129, 0.131] | 9.681 |
| Cyclic-7 / Goldilocks | 6.556 [6.407, 6.749] | 7.088 [6.998, 7.270] | 1.079 [1.060, 1.110] | 3.021 [2.965, 3.081] | 2.218 |
| Cyclic-7 / 2⁶⁴−353 | 6.645 [6.578, 6.708] | 7.128 [7.058, 7.247] | 1.070 [1.067, 1.102] | 3.276 [3.210, 3.290] | 2.044 |
| katsura-4 / Goldilocks | 0.982 [0.947, 1.010] | 1.080 [1.057, 1.100] | 1.096 [1.079, 1.135] | 1.009 [0.966, 1.030] | 0.974 |
| katsura-4 / 2⁶⁴−353 | 0.953 [0.925, 0.975] | 1.073 [1.056, 1.080] | 1.130 [1.097, 1.141] | 0.997 [0.974, 1.034] | 0.965 |
| noon-7 / Goldilocks | 0.603 [0.600, 0.625] | 0.635 [0.629, 0.660] | 1.048 [1.042, 1.069] | 0.541 [0.536, 0.545] | 1.130 |
| katsura-9 (held out) | 0.717 [0.708, 0.722] | 0.707 [0.689, 0.713] | 0.988 [0.980, 0.991] | 0.306 [0.304, 0.310] | 2.360 |
| noon-8 (held out) | 0.730 [0.715, 0.737] | 0.748 [0.746, 0.755] | 1.033 [1.016, 1.042] | 0.476 [0.470, 0.484] | 1.542 |

Read against §6.2 *as a baseline only* (the criteria apply to M31's final code): Eco-12 needs a
0.75 median; design 2 is 1.83× too slow for it. Katsura-11 / Goldilocks already passes criterion 2
under design 2. The controls fail criterion 3 at 16 workers on Cyclic-7 (7.1×) and on katsura-4
(upper bounds 1.10 and 1.08), which is the dispatch question #905 owns. Peak RSS is ≤ 1.11× F4-16 on
every row except Cyclic-7 (3.5×), as in M30.

## 4. Stage decomposition and design 1's unaccounted wall (cohort records, n = 9, medians)

| Row / arm | Elimination | Interreduction | Bookkeeping | Symbolic | Σ stages | Engine glue (total − Σ) | Input load | Render + hash (example) | Exec + exit | Process wall | Σ ÷ process |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Eco-12 d1 | 1.890 | 0.780 | 0.504 | 0.505 | 3.679 | 0.083 | 0.046 | 0.149 | 0.021 | 3.976 | 1.000 |
| Eco-12 d2 | 1.192 | 0.780 | 0.512 | 0.520 | 3.004 | 0.096 | 0.046 | 0.150 | 0.023 | 3.316 | 1.001 |
| Katsura-11 / Goldilocks d1 | 0.631 | 0.121 | 0.022 | 0.180 | 0.954 | 0.028 | 0.041 | 0.142 | 0.012 | 1.172 | 1.004 |
| Katsura-11 / Goldilocks d2 | 0.311 | 0.122 | 0.024 | 0.182 | 0.639 | 0.034 | 0.041 | 0.144 | 0.013 | 0.872 | 0.997 |
| MQ11 d1 | 4.237 | 0.605 | 0.038 | 0.504 | 5.384 | 0.108 | 0.141 | 0.495 | 0.024 | 6.166 | 0.998 |
| MQ11 d2 | 1.272 | 0.612 | 0.039 | 0.511 | 2.435 | 0.117 | 0.142 | 0.496 | 0.024 | 3.213 | 1.000 |
| Cyclic-7 / Goldilocks d1 | 0.160 | 0.021 | 0.575 | 0.132 | 0.888 | 0.036 | 0.008 | 0.008 | 0.006 | 0.947 | 0.998 |

Seconds. The pieces are disjoint clocks, so they sum to process wall by construction; the last
column checks that their medians do (all within 0.4%, against the 5% acceptance bound).
`call − total` (the `sig_f4_reported` wrapper) is under 0.1 ms everywhere and omitted.

- **Answering plan §4.3 item 4:** on Eco-12, of the 0.297 s outside the four stages, 0.149 s is the
  example rendering 743 polynomials to text and hashing them, 0.046 s is loading and parsing the
  input, 0.021 s is exec and exit, and 0.083 s is inside the engine but outside every stage clock.
  The split instrument (§5) attributes 0.065 s of that to converting the signature basis into
  polynomials before interreduction; input normalization and dropping the engine are under 1 ms.
  So "startup" is 0.067 s, "minimal-basis work" is the 0.065 s materialization, and the remaining
  0.15 s is the measurement harness, which the F4 arm pays too (same basis, same code).
- Only the 0.083 s of glue is an engine cost #903 can target; the input load and render are fixed
  costs of both arms in `sig_f4_study`, and leave every ratio here slightly closer to 1 than the
  engines' own ratio (Eco-12 d1 without them: (3.976 − 0.195) ÷ (2.416 − 0.195) ≈ 1.70).
- Design 2's serial stages run 1–3% slower than design 1's (bookkeeping 0.512 against 0.504,
  symbolic 0.520 against 0.505, setup in §5 0.568 against 0.484). That is consistent with the
  all-core clock lingering after each parallel pass (boost hysteresis), not with extra work: the
  serial stages do identical work in both designs.

## 5. Elimination split: reducer block against the cross-target cascade (split binary, n = 5)

`research-sigf4-split` clocks each batch's elimination in three parts — **setup** (the column index
and the sparse-row construction, serial in both designs), design 2's **parallel pass** (every target
against the reducer block alone, 16 threads), and the **serial pass** (targets in signature order
against reducer pivots and earlier targets) — and attributes every coefficient product to the pivot
that spent it: a reducer-block row, or an earlier target of the same batch (the **cascade**).

| Row / arm | Elimination | Setup | Parallel pass | Serial pass | Products G: parallel / serial reducer / cascade | Cascade share | Targets cascading |
|---|---:|---:|---:|---:|---:|---:|---:|
| Eco-12 d1 | 1.831 | 0.484 | — | 1.347 | — / 0.522 / 0.089 | 14.5% | 2,447 / 2,898 |
| Eco-12 d2 | 1.170 | 0.568 | 0.100 | 0.502 | 0.522 / 0.132 / 0.089 | 11.9% | 2,447 / 2,898 |
| Katsura-11 / Goldilocks d1 | 0.610 | 0.171 | — | 0.439 | — / 0.180 / 0.020 | 10.2% | 681 / 706 |
| Katsura-11 / Goldilocks d2 | 0.309 | 0.220 | 0.036 | 0.053 | 0.180 / 0.000 / 0.020 | 10.2% | 681 / 706 |
| Katsura-11 / 2⁶⁴−353 d1 | 0.604 | 0.173 | — | 0.431 | — / 0.180 / 0.020 | 10.2% | 681 / 706 |
| Katsura-11 / 2⁶⁴−353 d2 | 0.307 | 0.220 | 0.035 | 0.052 | 0.180 / 0.000 / 0.020 | 10.2% | 681 / 706 |
| MQ11 d1 | 4.084 | 0.488 | — | 3.599 | — / 1.558 / 0.187 | 10.7% | 1,296 / 1,307 |
| MQ11 d2 | 1.243 | 0.593 | 0.227 | 0.422 | 1.558 / 0.000 / 0.187 | 10.7% | 1,296 / 1,307 |

Seconds; products are deterministic and identical across repetitions. The split binary's walls
(Eco-12 d1 3.915 s, d2 3.284 s) are within 1.6% of the cohort's, so the instrument does not
visibly perturb the stage, but they are a separate session and are not paired with §3.

What this says, for #902:

1. **The cascade is small in products and large in time once the reducer block is parallel.** On
   Eco-12 the cascade is 0.089 G of design 1's 0.611 G. Design 2's serial pass spends 0.502 s on
   0.221 G: the cascade's 0.089 G plus **0.132 G of reducer work that only appears after the
   cascade** (fill-in: an earlier target's tail reintroduces columns that need reducer pivots).
   Katsura-11 and MQ11 have none of that second kind; their serial pass is the cascade alone
   (0.053 s and 0.422 s). This is the 0.611 → 0.743 G product rise #857 §5 reported, now located.
2. **Setup is the largest serial piece of design 2's elimination**: 0.568 s of 1.170 s on Eco-12
   (49%), 0.220 of 0.309 on Katsura-11 (71%). No cascade schedule touches it.
3. Nearly every target cascades (84% on Eco-12, 96% on Katsura-11, 99% on MQ11), so the cascade's
   dependency structure is dense in membership; its critical path is #902's question.
4. Eco-12's elimination is concentrated: 4 of 29 batches (17, 15, 19, 13; 273–603 targets,
   4,247–8,233 reducers) hold 72% of design 1's time. Batch 17 alone is 0.444 s in design 1 and
   0.291 s in design 2, of which 0.193 s is serial pass. Per-batch tables: `tables.md`.

### 5.1 Elimination-stage ceilings against design 1 (from the measured parts)

| Schedule | Eco-12 elimination | ceiling | Katsura-11 elimination | ceiling |
|---|---:|---:|---:|---:|
| Design 2 as measured | 1.170 | 1.56× | 0.309 | 1.97× |
| Cascade free, design 2's setup | 0.668 | **2.74×** | 0.256 | 2.38× |
| Cascade free, design 1's setup | 0.584 | **3.14×** | 0.207 | 2.95× |
| Cascade and setup free (parallel pass only) | 0.100 | 18.3× | 0.036 | 16.9× |

"Cascade free" means the serial pass costs nothing — every cascade product and every post-cascade
reducer product done in zero time — so these are upper bounds on any parallel-cascade schedule
that leaves setup serial. **Gate A item 2 asks ≥ 3.5× on Eco-12; neither setup-serial ceiling
reaches it.** A schedule that passes item 2 must also parallelize or shrink setup (0.484–0.568 s,
the column `MonomialMap` and the monomial-product row conversion in `engine.rs::eliminate`), which
is equally a #903 serial-overhead target.

## 6. Plan §6.3 re-derived at the freeze

Every input is from this freeze, this binary and this session: design 1's median process wall
**3.976 s**, the same binary's F4-16 median **2.416 s**, and design 1's median stage clocks from the
same nine repetitions. Each row subtracts the saved stage time, `stage × (1 − 1/factor)`, from
design 1's wall and divides by F4-16. It is an additive Amdahl estimate, not a prediction; the
0.297 s outside the stages (§4) is never cut. The 0.75 target is 1.812 s, so the **required cut is
2.165 s** (it was 1.87 s in the plan).

| Scenario (Eco-12 / 2⁶⁴−353) | Elimination 1.890 s | Interreduction 0.780 s | Bookkeeping 0.504 s | Symbolic 0.505 s | Projected wall | ÷ F4-16 |
|---|---|---|---|---|---:|---:|
| Elimination free, rest unchanged | free (−1.890) | — | — | — | 2.087 s | 0.864 |
| Other stages free, elimination unchanged | — | free (−0.780) | free (−0.504) | free (−0.505) | 2.187 s | 0.906 |
| Moderate | 3× (−1.260) | 1.5× (−0.260) | 1.25× (−0.101) | 2× (−0.253) | 2.103 s | 0.871 |
| Required shape (plan) | 3.5× (−1.350) | 2× (−0.390) | 1.5× (−0.168) | 3× (−0.337) | 1.732 s | **0.717** |
| Optimistic | 6× (−1.575) | 3× (−0.520) | 2× (−0.252) | 3.9× (−0.376) | 1.254 s | 0.519 |
| §5.1 ceiling, cascade free with design 2's setup; others at required shape | 2.74× (−1.200) | 2× | 1.5× | 3× | 1.881 s | 0.779 |
| §5.1 ceiling, cascade free with design 1's setup; others at required shape | 3.14× (−1.288) | 2× | 1.5× | 3× | 1.793 s | 0.742 |

The last two rows apply the §5.1 factors (measured in the split session) to the cohort's
elimination clock.

- **Neither workstream is sufficient, and the plan's required shape is no longer enough.** At this
  freeze it projects 0.717, above Gate A item 3's 0.70. Holding the other stages at the required
  shape, **elimination must reach 3.79×** design 1 for 0.70 (the 0.75 target needs about 3.05×).
  Elimination alone cannot reach 0.70 at any factor.
- **A cascade-only schedule does not reach Gate A.** With setup serial, the best possible
  elimination is 2.74×–3.14× (§5.1), which projects 0.742–0.779 even with S3 delivering the
  required shape. Gate A needs setup cut as well: with setup free, the parallel pass alone is
  18×, so the gate is reachable in principle, but only if the setup work is in scope.
- What changed against the plan's table: F4-16's paired arm and design 1 are both from one binary
  now (the plan mixed `2d589a80` stage clocks with `e4826153` walls), the elimination clock is
  1.890 s rather than 1.698 s, and the 0.297 s outside the stages is explicit. The required cut grew
  from 1.87 s to 2.165 s while the staged time grew from 3.393 s to 3.679 s, so the
  shape factors buy less than they did.

**Katsura-11 / Goldilocks** (second family; target 0.90): design 1 1.172 s, F4-16 1.400 s,
design 1 is already 0.839, so no cut is required; the required shape would project 0.381, and
design 2 alone measures 0.622.

## 7. Acceptance criteria

| Criterion (issue #901) | Status |
|---|---|
| Freeze recorded with every Scope (1) item; held-out digests committed before any S2/S3 timing | Done: §1; `956a5b17` was pushed before any timing in this issue and reported to #903 before it timed |
| Wall cohort complete, every attempt retained, medians with 95% bootstrap intervals | Done: 666 of 666 children complete; plus the eco-14 probe's 3 stopped attempts, retained |
| Stage decomposition sums to process wall within 5%, or the residual is named | Done: within 0.4% on every row, every residual named (§4) |
| Cascade against reducer-block split for Eco-12 and Katsura-11 | Done: §5, both fields of Katsura-11, and MQ11 |
| `tools/check-measurement-provenance.sh` passes | Done |

Not done, and why: the signature path has no MQ10 field in `sig_f4_study`, so MQ10 is shipping F4
only (§2); adding fields to the example was not needed by any gate. The memory guard ran unattached
in two of three sessions (§2), with every child's own peak recorded and none near the cap.

## 8. Reproduction

[`research/m31-baseline/README.md`](../../research/m31-baseline/README.md): build commands (two
private target directories), `setsid -w research/m31-baseline/run.sh probe|walls|split OUT`, and
the `summarize.py` line that regenerates `tables.md`; CI re-runs that line and diffs it.
