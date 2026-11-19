# M32-0: baseline, corpus pin and signature-F4 performance model (#939)

**Status:** complete, 2026-11-19 (#939 deliverables 1–6; #934 and #935 within it).
**Measured at:** baseline `7b25a1ee` and M31 reference `8715c8ed` for the cohort; `f26b8d80` (tag
`measured/939-pin`) for the held-out admission read; `45107ec3` (tag `measured/939-instrument`) for
the split, small-control and A/B builds (the baseline's library plus `research-*`-gated
instruments). 2026-11-19, `tools/bench-reserve.sh` sessions on CCDs 1–2 under `benchlock`
(`zb-939`). Other sessions' compilers ran on the remaining CPUs throughout (load 1–18), so
absolute walls are beside builds. Executable SHA-256s, toolchain and options:
[`research/m32-baseline/identities.json`](../../research/m32-baseline/identities.json).
**Plan:** [`MILESTONE-ADAPTIVE-F4.md`](../MILESTONE-ADAPTIVE-F4.md) §6.3, §7.1, §8.3, §10.
**Records and generated tables:** [`research/m32-baseline/`](../../research/m32-baseline/),
[`tables.md`](../../research/m32-baseline/tables.md). Every figure below is from those tables.

## Summary

- **Freeze and pin.** F0 is the M31 reference `8715c8ed` and the M32 baseline `7b25a1ee`, which
  are identical in code. There are 13 development rows. Three held-out rows are kept: MQ10 /
  Goldilocks, Katsura-10 / GF(2³¹−1) and Eco-11 / GF(2³¹−1). Three are dropped by the rule and not
  replaced (§2).
- **M31 reproduces.** On all ten substantial rows, the baseline's `f4_signature` ÷ conventional-F4
  ratio at 16 workers is within 1.6% of M31 §15.2. The worst is MQ10 / 32003: 1.609 against 1.583.
  Baseline ÷ reference at 16 workers is 0.990–1.013 on every row (§3).
- **Symbolic is mostly interning.** In the split build, hash interning of row terms is 52–86% of
  the signature engine's symbolic stage. Monomial multiplication is 10–21%, the reducer search
  1–13% and the column sort 2–13%. The shares barely move with workers (§4).
- **Symbolic growth with workers is partly clock.** The symbolic thread runs at about 4.4 GHz alone
  and about 4.0 GHz with a team (8 or 16 workers), about −10%. Over the same range Eco-12's
  symbolic stage grows from 462 to 552 ms, +19%. The other half of the growth is not clock (§4).
- **An unplanned finding for #933.** The split build's unfused symbolic path, which multiplies each
  row into a buffer before interning, is faster than the shipping fused loop on Eco-12 (symbolic
  0.60–0.66×, process wall 0.90–0.93×) and on MQ10 (0.64–0.69×, wall 0.82–0.83×), but slower on
  Katsura-11 (1.08–1.16×). This comes from an A/B run interleaved in one session (§4.1).
- **Eco-12's ~300 ms outside the four stages:** about 103 ms inside the engine but outside its
  stage clocks, almost all of it basis materialization; 140 ms rendering the basis for the digest
  (harness); 41 ms of parsing and report (harness); 19 ms of exec and exit. About two thirds of the
  gap is therefore harness cost, which the comparands' drivers do not pay in the same way (§5).
- **Ceilings (§6).** Removing Eco-12's symbolic growth alone gives 0.948× the current sig path.
  1.5×/2×/3× symbolic speedups give 0.895/0.842/0.790×, and free symbolic gives 0.685×. For T3 on
  MQ10, S1 alone would need ≥ 2.3× (32003) and ≥ 3.1× (2³¹−1).
- **#934.** In-process call time (k = 21 calls per process, the cold first call dropped, n = 31
  processes) resolves katsura-4's entry-point ÷ shipping ratio to a half-width of 0.50–0.70% at
  both fields and 1 and 16 workers, against the 2% acceptance. Process wall at the same n gives
  0.83–1.61%. The plan's default method stands (§7).
- **#935.** See §8.

## 1. Freeze (F0)

- **M31 reference:** `8715c8ed`, M31's final `main` (#926).
- **M32 baseline:** `7b25a1ee`, `main` at the freeze (#943). Its timed `src/` equals the planning
  base `e59a90a1`'s and differs from the reference only in documentation: eight added lines, a
  performance caveat in `f4_signature`'s doc comment and one `#[doc = include_str!(…)]` in
  `src/lib.rs`. No code line differs; `Cargo.toml`, `Cargo.lock` and `.cargo/` are identical.
- **Instrument build** `45107ec3`: the baseline plus #948's `research-sigf4-usage` and #939's split.
  Outside research features its `src/` differs only by #948's same-predicate rewrite of the
  rewriter check.

Every build comes from a `git archive` (release, fat LTO, one codegen unit, `x86-64-v3`). The
executables' SHA-256s are in the research README.

## 2. Corpus pin

The development set is plan §10.1's, unchanged. The held-out candidates were built by the public
generators the plan names and admitted by its fixed rule: conventional F4 at 16 workers completes in
20 ms–60 s, and both engines accept the field. Pins, generators and admission evidence are in
[`research/m32-baseline/README.md`](../../research/m32-baseline/README.md) §2.

| Held-out candidate | Field | F4-16 median process wall | Verdict |
|---|---|---|---|
| mq-random-10 | Goldilocks | 930.5 ms | kept |
| mq-random-12 | 2⁶⁴−353 | 104554.0 ms | dropped |
| mq-random-9 | GF(32003) | 3.1 ms | dropped |
| katsura-10 | GF(2³¹−1) | 242.4 ms | kept |
| eco-11 | GF(2³¹−1) | 427.4 ms | kept |
| cyclic-6 | Goldilocks | 7.6 ms | dropped |

MQ12 / 2⁶⁴−353 is over the 60 s bound, so the held-out set has no dense MQ beyond the crossover.
Cyclic-6 and the seed-9 MQ9 (an inconsistent system, basis {1}) are under 20 ms. None is replaced.

## 3. Baseline cohort

The cohort is n = 9 fresh processes per cell with arms rotated per repetition. Each of the 13 rows
has 20 arms: shipping F4 and the entry point at 1/4/8/16 workers, from both the baseline and the
reference, plus the signature engine's stage-clock arms (`d1:1`, `cl:4/8/16`). That is 2,340
children, all complete.

| Row | Route | en ÷ f4, 1 w | 4 w | 8 w | 16 w | M31 §15.2 (16 w) | M32 ÷ M31 |
|---|---|---:|---:|---:|---:|---:|---:|
| Eco-12 / 2⁶⁴−353 | Signature | 0.198 | 0.426 | 0.582 | **0.738** | 0.737 | 1.001 |
| Katsura-11 / Goldilocks | Signature | 0.097 | 0.222 | 0.323 | **0.454** | 0.453 | 1.001 |
| Katsura-11 / 2⁶⁴−353 | Signature | 0.100 | 0.227 | 0.332 | **0.456** | 0.459 | 0.993 |
| MQ11 / Goldilocks | Signature | 0.129 | 0.230 | 0.322 | **0.458** | 0.456 | 1.005 |
| MQ10 / 32003 | Signature | 0.432 | 0.966 | 1.311 | **1.609** | 1.583 | 1.016 |
| MQ10 / 2³¹−1 | Signature | 0.488 | 1.092 | 1.458 | **1.745** | 1.728 | 1.010 |
| Cyclic-7 / Goldilocks | Shipping (degree spread) | 1.008 | 1.001 | 1.000 | 1.008 | 0.996 | 1.012 |
| Cyclic-7 / 2⁶⁴−353 | Shipping (degree spread) | 0.994 | 1.005 | 1.000 | 1.001 | 1.001 | 1.000 |
| noon-7 / Goldilocks | Signature | 0.482 | 0.589 | 0.621 | 0.560 | 0.558 | 1.005 |
| noon-8 / 2⁶⁴−353 | Signature | 0.421 | 0.592 | 0.622 | 0.611 | 0.612 | 0.999 |

These are paired medians; the intervals are in `tables.md`. katsura-4 (6 ms) and katsura-9
(43 ms) are under 50 ms and are not gated by process wall (§7). The MQ10 crossover is unchanged:
the signature route wins at one worker, ties near four and loses from eight up.

**Stage clocks, Eco-12 and MQ10** (signature route, medians, ms):

| Row | Arm | Wall | Symbolic | Elimination | Bookkeeping | Interreduction | Four stages |
|---|---|---:|---:|---:|---:|---:|---:|
| Eco-12 / 2⁶⁴−353 | d1:1 | 2,565 | 462 | 1,326 | 230 | 269 | 2,287 |
| | cl:4 | 1,836 | 483 | 565 | 239 | 261 | 1,554 |
| | cl:8 | 1,746 | 514 | 429 | 252 | 263 | 1,458 |
| | cl:16 | 1,745 | 552 | 370 | 260 | 262 | 1,446 |
| MQ10 / 32003 | d1:1 | 473 | 205 | 191 | 19 | 23 | 437 |
| | cl:16 | 383 | 234 | 56 | 21 | 25 | 336 |
| MQ10 / 2³¹−1 | d1:1 | 448 | 197 | 169 | 18 | 22 | 408 |
| | cl:16 | 392 | 230 | 69 | 21 | 24 | 343 |

At 16 workers symbolic is now the largest stage on Eco-12 (38% of the four) and is 67–70% of the
four stages on MQ10. Plan §2.2's figures (552 / 370 / 259 / 264 ms on Eco-12) reproduce to within
5 ms.

## 4. The symbolic stage by component, and its clock

From the split build (n = 5; shares of its own symbolic total; full table in `tables.md`):

| Row | Workers | Reducer search | Multiply | Interning | Column sort | Other | Symbolic-thread MHz |
|---|---:|---:|---:|---:|---:|---:|---:|
| Eco-12 / 2⁶⁴−353 | 1 | 7.8% | 20.6% | 60.9% | 7.0% | 3.7% | 4,465 |
| | 4 | 8.2% | 20.9% | 59.7% | 7.2% | 4.1% | 4,122 |
| | 8 | 8.1% | 20.7% | 60.0% | 7.2% | 4.1% | 3,985 |
| | 16 | 7.0% | 17.9% | 64.3% | 6.4% | 4.4% | 3,986 |
| Katsura-11 / Goldilocks | 1 / 16 | 2.3% / 2.6% | 11.3% / 10.1% | 82.3% / 82.7% | 2.8% / 2.7% | 1.3% / 1.8% | 4,300 / 3,974 |
| MQ11 / Goldilocks | 1 / 16 | 1.0% / 1.2% | 11.4% / 10.9% | 85.5% / 85.6% | 1.6% / 1.6% | 0.5% / 0.7% | 4,369 / 3,988 |
| MQ10 / 32003 | 1 / 16 | 12.8% / 12.6% | 13.6% / 12.1% | 52.2% / 54.1% | 13.3% / 11.9% | 8.0% / 9.1% | 4,301 / 3,953 |
| MQ10 / 2³¹−1 | 1 / 16 | 13.0% / 13.1% | 13.9% / 12.5% | 52.5% / 54.4% | 13.6% / 12.0% | 6.9% / 8.0% | 4,174 / 3,957 |

- **Interning dominates everywhere.** The `MonomialMap` probe and insert run once per row term:
  14.6 M terms on Eco-12, 16.1 M on MQ11. The reducer search, which plan §6.3 singled out as
  different work from conventional F4's, is ≤ 13%.
- **Frequency.** The symbolic thread's CPU drops from 4.2–4.5 GHz with no team (one worker) to
  3.95–4.0 GHz with a team of 8 or 16, 5–11% lower on every row. The CPU set's sampled mean drops much
  further (to 1.8–2.3 GHz) because it averages in idle team cores. Eco-12's timed symbolic grows
  19% from 1 to 16 workers and MQ10's 14–17%, so clock explains about half the growth. The
  remainder scales with team size and is not clock. Separating it is #933's job.

### 4.1 The split build's symbolic path is itself faster on two rows

The split build moves each row's products into a scratch buffer and then interns them, where the
shipping loop interns each product as it is formed. A paired A/B against the instrument build (same
source, feature off, interleaved in one session, n = 5):

| Row | Workers | Symbolic, shipping loop | Symbolic, unfused | Ratio [95%] | Process wall ratio [95%] |
|---|---:|---:|---:|---:|---:|
| Eco-12 / 2⁶⁴−353 | 1 | 512 | 307 | 0.601 [0.595, 0.617] | 0.932 [0.929, 0.933] |
| | 16 | 552 | 360 | 0.655 [0.647, 0.677] | 0.897 [0.893, 0.906] |
| Katsura-11 / Goldilocks | 1 | 169 | 195 | 1.156 [1.092, 1.159] | 1.024 [1.014, 1.025] |
| | 16 | 185 | 200 | 1.082 [1.069, 1.161] | 1.032 [1.023, 1.044] |
| MQ10 / 32003 | 1 | 216 | 139 | 0.643 [0.638, 0.694] | 0.823 [0.818, 0.842] |
| | 16 | 232 | 159 | 0.686 [0.665, 0.742] | 0.828 [0.807, 0.862] |

The unfused split build is faster even though it clocks every reducer lookup. That is a lead, not
a design. It is row-dependent: it loses on Katsura-11, and it is unexplained (instruction-level
parallelism in the hash probes is one candidate). It is handed to #933 with the records. The
component shares above are the split build's own, so they describe the unfused path.

## 5. Eco-12's ~300 ms outside the four stages

At 16 workers (`cl:16`; medians, ms) the process wall of 1,745 splits as follows:

| Part | ms | What |
|---|---:|---|
| Four stages | 1,446 | symbolic + elimination + bookkeeping + interreduction |
| Engine, outside the stage clocks | 103 | the split build names basis materialization (68 ms); input normalization and the engine drop are under 1 ms |
| Render | 140 | `sig_f4_study` sorting and printing the basis for its SHA-256 (harness) |
| Harness | 41 | argument and input parsing, the JSON report |
| Exec + exit | 19 | process wall − in-process `main` |

The same split holds at one worker (82 / 138 / 42 / 12 ms). On MQ11 the render alone is 467 ms. A
comparand driver that does not render its basis does not pay the render, so process-wall
comparisons carry this harness cost on Zeebra's side. The roughly 35 ms of the 103 ms that
materialization does not explain is spread across batch setup outside the clocks.

## 6. Plan §6.3 re-derived

Eco-12 / 2⁶⁴−353: sig path (en:16) 1,753 ms, symbolic at 16 workers 552 ms, at one worker 462 ms,
conventional F4-16 2,369 ms. The grobx figures are quoted from M31's and M30's sessions, not
re-measured.

| Symbolic at 16 w | Saved ms | Projected wall | ÷ sig now | ÷ conventional F4-16 | ÷ grobx raw, M31 (1,746.5) | ÷ grobx raw, M30 (1,613.7) |
|---|---:|---:|---:|---:|---:|---:|
| growth removed only (462) | 90 | 1,662 | 0.948 | 0.702 | 0.952 | 1.030 |
| 1.5× (368) | 184 | 1,569 | 0.895 | 0.662 | 0.898 | 0.972 |
| 2× (276) | 276 | 1,476 | 0.842 | 0.623 | 0.845 | 0.915 |
| 3× (184) | 368 | 1,384 | 0.790 | 0.584 | 0.793 | 0.858 |
| free (0) | 552 | 1,200 | 0.685 | 0.507 | 0.687 | 0.744 |

MQ10, symbolic needed for T3 (sig ≤ 1.05 × conventional F4-16) by S1 alone:

| Row | Sig 16w | F4-16 | T3 limit | Symbolic now | Symbolic needed | Speedup needed |
|---|---:|---:|---:|---:|---:|---:|
| MQ10 / 32003 | 385 | 240 | 252 | 234 | ≤ 101 | ≥ 2.3× |
| MQ10 / 2³¹−1 | 393 | 226 | 238 | 230 | ≤ 75 | ≥ 3.1× |

At a 1.5× symbolic cut: Katsura-11 / Goldilocks 616 → 555 ms (0.90× sig now), Katsura-11 /
2⁶⁴−353 612 → 550 (0.90×), MQ11 2,144 → 1,973 (0.92×). Eco-12's serial remainder after S1
(bookkeeping + interreduction) is 522 ms. Plan §6.3's table holds to within 0.005 in every ratio.
Its conclusions stand: removing the growth alone is not enough for T2, and MQ10 needs routing
unless S1 reaches 2.3–3.1×. §4.1's unfused path (Eco-12 symbolic 0.65× at 16 workers, about 1.5×)
would by itself sit near the 1.5× row.

## 7. Small controls (#934)

Plan §10.3's default: in-process call time, k calls per process with the cold first call dropped,
the median per process, n ≥ 31 fresh processes, paired per repetition. Measured on katsura-4 with
k = 21 and n = 31:

| Row | Workers | f4 call | en call | en ÷ f4, call [95%] | Half-width | en ÷ f4, process wall [95%] | Half-width | Dispatch |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| katsura-4 / Goldilocks | 1 | 42 µs | 43 µs | 1.005 [1.000, 1.010] | 0.50% | 1.000 [0.990, 1.009] | 1.05% | 0.1 µs |
| | 16 | 47 µs | 47 µs | 0.999 [0.994, 1.002] | 0.54% | 0.998 [0.988, 1.005] | 1.03% | 0.1 µs |
| katsura-4 / 2⁶⁴−353 | 1 | 42 µs | 42 µs | 1.002 [0.996, 1.009] | 0.69% | 1.000 [0.992, 1.016] | 1.61% | 0.1 µs |
| | 16 | 47 µs | 47 µs | 1.001 [0.994, 1.008] | 0.70% | 0.999 [0.991, 1.008] | 0.83% | 0.1 µs |

**Method for every M32 gate on a row under 50 ms:** `sig_f4_study --repeat 21`, n ≥ 31 fresh
processes, the median of the 20 warm calls per process, ratios paired per repetition, process wall
reported beside it, and the dispatch cost (`dispatch_ns`) read on its own for T9. Every half-width
is ≤ 0.70%, inside 2%. At n = 31 process wall happens to resolve too (≤ 1.61%), but with half the
margin. The M31 miss (#934's finding) came from n = 9, not from process wall as such.

## 8. groebner-rs at its best worker count (#935)

Pending.
