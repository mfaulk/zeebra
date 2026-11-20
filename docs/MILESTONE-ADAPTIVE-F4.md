# M32 — Adaptive F4: Parallel Symbolic Preprocessing and Production Qualification

**Status:** §§1–13 are the plan, fixed 2026-11-19 before any M32 measurement and not edited
since. §15 is the integration report (#942) in **draft**, 2026-11-20. It is written from the merged
gate records. The final cohort at F3, Gate Q's outcome, the held-out results and the #937 decision
are marked `TODO(F3)` and are not yet measured or decided.
**Predecessor:** M31 — Signature-F4 Wall-Time Conversion and Competitive Performance
([`MILESTONE-COMPETITIVE-SIGNATURE-F4.md`](MILESTONE-COMPETITIVE-SIGNATURE-F4.md), §15 integration
report; tracker #900, closed).
**Planning base:** `main` at `e59a90a1`. Its timed `src/` differs from M31's final `8715c8ed` only
in doc comments (`src/grobner/sigf4/dispatch.rs`, `src/lib.rs`).
**Measured at:** not measured here. §§2–6 quote `8715c8ed`. §15 quotes M32's gate records, each
at the commit its record names: `7b25a1ee`, `8715c8ed` and `45107ec3` (#939); `8694d172` (#933);
`3d46b15f` (#936); `592653ee` and `62cbe4de` against `ce67df76` (#940); `8544cf24` and `588d2a44`
against `c1d93389` (#927); `f427e8d7` and `f8ec0b4c` (#941, posted on the issue, not yet merged).
Every figure in §§2–6 is quoted from M31's final cohort at `8715c8ed` (evidence and every table in
[`research/m31-final/`](../research/m31-final/README.md)), from
[`m31-sigf4-dispatch.md`](research/m31-sigf4-dispatch.md) (`5bd0db63`), from
[`m31-sigf4-parallel.md`](research/m31-sigf4-parallel.md) (`4b702ea3`), or from the M30 report
(`e4826153`), each named where used. Figures derived in §6.3 are labelled estimates.
**Tracking issue:** [#938](https://github.com/mfaulk/zeebra/issues/938).
**Project:** [Zeebra #7](https://github.com/users/mfaulk/projects/7); label `M32`. Priority is the
Project field (P0 → High, P1 → Medium). A conditional issue carries `blocked` until its gate's
evidence is posted on it. Milestones here are labels and documents, not GitHub milestone objects.

**Focus.** M31 shipped an opt-in signature-F4 path that beats Zeebra's conventional F4 by 1.4–2.2×
on most graded families, but is serial in three of its four stages and loses 1.6–1.7× on MQ10 at
16 workers. M32 removes the largest serial stage, fixes algorithm and worker-count selection, and
decides on evidence whether the adaptive path can become the default for graded orders.

## 1. Vision and executive summary

> **M32 — Adaptive F4.** Make Zeebra's signature-based F4 engine more competitive and reliable by
> removing its largest remaining serial bottleneck, improving algorithm and worker-count selection,
> and establishing whether it can safely become the default for supported polynomial systems.

The questions, in order of priority:

1. Can **parallel signature-aware symbolic preprocessing** substantially reduce complete F4 wall
   time? (S1: #933, then #940)
2. Can an **adaptive dispatcher** reliably choose between conventional and signature F4, and a
   worker count, without material regressions? (S2: #927)
3. Does the implementation **scale better** from 8 to 16 workers?
4. Can the adaptive path be **qualified as the default** for graded orders without compromising
   correctness, resource safety or behaviour on unfavourable inputs? (Q: #941; decision: #937)
5. Does Zeebra's **competitive position** against msolve, grobx and groebner-rs improve? (I: #942)

**Why this shape.** M31's final cohort puts Eco-12's 16-worker signature path at 1,744 ms, of
which symbolic preprocessing is 552 ms, elimination 370, bookkeeping 259 and interreduction 264.
Elimination is already parallel (3.60× over design 1); the other three are serial, and symbolic is
the largest and the only one that *grows* with workers (466 ms at one). MQ10's loss is a
worker-count crossover (§2.3): the signature path wins at one worker and loses from about four,
because its serial symbolic stage (232 of 380 ms) stops it from scaling. So:

- **S1 is the critical-path engineering work.** A 1.5× symbolic cut buys about 10% of Eco-12's
  wall (§6.3). It cannot by itself close MQ10 unless it reaches 2.2–3.0×.
- **S2 is what makes MQ10 safe** in any outcome of S1, by routing on worker count and cheap input
  features.
- **S3 (signature-basis outgrowth) is conditional research**, off the critical path.
- **Q and #937** turn the result into a defensible production-default decision, either way.

The primary measure of success is a materially faster and more reliable F4 with enough evidence to
decide the default — not the number of issues closed.

## 2. Completed M31 results

All figures: M31 final cohort, `8715c8ed`, n = 9 per cell, process wall, fresh processes, arms
rotated, paired 95% bootstrap ([`tables.md`](../research/m31-final/tables.md)), unless stated.
"Sig path" is the opt-in `grobner::f4_signature` with its dispatch.

### 2.1 End-to-end, 16 workers

| Row | Conventional F4-16 ms | Sig path 16w ms | Sig ÷ F4 [95%] | Sig RSS ÷ F4 | Route |
|---|---:|---:|---:|---:|---|
| Eco-12 / 2⁶⁴−353 | 2,372 | 1,744 | 0.737 [0.732, 0.740] | 0.853 | signature |
| Katsura-11 / Goldilocks | 1,359 | 616 | 0.453 [0.451, 0.455] | 0.764 | signature |
| Katsura-11 / 2⁶⁴−353 | 1,344 | 613 | 0.459 [0.453, 0.461] | 0.764 | signature |
| MQ11 / Goldilocks | 4,669 | 2,126 | 0.456 [0.454, 0.459] | 0.939 | signature |
| **MQ10 / GF(32003)** | 241 | 378 | **1.583** [1.561, 1.602] | 0.674 | signature |
| **MQ10 / GF(2³¹−1)** | 226 | 391 | **1.728** [1.717, 1.756] | 0.834 | signature |
| noon-7 / Goldilocks | 193 | 108 | 0.558 [0.546, 0.571] | 0.870 | signature |
| katsura-9 / 2⁶⁴−353 (M31 held out) | 73 | 43 | 0.585 [0.582, 0.596] | 0.921 | signature |
| noon-8 / 2⁶⁴−353 (M31 held out) | 980 | 596 | 0.612 [0.603, 0.621] | 0.818 | signature |
| Cyclic-7 / Goldilocks; / 2⁶⁴−353 | 145; 146 | 145; 146 | 0.996; 1.001 | 1.00 | conventional (`DegreeSpread`) |
| katsura-4 / Goldilocks; / 2⁶⁴−353 | 6; 6 | 6; 6 | 0.999; 1.002 | 0.99 | conventional (`Small`) |

At one worker the sig path is 0.096–0.48× conventional F4-1 on every signature-routed row, MQ10
included. Every output was one basis digest per row across 108 children and independently
certified; no child stopped on a budget.

### 2.2 Where the 16-worker wall goes (signature cascade, stage medians, s)

| Row | Workers | Wall | Symbolic | Elimination | Bookkeeping | Interreduction |
|---|---:|---:|---:|---:|---:|---:|
| Eco-12 / 2⁶⁴−353 | 1 (design 1) | 2.567 | 0.466 | 1.333 | 0.231 | 0.271 |
| | 4 | 1.863 | 0.490 | 0.578 | 0.244 | 0.262 |
| | 8 | 1.755 | 0.514 | 0.430 | 0.253 | 0.267 |
| | 16 | 1.752 | 0.552 | 0.370 | 0.259 | 0.264 |
| Katsura-11 / Goldilocks | 1 → 16 | 0.946 → 0.617 | 0.156 → 0.184 | 0.453 → 0.076 | 0.015 → 0.018 | 0.110 → 0.113 |
| MQ11 / Goldilocks | 1 → 16 | 5.340 → 2.129 | 0.439 → 0.514 | 3.643 → 0.330 | 0.027 → 0.030 | 0.511 → 0.505 |
| MQ10 / GF(32003) | 1 → 16 | 0.470 → 0.380 | 0.202 → 0.232 | 0.190 → 0.056 | 0.019 → 0.020 | 0.023 → 0.025 |
| Cyclic-7 / Goldilocks (engine forced) | 1 → 16 | 0.585 → 0.669 | 0.120 → 0.133 | 0.058 → 0.077 | 0.330 → 0.369 | 0.020 → 0.021 |

Observations that drive M32:

- Symbolic preprocessing is the largest single stage on Eco-12 at 16 workers and **grows** with the
  worker count on every substantial row (Eco-12 +18%, MQ11 +17%, MQ10 +15%). M31 did not attribute
  it; lower single-core boost beside an active team has been seen on this host before.
- 8 workers capture the whole wall gain on Eco-12 (1.755 → 1.752 s) and Katsura-11, although
  elimination keeps scaling. MQ11 still gains 8% from 8 to 16.
- About 300 ms of Eco-12's 1,752 ms process is outside the four stages (startup, parsing,
  minimal-basis selection, output) and is unattributed.

### 2.3 The MQ10 crossover (process wall ms, conventional F4 vs signature cascade)

| Workers | MQ10 / 32003 F4 | MQ10 / 32003 sig | ratio | MQ10 / 2³¹−1 F4 | MQ10 / 2³¹−1 sig | ratio |
|---:|---:|---:|---:|---:|---:|---:|
| 1 | 1,085 | 470 (design 1) | 0.43 | 935 | 447 | 0.48 |
| 4 | 383 | 374 | 0.98 | 341 | 374 | 1.10 |
| 8 | 274 | 359 | 1.31 | 249 | 365 | 1.47 |
| 16 | 241 | 380 | 1.58 | 226 | 393 | 1.74 |

Ratios here are median ÷ median from the wall table, not paired; the paired 16-worker figures are
§2.1's. Conventional F4 scales 4.5× (32003) and 4.1× (2³¹−1) on MQ10; the signature path scales
1.25×. M31's dispatch rule (variables, nonzero generators, least nonlinear and greatest degree; no
worker count) had no feature separating MQ10 from katsura-9 and noon-8 without fitting to MQ10
(`m31-sigf4-dispatch.md` §5).

### 2.4 Competitive position (M31 §15.2; mode and worker counts are part of every figure)

| Row | Comparand, best supported configuration | Sig 16w ÷ comparand [95%] | Equal-worker ratio |
|---|---|---:|---:|
| MQ11 / Goldilocks | grobx raw randomized, 1w | **0.679** [0.645, 0.720] | 1.711 |
| Eco-12 / 2⁶⁴−353 | grobx raw randomized, 1w | 0.999 [0.948, 1.063] | 1.464 |
| Katsura-11 / 2⁶⁴−353 | grobx raw randomized, 1w | 1.056 [0.989, 1.106] | 1.578 |
| Eco-12, Katsura-11, MQ11 | groebner-rs, 1w (wide adapter's only count, #935) | 0.22–0.55 | 0.41–0.80 |
| MQ10 / 32003; / 2³¹−1 | msolve exact, 8w; 4w | 3.233; 2.392 | 3.067; 2.291 |
| MQ10 / 32003; / 2³¹−1 | groebner-rs, 8w | 4.311; 3.977 | 4.090; 3.718 |

These are not equal-worker or equal-guarantee comparisons: grobx raw is randomized and
uncertified; Zeebra is deterministic and its output certified outside the solve. grobx raw ran 4–9%
slower in M31's session than in M30's with the same executable (Eco-12 1,746.5 against 1,613.7 ms),
so a ratio against grobx carries that session sensitivity (§6.4).

### 2.5 What M31 established and what it left

Established: a 6.5–22.8× coefficient-work saving with identical bases (unchanged in M31); a proven,
adversarially tested parallel cascade (Theorem 1 of
[`m31-parallel-signature-elimination.md`](research/m31-parallel-signature-elimination.md),
3.60× elimination on Eco-12); typed refusals for non-graded orders; size-limit fallback to
conventional F4; a certification deadline; dispatch cost 0.2–3.3 µs.

Left open, each now an M32 package: the serial symbolic stage (#933), MQ10 (#927), signature-basis
outgrowth (Eco-12 1,885 elements for 743 reduced, Cyclic-7 3,083 for 209, MQ10 585 for 247; #936),
the small-control measurement method (#934), groebner-rs's best worker count (#935), and the
default decision (#937).

## 3. Current architecture and bottlenecks

- **Entry point.** `grobner::f4_signature` / `f4_signature_reported`
  (`src/grobner/sigf4/dispatch.rs`). `signature_route` reads four features in one pass and returns
  `Shipping(Linear | Small | DegreeSpread)` or `Signature`; thresholds `SIGNATURE_MIN_VARIABLES = 6`
  and `SIGNATURE_MAX_DEGREE_SPREAD = 1`. More than one worker selects the parallel cascade at the
  caller's full worker count. Lex, `Weighted` and `Block` return `SigF4Error::Unsupported`.
  The library default (`grobner::f4`, `f4_with_options`) is conventional F4 and is untouched.
- **Signature engine** (`src/grobner/sigf4/engine.rs`, design 1; `claim.rs`, the parallel cascade).
  Per batch: symbolic preprocessing, elimination, bookkeeping (rewrite and syzygy stores, pairs),
  then a final interreduction.
- **Signature symbolic preprocessing** (`Engine::symbolic`, `engine.rs`). A breadth-first closure
  over a worklist of column monomials: each new monomial is interned in a `MonomialMap`, then
  `reducer(m)` finds the **least-ratio** basis element whose lead divides `m` by a linear scan over
  the elements' lead masks, cached per monomial and rescanning only elements added since; the
  reducer's multiplied tail is interned and appended to the worklist. The columns are then sorted
  by the monomial order and the row handles remapped. Entirely serial; it mutates the reducer
  cache.
- **Conventional F4 symbolic preprocessing** uses #861's parallel interning
  (`src/grobner/f4/symbolic_intern.rs`), which took M30's Eco-12 stage from 992.6 to 256.6 ms at 16
  workers and MQ10 / 32003 from 92.6 to 45.0 ms (`e4826153`). Its reducer choice is not
  signature-aware, and M31's rules kept sig-F4 PRs from modifying it.
- **Input analysis** exists already: `grobner::planning::analyze` returns `SystemShape` (variables,
  generators, terms, degree histogram, per-variable occurrences) in one pass over the terms.

Bottlenecks in order of measured size at 16 workers (Eco-12): symbolic 552 ms (serial, growing);
elimination 370 (parallel); unattributed process overhead ~300; interreduction 264 (serial);
bookkeeping 259 (serial, fed by outgrowth).

## 4. Hypotheses and unknowns

### 4.1 Hypotheses (unmeasured; each names what falsifies it)

- **H1 — parallel symbolic closure.** For a batch, the column set and each column's least-ratio
  reducer are functions of the batch's targets and of the basis, which does not change during
  symbolic preprocessing. A frontier-parallel closure (reducer lookup, multiplication and interning
  on workers; deterministic merge) therefore produces the serial closure's rows, and on Eco-12 has
  enough frontier width to cut the stage ≥ 2× at 16 workers. *Falsified* if #933's replay of real
  Eco-12 batches bounds the speedup below 2.0×, or the correctness argument leaves a load-bearing
  obligation open (Gate P).
- **H2 — the worker-count growth is not work.** Most of symbolic's growth from 1 to 16 workers
  (Eco-12 +86 ms) is CPU frequency beside an active or recently active team, or team overhead, not
  extra symbolic work. *Falsified* if the growth persists with the team parked and the frequency
  recorded flat.
- **H3 — serial closure cost.** The signature closure's serial cost per row exceeds conventional
  F4's (MQ10: about 200 ms against 92.6 ms serially, at different commits, so an estimate), and
  reducer search dominates it. If #939's split confirms reducer search ≥ 30% of the stage, a
  divisibility index belongs inside S1's one design. *Falsified* if reducer search is < 30%.
- **H4 — worker-aware dispatch.** The worker count plus cheap `SystemShape` features (density
  against the monomials of each degree, size, degree histogram) route MQ10 to conventional F4 at
  the worker counts where it loses, without moving any favourable dev row off the signature engine.
  *Falsified* if Gate R fails, or leave-one-family-out validation misroutes a row at a cost
  > 5%.
- **H5 — outgrowth is reducible.** A sound subset of the signature basis suffices for the rewrite
  and syzygy criteria and cuts Eco-12 bookkeeping ≥ 30%. *Falsified* by #936's research note.

### 4.2 Not hypotheses (settled; do not reopen without new evidence)

- Displacement-based parallel elimination was rejected with open load-bearing obligations (#902
  §10). The parallel cascade (`claim.rs`) is the elimination design.
- In-solve signature → F4 handover is net-negative where grobx fired it (#716); excluded.
- Randomized row combinations and uncertified zero tests are excluded (M30 §13; #714).
- Conventional F4's remaining serial symbolic pieces cap at 6.6% of MQ10's F4 call (#896); #888 is
  independent backlog, not M32.

### 4.3 Unknowns M32 must answer

1. What the symbolic stage's time is made of (reducer search, interning, multiplication, sort) and
   why it grows with workers (#939 measures, #933 interprets).
2. Whether S1 alone closes MQ10 (needs 2.2× at 32003 and 3.0× at 2³¹−1; §6.3).
3. Where Eco-12's ~300 ms outside the four stages goes (#939).
4. Whether any cheap feature separates MQ10 from katsura-9 and noon-8 without overfitting (#927).
5. Whether qualification on held-out systems, both graded orders, every field width and every
   budget uncovers behaviour gaps the M31 corpus did not (#941).

## 5. Scope, exclusions and the cryptanalysis boundary

**In scope:** signature-aware symbolic preprocessing; dispatch and worker-count policy; a bounded
outgrowth study; production qualification and a default-off integration path; the final cohort.

**Excluded:** a second parallel-symbolic design without an owner decision on #938; a new solver
subsystem; F5, Matrix-F5 or GVW engines; any FGLM rewrite; GPU; out-of-core; a broad polynomial
or monomial representation rewrite; randomized or uncertified reduction; conventional-F4
optimization campaigns; unbounded benchmark campaigns; a default change before Gate Q and the
owner's decision on #937.

**Public / private boundary.** Zeebra is the public general-purpose library; the private
`cryptanalysis` repository owns primitive models, attack formulations, reproductions of published
attacks, target selection and their benchmark campaigns. M32:

- uses only public generic systems (Katsura, Eco, Cyclic, Noonburg, random dense MQ) for every
  performance and correctness figure;
- does not depend on any cryptanalysis milestone, and no M32 package needs access to that
  repository;
- contains no primitive model, attack implementation, private dataset or private result;
- accepts upstream requests from cryptanalysis as ordinary Zeebra issues that state a generic
  requirement with a **public reproducer**. Such a request enters M32 only by a planning decision
  recorded on #938, and only if it fits §11's caps.

**Licensing.** grobx is GPL-3.0-only and Zeebra is MIT: grobx's papers, manual and measurements
are references, never a source of code ([`external-provenance-policy.md`](research/external-provenance-policy.md)).
Every signature change is implemented independently from published algorithms.

## 6. Success tiers (fixed now; scored as written; not rewritten after measurement)

#942 scores each criterion **met**, **missed** or **not attempted**, with the reason. Unless stated,
a criterion is read at the 16-worker operating point, n ≥ 9 per arm, interleaved fresh processes,
paired 95% bootstrap of the median (20,000 draws), under §10's precision rule. "M31 reference" is
the code at `8715c8ed` built in the same campaign. "Adaptive path" is `f4_signature` at the final
revision.

### 6.1 Minimum — decisive engineering evidence

1. **Baseline.** #939 freezes a reproducible M32 baseline, reproduces M31's §2.1 ratios within 3%
   on every substantial row (or explains the difference), publishes the symbolic-stage component
   split and the re-derived §6.3 ceilings, and completes #934 and #935.
2. **Parallel symbolic, investigated.** #933 publishes the attribution of symbolic's worker-count
   growth, one design with its correctness argument, a measured ceiling and a Gate P read.
3. **MQ10.** #927 passes Gate R, or documents rigorously why no admissible rule does.
4. **Safety of anything adopted.** Every merged optimization passes §9 and the resource checks.
5. **Decision.** #937 records the production-default decision and its reasons, either way.
6. **Report.** #942 publishes the report, including every negative and stopped result.

Minimum does not require any change to the public default.

### 6.2 Target — a meaningfully faster and more reliable adaptive F4

- **T1. Symbolic stage, Eco-12 / 2⁶⁴−353:** M31 reference ÷ final, median ≥ 1.5× and 95% lower
  bound ≥ 1.4×.
- **T2. Eco-12 complete wall:** adaptive path ÷ M31 reference `f4_signature`, median ≤ 0.90 and
  95% upper ≤ 0.92.
- **T3. MQ10, both fields:** adaptive path ÷ conventional F4 at the same revision, 95% upper ≤ 1.05
  at **1, 4, 8 and 16** workers (a worker-aware fix must not create a loss at an intermediate
  count).
- **T4. Gains preserved:** on Katsura-11 (both fields) and MQ11, adaptive ÷ conventional median ≤
  0.50; on Eco-12 ≤ 0.70; and on every signature-routed dev row, adaptive ÷ M31 reference 95%
  upper ≤ 1.03.
- **T5. No regressions:** on every dev control and every held-out row, adaptive ÷ conventional 95%
  upper ≤ 1.05 at 1 and 16 workers; rows under 50 ms by #934's method.
- **T6. Memory:** peak RSS ≤ 1.25× conventional F4 on every row, and ≤ 1.10× the M31 reference on
  every signature-routed row.
- **T7. Correctness:** §9's complete contract on every output; equality with conventional F4;
  independent certification of every substantial output.
- **T8. Resource and behaviour:** worker, wall, matrix and live-memory budgets honoured on every
  route, with actual threads never above `max_workers`; typed errors; cancellation at safe points;
  no panic or divergence under adverse schedules at every worker count 1–16.
- **T9. Dispatch cost:** ≤ 50 µs, and ≤ 0.1% of wall on every row of ≥ 50 ms.
- **T10. Qualified:** Gate Q (#941) passes, and #937 records a default policy with reasons.

**Why these thresholds.** T1 and T2 are the brief's targets, and §6.3 shows they are consistent:
1.5× on symbolic alone gives 0.894. T2's upper bound of 0.92 is affordable because Eco-12's
interval half-width was 0.2–0.5% in M31. T3 is the brief's 5% bound, extended to the worker counts
where §2.3 shows the crossover. T4's absolute bounds sit 4–5 points above M31's measured 0.453–0.459
and 0.737, so they detect a lost gain, not noise. T6 keeps M31's 1.25× bound to conventional and
adds a 1.10× bound against M31, the slack #904 needed for phase-A scratch (1.039×).

### 6.3 Feasibility arithmetic (estimates from §2.2's medians; additive Amdahl, not predictions)

**Eco-12 / 2⁶⁴−353**, sig path 1,744 ms at 16 workers, symbolic 552 ms, everything else unchanged:

| Symbolic at 16 w | Saved ms | Projected wall | ÷ M31 sig | ÷ conventional F4-16 (2,372) | ÷ grobx raw, M31 session (1,746.5) | ÷ grobx raw, M30 session (1,613.7) |
|---|---:|---:|---:|---:|---:|---:|
| growth removed only (466) | 86 | 1,658 | 0.951 | 0.699 | 0.949 | 1.027 |
| 1.5× (368) | 184 | 1,560 | 0.894 | 0.658 | 0.893 | 0.967 |
| 2× (276) | 276 | 1,468 | 0.842 | 0.619 | 0.841 | 0.910 |
| 3× (184) | 368 | 1,376 | 0.789 | 0.580 | 0.788 | 0.853 |
| free (0) | 552 | 1,192 | 0.683 | 0.503 | 0.683 | 0.739 |

Removing the growth alone is not enough for T2; parallelism is needed. #861 reached 3.9× on
conventional F4's Eco-12 symbolic stage, so 1.5–3× is a plausible range, not a promise: the
signature closure's least-ratio reducer search is different work.

**MQ10**, symbolic needed for T3 by S1 alone (all else unchanged):

| Row | Sig 16w | F4-16 | T3 limit (1.05×) | Symbolic now | Symbolic needed | Speedup needed |
|---|---:|---:|---:|---:|---:|---:|
| MQ10 / 32003 | 380 | 241 | 253 | 232 | ≤ 107 | ≥ 2.2× |
| MQ10 / 2³¹−1 | 393 | 226 | 237 | 230 | ≤ 76 | ≥ 3.0× |

At 1.5× MQ10 would still be about 1.26× and 1.40× conventional. **Routing is therefore required**
unless S1 far exceeds its target; routing MQ10 to conventional F4 where it loses gives about 1.00×
(the shipping-routed rows measured 0.996–1.002 in M31). S1 still matters for MQ10: every gain it
makes moves the crossover to more workers.

**Other rows at a 1.5× symbolic cut:** Katsura-11 / Goldilocks 616 → 555 ms (0.90×); MQ11 2,126 →
1,955 ms (0.92×). After S1, the serial remainder on Eco-12 is bookkeeping + interreduction (523 ms)
and unattributed process overhead (~300 ms), so further gains beyond about 0.68× need work outside
M32 or S3.

### 6.4 Stretch — frontier competitiveness (each scored separately)

- **S-a.** Eco-12 / 2⁶⁴−353: adaptive path at 16 workers ÷ grobx raw randomized at its best
  supported configuration (one worker), **measured in the same session**, median ≤ 0.90 and 95%
  upper ≤ 0.95. Reported as "Zeebra 16w vs grobx 1w (best supported configuration)", with the
  equal-worker row and the guarantee difference. Against M31's grobx session this is reachable at
  about 1.5×; against M30's it needs about 2.1× (§6.3), which is why it is a stretch and not T2.
- **S-b.** On Eco-12 or Katsura-11: adaptive path 16w ÷ 8w median ≤ 0.90 and 95% upper ≤ 0.93
  (M31: 0.998 and 1.01). MQ11 does not count: it was already 0.92.
- **S-c.** The adaptive path becomes the supported default for graded orders, if Gate Q passes and
  the owner approves on #937.
- **S-d.** If #936 is admitted at Gate G: a further ≥ 5% on Eco-12's complete wall from reduced
  outgrowth, or Cyclic-7 through the engine at ≤ 1.00× conventional F4 at 16 workers.

An advantage over a randomized, uncertified solver is never reported as an advantage under equal
guarantees.

## 7. Workstreams and deliverables

| WP | Issue | New / reused | Priority | Kind | Blocked by |
|---|---|---|---|---|---|
| Tracker | [#938](https://github.com/mfaulk/zeebra/issues/938) | new | High | tracking (`blocked`) | its children |
| M32-0 baseline, corpus, cost model | [#939](https://github.com/mfaulk/zeebra/issues/939) | new | High (P0) | required | — |
| ↳ small-control method | [#934](https://github.com/mfaulk/zeebra/issues/934) | reused (Low → Medium) | Medium | required, under #939 | — |
| ↳ comparand worker counts | [#935](https://github.com/mfaulk/zeebra/issues/935) | reused (Low → Medium) | Medium | required, under #939 | — |
| M32-S1a attribution, design, Gate P | [#933](https://github.com/mfaulk/zeebra/issues/933) | reused (Medium → High) | High (P0) | required, research | — (timing uses #939's freeze) |
| M32-S1b parallel symbolic implementation | [#940](https://github.com/mfaulk/zeebra/issues/940) | new | High (P0) | **conditional** (`blocked`) | #939, #933 (Gate P) |
| M32-S2 adaptive dispatch, worker policy | [#927](https://github.com/mfaulk/zeebra/issues/927) | reused (unset → High) | High (P0) | required (`blocked` until the corpus pin) | #939 |
| M32-S3 signature-basis growth | [#936](https://github.com/mfaulk/zeebra/issues/936) | reused (Low → Medium) | Medium (P1) | conditional research | — |
| M32-Q production qualification | [#941](https://github.com/mfaulk/zeebra/issues/941) | new | Medium (P1) | conditional (`blocked`) | #927, #940 |
| Default-engine decision | [#937](https://github.com/mfaulk/zeebra/issues/937) | reused | Medium (P1) | decision (`blocked`) | #941 |
| M32-I final cohort and report | [#942](https://github.com/mfaulk/zeebra/issues/942) | new | High (P0) | closeout (`blocked`) | all of the above |

Each issue's body carries its full deliverables, acceptance criteria, gate and caps; the sections
below are the plan-level summary.

### 7.1 M32-0 — baseline, corpus pin and performance model (#939; #934, #935)

Freeze the M31 reference (`8715c8ed`) and the M32 baseline at an explicit `main` commit. **First
deliverable:** pin §10.1's development and held-out sets by canonical SHA-256 and post the pin on
#927, which unblocks S2. Then: the baseline cohort (conventional F4 and `f4_signature` at 1/4/8/16
workers, M31 reference beside it, every dev row, n = 9, every §10.6 field recorded); the symbolic
stage split into reducer search, interning, multiplication and sort at four worker counts, with the
symbolic thread's CPU frequency with and without an active team; the attribution of Eco-12's ~300 ms
outside the stages; §6.3 re-derived. #934 fixes the small-control method (§10.3) and #935 measures
groebner-rs at 1/4/8/16 workers on the wide rows.

### 7.2 M32-S1 — parallel signature-aware symbolic preprocessing (#933 → #940)

**#933 (design and Gate P).** Attribute the growth with workers, separating CPU frequency,
allocator contention, cache effects, team overhead and symbolic work (H2). Compare per-row serial
cost to conventional F4's closure (H3). Select **one** design: which operations run concurrently
(reducer lookup against the fixed basis, multiplication, interning, column sort), how the reducer
cache is updated, and whether `symbolic_intern.rs` is reused unchanged, generalized in a separate
PR, or not used. Write the correctness argument (§9.2) before any substantial implementation.
Replay real Eco-12 and MQ10 batches for a ceiling. A scheduling-only change that removes the
growth without touching the algebra (for example parking the elimination team during symbolic) may
land under #933 if attribution supports it, gated by #940's Gate S rows.

**#940 (implementation and Gate S).** Build the selected design in `src/grobner/sigf4/`, measured
through the complete `f4_signature` entry point, never a microbenchmark alone: Eco-12 stage and
wall (T1, T2), a worker curve 1/2/4/8/16 on Eco-12 and MQ10 with stage clocks, no regression on the
dev corpus, MQ10 re-read on #927, and every §9.2 test.

### 7.3 M32-S2 — adaptive algorithm and worker-count selection (#927)

Three distinct decisions, each reported in `SignatureDispatch`: conventional vs signature F4;
serial vs parallel cascade; the team size actually used, within the caller's `max_workers` and
never above it. Features are pre-solve only (`planning::analyze`'s `SystemShape` plus the worker
count and field width); their own cost is reported. The rule is fitted on the dev corpus only, with
leave-one-family-out validation and at most two revisions after the first dev read; the held-out
set is not read by #927. If no feature separates MQ10 without a threshold fitted to MQ10 alone, a
simple conservative rule with its reason recorded is the expected result, not a classifier. Gate R
(§8.2) is read on dev rows; #941 re-checks the thresholds once on the merged engine if #940 merges
later, and reads the held-out set.

### 7.4 M32-S3 — signature-basis growth and bookkeeping (#936, conditional)

A research note first (`docs/research/m32-signature-basis-growth.md`): which elements the rewrite
and syzygy criteria actually consult (instrumented counts on Eco-12, Cyclic-7, MQ10); which could be
stored compactly, lazily or discarded, with a soundness argument from the published algorithms;
and a cost model. Prototype only through Gate G. S3 never delays S1 or S2, and a justified negative
result completes it.

**Result (2026-11-19):** Gate G failed. The outgrowth is the unique minimal signature basis, and no
element can be discarded. The exact bookkeeping options project 3.1% of Eco-12's 16-worker wall,
and Cyclic-7's floor is 1.92× conventional F4. H5 is falsified. See
[`m32-signature-basis-growth.md`](research/m32-signature-basis-growth.md).

### 7.5 M32-Q — production qualification (#941) and the default decision (#937)

#941 qualifies the merged S1 + S2 path at freeze F2 (§8.3): correctness against conventional F4 and
independent references; grevlex and graded-lex; GF(32003), GF(2³¹−1), Goldilocks, 2⁶⁴−353; 1/4/8/16
workers; small and unfavourable systems; held-out rows (read once); time, matrix, basis-size,
live-memory and certification limits; cancellation; typed partial results; fallback; determinism;
and an explicit, default-off option by which `f4_with_options` and the solvers on it route graded
orders through the adaptive path. Lex, `Weighted` and `Block` keep their algorithm and documented
semantics on every public API. #941 posts its report and a recommendation on #937.

#937 stays the **decision**: the owner promotes the path to the default for graded orders, or
keeps it opt-in with reasons and follow-up issues. A default flip is its own PR citing #941.

### 7.6 M32-I — final cohort and integration report (#942)

At freeze F3: the M31 reference, conventional F4 at the final revision, the final adaptive path at
1/4/8/16 workers, the signature engine forced at 1 and 16 workers, and the comparands (msolve exact
where the characteristic is below 2³¹, grobx raw randomized and certified, groebner-rs at its best
measured worker count). §13 is the template. No optimization starts from #942.

## 8. Dependencies, gates and freezes

### 8.1 Graph

```
#939 M32-0 freeze + corpus pin ──┬──────────────► #927 S2 dispatch ──── Gate R ─────────┐
  ├─ #934 small-control method   │                                                       │
  └─ #935 comparand workers      │                                                       ▼
                                 ├──► #933 S1a design ── Gate P ──► #940 S1b ── Gate S ──► #941 Q ── Gate Q ──► #937 decision
                                 │                                                                                 │
#936 S3 research note ── Gate G ── (prototype only if admitted; after #940 if it touches engine.rs) ──────────────┤
                                                                                                                   ▼
                                                                                            #942 M32-I ── Gate F
```

No cycles. **Critical path:** #939 → #933 → Gate P → #940 → #941 → #937 → #942. #927 runs beside
#933/#940 once the corpus is pinned; #936 runs beside everything. #934 and #935 must close before
any gate that reads a small row or a groebner-rs comparison.

### 8.2 Gates

| Gate | Read on | Passes if | If it fails |
|---|---|---|---|
| **P** (feasibility) | #933 | correctness argument with no load-bearing open obligation; projected Eco-12 symbolic ≥ 2.0× at 16 w from replayed batches; projected Eco-12 wall ≤ 0.88× M31 reference | #940 closes not planned with the evidence; #927 resolves MQ10 by routing; report |
| **S** (prototype) | #940 | T1 and T2 on #940's head vs merge base; dev-corpus head ÷ base 95% upper ≤ 1.05 at 1 and 16 w; RSS ≤ 1.10× base; every §9.2 test | #940 closes with its negative result; no second design without an owner decision on #938 |
| **R** (routing) | #927 | T3 at 1/4/8/16 w on dev rows; favourable dev rows new ÷ M31 entry 95% upper ≤ 1.03; Cyclic-7 and small controls ≤ 1.05 vs conventional; T9 | #927 documents the blocker; #941 qualifies the path with the M31 rule and MQ10 listed as a known loss |
| **G** (outgrowth) | #936 | soundness argument; projected Eco-12 wall saving ≥ 5% or Cyclic-7 engine ≤ 1.00× conventional at 16 w; no conflict with #940 | #936 closes completed with its negative result |
| **Q** (qualification) | #941 | T3–T9 at F2; every §9 and behaviour check; held-out rows ≤ 1.05 at 1 and 16 w; no default changed | the path stays explicit opt-in; each failing criterion gets a follow-up issue |
| **Decision** | #937 | owner records promote or keep opt-in, citing Gate Q | — (either outcome completes it) |
| **F** (closeout) | #942 | report complete per §13 | — |

Gates are read once, as written. Re-running a cell until it passes is resampling and is not done
(§10.3 has the only admitted extension).

### 8.3 Freezes and changes to `main`

- **F0 — baseline** (#939): the M31 reference `8715c8ed` and the M32 baseline commit.
- **F1 — per gate:** each gate builds its head **and** its merge base (or F0) from `git archive`
  into separate private target directories, interleaved in one campaign; never against a published
  figure.
- **F2 — qualification** (#941): a pinned commit after #940 and #927 have merged or closed.
- **F3 — final** (#942): the final revision, with F0 rebuilt beside it.
- **When `main` moves.** Gates are read against conventional F4 built from the evaluated tree. If a
  change to measured paths (`src/grobner/`, `src/linalg/`, `src/fields/`, `src/poly/`) merges
  between F2 and F3, #942 reports against both and records the `git log F2..F3 --numstat` on those
  paths; Gate Q is re-read only if `src/grobner/sigf4/` or the dispatch changed. Measured commits
  are tagged `measured/<issue>-<slug>` before squash-merging.
- Independent backlog that may move the conventional arm (#877 tail-only interreduction, #888,
  #894, #918) is read under this rule; none of it is M32 work, and none of it may share a PR with
  M32 work.

### 8.4 Effort and resource caps (predeclared)

| Package | Cap |
|---|---|
| #939 | 4 sessions; instrument code ≤ 400 net lines; no library behaviour change |
| #933 | 4 sessions; replay/instrument code ≤ 600 net lines behind `research-sigf4` |
| #940 | **one design**; ≤ 1,500 net lines under `src/` excluding tests; ≤ 8 sessions to a correct end-to-end result, ≤ 12 total |
| #927 | ≤ 600 net lines; ≤ 5 sessions; ≤ 2 rule revisions after the first dev read |
| #936 | note ≤ 3 sessions; prototype (if admitted) ≤ 1,000 net lines, ≤ 5 sessions |
| #941 | ≤ 1,200 net lines; ≤ 6 sessions; one re-fit of #927's thresholds |
| #942 | 3 sessions; no library change |
| Benchmarks | §10's repetitions and budgets; one campaign on the machine at a time |

Exceeding a cap is an owner decision recorded on #938, not an implicit extension.

## 9. Correctness and resource-safety requirements

### 9.1 Contract for every output (as M31 §9.1)

1. **Equality:** the reduced basis equals conventional F4's, coefficient for coefficient, on every
   corpus output and at every worker count.
2. **Gröbner and reduced:** reducedness and Buchberger's criterion over all pairs, by
   `certify_f4_output` or grobx certified mode.
3. **Ideal equality both ways:** input ⊆ ⟨G⟩ by the certificate; ⟨G⟩ ⊆ input by equality with an
   independently computed reduced basis (Singular on MQ and small rows, grobx certified on the wide
   rows, `buchberger_reference` on the smallest). Agreement between two Zeebra engines alone is not
   evidence.
4. **Signature invariants** under `SigF4Options::checked()` on the correctness corpus.

### 9.2 Parallel symbolic preprocessing (#933 argues, #940 tests)

- For every batch, the column set and the multiset of rows `(signature, multiplier, source)`, with
  each column's reducer the least-ratio element whose lead divides it, equal the serial closure's,
  for every worker count and schedule. Row order may differ only through a canonicalization that a
  per-batch oracle test checks; the batch's elimination outcome must then equal the serial
  engine's.
- **Final-basis equality alone is not accepted** as evidence for any optimization that changes
  intermediate rows or signatures; such a change needs a mathematical justification and the
  per-batch oracle.
- Concurrent updates of the reducer cache and of the interning tables are either serialized or
  shown not to change any lookup's result.
- Deterministic adverse schedules (seeded yields, forced interleavings) at every worker count 1–16,
  not only repeated runs. Wall-budget cancellation at safe points inside the closure; scratch and
  shared tables charged to `SigF4Options::max_live_bytes`; typed budget errors. No `unsafe`
  without a written invariant.

### 9.3 Dispatch and qualification (#927, #941)

- The route never changes the output: every route returns the identical reduced basis.
- The actual team size is at most the caller's `max_workers`; wall, matrix, basis-size and
  live-memory budgets mean the same on every route; size-limit fallback stays typed and uses only
  the remaining wall budget; time and certification budgets are never fallen back.
- Non-graded orders keep their existing algorithm on every public API; `f4_signature` keeps its
  typed `Unsupported`.

### 9.4 Fields and orders

GF(32003), GF(2³¹−1), Goldilocks and 2⁶⁴−353 in the corpus; at least two fields in every unit test;
grevlex and graded-lex.

## 10. Benchmark methodology and reproducibility

M32 reuses M31's protocol and tools (`m30-protocol.md`; `tools/benchlock.sh`,
`tools/bench-reserve.sh`, `tools/cpu-context.sh`, `tools/rss-guard.sh`,
`examples/sig_f4_study.rs`, `examples/m29_cost_model.rs`, `examples/wide_corpus.rs`,
`research/m31-final/campaign.py`, `comparand-scaling.py`, `wide-corpus.py` and the comparand
adapters). **No new harness.** `tools/check-measurement-provenance.sh` applies to every document.

### 10.1 Corpus

**Development set** (tuning allowed): M31's §10.3 corpus — Eco-12 / 2⁶⁴−353; Katsura-11 /
Goldilocks and / 2⁶⁴−353; MQ11 / Goldilocks; MQ10 / GF(32003) and / GF(2³¹−1); Cyclic-7 /
Goldilocks and / 2⁶⁴−353; katsura-4 / Goldilocks and / 2⁶⁴−353; noon-7 / Goldilocks — plus M31's
held-out katsura-9 and noon-8 / 2⁶⁴−353, **demoted to development** because M31 published their
results.

**Held-out set** (never used for tuning; read once by #941 and again by #942), pinned by #939 by
canonical SHA-256 before any S2 timing, from these candidates built by existing public generators
(`research/wide-corpus/cases.json`, `grobner::benchmark_systems`, `grobner::external::corpus::random_mq_instance`):

| Candidate | Field | Why |
|---|---|---|
| mq-random-10 | Goldilocks | MQ10's family and size at another field width: is the rule field-fitted? |
| mq-random-12 | 2⁶⁴−353 | larger dense MQ, the other side of the crossover |
| dense random MQ, 9 variables, new seed | GF(32003) | smaller dense MQ |
| katsura-10 | GF(2³¹−1) | favourable family, unseen size and field |
| eco-11 | GF(2³¹−1) | favourable family, unseen size and field |
| cyclic-6 | Goldilocks | degree-spread control |

Admission rule (fixed now): a candidate is kept if conventional F4 at 16 workers completes it in 20
ms–60 s under §10.4's budgets and both engines accept its field; otherwise it is dropped with the
reason and **not replaced**. No private or application-specific system enters either set.

### 10.2 Method

- Fresh process per run; arms interleaved and rotated per repetition; n ≥ 9 for every gate and for
  #942, n ≥ 5 for exploration. Medians with 95% bootstrap intervals (20,000 draws); Zeebra ratios
  paired per repetition; a Zeebra ÷ comparand ratio is median ÷ median with independent resampling.
- Worker curves at 1, 4, 8, 16 (and 2 where #940 asks). The primary budget stays **16 workers**;
  32- or 64-worker rows are exploratory and labelled.
- `tools/bench-reserve.sh reserve 1,2` for timed sessions, released at session end; children
  CCD-aligned with `taskset`; `cpu-context` around each child; frequency sampled on the symbolic
  thread where #939/#933 ask.
- Build before reserving: `CARGO_TARGET_DIR=/buildcache/cargo-target/zeebra-<issue>`,
  `TMPDIR=$CARGO_TARGET_DIR/tmp`, `RUSTC_WRAPPER=""`; release, fat LTO, one codegen unit,
  `x86-64-v3`. Every arm from a `git archive` of its commit; SHA-256s recorded.
- One campaign on the machine at a time, under `benchlock`.

### 10.3 Resolving each threshold

- **Precision rule.** A gate is readable only if its 95% interval half-width is at most half the
  distance between its threshold and 1.0 (for a 1.05 bound: ≤ 2.5%; for T2's 0.92: ≤ 4%). If a
  cell misses this after n = 9, **one** predeclared extension block of n = 12 is run and pooled
  (n = 21), decided on the interval width alone, and the gate is read once on the pooled data.
- **Rows under 50 ms process wall** are gated by #934's method. The default, unless #934 measures a
  better one before any M32 gate: in-process call time (k warm calls per process, median per
  process) over n ≥ 31 fresh processes, process wall reported beside it, and the dispatch cost
  gated on its own (T9).
- Stage ratios (T1) come from the timed binary's stage clocks, paired per repetition.

### 10.4 Resource budgets (declared per arm before execution)

Solve 180 s wall and 8 GiB (`rss-guard`); certification 600 s wall at 16 workers, separate from
the solve; grobx certified Eco-12 at 32 GiB, other grobx rows at 8 GiB. A design needing a larger
cap than conventional F4 reports that as a result, not as a cap change.

### 10.5 Fair comparison

Worker counts and modes on every row. Equal-worker and best-supported-configuration rows stay
separate; randomized vs deterministic and raw vs certified are never merged; solver time and
verification time are reported separately; stage speedups are never reported as complete-wall
speedups. A new comparand needs its own adapter, source pin and execution contract under
`tools/external/` before any figure is quoted.

### 10.6 Recorded per child

Solver and source revision; executable SHA-256; compiler and flags; field and representation;
monomial order; algorithm and dispatch decision (with reason and cost); requested and actual worker
count and CPU affinity; process wall; in-process solver time; per-stage times; peak RSS;
coefficient products; signature-basis size; basis digest; certification status and cost; and every
refusal, timeout, budget stop or incomplete result. Every attempt is retained.

## 11. Implementation limits, file ownership and stop rules

**Tracks** (one writer per checkout, own `git worktree`, own branch, own `CARGO_TARGET_DIR`):

| Track | Issues | Owns |
|---|---|---|
| A — symbolic | #933 → #940 | `src/grobner/sigf4/engine.rs` (symbolic), new files under `src/grobner/sigf4/` |
| B — dispatch | #927 | `src/grobner/sigf4/dispatch.rs`, dispatch options; additive changes to `src/grobner/planning/analysis.rs` |
| C — outgrowth | #936 | a research note; a prototype touching `engine.rs` waits for #940 to merge |
| D — measurement | #939, #934, #935, gate campaigns, #942 | `research/`, `docs/research/`, `tools/external/` (#935), flags in `examples/sig_f4_study.rs` |
| E — qualification | #941, then #937 | `src/grobner/mod.rs`, `src/grobner/f4/options.rs` (the default-off option), after #940 and #927 |

Rules:

1. `src/grobner/f4/symbolic_intern.rs` and every other conventional-F4 file change only in a
   separate PR with its own conventional-F4 A/B, never inside a signature-F4 PR.
2. #927 does not edit `engine.rs`; #940 does not edit `dispatch.rs` beyond a call site.
3. `examples/sig_f4_study.rs` is shared: each package adds its own flags; the later rebaser resolves
   conflicts.
4. Read-only work (attribution, the S3 note, comparand sweeps) parallelizes freely; benchmark
   campaigns do not.

**Stop rules.** Gate P fails → #940 closes not planned, #927 carries MQ10, report. Gate S fails or a
cap is hit → #940 closes with its negative result. Gate R fails → #941 qualifies with MQ10 as a
documented loss, or recommends keeping opt-in. Gate G fails → #936 closes with its negative result.
Gate Q fails → the path stays opt-in; no default change. The milestone does not continue because an
ambitious hypothesis failed, and no package substitutes a new algorithm for a failed one.

**Related, independent and not M32:** #877 (tail-only interreduction default, including lex),
#920 (canonical polynomial serialization), #888 (conventional symbolic serial remainder), #894,
#918. Any may be worked; none blocks or shares a PR with M32 work.

## 12. Issue tracking

| WP | Issue | Labels | Priority | Native parent | Blocked by |
|---|---|---|---|---|---|
| tracker | [#938](https://github.com/mfaulk/zeebra/issues/938) | `M32`, `blocked` | High | — | children |
| M32-0 | [#939](https://github.com/mfaulk/zeebra/issues/939) | `M32` | High | #938 | — |
| small controls | [#934](https://github.com/mfaulk/zeebra/issues/934) | `M32` | Medium | #939 | — |
| comparand workers | [#935](https://github.com/mfaulk/zeebra/issues/935) | `M32` | Medium | #939 | — |
| S1a | [#933](https://github.com/mfaulk/zeebra/issues/933) | `M32` | High | #938 | — |
| S1b | [#940](https://github.com/mfaulk/zeebra/issues/940) | `M32`, `blocked`, `performance` | High | #938 | #939, #933 |
| S2 | [#927](https://github.com/mfaulk/zeebra/issues/927) | `M31`, `M32`, `blocked` | High | #938 | #939 |
| S3 | [#936](https://github.com/mfaulk/zeebra/issues/936) | `M32` | Medium | #938 | — |
| Q | [#941](https://github.com/mfaulk/zeebra/issues/941) | `M32`, `blocked` | Medium | #938 | #927, #940 |
| decision | [#937](https://github.com/mfaulk/zeebra/issues/937) | `M32`, `blocked` | Medium | #938 | #941 |
| M32-I | [#942](https://github.com/mfaulk/zeebra/issues/942) | `M32`, `blocked` | High | #938 | #939, #933, #940, #927, #936, #941, #937 |

Dependencies are native "blocked by" relations; the `blocked` label is what keeps
`zb-claim.sh orient` from offering an issue, so whoever posts a gate's passing evidence removes it.
**Provenance:** #927 and #933–#937 were M31 follow-ups under #900 (M31 report §15.8). GitHub allows
one native parent, so they were re-parented to #938 (and #939); each keeps its original body, with
an appended "M32 scope" section, and #900 carries a comment recording the move.

At planning time the claimable issues are #939, #934, #935, #933 and #936; #927 becomes claimable
when #939 posts the corpus pin.

## 13. Integration report template (§15, written by #942)

**15.0 Header.** Final revision, F0 commits, dates, reservation, attempt counts, comparand
identities, evidence path `research/m32-final/`.

**15.1 Status.** One paragraph per tier; then four verdicts kept apart: (1) algorithmic work
(products, reductions to zero, signature-basis size); (2) stage speedups; (3) complete process wall
against conventional F4 and against the M31 reference; (4) competitive position.

**15.2 Primary scoreboard.** Per row: conventional F4 16w; M31 reference sig path 16w; adaptive
path 16w; adaptive ÷ conventional; adaptive ÷ M31; RSS ratios; route; best comparand (mode,
workers), ratio and equal-worker ratio; verification.

**15.3 Worker scaling and stages.** Wall and four stage clocks at 1/4/8/16 workers for both engines
and the adaptive path; the 8 → 16 ratio (S-b).

**15.4 Dispatch.** Every row's route and team size at each worker count, every case that chose
conventional F4 with its reason, dispatch cost, held-out results.

**15.5 Correctness and safety.** Digests, certification status and time, independent references,
budget and cancellation checks, adverse-schedule suite.

**15.6 Success criteria.** A table scoring every §6 criterion met / missed / not attempted, with
evidence.

**15.7 Competitive gap.** Per comparand: best-configuration and equal-worker gaps, the guarantee
difference, and the stage decomposition that explains what remains.

**15.8 Negative, inconclusive and stopped results.** Every failed gate, stopped experiment, refusal
and timeout.

**15.9 Dispositions and follow-ups.** Every M32 issue's outcome; follow-ups filed on Project #7
with Priority and linked to #938.

## 15. Integration report (#942) — DRAFT

> **Draft, 2026-11-20.** This is written from the merged gate records only. Nothing in §15 was
> measured for it. Every `TODO(F3)` marks a figure or verdict that waits for the final cohort at
> freeze F3, for Gate Q (#941), for the held-out read, or for the owner's decision (#937). None of
> them is estimated here. Each figure names its source file and the commit it was measured at.
> Figures posted on an issue but not yet merged say so.

### 15.0 Header

| Item | Value |
|---|---|
| Final revision (F3) | `TODO(F3)` |
| F0 | M31 reference `8715c8ed`; M32 baseline `7b25a1ee`, identical in code ([`m32-baseline.md`](research/m32-baseline.md) §1) |
| F2 | `f427e8d7` (`main` after #950), declared on #941 ([predeclaration](https://github.com/mfaulk/zeebra/issues/941#issuecomment-7042293851)) |
| Gate records | #939 [`research/m32-baseline/`](../research/m32-baseline/README.md); #933 [`m32-parallel-symbolic.md`](research/m32-parallel-symbolic.md); #936 [`m32-signature-basis-growth.md`](research/m32-signature-basis-growth.md); #940 [`research/m32-gate-s/`](../research/m32-gate-s/README.md); #927 [`m32-adaptive-dispatch.md`](research/m32-adaptive-dispatch.md) |
| Dates | gates read 2026-11-19 to 2026-11-20; final cohort `TODO(F3)` |
| Reservation | every M32 campaign so far: CCDs 1–2 (CPUs 8–23) through `tools/bench-reserve.sh`, under `benchlock`. Final cohort `TODO(F3)` |
| Attempts | Gate P 1 read; Gate G 1; Gate S 2 (the second allowed by the owner on #938); Gate R 2 (first read plus revision 1 of 2); Gate Q `TODO(F3)` |
| Comparands | groebner-rs driver `81dc5c4c` (M30-0's), [`research/m32-baseline/README.md`](../research/m32-baseline/README.md) §1. grobx and msolve are not yet run in M32: `TODO(F3)` |
| Evidence path | `research/m32-final/` — `TODO(F3)`, not yet created |

### 15.1 Status

**Minimum.** Items 1–3 are met on the merged record: the baseline (#939), parallel symbolic
investigated to a Gate P read (#933), and MQ10 handled by routing (#927, Gate R passed at
revision 1). Items 4–6 are `TODO(F3)`: the safety checks of the adopted dispatch (Gate Q's `check`
suite), the decision (#937), and this report's final form.

**Target.** The one optimization that cleared its gate is the worker-aware dispatch (#950). The
parallel symbolic closure (#940) passed T1 and T2 twice on its own head but failed Gate S twice,
and it is not merged. So T1 and T2 cannot be met at F3 unless something new merges. Every Target
cell is `TODO(F3)` (§15.6).

**Stretch.** `TODO(F3)`. S-d is not attempted, because Gate G failed.

The four verdicts, kept apart:

1. **Algorithmic work.** No merged M32 change alters the signature engine's algebra. #933's replay
   and #940's head produce the serial closure's rows exactly
   ([`m32-parallel-symbolic.md`](research/m32-parallel-symbolic.md) §4, at `8694d172`). The
   signature basis is the unique minimal one, and none of it can be discarded
   ([`m32-signature-basis-growth.md`](research/m32-signature-basis-growth.md) §0, at
   `3d46b15f`). Products and reductions to zero at F3: `TODO(F3)`.
2. **Stage speedups.** Eco-12's symbolic stage ran 2.630× and 2.621× faster on #940's two heads
   (base ÷ head, `cl:16`). Neither head is merged. At F3 the symbolic stage is M31's: `TODO(F3)`
   to confirm.
3. **Complete process wall.** MQ10 is routed to conventional F4 from 4 workers, at 0.99–1.01×
   conventional (Gate R). Against the M31 reference, katsura-9 reads 2.4–2.9% slower at F2
   (§15.8.4). F3 cohort: `TODO(F3)`.
4. **Competitive position.** groebner-rs at its best worker count (8) is ahead of Zeebra's
   16-worker entry point on Eco-12 and Cyclic-7, and level on MQ11 and Katsura-11 (§15.7). msolve
   and grobx at F3: `TODO(F3)`.

### 15.2 Primary scoreboard

`TODO(F3)`: the full scoreboard, per §13, from the final cohort. Until then, the F0 reference
cohort is the last complete read of every dev row. Its ratios are entry point ÷ conventional F4 at
16 workers, n = 9, paired medians, at `7b25a1ee` against `8715c8ed`
([`research/m32-baseline/tables.md`](../research/m32-baseline/tables.md); `en:16` walls recomputed
from `walls.jsonl.gz`):

| Row | F0 route | Entry 16 w, ms | Entry ÷ F4, 16 w | Baseline ÷ M31 | Adaptive 16 w | Adaptive ÷ conventional | Adaptive ÷ M31 |
|---|---|---:|---:|---:|---|---|---|
| Eco-12 / 2⁶⁴−353 | Signature | 1,753 | 0.738 | 1.001 | `TODO(F3)` | `TODO(F3)` | `TODO(F3)` |
| Katsura-11 / Goldilocks | Signature | 616 | 0.454 | 1.001 | `TODO(F3)` | `TODO(F3)` | `TODO(F3)` |
| Katsura-11 / 2⁶⁴−353 | Signature | 612 | 0.456 | 0.993 | `TODO(F3)` | `TODO(F3)` | `TODO(F3)` |
| MQ11 / Goldilocks | Signature | 2,144 | 0.458 | 1.005 | `TODO(F3)` | `TODO(F3)` | `TODO(F3)` |
| MQ10 / 32003 | Signature (F0) | 385 | 1.609 | 1.016 | `TODO(F3)` (routed to F4 from 4 w) | `TODO(F3)` | `TODO(F3)` |
| MQ10 / 2³¹−1 | Signature (F0) | 393 | 1.745 | 1.010 | `TODO(F3)` (routed to F4 from 4 w) | `TODO(F3)` | `TODO(F3)` |
| Cyclic-7 / Goldilocks | Shipping (degree spread) | 146 | 1.008 | 1.012 | `TODO(F3)` | `TODO(F3)` | `TODO(F3)` |
| Cyclic-7 / 2⁶⁴−353 | Shipping (degree spread) | 146 | 1.001 | 1.000 | `TODO(F3)` | `TODO(F3)` | `TODO(F3)` |
| noon-7 / Goldilocks | Signature | 109 | 0.560 | 1.005 | `TODO(F3)` | `TODO(F3)` | `TODO(F3)` |
| noon-8 / 2⁶⁴−353 | Signature | 602 | 0.611 | 0.999 | `TODO(F3)` | `TODO(F3)` | `TODO(F3)` |
| Held-out rows (3) | — | — | — | — | `TODO(F3)` | `TODO(F3)` | `TODO(F3)` |

RSS ratios, best comparand per row, equal-worker ratios and verification: `TODO(F3)`.

### 15.3 Worker scaling and stages

`TODO(F3)`: wall and the four stage clocks at 1/4/8/16 workers for both engines and the adaptive
path, and the 8 → 16 ratio (S-b).

The F0 reference, Eco-12 / 2⁶⁴−353, signature route, medians in ms, at `7b25a1ee`
([`m32-baseline.md`](research/m32-baseline.md) §3):

| Arm | Wall | Symbolic | Elimination | Bookkeeping | Interreduction |
|---|---:|---:|---:|---:|---:|
| `d1:1` | 2,565 | 462 | 1,326 | 230 | 269 |
| `cl:4` | 1,836 | 483 | 565 | 239 | 261 |
| `cl:8` | 1,746 | 514 | 429 | 252 | 263 |
| `cl:16` | 1,745 | 552 | 370 | 260 | 262 |

At F0 the 8 → 16 wall ratio is 1,745 ÷ 1,746, about 1.00. #940's unmerged head did no better
past 8 workers: its Eco-12 wall went 1,440 → 1,418 ms from 8 to 16 and its symbolic stage
183 → 201 ms ([`research/m32-gate-s/README.md`](../research/m32-gate-s/README.md), worker curve, at
`592653ee`).

**Why symbolic grows with workers.** Of Eco-12's +90 ms (462 → 552 ms), #953 attributes about
50 ms to CPU clock and about 40 ms to cross-CCD cache locality, with zero extra symbolic work
([`m32-parallel-symbolic.md`](research/m32-parallel-symbolic.md) §5, restored on `main` by #959 in
`dfd984c0`).

### 15.4 Dispatch

The rule merged in #950 (`f427e8d7`;
[`m32-adaptive-dispatch.md`](research/m32-adaptive-dispatch.md) §2):

| Condition, in order | Decision | Dev rows it takes |
|---|---|---|
| linear, fewer than 6 variables, or nonlinear degree spread > 1 (M31's rule) | conventional F4 (`Linear`, `Small`, `DegreeSpread`) | katsura-4 (`Small`); Cyclic-7 (`DegreeSpread`) |
| greatest degree 2, variables in `10..=10`, cap ≥ 4 workers | conventional F4 (`WorkerCrossover`) | MQ10, both fields, at 4, 8 and 16 w |
| otherwise | signature engine; team min(cap, 8) below 10 variables, else the cap | Eco-12, Katsura-11, MQ11, MQ10 at 1 w; noon-7, noon-8 and katsura-9 capped at 8 |

**Dispatch cost (T9)**, Gate R revision 1 at `588d2a44`: median 1.0 µs, max 5.1 µs (MQ11, 16 w).
The worst share of wall on rows ≥ 50 ms is 0.0013%.

**Held out.** Two held-out rows sit on the band's edges by shape alone, read from the pin file's
generator names and not from their terms. katsura-10 / GF(2³¹−1) and mq-random-10 / Goldilocks
both have 10 variables, so the band routes them to conventional F4 from 4 workers
([`m32-adaptive-dispatch.md`](research/m32-adaptive-dispatch.md) §5). Every route at every worker
count, and the held-out results: `TODO(F3)` (Gate Q's `held` suite, read once).

### 15.5 Correctness and safety

`TODO(F3)`: digests, certification status and time, independent references, budget and
cancellation checks, and the adverse-schedule suite, from Gate Q's `check` suite and the final
cohort.

On the merged record so far:

- **#939.** Each of its 2,340 cohort children and every split, A/B and small-control child
  returned its row's one basis digest. Every held-out admission record matches its pin.
- **#927.** All 1,144 first-read children and every revision-1 child have one basis digest per
  row.
- **Known T8 gap, declared before measurement on #941.** The signature engine charges
  `max_live_bytes` only in its parallel cascade. At one worker the adaptive route therefore has no
  live-byte budget
  ([predeclaration](https://github.com/mfaulk/zeebra/issues/941#issuecomment-7042293851)).

### 15.6 Success criteria

| Criterion | Status | Evidence |
|---|---|---|
| Min 1. Baseline | **met** | #939: M31's ratios reproduce within 1.6% (worst MQ10 / 32003, 1.609 against 1.583); component split; §6.3 re-derived; #934 and #935 closed ([`m32-baseline.md`](research/m32-baseline.md)) |
| Min 2. Parallel symbolic investigated | **met** | #933: one design, correctness argument, replay ceiling S16 = 2.95, Gate P passed. The attribution is #953's (§15.3) |
| Min 3. MQ10 | **met** | #927: Gate R passed at revision 1. MQ10 is routed, with the caveats in §15.8.3 |
| Min 4. Safety of anything adopted | `TODO(F3)` | the one adopted change is the dispatch; Gate Q `check`; the T8 gap in §15.5 |
| Min 5. Decision | `TODO(F3)` | #937 |
| Min 6. Report | `TODO(F3)` | this section, completed at F3 |
| T1. Eco-12 symbolic ≥ 1.5× | `TODO(F3)`; cannot be met without a merged parallel symbolic stage | #940 read 2.630 and 2.621 on its unmerged heads |
| T2. Eco-12 wall ≤ 0.90× M31 | `TODO(F3)`; the same | #940 read 0.819 and 0.824 on its unmerged heads |
| T3. MQ10 ≤ 1.05 at 1/4/8/16 w | `TODO(F3)` | Gate R passed. Gate Q's re-check on dev rows also passes: worst 1.008 [0.990, 1.016], 32003 at 4 w, n = 21 (#941, posted, not merged) |
| T4. Gains preserved | `TODO(F3)`; at risk | Gate Q's re-check: katsura-9 at 16 w, ad ÷ m31 **1.036 [1.034, 1.040]** against 1.03 (#941, posted, not merged); §15.8.4 and #958 |
| T5. No regressions (dev and held out) | `TODO(F3)` | held out unread |
| T6. Memory | `TODO(F3)` | — |
| T7. Correctness | `TODO(F3)` | — |
| T8. Resource and behaviour | `TODO(F3)`; known gap | §15.5 |
| T9. Dispatch cost | met at Gate R revision 1; `TODO(F3)` to re-read | §15.4 |
| T10. Qualified | `TODO(F3)` | Gate Q, #937 |
| S-a. Eco-12 vs grobx | `TODO(F3)` | grobx is not run in M32 so far |
| S-b. 16 w ÷ 8 w ≤ 0.90 | `TODO(F3)`; F0 reads about 1.00 | §15.3 |
| S-c. Default for graded orders | `TODO(F3)` | #937 |
| S-d. Reduced outgrowth | **not attempted** | Gate G failed (§15.8.1) |

### 15.7 Competitive gap

**groebner-rs at its best worker count (#935).** Process wall, ms, median of n = 9, at driver
`81dc5c4c`, against Zeebra's F0 entry point at 16 workers (`7b25a1ee`). Both are from
[`research/m32-baseline/tables.md`](../research/m32-baseline/tables.md), and the medians were
recomputed from `rs.jsonl.gz` and `walls.jsonl.gz`:

| Row | groebner-rs 8 w | groebner-rs best | Zeebra entry 16 w | Zeebra ÷ rs best |
|---|---:|---|---:|---:|
| Eco-12 / 2⁶⁴−353 | 907.5 | 8 w | 1,753 | 1.93 |
| Katsura-11 / 2⁶⁴−353 | 597.2 | 16 w, 596.6 (8 w inside its interval) | 612 | 1.03 |
| MQ11 / Goldilocks | 2,170.2 | 8 w | 2,144 | 0.99 |
| Cyclic-7 / 2⁶⁴−353 | 69.3 | 8 w | 146 (entry dispatches to F4) | 2.11 |

This is a best-supported-configuration reading, not equal-worker: it divides medians across
worker counts (16 against 8). M31 read groebner-rs at one worker on these rows, which put
Zeebra-16 ÷ groebner-rs-1 at 0.220–0.753. At its best configuration groebner-rs is ahead on
Eco-12 and Cyclic-7 and level on MQ11 and Katsura-11. Two caveats:

- The sweep ran at load 5.0–30.5 (median 18.0, recomputed from `rs.jsonl.gz`; §15.8.5).
- Zeebra's process wall includes harness cost that a comparand driver which does not render its
  basis does not pay. On Eco-12 at 16 workers that is 140 ms of render, 41 ms of parsing and
  report, and 19 ms of exec and exit ([`m32-baseline.md`](research/m32-baseline.md) §5).

grobx raw and certified, msolve exact, equal-worker rows, the guarantee difference and the stage
decomposition of what remains: `TODO(F3)`.

### 15.8 Negative, inconclusive and stopped results

#### 15.8.1 Gate G fails; H5 falsified (#936, `3d46b15f`)

Every sound option projects at most **3.1%** of Eco-12's 16-worker wall: query-first Koszul
insertion about 19 ms, plus incremental essential tracking about 35 ms, of 1,744 ms. The bar is
5%. Roune–Stillman's lazy Koszul queue is bounded at 6.8%, but only if 95,207 lost eliminations
cost nothing, which is unproven for this engine. Cyclic-7 cannot reach conventional F4 this way.
With bookkeeping and interreduction both at zero it would still take 0.279 s, **1.92×**
conventional F4's 0.145 s. #936 closed completed with this result. The MQ10 side finding is #946
([`m32-signature-basis-growth.md`](research/m32-signature-basis-growth.md) §0, §6).

#### 15.8.2 Gate S fails twice (#940)

| Read | Head | T1 symbolic | T2 wall | Cells missed (upper > 1.05) | Peak RSS max |
|---|---|---|---|---|---|
| First | `592653ee` | 2.630 [2.585, 2.649] met | 0.819 [0.813, 0.824] met | Katsura-11 / Goldilocks 1 w 1.044 [1.020, 1.068]; MQ11 / Goldilocks 1 w 1.037 [1.033, 1.054]; noon-7 / Goldilocks 16 w 1.055 [1.040, 1.071] | 1.085 |
| Re-read after the owner's fix pass | `62cbe4de` | 2.621 [2.602, 2.652] met | 0.824 [0.812, 0.831] met | **noon-7 / Goldilocks 16 w 1.057 [1.041, 1.082]** | 1.094 |

Both reads are against `ce67df76`
([`research/m32-gate-s/tables.md`](../research/m32-gate-s/tables.md),
[`s2/tables.md`](../research/m32-gate-s/s2/tables.md)). The re-read session was **stopped**
before its `small` and `curve` suites, because the missed cell already decided the gate. The
1-worker gap in the first read was code placement: with 64-byte function alignment on both builds,
a diagnostic, head ÷ base was 0.997–0.999. #940 is closed with no `src/` merged. Its code is on the
tags `measured/940-gate-s` and `measured/940-gate-s2`.

#### 15.8.3 Gate R's first read fails; H4 falsified (#927)

- **First read** (`8544cf24` against `c1d93389`). katsura-9 against the M31 entry point at 8 w read
  **1.029 [1.028, 1.030]**, upper 1.0300 against 1.03. The team cap was 4 against M31's 8.
  **T9 failed**: dispatch took a median 93 µs and a max 118 µs from 4 workers up, a cgroup CPU
  count read inside the clock. The katsura-9 medians were recomputed from `small.jsonl.gz` and match.
- **Revision 1** (`588d2a44`) passed. **Caveat:** it re-read only the cells the revision can move:
  katsura-9 at 1/4/8/16 w, noon-7 and noon-8 at 8 and 16 w, and T9 dispatch cost on every dev row.
  Every other Gate R cell is carried over from the first read, at `8544cf24`.
- **H4 is falsified on its validation clause.** In leave-one-family-out validation, the MQ fold
  fits no band and misroutes MQ10 at 4, 8 and 16 w by **1.10–1.75×** (M31 figures), over the 5%
  bound. The `10..=10` band is fitted to MQ10 alone. No cheap feature separates MQ10: its density
  is 0.157, against katsura-9's 0.164
  ([`m32-adaptive-dispatch.md`](research/m32-adaptive-dispatch.md) §2).

#### 15.8.4 katsura-9: Gate Q's T4 fail is a protocol confound (#958)

Gate Q's T4 cell, katsura-9 / 2⁶⁴−353 at 16 w, read ad ÷ m31 **1.036 [1.034, 1.040]** against
1.03, and #941's diagnostic read F2 entry ÷ M31 entry at 1.029 [1.021, 1.034] (1 w) and
1.024 [1.020, 1.027] (16 w) ([`m32-qualification.md`](research/m32-qualification.md) §2). Every
head-side arm there ran `--repeat 21` and every M31 arm `--calls 20`.

#958 (PR #976, `9c24a24f`; [`research/m32-katsura9-gap/`](../research/m32-katsura9-gap/README.md))
timed four libraries through one shared harness, n = 21. **Under one protocol (`--calls 20`), F2 ÷
the true M31 `8715c8ed` is 0.997 [0.984, 1.001] at 1 w and 0.985 [0.983, 0.986] at 16 w.** On the
same F2 binary, `--repeat 21` ÷ `--calls 20` is 1.054 / 1.058: `--repeat` frees every basis between
calls, glibc trims the heap top back to the kernel, and the next call faults it in again. With
trimming disabled the penalty mostly goes away. #947's and #948's refactor costs nothing
(`ce67df76` ÷ `8715c8ed` 0.998 / 0.996), and harness text placement moves the row 0.997–1.001.

**Both reads stand side by side.** Gate Q's recorded verdict is unchanged: T4 failed at Gate Q,
with this confound named. Read under one protocol, the library is level with M31 on this row. One
gap is not explained: #958's session read the cross-protocol pairing at 1.050–1.060, against
#941's 1.024–1.029. Direction and cause agree; the size difference does not.

This is why the F3 cohort (§15.0) builds `8715c8ed` itself and runs every Zeebra arm through one
harness with one protocol per suite.

#### 15.8.5 Load during the reads

- **#927.** Another session ran a 32-thread memory-heavy job on CPUs 24–55 from about 13:40 to
  14:57 local on 2026-11-19. That is outside the reserved CCDs but shares package clock and DRAM
  bandwidth. All 432 `fav` children (load 16.9–20.0) and `small` repetitions 27–30 (up to 20.3)
  ran inside it. #927 records that no verdict depends on those windows
  ([`m32-adaptive-dispatch.md`](research/m32-adaptive-dispatch.md) §3.3).
- **#939.** Its `ab` session (14:20–14:25 local) ran inside the same window at load 18.5–19.8. The
  `rs` sweep (#935) started at 14:57 at load 17.47 (`benchlock.log`). Its children ran at load
  5.0–30.5, median 18.0. Whether the same job caused this is not recorded.
- **#939's header understates the load.** It says per-child `load_start` was 1–18. The records
  show `walls` at 0.5–41.2, with 15 of 2,340 children above 18, at about 10:36 local. The
  ratios are paired and interleaved, but those absolute walls are not quiet-box figures.
  (Recomputed from `walls.jsonl.gz` and `rs.jsonl.gz`.)

#### 15.8.6 The unfused symbolic loop: confirmed on a quiet box (#939, #964)

In #939's split build, multiplying each row into a buffer and then interning it ran faster than the
shipping fused loop on two rows and slower on a third. #964 re-ran the identical suite from fresh
builds of `45107ec3` at load 1.4–3.4 (PR #976, `9c24a24f`;
[`research/m32-katsura9-gap/README.md`](../research/m32-katsura9-gap/README.md) §#964). Symbolic
stage, unfused ÷ shipping, n = 5:

| Row | Workers | #939 (load 18.5–19.8) | #964 (quiet) |
|---|---:|---:|---:|
| Eco-12 / 2⁶⁴−353 | 1 | 0.601 [0.595, 0.617] | 0.612 [0.606, 0.633] |
| | 16 | 0.655 [0.647, 0.677] | 0.675 [0.667, 0.680] |
| Katsura-11 / Goldilocks | 1 | 1.156 [1.092, 1.159] | 1.143 [1.077, 1.172] |
| | 16 | 1.082 [1.069, 1.161] | 1.154 [1.081, 1.420] |
| MQ10 / 32003 | 1 | 0.643 [0.638, 0.694] | 0.656 [0.649, 0.729] |
| | 16 | 0.686 [0.665, 0.742] | 0.698 [0.680, 0.760] |

**The lead survives.** Every cell keeps its direction and stays within about 0.02 of the loaded
read, except Katsura-11 at 16 w, whose interval is wide in both. It is row-dependent and still
unexplained. It is M33's to pursue (#970), not M32 work.

#### 15.8.7 Other negative and stopped results

- **H3 is falsified** (#933, `8694d172`). Reducer search is 2.3–2.6% of the Eco-12 closure and
  5.6–6.0% of MQ10's, against H3's 30%. #939's split build puts it at 1–13% of the stage.
  Interning is 52–86%.
- **Held-out rows dropped by the admission rule and not replaced** (#939): mq-random-12 /
  2⁶⁴−353 (conventional F4-16 took 104.6 s, over 60 s), mq-random-9 / GF(32003) (3.1 ms; an
  inconsistent system) and cyclic-6 / Goldilocks (7.6 ms). The held-out set has no dense MQ
  beyond the crossover.
- **Gate Q.** The threshold re-check fails T4 on katsura-9 (§15.6). Under #941's rule the re-fit
  is not used and the thresholds stand. Outcome: `TODO(F3)`.
- Refusals and timeouts at F3: `TODO(F3)`.

### 15.9 Dispositions and follow-ups

| Issue | Outcome |
|---|---|
| #939 M32-0 | closed: baseline, pin and model ([`m32-baseline.md`](research/m32-baseline.md)) |
| #934 small controls | closed: in-process warm-call method, half-width ≤ 0.70% on katsura-4 |
| #935 comparand workers | closed: groebner-rs best at 8 workers (§15.7) |
| #933 S1a | closed: Gate P passed |
| #940 S1b | closed: Gate S failed twice; nothing merged |
| #936 S3 | closed: Gate G failed; H5 falsified |
| #927 S2 | closed: Gate R passed at revision 1, merged as `f427e8d7` (#950); H4 falsified |
| #941 Q | `TODO(F3)`: open, draft PR #957 |
| #937 decision | `TODO(F3)`: open |
| #942 M32-I | this draft; final cohort `TODO(F3)` |

**Follow-ups filed on Project #7, linked to #938:**

- #946: MQ10 tail after the last essential element (`opportunity`)
- #958: the katsura-9 F2 ÷ M31 regression triage (Medium)
- #959: restore #953's attribution text (Low)

Follow-ups from Gate Q and the F3 cohort: `TODO(F3)`.
