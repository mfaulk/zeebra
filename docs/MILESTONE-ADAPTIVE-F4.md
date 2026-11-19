# M32 — Adaptive F4: Parallel Symbolic Preprocessing and Production Qualification

**Status:** planned, 2026-11-19. No M32 measurement has been taken. §§1–13 are the plan, fixed
before measurement; §15 will hold the integration report (#942), written from §13's template.
**Predecessor:** M31 — Signature-F4 Wall-Time Conversion and Competitive Performance
([`MILESTONE-COMPETITIVE-SIGNATURE-F4.md`](MILESTONE-COMPETITIVE-SIGNATURE-F4.md), §15 integration
report; tracker #900, closed).
**Planning base:** `main` at `e59a90a1`. Its timed `src/` differs from M31's final `8715c8ed` only
in doc comments (`src/grobner/sigf4/dispatch.rs`, `src/lib.rs`).
**Measured at:** `8715c8ed`, quoted; nothing here is measured by M32. Every figure in §§2–6 is quoted from M31's final
cohort at that commit (evidence and every table in
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
