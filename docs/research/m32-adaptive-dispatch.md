# M32-S2: adaptive algorithm and worker-count selection (#927)

**Status:** complete, 2026-11-19. **Gate R: the first read fails** (katsura-9 at 8 workers, T9);
**after revision 1 every criterion passes.** H4 is falsified on its leave-one-family-out clause: the
MQ10 crossover is fitted to MQ10 alone (§2).
**Measured at:** first read head `8544cf24` (tag `measured/927-head`), revision 1 head `588d2a44`
(tag `measured/927-rev1`), #978's held-out check `e3a25264` (tag `measured/978-held-out`, Addendum), #1141's held-out check
`e98322f4` (tag `measured/1141-held-out`, Addendum), the first three against base `c1d93389` (tag
`measured/927-base`; `src/` identical to `main` at `ce67df76`, plus the library-neutral
`sig_f4_study --calls` harness), each built from a `git archive` into its own target directory
(release, fat LTO, one codegen unit, x86-64-v3, `--features research-sigf4`, `RUSTC_WRAPPER=""`,
`CARGO_INCREMENTAL=0`); SHA-256s in [`binaries.sha256`](../../research/m32-adaptive-dispatch/binaries.sha256).
Fitting figures in §2 are quoted from M31's final cohort at `8715c8ed`
([`research/m31-final/tables.md`](../../research/m31-final/tables.md)), whose `src/` the M32
baseline `7b25a1ee` matches line for line.
**Plan:** [`MILESTONE-ADAPTIVE-F4.md`](../MILESTONE-ADAPTIVE-F4.md) §4.1 (H4), §6.2 (T3, T9),
§7.3, §8.2 (Gate R), §10.3. **Corpus:** development rows only
([`research/m32-baseline/pins.json`](../../research/m32-baseline/pins.json)); no held-out row was
built, run or inspected.

## 1. What was built

`signature_route(generators, order, &F4Options)` and `f4_signature_reported` return a
`SignatureDispatch` carrying three separate decisions and the features they read:

| Decision | Field | Values |
|---|---|---|
| engine | `route` | `Signature`, or `Shipping(Small \| Linear \| DegreeSpread \| Order \| WorkerCrossover \| Fallback)` |
| team | `workers` | signature route: at most the caller's cap, never above it; shipping route: the caller's options unchanged |
| cascade | `cascade` | `Some(Parallel)` when the signature team has more than one worker, `Some(Serial)` otherwise, `None` on the shipping route |

Features, one pass over the generators' terms: variables that appear, nonzero generators, least
nonlinear and greatest degree, terms, the monomials each generator's degree allows (density =
terms ÷ monomials, `planning::monomials_up_to_degree`, also `SystemShape::monomial_density`), the
caller's worker cap (the larger of `parallel_forward` and `parallel_symbolic`), and the field
element's width in bits. `planning::analyze` itself is not called: its interaction-pair set
allocates per monomial and the rule reads none of its other fields.

## 2. The rule and why each threshold sits where it does

| Condition, in order | Decision |
|---|---|
| M31's rule: linear, < 6 variables, nonlinear degree spread > 1 | shipping |
| graded-lex (added after Gate Q, #961) | shipping (`Order`) |
| greatest degree 2, variables in `10..=10`, caller's cap ≥ 4 workers | shipping (`WorkerCrossover`) |
| otherwise | signature engine; team = min(cap, 8) below 10 variables (4 in the first read), else the cap; parallel cascade iff team > 1 |

**No cheap feature separates MQ10.** The issue's expected shape was "dense quadratic inputs below a
size bound". MQ10 from the published ladder is not dense: 9 quadratic generators and 1 linear one
in 10 variables, 95 terms, density 0.157, against katsura-9's 0.164 and katsura-11's 0.135. Its
degree histogram is Katsura's. Every quadratic dev row, by variables:

| Row | Variables | Terms | Density | 16 w: signature ÷ F4 (M31) | F4 scaling 1→16 w |
|---|---:|---:|---:|---:|---:|
| katsura-9 / 2⁶⁴−353 | 9 | 74 | 0.164 | 0.59 | 2.3× |
| **MQ10 / GF(32003)** | 10 | 95 | 0.157 | **1.58** | 4.5× |
| **MQ10 / GF(2³¹−1)** | 10 | 95 | 0.157 | **1.74** | 4.1× |
| katsura-11 (both fields) | 11 | 107 | 0.135 | 0.45 | 6.8–7.2× |
| MQ11 / Goldilocks | 11 | 858 | 1.000 | 0.46 | 8.9× |

The loss is a band in size at fixed workers, not a side of a threshold: below it the shipping F4
does not scale (katsura-9 bottoms at 70 ms), above it the signature engine's serial advantage
outgrows the shipping F4's parallel speedup (katsura-11 serially 0.10×, MQ11 0.13×). MQ10 is the
only dev row inside it, so its edges are fitted to MQ10 alone, and on integer variable counts
between katsura-9 and katsura-11 the band can only be `10..=10`. That is the conservative rule the
plan anticipated (§7.3): it only ever moves an input to the shipping F4, so a held-out row it
catches by mistake loses the saving and is never slower than conventional F4. Field width was read
and not used: MQ10 loses at both fields.

**Worker threshold 4.** MQ10's M31 wall medians are at parity at 4 workers (0.98× at 32003, 1.10×
at 2³¹−1). 2 and 3 workers were not measured; interpolating the shipping F4's own scaling puts it
at roughly 470–600 ms there against the signature engine's 374–470 ms, an estimate, not a figure.
T3 reads 4, so the crossover starts there.

**Team cap.** In M31's cohort the parallel cascade at 4 workers (`cl:4`) beat 16 (`cl:16`) on
katsura-9 (41 vs 43 ms), noon-7 (102 vs 108) and noon-8 (582 vs 600), and lost on katsura-11 (652 vs
617), Eco-12 (1,863 vs 1,752) and MQ11 (2,675 vs 2,129). The threshold sits midway between the
largest preferring 4 (9 variables) and the smallest preferring the full team (11). The cap itself was
four in the first read and is eight after revision 1 (§3): katsura-9's warm calls preferred eight
to four, and eight to sixteen still holds on katsura-9, noon-7 and noon-8.

### Leave-one-family-out

Procedure, fixed before the read: the band is the narrowest variable range covering every losing
quadratic training row; the team threshold is the midpoint between the largest cap-preferring and
the smallest full-team-preferring training row. Each family left out in turn, then routed:

| Left out | Band fitted | Team threshold | Left-out rows misrouted |
|---|---|---|---|
| Eco | 10..=10 | 10 | none |
| Katsura | 10..=10 | 9.5 | none (katsura-9 capped, katsura-11 full) |
| **MQ** | **none** (no losing row) | 10 | **MQ10 at 4, 8, 16 w: 1.10–1.75× (M31)** |
| Cyclic | 10..=10 | 10 | none (degree spread) |
| Noon | 10..=10 | 10 | none |

The MQ fold misroutes by more than 5%, so **H4 is falsified on its own validation clause** whatever
Gate R reads: the band is MQ10's, not a property the other families predict.

### Addendum (#978): the band now requires a solution at infinity

The M32 final cohort found the band catching two held-out rows of MQ10's shape where it is wrong:
mq-random-10 / Goldilocks and katsura-10 / GF(2³¹−1). Forced, the signature engine there is
0.552× and 0.601× conventional F4 at 16 w, so the routed path read 1.80× and 1.66× M31
([M32 report](../MILESTONE-ADAPTIVE-F4.md) §15.4). The band row in the table above now reads
"greatest degree 2, variables in `10..=10`, **a solution at infinity**, cap ≥ 4 workers".

The added condition is structural, not fitted. Let `x_k` be a variable that appears in the input
but has no pure power `x_k^d` in any degree-`d` generator's top-degree form. Then the coordinate
point `e_k` is a common zero of the top forms, which therefore have a nontrivial projective zero.
That means they are not a regular sequence, and the input has a solution at infinity. The signature
criterion removes every zero reduction only on regular input, so this is where the signature
engine's extra elements live. The test is one pass over the terms
(`DispatchFeatures::infinity_witness`). It is a sufficient condition for non-regularity, not a
characterization: a non-regular input can lack the witness.

| Row (10 variables, quadratic) | Pure powers in the top forms | Witness | Route from 4 w |
|---|---|---|---|
| MQ10, sparse ladder (both fields) | `x3²`, `x10²` and the linear form's `x6`, `x9`, `x10` | `x1` | shipping (unchanged) |
| katsura-10 (any field) | every `x_k²` | none | signature (was shipping) |
| mq-random-10 / Goldilocks, dense | every `x_k²` | none | signature (was shipping) |

Outside the band nothing changes. On every dev row the route is unchanged. The narrowing only moves
rows from the shipping F4 back to the signature engine, which is M31's route for them, so on any
row it returns M31's behaviour. Both rows above were read in the final cohort, so they are
development data under #1005's cohort rule. Confirming the condition on rows nobody has read still
needs a new held-out set on the bench host.

**Held-out check (bench host, `e3a25264`, tag `measured/978-held-out`): not confirmed.** The set,
protocol and rule were posted on #978 before any timed run; the evidence is in
[`research/978-worker-crossover/`](../../research/978-worker-crossover/README.md). Nine rows nobody
had read, 9 fresh pinned processes per engine and worker count, CCDs 1–2 reserved. A cell agrees
when the engine the band picks is within 5% of the other forced engine. Every route the entry point
took matched the witness, and every basis agreed across engines.

| Group | Rows | sigf4 ÷ f4 at 4 / 8 / 16 w | Cells that agree |
|---|---|---|---|
| no witness → signature | katsura-10 over GF(32003), Goldilocks, wide64 | 0.22–0.24 / 0.31–0.32 / 0.37–0.39 | 9 of 9 |
| witness → conventional F4 | ladder MQ, seed 11 over both fields | 1.02–1.13 / 1.21–1.28 / 1.30–1.42 | 6 of 6 |
| witness → conventional F4 | ladder MQ, seeds 12 and 13 over both fields | 0.46–0.64 / 0.67–0.85 / 0.95–1.24 | 3 of 12 |

The narrowing itself holds on unseen rows: every no-witness row belongs on the signature engine,
which is 2.6–4.4× faster than conventional F4 there. The band's *remaining* rows do not all hold.
On ladder seeds 12 and 13 the signature engine is faster at 4 and 8 workers (0.46× at worst,
seed 13 / GF(32003) at 4 w), so the band still costs up to 2.2× on rows it keeps. It crosses over
only at about 16 workers. The witness separates katsura-like inputs from MQ10's shape. It does not
locate the worker crossover within that shape. The four dense planted `m = 2n` rows fell under the
20 ms floor and were dropped. Whether to narrow further, refit the worker threshold, or accept the
residual cost is an owner decision (#978).

**#1141: a term-count refit, not confirmed (`e98322f4`, tag `measured/1141-held-out`).** On
ladder MQ seeds 10–13 only the term count separates the rows F4 wins at 4 w (95, 107 terms) from
the ones it loses (120, 121); monomials and quadratic generators do not (seed 12 has MQ10's 605
and 9). The candidate, posted on #1141 before any timed run, kept the band's shipping route at
`workers >= 16`, or at `workers >= 4` with `terms < 114`. On 20 fresh rows (seeds 14–25 over both
fields, 9 pinned processes per cell) it agreed on 53 of 60 cells, short of the pre-declared 90%,
against the incumbent's 35; seed 18 (115 terms) at 8 w and seed 24 at 16 w missed by 1.30–1.51×.
The band is not removed either: low-term rows lose 1.3–23× on the signature engine (seed 22, 94
terms, 13–23×). MQ10 itself now favours the signature engine at 4 w (0.66 / 0.75), so the band's
own fitting row no longer sits at parity there. The rule is unchanged; evidence and the
descriptive breakdown are in [`research/1141-worker-crossover/`](../../research/1141-worker-crossover/README.md).

## 3. Gate R (plan §8.2)

Method: plan §10.2–10.3. Fresh process per child, arms rotated one place per repetition, ratios
paired per repetition, median with a 95% bootstrap interval of the median (20,000 draws),
CCD-aligned `taskset` from CPU 8, `rss-guard` 8 GiB, 180 s cap
([`campaign.py`](../../research/m32-adaptive-dispatch/campaign.py),
[`summarize.py`](../../research/m32-adaptive-dispatch/summarize.py), records `*.jsonl.gz`). Every
suite ran under `tools/bench-reserve.sh run` inside the CCD 1–2 reservation another session (#939)
held most of the day; this issue reserved only for its last extension block (§3.2), and its
suites queued behind #939's and #940's under benchlock. Load outside the reservation 0.7–20.3 (§3.3). Rows under 50 ms (katsura-4, katsura-9) use §10.3's
default, since #934 had not landed when the gate was read (it merged in #952 afterwards, and its
`--repeat` replaced this harness's `--calls` on `main`): the median of 10 warm in-process calls per process, n = 31
processes. 1,144 of 1,144 first-read children completed; every row has one basis digest across all
arms and repetitions.

### 3.1 First read (head `8544cf24`): **fails**

| Criterion | Worst cell | Read |
|---|---|---|
| T3: MQ10 / 32003 ÷ conventional, 1/4/8/16 w | 1.007 [0.991, 1.012] at 4 w | pass |
| T3: MQ10 / 2³¹−1 ÷ conventional | 4 w: 0.992 [0.959, 1.037] after n = 9, imprecise (3.9%); pooled with the extension block (n = 21): **0.992 [0.985, 1.009]** | pass |
| favourable rows ÷ M31 entry, 1/4/8/16 w (Eco-12, Katsura-11 ×2, MQ11, noon-7, noon-8) | katsura-11 / 2⁶⁴−353, 16 w: 1.006 [1.003, 1.011] | pass |
| katsura-9 ÷ M31 entry (warm calls) | **8 w: 1.029 [1.028, 1.030]**, team 4 against M31's 8 | **fail** (upper 1.0300 > 1.03) |
| Cyclic-7 ÷ conventional, 1 and 16 w | wide64, 16 w: 1.007 [0.988, 1.018] | pass |
| katsura-4 ÷ conventional (warm calls), 1 and 16 w | wide64, 1 w: 1.015 [1.008, 1.021] | pass |
| T9: dispatch ≤ 50 µs, ≤ 0.1% of wall | **median 93 µs, max 118 µs** from 4 workers up; 1.1 µs at 1 | **fail** |

MQ10 at 1 worker keeps the signature engine and wins (0.418× and 0.487×); from 4 workers it takes
conventional F4 and sits at 0.99–1.01×. The favourable rows are at or under M31's entry point;
the team cap of four gains on noon-7 at 16 workers (0.961 [0.946, 0.973]) and loses on katsura-9.

Both failures have a cause in the code. **Team:** katsura-9's warm calls ran faster on M31's eight
workers (20.8 ms) than on four (21.4 ms); M31's process-wall evidence for four (§2) did not survive
the in-process method. **T9:** from 4 workers the worker cap resolves an `Auto` policy against the
process's CPU count, whose first read is a cgroup lookup (#752's `OnceLock`, about 95 µs). M31's
entry point paid it too, after its clock; the rule itself costs about a microsecond.

### 3.2 Revision 1 (head `588d2a44`)

The first of the two revisions plan §7.3 allows: `SIGNATURE_SMALL_TEAM` 4 → 8, and the worker cap
resolved before the dispatch clock (`052e2364`). Read once, on the cells the revision can move
(katsura-9 at 1/4/8/16 w, noon-7 and noon-8 at 8 and 16 w, both ÷ M31's entry point) and on the
dispatch cost of every dev row at 1/4/8/16 w (n = 3); every other cell is unchanged by it (MQ10 at
4 w and up never reaches the signature engine, and rows of 10 or more variables keep the full team).

| Criterion | Cells | Read |
|---|---|---|
| katsura-9 ÷ M31 entry (warm calls), 1/4/8/16 w | 1.006 [0.994, 1.023]; 1.004 [1.001, 1.008]; 1.005 [1.004, 1.008]; 0.989 [0.986, 0.990] | pass |
| noon-7 ÷ M31 entry, 8 and 16 w | 1.000 [0.992, 1.009]; 0.973 [0.962, 0.979] (n = 21) | pass |
| noon-8 ÷ M31 entry, 8 and 16 w | 0.998 [0.986, 1.007]; 0.993 [0.982, 1.010] (n = 21) | pass |
| T9: dispatch, every dev row at 1/4/8/16 w | median 1.0 µs, max 5.1 µs (MQ11, 16 w); worst share of wall on rows ≥ 50 ms 0.0013% | pass |

The 16-worker noon cells missed the precision rule at n = 9 (1.5% and 2.3% against 1.5%) and got
§10.3's one n = 12 extension block each, pooled; that block ran under this issue's own CCD 1–2
reservation after the others released theirs, and released it at the end. Every revision-1 child
completed with the row's one basis digest. With the first read's unchanged cells, **Gate R passes
on revision 1**: T3 on MQ10 at both fields and all four worker counts, every signature-routed dev
row ≤ 1.03 against M31's entry point, Cyclic-7 and katsura-4 ≤ 1.05 against conventional F4, T9.
One revision remains under the cap.

### 3.3 Machine load during the read

Another session ran a 32-thread memory-heavy job on CPUs 24–55 from about 13:40 to 14:57 local,
outside the reserved CCDs but sharing package clock and DRAM bandwidth. Per child `load_start`:
all 432 `fav` children (load 16.9–20.0) and `small` repetitions 27–30 (54 children, up to 20.3)
ran inside it; every other suite ran at load ≤ 3.9 (`rev1favx` ≤ 8.5). No verdict depends on
those windows. The `fav` cells are paired, interleaved ratios with their worst upper bound at 1.011
against 1.03, and the revision-1 read at load ≤ 1.9 reproduces the noon cells. The failing
katsura-9 cell reads 1.029 [1.029, 1.031] without repetitions 27–30, and the clean revision-1
read reproduces both of its arms (M31's 8 workers 20.80 ms, four workers 21.31 ms). Nothing was
re-run because of the load.

## 4. Caps

One claim lease plus the campaign's queueing (most of the day was spent queued behind #939's and
#940's suites under benchlock): about 175 net lines under `src/` excluding the dispatch tests,
against 600; one rule revision of two; one extension block per imprecise cell.

## 5. For #941

Re-check `SIGNATURE_CROSSOVER_VARIABLES` (10..=10), `SIGNATURE_CROSSOVER_WORKERS` (4),
`SIGNATURE_SMALL_TEAM_VARIABLES` (10) and `SIGNATURE_SMALL_TEAM` (8) once on the merged engine if
#940 lands: a parallel symbolic stage moves the crossover up in workers and may close the band.
Two held-out rows sit on the band's edges by shape alone (read here from the pin file's generator
names, not from their terms): katsura-10 / GF(2³¹−1) has MQ10's variable count, so the band routes
it to conventional F4 from four workers, and mq-random-10 / Goldilocks (the wide catalog's dense MQ)
does too. Neither was used to place any threshold.
