# The M27 baseline: what is on record, at which commit, and what it may be divided by

**Issue:** #451 (M27-0). **Frozen at:** `1985504`, re-verified at `53fbf50`, 2026-11-07.
**Purpose:** M27 quotes ratios. This document is the thing they are quoted against, so that a later
agent cites a figure instead of re-deriving one — and so that no ratio is formed by dividing two
numbers that were never measurements of the same quantity.

It **freezes what exists and names what is missing**. It takes no new frontier measurement. The
measurements it does take are in §2, because the stage split M27-A is organized around was taken
before #437 landed and nothing in the tree could say whether #437 moved it.

> **`main` moved four merges during this freeze** — #476, #478, #479 and #460 landed, #478 being
> the matrix interreduction carrying a reported 4.18x. §2 was therefore re-taken at `53fbf50` and
> **the baseline survives**, for one reason that matters more than the re-measurement:
> `interreduce_by_matrix` is **off in `F4Options::recommended()`**, which is `default()`, so no
> board row and no default-path run gets the 4.18x yet. §2.3 and §2.4.
>
> **Since #507** the flag is `F4Options::interreduction: InterreductionRoute` and its default is
> still the division route, so the sentence above still holds of the default path — but the board
> now does carry matrix-route rows, each labelled in its `library_version`. §2.4's projection was
> re-taken as a measured cohort and held to 2.0%; what keeps the default where it is turned out to
> be unbudgeted memory rather than a missing A/B. `interreduction-cost.md` §3e and **#536**.

## 0. Four conventions, because three of the four discrepancies below are conventions

1. **Wall clock and core time are different quantities.** A table of one may not be compared term
   by term with a table of the other. §4 is entirely this.
2. **A projection is not a measurement**, even when every input to it was measured. §4 and §6 both
   turn on a figure labelled *extrapolated* being read as though it were observed.
3. **The three scoreboard classes are never added together** (`SCOREBOARD.md`, line 3). §3 respects
   this; so must anything quoting it.
4. **Every figure here carries its commit**, per #335. Where the commit is unreachable from `main`,
   §5.2 says so — that is a real defect and recording the SHA does not repair it.

---

## 1. The competitive baseline per engine, and what is actually on `main`

**#451's second premise is now stale, and this is the correction.** It records that
`research/competitive/results/history.json` holds "72 rows, `zeebra` 36 and `singular` 36, and
nothing else", with every msolve, Groebner.jl and Sagebrush figure existing "only in PR #435".

**PR #435 merged at 2026-11-07T21:52:03Z** (`25e10fe`). The file on `main` now holds **387 rows
across five libraries**:

| library | rows | problems | complete | unsupported | stopped-by-limit | failed |
|---|---:|---:|---:|---:|---:|---:|
| zeebra | 99 | 18 | 86 | 4 | 9 | 0 |
| singular | 99 | 18 | 81 | 11 | 6 | 1 |
| sagebrush | 63 | 18 | 52 | 6 | 4 | 1 |
| groebner.jl | 63 | 18 | 29 | 32 | 2 | 0 |
| msolve | 63 | 18 | 27 | 34 | 2 | 0 |

So **every engine's rows are on `main`**, and the answer to "what is in flight" is: nothing, for
this file. The 387 rows are four cohorts, and the cohort is the unit that may be compared within:

| cohort | taken | machine / affinity | libraries | rows | characteristic |
|---|---|---|---|---:|---|
| `663097a` | 2026-11-06 21:03 | workstation, 0-7 | zeebra, singular | 72 | GF(2³¹−1) |
| `7adb29e` | 2026-11-07 16:11 | workstation, 0-7 | all five | 180 | GF(2³¹−1) |
| `87a807e` | 2026-11-07 18:30 | workstation, 0-7 | all five | 130 | GF(32003) |
| `a904145` | 2026-11-07 17:31 | **fedora, affinity unset** | all five | 5 | GF(2³¹−1) |

`a904145` is five rows on a **different machine with affinity unset**. It is a one-problem
(`cyclic-4`) conversion set and it must not be pooled with the workstation cohorts. Nothing
currently stops a consumer from doing so; the grouping discipline lives in the reader, not the file.

### 1.1 The headline, and a second characteristic that corroborates it

`mq-random-10`, `reduced-grobner-basis`, grevlex, one worker, affinity 0-7. Two independent
five-engine cohorts at two different characteristics — **different problem digests, so these are two
problems, not two runs of one**:

| engine | `7adb29e`, GF(2³¹−1), `72d0ad315fc2` | ratio | `87a807e`, GF(32003), `16422dafcdb6` | ratio |
|---|---:|---:|---:|---:|
| **zeebra** | **29 011.4 ms** | — | **28 688.3 ms** | — |
| singular | 7 001.1 ms | 4.14x | 7 073.5 ms | 4.06x |
| sagebrush | 334.9 ms | 86.6x *(not authoritative)* | 323.5 ms | 88.7x *(not authoritative)* |
| msolve | 243.1 ms | 119.3x | 222.8 ms | 128.8x |
| **groebner.jl** | **83.4 ms** | **347.8x** | **84.8 ms** | **338.3x** |

**Every ratio is reproduced at a second characteristic to within 8%, and four of the five to within
3%.** That is the most useful single fact in this document: the 348x is not an artefact of one
field, one digest or one cohort. Sagebrush's ratio is marked non-authoritative by the board itself
and is context, not a competitive claim; Groebner.jl's is an *inner* time whose JIT question #447
settled at a 2.2% self-inflation (`groebner-jl-gap.md` §6), so two significant figures are
defensible at this instance size and the figure errs **against** Groebner.jl.

### 1.2 The Zeebra side of the retained 4.13x is 28 709 ms, not 30 112 ms

#451 states the board's retained ratio as "**4.13x** against a Zeebra side of ~30 112 ms". The
retained 4.13x is `competitive-baseline.md` §4a's measured-rows table, and it is

> 28 708.5 ms / 6 958.8 ms = **4.126x**, cohort `663097a`.

**The string `30 112` occurs nowhere in this repository** — not in `history.json`, not in `docs/`,
not in `research/`. It is unsourced, and since #451's own warning is that neither number may be
published as the other, the first thing to freeze is which numbers exist.

---

## 2. The stage split re-taken at `1985504`, and #304 did not move this row

**This is the one new measurement.** #349's split is pre-#437, and #450 carries the caveat that
M27-0 must re-take it. Re-taken with the same instrument on the same digest:

**Protocol.** `cargo run --release --example f4_profile -- mq`, which builds `mq-random-10` through
`grobner::external::instance` at `REFERENCE_CHARACTERISTIC` under grevlex and **asserts the identity
digest `72d0ad315fc25409`** — the digest both the zeebra and singular retained records carry. Under
`F4Options::default()` with `measure_stages`, not `baseline()`, because that is the configuration
`competitive_sweep.rs` builds and because **under `baseline()` this instance does not finish**
(§2.2). `tools/benchlock.sh zb-451-baseline`, `taskset -c 0-7`, private `CARGO_TARGET_DIR`,
`RUSTC_WRAPPER=""`, `ZEEBRA_MACHINE=workstation`, `ZEEBRA_AFFINITY=0-7`, commit `1985504`.

**Three runs, sequentially on the lock:**

| run | total/ms | symbolic | construction | elimination | extraction | **interreduction** | other | batches | pairs | basis |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 1 | 33 846.8 | 503.9 | 1 337.1 | 4 576.6 | 117.0 | **27 221.7** | 90.5 | 10 | 1 777 | 247 |
| 2 | 32 871.1 | 441.8 | 1 158.4 | 5 869.8 | 117.9 | **25 193.3** | 89.9 | 10 | 1 777 | 247 |
| 3 | 33 578.3 | 443.4 | 1 134.8 | 4 461.5 | 116.6 | **27 333.0** | 89.1 | 10 | 1 777 | 247 |
| **share** | — | **1.4%** | **3.6%** | **14.9%** | **0.4%** | **79.5%** | **0.3%** | | | |

**Batches (10), pairs (1 777) and basis size (247) are identical across all three runs and identical
to #349's**, so the computation is deterministic, the work is the same work, and the spread is
timing alone. Stage coverage is **100.00%** in every run — the four stages plus `other` account for
the whole total, so the breakdown is not looking in the wrong place.

| | #349, pre-#437 | here, post-#437 (`1985504`) |
|---|---|---|
| symbolic | 1.4% | **1.4%** |
| construction | 3.5% | **3.6%** |
| elimination | 13.9% | **14.9%** |
| extraction | 0.4% | **0.4%** |
| **interreduction** | **80.4%** | **79.5%** (per-run 80.4% / 76.6% / 81.4%) |
| other | 0.3% | **0.3%** |
| Amdahl ceiling if interreduction were free | 5.10x | **4.88x** |

**The split is unchanged.** The aggregate interreduction share moves 80.4% → 79.5%, and the
per-run range (76.6–81.4%) brackets #349's figure. Run 2 is the outlier in both directions at once
— elimination 5 869.8 ms against ~4 500 ms in runs 1 and 3, interreduction correspondingly lower —
which is box state, not computation: the work counts are identical.

**The total is instrumented and is not the board figure.** The mean here is 33 432 ms, against
#349's instrumented mean of 30 811 ms and the board's 29 011 ms. `measure_stages` reads a clock four
times a batch, and #349 already recorded its own totals running 3.8–11.5% above the record for that
reason. These run **+8.5% above #349's instrumented total** and **+15.2% above the board row**, on a
box that other sessions were compiling on throughout. **No regression may be read from that
number**, and no M27 figure should be: the shares are what this measurement establishes, and the
board row (§1.1) is the wall clock of record.

### 2.1 What the re-measurement settles

**Interreduction is still ~80% of this row after #437.** #349 measured 80.4% before #437; the share
is unchanged within the run-to-run spread. #437 removed the duplicated basis storage — it was filed
and merged as a **memory** finding — and §6b.2 of `competitive-baseline.md` warned at the time that

> the screen bounds a candidate from above and cannot promise anything from below.

The measurement is that warning coming due. **#304's ceiling of 5.10x was real as a bound and
delivered none of it as a speedup on this row** — the wall moved by less than §6.4's ~1%
same-machine repeatability — because the time in that stage was never in the duplication.
#436 then located it in the `normal_form` loop, and #477 located the reason upstream of the loop
(the candidates reach interreduction unreduced, so the matrix carries ~7 395 reducible tail
monomials against Groebner.jl's ~3). All three are consistent with this split.

**So #451's first premise also needs correcting.** It reads "#304 moved Zeebra to 29 011 ms, which
would make it ~3.98x". #304/#437 is in both the `7adb29e` and `87a807e` cohorts and in neither did
the row improve:

| cohort | contains #437 | zeebra on `mq-random-10` |
|---|:---:|---:|
| `663097a` | no | 28 708.5 ms |
| `7adb29e` | **yes** | 29 011.4 ms |
| `87a807e` | **yes** | 28 688.3 ms *(GF(32003), different digest)* |

29 011.4 ms is not where #304 moved the row to; it is what the post-#437 cohort measured, and it is
**1.1% slower** than the pre-#437 figure. The proposed 4.13x → 3.98x adjustment would therefore
have been worse than an arithmetic adjustment where a measurement belonged: it would have credited
a 3.6% improvement to a change with no measurable effect on this row, in the direction opposite to
the one the figures show.

**No ratio on this row may be quoted as an improvement attributable to #304.**

### 2.2 The budget cliff, which is a property of the baseline and not of an instance

Under `F4Options::baseline()` this instance refuses at **20 000 277 live nonzero entries against the
20 000 000 budget** — one part in 72 202 over. Anemoi `N = 6` PCICO crosses the same budget by one
part in 178 571 and `poseidon31-cico-t16-rf4-rp2` by one part in 2 222 (0.045%) (#322, #490). Three
unrelated workloads landing that close to one cap is not a margin. Two consequences for M27's
baseline:

- The ablation's starting configuration **cannot run the instance the competitive board runs**, so
  no ablation row on this instance is comparable to a board row.
- **Every figure taken under the current cap is a figure under a policy, not a property of the
  implementation** (#490). Raising `max_live_bytes` to 400 MB would admit 25 000 000 entries and
  turn three `stopped_at_limit` rows into completions, which is why #469 declined to do it as a
  side effect.

### 2.3 Re-verified at `53fbf50`, after #476/#478/#479 landed

`main` moved four merges mid-freeze. One `f4_profile -- mq` invocation at `53fbf50`, same protocol,
same digest assertion:

| | total/ms | symbolic | construction | elimination | extraction | **interreduction** | other |
|---|---:|---:|---:|---:|---:|---:|---:|
| `53fbf50` | 31 257.3 | 422.3 | 1 052.6 | 4 299.8 | 109.0 | **25 289.0** | 84.7 |
| share | — | 1.35% | 3.37% | 13.76% | 0.35% | **80.91%** | 0.27% |

Work counts again identical: 10 batches, 1 777 pairs, 247 elements. **The interreduction share is
80.91%**, against #349's 80.4% pre-#437 and §2's 79.5% at `1985504`. The three agree.

**Why the share did not move when a 3.6x on that stage had just merged.** Because the stage that
merged is **off by default**. `F4Options::recommended()` — which `Default` returns, and which
`competitive_sweep.rs` builds — sets `interreduce_by_matrix: false`, documented in `options.rs` as
*"off by default until the A/B is on record, which is the discipline every other strategy flag in
this struct follows."* So:

> **No row on the competitive board, and no run through `F4Options::default()`, currently gets the
> matrix route.** The 80% interreduction share and the 29 011 ms board figure remain the accurate
> description of `main`'s default path. Flipping the flag is a separate decision on separate
> evidence, and §2.4 is that evidence re-taken.

**Since #507, the board does carry matrix-route rows** — `mq-random-10` at both tasks and
`katsura-11`, each labelled in its `library_version` — and `F4Options::default()` still does not
produce them: the option is now `InterreductionRoute`, and its default is still `Division`. So the
29 011 ms figure remains the accurate description of the default path, for the reason in
`interreduction-cost.md` §3e.3 rather than for want of an A/B.

### 2.4 The interreduction A/B at `53fbf50`, and it comes in at 3.63x rather than 4.18x

#478 landed `f4_profile -- mq-matrix`, which runs both routes **interleaved in one process on one
build** — so no cross-build or cross-session difference is inside the ratio. One invocation under
the lock, `taskset -c 0-7`:

| rep | route | total/ms | interreduction/ms | interreduction % | basis |
|---:|---|---:|---:|---:|---:|
| 1 | division | 29 624.85 | 23 654.83 | 79.85 | 247 |
| 1 | **matrix** | **8 130.62** | **2 299.22** | **28.28** | 247 |
| 2 | division | 29 259.64 | 23 385.60 | 79.92 | 247 |
| 2 | **matrix** | **8 091.84** | **2 306.05** | **28.50** | 247 |
| 3 | division | 29 512.52 | 23 719.00 | 80.37 | 247 |
| 3 | **matrix** | **8 152.14** | **2 313.35** | **28.38** | 247 |
| **mean** | division | **29 465.7** | **23 586.5** | **80.05** | 247 |
| **mean** | **matrix** | **8 124.9** | **2 306.2** | **28.38** | 247 |

Matrix shape **7 642 × 7 996, 893 531 nonzeros** (1.46% dense), 247 elements — the rows and columns
match #477's table exactly, and 7 642 × 7 996 = 61 105 432 cells is #477's cell count to the digit.
Both routes return a basis of 247 elements and the example **asserts them equal** rather than
assuming it.

| quantity | value |
|---|---:|
| **end to end** | **3.627x** |
| the interreduction stage alone | **10.23x** |
| everything except interreduction | **1.010x** |
| Amdahl ceiling if the stage were free | 5.01x |

**The A/B is internally sound, and the third row is why.** Everything outside interreduction costs
the same to within **1.0%** across the two routes, which is what must happen if the routes are
identical up to the final stage — so the ratio is measuring the stage and nothing else.

**But the end-to-end figure is 3.63x, where #478 reports 4.18x median.** Both were taken with the
same interleaved harness, so the difference is not the instrument. #478's own table makes it
legible:

| | division total | its stage | matrix total | its stage | end to end | stage |
|---|---:|---:|---:|---:|---:|---:|
| **#478** (PR table, mean of 3) | 40 712.5 | 35 122.6 (**86.27%**) | 9 690.6 | 4 094.5 (42.25%) | **4.20x** | 8.58x |
| **here** (`53fbf50`, mean of 3) | 29 465.7 | 23 586.5 (**80.05%**) | 8 124.9 | 2 306.2 (28.38%) | **3.63x** | **10.23x** |
| their / mine | 1.382x | 1.489x | 1.193x | 1.775x | | |

**Every column of #478's run is slower than this one, and the interreduction stage is slower by
more than the rest.** Decisive detail: **#478's division side is 1.40x the board row** that all of
M27's ratios are quoted against (40 712.5 against 29 011.4 ms), where this one is **1.016x** it. And
#478's interreduction share is **86.27%**, where #349 (80.4%), §2 (79.5%) and §2.3 (80.91%) all
agree on ~80%.

> **The 4.18x was measured on a box state in which the stage being removed was itself inflated —
> which inflates the ratio, because the numerator is the thing being taken away.** Hence the two
> figures move in apparently opposite directions: #478's end-to-end ratio is *higher* while its
> stage-level ratio is *lower* (8.58x against 10.23x), exactly what a disproportionately contended
> division stage produces.

**This is a discrepancy, not a refutation.** The change, the mechanism and the matrix shape are
identical, both A/Bs are internally interleaved, and both clear M27's 2x minimum by a wide margin.
But **3.63x is the figure to carry forward**, for one stated reason: its division side agrees with
the board row to 1.6%, so it is the only one of the two that composes with §1.1's ratios. #478's
4.18x should not be quoted against a board figure, and #477's "remaining stage cost is 4 094 ms"
belongs to the same loaded run — the stage measures **2 306 ms** here, 1.78x less.

**M27-A's target should be quoted as 3.63x end to end from the matrix route, with the Amdahl
remainder stated**: the stage falls to 28.4% from 80%, and the ceiling from removing what remains of
it falls from 5.01x to **1.40x**.

Projected onto §1.1's board row — **applying the measured 3.627x to the board's own 29 011.4 ms
rather than pairing an instrumented total with an uninstrumented comparand**, since both sides must
come from the same measurement regime — the matrix route would put Zeebra at **~7 999 ms**:

| comparand | board figure | Zeebra projected at 3.627x | gap |
|---|---:|---:|---:|
| singular | 7 001.1 ms | 7 999 ms | **1.14x behind** |
| msolve | 243.1 ms | 7 999 ms | 32.9x behind |
| groebner.jl | 83.4 ms | 7 999 ms | 95.9x behind |

**That is M27's 2x minimum met on this row, and it is not Singular parity — it stops 1.14x short.**
M27's plan computed 5 686 ms and "1.23x ahead of Singular" for interreduction becoming *free*; the
stage does not become free, it becomes 2 306 ms, and those 2 306 ms are the difference between
leading Singular and trailing it. Parity on this row needs the matrix pass itself cut by about half
again.

**This projection is arithmetic on two measurements and is not itself a measurement.** The board row
must be re-taken with the flag on before any of it is published.

> **Re-taken, and the projection held.** #507 took the row as a five-engine cohort at one commit on
> the pinned digest — `docs/research/interreduction-cost.md` §3e.0. Measured: **8 333.1 ms** mean of
> three against the 7 999 ms projected here, **4.2% out**, and **1.07x behind Singular** against the
> 1.14x projected. End to end the cohort gives 3.74x on the means and **3.69x on the minima**, the
> latter 1.8% from the 3.627x applied above. The division side's ratio against this cohort's own
> Singular is 4.01x–4.02x against the retained 4.126x, so the cohort composes with §1.1 to about 5%
> — this box's run-to-run spread, not a disagreement.
>
> Two things §2.4 could not have said. On `lex-basis-by-conversion` the matrix route reaches
> **8 827.7 ms against Singular's 9 643.7 ms** — parity, and the first `mq-random-10` row not behind
> Singular. And **the default did not move anyway**: peak RSS, which `f4_profile` does not report,
> goes 163.4 MB → 600.8 MB here and **534.6 MB → 13 148.3 MB on katsura-11**, with every budget
> satisfied, because the refusal counts matrix entries and the entries are not where the memory
> goes. §3e.3 and **#536**.

---

## 3. The cryptanalysis frontier, by class, never summed

From `research/scoreboard/SCOREBOARD.md` and the 61 registered challenges with 78 retained runs.
**An engineering surrogate's witness is not evidence about a public challenge**, and these three
tables may not be added together or read as one ladder.

### 3.1 `Official` — 48 registered, 5 attempted, **43 not attempted**

| | |
|---|---|
| **hardest completed** | `fukuoka-mq-III-n15-seed0` — 15 vars / 30 eqs, **verified witness in 7 798.5 ms**, as published |
| also completed | `fukuoka-mq-III-n10-seed0` (10/20, 106.4 ms); `fukuoka-mq-VI-n10-seed0` (10/7, 577.8 ms, slice(3 fixed, seed 7)) |
| attempted, not completed | `fukuoka-mq-III-n20-seed0`; `fukuoka-mq-VI-n15-seed0` |
| **not attempted** | **43 of 48** |

**Every completion in this class is a toy example published with its answer.** That is a real and
correctly-labelled result, and it is not challenge participation: `SUPPORTED_DIMENSIONS` stops at
`n = 20` and the smallest *real* contest instance in an importable type is type VI `m = 16`, which
the generator renders at `n = 24` (#454). Until the dispatch reaches 24 there is no registered row
Zeebra can attempt that is not a toy example.

> **Correction to #451.** It states "39 of 48 official registry rows are `not attempted`". The
> figure is **43 of 48** — 48 rows, 5 of which carry a run. Counted from the generated table and
> from the 61 challenge files independently; both give 43.

### 3.2 `FaithfulReduction` — 9 registered, 9 attempted, 5 completed

| | |
|---|---|
| **hardest completed, by round count** | `poseidon31-cico-t16-rf4-rp2` — 80 vars / 68 eqs, **verified witness in 328 219.0 ms on 32 workers**, resultant, slice(12 fixed, seed 1) |
| **hardest completed, by wall clock** | `poseidon31-cico-t16-rf2-rp4` — 50 vars / 70 eqs, 3 274 316.5 ms on 32 workers (**54.6 min**, 10x `rf4-rp2`'s wall) |
| also completed | `rf2-rp0` (6.0 ms), `rf2-rp2` (47 598.5 ms), `rf4-rp0` (50 638.1 ms) |
| not completed | `rf4-rp4`, `rf6-rp0`, `rf6-rp2`, `rf6-rp4` |

**These two "hardest" are different achievements and the distinction is #370's acceptance criterion
4.** `rf4-rp2` has more *full* rounds; `rf2-rp4` has more *partial* rounds and costs 10x the wall.
A frontier claim must say which it means. #451 names `rf4-rp2` as the class frontier, which is the
round-count reading, and this document adopts it **with the qualifier stated**.

Every witness in this class says **nothing** about the official target it reduced from, which the
retained record states in its own `significance` field: *"witness for a reduction of
poseidon31-cico-rf6-rp8; says nothing about it."*

### 3.3 `Engineering` — 4 registered, 4 attempted, 3 completed

`poseidon-t2-rf2-rp0-planted` (0.8 ms), `poseidon-t2-rf2-rp2-planted` (141.2 ms),
`poseidon-t2-rf4-rp0-planted` (348.3 ms), all as generated. `poseidon-t3-rf2-rp1-planted` stopped at
`max_matrix_columns`, degree 11. Reduced width, planted targets: evidence about the implementation
and about nothing else.

### 3.4 One board defect found while reading the frontier

`SCOREBOARD.md`'s "Where the unfinished runs stopped" table has **38 rows containing duplicates**:
`poseidon-t3-rf2-rp1-planted / as generated / max_matrix_columns at degree 11 / 42229 cols /
155.3 MB` appears **three times**, byte-identical. `poseidon31-cico-t16-rf2-rp0 / slice(12 fixed,
seed 0)` appears twice with two different outcomes (`basis only, no witness` and `the slice is
empty`). The table is generated, so the duplication is in the run set or the generator, not in the
prose. It does not change any frontier figure above — none of the duplicated rows is a completion —
but a reader counting stopped runs will overcount. **Filed for M27-C**, which owns the board
defects; recorded here so the frontier count is not read off that table.

**Resolved (#506): the generator, and no record is duplicated.** Checked by hashing each record in
`results/history.json` whole — **zero** byte-identical records. The three planted rows are three
real runs, at `7e333fb` twice (17.09 s and 17.19 s) and `744fdf9` once (18.68 s); the matrix figures
are identical because F4 is deterministic, and the rows rendered identically because the table had a
column for neither the commit nor the elapsed time. The `slice(12 fixed, seed 0)` pair is likewise
**one problem, two runs**: identical frontier down to `peak_live_nonzeros`, at `3fe69c6`
(`basis_only`, no quotient dimension recorded) and `7e333fb` (`slice_established_nothing`,
`quotient_dimension = 81`) — the same computation under a later and more precise verdict, not two
formulations sharing a label. The table now renders one row per distinct rendering with `runs` and
`commits` columns, so the count is 38 rows standing for 40 runs and both facts are readable.

---

## 4. The `rf4-rp2` row: the three cost tables agree, and the discrepancy was a unit

#451 records three "mutually inconsistent" cost tables for `poseidon31-cico-t16-rf4-rp2` and asks
that the row be resolved to the retained record with the other two retained and labelled. **The
stronger result is available: read in the right units the three tables do not disagree on any term,
and both conversion factors are independently measured.**

### 4.1 The retained record is authoritative, and it closes

`research/scoreboard/runs/poseidon31-cico-t16-rf4-rp2--resultant--slice-12-fixed--seed-1---c32--ad7ec4a.json`
— `verified_witness`, class `faithful-reduction`, formulation `resultant, slice(12 fixed, seed 1)`,
challenge digest `80957f3ccf46…`, commit **`ad7ec4a`**, machine **workstation**, **32 logical,
affinity 0-31**, concurrency **32**, release with `RUSTFLAGS` from `.cargo/config.toml`.

| term | seconds | share | source |
|---|---:|---:|---|
| generation (symbolic build) | **289.374** | 88.17% | `stages[generation]` |
| elimination | **38.632** | 11.77% | `stages[elimination]` |
|  — sampling (determinants) | 6.535 | 1.99% | `detail.sampling_us` |
|  — interpolation | 29.323 | 8.93% | `detail.interpolation_us` |
|  — off-domain validation | 2.774 | 0.85% | `detail.validation_us` |
| univariate (root finding) | **0.212** | 0.06% | `stages[univariate]` |
| verification | **0.000** | 0.00% | `stages[verification]`, 8 off-domain checks |
| **total** | **328.219** | 100% | `elapsed_nanos` |
| peak RSS | 825 307 136 B = **825.3 MB** | | `measured_peak_resident_bytes` |

**It is the only one of the three tables that closes.** The four stages sum to the total to within
**0.4 ms in 328 s**, and the three elimination sub-terms sum to the elimination stage to within
**2 µs**. Reproduce with:

```sh
cargo run --release --example resultant_cico -- --row poseidon31-cico-t16-rf4-rp2 \
  --concurrency 32 --kernel euclidean --root-finder deflation \
  --max-samples 59050 --wall-budget 3600 --write
```

### 4.2 #410's table is a **one-core cost model**, and that is the whole discrepancy

| term | retained (32-worker wall) | #410 (one core) | #410 / retained | reconciles? |
|---|---:|---:|---:|---|
| symbolic build | 289.374 | 324.0 | 1.12x | sequential stage; spread is §6's systematic |
| **determinants** | **6.535** | **65.5** | **10.02x** | **yes — exactly** |
| interpolation | 29.323 | 36.0 *(extrapolated)* | 1.23x | a projection, 23% high |
| **off-domain validation** | **2.774** | **18.6** | **6.70x** | **yes — exactly** |
| root finding | 0.212 | 0.5 *(pessimistic gcd band)* | 2.36x | a band, not a point |

**The determinant term.** 59 050 determinants × 1.109 ms one-core (§5.5 of #350) = **65.49 s**,
which is #410's 65.5 s to three figures. Against the retained 32-worker wall of 6.535 s that is a
speedup of **10.02x**. #412 measured the Euclidean kernel's width penalty at 32 workers as
**3.21x**, which predicts 32 / 3.21 = **9.97x**. The two agree to **0.52%**.

Reconstructed forward from first principles, 59 050 × 1.109 ms / 32 × 3.21 = **6.569 s** against the
record's **6.535 s** — **0.5%**. The retained figure, #410's figure and #412's penalty are three
views of one measurement and all three are consistent.

**The off-domain term.** #412 puts the Euclidean kernel at **2 094x faster per determinant** than
the dense one at order 1 458, so a dense determinant there costs 1.109 ms × 2 094 = **2.322 s** on
one core and 8 of them **18.58 s** — which is #410's 18.6 s. Against the retained 2.774 s that is
**6.70x**, and with only **8 tasks** the parallel ceiling is 8, not 32: the run achieved **84% of
the available 8-way**. The term that looked like the one genuine 6.7x conflict is the same unit
change with a smaller task count.

**So #410's table is not a competing measurement of the row.** It is a one-core cost model, built
for a budget guard, and its two parallel terms differ from the record by exactly the two measured
parallel factors. Its `interpolation` is labelled *extrapolated* in #410 itself and was 23% high;
its `root finding` is offered as a pessimistic band. Nothing in it contradicts the record.

### 4.3 The third table is a different run, not a correction

| term | retained | circulating | ratio |
|---|---:|---:|---:|
| total | 328.219 | 362 | 1.103x |
| generation | 289.374 | 320.8 | 1.109x |
| determinants | 6.535 | 6.57 | 1.005x |
| interpolation | 29.323 | 31.7 | 1.081x |
| root finding | 0.212 | 0.19 | 0.896x |
| peak RSS | 825.3 MB | ~726 MB | 0.880x |

Every term is within 1.005x–1.11x of the record **in the same units**, and the circulating table's
stated terms sum to 359.26 against its total of 362 — leaving **2.74 s** unaccounted, which is the
record's off-domain validation term (2.774 s) omitted rather than disagreed with. This is an
**unretained run of the same configuration**, and its spread from the record sits inside §6's
systematic. It is retained here as what it is and is **not** a correction to anything.

### 4.4 The resolution, stated once

> **The `rf4-rp2` row is `ad7ec4a`'s retained record: 328.219 s total, 289.374 s symbolic,
> 38.632 s elimination, 0.212 s root finding, 825.3 MB peak, 32 workers at affinity 0-31.** #410's
> table is a one-core cost model of the same row and agrees with it on every term once converted at
> the two measured parallel factors (10.02x over 59 050 tasks, 6.70x over 8). The third table is an
> unretained run of the same configuration, 1.10x slower end to end. **All three are retained**; the
> cost-model register's append-only rule is what makes that the correct outcome rather than erasing
> two of them.

### 4.5 One stale reading this row invites, flagged rather than fixed

`resultant-elimination.md` §6.9's "The rows restated" table, and the `README.md` passage that quotes
it, project `rf4-rp2`'s determinant stage at **1.79 h on 32 workers**. The retained record measures that stage at **6.535 s** — a collapse of
**986x**. Both figures are correct and properly labelled: 1.79 h is the **dense** route at
2.404–3.148 s a determinant, and 6.535 s is the **Euclidean** route #350 introduced, whose
per-determinant advantage #412 measures at 2 094x. The hazard is that §6.9's table is headed
*"Determinant time only — the symbolic build … not in these numbers"*, so a reader taking 1.79 h as
the row's cost is reading a dense-route determinant projection as a Euclidean-route row total and
will be wrong by three orders of magnitude in one direction and by the missing 88% in the other.
**Not edited here** — it belongs to #410's "report which terms are modelled" and to #370's prose
pass — but no M27 figure should be derived from it.

---

## 5. Provenance: what is traceable, and one defect that recording the commit does not fix

### 5.1 Reproduction commands, per figure class

| figure class | regenerate with | provenance |
|---|---|---|
| competitive rows (§1) | `examples/competitive_sweep` | `history.json`, append-only, per-row `environment.commit` |
| the stage split (§2) | `examples/f4_profile -- mq` | digest-asserted in the example; commit `1985504` |
| scoreboard rows (§3) | `examples/<row example> --write` | `research/scoreboard/runs/*.json`, one file per run |
| the `rf4-rp2` row (§4) | `examples/resultant_cico … --write` | the retained record's own `reproduce` field |

### 5.2 Three of the four competitive cohorts were taken at commits unreachable from `main`

`663097a` is an ancestor of `origin/main`. **`7adb29e`, `87a807e` and `a904145` are not.** They were
branch commits on PR #435's history and did not survive the merge, so:

> **Every five-library figure in §1 — including the 348x that all of M27-A is organized around —
> records a commit that cannot be checked out from `main`.**

#335 asks that every measurement record the commit it was taken at. These do. The letter of the
criterion is met and its purpose is not: the figures cannot be re-taken at the stated commit,
because the stated commit is not reachable. The rows remain usable — they are internally consistent,
they agree across two characteristics (§1.1), and the `663097a` cohort that *is* reachable
corroborates the zeebra and singular sides to 1.1% — but **"re-measure at `7adb29e`" is not an
instruction anyone can now carry out.** Filed as a follow-up; the fix is for the sweep to record a
commit reachable from the branch it will merge to, or to re-stamp on merge.

**Resolved (#505), and resolved for the rows already on record.** Every row now carries two more
fields beside `commit`:

| field | what it is | why it cannot dangle |
|---|---|---|
| `base_commit` | `git merge-base HEAD origin/main` | a merge base is an ancestor of `main` and nothing can make it stop being one |
| `patch_id` | `git patch-id --stable` over `base_commit..commit` | a function of the **diff**, so a reader recomputes it over a candidate range rather than needing the object to have survived |

`Environment::stamp_is_resolvable` is the criterion, and two tests assert it over the committed
files — one per board — so a sweep cannot reintroduce the defect. The three unreachable cohorts were
stamped retroactively, which was possible only because their commit objects still existed in a local
checkout; `commit` was left exactly as recorded rather than overwritten:

| cohort | base, on `main` | patch id |
|---|---|---|
| `7adb29e` | `7ab1e86` | `b2b959eaed68…` |
| `87a807e` | `5398c83` | `a7f82d37d070…` |
| `a904145` | `6e67953` | `b0855cb27e70…` |

A **second instance** turned up on the cryptanalysis side while fixing this one: `1409a48`, two runs
in `research/scoreboard/results/history.json`, likewise unreachable, base `1985504`. Both boards
share one `Environment`, so both are fixed by the same change. The 23 cost-model rows #294
transcribed carry an empty `commit` and remain unresolvable — that is #335's backlog, not this
defect: nothing was lost by a merge, the commit was never written down.

Note what a patch id does and does not buy. It identifies *what was measured*; it does not resurrect
a deleted object. A reader who wants the exact tree checks out `base_commit` and then looks for the
range on `main` whose patch id matches — which is a procedure, where before there was none.

---

## 6. The #318/#319 systematic, bounded — and narrowed by the competitive cohorts

#451 requires that these be resolved or explicitly bounded, and that no M27 ratio cross the boundary
without carrying it. **They are not resolved. This is the bound.**

### 6.1 They are one question seen twice

#319 says so in its own last line: *"it is the same ~1.2x question seen through the worker count."*
#318 is the drift between a figure on record and the same measurement today; #319 is the drift
between §6.6's width penalty and today's.

### 6.2 The bound on #318 is **not a uniform scale factor**, and that is the finding

| measurement | on record | re-measured | ratio |
|---|---:|---:|---:|
| order-162 determinant, 1 worker, reference route on `rf2-rp2` | 2.868 ms | 3.439 ms | **1.199x** |
| order-162 determinant, 1 worker, synthetic pair | — | 3.624 ms | **1.264x** vs §6.5 |
| order-18 determinant, 1 worker | 8.45–8.6 µs | 7.88 µs | **0.92x** |
| order-1 458 determinant, 32 workers, core time | 2.70 s | 3.148 s | **1.166x** |

Three point one way by ~1.2x; the smallest order points the **other** way. So the honest bound is a
**bracket, not a factor**:

> **Any ratio pairing a pre-M25 `resultant-elimination.md` §6.5/§6.6 figure with a figure taken now
> carries up to +26% / −8% of unexplained drift, and its sign depends on matrix order.**

A single ~20% correction factor is therefore *not* available, and applying one would be a fourth
unretained figure. The order-18 reversal is itself informative — it suggests fixed per-determinant
overhead got cheaper while the inner loop got dearer — and it is the reason "machine drift" does not
yet explain the set.

### 6.3 The bound on #319

| order | 1 worker | 8 workers | 32 workers | 32 w, 4 dets/worker |
|---:|---:|---:|---:|---:|
| 162 | 3.624 ms | 1.11x | **1.44x** | — |
| 486 | 94.494 ms | 1.13x | **1.44x** | — |
| 1 458 | 2.404 s | 1.17x | **1.52x** | **1.31x** |

§6.6 recorded 1.04–1.09x for the same thing: the measured penalty is **4 to 10 times** what is on
record. §6.6's *mechanism* survives — the penalty is 1.44x at both order 162 and order 486, whose
matrices differ by 9x, which a bandwidth limit would not do — but its *size* does not.

> **Any 32-worker projection from a 1-worker anchor carries 1.31x–1.52x, where §6.6 would have said
> 1.04–1.09x.** Project with **1.31x**, not 1.52x: a row sees the un-amortized first-touch cost only
> in its last ragged block.

### 6.4 What the competitive cohorts newly contribute: the drift is **not machine-wide**

This is new evidence #318 and #319 did not have. The `663097a` and `7adb29e` cohorts are the same
digests on the same machine at the same affinity, 19 hours apart, with the same rustc:

| row | engine | `663097a` | `7adb29e` | change |
|---|---|---:|---:|---:|
| `mq-random-10` | zeebra | 28 708.5 ms | 29 011.4 ms | **+1.06%** |
| `mq-random-10` | singular | 6 958.8 ms | 7 001.1 ms | **+0.61%** |
| `katsura-7` | zeebra | 25.8 ms | 27.2 ms | +5.24% |
| `poseidon-t2-rf4-rp0-planted` | zeebra | 306.0 ms | 292.8 ms | −4.32% |
| `cyclic-4` | zeebra | 0.1 ms | 0.2 ms | +46.4% |

> **Same-week repeatability on this machine is ~1% where the wall is seconds**, degrading to tens of
> percent on sub-millisecond rows, where it is timer resolution and startup rather than drift.

Two consequences:

1. **The #318/#319 systematic is confined to cross-era comparison, not to this machine's current
   state.** Had the all-core clock drifted 20%, the F4 rows would have moved with it. They moved
   1%. So a ratio formed from two figures taken *in the same cohort* does not carry the systematic;
   only one spanning M25-era records and today does.
2. **It says nothing about #319's width axis.** Every row in the table above is **one worker** at
   affinity 0-7. The width penalty is untested by it, and the determinant path is not the F4 path.

### 6.5 The rule M27 must follow

> A ratio between two figures **in the same cohort** carries no #318/#319 systematic and may be
> quoted plainly. A ratio **spanning a pre-M25 record and a current figure** carries +26%/−8% and
> must say so on the line that quotes it. A **32-worker projection from a 1-worker anchor** carries
> 1.31x–1.52x. §1.1's cross-library ratios are all within-cohort and are clean.

---

## 7. Each M27 target's barrier, by stage reached and the reason it stopped

**Runtime alone is not an indicator of progress toward a solution, and a larger degree crossed is
not nearer one.** This table names the bound that bound, not the time spent.

| target | class | stage reached | the actual barrier |
|---|---|---|---|
| `mq-random-10` basis | corpus | **completes** | **time**: 80.9% in final interreduction on the default path (§2.3), 348x behind Groebner.jl. Not a limit. With `interreduce_by_matrix` on, 28.4% and 3.63x faster (§2.4) — but that flag is off by default |
| `mq-random-10` under `baseline()` | corpus | refuses | `max_live_nonzeros`, 20 000 277 / 20 000 000 — **one part in 72 202** (§2.2) |
| `fukuoka-mq-III-n20-seed0` | official | degree 5, **4 completed** | `max_live_nonzeros`, 20 001 424 / 20 000 000 — **one part in 14 045**; 10 297 × 10 147 matrix, 195.5 MB accounted. **Stale: predates #305** (#453) |
| `fukuoka-mq-VI-n15-seed0` | official | degree 9, **8 completed**, 8 slices | `max_live_nonzeros` on every slice, 20 146 cols, ~217.9 MB; campaign reached **no verdict**. **No slice tested whether a solution exists** |
| types I/II/IV/V, any real size | official | **not importable** | `SUPPORTED_DIMENSIONS = [10, 15, 20]`; smallest real instance needs **n = 24** (#454) |
| `poseidon31-cico-t16-rf4-rp4` | faithful | degree 5, 4 completed | `max_live_nonzeros`; 24 441 cols, 29.8 MB |
| `rf6-rp0` / `rp2` / `rp4` | faithful | degree 5, 4 completed | `max_live_nonzeros`; 28 794 / 31 296 / 34 639 cols, 30.6–40.7 MB |
| `poseidon-t3-rf2-rp1-planted` | engineering | degree 11, 10 completed | `max_matrix_columns`; 42 229 cols, 155.3 MB |

**The pattern is one barrier, and it is a policy rather than a resource.** Every target above that
stops at a budget stops at `max_live_nonzeros` except one — the planted surrogate, which stops at
`max_matrix_columns` — and three cross it by **less than 0.05%**: `mq-random-10` by one part in
72 202, III n=20 by one part in 14 045, `rf4-rp2` by one part in 2 222. The accounted working sets
at those stops are all **under 220 MB** on a 300 GB machine. #305 already took III n=20's peak RSS from 13 996 MB
to 1 496.5 MB and the budget still refuses it on a 195 MB matrix, which is #453's whole point: that
record describes a machine state that no longer exists, and **re-diagnosing it costs one short run**.

Whether 20 000 000 was ever chosen against a measured working set is **unanswered** (#490).

---

## 8. #412, recorded as a falsified hypothesis

#451 requires this be on record as a falsification with its mechanism still unmeasured. It is.

**The hypothesis.** #350 §4 and `structured-sylvester.md` §5.2 predicted that axis 4 would *recover*
#319's width penalty along with the exponent: the per-sample working set falls from a 17 MB matrix
to two ~6 kB coefficient vectors, a factor of ~2 800, so bandwidth contention should go with it.

**The measurement, which settled it in the other direction.** `rf4-rp2`, 59 050 determinants of
order 1 458, Euclidean kernel, 32 workers, on the lock, `taskset -c 0-31`:

| quantity | value |
|---|---:|
| determinant stage wall | 6.574 s |
| core time (× 32) | 210.4 s |
| core time per determinant | 3.563 ms |
| the same on one core | 1.109 ms |
| **width penalty at 32 workers** | **3.21x** |
| the dense kernel's, for comparison | 1.32x modelled, 1.31–1.44x measured (#319) |

**The ~6 kB working set contends worse than the 17 MB one** — 3.21x against 1.31–1.44x. Whatever
dominates here, it is not the quantity the prediction was about.

**Corroboration from §4.** #412's stage wall of 6.574 s and the retained record's 6.535 s are the
same measurement to **0.59%**, and the penalty it reports reconstructs the record's sampling term to
**0.5%** (§4.2). The falsification rests on a figure that two independent routes confirm.

**Why it is load-bearing and not an accounting note.** `euclidean_core_ms` was first written using
the dense `width_penalty` on the stated reasoning that doing so was conservative. It was not: the
guard predicted **2.7 s** for a stage that took **6.574 s**, under-predicting by **2.43x**.
Corrected in #367 to a measured two-point penalty.

**The mechanism was measured, and the falsification does not survive it.** See
`structured-sylvester.md` §5.6.2. The 3.21x above is correct arithmetic over two correct
measurements and **it is not a width penalty**: the `1.109 ms` and the `3.563 ms` were taken over
two different *pairs*, and the per-sample cost of those two pairs differs by **3.01x at identical
width**. Swept in one process over the `rf4-rp2` row's own two polynomials the Euclidean kernel is
**1.100x at 32 workers — 90.9% parallel efficiency**, and the dense kernel measured in the same
session is the worse of the two at every width they share. `2.90 × 1.100 = 3.19` against 3.21, and
the 32-worker end re-measures at 3.584 ms against the recorded 3.563 ms.

The missing quantity is a **term of the cost law**, not a property of the machine.
`sylvester_resultant_euclid` specializes the pair at each sample point inside the per-determinant
timer, which on a row of total degree `d = 3^R` is `d(d + 1)` Horner multiply-adds — **2.00x the
remainder sequence's own operation count**, counted off the pairs at three orders. On
`determinant_sweep`'s synthetic pair, which is degree 1 in the surviving variable, it is 1 460 steps
and 0.4% of the determinant. That is the whole of the gap.

The **allocator candidate is refuted**: the Euclidean kernel makes 1 391 allocation calls per
determinant against the dense kernel's 666 and has the *lower* width penalty; the half of the kernel
holding every per-step allocation contends within 1.7% of the half holding two; and the penalty
*falls* with order — 1.370x / 1.114x / 1.100x at 162 / 486 / 1 458 — which is thread-spawn overhead
amortizing, the opposite shape from contention.

**So what #451 required on record is this**: §5.2's prediction that axis 4 would not contend worse
was **right**, the measurement that appeared to falsify it was a one-term cost law reading a missing
term as contention, and the guard was right about `rf4-rp2` only because a 3x-low anchor and a
3x-high penalty cancelled. `euclidean_core_ms` is now two terms and no longer depends on that
cancellation.

**Not claimed:** that the Euclidean kernel is a bad choice. It is 2 094x faster per determinant at
this order and it is what made the row run in 5.47 minutes instead of a projected 1.79 h (§4.5).

---

## 9. #410's defect, stated precisely — and why it is a safety fix

**Not fixed here.** #410 is a separate issue, now Priority High, and it is a code change to
`examples/resultant_cico.rs` under an issue whose own scope is to freeze figures. What this document
owes it is the measured term shares that make the fix mechanical, and §4.2's finding that the
guard's table is a one-core model.

`RowCost::of` costs exactly one term:

```rust
let each = kernel_core_ms(kernel, matrix_order, workers) / 1e3 / workers.max(1) as f64;
predicted_seconds: samples as f64 * each,
```

No symbolic build, no interpolation, no root finding. Against the **retained record's own measured
shares** (§4.1):

| term | share of the row | modelled by the guard? |
|---|---:|:---:|
| generation (symbolic build) | **88.17%** | **no** |
| interpolation | 8.93% | no |
| **determinants** | **1.99%** | **yes** |
| off-domain validation | 0.85% | no |
| root finding | 0.06% | no |

**The guard models 1.99% of the row it admits.** #410 states this as "the 15% and ignores the 73%",
from its own one-core table where the determinant term is inflated 10.02x by the unit (§4.2). In
wall-clock terms — the units `--wall-budget` is denominated in — **the modelled fraction is 2%, not
15%**, so the defect is about 7x worse than #410 describes it.

And it fails in both directions: on `rf6-rp0`, `structured-sylvester.md` §7.1 puts the row at **78%
root finding** after axis 4, a term the guard has never looked at.

> A guard that admits a row by modelling 2% of its cost is not conservative in either direction. It
> did not affect #367 — that row is inside its ceiling on every term — which is precisely why it
> should be fixed before a row whose margin is thinner.

**Not claimed:** that the guard has ever passed a row it should have refused.

---

## 10. Acceptance against #451's five criteria

| # | criterion | status |
|---|---|---|
| 1 | every figure traceable to a regenerable record or a named measurement, with its commit | **met**, §5.1 — and §5.2 records the one place where the commit is unreachable |
| 2 | no ratio quoted across the #318/#319 boundary without its systematic stated | **met**, §6.5 states the rule; §6.4 narrows it to cross-era comparisons |
| 3 | the `rf4-rp2` discrepancy resolved in writing, all three tables retained | **met**, §4 — resolved to the retained record, and the other two reconciled to it rather than merely retained |
| 4 | frontier by class, never summed, slices carrying name and seed | **met**, §3 — with #451's own 39-of-48 corrected to 43 of 48 |
| 5 | what is on `main` distinguished from what is in flight, per engine | **met**, §1 — all five engines are now on `main`; #451's premise was stale |

### 10.1 What this document corrects in #451 itself

1. **All five engines are on `main`** as of PR #435 (2026-11-07T21:52Z). §1.
2. **The retained 4.13x is against 28 708.5 ms**; `30 112` is unsourced in this repository. §1.2.
3. **#304/#437 did not move `mq-random-10`** — the post-#437 cohort is 1.1% *slower*, so the
   4.13x → 3.98x adjustment would have credited an improvement that was not measured. §2.1.
4. **43 of 48 official rows are not attempted**, not 39. §3.1.
5. **The three `rf4-rp2` tables are not mutually inconsistent.** Two are a one-core model and an
   unretained run, and both reconcile to the record at independently measured factors. §4.
6. **#410's modelled fraction is 2% of the row in wall clock**, not 15%. §9.

### 10.1a Two findings about work that landed during the freeze

7. **#478's matrix route is off in `default()`**, so the 4.18x reaches no board row and no
   default-path run. The 80% interreduction share still describes `main`. §2.3.
8. **The interleaved A/B measures 3.63x end to end, not #478's 4.18x.** #478's division side is
   1.40x the board row and its interreduction share 86.27% against the ~80% that three other
   measurements agree on, so the stage it removed was itself inflated. **3.63x is the figure that
   composes with §1.1**, because its division side agrees with the board row to 1.6%. At 3.63x this
   row lands **1.14x behind Singular rather than 1.23x ahead**: the matrix route clears M27's 2x
   minimum and does **not** reach parity on it. §2.4.

### 10.2 Deliberately not done

- **#318/#319 are bounded, not resolved** (§6). Resolving them means bisecting the order-162
  reference measurement over the commit range, which is their own issues' work and is a measurement
  campaign rather than a freeze.
- **#410 is not fixed** (§9), for the reason stated there.
- **`README.md`'s Status list is untouched** — #370's, and #451 scopes it out. §4.5 flags one
  further README passage for that pass without editing it.
- **No new frontier measurement was taken.** §3 reports the frontier that exists.
- **PR #435 was neither merged nor modified by this work**; it merged independently during it.
