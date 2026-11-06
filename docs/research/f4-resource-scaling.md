# F4 resource scaling: what a larger live-entry budget buys, and what it does not

Deliverable for M24-D (#215). One question, which no amount of argument could settle: when a
registered problem stops at `max_live_nonzeros`, is it **out of reach** or merely **out of this
budget**?

The answer is both narrower and more interesting than the question. More budget buys almost
nothing, and — separately — **the budget is not what bounds the memory.**

## 1. What M23 left open

M23's full-width frontier ran at 20 000 000 live entries, 200 000 columns, and a wall clock that
never bound. Under it, fourteen of eighteen full-width Poseidon rows crossed the entry cap at
**degree 4 or 5**, and `fukuoka-mq-III-n20-seed0` crossed it at degree 5 after 67.5 s
([`fukuoka-mq.md`](fukuoka-mq.md) §4.1). Those are modest budgets against a 503 GB workstation, and
`MILESTONE-CRYPTANALYSIS-SCOREBOARD.md` §5b.2 had just moved the binding bound from columns to
entries — so the entry cap was the right axis to sweep and nobody had swept it.

The knobs already existed. `examples/scoreboard.rs` reads `ZEEBRA_MAX_ENTRIES` and
`ZEEBRA_WALL_SECONDS`, and the comment at the call site states their purpose in exactly these
terms. So this is a measurement campaign and not a build, and **no default was changed by it** —
every M23 figure still reproduces from the default configuration.

## 2. The instruments, and the one that was wrong

Three quantities, deliberately kept apart:

| quantity | where it comes from | what it is |
|---|---|---|
| live nonzero entries | the solver's own counter, in the stop message | what the budget bounds |
| `peak_estimated_bytes` | the run record, at 16 bytes an entry | an estimate of **one** allocation |
| peak process RSS | `/proc/<pid>/status` `VmHWM`, and `/usr/bin/time -v` | what the machine actually paid |

The third is the one M24-D exists to add, because the gap between it and the second is precisely
what the estimate cannot see.

**A harness defect, recorded because it produced a figure that was wrong by four orders of
magnitude.** The first peak-RSS probe read `/proc/$!/status` after backgrounding
`timeout … taskset … scoreboard`. `taskset` **execs**, so its pid is the solver's; `timeout`
**forks**, so its pid is not. The probe reported **2 MB** — `timeout`'s own footprint — for a run
that actually peaked at 14 GB. A measurement that is wrong by 7 000x looks exactly like a
measurement, which is the argument for cross-checking an instrument before trusting a surprise.

Cross-checked after the fix, on the same configuration: `/usr/bin/time -v` reports 14 406 056 kB
and `VmHWM` reports 14 412 076 kB — **0.04% apart**, from two independent mechanisms. The surprise
is real.

## 3. The ladder

`fukuoka-mq-III-n20-seed0`, 20 variables, 40 equations over GF(31), grevlex, as published. Pinned
to cores 0–7, `ZEEBRA_AFFINITY=0-7`, release with fat LTO and `-C target-cpu=x86-64-v3`.

| live-entry cap | entries needed | stopped during degree | last completed stage | peak RSS |
|---:|---:|---:|---|---:|
| 2 000 000 | 2 000 076 | **4** | generation | **617 MB** |
| 10 000 000 | 10 000 178 | **4** | generation | **617 MB** |
| 20 000 000 | 20 001 424 | **5** | generation | **14 072 MB** |
| 50 000 000 | 50 004 816 | **5** | generation | **14 073 MB** |
| 100 000 000 | 100 002 185 | **5** | generation | **14 073 MB** |

The 20 000 000 row reproduces M23's record exactly — same limiting resource, same degree, same
stage, and the identical entry count **20 001 424** — which is what makes the rest of the column a
comparison rather than a new experiment. Its runtime, 70.9 s against M23's 67.5 s, is inside this
machine's noise and is not read.

**Every row stops the same way, and the pattern is weaker evidence than it looks.** The
entries-needed figure sits a few thousand above whatever cap it was given — 1 424 above 2M, 178
above 10M, 2 185 above 100M.

A first reading of that is "the requirement is far above the budget, detected the moment the counter
crosses it". **That reading is not supported by these rows**, and it was in an earlier draft of this
document. Live entry counts grow monotonically as a batch accumulates, so a cap placed anywhere
along that growth is crossed at `cap + ε` whatever the eventual requirement is. The pattern is
equally consistent with a requirement of 20M, of 100M, or of 10^10 — it distinguishes none of them,
and what it actually measures is that the counter is checked densely.

Separating those needs a cap the computation does **not** cross, and §6a is that experiment. What
the rows above do establish, without interpretation, is that **no cap from 2M to 100M changes the
outcome's shape**: the same limiting resource, the same stage, and only two distinct peak-RSS
values.

## 4. Peak RSS does not move with the budget

This is the finding, and it was not what the ladder was built to look for. Its *cause* is a separate
question that §6a reopens and does not close.

```
caps  2 000 000 and  10 000 000              ->  degree 4  ->   617 MB  (631 888 / 632 172 kB)
caps 20 000 000, 50 000 000 and 100 000 000  ->  degree 5  ->  14.07 GB (14 406 056 / 14 410 724 / 14 411 520 kB)
```

Two groups. Inside the degree-4 group the cap differs by 5x and the peaks agree to **0.04%**; inside
the degree-5 group the cap differs by **5x** — a 20M-to-100M span — and the three peaks agree to
**0.01%**. Across the groups the cap differs by only 2x and the peak differs by **22.8x**.

Five caps, two values, and within each group the budget moves the peak by nothing measurable.

> **Read §6a before drawing a mechanism from this.** Two further rungs with the cap effectively
> removed plateau at a **third** value, 4 978 MB, *below* the degree-5 group while doing strictly
> more work. So the description above is accurate for these five rows and the obvious causal
> reading of it — that this is what entering degree 5 costs — is **false**.

Whatever the mechanism, the magnitude is not in doubt: across every row in this document the entry
counter accounts for at most 1.3% of peak RSS, and the gap is between **0.6 GB and 14 GB** of
memory the budget does not see.

## 5. What the byte accounting bounds, and what it does not

At the 20 000 000 cap, M23's record gives `peak_estimated_bytes = 195 474 568` — 195 MB — against a
measured 14.75 GB of process RSS. **The accounting sees 1.3% of what the run costs.**

| | at the 20M cap |
|---|---:|
| accounted: `peak_live_nonzeros` × 16 B | 195 MB |
| measured: process `VmHWM` | 14 752 MB |
| ratio | **75x** |

At the degree-4 caps the direction is the same and the factor smaller: 617 MB measured against a
160 MB *cap* (10 000 000 × 16 B), and the accounted peak-live figure is necessarily below that cap,
so 3.9x is a lower bound on the gap there rather than the gap.

**This is not an undocumented behaviour, and the distinction matters.** README's *Entry budgets and
byte budgets* already says so, accurately:

> Neither is a ceiling on the process. … None of them accounts for the monomial-to-column map, the
> basis's term vectors, or allocator overhead; for the process figure use
> `util::peak_resident_bytes`.

So the limit is honest about its scope, and it is reproducible and machine-independent, which is
exactly why M23 chose an entry count over a wall clock. What is new here is **the magnitude and the
shape of the omission**, neither of which the caveat carries:

- **75x.** A documented caveat at 1.2x is a rounding note. The same caveat at 75x changes how the
  limit can be used, and nothing in the repository had attached a number to it.
- **The omitted part does not move with the cap at all, and takes a different value depending on
  which stop the run is heading for** (§4, corrected by §6a). That is not implied by "does not
  account for the monomial-to-column map", and it is what stops the entry budget from working even
  as a rough proxy: the quantity it omits is not a function of the budget, and the largest value it
  takes is reached on the path that *refuses* rather than the path that proceeds.

**The cost of the unquantified caveat, recorded because it was paid.**
`MILESTONE-PUBLISHED-ATTACK-REPRODUCTION.md` §9.1 sized this very ladder as "0.32 / 1.6 / 6.4 /
16 GB of entry storage" at 16 bytes an entry — written by someone who had read the README paragraph
above. A caveat a careful reader discounts anyway is a caveat that needs a figure next to it, and
adding this one to README is the cheapest item in #237.

Where the untracked 98.7% goes is **not established here** and should not be guessed from this
measurement. The step's coincidence with a degree boundary points at degree-5 symbolic
preprocessing — and README's three named categories are the obvious candidates — but attributing it
needs a profile, not an inference from one correlation. That is #237's first task, and it is a
different piece of work from raising a cap.

## 6. The stop rule, and its verdict

M24-D fixed its stop rule before running anything: **stop when one increment of budget buys less
than one additional completed degree.**

| increment | completed degree before | after | verdict |
|---|---|---|---|
| 2M -> 10M (5x) | 3 | 3 | nothing |
| 10M -> 20M (2x) | 3 | **4** | one degree |
| 20M -> 50M (2.5x) | 4 | 4 | nothing |
| 50M -> 100M (2x) | 4 | 4 | nothing |

**What was measured here is the degree the run stopped *during***, which is what the stop message
reports; the completed degree is one below it. That relationship is not assumed — M23's record for
the 20 000 000 row carries both, `max_pair_degree = 5` and `highest_completed_degree = 4`, and the
other rows are read off their stop degree by the same rule. A row whose completed degree were two
below its stop degree would break this column, and nothing in these runs emits that figure directly
without `--write`.

One step in the whole ladder, and it is the smallest increment in it. A 5x increment bought nothing,
then a 2x increment bought a degree, then 5x more bought nothing again. **The rule fires**, and it
fires in a way that says the quantity being bought is not continuous in the budget: a degree either
fits or it does not, and degree 5 does not fit at any budget this ladder reached.

## 6a. The cap removed: the binding resource changes, and that is the real answer

§3 could not distinguish "the requirement is far above the cap" from "the cap is crossed wherever it
is placed". Two rungs with the cap effectively removed settle it, and they settle §1's question
better than the stop rule does.

| live-entry cap | outcome | elapsed | peak RSS |
|---:|---|---:|---:|
| 400 000 000 | **no entry stop** — stopped deliberately at 8 min 38 s to free the benchmark lock | > 8 min | 4 978 MB |
| 1 000 000 000 | **`wall_clock`, 4 batches started** | 2 400 s | **4 978 MB** |

> At a billion live entries the run is **time-bound, not entry-bound**: it got **four batches
> started in forty minutes** and the entry cap never fired. The 2M–100M rows stopped in 1.3–81 s
> because the cap cut them off inside a batch, not because they had reached a wall.

Three things follow, and the first supersedes §3's framing.

**The entry cap was never measuring the requirement.** Remove it and nothing completes anyway. So
"out of reach, not out of budget" is the right answer to §1 — but the evidence is this rung, not the
`cap + ε` pattern, which §3 now says distinguishes nothing.

**The peak-RSS step is about the cap, not about the degree.** This is a correction to §4. Both
uncapped rungs plateau at **4 978 MB** — 4 977 776 kB and 4 977 796 kB, **20 kB apart** — which is
*below* the 14 072 MB that every capped degree-5 row reached. A run doing strictly more work peaks
at a third of the memory. So 14.07 GB is **not what degree 5 costs**; it is reached on the path that
ends in a refusal and not on the path that proceeds. §4's "step function of the degree entered"
holds as a description of the five capped rows and **fails as a causal claim**, and the honest
statement is narrower:

> Peak RSS took exactly two values across five capped rows and a third value across two uncapped
> ones. It tracks **which stop the run is heading for**, which is not a quantity a caller can
> choose.

What produces the 14.07 GB on the refusal path specifically is **not established**, and the
candidates are now different from §5's: the limit check fires during a batch, and `f4_observed_reported`
retains a clone of the system for the report, so an allocation on the error path is as plausible as
one in degree-5 preprocessing. #237's profile should compare a capped run against an uncapped one at
the same point, which is a sharper experiment than profiling either alone.

**A run killed by the wall clock reports no matrix statistics at all** — "F4 has no cooperative time
check, so no matrix statistics exist for a run killed this way". So the group-B metrics M23 §4.3
defines are available only for runs that stop at a *resource* bound, and a time-bound run is
diagnostically poorer than an entry-bound one. That is an argument for keeping the entry cap as the
primary budget even though it does not bound memory: it is the bound that yields a report.

So, for this instance: **out of reach, not out of budget** — and "out of reach" is a statement about
the S-box-per-variable grevlex formulation under F4 and nothing else. M23's §5b.4 reached the same
conclusion from the other direction, where changing the *formulation* of a Poseidon slice was worth
three orders of magnitude and every scheduling strategy was worth 7%–14.5%.

## 7. What this does not say

- **Nothing about Fukuoka III `n = 20` as a problem.** It says this pipeline does not reach it at
  these budgets. The published answer exists and `n = 15` recovers it.
- **No default changed.** The budget is an environment variable that already existed, and its
  absence is the configuration every M23 and M24 scoreboard figure was taken under.
- **No scoreboard record was written.** `--write` was deliberately not passed: `Environment` gained
  a concurrency field in #180 during the same cycle, and a record emitted here would have been keyed
  against a schema in motion. Every figure above is reproducible from §8 without one.
- **The wall clocks are not reported as results.** The box ran three other agents throughout, one of
  them resident at 55 GB. Peak RSS is a per-process high-water mark and is unaffected by that; the
  degree, the stage and the entry counts are deterministic given the budget; elapsed time is not,
  and the 70.9 s control is quoted only against M23's 67.5 s to show the row is the same row.

## 8. Reproducing

```sh
tools/fetch-mq-challenge.sh

ZEEBRA_MAX_ENTRIES=20000000 ZEEBRA_WALL_SECONDS=900 \
  tools/scoreboard.sh mq fukuoka-mq-III-n20-seed0 --seeds 1
```

Vary `ZEEBRA_MAX_ENTRIES` for the other rungs. For the peak-RSS column, background the binary
directly — `taskset` execs and keeps the pid, `timeout` forks and does not (§2) — and poll
`/proc/<pid>/status` for `VmHWM`. Take timings under `tools/benchlock.sh`; the peaks do not need it.
