# F4 resource scaling: what a larger live-entry budget buys, and what it does not

**Measured at:** §§1-10, publication bound `9d05baa2`…`cede98ac` — the commits that published those
figures, recovered from git rather than recorded at the time
([§10](external-comparison-protocol.md#10-the-commit-and-what-a-publication-bound-is)). **§14** is
history read from git plus one exact counter, so it carries no timing and names no box; its figure
is asserted by a test rather than recorded. **§12** was
measured at the tree that section's own change introduces, on branch
`perf/536-interreduce-working-set` (#536), and **§13** at the tree its change introduces, on branch
`perf/554-sparse-row-buffer` (#554): in both the figures and the code that produces them land in one
commit, so the publication bound is that commit and its merge.

Deliverable for M24-D (#215). One question, which no amount of argument could settle: when a
registered problem stops at `max_live_nonzeros`, is it **out of reach** or merely **out of this
budget**?

The answer is both narrower and more interesting than the question. More budget buys almost
nothing, and — separately — **the budget is not what bounds the memory.**

> **M25 (#237) added §9**, which attributes the memory the budget does not see. 88% of peak RSS is
> **one `VecDeque<Monomial<20>>`** in symbolic preprocessing, reached before any matrix exists.
> §9.4a re-runs the capped-against-uncapped comparison §6a asked for and finds the two peaks
> **identical to the kilobyte**, so §6a's 4 978 MB uncapped figure is a measurement error
> and its refusal-path reading is withdrawn. §6a's argument for keeping the entry cap "because it is
> the bound that yields a report" is retracted too, by #284's cooperative time check. Sections 1-8
> are left as they were taken, with retraction markers where a claim no longer stands.
>
> **M25 (#305) added §10**, which bounds that `VecDeque` by deduplicating on push instead of on pop.
> Peak RSS on the same instance falls from 13 996 MB to **1 496.5 MB**, the symbolic closure is proved
> unchanged, and the site that binds is now **the basis, held twice** at the degree-5 rung and
> **matrix construction** at the degree-4 one — so there is no single answer to what dominates F4's
> memory. No stop reason and no default changed, so §§3-9 still reproduce.
>
> **M27 (#536) added §12**, which does the same for the stage after the batch loop. The matrix
> interreduction route took `katsura-11` from 533.0 MB to **13 144.3 MB with every budget
> satisfied**, because the live-entry allowance was checked at construction and not at elimination.
> The peak is **one allocation** — the `SparseRow` entry buffers during back-substitution, 1 584.9 MB
> of payload held in 18 126.4 MB of capacity — and the budget saw the construction's 172.6 MB.
> Budgeting the elimination takes the same run to **1 083.7 MB**. §§1-10 are unaffected: the batch
> loop's allowance already covered its own elimination.
>
> **M27 (#554) added §13**, which removes the amplification §12 only measured. The mechanism was not
> the reserve but the **swap**: installing the reserved buffer in the row left the merge scratch
> holding the row's old one, so the scratch's high-water capacity migrated into whichever row was
> merged next however short that merge was. Copying the result back instead takes `katsura-11` from
> 11.44x the payload to **1.81x** and from 13 145.9 MB to **2 759.5 MB**, with the interreduction
> stage **2.1% faster** — the copy replaces an allocation rather than adding one. Two shrink policies
> were measured against it and both cost more than they save. §12's figures stand as the
> before-and-after's "before".

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

> **Read §6a and then §9.4a before drawing a mechanism from this.** §6a reported two further rungs
> with the cap effectively removed plateauing at a **third** value, 4 978 MB, *below* the degree-5
> group. **§9.4a re-measures that and gets 14 336 724 kB — the capped rung's figure to the
> kilobyte** — so the third value was a measurement error and the peak does not move with the cap
> at all, because it is reached before any matrix exists and no entry cap can touch it. What the
> peak does track is **which batch's symbolic preprocessing ran**, and the queue that stage builds
> is a function of the closure rather than of any budget here.

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

Where the untracked 98.7% goes was **not established here** and should not be guessed from this
measurement. The step's coincidence with a degree boundary points at degree-5 symbolic
preprocessing — and README's three named categories are the obvious candidates — but attributing it
needs a profile, not an inference from one correlation. That is #237's first task, and it is a
different piece of work from raising a cap.

> **Resolved in §9 (M25, #237).** It is degree-5 symbolic preprocessing, and specifically **one
> `VecDeque<Monomial<20>>`**: 88% of peak RSS is the pre-deduplication monomial queue. None of
> README's three named categories is the answer, and neither is the error path §6a suspected. The
> correlation with the degree boundary was real; the mechanism is not the one it suggested.

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

~~**The peak-RSS step is about the cap, not about the degree.**~~ This was offered as a correction
to §4. Both uncapped rungs plateau at **4 978 MB** — 4 977 776 kB and 4 977 796 kB, **20 kB
apart** — which is *below* the 14 072 MB that every capped degree-5 row reached. A run doing
strictly more work peaks at a third of the memory. So 14.07 GB is **not what degree 5 costs**; it is
reached on the path that ends in a refusal and not on the path that proceeds.

> **Withdrawn in §9.4a (M25, #237).** Re-measured on the same instance and cores, the uncapped and
> capped rungs both peak at **14 336 724 kB** — the same number, not merely a close one. The 4 978 MB above is a measurement error, and every inference drawn from it below,
> including the refusal-path reading, falls with it. The deduction was valid; the premise was not.
> §9.2 attributes the 14 GB to one `VecDeque<Monomial<20>>` in symbolic preprocessing, which is
> reached **before any matrix exists** and therefore before any budget can be crossed.

~~What produces the 14.07 GB on the refusal path specifically is **not established**, and the
candidates are now different from §5's: the limit check fires during a batch, and `f4_observed_reported`
retains a clone of the system for the report, so an allocation on the error path is as plausible as
one in degree-5 preprocessing. #237's profile should compare a capped run against an uncapped one at
the same point, which is a sharper experiment than profiling either alone.

**A run killed by the wall clock reports no matrix statistics at all** — "F4 has no cooperative time
check, so no matrix statistics exist for a run killed this way". So the group-B metrics M23 §4.3
defines were available only for runs that stop at a *resource* bound, and a time-bound run was
diagnostically poorer than an entry-bound one. ~~That is an argument for keeping the entry cap as
the primary budget even though it does not bound memory: it is the bound that yields a report.~~

> **Retracted in M25 by #284.** The argument rested on a missing feature, not on a property of
> either bound. `F4Options::max_wall_time` is now checked once per batch and *returns*
> `F4Error::TimeBudgetExceeded`, so a time-bound run carries the full group-B counters out with it —
> §9.1 is measured on exactly such a run. The entry cap keeps one real advantage over a wall clock,
> stated positively: an entry count is a property of the system and reproduces on any machine, while
> an elapsed time is a fact about one box under one load. That is why `F4Error::stop_kind`
> distinguishes `StopKind::Resource` from `StopKind::Time` and why the two must never be ranked
> against each other. It is not because one of them yields a report and the other does not.

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

## 9. The attribution (M25, #237)

§5 said where the untracked 98.7% goes was "not established here". This establishes it, by
measurement rather than by correlation, and the answer is one data structure.

### 9.1 The instrument

`examples/f4_memory.rs`. Two instruments at once, because neither alone would settle it:

| instrument | what it gives | what it cannot give |
|---|---|---|
| a tracking `#[global_allocator]` (LIVE/PEAK atomics) | the **peak live heap of a named stage**, exactly, temporaries included | which `Vec` the bytes went to |
| the solver's own counters x `size_of` | a **named structure's** payload share | the slack a `HashMap`'s capacity or a `Vec`'s doubling leaves |
| `/proc/<pid>/status` `VmHWM` | what the machine paid | which stage raised it |

The stages are measured **on the real batches**, not on a reimplemented main loop: a
`BatchObserver` receives each batch as F4 selected it and re-runs symbolic preprocessing and matrix
construction under the allocator before the library does them for real. That costs the stages twice
in wall time (99.1 s against the uninstrumented 71 s) and nothing in peak memory, since each copy
is dropped before the next allocation.

**The batch that matters is the batch that is refused**, and no `F4Statistics` field describes it:
`reduce_batch_in` returns `Err` with nothing to attach the refused batch's counters to. The probe
sees it because the observer is called *before* the batch is reduced. That is why the figures below
cannot be read off a scoreboard record, and why the campaign in §3 could not have produced them.

### 9.2 The 20 000 000-entry rung, attributed

`fukuoka-mq-III-n20-seed0`, grevlex, 200 000 columns, `max_live_bytes` set clear of the entry cap,
pinned to cores 0-7, release at `-C target-cpu=x86-64-v3`. Three batches completed; the fourth, at
**degree 5**, refused during construction. `Monomial<20>` is `[u32; 20]` = **80 B**; a matrix entry
is `(usize, Zp31)` = **16 B**.

| site | measured MB | share of `VmHWM` | method |
|---|---:|---:|---|
| **symbolic preprocessing's pending monomial queue** | **12 374** | **88.4%** | 162 188 194 monomials at the queue's high-water x 80 B |
| the basis, held twice | 905 | 6.5% | 5 389 241 terms x (80 + 8) B x 2 copies, and a **lower bound** — see below |
| **matrix entries — the budgeted quantity** | **186** | **1.3%** | `max_live_nonzeros` 12 212 087 x 16 B + 40 588 B of dense buffer |
| preprocessed row vector | 5.9 | 0.04% | 64 062 rows x `PreprocessedRow<20>` = 96 B |
| `examined` + `covered` monomial sets | 5.3 | 0.04% | 34 210 distinct monomials x 81 B x 2 sets |
| pair heap | 4.5 | 0.03% | 16 874 entries x `ScheduledPair<20>` = 280 B |
| pair criteria sets | 0.3 | 0.00% | 19 422 keys x 16 B |
| unnamed remainder | ~515 | 3.7% | allocator slack and completed batches' column structures |
| **measured `VmHWM`** | **13 996** | 100% | the example's own `util::peak_resident_bytes`, read after F4 returned |

The row names are the ones the harness printed at the stamp above. `examined` is a map rather than a
set since #621, so a run today prints it, the monomial arena and the per-term handles as three rows
in place of the one; the quantity is the same structure and the 0.04% is unaffected at this scale,
because a handle is four bytes against `Monomial<20>`'s eighty.

**Two readings of `VmHWM`, 4 MB apart, and which is which.** The shares above are against the
example's own in-process read, 13 996 MB, taken after F4 returns — that is the figure the
percentages divide by. The external poller, sampling `/proc/<pid>/status` every 200 ms while the run
was live, caught **14 336 724 kB = 14 000 MB**. The 0.03% difference is because `VmHWM` is not
reliably monotonic on this kernel (see the caveat on `util::peak_resident_bytes`), so a read after
the fact can come back slightly below a read taken at the peak. §9.4a uses the poller's figure
throughout, because comparing two runs needs one instrument.

Named sites account for **96%** of peak RSS. The two stage measurements bracket it: symbolic
preprocessing's peak live heap is **20 499 MB** and construction adds **317 MB** on top.

**Every `count x size_of` row is a payload lower bound, by construction.** It excludes the slack a
container's growth policy leaves, which is why the rows are reported beside an allocator measurement
rather than instead of one. The basis row is the clearest case: of its two copies,
`MonicBasis`'s is a `Vec<(Monomial<20>, Zp31)>` and costs exactly 88 B a term, while
`MultivariatePolynomial`'s is a `HashMap<Monomial<20>, Zp31>` and costs 88 B of payload plus one
control byte per slot in a power-of-two table — between 1.14x and 2.3x more. So 905 MB is a floor
and the true figure is 1.0-1.5 GB, which is where most of the unnamed remainder is.

**Why the allocator's 21 674 MB exceeds `VmHWM`'s 13 996 MB, and why that is the mechanism rather
than an inconsistency.** A `VecDeque` grows by doubling, so at 162 188 194 elements its capacity is
2^28 = 268 435 456 slots — `20 480 MiB` of 80-byte monomials in **one allocation**, which is
20 499 MB less the 11 MB of sets and rows, to within rounding. Only 60% of that capacity is ever
written, and `VmHWM` counts *touched pages*. So:

- the allocator figure is the queue's **capacity**: 20 480 MB;
- the resident figure is the queue's **payload**: 12 374 MB;
- and the ratio between them is exactly the doubling slack.

That is the whole explanation of the 14 GB, and it is a property of one `VecDeque`.

### 9.3 The same mechanism at the degree-4 rung

| | 10 000 000 cap | 20 000 000 cap |
|---|---:|---:|
| batches completed | 2 | 3 |
| degree refused at | 4 | 5 |
| basis at peak | 278 elements / 240 551 terms | 1 318 / 5 389 241 |
| rows in the refused closure | 10 297 | 64 062 |
| **queue high-water** | **6 196 886 monomials / 473 MB** | **162 188 194 / 12 374 MB** |
| symbolic preprocessing's peak live heap | 644 MB | 20 499 MB |
| matrix entries (budgeted) | 5.8 MB | 186 MB |
| `VmHWM`, in-process read | **608 MB** | **13 996 MB** |
| `VmHWM`, external poller | 609 MB (623 460 kB) | 14 000 MB (14 336 724 kB) |
| queue as a share of `VmHWM` | **78%** | **88%** |

608 MB here against §3's 617 MB from the scoreboard binary, which also holds the challenge data and
the record machinery — the same row. **The queue dominates at both rungs**, so this is not a
degree-5 phenomenon; it is what symbolic preprocessing costs at every degree, scaling with the
closure.

### 9.4 Two hypotheses the measurement kills

**The pair heap is not the problem.** It was the top-ranked suspect on size grounds — `O(B²)` pairs
at 280 B each, which at `B = 10 000` would be the whole gap. Measured: **4.5 MB, 0.03%**. The
estimate assumed a basis an order of magnitude larger than the one this instance actually reaches
(1 318 elements before interreduction).

**The refusal path is not the problem** — §6a's conclusion that "14.07 GB is reached on the refusal
path and not on the path that proceeds" is **withdrawn**. The peak occurs inside symbolic
preprocessing, *before any matrix exists* and therefore before any budget can be crossed; the
process is observed at 1.3 GB resident while still running, after the 14 GB mark has been set. §6a
named `f4_observed_reported`'s retained clone of the system as a suspect: that clone is 40
polynomials of 20 variables, a few tens of kilobytes, and it lives in the harness rather than in the
library.

§6a reached the refusal-path reading from a sound deduction over an unsound premise. The deduction:
the capped and uncapped runs are *identical* until the first budget crossing, so a peak the capped
run reaches before crossing must also be reached by the uncapped run — and if the uncapped run peaks
lower, the capped run's extra must come after the crossing. **That deduction is valid.** The premise
is §6a's 4 978 MB for the uncapped rungs, and that is the part that fails.

### 9.4a Capped against uncapped, at the same point

§6a asked for exactly this comparison and named it the sharpest available experiment. Run on the
same binary, the same instance and the same cores, differing only in the entry cap:

| | 20 000 000 cap | 1 000 000 000 cap (uncapped in effect) |
|---|---:|---:|
| outcome | `max_live_nonzeros` at degree 5, 99.1 s | no entry stop; abandoned inside the degree-5 batch at 326 s of CPU |
| **`VmHWM`, external poller** | **14 336 724 kB** | **14 336 724 kB** |

**Identical to the kilobyte.** Not "close": the same number, from two runs that differ in outcome,
in runtime by 3x, and in entry cap by 50x. The peak does not move with the cap at all, which is what
the mechanism predicts and what §6a's figures contradict: the only budget symbolic preprocessing
reads is `max_matrix_rows`, so the queue it builds at a given batch is byte-identical whatever the
entry cap is. The entry cap cannot change a peak that is reached before the matrix exists.

The agreement is exact because the peak is **one allocation** — a single `VecDeque` reserve of 2^28
monomial slots — rather than a sum of many, so there is nothing for run-to-run variation to move.
That is itself evidence for the mechanism: an aggregate of scattered allocations would not reproduce
to the kilobyte.

So **§6a's 4 978 MB is a measurement error, not a plateau**, and the "refusal path" conclusion that
rested on it goes with it. Two independent runs of very different length agreeing to 20 kB
(4 977 776 and 4 977 796 kB) is a signature of a poller that stopped early rather than of a physical
limit — see §2 for the earlier probe in this very document that was wrong by 7 000x. The lesson §2
drew applies to itself: cross-check an instrument before building an argument on a surprise.

The uncapped rung also reproduces §6a's *other* observation, the one that was never in doubt: it is
**time-bound, not entry-bound**. The degree-5 batch does not finish, and `max_wall_time` cannot
interrupt it, because a cooperative check between batches cannot stop a batch already in progress —
which is precisely the caveat `F4Options::max_wall_time` documents and the reason an external
supervisor remains the right backstop.

### 9.5 What this changes

- **`max_live_bytes` is not a process-memory limit and must not be read as one.** Its corrected doc
  comment now enumerates what it does bound — the `SparseRow` payload of one batch's matrix, at that
  batch's peak — and what no budget in F4 bounds. The name is kept: `max_entry_bytes` would describe
  the scope better, and renaming it would make every figure recorded against the old name ambiguous,
  which is the objection that made it a second budget rather than a redefinition of
  `max_live_nonzeros` in the first place.
- **An RSS backstop would belong in symbolic preprocessing, not beside the entry budget.** The peak
  is reached before a matrix exists, so a second limit checked where the entry budget is checked
  would be checked after the damage. The queue is the thing to bound, and #305 proposes bounding it
  directly, which is cheaper and reproducible where a resident-size limit is neither.
- **No default changed**, so every figure in §3, §4, §6 and §6a still reproduces.

### 9.6 Reproducing §9

```sh
tools/fetch-mq-challenge.sh
cargo build --release --example f4_memory

ZEEBRA_MAX_ENTRIES=20000000 taskset --cpu-list 0-7 \
  ./target/release/examples/f4_memory mq fukuoka-mq-III-n20-seed0
```

The example reads `VmHWM` itself, so the pid hazard of §2 does not arise; an external poller must
still read the binary's own pid. `ZEEBRA_WALL_SECONDS` sets `F4Options::max_wall_time`, a
**cooperative** per-batch budget rather than a supervisor, which is what makes an uncapped rung
measurable at all: it stops between batches and returns, so the statistics survive. Peak-RSS runs
do not need `tools/benchlock.sh`; the elapsed times quoted here are not results.

## 10. The queue bounded (M25, #305)

§9 attributed 88.4% of a 13 996 MB peak to one `VecDeque<Monomial<20>>`. This removes it. The
interesting part is not the size of the win, which was predictable from §9.2 once the mechanism was
known, but two things that were not: whether the algorithm survived, and **what the peak becomes
afterwards**, since removing 88% of it promotes something else to the top.

### 10.1 The change, and the argument that it is the same algorithm

Symbolic preprocessing pushed every term of every row onto the queue and tested `examined` only
when popping. It now tests on push. The same number of hash operations, one step earlier, and the
queue is then bounded by the **distinct** monomials of the closure — which are exactly the matrix's
columns, hence `max_matrix_columns`, hence a quantity a caller sets.

The risk, and the only real risk in the change, is that moving the test changes *when* a monomial is
marked examined relative to when its multiples are generated. A different symbolic closure would be
a different algorithm, and its statistics would not be comparable with anything recorded here.

**It is the same closure.** The induction is written at the push site in `src/grobner/f4/symbolic.rs`
and turns on two invariants: the push-time `examined` set is exactly (processed) u (queued), and the
push-time queue is the pop-time queue with the already-processed monomials and the duplicate
occurrences deleted. Both queues are FIFO, so the head of one is the first element of the other that
pop-time deduplication would not discard: the two process the same monomial next, run the same tests
on it, and append the same row.

The consequence worth stating is the one #305 expected to go the other way. #305 reasoned that
deduplicating on push "does change the queue's *order* if a monomial is enqueued twice before either
copy is popped, so the row order could move". **It does not.** Deduplicating on push keeps a
monomial at its *first* occurrence's position in the queue; deduplicating on pop also *processes* it
at its first occurrence's position, because the later copies are discarded. The two disciplines
agree on order, not merely on membership.

Three checks, in increasing strength:

- `test_push_time_deduplication_preserves_the_closure` compares the two disciplines on **every batch
  of the correctness corpus under all three orders**, and on katsura-5 and cyclic-5: rows element for
  element and in order, the covered set, the column set, and the work counters. The two memory
  counters are excluded, being what changed.
- The comparison is against `symbolic_preprocessing_pop_deduplicated`, a `#[cfg(test)]`
  reimplementation of the old discipline rather than a runtime flag, so the unbounded discipline
  cannot reach a caller. A `push_front` mutation of the live code fails it on batch 2 of the corpus
  and batch 0 of katsura-5, naming the row order — so the check has teeth on exactly the property
  at issue.
- On the instance itself, **every structural figure in §9.2 and §9.3 reproduces unchanged**: 3
  batches, a peak basis of 1 318 elements / 5 389 241 terms, a 16 874-entry pair heap, 64 062 rows in
  the refused degree-5 closure, 34 210 distinct monomials tested, 12 212 087 live matrix entries, and
  the refusal at 20 001 424 entries against the 20 000 000 limit. That is a twenty-variable instance
  agreeing to the unit on every number the closure determines, which no unit test could establish.

### 10.2 Before and after, at both rungs

`fukuoka-mq-III-n20-seed0`, grevlex, pinned to cores 0-7, release at `-C target-cpu=x86-64-v3`,
`examples/f4_memory`. The "before" column is §9.2 and §9.3 and was not re-measured.

| | 10 000 000 cap (degree 4) | | 20 000 000 cap (degree 5) | |
|---|---:|---:|---:|---:|
| | before | after | before | after |
| **queue high-water, monomials** | 6 196 886 | **9 369** | 162 188 194 | **40 929** |
| **queue payload** | 473 MB | **0.7 MB** | 12 374 MB | **3.1 MB** |
| symbolic preprocessing, peak live heap | 644 MB | **5.0 MB** | 20 499 MB | **24.4 MB** |
| matrix construction, added peak live heap | not recorded | 109.7 MB | 317 MB | 317.2 MB |
| matrix entries — the budgeted quantity | 5.8 MB | 5.8 MB | 186 MB | 186.4 MB |
| basis, held twice | 40.4 MB | 40.4 MB | 905 MB | 904.6 MB |
| **`VmHWM`, in-process read** | **608 MB** | **211.2 MB** | **13 996 MB** | **1 496.5 MB** |
| queue as a share of `VmHWM` | 78% | **0.33%** | 88.4% | **0.21%** |

The queue falls by **661x** at the degree-4 rung and **3 962x** at the degree-5 rung, and peak RSS
by **2.9x** and **9.4x**. The two reductions differ because the queue was a larger share of the
larger rung, which is §9.3's observation read forwards.

The queue's new size is what the closure's column count predicts and not an empirical surprise:
there are `C(25, 5) = 53 130` monomials of degree at most 5 in twenty variables, so 40 929 distinct
monomials is within a small factor of the arithmetic ceiling on this batch, and no instance of this
shape can push the queue past it. That is the difference between a structure bounded by a budget and
one bounded by nothing: the bound here is a property of the problem rather than of a setting.

The `VecDeque` doubling slack of §9.2 goes with the payload. At 40 929 elements the capacity is
`2^16 = 65 536` slots, 5.2 MB, so the allocator-against-resident gap that explained the 21 674 MB
against 13 996 MB is now a few megabytes and not worth separating.

**The benchmark systems, where the win is real and immaterial.** `examples/f4_memory` with no
arguments, same binaries:

| system | queue high-water before | after | factor | monomials offered | peak live heap before / after |
|---|---:|---:|---:|---:|---:|
| katsura-6 | 2 908 | **206** | 14.1x | 17 550 | 0.3 MB / 0.3 MB |
| katsura-7 | 16 334 | **693** | 23.6x | 92 669 | 1.2 MB / 1.2 MB |
| cyclic-6 | 5 684 | **293** | 19.4x | 62 216 | 0.7 MB / 0.7 MB |

The factor is larger here than one might guess from the MQ rungs and the peak does not move at all,
because at six and seven variables the whole computation fits in a megabyte and the queue was never
what bound it. The queue's cost scales with rows times terms per row, which is what makes it a
twenty-variable problem and not a general one. Reported because the issue asked for the benchmark
systems, and a figure that shows a change mattering nowhere is worth as much as one that shows it
mattering somewhere.

The column that matters for equivalence is **monomials offered**, which is byte-identical before and
after on all three — 17 550, 92 669, 62 216 — as are the batch counts, the stop lines and the peak
basis sizes. Only the high-water moved, which is the whole intent: `monomials_enqueued` still counts
offers rather than admissions precisely so that this comparison is possible.

### 10.3 The new binding site, and that it is not the same one at both rungs

Removing 88% of a peak promotes something else to the top, which is the whole reason to recompute
the attribution rather than report a ratio. The sites are priced exactly as in §9.2 — the solver's
own counters times `size_of`, every row a payload **lower bound** — so the two tables are
comparable row by row.

**The degree-5 rung, against the in-process `VmHWM` of 1 496.5 MB:**

| site | measured MB | share | was (§9.2) |
|---|---:|---:|---:|
| **the basis, held twice** | **904.6** | **60.4%** | 6.5% |
| matrix entries — the budgeted quantity | 186.4 | 12.5% | 1.3% |
| preprocessed row vector | 5.9 | 0.39% | 0.04% |
| `examined` + `covered` monomial sets | 5.3 | 0.35% | 0.04% |
| pair heap | 4.5 | 0.30% | 0.03% |
| **pending monomial queue** | **3.1** | **0.21%** | **88.4%** |
| pair criteria sets | 0.3 | 0.02% | 0.00% |
| unnamed remainder | ~386 | 25.8% | 3.7% |

**The basis, held twice, is the new peak**, and the figure understates it. §9.2 established that this
row is a floor by construction: of the two copies `MonicBasis`'s `Vec<(Monomial<20>, Zp31)>` costs
exactly 88 B a term while `MultivariatePolynomial`'s `HashMap` costs 88 B of payload plus a control
byte per slot in a power-of-two table, between 1.14x and 2.3x more, so the true figure is 1.0-1.5 GB.
Against a 1 496.5 MB peak that is between 60% and essentially all of it, and it is where most of the
unnamed remainder has to be. The remainder's *share* grew from 3.7% to 25.8% without growing in
bytes — 515 MB to 386 MB — because the denominator fell 9.4x. Named sites account for 74%.

Note that matrix construction's stage peak, 317.2 MB measured by the allocator, overlaps the 186.4 MB
entry row rather than adding to it: the difference is the column vector, the monomial-to-column map
and the temporaries construction builds them from, which §5 counted as four copies of the column
monomials with three live at once.

**The degree-4 rung is bound by something else.** Against its 211.2 MB `VmHWM`, matrix construction's
stage peak is **109.7 MB, 51.9%**, and the basis only 40.4 MB, 19.1%; the queue is 0.7 MB, 0.33%.

That difference is structural rather than noise, and it is the useful part of this subsection. **The
basis grows with the whole computation; a batch's matrix grows with that batch.** So which site binds
depends on how far the computation got before it stopped, and a single "what dominates F4's memory"
answer does not exist. At the degree-5 rung the computation has run long enough for 5 389 241 basis
terms to outweigh one batch's matrix; at the degree-4 rung it has not. Both are now in the hundreds of
megabytes rather than the tens of gigabytes, which is the change that makes the question interesting
again.

### 10.4 The stop reason does not change, and what that leaves

The instance still records `max_live_nonzeros` at degree 5 — 20 001 424 entries needed against the
20 000 000 limit — and the degree-4 rung still stops at 10 000 178 against 10 000 000. **No stop
reason moved, and no default changed**, so every figure in §3, §4, §6, §6a and §9 still reproduces
and the recorded scoreboard ladder is untouched. No scoreboard record was written for §10.

What *did* change is the character of the refusal. Before, the computation reached 14 GB of resident
memory inside symbolic preprocessing and then refused on a 186 MB matrix. The refusal was honest but
the resource it named was not the resource being consumed. Now the two agree: the run peaks at
1 496.5 MB and refuses on the quantity its budget is written in.

This bears on M24's negative result #3 — that `fukuoka-mq-III-n20-seed0` is "out of reach, not out of
budget". The verdict **stands**, and §9.4a's evidence for it is untouched: the uncapped rung is
time-bound, and a cooperative per-batch check cannot interrupt a batch already in progress. But the
*shape* of what remains has changed. The obstacle to the degree-5 batch was previously time **and** a
14 GB working set; it is now time alone, at a working set an order of magnitude smaller. Whether a
much longer budget and an external supervisor would finish that batch is a question this document
cannot answer and did not previously have any reason to ask.

### 10.5 Runtime, and it is faster rather than flat

Moving the deduplication does not change how many hash operations happen — every term is tested
exactly once either way — so the expectation was a flat runtime, and the honest reason to measure
was that an expectation is not a measurement. It is **7% to 10% faster**, and the expectation was
wrong for a reason worth recording: what the change removes is not hash work but 162 million
`push_back`/`pop_front` pairs and the first-touch page faults on 20 GB of `VecDeque` the allocator
reserved and never needed.

`examples/scoreboard`, two interleaved repetitions, both variants built from this one tree into
private target directories, pinned to cores 0-7, under `tools/benchlock.sh` so nothing else ran:

| rung | | rep 1 | rep 2 | mean | peak RSS, `/usr/bin/time -f %M` |
|---|---|---:|---:|---:|---:|
| 20 000 000, degree 5 | before | 69.57 s | 72.24 s | **70.9 s** | 14 407 956 / 14 407 396 kB |
| | after | 64.47 s | 63.05 s | **63.8 s** | 1 589 768 / 1 590 272 kB |
| | | | | **-10.0%** | **9.06x lower** |
| 10 000 000, degree 4 | before | 4.34 s | 4.35 s | **4.35 s** | 629 568 / 630 052 kB |
| | after | 4.04 s | 4.03 s | **4.04 s** | 225 040 / 223 664 kB |
| | | | | **-7.1%** | **2.80x lower** |

**The before column reproduces the recorded ladder, which is what makes the comparison a comparison
rather than two unrelated runs.** Its 20 000 000 rung gives a mean of **70.9 s** against §3's
quoted 70.9 s for the same rung, and a peak of 14 407 956 kB against §3's 14 406 056 kB — 0.013%
apart. Its degree-4 rung gives 629 568 kB against §3's 617 MB. A binary built from the commit
before the change therefore behaves as the recorded ladder did, so the after column's differences
are the change and not the five weeks between the two sets of figures.

The stop lines are byte-identical between the variants at both rungs, which is the equivalence check
of §10.1 reappearing in the timing harness: same resource, same entry count, same degree, same last
completed stage.

Two instrument notes. `/usr/bin/time -f %M` reports 14 407 956 kB for a run launched through
`timeout … taskset …`, so it is **not** subject to §2's pid hazard: `%M` comes from `wait4`'s
`rusage`, which propagates a child's high-water up the chain, where reading `/proc/<pid>/status` of
the `timeout` process does not. And these are `scoreboard` figures, uninstrumented, so they are
directly comparable with §3 and not with §9's `f4_memory` elapsed times — the latter run both
allocating stages twice per batch and §9.6 is explicit that they are not results.

### 10.6 Reproducing §10

```sh
tools/fetch-mq-challenge.sh
cargo build --release --example f4_memory

ZEEBRA_MAX_ENTRIES=20000000 taskset --cpu-list 0-7 \
  ./target/release/examples/f4_memory mq fukuoka-mq-III-n20-seed0     # the degree-5 rung
ZEEBRA_MAX_ENTRIES=10000000 taskset --cpu-list 0-7 \
  ./target/release/examples/f4_memory mq fukuoka-mq-III-n20-seed0     # the degree-4 rung
```

As in §9.6, the example reads `VmHWM` itself so the pid hazard of §2 does not arise, and the
peak-RSS runs do not need `tools/benchlock.sh`. §10.5's timings do, and were taken under it with
both variants built from one tree into private target directories — `tools/benchlock.sh`'s own
header lists the companion hazards that the lock does not cover and each of which has cost a re-run
here.

The before column of §10.2 is §9.2 and §9.3 and was deliberately **not** re-measured: #237's
attribution is the baseline, and re-deriving it would have produced a second set of numbers to
reconcile rather than a comparison. The after column's structural figures — batches, basis size,
rows in the refused closure, distinct monomials tested, live entries, the refusal threshold — are
what make that legitimate, because they are identical to §9.2's and §9.3's, which is only possible
if the two runs did the same work.

The closure-equivalence checks run in the ordinary test suite and need no instance data:

```sh
cargo nextest run -E 'test(push_time_deduplication) + test(the_monomial_queue)'
```

## 11. The re-diagnosis asked for in §10.4 (#453)

§10.4 closed by naming a question it had no reason to ask before #305:

> Whether a much longer budget and an external supervisor would finish that batch is a question
> this document cannot answer and did not previously have any reason to ask.

This section answers it, and the answer corrects a reading the recorded figures invite.

**Authorization and protocol.** `docs/MILESTONE-COMPETITIVE-MQ-SOLVING.md` §9 authorizes the III
n=20 re-diagnosis at **≤ 30 min wall and ≤ 32 GB peak RSS**, and authorizes **no completion
attempt**. Both caps were enforced externally and neither was approached. Machine and protocol as
§4: `taskset --cpu-list 0-7`, every run under `tools/benchlock.sh`, an external
`tools/rss-guard.sh` matching the measured binary by `/proc/<pid>/comm` and never by `pgrep -f`
(#328), launched under `setsid` so the run outlives its launcher (#344). The ISA floor was
**verified and not assumed** — `cargo build -v` shows `target-cpu=x86-64-v3`.

Taken at `96bf1969`, whose base is `b7847824` on `main`. The delta from that base is `CLAUDE.md`
and two files under `scripts/agent/` — **no Rust at all**, so it cannot affect a measurement, and
the recorded `patch_id` is what lets a later reader check that rather than take it on trust.

### 11.1 §10.3's attribution reproduces at current `main`

Same instrument, same two rungs, three milestones later:

| | §10.3 | here | agreement |
| --- | ---: | ---: | --- |
| degree-5 rung, process `VmHWM` | 1 496.5 MB | **1 495.5 MB** | 0.07% |
| the basis, held twice | 904.6 MB, 60.4% | **904.6 MB, 60.5%** | exact |
| matrix entries — the budgeted quantity | 186.4 MB, 12.5% | **186.4 MB, 12.4%** | exact |
| pending monomial queue | 3.1 MB, 0.21% | **3.1 MB** | exact |
| degree-4 rung, process `VmHWM` | 211.2 MB | **213.1 MB** | 0.9% |
| degree-4, matrix construction's stage peak | 109.7 MB, 51.9% | **109.7 MB** | exact |
| degree-4, the basis held twice | 40.4 MB, 19.1% | **40.4 MB** | exact |

The counter-derived rows are exact because they are counts times `size_of` and the counts did not
move; only the two allocator-measured peaks differ at all, and by under 1%. **§10.3 stands as
written**, and the site that binds at the degree-5 rung is still the basis held twice.

### 11.2 Doubling the entry budget buys nothing, and the recorded figure never bounded the demand

The authorized run raised `max_live_nonzeros` to 40 000 000 — past the 20 001 424 the record names
— with `max_live_bytes` already at 64 GB so that the raised knob genuinely binds (#322's trap does
not apply to this tier, and `BudgetReport` prints which of the two it is). Against the record it
replaces:

| budget | reported "needed" | **excess over its own budget** | degree | last completed stage | elapsed |
| ---: | ---: | ---: | ---: | --- | ---: |
| 10 000 000 | 10 000 178 | **178** | 4 | generation | 5.0 s |
| 20 000 000 | 20 001 424 | **1 424** | 5 | generation | 67.5 s |
| **40 000 000** | **40 003 287** | **3 287** | **5** | generation | **66.9 s** |

**The refusal tracks the budget.** Each run stops a few thousand entries past whatever limit it was
given, which means the number the record reports is **the budget plus one step, not the demand.**
Read on its own, `20 001 424 live nonzero entries were needed, over the limit of 20 000 000` invites
the inference that a 0.01% larger budget would clear it. Doubling the budget does not clear it.

And doubling it does not buy progress of any other kind either: same degree, same stage, same
resource, and **66.9 s against 67.5 s** — a 0.9% difference, which is noise on this instrument. The
twenty million additional entries were consumed inside the same operation with no measurable time
and no additional degree.

So the degree-5 batch's entry demand is **greater than 40 000 000 (> 640 MB of entries)** and these
measurements do not bound it above. That is a statement about what was measured, not an estimate.

### 11.3 What binds, and the branch this selects

#453 offered four branches. The measurement selects the second:

> **the entry budget again, now agreeing with the resource consumed** → the barrier is matrix size
> at degree 5.

Both halves hold. The budget binds — `max_live_nonzeros` is the named resource at every rung, and
`BudgetReport` confirms the byte budget has slack. And it now agrees with the resource consumed, as
§10.4 said: the run peaks at 1 495.5 MB and refuses on the quantity its budget is written in,
against the pre-#305 state where it reached 14 GB and refused on a 186 MB matrix.

What the re-diagnosis adds to §10.4 is that this is **not** a near miss. §10.4 established the
obstacle was "time alone, at a working set an order of magnitude smaller"; the first branch — time
alone, a costed single run to the owner — would have followed from that. It is wrong. The run does
not spend its budget getting further; it stops in the same place at twice the budget. **The barrier
is the size of the degree-5 matrix, and no authorized budget reaches it.**

### 11.4 The cost of a completion, and its dominant term is unmeasured by construction

| term | value | measured? |
| --- | ---: | --- |
| everything before the degree-5 batch | ~66 s | **measured**, and stable across both budgets |
| the degree-5 batch's entry demand | **> 40 000 000 entries, > 640 MB** | **a lower bound only** |
| peak RSS at the degree-5 refusal | 1 495.5 MB | measured |
| of which the basis, held twice | 904.6 MB, 60.5% | measured (a floor — §10.3's 1.0–1.5 GB) |
| the degree-5 batch's wall clock | **unknown** | **not measured, and not bounded** |

**The dominant term is the one that is unmeasured**, and this is the #410 situation stated in
advance rather than discovered later: a guard that models only the terms it can price authorizes
runs whose cost is in the term it cannot. No completion is costed here, and none should be
authorized on this section — §9's prohibition stands and this measurement strengthens rather than
weakens it.

Two things would make the dominant term measurable, and neither is this issue: a budget ladder that
locates the degree-5 entry demand rather than bounding it below, and the representation question
M27-A owns — at 60.5% of peak, the basis held twice is what makes a larger matrix unaffordable in
memory even where it is affordable in time.

**Magma V2.19-9 solved this instance in 259.27 s** on a 1 TB machine in 2015
(`fukuoka-mq.md:644`). That licenses **no ratio** — `classical-benchmarks.md:160` forbids a
wall-clock comparison against a figure of that age, and Magma is not installed here. What it
establishes is that the target exists: this instance is solvable by an F4 on one machine. It is not
a budget for this machine, and §9 says so explicitly.

### 11.5 Reproducing §11

```sh
tools/fetch-mq-challenge.sh && tools/fetch-mq-challenge.sh --verify

# §11.1, the attribution at both rungs. f4_memory reads VmHWM itself, so no pid hazard.
export CARGO_TARGET_DIR="$PWD/target-rediagnosis" RUSTC_WRAPPER=""
cargo build --release --example f4_memory --example scoreboard
cargo build -v --release --example f4_memory | grep target-cpu   # must show x86-64-v3
for rung in 20000000 10000000; do
  ZEEBRA_MAX_ENTRIES=$rung ZEEBRA_WALL_SECONDS=1800 taskset --cpu-list 0-7 \
    ./target-rediagnosis/release/examples/f4_memory mq fukuoka-mq-III-n20-seed0
done

# §11.2's third row, the authorized run: one instance, --write, never --all, externally guarded.
tools/rss-guard.sh f4_memory fukuoka-mq-III-n20-seed0 $((32 * 1024 * 1024)) --poll 10 --wait 2400 &
ZEEBRA_MACHINE=fedora ZEEBRA_AFFINITY=0-7 ZEEBRA_WALL_SECONDS=1620 ZEEBRA_MAX_ENTRIES=40000000 \
  tools/benchlock.sh zb-453 timeout --signal=INT --kill-after=60s 1800 taskset --cpu-list 0-7 \
  ./target-rediagnosis/release/examples/scoreboard mq fukuoka-mq-III-n20-seed0 --write
```

`end=exited` in `$HOME/.zeebra/benchlock.log` is what asserts the run completed; `status=0` does not
(#344). The guard's exit 0 means the ceiling was never crossed, and **exit 1 means nothing was
guarded and is not a pass**. Two traps cost time here and are worth stating: `rss-guard`'s
`--wait` defaults to **60 s**, which a run queued behind another agent's lock will exceed, leaving
it unguarded; and one guard cannot span several rungs, because it returns 0 at its first non-match
and would report a clean run for the gap between them.
---

## 12. The final interreduction's working set (M27, #536)

§9 and §10 attribute the **batch loop's** memory. This attributes the stage that runs after it, and
it exists because [#507](https://github.com/mfaulk/zeebra/issues/507) found a configuration that
takes `katsura-11` from **533.0 MB to 13 144.3 MB with every budget satisfied** — the matrix
interreduction route — and could not say where the bytes were.

### 12.1 What was unbudgeted, and why the shape could not show it

`F4Options::max_live_nonzeros` documents itself as bounding the entries live at once "in
construction and in elimination". The matrix interreduction route honoured the first half only: it
passed `live_entry_allowance::<F>()` to `MacaulayMatrix::build_within` and then called the
**unbounded** `reduced_row_echelon`. The batch loop has never had that gap — `reduce_batch_in`
passes the same allowance into `eliminate`, which checks it after every row operation — and #477
added `reduced_row_echelon_within` for the batch path while naming this stage in its own doc comment
as the one still "budgeting at matrix *construction* instead, which bounds what is built rather than
what elimination then makes of it". This is that sentence closed.

So the budgeted quantity was the matrix as *built*, and the quantity that binds is the matrix as
*reduced*. The two are not close, and nothing about the shape says how far apart they are:
back-substitution clears every pivot column out of every row holding one, not only out of the rows
below it, so the live entry count during that pass is a function of the fill-in.

### 12.2 The instrument

`examples/interreduce_working_set.rs`, **one rung and one arm per process**, because peak resident
size is a per-process reading and two arms in one process would report the larger of them twice.
Three instruments, as in §9.1:

| instrument | what it gives |
|---|---|
| `EliminationStatistics::peak_nonzeros`, carried out through `MatrixInterreduction` | the **payload** high-water: the entries the mathematics needs, which is the unit the budget is stated in |
| `EntryBufferPeak::capacity` (#536) | what the **allocator** holds: the total `Vec` capacity of the rows' entry buffers, plus the merge scratch's |
| `util::peak_resident_bytes` (`VmHWM`), cross-checked against `/usr/bin/time -v` | what the machine paid |

The second is the one this section turned on, and it is a counter rather than an inference:
`SparseRow::subtract_scaled` reserves `self.len() + other.len()` and **swaps the buffer in**, so a
row whose entries cancelled down keeps the capacity the merge might have needed, and nothing shrinks
it. Counting it costs one `Vec::capacity()` per row operation.

The arms are `--arm unbounded` (both halves of the coupled live-entry pair lifted, so the pass runs
to completion and reports its own high-water), `--arm default` (the shipped allowance), and
`--arm division` (the comparand).

### 12.3 `katsura-11` attributed

grevlex, GF(2147483647), pinned to cores 0-7, release at `-C target-cpu=x86-64-v3`, under
`tools/benchlock.sh`. One 104 403 x 105 427 interreduction matrix over a 537-element basis. An entry
is `(usize, Zp2147483647)` = **16 B**.

| site | measured MB | share of `VmHWM` | method |
|---|---:|---:|---|
| **elimination's row buffers — capacity** | **18 126.4** | **137.9%** | 1 187 934 712 entries x 16 B, counted at the high-water; exceeds `VmHWM` because capacity is reserved and `VmHWM` counts touched pages |
| of which payload — *the quantity now budgeted* | 1 584.9 | 12.06% | 103 865 277 live entries x 16 B |
| the matrix as built — **the quantity budgeted before** | 172.6 | 1.31% | 11 311 802 entries x 16 B |
| the batch loop's own high-water, over 11 batches | 260.9 | 1.98% | 17 099 200 entries x 16 B — **inside the 20 000 000 allowance**, which is why #507 found every budget satisfied |
| the column vector and the monomial-to-column map | 8.8 | 0.07% | 105 427 monomials x `Monomial<11>` = 44 B, twice; a payload figure, excluding the map's table slack |
| the preprocessed row vector, held twice | 14.3 | 0.11% | 104 403 rows x `PreprocessedRow<11>` = 72 B, twice (`Preprocessed` and `MacaulayMatrix` each hold one) |
| **measured `VmHWM`** | **13 144.3** | 100% | the example's own in-process read; `/usr/bin/time -v` reports 13 459 732 kB on the same run, the same figure |

**The answer is one allocation, and it is not the one #536 suspected.** The issue named the closure
"built as polynomials before it becomes rows". It is not: `interreduction_rows` stores a row as a
`(multiplier, basis_index, kind)` triple — `PreprocessedRow<11>` is 72 bytes — and both copies of
the whole row vector come to fourteen megabytes. The memory is in the `SparseRow` entry buffers *during* back-substitution,
and the single named site accounts for the entire peak with 1.38x to spare.

**Two numbers, 11.44x apart, and which is which.** The payload is 1 584.9 MB and the capacity is
18 126.4 MB. The ratio is not allocator policy — a `Vec`'s doubling would give at most 2x — it is
`subtract_scaled`'s reserve-and-swap: every row the pass touches acquires a buffer sized for the
worst-case merge and keeps it after cancellation shortens the row. **At most 72.5%** of that
capacity is ever written, which is the 13 144.3 MB against 18 126.4 MB — at most, because the
resident figure also covers the basis, the columns, and everything else the process holds.

All "MB" in this section are the 1024-based megabytes `util::peak_resident_bytes` and the example
print, which is also what `kB` means in `/proc` and in `rusage`: 13 459 732 / 1024 = 13 144.3, so
the two instruments agree exactly rather than approximately.

### 12.4 The amplification grows with the rung, so one rung does not locate it

| rung | matrix | built | elimination payload | x built | buffer capacity | x payload | `VmHWM` by matrix | by division | x |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|
| `katsura-9` | 7 977 x 8 233 | 413 640 | 1 966 015 | 4.75x | 12 157 282 | 6.18x | 164.5 MB | 24.3 MB | 6.77x |
| `katsura-10` | 26 839 x 27 351 | 2 113 826 | 13 260 077 | 6.27x | 102 979 071 | 7.77x | 1 217.6 MB | 101.5 MB | 11.99x |
| **`katsura-11`** | **104 403 x 105 427** | **11 311 802** | **103 865 277** | **9.18x** | **1 187 934 712** | **11.44x** | **13 144.3 MB** | **533.0 MB** | **24.66x** |

Both ratios rise monotonically, which is why a size threshold on the matrix shape would not have
worked: rows grow **3.4x** and then **3.9x** a rung while the elimination payload grows **6.7x** and
then **7.8x**, so a threshold calibrated on one rung's shape is wrong by about 2x at the next.

`katsura-9` and `katsura-10` are **inside** the default allowance at 1.97 M and 13.26 M live entries
and are admitted, as they should be — `katsura-10`'s 1 217.6 MB against the division route's
101.5 MB is a real 11.99x, and it is the amplification of §12.3 rather than a budget failure.
Removing it is [#554](https://github.com/mfaulk/zeebra/issues/554), not this issue.

### 12.5 The budget, and what the refusal costs

The allowance now covers the elimination, which is what `max_live_nonzeros` already said it did.
`katsura-11`'s pass is refused at **20 000 020** live entries — the overshoot is bounded by one row —
and falls back, recording `MatrixRefusal::LiveEntries`:

| arm | wall | interreduction stage | `VmHWM` | verdict |
|---|---:|---:|---:|---|
| division (the default) | 281 453.9 ms | 227 501.9 ms | **533.0 MB** | — |
| matrix, allowance lifted | 110 695.7 ms | 55 762.2 ms | **13 144.3 MB** | the pass ran |
| **matrix, default allowance** | 284 226.2 ms | 230 855.6 ms | **1 083.7 MB** | **refused at 20 000 020 live entries, fell back** |

So the pass that could reach 13.1 GB now costs **1 083.7 MB**, a **12.13x** reduction, and the
remaining 550.7 MB over the division route's own peak is the attempt: the 104 403 x 105 427 matrix
plus elimination filled to the 20 000 000-entry ceiling, which is 305.2 MB of payload by
construction. That is the sense in which the cost is now visible to a limit — it is proportional to
the allowance a caller set, not to what the instance happens to want.

**The fallback record now says what it refused.** A refusal on the elimination happens after the
matrix exists, so `MatrixInterreduction` carries its shape instead of zeros; before this it carried
`..Default::default()` on every refusal path, which made `fell_back` rows say only that something
had happened.

**What this does not claim.** That `katsura-11` is unreachable by the matrix route — it is reachable,
at a deliberately raised allowance (`F4Options::with_live_budget`), which is the whole point of
putting it behind a number. And not that 13.1 GB is a defect in the route: it is the route's honest
cost at that rung, and §12.4 says it is dominated by a buffer-reuse policy rather than by the linear
algebra.

### 12.6 What this unblocks

#507's default flip was gated on this and the gate is now removable **as a gate**: the matrix
route's working set is a budgeted quantity, a rung that exceeds it falls back rather than growing,
and the fallback is recorded with the shape that caused it. Whether the default should move is still
#507's measurement to make, and §12.5's table is a reason to take it carefully — at the default
allowance `katsura-11` by matrix is the division route's timing under another name, so a cohort
re-taken after this change must read `fell_back` before quoting a row. That decision is not made
here.

### 12.7 Reproducing §12

```sh
export CARGO_TARGET_DIR=/path/outside/the/worktree RUSTC_WRAPPER=""
unset RUSTFLAGS
cargo build --release --example interreduce_working_set

# One arm per process. katsura-11 is 111-114 s by matrix and 274-281 s by division.
for arm in unbounded division default; do
  tools/benchlock.sh <tag> taskset --cpu-list 0-7 \
    ./target/release/examples/interreduce_working_set katsura-11 --arm "$arm"
done

# The ladder of §12.4, which is cheap.
for rung in katsura-9 katsura-10; do
  taskset --cpu-list 0-7 ./target/release/examples/interreduce_working_set "$rung" --arm unbounded
done
```

Every figure in §§12.3-12.5 is from **one** locked run, in twelve minutes: two rungs x two arms plus
`katsura-11` x three arms. The binary was built at the commit this section's code lands in; the
commits after it change a doc comment and this section only, so the measured code is that
commit's.

**Three campaigns, and what moved between them.** The campaign was run three times during this
work, at different ambient loads. Every *counter* is identical to the unit across all three —
11 311 802 built, 103 865 277 live, 1 187 934 712 allocated, 20 000 020 at the refusal, and the same
104 403 x 105 427 shape — which is what makes the attribution a measurement rather than a sample.
`VmHWM` moved by **under 0.05%** (13 142.5 / 13 144.3 / 13 148.0 MB) and the wall times by up to
**7%**, which is this machine's spread with a dozen agents on it and is why the memory ratio is the
figure this section rests on and the wall times are reported but not compared.

The example reads `VmHWM` itself, so §2's pid hazard does not arise; the `/usr/bin/time -v`
cross-check in §12.3 was taken through `taskset` and agrees, because `%M` comes from `wait4`'s
`rusage` rather than from `/proc/<pid>/status` of the wrapper.

The budget's behaviour is checked in the ordinary test suite, on figures each test measures for
itself rather than on constants:

```sh
cargo nextest run -E 'test(the_allowance_covers_the_elimination) \
  + test(the_entry_capacity_is_counted) \
  + test(tracking_the_buffers_changes_nothing_else) \
  + test(falls_back_on_its_elimination_working_set)'
```

The budget on the second pass itself is #477's
`test_the_budget_covers_the_back_substitution_pass`, which this section relies on and does not
duplicate.

## 13. The amplification removed (M27, #554)

§12 attributed `katsura-11`'s 13.1 GB to one allocation and then budgeted the *payload*, leaving the
amplification between the two for this section. The amplification is gone: the elimination's row
buffers hold **1.81x** their payload where they held **11.44x**, and `katsura-11` by matrix peaks at
**2 759.5 MB** where it peaked at **13 145.9 MB** — the same row operations, the same reduced basis,
and the interreduction stage **2.1% faster** rather than slower.

The last clause is the part that was not expected. #554 was filed asking for both axes because a
policy that reallocates to save memory need not be a win, and it turned out there is no trade to
make: the copy this change adds replaces an allocation it was already paying, so copy-back is ahead
on memory **and** on time on all four rungs. The policies that *do* trade time for memory were
measured too, and both cost more than they save (§13.4).

### 13.1 The mechanism was not the reserve

§12 named the reserve: `subtract_scaled` reserves `self.len() + other.len()` and installs that buffer
in the row, "so a row whose entries cancelled down keeps the capacity the merge might have needed".
That is true and it is not sufficient, because it bounds a row's capacity by its own merge, and a
row's own merge cannot be more than twice its own length when the result is short — the result has
at least `other.len() - self.len()` entries, so a *short* result requires `self.len()` to be the
larger of the two. Reserve-and-keep alone therefore cannot exceed 2x, and the measured figure is
11.44x.

What produces 11.44x is the **swap**, and specifically what the swap does to the caller's scratch:

```rust
scratch.clear();
scratch.reserve(self.entries.len() + other.entries.len());
// ... merge ...
std::mem::swap(&mut self.entries, scratch);   // the row gets the scratch's buffer, whatever its size
```

After the swap the scratch holds the row's *old* buffer, so the next merge reserves again, and the
scratch's high-water capacity is handed to whichever row is merged next **however short that merge
is**. One long merge early in a pass therefore sizes every later row's buffer, and back-substitution
is exactly the pass that supplies one: it clears each pivot column out of every row holding it, with
pivot rows that span the columns to their right.

The unit test is the shortest statement of it — `test_a_short_merge_does_not_inherit_a_long_merges_buffer`
does one 512-against-512 merge and then one two-against-two merge, and before this change the
two-entry row came out holding capacity for 512. That is the 11.44x in nine lines, and no
cancellation is needed to produce it.

### 13.2 The four policies

All four were built from one tree as four binaries, differing only in the lines after the merge
loop, and every one of them produces bit-identical rows (§13.5).

| policy | after the merge | what it costs |
|---|---|---|
| **swap** (before) | `mem::swap(&mut self.entries, scratch)` | no copy; the scratch's capacity migrates into the row and the scratch must regrow |
| **copy-back** (shipped) | `self.entries.clear(); self.entries.extend_from_slice(scratch)` | one sequential `memcpy` of the merged length; saves the regrow, and the scratch becomes one buffer reused |
| **swap + shrink** | the swap, then `shrink_to_fit()` when `capacity > 2 * len` | a reallocation on most row operations |
| **copy-back + shrink** | copy-back, then the same shrink | the `memcpy` plus a reallocation when the row is over-sized |

`copy-back` is the issue's second option ("copying the merge result back into the row's own buffer").
The two shrink policies are its first ("`shrink_to_fit` when `capacity > k * len`"), applied on top of
each installation policy so that the shrink and the installation are separable in the table.

### 13.3 Both axes, on four rungs

grevlex, GF(2147483647), pinned to cores 0-7, release at `-C target-cpu=x86-64-v3`, one rung and
one arm per process under `tools/benchlock.sh`, with `--arm unbounded` so the elimination runs to
completion and reports its own high-water. An entry is 16 B. **Policies interleaved within a round**
and the mean of `n` rounds reported, each round's load bracket under 6 at both ends — see §13.6 for
why one run per arm was not enough.

`buffer capacity` is `EntryBufferPeak::capacity`, the total `Vec` capacity of the rows' entry
buffers plus the merge scratch at the high-water; `x payload` is that against
`EliminationStatistics::peak_nonzeros`, which is **identical across all four policies on every
rung** and is the sense in which these are the same elimination.

| rung | payload | policy | `n` | interreduction stage | total wall | buffer capacity | x payload | `VmHWM` |
|---|---:|---|---:|---:|---:|---:|---:|---:|
| `katsura-9` | 30.0 MB | swap (before) | 3 | 450.2 ms | 1 085.1 ms | 185.5 MB | 6.18x | 164.3 MB |
| 7 977 x 8 233 | | **copy-back** | 3 | **420.5 ms** | **1 061.5 ms** | **53.5 MB** | **1.78x** | **72.3 MB** |
| | | copy-back + shrink | 3 | 440.6 ms | 1 080.2 ms | 44.3 MB | 1.48x | 66.0 MB |
| | | swap + shrink | 1 | 499.8 ms | 1 137.1 ms | 34.0 MB | 1.13x | 91.9 MB |
| `katsura-10` | 202.3 MB | swap (before) | 5 | 4 407.9 ms | 9 631.4 ms | 1 571.3 MB | 7.77x | 1 217.9 MB |
| 26 839 x 27 351 | | **copy-back** | 5 | **4 276.5 ms** | **9 411.3 ms** | **363.1 MB** | **1.79x** | **400.1 MB** |
| | | copy-back + shrink | 5 | 4 453.0 ms | 9 682.4 ms | 309.0 MB | 1.53x | 376.6 MB |
| | | swap + shrink | 1 | 5 470.9 ms | 10 651.3 ms | 225.8 MB | 1.12x | 597.4 MB |
| `mq-random-10` | 37.4 MB | swap (before) | 3 | 2 248.1 ms | 7 912.0 ms | 678.8 MB | **18.13x** | 598.8 MB |
| 7 642 x 7 996 | | **copy-back** | 3 | **2 204.3 ms** | **7 688.0 ms** | **72.3 MB** | **1.93x** | **160.0 MB** |
| | | copy-back + shrink | 3 | 2 414.4 ms | 7 995.5 ms | 53.9 MB | 1.44x | 160.4 MB |
| | | swap + shrink | 1 | 2 381.7 ms | 8 007.9 ms | 44.3 MB | 1.18x | 218.9 MB |
| **`katsura-11`** | **1 584.9 MB** | swap (before) | 2 | 51 357.4 ms | 102 674.9 ms | **18 126.4 MB** | **11.44x** | **13 145.9 MB** |
| 104 403 x 105 427 | | **copy-back** | 3 | **50 286.7 ms** | **101 065.3 ms** | **2 865.1 MB** | **1.81x** | **2 759.5 MB** |
| | | copy-back + shrink | 3 | 53 534.0 ms | 104 965.8 ms | 2 494.4 MB | 1.57x | 2 634.6 MB |
| | | swap + shrink | 1 | 85 601.0 ms | 136 901.7 ms | 1 743.4 MB | 1.10x | 4 506.5 MB |

The `swap` row on `katsura-11` reproduces §12 to **0.01%** on `VmHWM` (13 145.9 MB against
13 144.3 MB) and to the entry on every counter, which is what makes this a before-and-after of the
policy rather than of the machine.

### 13.4 The verdict

**Copy-back ships, and the trade-off the issue expected does not exist.** The brief for #554 was to
report both axes because "a merge that reallocates every step to save memory is not obviously a
win". For copy-back there is nothing to trade: it is **faster on the interreduction stage on every
rung** and it holds **2.27x to 4.76x less resident memory**.

| rung | `VmHWM` reduction | interreduction stage | ranges disjoint? |
|---|---:|---:|---|
| `katsura-9` | **2.27x** | **-6.6%** | 407-440 against 439-462, touching |
| `katsura-10` | **3.04x** | **-3.0%** | 4 236-4 311 against 4 371-4 458, **yes** |
| `mq-random-10` | **3.74x** | **-1.9%** | 2 170-2 253 against 2 159-2 312, no |
| **`katsura-11`** | **4.76x** | **-2.1%** | 50 061-50 465 against 51 310-51 405, **yes** |

The copy is not free; it is *cheaper than what it replaces*. The merged length is copied once,
sequentially, into a buffer the row already owns — and in exchange the scratch stops being handed
away, so it grows once per pass instead of being re-grown at nearly every row operation. One
`memcpy` against one `malloc` plus the `memcpy` the allocator's growth path performs anyway is not a
close contest, and the measured direction is the same on all four rungs.

**The shrink policies are the ones with a real trade-off, and neither is worth taking.**

- **copy-back + shrink** buys a further **0% to 5.9%** of peak RSS (160.4 against 160.0 MB on
  `mq-random-10`; 2 634.6 against 2 759.5 MB on `katsura-11`) for **3.9% to 9.5%** more
  interreduction time. A genuine trade, and a poor one at that exchange rate: the amplification
  copy-back leaves is already down to 1.78-1.93x, which is `Vec`'s own doubling against each row's
  high-water length, and buying the last fraction of it back costs more than it saves.
- **swap + shrink** is **dominated on both axes**, which is the result worth keeping. It reaches the
  *lowest* buffer capacity of the four — 1.10x the payload on `katsura-11`, almost exactly the
  payload — and the *highest* `VmHWM` of the three fixes, 4 506.5 MB against copy-back's 2 759.5 MB,
  while costing **66.7%** more interreduction time. Both halves follow from the same thing: the
  swap still hands the scratch away, so the shrink is returning to the allocator a buffer the next
  merge immediately re-requests, and `VmHWM` counts pages touched rather than capacity held, so
  churning address space does not lower it. **A capacity counter is not a memory measurement** — this
  row is the proof, and it is why §13.3 reports `VmHWM` beside the counter rather than the counter
  alone.

### 13.4a What this costs at the shipped allowance

The default does not lift the live-entry allowance, so `katsura-11` by matrix is still **refused at
20 000 020 live entries** — the same threshold, since the payload counters do not move — and still
falls back to division. What changes is what the attempt costs before it is refused:

| policy | wall | interreduction stage | `VmHWM` | verdict |
|---|---:|---:|---:|---|
| swap (before) | 247 996.9 ms | 196 135.4 ms | **1 084.8 MB** | refused at 20 000 020, fell back |
| **copy-back** | 232 304.6 ms | 181 667.7 ms | **691.0 MB** | refused at 20 000 020, fell back |

So the refused attempt costs **1.57x less** resident memory, and §12.5's "remaining 550.7 MB over the
division route's own peak is the attempt" becomes about 158 MB over it. The division route's own
peak (533.0 MB, §12.4) is untouched by this change: it runs no matrices.

### 13.4b What this does not claim

- **Not that the amplification is zero.** It is 1.78-1.93x, and that is each row's own `Vec` growth
  history: a buffer that doubled and then cancelled down is still resident at its doubled size.
  Removing *that* is the shrink policies, which were measured and cost more than they save.
- **Not that the matrix route should now be the default.** That is still #507's measurement. §13 moves
  the route's memory cost down by 2.3-4.8x and its wall clock slightly down; whether that is enough
  to flip the default is a cohort comparison this section does not run, and §12.6's warning stands —
  a cohort re-taken after this change must read `fell_back` before quoting a row.
- **Not that any other elimination was measured.** `subtract_scaled` is the inner loop of every
  sparse elimination in the crate, and the four rungs here exercise it through F4's final
  interreduction only. The batch loop uses the same merge and should benefit in the same direction;
  that is unmeasured here, and §§9-11's attribution says the batch loop's peak is dominated by
  symbolic preprocessing rather than by row buffers, so the benefit there is not expected to be
  visible in `VmHWM`.

### 13.5 That the rows did not move

Three independent checks, because a wrong merge here is a silently wrong Gröbner basis rather than a
crash:

1. **A differential test against a dense reference.**
   `test_subtract_scaled_matches_a_dense_reference` runs 360 `(row, row, factor)` cases over five
   fields — GF(2), GF(13), GF(32003), GF(2147483647) and a 64-bit prime — against a reference that
   widens both rows, subtracts at an index, and narrows the result, so it shares only the field
   arithmetic and none of the merge's two-pointer logic, cancellation test, or buffer policy. The
   cases are the ones that decide how much of the reservation is written: disjoint supports, identical
   supports, an exact multiple that cancels to zero, a leading-column cancellation that moves the
   leading column right, the zero row on either side and on both, random overlaps, and containment in
   both directions. Field arithmetic is exact, so agreement is bit-identity.
2. **The counters, across all four policies.** Every row in §13.3 reports the *same* elimination
   payload, the same `peak_nonzeros`, the same matrix shape, and the same basis size as the baseline
   on its rung. The number of row operations and the order they happen in are properties of the
   algorithm, and a buffer policy that changed either would show up here.
3. **#536's identity assertions, unchanged.** `test_the_matrix_route_reproduces_the_division_route`
   and `test_the_allowance_covers_the_elimination_and_not_only_the_construction` are green, so the
   interreduced basis and the refusal threshold are where #536 left them.



### 13.6 Reproducing §13

The four policies are four binaries from one tree, differing only in the lines after the merge loop
in `SparseRow::subtract_scaled`. `copy-back` is what `main` ships; the other three are reached by
substituting the body from §13.2's table.

```sh
export CARGO_TARGET_DIR=/path/outside/the/worktree RUSTC_WRAPPER=""
unset RUSTFLAGS
cargo build --release -j24 --example interreduce_working_set   # -j24: see the note below

# One rung and one arm per process, because VmHWM is a per-process reading.
for rung in katsura-9 katsura-10 mq-random-10 katsura-11; do
  tools/benchlock.sh <tag> taskset --cpu-list 0-7 \
    ./target/release/examples/interreduce_working_set "$rung" --arm unbounded
done

# The shipped allowance on the top rung, where the pass is refused and falls back.
tools/benchlock.sh <tag> taskset --cpu-list 0-7 \
  ./target/release/examples/interreduce_working_set katsura-11 --arm default
```

`mq-random-10` is new to this example in #554, built through `grobner::external::instance` at
`REFERENCE_CHARACTERISTIC` under grevlex with its identity digest asserted, exactly as
`examples/f4_profile.rs` builds it. katsura is one family with an unusually tall interreduction
matrix and unusually heavy fill-in, and a buffer policy weighed on it alone would be weighed on one
shape; `mq-random-10` is the corpus family closest to a cryptanalytic system and it is where the
amplification was *worst* (18.13x against katsura-11's 11.44x).

**Three campaigns, and why only the third is published — plus what the first two got wrong.** The
method here was arrived at by two failures, and both are worth recording because the lock does not
prevent either.

1. **The load the lock does not serialize.** The first campaign ran inside one lock acquisition
   while six agents shared this box, and the one-minute load average rose from 64 to **687** on 128
   cores — driven by concurrent release builds, which `tools/benchlock.sh` deliberately does not
   serialize. Its counters agree with the third to the entry and its `VmHWM` figures to within
   **0.3%**, so the memory story was never in doubt; its wall times were wrong by up to **10%** and
   in the wrong *direction* — they made copy-back look 4.6% faster than it is on `katsura-10` and
   13% slower on the rung where a build storm landed mid-run. None of its wall times are reported.
2. **The reading a caller gated on is stale by the time it holds the lock.** The second campaign
   read the load before queueing, waited 1 143 s for the lock, and acquired it at 18.77. So the gate
   has to be read **inside** the lock, after the queue wait — and again before every individual run,
   and again at the end, because a 105-second run can start under the ceiling and be contaminated
   before it finishes. That is exactly what happened to `copyback katsura-11`, whose first clean-start
   run ended at load 52.65 and came back 13% slow; it was discarded and re-run.
3. **One run per arm cannot resolve a few percent.** `katsura-10`'s single copy-back run landed
   **9% above its own five-run mean** while inside the ceiling at both ends. The published walls are
   therefore interleaved means — the policies cycled within a round so that a slow patch of the
   machine hits every arm rather than whichever one was running — over five rounds on `katsura-10`
   and three on the rest, every round's bracket under 6. Within that protocol the spread is **1.3%
   to 2.0%** peak-to-peak, which is what makes a 2-3% difference reportable at all.

Every published row's load bracket is under 6 at both ends, and the aggregation drops any run whose
bracket exceeded it rather than averaging it in. A build on a machine this contended should be
capped — `-j24` — for the same reason: an uncapped `cargo build --release` here is itself one of the
storms that invalidated campaign one.

**Re-validated at the merge target.** §13.3's binaries were built at `e20d79da`; `main` then gained
[#330](https://github.com/mfaulk/zeebra/issues/330), which releases the interned monomial set as soon
as the columns are built — a memory change on a measured path. §12.3 bounds that term at **0.07%** of
`katsura-11`'s peak, and that bound was checked rather than assumed: both arms were rebuilt at the
rebased tree and re-run interleaved.

| rung | arm | `VmHWM` at `e20d79da` | at the merge target | x payload, both |
|---|---|---:|---:|---:|
| `katsura-10` | swap | 1 217.9 MB | 1 219.8 MB | 7.77x |
| `katsura-10` | copy-back | 400.1 MB | 401.3 MB | 1.79x |
| `mq-random-10` | swap | 598.8 MB | 597.9 MB | 18.13x |
| `mq-random-10` | copy-back | 160.0 MB | 159.1 MB | 1.93x |
| `katsura-11` | swap | 13 145.9 MB | 13 150.7 MB | 11.44x |
| `katsura-11` | copy-back | 2 759.5 MB | 2 762.0 MB | 1.81x |

Every `VmHWM` agrees to within **0.6%** and every capacity ratio to the reported precision, and
`katsura-11`'s copy-back interreduction stage came back at 50 228.5 ms against the published
50 286.7 ms, a **0.12%** difference. So #330 does not reach these figures and §13.3 describes the
tree this change merges into.

The policy's correctness is checked in the ordinary suite rather than here:

```sh
cargo nextest run -E 'test(subtract_scaled) + test(short_merge_does_not_inherit) \
  + test(scratch_buffer_is_not_handed) + test(matrix_route_reproduces_the_division_route) \
  + test(the_allowance_covers_the_elimination)'
```

---

## 14. Where 20 000 000 came from, and what still crosses it (#490)

#490 asks two things of `max_live_nonzeros`: where the number came from, and what the workloads that
cross it by a hair actually need. The first is answered here from the history; the second is answered
for one of the three workloads and not for the other two, and §14.3 says why.

### 14.1 It was never measured. It is a round number from F4's first batch-reduction commit

`20_000_000` arrives in **`057b4b6f`** (2026-11-02), the commit that added `reduce_batch` — the first
commit in the repository that could run out of memory at all. Its message describes the budget's
purpose and claims nothing about its size:

> Resource exhaustion becomes a return value. `row_echelon_within` gives the sparse elimination a
> budget on live nonzero entries, checked after every row operation, so fill-in reports
> `F4Error::TooManyNonzeros` instead of exhausting memory […] `F4Options` carries the limits with
> documented defaults

And the field's own doc comment, as introduced, is explicit that it is not a memory limit:

> This is a budget on the entries F4 holds, not a ceiling on the process. It does not account for
> the monomial-to-column map, the term vectors of the basis, the scratch buffer elimination merges
> through, or allocator overhead […] **Treat it as the knob that keeps matrix growth recoverable,
> not as a memory limit.**

So the entry count is the primary figure and it was chosen as a recoverability valve, not against a
working set. **The 320 MB came second and is derived from it**, not the other way round: `max_live_bytes`
arrives two days later in **`b2283f1e`**, whose message says the byte budgets

> default to the 320 MB the entry budgets **already described** at 16 bytes an entry

That settles #490's first checkbox. The answer to its title is **no** — and the follow-on question it
poses is therefore the live one: whether 320 MB is the right ceiling for a machine with 503 GB of
RAM. Nothing here answers that, and it is not a question about the entry count.

### 14.2 `mq-random-10` is no longer a near-miss. It peaks 5.1x under the cap

#490's table lists three workloads crossing 20 000 000 by less than 0.05%, which it rightly calls a
coincidence rather than a policy. One of them can be re-measured cheaply, and the premise has
expired:

| | #322's figure | now | against the cap |
|---|---:|---:|---:|
| `mq-random-10` peak live entries | 20 000 277 *(stopped)* | **3 933 045** *(completes)* | **5.1x under** |

#575's defaults are why: with each batch left reduced the matrices the elimination fills in are
smaller, so the quantity this budget counts fell by a factor of five. The figure is identical at caps
of 20 000 000, 25 000 000 and 64 000 000 — which is the check that the peak is the computation's and
not the budget's — and
`f4::tests::test_mq_random_10_no_longer_approaches_the_live_entry_cap` asserts it.

A live-entry count is a **counter**, so this is exact: identical on any machine and under any load,
which is what makes it reportable from a box that could not have produced a timing.

### 14.3 The other two are not measured, and the re-sweep is not either

`anemoi N = 6 PCICO` and `poseidon31-cico-t16-rf4-rp2` are full-width cryptanalysis rows costing
minutes to hours each, and no instrument in the tree reports their peak at a raised budget without
one being written — `examples/f4_memory.rs` reads `ZEEBRA_MAX_ENTRIES` but compiles the Fukuoka
`N = 20` path only. Given that `mq-random-10`'s figure moved by 5.1x under a default change, the
honest expectation is that **theirs moved too**, and that #490's table should be re-measured before
its budget decision rather than reasoned from.

#490's third checkbox — the re-sweep, if the budget moves — is untouched for a second reason: it is a
board-row task, and over the hours this work ran the one-minute load average sat between **592 and
1 261** from other agents' linkers, which `tools/benchlock.sh` does not serialize because they are
builds. §12's own figures were taken under the lock on a quiet box; a re-sweep from this one would
not be comparable with them.

**So the budget does not move here**, and the reason is now a better one than #469's: not that
changing it would reprice old figures, but that two of the three workloads said to need it have not
been measured since the change that moved the third by 5.1x.
