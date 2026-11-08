# Inside final interreduction: which half, and what the reductions actually cost

**Measured at:** publication bound `530816cb`…`d412374c` for §0–§3b — the commits that published
those figures, recovered from git rather than recorded at the time
([§10](external-comparison-protocol.md#10-the-commit-and-what-a-publication-bound-is)). **§3c was
taken at `489ccbd6` plus the change it measures**, recorded at the time rather than recovered,
which is what #335 asked for. **§3d was taken on this branch's two commits before they were rebased
onto `4b0d2282`** — the region-split counters (`c24bcc01` post-rebase) for the counts, and those
against the hoist (`132d20b8`) for the A/B, two builds from one tree. The rebase brings in
`922deeb6`, which adds `F4Options::reduce_batch_rows` **off by default**, so it changes neither the
path these figures describe nor their comparability with §3a and §3b. **§3e was taken at
`0840207f`, base `9746b4ce`**, also recorded at the time; its board rows carry their own resolvable
#505 stamp, so that one is checkable from the data and not only from this header.

Measurement record for #452, which exists because the stage with the largest Amdahl ceiling in this
repository had neither a sub-stage split, a benchmark, nor an operation counter.

**[§3e](#3e-the-adjudication-436s-four-mechanisms-and-what-became-of-the-510x-ceiling) adjudicates
#436's four candidate mechanisms against everything below and says what is left of the 5.10x
ceiling.** Read it first if that is the question; it takes no new measurement and cites only what
the rest of this note establishes.

Pinned: Zeebra at the commit recorded beside each figure. Instance `mq-random-10` from the external
corpus at `REFERENCE_CHARACTERISTIC = 2147483647` under grevlex, identity digest
`72d0ad315fc25409…`, asserted by `examples/f4_profile.rs` against the one in the retained
`reduced-grobner-basis` record. `F4Options::default()`, because that is what
`examples/competitive_sweep.rs` builds its solver from and therefore what the competitive record
describes — under `baseline()` this instance does not finish, refusing at 20 000 277 live nonzero
entries against the 20 000 000 budget both configurations share.

Machine: AMD Ryzen Threadripper PRO 5995WX, 128 hardware threads, 503 GB RAM. Every timing under
`tools/benchlock.sh`, `taskset -c 0-7`, one worker, `RUSTFLAGS` unset, `RUSTC_WRAPPER=""`, a
per-worktree `CARGO_TARGET_DIR`, and the `-C target-cpu=x86-64-v3` floor **verified in the artifact**
by `tools/vec_census.sh` rather than inferred from a build log.

**Durations here are shared-machine durations.** Other agents build concurrently on this box;
`benchlock` excludes other *measurements* and does nothing about shared L3 or memory bandwidth. The
**counts are not affected at all** — they are exact, deterministic, and machine-independent, which
is the whole reason this note treats them as the result and the durations as context.

---

## 0. What was missing, and why it mattered

#436 measured final interreduction's two halves on this instance:

| part of `reduce_grobner_basis_until` | time | share |
|---|---:|---:|
| `minimize_grobner_basis` | 14.03 ms / 14.11 ms | 0.06% |
| the `normal_form` reduction loop | 23.95 s / 24.29 s | **99.94%** |

**That figure existed only in the commit message of `92a262d`.** The string `#436` appeared nowhere
in the tree, and nothing in it could re-derive the split: `StageTimings::interreduction` is one
`Duration`, and `benches/f4_stages.rs:23` stated in its own header that "pair selection, basis
bookkeeping, and **interreduction are outside every stage**" — so the stage
`docs/research/groebner-jl-gap.md` §3 measures at **80.69%** of the run and **13 871x**
Groebner.jl's was the one stage with no Criterion coverage at all.

It also had no operation counters. `F4Statistics::divisor_queries` and `divisor_scan_steps` cover
the **batch** path only. So `groebner-jl-gap.md` §4, arguing that the stage's cost is intermediate
expression swell, had to label its own argument:

> **Labelled as inference, with the measurement that would settle it.** The per-element arithmetic
> above is a plausibility argument, not a measurement: nothing counts terms processed or
> `checked_div` calls inside `normal_form`. … **Not taken here.**

This note takes it.

---

## 1. The instrument

`NormalFormCounts`, filled by `SparseMultiPoly::normal_form_counted`. The counting is a
**const-generic parameter on one function**, not a second implementation:
`normal_form_counting::<COUNT>` is what both entry points call, so the uncounted path compiles the
increments away and the counted path cannot drift from the code it is describing. A proptest over
three fields (GF(13), GF(7), GF(2^31−1)), three arities and all three monomial orders asserts the
two agree —
`sparse_multivariate_polynomial_arithmetic::tests::test_counting_does_not_change_the_normal_form`.

### 1.1 Timing and counting are separate runs, and this was measured rather than assumed

The first version tied the counters to `measure_stages`. On this instance that run reported
**41 752.79 ms** total with **35 487.60 ms** in interreduction, against the ~29 913 ms the same
configuration had been recording — because the divisor-test counter increments **once per reducer
per term popped**, which is the innermost loop in F4.

`measure_stages`' own overhead is 3.8%–11.5% (#349). A counter that costs a third of the stage
cannot share a flag with one that costs a tenth of the run, because then the stage split could only
ever be read off a run that was substantially slower than the one being described. So
`F4Options::count_interreduction` is a separate flag with a separate entry point
(`reduce_grobner_basis_counted`), and
`interreduction_stop_tests::test_measuring_times_the_stage_without_counting_operations` pins that
measuring does **not** count.

**Consequence for anyone reading a counted run:** its durations are not quotable. The counts are.

---

## 2. The split, confirmed — and a baseline that does not reproduce

Six runs, **interleaved** between this change and its parent commit `a1867a7`, in one session on
cores 0-7 under the lock. Both binaries built from one tree into separate target directories with
the AVX2 floor verified in each artifact. `base` is the parent; `mine` is this change.

| rep | side | total/ms | symbolic | construction | elimination | extraction | **interreduction** | other |
|---|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | base | 42 203.16 | 419.67 | 1 062.14 | 4 267.87 | 112.76 | **36 241.70** | 99.01 |
| 1 | mine | 41 646.55 | 409.40 | 1 024.33 | 4 153.60 | 112.07 | **35 852.14** | 95.01 |
| 2 | base | 42 980.32 | 390.80 | 1 019.85 | 4 103.45 | 107.85 | **37 265.31** | 93.06 |
| 2 | mine | 43 583.02 | 425.46 | 1 093.18 | 4 308.61 | 118.25 | **37 536.45** | 101.07 |
| 3 | base | 46 085.88 | 436.10 | 1 112.64 | 4 343.78 | 116.11 | **39 973.35** | 103.90 |
| 3 | mine | 44 877.78 | 435.74 | 1 110.26 | 4 470.20 | 120.87 | **38 636.89** | 103.81 |

Counts identical on every run: 10 batches, 1 777 pairs reduced, 247 basis elements.

**First result — the instrumentation is free when it is off.** Median total 42 980 ms against
43 583 ms, a ratio of **1.014**, inside each side's own run-to-run spread of **1.08x–1.09x**. The
const-generic gate does what it claims: a build that is not counting does not pay for the counters.

**Second result, which was not what this issue set out to find.** Against
`groebner-jl-gap.md` §3's figures for the same configuration on the same instance:

| stage | here (base median) | §3 | ratio |
|---|---:|---:|---:|
| symbolic | 419.67 | 403.16 | 1.041x |
| construction | 1 062.14 | 1 025.21 | 1.036x |
| elimination | 4 267.87 | 4 159.19 | 1.026x |
| extraction | 112.76 | 108.04 | 1.044x |
| **interreduction** | **37 265.31** | **24 136.08** | **1.544x** |

**Four stages reproduce within 4.4%. Interreduction is 54% higher.** Uniform machine load cannot
produce that pattern — it would move all five. So one of the following holds, and this note does not
establish which:

1. Interreduction is the one stage that walks a multi-thousand-term working polynomial 534 135
   times (§3), so it is the one whose working set leaves cache and the one exposed to L3 contention
   from the concurrent builds that run constantly on this box. The other four stages are small.
2. Something between `25e10fe` (§3's pin) and `a1867a7` made the stage slower. Nothing in that
   range touches `normal_form`; the interleaved A/B above rules out *this* change as the cause.

**What it means for the conclusions either way.** The share is **86.70%**, not 80.69%, and the
Amdahl ceiling is **7.52x**, not 5.10x. Both move in the direction that makes replacing this stage
more valuable, not less. But **no ratio should be computed across the two sessions** — this is M26's
Rule 3, and #318/#319 are the standing instances of it. Figures quoted against each other must come
from one session, which is why the A/B above is interleaved.

---

## 3. The counts, and the verdict: rewrite-bound, not swell-bound

One `mq-counts` run. Durations from a counting run are not quotable (§1.1); the counts are exact.

| quantity | value |
|---|---:|
| elements reduced | 247 |
| reduction loop's share of the stage | **99.97%** (10.71 ms / 35 438.62 ms) |
| reduction steps | 534 135 |
| terms popped | 602 377 |
| terms in the answer | 68 242 (~276 an element) |
| divisor tests | 22 587 181 |
| reducers per call | 246 |
| divisor-tail terms merged | 18 296 667 (~34.3 a step) |
| **terms rewritten** | **1 174 314 651** (~2 199 a step) |
| largest working polynomial | 7 283 terms |
| **swell** — popped / answer | **8.8x** |
| **scan** — tests / popped | **37.5** |
| **rewrite** — rewritten / tail merged | **64.2x** |

**The 99.94% split is confirmed**, at 99.97% here: `minimize_grobner_basis` is 10.71 ms against the
reduction loop's 35 438.62 ms. #436's figure now has a source in the tree.

**And §4's inference about swell is wrong, in the direction that matters.** It argued:

> At roughly a nanosecond per `checked_div` that is of order **10⁸ divisor tests for one element** —
> several hundred thousand terms passing through a working polynomial whose answer has a few
> hundred. **That is intermediate expression swell.**

Measured: **22.6 million divisor tests for all 247 elements**, about 91 000 per element — three
orders of magnitude below the inference. And the answer is not "a few hundred" terms but **68 242**
across 247 elements, i.e. ~276 terms each; §4 read the 604 figure as terms when it is Groebner.jl's
*column* count, which is distinct monomials. So the swell factor is **8.8x**, which is real but
modest, and 22.6 M divisor tests cannot be 35 seconds at any plausible cost per test.

**The cost is the per-step rewrite.** `subtract_shifted` is linear in the whole working polynomial
on every reduction step, whether or not the divisor's tail reaches it. Each step merges **34.3**
tail terms into a working polynomial of mean length **2 199** — an amplification of **64.2x** — and
over 534 135 steps that is **1 174 314 651 terms rewritten**. Nothing else in the counters is within
an order of magnitude of it.

### 3.0a And the per-term cost says *which part* of the rewrite is expensive

1 174 314 651 rewrites in 35 438.62 ms is **30.2 ns a term**. A term here is
`(Monomial<10>, Zp2147483647)` — 48 bytes — so if the rewrite were the `extend_from_slice` memcpy
it mostly looks like, it would be moving 56.4 GB in 35.4 s, i.e. **1.59 GB/s** on a machine whose
single-core streaming bandwidth is more than an order of magnitude above that.

So it is **not** memory bandwidth. 30 ns a term is about right for what
`subtract_shifted`'s *merge* region does per element: one `Monomial` multiply (`:491`, ten `u32`
additions, recomputed per call rather than per surviving term) plus one `MonomialOrder::cmp`
(`:492`), which under grevlex recomputes `degree()` on both operands by summing `[u32; N]` and then
walks the exponents in reverse.

**That is the single most actionable thing in this note.** The expensive part of the 64.2x is the
comparison region, not the copy region — and the comparison region is exactly what #440 stage 2
removes, by binary-searching for the smallest shifted tail term and memcpy-ing everything below it
wholesale. The cheap stage is aimed at the expensive half.

It also explains why `maxwrk` matters less than it looks: the peak working polynomial is 7 283 terms
against a 2 199-term mean, so the cost is the *typical* step rather than a few large ones.

### 3.1 The verdict, keyed to the fix each answer implies

#440 asks for one of four verdicts. It is **copy-bound**:

| verdict | measured | the fix it would imply |
|---|---|---|
| compare-bound | no — 22.6 M tests cannot be 35 s | a cheaper monomial comparison (#317) |
| search-bound | no — 37.5 of 246 reducers scanned, and the same 22.6 M bound applies | a leading-monomial index (#331, #436 candidate 1) |
| **copy-bound** | **yes — 64.2x amplification, 1.17e9 terms rewritten** | **windowing the merge (#440 stage 2), or not building the intermediates at all (#471)** |
| none of them | no | the issue would have closed cheaply |

So **#440 stage 2 is funded, and §3.0a says it is aimed at the right half.** It removes the
comparison work over terms the tail never reaches, and the comparison work — not the copying — is
what the 30.2 ns a term is made of. Stage 2's own acceptance criteria say it keeps the `Θ(R·W)` in
term *copies*; at 1.59 GB/s implied, those copies are not what is costing the time, so keeping them
is acceptable and **stage 3's heap division stays unfunded** — which is the outcome #440's own
staging said it preferred.

**And this is the strongest available argument for #471.** A matrix formulation neither windows the
rewrite nor makes it cheaper: it does not perform it. 1.17 billion term rewrites, for a final basis
of 68 242 terms reached in 534 135 steps, is the signature of exactly the intermediate growth F4's
matrix formulation exists to avoid — which Zeebra avoids in every batch and then pays once, at the
end, for six sevenths of the run.

### 3.2 What these counters do not settle

* **How the 64.2x splits between the two regions.** §3.0a infers from the per-term cost that the
  comparison region dominates; it does not measure the split. #440 stage 1 asks for exactly that
  — terms below `pos(q·tail_min)`, between it and `pos(q·tail_max)`, and above — and one more
  counter pair settles it. The inference is strong enough to fund stage 2 and not strong enough to
  predict how much of the 64.2x it recovers.
* **Whether the baseline discrepancy in §2 is contention or a change.** Stated as an open question
  rather than resolved; see the two candidates there.
* **Nothing about any other instance.** Every figure here is `mq-random-10` grevlex at one digest.
  katsura and cyclic have very different interreduction shapes — `buchberger.rs:294-314` records
  katsura-6 under lex going from 2.5 s to a millisecond on the sort alone — and none of this
  transfers to them.

---

## 3a. #471: the matrix route, measured

Three reps, **interleaved in one process on one build**, so no cross-build or cross-session
difference is in the ratio. The example asserts the two routes' bases **equal** on every run; a
difference would have panicked rather than printed.

| rep | route | total/ms | interreduction/ms | stage share | basis |
|---|---|---:|---:|---:|---:|
| 1 | division | 40 843.17 | 35 149.00 | 86.06% | 247 |
| 1 | **matrix** | **9 517.01** | **4 004.10** | 42.07% | 247 |
| 2 | division | 40 808.56 | 35 247.40 | 86.37% | 247 |
| 2 | **matrix** | **9 753.13** | **4 185.36** | 42.91% | 247 |
| 3 | division | 40 485.68 | 34 971.39 | 86.38% | 247 |
| 3 | **matrix** | **9 801.60** | **4 093.93** | 41.77% | 247 |

| | median | per-rep |
|---|---:|---|
| **end to end** | **4.18x** | 4.29x, 4.18x, 4.13x |
| the stage itself | **8.59x** | 8.78x, 8.42x, 8.54x |

Run-to-run spread is 1.009x on the division side and 1.030x on the matrix side, so a 4.18x median
is not a noise artefact — it is two orders of magnitude outside the spread.

The matrix is **identical on all three reps** — 7 642 x 7 996, 893 531 nonzeros — which is what a
deterministic construction should be and is a check on the instrument as much as on the change.

### 3a.1 The estimate was wrong by 24x, and the reason is the better finding

`groebner-jl-gap.md` §4 estimated the matrix pass at **~170 ms**, by scaling Groebner.jl's 1.74 ms
by Zeebra's own 97.1x per-operation constant. The measured pass is **4 094 ms**, twenty-four times
that — and the error is not in the constant. It is in the **shape**:

> **The 4 094 ms is this run's and is the high end of the range.** §2.4 of `m27-baseline.md`
> measures the same stage at **2 306.2 ms** at `53fbf50` and §3c.4 at **2 085.9 ms**, on boxes whose
> division side matches the board row where this one's is 1.40x it. The honest range is
> **2 086–4 094 ms**; the ratios below use the cell counts, which are exact and reproduce to the
> digit, so none of them moves.

| | Groebner.jl | Zeebra | ratio |
|---|---:|---:|---:|
| rows | 250 | **7 642** | 30.6x |
| columns | 604 | **7 996** | 13.2x |
| cells | 151 000 | **61 105 432** | **405x** |

The estimate assumed the two engines would build the *same matrix* and differ only in cost per
entry. They do not. **Zeebra's autoreduce matrix has 405x the cells**, and 405x / 24x says Zeebra's
per-cell cost is actually *better* than the scaling assumed — the pass is slow because the matrix is
enormous, not because the kernel is.

And the row counts say why. 250 rows for 247 elements means Groebner.jl's closure added about
**three** reducer multiples; Zeebra's added **7 395**. Groebner.jl's 604 columns is almost exactly
`247 leading monomials + 354 standard monomials = 601`, i.e. **the only monomials in its basis
entering autoreduce are the leading monomials and the standard monomials** — nothing in its tails is
reducible at all, so there is nothing for a closure to find. Zeebra's basis carries ~7 395 further
reducible monomials in its tails.

That is a property of the *main loop*, not of interreduction. Groebner.jl's `linalg_main!` reduces
rows fully against the pivots in every batch, so a candidate leaves a batch already in normal form
with respect to everything above it. Zeebra's candidate extraction takes rows from an echelon form
that has not been back-substituted, so candidates carry reducible tails and the debt accumulates to
the end of the computation — where this stage pays it.

**So the remaining pass is a measured, attributable, and separately addressable cost** — 2 086 ms at
§3c.4's instrument, 4 094 ms here — and the ceiling on it is Groebner.jl's own 1.74 ms for the same
stage. Filed separately as #477; it is not this change's to fix, and this change does not need it to
be worth 4.18x. #477's own text quotes the 4 094 ms, so its arithmetic about the 405x cell count is
built on a figure **1.78x–1.96x too large**; §3c.4 records the correction.

> **Fixed by #477; see §3c.** Making each batch's candidates come out reduced takes this matrix
> from 7 642 x 7 996 to **252 x 606** — Groebner.jl's 250 x 604 to within six columns — and the
> stage from 2 400 ms to **16.4 ms**, which is 9.4x the comparand rather than 2 353x. The
> attribution in this paragraph was correct: the cost was the main loop's, and paying it there
> costs 2.4% of the elimination stage.
>
> **And the 4 094 ms above is the high end of a range.** §2.4 of `m27-baseline.md` measures the
> same stage at **2 306.2 ms** and §3e.4 at **2 085.9 ms**, on boxes whose division side matches
> the board row where this one's is 1.40x it. So the pre-#477 stage is **2 086–4 094 ms**, and the
> figure #477 reasoned from was 1.78x–1.96x the smaller end. None of the cell counts move: they are
> exact and reproduce to the digit.

### 3a.1b The small instances, which say the matrix route must not become the default *globally*

> **Superseded in part by §3e.** The lex regression below is confirmed end-to-end and across more
> rungs, and the order-aware route this section proposes now exists as
> `InterreductionRoute::ByOrder`. What keeps the default on the division route is no longer this
> section's reason — see §3e.3, which is memory with no budget on it.

`cargo bench --bench f4_stages -- interreduction`, on the lock, pinned. Both routes over the **same**
basis from the same trace, so each pair is an A/B rather than two numbers over two inputs.

| instance / order | division | matrix | |
|---|---:|---:|---|
| katsura-6 grevlex | 2.0725 ms | 1.9373 ms | 1.07x faster |
| katsura-6 grlex | 1.5841 ms | 0.99858 ms | 1.59x faster |
| **katsura-5 lex** | **89.168 µs** | **2.2249 ms** | **25.0x slower** |
| cyclic-5 grevlex | 237.53 µs | 138.20 µs | 1.72x faster |

Three rungs favour the matrix route by 1.07x–1.72x. **The fourth is a 25x regression**, and it is
the case `buchberger.rs:294-314` already documents:

> On katsura-6 under lex — whose basis is in shape position, five linear elements over one
> univariate of degree 32 — that is the difference between 2.5 seconds and a millisecond.

A basis in shape position is the **best** case for iterated division — the ascending-order sort means
every substituted tail is already in normal form — and the **worst** case for a matrix, which must
carry columns spanning the univariate's whole degree range. So the matrix route's advantage is not
uniform, and the measured spread across one flag is from **+4.18x end-to-end** to **−25x on a
stage**, separated by the monomial order.

**Consequence.** The default stays on the division route, on evidence rather than on caution. The
right shape is not a global default but a route chosen from the instance and the order, which is the
"order-specific default rather than a global one" that M22-A's and M22-E's measurements jointly
implied and which **#273** owns. `fglm::shape` already ships a tested shape-position detector that
is deliberately unwired; it would serve as the criterion here.

**What §3e did with that.** The order half is now built — `InterreductionRoute::ByOrder` builds a
matrix under a graded order and divides under lex — and measured across the whole ladder, where the
split this section inferred from four rungs holds on seventeen. The instance half is still #273's.
`ByOrder` is **not** the default, for the reason in §3e.3 rather than the reason here.

### 3a.2 What the matrix route does not change

* **The answer.** Asserted equal on every rep here, and asserted equal against the division route
  over katsura-4, katsura-5, cyclic-4, cyclic-5 and katsura-4 over GF(13), under all three orders,
  by `interreduce::tests::test_the_matrix_route_reproduces_the_division_route`.
* **Any other instance's cost.** Every figure above is `mq-random-10` grevlex at one digest. The
  stage's shape on katsura under lex is completely different — `buchberger.rs:294-314` records the
  ascending sort alone taking it from 2.5 s to a millisecond — and nothing here transfers.
* **The division route's existence.** It remains the default — see §3a.1b, where it wins by 25x,
  and §3e.3, which is why the default did not move even once the lex case was handled — remains the
  fallback when a budget refuses the matrix, and remains the oracle the matrix route is tested
  against. It is also still on the critical path of FGLM border reduction, the differential
  oracles and `multi_div_rem`, which is why #440 stage 2's windowed merge is worth taking
  independently of this change.

---

## 3b. #440 stage 2: the windowed merge, and where the divisor tail actually lands

Three reps, interleaved between this change and its parent, one session, on the lock, pinned, both
artifacts' ISA floor verified. The division route is what `mq` measures, so this is an A/B on the
merge alone.

| rep | unwindowed total | windowed total | ratio | unwindowed stage | windowed stage | ratio |
|---:|---:|---:|---:|---:|---:|---:|
| 1 | 41 373.19 | 38 945.18 | 1.062x | 35 744.99 | 33 051.01 | 1.082x |
| 2 | 42 473.61 | 41 083.92 | 1.034x | 36 889.26 | 35 261.24 | 1.046x |
| 3 | 41 771.20 | 38 216.97 | 1.093x | 35 909.35 | 32 617.00 | 1.101x |

**Median 1.073x end to end. The windowed side's own run-to-run spread is 1.075x.**

So the effect is **inside the noise band**, and well inside the ~20% this repository reads
differences at. What can be said is weaker than a ratio and still worth saying: the sign is
consistent **3 of 3**, paired within each rep, at 3.4%–9.3%. That is evidence the change is not a
regression. **It is not a measured speedup and is not quoted as one.**

### 3b.1 And that answers #440's own open question, in the opposite direction to its guess

#440's comment reasoned about where the shifted tail lands:

> The shifted tail is `q · tail(d)`, bounded above by `q · lead(d)`, which is exactly the term just
> popped — i.e. `working`'s old maximum. So the tail lands *below the old top but plausibly near
> it*, and the comparison region then spans almost all of `working` in order to place terms
> clustered at its far end. The cheap memcpy region gets what is left, which may be almost nothing.
>
> **This is a hypothesis about where the tail lands, not a measurement.**

If that were right, the prefix below `q · tail_min` would be almost all of `working` and windowing
would remove almost all of the comparison work — a large win, not a 7% one. The measurement says the
prefix is **small**, so `q · tail_min` lands near `working`'s *bottom* and the shifted tail **spans
most of the working polynomial** rather than clustering near its top. With a mean tail of 34.3 terms
over a mean working length of 2 199, the tail is sparse across a wide span rather than dense in a
narrow one.

**The consequence, stated plainly: the 64.2x amplification is largely irreducible by windowing.**
Most of those 1.17 billion rewrites are inside the span the tail genuinely straddles, and no merge
boundary removes them. Two routes remain:

- **#440 stage 3, heap division**, which is what removes the per-step live set rather than
  narrowing it. Its own staging said stage 3 should be reached "only if stage 2 leaves the copies
  dominant"; the measurement says stage 2 leaves *most of the work* dominant, which is a stronger
  trigger than the one it wrote.
- **#471's matrix route**, which does not narrow the rewrite or make it cheaper: it does not perform
  it. Measured at **4.18x** (§3a), against this change's unmeasurable ~7%.

So the ordering the evidence supports is the one §3a already took: replace the stage, and keep the
windowed merge because it is free, correct and marginally positive for the division route that
remains on FGLM border reduction, the differential oracles and `multi_div_rem`.

### 3b.2 What this does not establish

The per-step region split #440 stage 1 asked for is **still not measured directly** — this infers
the prefix's size from an end-to-end ratio, which is a weaker instrument than counting it. A
`terms_below_window` counter beside the existing ones would turn the inference into a measurement,
and is the honest remaining item on #440.

**Taken in §3d.**

---

## 3d. #440 stage 1, finished: the per-step region split, counted rather than inferred

One `mq-counts` run at the recorded digest `72d0ad315fc25409…`, build flags verified in the
artifact. Every count in §3 reproduces to the digit — 602 377 popped, 68 242 in the answer,
18 296 667 tail terms merged, 1 174 314 651 rewritten over 534 135 steps, 64.2x — so this is the
same computation §3 described, with three more counters on it.

| region of the per-step rewrite | what it costs an element | terms | share | mean a step |
|---|---|---:|---:|---:|
| below the window, `[0, pos(q·tail_min))` | `extend_from_slice` | 166 320 801 | **14.2%** | 311.4 |
| **the span, `[pos(q·tail_min), pos(q·tail_max)]`** | **a monomial multiply and an `order.cmp`** | **893 610 377** | **76.1%** | **1 673.0** |
| above the window | `extend_from_slice` | 114 383 473 | 9.7% | 214.2 |
| total rewritten | | 1 174 314 651 | | 2 198.5 |

**§3.0a's inference was right, and this is the measurement it asked for.** Three quarters of the
rewrite is in the region that pays a monomial multiply and a `MonomialOrder::cmp` per element; the
quarter that is `memcpy` is split 14.2% below the window and 9.7% above it. So the 30.2 ns a term
in §3.0a is not a bandwidth figure averaged over a memcpy — it is the per-element cost of the
comparison region, diluted by a quarter of cheap copying.

**It also explains stage 2's ~7% exactly, in the direction §3b.1 guessed.** The window removes the
comparison work over the prefix, and the prefix is **14.2%** of the rewrite. A change that removes
14.2% of the dominant cost in a stage that is ~86% of the run predicts roughly 10% end to end, and
§3b measured 3.4%–9.3%. The prefix is small, as §3b.1 inferred from the ratio; it is now counted.

**The window's downside is bounded, and now quantified.** Comparisons total 900 169 163 against a
span of 893 610 377, so everything that is not a span element — the binary search plus the two
loop-exit comparisons — is **6 558 786**, i.e. **12.3 a step** against a mean working polynomial of
2 199 whose `log2` is 11.1. The `partition_point` costs what it claims and nothing more.

### 3d.1 And it exposes a redundancy that is neither of #440's three stages

| | count |
|---|---:|
| divisor-tail terms merged | 18 296 667 |
| **`Monomial` products computed in the merge** | **894 232 085** |
| products per tail term merged | **48.9x** |

`subtract_shifted`'s merge loop computed `&tail[j].0 * monomial` **once per iteration**, and
`Ordering::Less` — the branch taken for every working term stepped over, which is 1 673 of them a
step against a 34.3-term tail — leaves `j` alone. So the same ten-`u32` product was recomputed
across the whole span: **875 935 418 of the 894 232 085 products were recomputations of a value the
previous iteration had already formed.**

This is not a candidate from #436's list and not one of #440's three stages. It needs no new data
structure, no new boundary and no change of algorithm — only computing the shifted term in the
outer loop, where `j` advances, instead of the inner one. The bound after the change is
`tail_terms_merged + 2 · reduction_steps`, which on these counts is **≤ 19 364 937** products — at
least **46.2x** fewer. The bound is **asserted**, by
`sparse_multivariate_polynomial_arithmetic::tests::test_the_merge_multiplies_each_tail_term_once`,
rather than trusted; the exact post-change count on this instance is derived from the bound and not
separately measured.

Whether removing 875.9 M monomial multiplies moves the wall clock is a separate question from
whether the source performs them, because LLVM's partial-redundancy elimination could in principle
have hoisted the product across the back edge already. §3d.2 measures it, and the answer is the
useful part of this section.

### 3d.2 The hoist, measured: ~1.6% on the stage, and that is the finding

Three reps, **interleaved** between the hoist and its parent, one session, on the lock, pinned to
cores 0-7, two builds from one tree into separate binaries with each artifact's AVX2 floor verified
by `tools/vec_census.sh` — the same protocol as §3b, for the same reason.

| rep | base total | hoist total | ratio | base stage | hoist stage | ratio |
|---:|---:|---:|---:|---:|---:|---:|
| 1 | 28 514.09 | 28 409.27 | 1.0037x | 22 760.56 | 22 530.91 | 1.0102x |
| 2 | 28 900.52 | 28 550.93 | 1.0122x | 22 988.56 | 22 598.37 | 1.0173x |
| 3 | 28 539.24 | 28 321.35 | 1.0077x | 22 815.06 | 22 459.63 | 1.0158x |

**Median 1.0077x end to end and 1.0158x on the stage, against a base-side spread of 1.0136x and
1.0100x.** Sign consistent 3 of 3, paired within each rep. That is evidence it is not a regression
and **it is not a measured speedup**, by the same standard §3b applied to stage 2.

**The negative result is worth more than the change.** Removing **875 935 418** monomial multiplies
from a 22.8-second stage moved it by about 360 ms — **under 0.4 ns a removed multiply**, which is
less than a single `checked_add`. A ten-variable `Monomial` product cannot be that cheap, so it was
not being performed: either LLVM eliminated the loop-carried redundancy already, or the multiply
issued into slots the loop was spending on something else. The two are not separable from a
duration, and nothing here distinguishes them.

**So §3.0a's attribution needs splitting, and this is the half that was wrong.** §3.0a read the
30.2 ns a term as "one `Monomial` multiply (recomputed per call rather than per surviving term) plus
one `MonomialOrder::cmp`". The multiply half is now measured at **≤1.6% of the stage**. What is left
in the span is the **comparison** and the **term copy** — 893 610 377 of each — and the per-term
cost is theirs.

**It ships anyway, on the same grounds stage 2 did, plus one this repository should care about more:
the counter was lying.** Before the hoist, `merge_monomial_multiplies` reported 894 232 085
multiplies that the machine was not performing — an instrument that would have funded a fix for a
cost that does not exist, which is precisely the failure mode §3.0a's inference fell into. After it,
the counter is bounded at **19 364 937** by a test, and reports something much closer to what the
hardware does.

### 3d.3 What stage 3 is now competing against

Stage 1 is finished and its verdict is sharper than the four #440 asked for. The stage is
**copy-bound in volume and compare-bound in cost**: 76.1% of the rewritten terms sit in the region
that pays per element, and the window cannot reach them because the shifted tail genuinely
straddles the working polynomial (§3b.1, now counted). Both cheap routes are now spent and **both
measured inside the noise** — stage 2's window took the 14.2% prefix for ~7%, §3d.2's hoist took the
48.9x multiply redundancy for ~1.6% — and what remains in the span is **893 610 377
`MonomialOrder::cmp` calls and 1 174 314 651 term copies**, which §3d.2 narrows the per-term cost
down to. Only two things touch those: a cheaper comparison (#317), or a structure that never
materializes the working polynomial.

That is Monagan–Pearce heap division, #440 stage 3. Reference of record under
`docs/research/external-provenance-policy.md` §6: **Monagan and Pearce, *Sparse polynomial division
using a heap*, J. Symbolic Comput. 46 (2011) 807–822**, and *Polynomial division using dynamic
arrays, heaps, and packed exponent vectors*, CASC 2007, LNCS 4770, 295–315. No implementation was
read and no code copied; any implementation would be from the published description.

**The headroom, labelled as an extrapolation rather than a measurement.** The heap holds one pending
entry per quotient term with an unexhausted divisor tail, so the live set goes from 2 199 terms to
at most `k` entries, where `k` is the quotient length — on this instance 534 135 steps over 247
elements, i.e. about **2 162** streams an element, `log2 k ≈ 11.1`. Total heap traffic is one
insert and one pop per tail term merged: **18 296 667**, against the span's 893 610 377
comparisons. At a sift cost of 1–2 comparisons a level that is **2.0e8–4.1e8** comparisons, a
**2.2x–4.4x** reduction in monomial comparisons, and the 1.17 billion term copies go to **zero**.
Against that: the comparisons become random access into a `k`-entry heap where today they are a
sequential walk, which is the risk #440 named and which no count can settle.

**And §3d.2 is a warning about that extrapolation, not a reason to trust it.** Two changes aimed at
counted operations in this merge have now each predicted a large reduction in a count and delivered
a ratio inside the noise. A third prediction from the same counters — however arithmetically sound —
has to carry that record with it. The heap is worth building only with an A/B budgeted up front and
a willingness to discard it on its numbers.

**And the stage it would speed up is no longer F4's.** #471 replaced final interreduction with one
Macaulay matrix at a measured 4.18x (§3a), so stage 3's value is for the division route that
survives — FGLM border reduction, the differential oracles, `multi_div_rem`, and the lex
shape-position bases where #478 measured division **25x** better than the matrix. The trigger #440
wrote ("only if stage 2 leaves the copies dominant") is met and then some; the *priority* is lower
than when it was written, because the instance that motivated it no longer runs this code by
default.

---

## 3c. #477: the debt, paid where it is incurred

**Measured at `489ccbd6` plus the change itself.** Both arms of every table below are flags on one
build, so there is no before-side tree to name and nothing merged after `489ccbd6` can have moved
one arm relative to the other. `489ccbd6` is a merge commit on `main` and so stays resolvable
(#505). ISA floor and instance digest are printed in the run's own header by
`f4_profile -- mq-rows`, measured as `x86-64-v3 or better (AVX2)` and
`72d0ad315fc25409792625465578d18329597d3ee183e75f257774d9215803b2`.

§3a.1 attributed the autoreduce matrix's 405x cell count to the **main loop** rather than to
interreduction, filed it separately, and said it was "not this change's to fix". This is that fix,
and it is worth more than the change that found it.

`F4Options::reduce_batch_rows` back-substitutes each batch's pivot columns out of every other row
after the plan's elimination, so a candidate leaves a batch already in normal form with respect to
everything above it — which is what Groebner.jl's `linalg_main!` does and what Zeebra's candidate
extraction, reading an echelon form that was never back-substituted, did not.

### The matrix is Groebner.jl's, to within six columns

| | Groebner.jl | Zeebra, echelon | Zeebra, reduced |
|---|---:|---:|---:|
| rows | 250 | 7 642 | **252** |
| columns | 604 | 7 996 | **606** |
| cells | 151 000 | 61 105 432 | **152 712** |
| nonzeros | — | 893 531 | **68 325** |
| the stage | 1.74 ms | 2 400 ms | **16.4 ms** |

§3a.1 said "Groebner.jl's 604 columns is almost exactly `247 leading monomials + 354 standard
monomials = 601`, i.e. the only monomials in its basis entering autoreduce are the leading
monomials and the standard monomials". Zeebra's reduced basis now enters autoreduce with 252 rows
and 606 columns against that 250 and 604 — a **400x** reduction in cells, landing on the comparand's
shape rather than near it. The remaining two rows and two columns are not explained here and are
small enough that nothing in this section rests on them.

The stage falls from 2 400 ms to **16.4 ms**, which is 9.4x Groebner.jl's 1.74 ms — inside the
11.6x–97.1x per-operation representation constant `groebner-jl-gap.md` §0 measures for every other
stage. **Interreduction is no longer an outlier**: the 13 871x of §3 and the 2 353x of §3a.1 were
both the shape, not the kernel, and with the shape fixed the stage behaves like the rest of the
engine.

### Four arms, because the default is the division route

The payoff lands in a different place on each interreduction route — a smaller autoreduce matrix on
the matrix route, fewer term rewrites on the division one — and the division route is what ships
(§3a.1b, and #507). So the cross is measured rather than one half of it:

| arm | total | elimination | interreduction | against the default |
|---|---:|---:|---:|---:|
| `div` + echelon — **ships today** | 31 713 ms | 4 483 ms | 25 744 ms | — |
| `div` + reduced | **6 441 ms** | 4 590 ms | 1 415 ms | **4.92x** |
| `mat` + echelon — #478's route | 8 467 ms | 4 590 ms | 2 400 ms | 3.75x |
| `mat` + reduced | **4 851 ms** | 4 531 ms | **16.4 ms** | **6.54x** |

Medians of three interleaved repetitions in one process on one build. Two things in that table are
worth saying out loud:

- **This flag alone beats #478's flag alone**, 6 441 ms against 8 467 ms, on the path that ships.
  The two are not alternatives — together they are 6.54x — but if only one were taken, it is this
  one.
- **The price is 2.4%.** Elimination goes from 4 483 ms to 4 590 ms while 2 058 195 rows are
  back-substituted. That is the finding that contradicts the prior: §3a.1b's
  `InterreducedBlock` was measured and *rejected* for filling in the reducer block, and this pass
  is the same fill-in paid after the elimination instead of before it. It is cheap here because the
  pass is output-sensitive — it indexes the pivot columns and visits only the rows that hold one —
  and because back-substitution at the end of a batch touches rows that are already as dense as
  they will get, where interreducing the block beforehand makes every later row operation longer.

### The classical rungs do not regress, which is the difference from #478's flag

§3a.1b is the standing warning against reading a default off one instance: the matrix interreduction
route is 1.07x–1.72x faster on three rungs and **25x slower** on katsura-5 under lex, because a
basis in shape position is the best case for iterated division and the worst case for a matrix.
That exposure was the reason its default did not move. Measured for this flag, with division
interreduction on both arms and the minimum of seven interleaved repetitions:

| instance / order | echelon | reduced | |
|---|---:|---:|---|
| katsura-5 lex | 0.5981 ms | 0.5892 ms | 1.02x — **the rung that breaks the matrix route** |
| katsura-5 grevlex | 0.4620 ms | 0.3595 ms | 1.29x faster |
| katsura-6 grevlex | 2.5268 ms | 1.6777 ms | 1.51x faster |
| cyclic-5 grevlex | 1.0336 ms | 0.8729 ms | 1.18x faster |
| cyclic-4 lex | 0.0348 ms | 0.0383 ms | 0.91x — **slower** |

No rung regresses materially, and the shape-position case that costs the matrix route 25x is
**neutral** here — because this flag does not change how interreduction is performed, only how much
there is left to do. The one loss is 3.5 µs on the smallest instance in the corpus, where a per-batch
pass has 35 rows to examine and nothing to save.

### Why the default does not move in this change

On this evidence it probably should, and that is a separate decision from this one:

- Every figure above is `mq-random-10` grevlex at one digest, plus five rungs. **A board row is not
  a projection**, and #507 is the issue that establishes the rule: the figure quoted against the
  board must be measured against the board, in a cohort with the other four engines.
- Flipping this changes every recorded Zeebra row, so it is a cohort re-take rather than a flag
  edit, and #507 already owns that work for `interreduce_by_matrix`. There are now two flags in the
  same position and one cohort run should settle both.
- #507's projection is superseded by this change and in Zeebra's favour. It projected ~7 999 ms for
  `mq-random-10` with `interreduce_by_matrix` on, putting the row **1.14x behind Singular**; with
  this flag as well the measurement is 4 851 ms, and the 2 306 ms #507 called "the difference
  between leading Singular and trailing it" is now 16.4 ms.

So the flag ships off, on the same discipline `interreduce_by_matrix` follows, and the decision
moves to #507 with better evidence than it had.

### What this does not establish

* **The answer.** Asserted equal on every rep here, and asserted equal against the echelon route
  over the correctness corpus under all three orders and over cyclic-4, katsura-4 and katsura-5 by
  `tests::test_reducing_batch_rows_returns_the_same_basis_on_the_corpus` and
  `tests::test_reducing_batch_rows_agrees_on_the_benchmark_families`. Both of those also assert
  that a candidate's *tail* differs somewhere in the sweep, so neither can pass vacuously.
* **That candidate selection is unchanged.** Back-substitution cannot move a row's leading column,
  so the selection is identical; §3a.1 called that an argument rather than a test, and
  `reduction::tests::test_the_row_form_does_not_change_candidate_selection` is now the test.
* **The two extra rows and columns.** 252 x 606 against Groebner.jl's 250 x 604 is unexplained.
* **Any other board row's cost.** Five rungs and one MQ instance are not the cohort.
* **The 7 395 reducer multiples.** §3a.1 attributed the row count to reducible tails in the basis;
  removing them took the autoreduce matrix to the comparand's shape, which is consistent with that
  attribution but does not separately measure the closure.
## 3e. #507: the decision, on a cohort rather than on a single-instance A/B

Pinned at `0840207f`, whose #505 stamp is base `9746b4ce` and patch id `e5476c47…`. All 55 board
rows here carry that stamp and no other, so they are a single cohort — and the stamp stays
resolvable through any later rebase of this branch, because a merge base is an ancestor of `main`
and a patch id hashes the diff rather than the history.

Every figure under `tools/benchlock.sh`, `taskset -c 0-7`, `ZEEBRA_MACHINE=workstation`,
`ZEEBRA_AFFINITY=0-7`, `RUSTC_WRAPPER=""`, a private `CARGO_TARGET_DIR`, one worker, `--wall 60`
except `katsura-11` at 600. Board rows `--measure --write`, one row per process, so their peak-RSS
figures are attributable.

**This section describes the default path, and §3c's change does not alter it.** `#555` landed
`F4Options::reduce_batch_rows` while this work was in flight, and it is what §3c measures — so the
two sections are about different configurations of the same stage and their figures are not
alternatives to each other. `reduce_batch_rows` is `false` in `F4Options::baseline()` and
`recommended()` inherits it, so every figure here has it off; `reduction.rs:164` is the whole of its
effect, selecting `RowForm::Reduced` over the pre-existing `RowForm::Echelon`. Read §3c for what the
stage costs once the debt is not accrued, and this section for what the route choice is worth on the
path the board rows and `F4Options::default()` actually take.

The ladder figures in §3d.2 come from `examples/interreduction_routes.rs` rather than from the
board, and were taken at `b89d68b7`, before this branch was rebased twice. They are not re-taken,
and the reason is checkable rather than asserted: of everything merged in between, `#541` made **no
`src/` change** at all (its result is negative), and `#555`'s is behind the flag above. The work
counts and matrix shapes are the check that matters, because they are exact and machine-independent
rather than timings — `mq-random-10` reproduces 7 642 × 7 996 with 893 531 nonzeros, and katsura-6
under lex 7 983 × 8 015 with 314 500, on both trees.

### 3e.0 What #451 projected, and what the board actually says

`m27-baseline.md` §2.4 applied a measured **3.627x** to the board's own 29 011.4 ms and projected
**~7 999 ms**, labelling it arithmetic and requiring the row to be re-taken before publication.
Here is the row, as a five-engine cohort at one commit on one digest (`72d0ad315fc2`),
`reduced-grobner-basis`, grevlex, three reps of the Zeebra side and six of each comparand:

| engine | mean | min | max | peak RSS |
|---|---:|---:|---:|---:|
| **zeebra, division** | **31 202.4 ms** | 30 505.8 | 31 679.7 | 163.4 MB |
| **zeebra, matrix** | **8 333.1 ms** | 8 263.0 | 8 400.6 | **600.8 MB** |
| singular | 7 760.5 ms | 7 615.3 | 8 209.0 | 23.5 MB |
| sagebrush | 377.7 ms | 354.5 | 405.1 *(not authoritative)* | 31.4 MB |
| msolve | 266.5 ms | 263.5 | 273.6 | 12.4 MB |
| groebner.jl | 90.6 ms | 85.1 | 93.2 | 730.4 MB |

Three reps of each Zeebra route, seven of each comparand.

**The projection was good.** Measured end to end: **3.74x** on the means, **3.69x** on the minima —
and 3.69x is 1.8% from §2.4's 3.627x, taken by a different instrument. The projected 7 999 ms lands
against a measured 8 333.1 ms, **4.2% out**.

So the figure that may now be published is a row and not an arithmetic step, and it says:

> `mq-random-10` under the matrix route is **1.08x behind Singular** on the means and 1.12x on the
> minima, where the division route is **4.25x** behind on the means and **4.11x** on the minima.
> M27's 2x minimum is met with room; Singular parity is **not** reached, and stops about 1.1x
> short — which is what §2.4 predicted at 1.14x.

One further row, under `--interreduction by-order`, confirms the route resolution end to end:
**8 461.0 ms at 602.0 MB** under grevlex — inside the three matrix reps' range on memory and 0.7%
above their maximum on time. The **602.0 MB against the division route's 163.4 MB** is the signature
that says `ByOrder` resolved to the matrix route, since the two routes differ in peak RSS by 3.68x
and in nothing else a board row observes.

Two things the division side corroborates. Its **minimum**, 29 623.8 ms, is **1.021x** the retained
board row's 29 011.4 ms, so this cohort composes with §1.1's ratios. Its **spread** is wide — 18%
across three reps against the matrix route's 3.7% — because other agents were building on the box
throughout; `benchlock` excludes other measurements and not other load. The minima are the cleaner
statistic and both are quoted.

### 3e.1 And the lex task crosses Singular, which no Zeebra row had done on this instance

One rep each, same cohort:

| engine | `lex-basis-by-conversion` | peak RSS |
|---|---:|---:|
| zeebra, division | 32 177.5 ms | 162.2 MB |
| **zeebra, matrix** | **8 827.7 ms** | **602.6 MB** |
| singular | 9 643.7 ms (mean of two; 9 267.3–10 020.2) | 36.1 MB |
| sagebrush | 480.8 ms *(not authoritative)* | 31.7 MB |

**8 827.7 against 9 643.7 is 1.09x ahead**, and against Singular's own fastest of the two reps
(9 267.3 ms) still **1.05x ahead**. At a 5–9% margin on a box whose spread is of that order this is
**parity rather than a lead** — but it is the first `mq-random-10` row on which Zeebra's figure is
not behind Singular's, and the division route on the same task is 3.34x behind. The route is worth
3.645x end to end here, within 2.7% of its value on the basis task. msolve and Groebner.jl are
`unsupported` on this task, so the column has two operands.

### 3e.2 The ladder, interleaved: the matrix route wins under every graded order and loses under lex

`examples/interreduction_routes.rs`, both routes in one process on one build with the bases asserted
equal, 60 s per route, `F4Options::default()` otherwise. This is the instrument the board rows
cannot be: it reports `F4Statistics::interreduction_matrix`, so a rung that does not move can be
told apart from one where the matrix was never built.

| rung | grevlex | grlex | lex |
|---|---:|---:|---:|
| katsura-4 | 1.77x | 1.18x | **0.67x** |
| katsura-5 | 1.38x | 1.13x | **0.37x** |
| katsura-6 | 1.01x | 1.26x | **0.16x** |
| katsura-7 | 1.24x | 1.71x | both stopped |
| katsura-8 | 1.53x | — | — |
| katsura-9 | 1.80x | — | — |
| katsura-10 | 2.06x | — | — |
| cyclic-4 | 1.43x | 1.14x | 1.11x |
| cyclic-5 | 1.14x | 1.25x | **0.64x** |
| cyclic-6 | 1.35x | — | — |
| cyclic-7 | 1.84x | — | — |
| cyclic-8 | 1.21x | — | — |
| mq-random-6 | 1.50x | 1.50x | both stopped |
| **mq-random-10** | **3.78x** | — | — |
| mq-planted-6 | 1.35x | 1.08x | 1.07x |
| mq-planted-10 | 1.22x | 1.07x | 1.10x |
| mq-planted-14 | 1.55x | 1.24x | 1.12x |

Above 1.00x the matrix route is faster.

**Four rungs here are below the instrument's noise floor and their ratios are not evidence.**
`katsura-4`, `cyclic-4`, `mq-planted-6` and `mq-planted-10` run in **25–170 µs**, where a stage
clock read four times a batch and a shared-L3 box dominate the difference. A third run of the table
put `mq-planted-6` grlex at **0.88x** where the one above has 1.08x — the same work, the same
matrix (9 × 19, 24 nonzeros, identical to the digit), and a ratio that crossed 1.00x. Quoting those
rungs either way would be quoting noise, so the ranges below exclude them.

Over the **thirteen rungs that take 0.5 ms or more**:

| order | range | rungs |
|---|---|---|
| grevlex | **1.01x–3.78x faster** | katsura-5…10, cyclic-5…8, mq-random-6, mq-random-10 |
| grlex | **1.15x–1.71x faster** | katsura-5, katsura-6, katsura-7, cyclic-5, mq-random-6 |
| lex | **1.59x–6.25x slower** (0.63x–0.16x) | katsura-5, katsura-6, cyclic-5 |

Not one graded rung above the noise floor favours the division route, and not one lex rung favours
the matrix route. And **every lex regression is on a rung whose basis is in shape position** —
katsura and cyclic-5. The lex rungs that are *not* in shape position are the `mq-planted` family,
whose lex basis is the planted point's linear forms, and `cyclic-4`; all of them sit at the noise
floor, so the shape-position reading is **consistent with** this table rather than separately
confirmed by it.

`cyclic-9`, `cyclic-10` and `mq-random-14` stopped under both routes at 60 s, which is a fact about
the rungs. The three Poseidon and two Anemoi rungs pin their own characteristic and this example
compiles the reference field only; their board times are 0.05–293 ms, so interreduction is not
where their cost is.

**The mechanism is legible in the matrix shape, not inferred.** katsura-6:

| order | matrix | basis | density |
|---|---|---:|---:|
| grevlex | 217 × 249 | 22 | 5.81% |
| grlex | 169 × 201 | 32 | 10.97% |
| **lex** | **7 983 × 8 015** | **6** | 0.49% |

A lex basis in shape position — linear elements over one univariate of high degree — is the **best**
case for iterated division, because the ascending-order sort leaves every substituted tail already
in normal form, and the **worst** case for a matrix, which must carry columns spanning the
univariate's whole degree range. This is what `buchberger.rs:294-314` already documented and what
§3a.1b measured at the stage level as a 25x regression on katsura-5 lex; the end-to-end figure for
that rung is 0.39x, and the regression **grows with the rung** — 2.56x and 6.25x slower for
katsura-5 and katsura-6, the two above the noise floor.

**No rung fell back.** `fell_back` was false and `refused_by` `None` on every rung under every
order, including the 7 983 × 8 015 lex matrix. That is not reassurance; §3e.3 is why.

### 3e.3 The decision: the default does not move, and the reason is memory with no budget on it

The time evidence above would flip the default to `InterreductionRoute::ByOrder`. The peak-RSS
figures, which §3a's A/B had no way to take because `f4_profile` does not report memory, say not
yet:

| rung | division | matrix | memory | time |
|---|---:|---:|---:|---:|
| `mq-random-10` | 163.4 MB | 600.8 MB | 3.68x | 3.74x faster |
| **`katsura-11`** | **534.6 MB** | **13 148.3 MB** | **24.59x** | 2.29x faster |

`katsura-11` finished both ways at a 600 s budget — 274 003 ms by division against 119 460 ms by
matrix — so 13.1 GB is what the pass costs and not a stopped run's partial footprint. It is also
**reproducible to 0.03%**: an earlier cohort on the pre-rebase tree measured 13 144.9 MB against
13 148.3 MB here, so this is a property of the computation and not of one run.

**And every budget was satisfied.** The matrix route's refusal tests rows, columns and live
*entries* (`mod.rs:546` into `interreduce::interreduce_by_matrix`, against `max_matrix_rows`,
`max_matrix_columns` and `live_entry_allowance::<F>()`), and the entries are not where the memory
goes. `mq-random-10` shows the gap directly: **893 531 nonzeros**, on the order of ten megabytes of
entries, against a **437 MB** increase in process peak. The quantity being budgeted is a small
fraction of the quantity that binds — which is precisely the defect `f4-resource-scaling.md` §10
records for symbolic preprocessing before #305 (88.4% of peak RSS in one `VecDeque<Monomial<20>>`
while the budget saw 1.3%), in a different stage. The suspected site is the one #477 names: the
closure is built as polynomials before it becomes rows, and `mq-random-10`'s closure adds **7 395**
reducer multiples where Groebner.jl's adds about three.

> **A default must not be able to take a 535 MB computation to 13.1 GB with every limit
> satisfied**, however much faster it is, because that converts a working computation into an OOM on
> any machine smaller than this one. So `ByOrder` ships selectable and measured, `Division` stays
> the default and stays the configuration every published figure was taken in, and the flip is
> gated on **#536** making the matrix pass's working set a budgeted quantity.

Siting a size threshold instead was considered and rejected: two points, 3.68x and 24.59x, do not
locate a crossover, and an unmeasured threshold is the thing this file exists not to produce.

**This supersedes §3a.1b's consequence and not its measurement.** §3a.1b concluded "the default
stays on the division route" from the lex regression alone, and proposed an order-aware route as
the right shape. The order-aware route now exists and is measured across the ladder, which is
§3a.1b's proposal carried out; what keeps the default where it is has turned out to be a different
and larger reason than the one §3a.1b gave.

### 3e.4 Two figures corrected

**#477's "remaining stage cost is 4 094 ms" is 2 085.9 ms.** The interleaved ladder run measures
`mq-random-10`'s matrix-route interreduction stage at **2 085.9 ms** of a 7 818.6 ms total (26.68%),
and §2.4 measured 2 306.2 ms at `53fbf50`. #477's 4 094 ms belongs to #478's PR run, whose division
side was 1.40x the board row — the loaded box §2.4 attributes the 4.18x to. The honest range is
**2 086–2 306 ms**, so #477's downstream reasoning about the 405x cell count is built on a figure
**1.78x–1.96x too large**. The cell count itself is unaffected: 7 642 × 7 996 is reproduced exactly
here, as is the 893 531 nonzeros.

**katsura-11 is a new board row**, and the first evidence that the route choice can be a capability
difference rather than a speed one. At a **120 s** budget the matrix route finishes and the division
route does not — it had reduced 259 of 537 basis elements when the budget expired — so inside that
budget the rung is reachable by one route only. At 600 s both finish, so the difference is
budget-relative and is stated that way. The cohort:

| engine | katsura-11, `reduced-grobner-basis` | peak RSS |
|---|---:|---:|
| zeebra, division | 274 002.9 ms | 534.6 MB |
| **zeebra, matrix** | **119 460.2 ms** | **13 148.3 MB** |
| singular | 54 836.1 ms (mean of two) | 41.7 MB |
| sagebrush | 2 808.6 ms *(not authoritative)* | 114.1 MB |
| msolve | 1 792.0 ms | 22.7 MB |
| groebner.jl | 524.3 ms | 861.5 MB |

All five engines agree on quotient dimension **1 024**. Zeebra's division route is **5.00x** behind
Singular here and its matrix route **2.18x** — the same shape as `mq-random-10`, one rung further
up, and the first `katsura-11` row the board has had at any characteristic.


### 3e.5 What this does not settle: the two flags together

**#477's `reduce_batch_rows` landed while this was in flight, and the combined default is not
decided here.** §3c measures it at **4.92x** end to end on the division route — more than the route
choice is worth on its own — and the two together at **6.54x**, and it regresses no classical rung,
including the katsura-5 lex case that costs the matrix route 25x. `README.md` records both defaults
as #507's to move.

One of the two is moved here and one is not, for a stated reason: **the flags are not independent,
and the interaction runs in the direction that could dissolve §3e.3's gate.** With batches left
reduced, §3c measures the autoreduce matrix at **252 × 606** rather than 7 642 × 7 996 — and that
closure is exactly what §3e.3 attributes the matrix route's memory to. So the plausible outcome is
that `matrix` + `reduced` costs neither the 13.1 GB nor the 437 MB, in which case the gate is on a
configuration nobody would ship and both defaults move together. The opposite outcome is equally
possible and equally unmeasured.

`competitive_sweep --reduce-batch-rows on|off` exists for that measurement, and the Zeebra row's
`library_version` now names **both** flags, because a row naming one is a row whose configuration
cannot be reconstructed. The 2×2 itself was attempted and **abandoned mid-table** rather than
published: the box reached a one-minute load average of **39.97** from other agents' builds, and the
`division` + `echelon` arm's Singular came in at **9 426.5 ms** against the clean cohort's
7 760.5 ms mean — 1.21x, larger than several of the ratios the table has to resolve. **#575** is the
2×2, re-taken on a quiet box.

**Two arms did complete, as five-engine cohorts, and one of them is a result.** They are at
different base commits, so no ratio spans them; each is read inside itself.

| arm | zeebra | its Singular | zeebra vs Singular | peak RSS |
|---|---:|---:|---:|---:|
| `division` + `echelon` | 29 988.1 ms | 9 426.5 ms *(contended)* | 3.18x behind | 163.1 MB |
| **`division` + `reduced`** | **6 115.6 ms** | **7 507.9 ms** | **1.23x ahead** | 413.8 MB |

> **`reduce_batch_rows` alone puts `mq-random-10` ahead of Singular on `reduced-grobner-basis`** —
> 6 115.6 ms against 7 507.9 ms in its own cohort, with msolve at 273.5 ms and Groebner.jl at
> 89.8 ms unchanged. That is the row M27 measured the 4.13x deficit on, and it is **the first
> `mq-random-10` basis row on which Zeebra's figure is not behind Singular's**. §3e.1's conversion
> parity was the first row of either task; this is the first on the task the comparison rests on.

Two cautions on it. The Singular figure in that arm is **7 507.9 ms against the clean cohort's
7 760.5 ms mean**, 3.2% low rather than 21% high, so this arm was not taken under the contention
that spoiled the other — but it is one rep, where §3e.0's figures are three. And the memory is
**413.8 MB against `echelon`'s 163.1 MB**, a 2.5x rise: smaller than the matrix route's 3.68x, in
the same direction, and now subject to #536's budget like everything else. Neither caution is a
reason to doubt a 1.23x; both are reasons #575 takes the table rather than quoting these two rows as
one.


---

## 3e. The adjudication: #436's four mechanisms, and what became of the 5.10x ceiling

#436 asked for one thing — *profile within `normal_form` on `mq-random-10` at the recorded digest,
divisor-search steps against arithmetic, and report which of three candidate mechanisms the cost is,
before any implementation*. #440 added a fourth. This section settles each against what is now on
record, because an adjudication kept only in an issue thread is not where the next reader of these
measurements will look.

**No new measurement is taken here.** Every figure below is already published in §3, §3a, §3b, §3c
or §3d of this note, at the commits its own header declares; the arithmetic over them is labelled as
arithmetic.

### 3e.1 The four mechanisms

| # | mechanism | verdict | what settles it |
|---|---|---|---|
| 1 | the divisor search inside `normal_form` | **refuted** | §3 — **37.5** divisor tests a term popped, **22 587 181** across all 247 elements |
| 2 | repeated work across elements | **still unmeasured** | nothing. See §3e.2 |
| 3 | the `O(n²)` loop shape itself | **confirmed as the count, refuted as the cost** | §3 — 534 135 reduction steps is real; §3.1 — the cost is per-step, not per-step-count |
| 4 | the per-step full-dividend merge (#440) | **confirmed, and it is the cost** | §3 — 64.2x amplification, **1 174 314 651** terms rewritten; §3d — 76.1% of them in the compared span |

**Candidate 1 is refuted by a counter at this site, not by analogy with the batch path.** #436 was
explicit that `F4Statistics::divisor_queries` and `divisor_scan_steps_per_query` cover the *batch*
path only and might not cover interreduction's `find_map`, and that whether the two behave alike was
the open question. They do not share a counter and the question was answered directly:
`NormalFormCounts::divisor_tests` increments **inside** the `find_map` in
`SparseMultiPoly::normal_form_counting`
(`src/poly/multivariate/sparse_multivariate_polynomial_arithmetic.rs`), which is the scan #436
quoted, reached through `reduce_grobner_basis_counted` — so the 37.5 is interreduction's own search
over its own 246 reducers. It is **higher** than the batch path's 16.6 steps a query and still
nowhere near enough: 22.6 M `checked_div` calls cannot be a 35-second stage at any plausible cost
per call, and they sit three orders of magnitude below the 1.17 G term rewrites beside them.
`interreduction_stop_tests::test_the_interreduction_counters_are_internally_consistent` pins that
the counter is populated from this loop.

**Candidate 3 needs splitting, and both halves are now answered.** #436 posed it as "if the per-division
cost is what dominates rather than the count, the fix is in `normal_form` and not in the loop". The
count is 534 135 reduction steps over 247 elements; the cost is 2 199 terms rewritten per step. The
per-step cost dominates, which is candidate 4 — so #436's own disjunction resolves against the loop
shape. But the *fix* went the other way from what that implied: #471 removed the loop outright
rather than making a step cheaper, and #477 removed most of the work before the stage ever sees it.

**Candidate 4 is the cost, and §3d's region split says which part of it.** Copy-bound in volume,
compare-bound in cost: 76.1% of the 1.17 G rewrites are inside the span the shifted tail straddles,
where each term pays a `MonomialOrder::cmp`. The two cheap fixes aimed at it both measured inside
the noise — stage 2's window ~7% (§3b), §3d.2's multiply hoist ~1.6% — and §3d.2 is the reason
§3.0a's attribution is now half retracted: the multiply half of the per-term cost was not being
performed at all. What is left in the span is the comparison and the copy, which is #562 (heap
division) and #317 (a cheaper comparison), and neither is this issue's.

### 3e.2 What candidate 2 still lacks, precisely

Element `i` and element `i + 1` are reduced against almost the same divisor set and nothing is
cached between them. **No counter in this note distinguishes work that is repeated across calls from
work that is not.** `NormalFormCounts` is per-call and summed: `calls`, `reducers`,
`dividend_terms`, `terms_popped`, `reduction_steps`, `tail_terms_merged` and the three region
fields all accumulate, so the 247 calls are indistinguishable from 247 unrelated ones. Measuring it
needs something the counters do not have — a repeat rate over `(quotient monomial, reducer)` pairs,
or a hit rate against a cache that does not exist — and §3's figures cannot be reanalysed into it.

So candidate 2 is **not** answered by elimination, and this note does not claim it is. What *can* be
said is that its subject has shrunk: the loop it would cache across is 25 744 ms on the path that
ships today and **1 415 ms** with `reduce_batch_rows` on, **2 400 ms** with `interreduce_by_matrix`
on, and **16.4 ms** with both (§3c) — so the headroom any cache could recover is bounded by whatever
#507 settles the default to be. It is filed separately rather than left inside a closed issue.

### 3e.3 The 5.10x ceiling: spent in the lab, intact in the product

#349 put final interreduction at **80.4%** of `mq-random-10`, an Amdahl ceiling of **5.10x** if the
stage became free. Arithmetic over §3c's four arms, which are flags on one build and therefore
directly comparable:

| arm | total | the stage | stage share | ceiling left on this arm | realized vs. shipping |
|---|---:|---:|---:|---:|---:|
| `div` + echelon — **the default** | 31 713 ms | 25 744 ms | 81.2% | 5.31x | 1.00x |
| `div` + reduced | 6 441 ms | 1 415 ms | 22.0% | 1.28x | 4.92x |
| `mat` + echelon | 8 467 ms | 2 400 ms | 28.3% | 1.40x | 3.75x |
| **`mat` + reduced** | **4 851 ms** | **16.4 ms** | **0.34%** | **1.003x** | **6.54x** |

Three things follow, and the third is the one that matters.

**The ceiling has been exceeded, not merely approached.** 6.54x against a ceiling of 5.31x computed
on the same arm's own stage share. An Amdahl bound assumes everything outside the stage is fixed and
#477 made it not fixed: the residue that is neither elimination nor interreduction falls from
`31 713 − 4 483 − 25 744 = 1 486 ms` to `4 851 − 4 531 − 16.4 ≈ 304 ms` (arithmetic over §3c's rows).
Candidates leaving each batch in normal form shrinks work the ceiling had treated as constant.

**And nothing is left inside the stage to take.** At 16.4 ms — 9.4x Groebner.jl's 1.74 ms, inside the
11.6x–97.1x per-operation constant `groebner-jl-gap.md` §0 measures for every other stage —
interreduction stops being an outlier, and the remaining ceiling on it is 1.003x. There is no
version of #436's loop worth optimizing in that arm.

**None of it ships.** `F4Options::default()` is `recommended()`, and `src/grobner/f4/options.rs`
sets `interreduce_by_matrix: false` and `reduce_batch_rows: false` — each documented "off by default
until the A/B is on record", the discipline every strategy flag here follows. So the shipping path is
the first row, the 5.10x ceiling is fully intact on it, and **the whole of the win is a default
decision rather than an implementation one**. That decision is #507's, in a cohort rather than from a
single-instance A/B, and #536 is the gate on half of it: the matrix route's working set is 13.1 GB on
katsura-11 with every budget satisfied.

### 3e.4 So #436's framing was right about the stage and wrong about the remedy

"This loop, not the storage" was correct and is confirmed twice over — 99.94% in `92a262d`, 99.97%
here (§3), against `minimize_grobner_basis`'s 10.71 ms, which is what retired #304 as a time
argument. What it got wrong is the implied premise that a cost located *in* a loop is fixed *in*
that loop. Every change that moved this stage came from outside it:

- **#471** does not make the loop cheaper; it does not run the loop. **3.75x** in §3c's cross,
  **4.18x** in §3a's own A/B, **3.63x** in #451's at `53fbf50`. The spread is the *division* side
  moving, not the matrix side: #507 established that #478's division arm was 1.40x the board row and
  its 86.27% stage share above the ~80% everything else agrees on, so the higher ratio comes from an
  inflated numerator. The figure that composes with the board is the lowest of the three.
- **#477** does not touch interreduction at all. It stops the **main loop** emitting candidates with
  reducible tails, so the stage has almost nothing to do. 4.92x on the shipping route — larger than
  #471's, from a change in a different stage.
- Both changes **inside** `normal_form`, aimed at counted operations in the hot merge, measured
  inside the noise: ~7% and ~1.6%.

That is the transferable finding, and it is worth more than the verdicts in §3e.1: in this engine,
two fixes aimed at the operation the counters said was hot each returned a ratio inside the noise,
and both large wins came from not generating the operation. §3d.2's warning applies to #562 for
exactly this reason.

---

## 4. Reproducing

```sh
# Build flags verified in the artifact, not inferred. `tools/vec_census.sh` counts vector
# instructions under `zeebra::`; a build that lost `-C target-cpu=x86-64-v3` has none.
export CARGO_TARGET_DIR=/path/outside/the/worktree RUSTC_WRAPPER=""
unset RUSTFLAGS
cargo build --release --example f4_profile
tools/vec_census.sh "$CARGO_TARGET_DIR/release/examples/f4_profile"

# The stage split. Cheap instrumentation; durations are comparable.
ZEEBRA_MACHINE=workstation ZEEBRA_AFFINITY=0-7 \
  tools/benchlock.sh <tag> taskset -c 0-7 \
  cargo run --release --example f4_profile -- mq

# The operation counts. ~36% slower for the per-reducer counter, so this run's
# durations must not be quoted beside the one above.
ZEEBRA_MACHINE=workstation ZEEBRA_AFFINITY=0-7 \
  tools/benchlock.sh <tag> taskset -c 0-7 \
  cargo run --release --example f4_profile -- mq-counts

# #471's A/B: both interreduction routes, interleaved in one process on one build.
ZEEBRA_MACHINE=workstation ZEEBRA_AFFINITY=0-7 \
  tools/benchlock.sh <tag> taskset -c 0-7 \
  cargo run --release --example f4_profile -- mq-matrix

# #477's A/B: both batch row forms crossed with both interreduction routes, interleaved in
# one process on one build, then the same flag over the classical rungs. Prints the ISA floor
# and the instance digest in its header. See §3c.
ZEEBRA_MACHINE=workstation ZEEBRA_AFFINITY=0-7 \
  tools/benchlock.sh <tag> taskset -c 0-7 \
  cargo run --release --example f4_profile -- mq-rows

# The stage in isolation, over a basis from a real trace. Both routes, same input.
tools/benchlock.sh <tag> taskset -c 0-7 cargo bench --bench f4_stages -- interreduction

# #440 stage 2's A/B is between two commits rather than two flags, so it needs two builds
# from one tree into separate target directories, interleaved. See §3b. The same applies to
# §3d.2's hoist; §3d's region split is counts and comes out of the `mq-counts` run above,
# on the `regions:` and `merge ops:` lines.

# §3e's ladder sweep: both routes per rung, in one process, with the matrix route's own
# verdict and the fallback reason. `--orders` adds grlex and lex.
tools/benchlock.sh <tag> taskset -c 0-7 \
  cargo run --release --example interreduction_routes -- --wall 60
tools/benchlock.sh <tag> taskset -c 0-7 \
  cargo run --release --example interreduction_routes -- --orders --wall 60 \
  katsura-4 katsura-5 katsura-6 katsura-7 cyclic-4 cyclic-5 \
  mq-planted-6 mq-planted-10 mq-planted-14 mq-random-6

# §3e's board rows. One row per process, so the peak-RSS figure is attributable; the
# memory figures in §3e.3 come from here and not from the sweep above.
. tools/external/env.sh
for route in division matrix; do
  ZEEBRA_MACHINE=workstation ZEEBRA_AFFINITY=0-7 \
    tools/benchlock.sh <tag> taskset -c 0-7 \
    cargo run --release --example competitive_sweep -- \
      --row mq-random-10 --task reduced-grobner-basis \
      --interreduction "$route" --measure --wall 60 --write
done

```
