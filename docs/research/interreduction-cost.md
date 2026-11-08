# Inside final interreduction: which half, and what the reductions actually cost

**Measured at:** publication bound `530816cb`…`d412374c` — the commits that published these figures,
recovered from git rather than recorded at the time ([§10](external-comparison-protocol.md#10-the-commit-and-what-a-publication-bound-is)).

Measurement record for #452, which exists because the stage with the largest Amdahl ceiling in this
repository had neither a sub-stage split, a benchmark, nor an operation counter.

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

**So the remaining 4 094 ms is a measured, attributable, and separately addressable cost**, and the
ceiling on it is Groebner.jl's own 1.74 ms for the same stage. Filed separately; it is not this
change's to fix, and this change does not need it to be worth 4.18x.

### 3a.1b The small instances, which say the matrix route must **not** become the default

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

### 3a.2 What the matrix route does not change

* **The answer.** Asserted equal on every rep here, and asserted equal against the division route
  over katsura-4, katsura-5, cyclic-4, cyclic-5 and katsura-4 over GF(13), under all three orders,
  by `interreduce::tests::test_the_matrix_route_reproduces_the_division_route`.
* **Any other instance's cost.** Every figure above is `mq-random-10` grevlex at one digest. The
  stage's shape on katsura under lex is completely different — `buchberger.rs:294-314` records the
  ascending sort alone taking it from 2.5 s to a millisecond — and nothing here transfers.
* **The division route's existence.** It remains the default — see §3a.1b, where it wins by 25x —
  remains the fallback when a budget refuses the matrix, and remains the oracle the matrix route is
  tested against. It is also still on the critical path of FGLM border reduction, the differential
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

# The stage in isolation, over a basis from a real trace. Both routes, same input.
tools/benchlock.sh <tag> taskset -c 0-7 cargo bench --bench f4_stages -- interreduction

# #440 stage 2's A/B is between two commits rather than two flags, so it needs two builds
# from one tree into separate target directories, interleaved. See §3b.
```
