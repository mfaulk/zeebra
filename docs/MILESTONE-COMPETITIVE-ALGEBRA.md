# M25 — Competitive Algebra Baselines and Verified Frontier Improvements

**Status:** in progress.
**Parent issue:** #292. **Integration issue:** #299.
**Prerequisite:** M24, complete and merged — #217 (report), #281 (close), #291 (the `RUSTFLAGS`
correction that invalidated two sets of #185 and #231 figures).
**Plan issues:** §4 lists every one, classified `required` / `conditional` / `independent parallel` /
`future`.

M23 changed the unit of progress from an optimization to a problem. M24 changed what counts as
progress on a problem: either a reproduction of something published, or a witness for a registered
instance nothing public has a witness for. M25 adds the axis neither had — **an external comparand
running on this machine.**

Every external figure this repository has ever quoted was measured on someone else's hardware. The
Anemoi calibration is the sharpest case. At `N = 5` Zeebra's FGLM conversion finished 479x faster
than the published Magma figure, and [`anemoi.md`](research/anemoi.md) §8a.1 declined to say whether
that is faster arithmetic, a better algorithm, or a different computation. That refusal was correct:
with a 2014 Xeon E5-2630 v3 on one side and a 2022 Threadripper PRO 5995WX on the other, **the
measurement cannot distinguish those three.** No amount of care in reading the number fixes that. A
same-machine comparand can.

---

## 1. Prior evidence, and the rule it imposes

M24 §10.1 produced a predicted-versus-observed table and then a methodological result sharper than
any of its benchmark rows:

> Every prediction about a stage Zeebra had already measured held. Every prediction about a quantity
> nobody had measured was wrong, and three of the four were wrong by more than an order of magnitude.

The three that were wrong:

| quantity | predicted | measured | factor |
|---|---|---|---|
| six-round symbolic build, peak memory | "not a concern", ~68 MB | **57.0 GB** | **838x** |
| F4 live-entry budget ladder, memory | 0.32 / 1.6 / 6.4 / 16 GB of entry storage | **195 MB accounted inside a 14 752 MB process** | **75x**, and the wrong quantity |
| univariate route, cost per family | ~2 min | **15.2 s** | 7.9x, from charging the loop a stage it does not run |

So M25 runs under one rule, and it is the rule that shapes every gate below:

> **Memory is measured before a run is authorized, not estimated after it.**

Both frontier attempts in this milestone — Anemoi `N = 6` (#286) and any Poseidon rung past
`rf2-rp4` (#297, #243) — are gated on a *measured* footprint at the rung below, not on a cost model
fitted to time.

### 1.1 One obsolete figure that must stop being cited

M16's initial F4 profile had elimination at **65–88%** of runtime. That was *before* M16's own
optimizations. The current profile is
[`MILESTONE-F4-OPTIMIZATION.md`](MILESTONE-F4-OPTIMIZATION.md) §8.5:

| system | order | total | symbolic | construction | elimination | interreduction |
|---|---|---:|---:|---:|---:|---:|
| cyclic-5 | lex | 3.14 ms | 0.65 | **1.48 (47%)** | 0.37 (12%) | 0.35 |
| katsura-6 | lex | 19.53 ms | 4.42 (23%) | **9.33 (48%)** | 1.28 (**7%**) | 2.33 |
| katsura-7 | grlex | 46.72 ms | 2.58 | 6.21 (13%) | 8.00 (**17%**) | **28.71 (61%)** |
| katsura-7 | grevlex | 32.13 ms | 1.64 | 5.53 (17%) | 7.12 (22%) | **16.90 (53%)** |

Elimination is **7–22%**. The cost moved to **interreduction** (the basis-size quadratic) and
**matrix construction** (the per-matrix monomial-to-column map and sort, which do not shrink now that
pair criteria replaced 59 large matrices with 107 small ones). On harder cryptanalytic instances
symbolic closure and matrix width can bind instead.

**#269 (H13) cites the 65–88% figure in its title.** So do parts of the H-series survey. Those claims
are corrected or qualified in §7.4 *before* being used to justify engineering work, and H12–H17 are
reprioritized from the measurements of #263 rather than from a profile that predates the
optimizations it describes.

### 1.2 What M24 named as the credible next steps

M24 §10.4 named five, each with the measurement that made it credible. All five are in M25:

1. **#243, a collecting multiply.** The six-round build's 57 GB is a transient `O(terms²)` sawtooth
   for a 4.3 MB result — 56.6 GB predicted against 57.0 GB measured. The gate on any eight-round
   attempt and on `rf4-rp2` / `rf6-rp0` at six.
2. **#237, profiling the F4 memory gap**, sharpened by `f4-resource-scaling.md` §6a: the *uncapped*
   rungs peak **below** the capped ones while doing more work, so an error-path allocation is now as
   plausible as a preprocessing one.
3. **Anemoi `N = 6` (#286).** The reference prints a basis and a dash for the conversion. A measured
   figure there would be **produced**, not reproduced.
4. **A `k = 3` family, or a hybrid (#287).** §6.4 showed round reduction cannot help, so these are
   the only directions that change the univariate trade.
5. **Axis 2 of #180, a structured Sylvester determinant (#297).** Now the only axis left with an
   asymptotic improvement in it, and measurable against an already-parallel baseline (92–95%
   efficient to 32 cores) rather than a serial one.

---

## 2. Objectives

1. **Make an external comparison possible at all.** Provision msolve, Groebner.jl, Sagebrush and
   Singular on this machine, with pinned versions and a smoke test proving each computes the same
   basis on the same input.
2. **Freeze a protocol that refuses bad comparisons** before any adapter writes a row — inequivalent
   mathematical inputs, inequivalent computational tasks, and ratios against a tool that could not
   accept the input.
3. **Produce a first competitive report** on identical problems and identical hardware, saying where
   Zeebra leads, lags, and **cannot be compared**.
4. **Attribute the Anemoi discrepancy** to arithmetic, algorithm, or a different computation — or
   state which of the three the available evidence cannot separate.
5. **Bound the symbolic build by its output** (#243), and find where F4's unaccounted memory actually
   lives (#237).
6. **Calibrate the resultant cost model** over enough points to be worth extrapolating from (#289),
   and decide the next Poseidon rung from it rather than from round count.
7. **Leave three durable scoreboards** — competitive, cryptanalytic, cost-model — regenerable from
   retained records.

## 3. Scope, and explicit non-goals

In scope: external process adapters; the comparison protocol; corpus normalization; measured RSS in
records; the collecting multiply; F4 memory attribution; the determinant cost model; the parallel
off-domain validation; the Anemoi multi-characteristic ladder and `N = 6`; three bounded research
gates.

**Not** in scope, and each for a stated reason:

| non-goal | why |
|---|---|
| Copying any comparand's implementation into Zeebra | msolve, Groebner.jl and Singular are GPL; Zeebra is MIT. [`external-provenance-policy.md`](research/external-provenance-policy.md) is the authority. Running a GPL binary as a separate process is fine; linking or copying is not. Sagebrush is MIT OR Apache-2.0 and reuse *is* permitted — see §7.5. |
| Running Magma | Not installed, not licensed here. The Anemoi comparands are the published logs, read as logs. |
| A sparse-FGLM implementation | `MILESTONE-FGLM-SCALABILITY.md` §8.5 records a no-go on three measurements, reaffirmed §9.7. #224 may revisit it only by overturning one of those three, naming which. |
| Wiedemann/Krylov for F4 | #58: permanent no. Deferred for FGLM behind a named trigger (large `D` **and** shape position) that nothing in the corpus is within three orders of. |
| GPU or out-of-core work | #69, #86–#89, #225. Requires a named target kernel, workload, predicted benefit and benchmark first. Expense alone does not justify it. |
| Implementing the whole FreeLunch attack | #202 delivers a go/no-go with a bounded experiment. §9.1. |
| A three-variable solver built to see what happens | #287 derives first. §9.2. |
| Reducing F4's memory | #237 is an *attribution* issue. A reduction found along the way becomes its own issue. |
| Reducing the off-domain check count | #285 keeps 8. The guard stays non-optional. |

---

## 4. Issue reconciliation

Reconnaissance read the tracker before anything was written. Six findings, and the first is a
coordination defect rather than a research one.

### 4.1 The board was lying by omission

`scripts/agent/zb-claim.sh orient` ranks open issues by joining them to their row on
[project #7](https://github.com/users/mfaulk/projects/7). **Thirty-one issues had no board row** —
including the entire H-series (#256–#274), every M24 follow-up (#237, #283–#290), and #243, the
issue M24 §10.4 named as its first next step. They were open, unclaimed, unblocked, and **invisible
to the orientation command every agent is told to start from.** An agent following `CLAUDE.md` §2
exactly would never have seen them.

All thirty-one are now on the board with a Priority set. This is recorded here because the failure
mode is silent: `orient` returned `rc=0` with a healthy-looking queue, so nothing distinguished
"nothing left" from "the thing you want is not joined".

### 4.2 Work already complete

| | evidence |
|---|---|
| #274 (H18) external provenance and licensing | Closed. Every comparand's licence verified from its own file at a pinned SHA. Three classes: reuse permitted (Sagebrush), algorithmic reference only (msolve, Groebner.jl, Singular, BRiAl, Giac, Oscar.jl, MathicGB), no grant (Fukuoka MQ data). M25 consumes this and does not re-derive it. |
| #180 axis 1, parallel determinants | Closed. 92–95% efficient to 32 cores. Axis 2 is #297. |
| #179, sample-count prediction | Closed. `d^(2R_F+R_P)` confirmed at 729 and 6 561; 17.96x fewer samples on `rf2-rp2`. |
| #244, the 4-byte vectorization loss | Closed by #291. It was the `RUSTFLAGS` trap, not a codegen cliff. **Every agent in M25 is instructed not to set `RUSTFLAGS`**, because setting it to anything replaces `target.*.rustflags` and silently drops `-C target-cpu=x86-64-v3`. |
| M24's six-round witness | `poseidon31-cico-t16-rf2-rp4`, verified through the permutation. 59.71 min on 32 workers, 56 987 MB peak RSS. |

### 4.3 Already tracked and suitable for M25 as written

#257, #258, #259, #260, #261, #262, #263, #264, #265, #266 (the H-series spine); #237, #243, #283,
#284, #285, #286, #287, #288, #289, #290; #202; #224 as related research. All relabelled `M25` and
boarded. None needed rescoping.

### 4.4 Work requiring a new issue

Seven created, each because the existing tracker had no home for it:

| issue | why it is new |
|---|---|
| **#292** | the M25 parent. |
| **#293** | Scoreboard A. #257 is the protocol *document* and #258 the runner *trait*; neither is the durable board. It must be a **second** board: overloading `RunRecord` with a `library` field would make `best()` rank msolve against Zeebra as two formulations of one run, and `verified_somehow` meaningless. |
| **#294** | Scoreboard C. M24 §10.1's predicted-vs-observed table was the most useful thing in that report and exists only as prose inside one document, so the next milestone cannot check its own predictions against it. |
| **#295** | `runs/*.json` filenames omit the slice seed, so two slices of one row collide. Found while mapping #288. It has not corrupted anything only because the formulation strings used so far happen to encode the seed. |
| **#296** | the off-domain validation is counted in **two** stages, so the recorded row total is inflated. Found while mapping #289. M24 §7.8's 59.71 min includes it. |
| **#297** | axis 2 of #180, which #180 closed without opening. |
| **#299** | the M25 integration issue. |

### 4.5 Deferred, with the reason

#267–#273 (H11–H17, the implementation-opportunity series) are deliberately **conditional**: they are
reprioritized by #263's measurements and not before. #268–#272 in particular are the ones most likely
to be mis-prioritized by the obsolete elimination figure. #167, #149, #168, #169, #193, #194, #164,
#163 remain future foundational work; §11 is their register.

### 4.6 Existing research whose priority should be revised

| issue | revision | because |
|---|---|---|
| **#269 (H13)** | **down** from its implied position | Its title cites "the 65–88% stage". Elimination is 7–22% (§1.1). The claim must be corrected before the issue is used to justify kernel work. |
| **#268 (H12)** | **hold for #263** | "Measure the gap the profile allows" — the profile it refers to must be the current one. |
| **#243** | **up to the top of M25-C** | M24 §10.4 lists it first, and it gates two separate frontier attempts. It had no board row at all (§4.1). |
| **#224** | **down** | §8.5's three-measurement no-go stands. Downgraded to "comment with new evidence", not "implement". |
| **#287** | **derivation only** | M24 negative result #1 means round reduction cannot rescue `2^31` families, which makes #287 the only live direction — and exactly the kind of issue that invites building before deriving. |

### 4.7 Shared code areas that make concurrent implementation unsafe

`CLAUDE.md` §1 is explicit that `Agent(..., isolation: "worktree")` is not a reliable guarantee for
concurrent writers, so M25 gives every agent a **real `git worktree` on its own branch**. The
contention magnets, and the assignment that resolves them:

| area | contending issues | owner |
|---|---|---|
| `src/grobner/research/challenge.rs` | #283/#286 add registry rows; #261/#293 want Katsura and Cyclic registered | **#283/#286 only.** The competitive board gets its own identity type rather than sharing the challenge registry. |
| `examples/scoreboard.rs` | #288, #290, #295 (records) and #284 (time budget) | **#288/#290/#295.** #284 is split: its *library* half (the cooperative check and the new error variant) is separate from its *harness* half (the wiring), and the library half lands first. |
| `src/grobner/research/resultant.rs` | #285, #289, #296 and — apparently — #243 | **#285/#289/#296 only.** #243 needs **no** change here: fixing `Mul` fixes `cico_bivariate`'s `power` closure for free, because that closure is already `result = &result * p`. |
| `src/poly/multivariate/**` | #243 and #164 | **#243 only.** #164 is explicitly not implemented here — see §8.1. |
| `src/grobner/f4/**` | #237, #284 | one owner for both. |
| `README.md` `### Status` | everyone | the integration owner. Every agent rebases before touching it; it is this repository's most frequent conflict. |

---

## 5. Workstreams

### 5.1 M25-0 — measurement integrity and common infrastructure

**Required.** #257, #258, #288, #290, #293, #294, #295, #296. **Conditional:** #261 (as far as the
corpus reaches), #284.

The runner contract (#258) is on the critical path: the msolve and Groebner.jl adapters are blocked
on it and must be buildable **from the contract alone**. It is therefore delivered and frozen before
the rest of M25-0 finishes.

Two facts shape the contract. First, the precedent already exists —
`src/grobner/differential/singular.rs` has `OracleError` (`:50`) with nine variants that already
discriminate unavailable / timeout / unsupported-field / self-inconsistent, `OracleQuery` (`:124`)
where **text is the interface**, a one-method `Oracle` trait (`:150`), a `version()` probe (`:221`),
output to a file rather than a pipe (`:385-387`), and the knowledge that **Singular exits 0 on
error** so the exit status is useless (`:478`). The contract extends that shape; it does not invent a
new one. Second, that oracle carries **no timing and no memory**, which is why #258 needs a sibling
type rather than a widened trait.

Measuring an external process's peak RSS is not `VmHWM` of self. The contract must get child-process
semantics right once so every adapter inherits it — and this repository has a recorded **7 000x**
error from reading the wrong pid (`f4-resource-scaling.md` §2: a 14 GB run reported as 2 MB, because
`timeout` forks and `taskset` execs).

### 5.2 M25-A — competitive baseline

**Required:** #259, #260, #263, #293. **Conditional:** #262, #264, #265, #266 (source studies in
parallel during the M25-0 gate).

Only **Singular 4.4.1** was installed on this machine. msolve, Julia/Groebner.jl and Sagebrush are
provisioned from source into a user prefix — there is **no sudo here**, so GMP, MPFR and FLINT are
built from source before msolve is. That provisioning is itself a deliverable
(`tools/external/provision.sh`), because a comparison nobody can reproduce is not a comparison.

Per-tool facts that decide whether a row is legitimate at all: msolve's supported prime-field range
(narrower than Zeebra's), each tool's degrevlex syntax **and variable-order convention** — a wrong
variable order silently produces an incomparable basis, which is the single most dangerous failure
mode in this workstream — and, for Sagebrush, whether its experimental maturity permits treating its
timings as authoritative at all.

### 5.3 M25-B — Anemoi frontier and FGLM attribution

**Required:** #283. **Conditional on its own gate:** #286. **Related:** #224.

#283's design is what makes it decisive: run the same `α = 3`, `ℓ = 1` ladder at **65537** and
**2^32 − 209** as well as 2^64 − 353, and compare the **within-implementation** conversion/basis
ratio against the published one at each characteristic. A 17-bit and a 32-bit prime fit any system's
fast path, so **if the gap persists at small characteristic, field arithmetic cannot explain it.**
Comparing within-implementation ratios rather than raw wall clocks is the whole point; a raw ratio
across two hardware generations is not evidence about an algorithm.

#286's gate is memory, and the arithmetic is already known: `FglmOptions::default()`'s four budgets
(`max_quotient_dimension` 4 096, `max_operator_entries` 20 M, `max_span_entries` 20 M,
`max_span_bytes` 320 MB) are checked from `D` **before any allocation**. `N = 5` at `D = 3 125` only
just fits — 19 534 375 span+accepted cells against a 20 M cap. `N = 6` at `D = 15 625` fails all
four: ~488 M cells ≈ 3.91 GB of dense blocks plus ~265 M operator entries ≈ 4.2 GB, so **≈8 GB**
total. That is inside the standing ceiling, but the order is fixed: measure `N = 5`'s actual
footprint, extrapolate from **measured** storage growth, state a wall budget and an RSS ceiling,
record the go/no-go, and only then run.

### 5.4 M25-C — foundational polynomial and resultant optimization

**Required:** #243, #237, #289, #296. **Conditional:** #285.

#243's mechanism is fully understood and the fix is not speculative: `Mul`
(`sparse_multivariate_polynomial_arithmetic.rs:46-59`) pushes every pairwise product into one `Vec`
with **no `with_capacity`** and only then calls `SparseMultiPoly::new`, whose body is *already* a
monomial-keyed hash accumulate with a drop-on-cancel `retain`. Three variants are measured — direct
accumulation, chunked collect, and a **dense indexed triangle** for the actual workload, which is the
`(d+1)(d+2)/2` dense bivariate triangle with **zero cancellation** and therefore needs no hashing at
all. Time as well as memory, because a map insert per product may cost more than a push plus a
combine, and 3.54e9 products is where that decides.

#237 is an **attribution** issue, and the sharpest experiment is the cheap one
`f4-resource-scaling.md` §6a already identified: the uncapped rungs plateau at **4 978 MB**, *below*
the capped degree-5 figure of 14 072 MB while doing strictly more work. So 14.07 GB is not what
degree 5 costs — it is reached on the **refusal path**. Profiling capped against uncapped at the same
point is worth more than any amount of reasoning about which structure is large.

#289 exists because the cubic law rests on **two** points, and a third already contradicts it: order
18 at 8.5 µs, order 162 at 2.868 ms, order 1 458 at ~2.70 s core-time. 18→162 is *sub*-cubic
(exponent 2.65); 162→1 458 is *super*-cubic (3.116). Concave in log–log — fixed overhead at the
bottom, a cache transition at the top (order-162 matrix 210 kB fits L2; order-1458 matrix 17 MB does
not). A single exponent may be the wrong model, and saying so is a legitimate result. Also: **#289's
own body is internally inconsistent** — it tabulates order 13 122 at 2 294 s against a stated 3.116
fit, but 2.868 ms × 81^3.116 = 2 541 s; 2 294 s corresponds to ≈3.09.

### 5.5 M25-D — bounded high-upside algorithm research

**Conditional, each behind its own gate:** #202, #287, #297.

Each delivers a decision with its derivation. The methodological warning is local and recent:
[`elimination-beyond-grobner.md`](research/elimination-beyond-grobner.md) lines 9-25 record **two
conclusions already retracted**, both from reasoning off complexity formulas rather than
implementations. A complexity-formula argument is labelled a hypothesis here, not a result.

---

## 6. Agent ownership boundaries

One writer per checkout, each on a real `git worktree` and its own branch.

| agent | worktree | branch | issues | primary files |
|---|---|---|---|---|
| TOOLCHAIN | `zb-m25-ext` | `build/m25-external-toolchain` | #259 (prereq) | `tools/external/**`, `docs/research/external-comparands.md` |
| RUNNER | `zb-m25-runner` | `feat/m25-external-runner` | #257 #258 #288 #290 #293 #295, #284 harness | `scoreboard.rs`, `record.rs`, `examples/scoreboard.rs`, `differential/**`, new runner module |
| POLY | `zb-m25-poly` | `perf/243-collecting-multiply` | #243 | `src/poly/multivariate/**`, `benches/sparse_polynomial.rs` |
| ANEMOI | `zb-m25-anemoi` | `research/m25-anemoi-attribution` | #283 #286 #224 | `anemoi.rs`, `anemoi_cico.rs`, `challenge.rs`, `examples/anemoi_ladder.rs` |
| F4MEM | `zb-m25-f4mem` | `perf/237-f4-memory-attribution` | #237, #284 library | `src/grobner/f4/**`, `pairs.rs`, `buchberger.rs` |
| RESULTANT | `zb-m25-resultant` | `perf/m25-resultant-models` | #289 #285 #296 | `research/resultant.rs`, `examples/resultant_cico.rs` |
| RESEARCH | `zb-m25-research` | `research/m25-algorithm-gates` | #202 #287 #297 | new `docs/research/*.md` only |
| integration | `lucky-prancing-shamir` | — | #292 #294 #299 | this document, `README.md`, scoreboard regeneration |

Research documentation is written independently and integrated later. No agent edits this document.

---

## 7. Experimental baselines

### 7.1 Hardware, recorded because every figure depends on it

AMD Ryzen Threadripper PRO 5995WX, 64 cores / 128 threads, 1 socket, L3 256 MiB across 8 instances,
503 GB RAM. Fedora, Linux 7.2.10, `gcc 16.2.1`. Measured figures record `ZEEBRA_MACHINE` and
`ZEEBRA_AFFINITY`; the published Anemoi comparands are from a Xeon E5-2630 v3 @ 2.40 GHz with Magma
V2.26-2, and **that difference is why §5.3 compares ratios rather than wall clocks**.

### 7.2 Protocol

Every recorded figure runs under `tools/benchlock.sh <owner-tag> <command>`, whose overlapping
`START..END` windows are the machine-checkable proof that two figures were *not* taken under the
protocol. Callers add, themselves: a per-worktree `CARGO_TARGET_DIR`, `RUSTC_WRAPPER=""`, a private
scratch directory, `taskset` pinning, and `timeout --signal=INT --kill-after=60s`.

**`RUSTFLAGS` must not be set.** Setting it to *anything* — including `-D warnings` or the empty
string — replaces `target.*.rustflags` rather than adding to it, and silently drops
`-C target-cpu=x86-64-v3`. That cost #185 a crossover constant and #231 a whole set of figures, and
`MILESTONE-SIMD-PARALLELISM.md` §3.1 had already recorded it costing a near-miss CI regression.
Verify with `cargo build -v 2>&1 | grep target-cpu` before taking any figure.

### 7.3 The corpus

Katsura, Cyclic roots, random and planted MQ, Fukuoka MQ Type III, representative Poseidon, Anemoi,
zero-dimensional FGLM workloads, and selected characteristic-two workloads. A ladder with easy,
intermediate and genuinely challenging rungs is preferred to large instances everywhere. Two hazards
are resolved in writing before any timing is published:

- **Katsura indexing.** `katsura::<N, F>()` (`benchmark_systems.rs:66`) is **N = n + 1 variables**.
  External tools differ. The translation is stated per tool.
- **Cyclic, affine versus homogenized.** And separately: **cyclic-4 is positive-dimensional**
  (`benchmark_systems.rs:10-15`), so it is not a zero-dimensional-solving row at all.

The Fukuoka MQ instances are **"All Rights Reserved", no stated licence** — fetched by
`tools/fetch-mq-challenge.sh` and never redistributed.

### 7.4 Stage-level attribution, and what it may be called

For each significant gap, attribution to one of: field arithmetic, polynomial representation,
symbolic preprocessing, critical-pair processing, matrix construction, linear algebra,
interreduction, FGLM/operator construction, order conversion, root finding or solution extraction.

**Where the external implementation does not expose comparable stages, the attribution is labelled a
hypothesis, not a measurement.** This is also where #269's obsolete 65–88% claim is corrected, and
where H12–H17 are reordered — by absolute computational cost, measured gap, expected benefit,
implementation difficulty, effect on maximum solvable size, and applicability to cryptanalytic
systems.

### 7.5 Provenance

[`external-provenance-policy.md`](research/external-provenance-policy.md) governs. The operative
conclusions: running a GPL binary as a separate process is fine; copying its code into Zeebra's MIT
core is not. **Sagebrush** (`sagemathinc/sagebrush`, MIT OR Apache-2.0) is the one comparand where
reuse is permitted — and Groebner.jl is a worked example of what a licence-compliant adaptation looks
like, since it names msolve as upstream and enumerates what it took.

---

## 8. Research gates

A gate is a decision criterion written **before** its measurement. A failed gate is a completed
research decision, and the milestone continues with the other workstreams rather than blocking.

### 8.1 Gate M25-0 — the contract freezes before the adapters

#258's trait must be reviewed and stable before #259 or #260 implement against it, and the acceptance
bar is that two independent agents can build the msolve and Groebner.jl adapters **from the contract
alone**. Source studies (#264, #265, #266) proceed in parallel during this gate.

Also fixed at this gate, so that neither is rediscovered: **#164 is not implemented in M25**, and the
reason is that it compounds with #243 — a collecting multiply does a hash lookup per *product*
(3.54e9 of them on the target workload) rather than per output term, so whichever of the two lands
second gets measured on a workload the other made hash-bound. The measurement that would decide #164
is left stated and untaken.

### 8.2 Gate M25-A — the report precedes the rewrites

#263 produces the initial competitive baseline **before** any major general-purpose implementation
rewrite is launched. In particular, F4 elimination is not prioritized on the strength of M16's
pre-optimization profile (§1.1).

### 8.3 Gate M25-B — Anemoi `N = 6`

In order, each step recorded: measure `N = 5`'s operator and conversion footprint; identify every
major retained structure; extrapolate `N = 6` from **measured** storage growth, not from the `D³`
*time* model; state a wall budget and an RSS ceiling; record the go/no-go against a criterion written
first. Then, and only then: register `N = 6` deliberately with the frozen identities preserved,
verify the quotient dimension is **15 625**, attempt FCICO, attempt PCICO only if the measured FCICO
cost supports it, and validate any witness **through the permutation**.

**A completed `N = 6` conversion is not evidence that Zeebra outperforms a maintained Magma
installation.** No comparable measurement exists. It is a produced figure.

### 8.4 Gate M25-C — the next Poseidon rung

Decided from the measured cost model, not from round count. Before any attempt: predict construction
time and memory, predict determinant count and cost, account for verification, state a maximum wall
time and RSS ceiling, record whether the computation is bounded and realistic, and decide go/no-go
first. An improved six-round run is a valid result even if no harder instance is reached. **The next
rung is not launched because more memory became available.**

#### 8.4.1 The decision, taken against #289's fit: `rf4-rp2` is costed, bounded, and **not
authorized**

The gate ran as written, and this subsection is its output. Everything below supersedes the
two-point extrapolation this section originally carried, which put `rf4-rp2` at ≈1.4 h on the
strength of a 2.70 s core-time; #289's calibration measures that figure at **3.148 s**.

`rf4-rp2` is the right candidate. It is a registered faithful reduction whose best recorded result is
`stopped: max_live_nonzeros at degree 4`, so a witness there would be a frontier extension rather
than a cheaper version of something already done; and at six rounds it shares `rf2-rp4`'s Sylvester
order 1 458 and resultant degree 729, so the only thing that grows is the sample count — 6 562 to
**59 050**, exactly `3^(2·4+2) + 1`.

Costed, each line labelled:

| stage | cost | basis |
|---|---:|---|
| symbolic build | **48.4 min**, **310.4 MiB** peak RSS | measured, §6.12 — **was 53.09 GiB before #243**; identical for every six-round row |
| 59 050 order-1458 determinants, 32 workers | **1.79 h** | model (`RowCost::of`, 10% conservative by construction) |
| the same, from measured core-times alone | **1.61 h** | 59 050 × 3.148 s / 32, measured per-determinant |
| off-domain validation, 8 points | **< 1%** of the row | measured, now on the parallel path (#285) |
| root finding at degree 59 049 | **not estimated** | §6.3 measured 70x for a 9x degree step (729 → 6 561); extrapolating that again is not defensible |
| **total** | **≈ 2.6 h**, **≈ 0.3 GB** | build + determinants, root finding unpriced |

**Against the §9 ceiling of ~2 h wall and ~64 GB peak RSS, this fails on time — and on time alone.**

That last clause is a correction to this section's own first draft, which also called the row "close
on memory, 57 GB against a 64 GB ceiling, 89% of it". **#243 landed between the costing and this
sentence and made the build's peak 175–179x smaller**, so the memory term is now 0.5% of the ceiling
rather than 89% of it. The arithmetic that refuses the row did not change; the reason it is refused
narrowed from two resources to one.

Which makes the point §13.7 draws from this harder to miss: **memory was never what blocked this
row.** It only looked like a binding constraint while it was the quantity that had been mis-estimated
by 838x, and the moment it was measured and then fixed, the constraint that remained was the one
nobody had been arguing about.

So the decision is **no-go pending explicit owner authorization**, and that is a completed research
decision rather than an unfinished attempt. Three things follow from recording it this way:

1. **The run is bounded and realistic, which is a different statement from authorized.** `rf4-rp2`
   is not out of reach — it is roughly a workday's third of a machine, and nothing in the cost model
   is extrapolated beyond the order it was fitted at. What it is not is inside a ceiling chosen for
   unattended work. An owner who wants it can authorize ~3 h and 64 GB and expect it to land.
2. **#243 changes the memory, not the time.** A collecting multiply bounds the build's 57 GB by its
   output, which removes the memory half of this gate almost entirely — but the build's 48.4 min is
   arithmetic the collecting multiply still has to do, so the total stays ≈2.6 h. Memory was never
   what blocked this row; it only looked like the binding constraint because it was the number that
   had been wrong by 838x.
3. **`rf6-rp0` is not close.** 531 442 samples is **16.15 h** on 32 workers by the model, **14.5 h**
   from measured core-times. Eight rounds is worse by three orders: `rf4-rp4` at order 13 122 is
   **490.5 d** on 32 workers, and that figure is extrapolated three times past the largest order
   measured. Neither is a candidate for any ceiling, and neither becomes one through a constant
   factor — which is what makes #297's axes 3–5 the only directions that matter, and #297's axis 1
   close to zero-sum against a sweep already 92–95% efficient.

**What would change this decision.** Not more memory, and not a faster determinant by a constant:
`rf4-rp2` needs a factor of ~1.3 to fit the existing ceiling, which a 10%-conservative model and an
unpriced root-finding term could swallow entirely. The honest routes are an owner authorization at
~3 h, or an asymptotic improvement from #297.

Two figures in the calibration are **unexplained and bound every ratio quoted against the older
records**, and they are the reason this decision is stated with its basis rather than as a number.
Determinant measurements taken now are **~1.2x slower** than the same measurements on record —
same registered row, same code path, same lock, months and a commit range apart (#318). And the
width penalty measures **31–44%** at 32 workers where §6.6 recorded **4–9%** (#319). Both were
treated as findings rather than repaired. A factor computed between a figure from §6.5 and a figure
taken today carries a ~20% systematic that is a property of neither implementation.

### 8.5 Gate M25-D — each research item separately

#202: validate the system at the published witnesses first — if it does not vanish there, nothing
downstream means anything. #287: derive before building; if the cost is invariant or worse, the
negative result is the deliverable. #297: a prototype only where the analysis identifies a credible
advantage over the **parallel** baseline, and a new major subsystem becomes a future issue rather
than being absorbed.

---

## 9. Resource budgets

- Ordinary benchmarks: short, modest.
- Longer experiments require a documented cost estimate before launch.
- **Any run projected to exceed ~2 h wall or ~64 GB peak RSS requires explicit owner authorization.**
  Lower when shared workstation activity or available memory warrants it.
- Never an unbounded computation because a predictor suggests it might finish.
- An external watchdog even where an internal time budget exists; a process-level memory supervisor
  for runs with material allocation risk.
- A run whose actual growth violates its approved ceiling is terminated.

Authorized at the time of writing: #243's `--build-only` re-measurement (~50 min; 57 GB before the
fix, expected far less after); #237's 14 GB rungs; #289's determinant sweep through order 4 374
(~153 MB per matrix); #286 at its measured ≈8 GB projection. **Not** authorized without a fresh
decision: `rf4-rp2`, `rf6-rp0`, any eight-round row, and PCICO `N = 6` before FCICO `N = 6` is
measured.

Resolved during the milestone, with the arithmetic in §8.4.1: **`rf4-rp2` remains unauthorized** at
≈2.6 h against the ~2 h ceiling, and it is the *time* that fails, not the memory — a result that
only became visible once #289 measured the per-determinant cost at 3.148 s rather than the 2.70 s on
record. `rf6-rp0` (16.15 h) and every eight-round row (≥490 d) are not near any ceiling.

---

## 10. Acceptance criteria

**M25-0.** #258's trait frozen, with `SingularOracle` refactored onto it and the existing
differential test unchanged and passing; a missing tool skipped-and-reported with a test; no new
required dependency in the core crate. #257's protocol records every §5.1 field with a stated
measurement method, forbids conflating the six tasks, and distinguishes "could not represent the
input" from "slower". #288: an F4 row's estimated/measured RSS ratio is recoverable from the record
alone, with one absent-encoding across both record types and a round-trip test on each. #290: the
append-only assumption stated next to the tie-break, with a test that fails if violated, and the
stale `solved.json` contract string fixed. #293 and #294 regenerable from retained records, with
historical rows never edited. #295 and #296 each with a test that fails against today's code.

**M25-A.** Each comparand either runnable with a pinned version and a passing smoke test, or an
individually documented blocker. ≥6 families normalized with reduced-basis digests agreeing or the
disagreement explained. #263 ranks optimization opportunities on the six axes of §7.4 and corrects
#269's claim.

**M25-B.** Ratio-of-ratios at all three characteristics, with an explicit verdict naming which
candidate the data supports **and which it rules out**. Quotient dimension verified at every new row;
the freeze test showing additions and never redefinitions. #286's gate recorded before its run, and
its outcome recorded whatever it is.

**M25-C.** #243: temporary memory bounded by accumulated distinct terms plus a bounded working chunk,
with the small-polynomial regression reported honestly and the time/memory trade stated explicitly.
#237: the ~13.5 GB attributed to named sites with the method stated, a recorded decision on the
budget's name and scope, and `max_live_bytes`'s doc comment saying exactly what it bounds. #289: an
exponent fitted over ≥4 orders with residuals and applicability limits, and `RowCost::of` making a
deliberate choice that does not replace a conservative bound with an aggressive extrapolation. #285:
identical verdicts and identical resultants at concurrency 1, 8 and 32, with the off-domain share
under 1% at six rounds and the probabilistic check never described as a proof.

**M25-D.** Three go/no-go reports, each judged against a criterion stated before its numbers, with
every figure labelled measured / fitted / extrapolated.

**Correctness, throughout.** Property tests where appropriate; independent reference calculations;
differential tests against established implementations where available; regression tests for the
affected workload; benchmarks against the previous implementation; edge cases and multiple field
characteristics. A performance change must not weaken basis completeness, field arithmetic
correctness, error handling, or resource-stop semantics. A cryptanalytic witness is verified
**through the primitive**, not only through the polynomial system the solver generated.

---

## 11. Future-work register

Maintained here and reconciled against the tracker by #299. Readiness is one of: **ready** for
independent implementation; **research needed**; **blocked**; **deferred by measurement**; **not
recommended unless new evidence emerges**.

| issue | topic | priority | potential benefit | readiness | dependency | milestone |
|---|---|---|---|---|---|---|
| #268 | compact monomial / polynomial representations | Low | memory and cache behaviour across F4 | deferred by measurement | #263 | M26+ |
| #269 | F4 elimination kernels | Low | 7–22% of runtime, **not** 65–88% | not recommended unless new evidence | #263, and a corrected premise | M26+ |
| #270 | field-width-specialized arithmetic | Low | broad, unquantified | research needed | #263 | M26+ |
| #271 | modular composition and univariate factoring | Low | root finding and eliminant extraction | research needed | #193, #194 | M26+ |
| #272 | GF(2)/GF(2^e) bit-packed linear algebra | Low | the characteristic-two stack is untested at scale | research needed | #218, #219 | M26+ |
| #273 | adaptive solving-strategy selection | Low | extends the existing planner | deferred by measurement | #263 | M26+ |
| #164 | monomial-keyed hasher | Medium | compounds with #243 — see §8.1 | ready, but **measure after #243** | #243 | M26 |
| #167 | parallel FGLM border reduction | Medium | the one F4-shaped independent batch | ready | — | M26 |
| #149 | 8-lane AVX2 elimination kernel | High (board) | decision pending, not implementation | ready | — | M26 |
| #168, #169 | sparse RREF back-substitution; matrix multiplication column indexing | Low | both are measured algorithmic defects | ready | — | M26 |
| #193, #194 | fast division by Newton inversion; half-GCD | — | blocked on each other and the FFT crossover | blocked | #193 before #194 | M26+ |
| #224 | sparse-FGLM and order-conversion alternatives | Medium | large, but a recorded no-go | not recommended unless new evidence | overturning one of §8.5's three measurements | M26+ |
| #218–#221 | Boolean solving readiness, SAT4CryptoBench, SAT as backend, LowMC | Medium | the first same-machine external baseline outside Gröbner | research needed | #218 before #219 | M26 |
| #195–#196, #205–#207 | MinRank and rank-based cryptanalysis; Boolean cryptanalysis | Medium | new challenge families | research needed | — | M26+ |
| #197–#199 | Fukuoka MQ I–V; HFE Challenge 1; classical collections | Medium | published external timings exist | ready | #261 | M26 |
| #201, #203, #204 | Anemoi ACICO; Feistel-MiMC and Rescue-Prime; Poseidon zero-test | Medium | more registered rows | research needed | ℓ>1 blocked by a u64-only primitive-root search | M26+ |
| #69, #86–#89, #225 | GPU suitability, sparse matvec, out-of-core, hardware cost | Low | unquantified | not recommended unless new evidence | a named kernel, workload, predicted benefit and benchmark | M27+ |
| #200 | prize-status ledger | Medium | one presently claimable award | owner action | — | — |

**Independently parallelizable, and not an M25 completion dependency:** #264/#265/#266 source studies;
#218/#219 Boolean importers; #193/#194 univariate work (independent files); #205–#207 MinRank
analysis; #199 classical-collection provenance.

---

## 12. Reproducing

External comparands:

```sh
tools/external/provision.sh          # pinned GMP, MPFR, FLINT, msolve, Julia + Groebner.jl, Sagebrush
. tools/external/env.sh              # PATH, LD_LIBRARY_PATH, JULIA_DEPOT_PATH
tools/external/smoke/smoke.sh        # one shared system through every available tool
```

Measured figures, under the protocol of §7.2:

```sh
# the six-round symbolic build, #243's before/after
ZEEBRA_MACHINE="$(hostname)" ZEEBRA_AFFINITY=40 \
tools/benchlock.sh m25 env CARGO_TARGET_DIR="$PWD/target" RUSTC_WRAPPER="" \
  timeout --signal=INT --kill-after=60s 7200 \
  taskset --cpu-list 40 ./target/release/examples/resultant_cico \
    --row poseidon31-cico-t16-rf2-rp4 --build-only

# the Anemoi ladder, one registered row
ZEEBRA_MACHINE="$(hostname)" ZEEBRA_AFFINITY=0-7 \
tools/benchlock.sh m25 env CARGO_TARGET_DIR="$PWD/target" RUSTC_WRAPPER="" \
  timeout --signal=INT --kill-after=60s 1200 \
  taskset --cpu-list 0-7 cargo run --release --example anemoi_ladder row anemoi64-cico-n5-fcico

# the F4 live-entry ladder, #237. Background the binary directly: taskset execs and keeps
# the pid, timeout forks and does not. Reading timeout's pid once reported 2 MB for a 14 GB run.
tools/fetch-mq-challenge.sh
cargo build --release --example scoreboard
ZEEBRA_MAX_ENTRIES=20000000 ZEEBRA_AFFINITY=0-7 \
  taskset --cpu-list 0-7 target/release/examples/scoreboard mq fukuoka-mq-III-n20-seed0 --seeds 1 &
grep VmHWM /proc/$!/status
```

Development checks, matching CI:

```sh
cargo fmt --all --check
cargo clippy --all-targets --all-features -- -D warnings
cargo nextest run
cargo test --doc
shellcheck -S warning scripts/agent/*.sh scripts/agent/test/*.sh
bash scripts/agent/test/zb-claim-test.sh
```

---

## 13. Final measurements and conclusions

Two items are still running at the time of writing and are marked as such: Anemoi `N = 6` (§13.2)
and M25-D's hybrid and structured-Sylvester derivations (§13.5). Everything else is final.

### 13.1 Competitive position

Four engines are provisioned on this machine, pinned, and reachable through one contract:

| engine | version | basis ceiling | eliminant ceiling | notes |
|---|---|---|---|---|
| msolve | 0.11.0 | `p < 2^31` (`iofiles.c:564`) | **`p < 1515531529`** (`linalg-fglm.c:38`) | two ceilings, not one |
| Groebner.jl | 0.10.11 / Julia 1.11.7 | `p < typemax(u64)` | — (no FGLM in 0.10.11) | measured at 2^64−353 |
| Sagebrush | `86d9f1c7` | `p < 2^62` (`lib.rs:1552`) | via `SB_FGLM` | **timings not authoritative** — §13.6 |
| Singular | 4.4.1 (44105) | `p < 2^31` | `fglm` | pre-existing |

**Zeebra loses in two places, and they are different places.** That matters more than either
figure: one explanation is unlikely to cover both, and the report does not offer one.

**Loss 1 — order conversion, ~30x against msolve.** On
Anemoi `N = 5` FGLM at `p = 65537`, same machine, byte-identical generators: **~21–35x end to end**
and **~30x on the conversion stage** against msolve. The ~280x per-core figure is defensible **for
the conversion stage only** — that stage is single-threaded at ~1 CPU-second per wall second
observed, while the basis stage had eight cores. Quoting per-core for the whole solve would
overstate it.

**Loss 2 — the basis stage, 4.11x against Singular**, on `mq-random-10`: 29 963 ms against 7 291 ms,
with conversion 3.57x behind as well. Zeebra against Singular 4.4.1 on all 19 corpus rungs × both
tasks, one machine, `taskset -c 0-7`, one worker, under `benchlock`. Every completed row agreed on
the quotient dimension — 9, 25, 57, 64, 81, 156, 354, 1024, 16 384 — which is what licenses the
timings at all.

Two things make it more consequential than its size:

- **It is in F4, not conversion.** On Anemoi the conversion was 75% of the solve; here conversion is
  nearly free (30.6 s against a 30.0 s basis) and the **whole** gap is in the basis. §6's gap map had
  the basis stage as "not yet measured"; it now has rank 2 at ~22.7 s absolute.
- **Random MQ is the corpus family closest in shape to a cryptanalytic system** — dense, square,
  quadratic, no exploitable structure. Loss 1 was on a structured CICO row at a 17-bit prime; this is
  a deficit on **the problems Zeebra exists for**.

**A measurement-method result that disqualifies four of Zeebra's apparent wins, and it is the most
reusable thing in this section. Singular's startup floor is 36.0 ms, measured.** Five rows cluster at
36.01, 36.04, 36.05, 36.07 and 36.08 ms across instances whose quotient dimensions differ by a factor
of **2 000**. A figure that constant across that range is not a computation. The rule:

> Where a comparand's wall is within ~2x of its own floor, the row is **not an engine comparison in
> either direction**.

That disqualifies apparent Zeebra wins of 2.2x, 3.4x, 8.4x and **450x**. The 450x is the sharpest
warning this milestone produced about reading a ratio without checking its denominator's floor — and
it would have been a very attractive number to publish.

**The rule is enforced in code, not in prose, and it needed no new field.** The floor is *derived
from the board's own rows*: `CompetitiveBoard::startup_floor(library)` is the shortest wall that
library recorded, requiring four answered rows first, since one fast row is a fast row and not a
floor. `Speedup` carries `baseline_floor_multiple`; `is_engine_comparison()` is false below **2.0**,
because at that point half the comparand's wall is the cost of starting it and the other half cannot
carry a conclusion through the 20% band; and `is_publishable()` is the **conjunction** of both gates,
so a renderer cannot satisfy one and forget the other. The disqualified rows are **kept and marked**
rather than dropped — the renderer prints `NOT AN ENGINE COMPARISON: baseline is 1.0x its startup
floor` — because the board is the artifact that stops someone recomputing the 450x from the raw
numbers next year. A test reproduces the measured shape exactly: four Singular rows at 36.01–36.08 ms
plus `mq-random-10` at 7 290 ms, four ratios disqualified, the real one surviving at 200x its floor,
and all ten rows still on the board.

**Where Zeebra cannot be compared, which is three results rather than three gaps.**

1. **Both solution tasks have no comparand at any field size.** `OneFiniteFieldSolution` and
   `AllFiniteFieldSolutions` are empty columns for **every** engine — msolve produces a rational
   parametrization rather than finite-field points (verified at `main.c:96-97`), and the other
   three have no solver. Zeebra's end-to-end solving capability has no external baseline.
2. **The corroboration boundary has four tiers**, and it is about corroboration rather than
   representability — a distinction with different fixes. Representability needs a new tool;
   corroboration needs a second tool **at the same field and for the same task**:

   | band | engines | basis corroboration |
   |---|---|---|
   | `p < 2^31` | all four | four-way, term-for-term |
   | `2^31 ≤ p < 2^62` | Groebner.jl, Sagebrush | two-way, no third opinion |
   | `2^62 ≤ p < 2^64` | Groebner.jl only | **none** |
   | 254/255-bit | none | **none at any size** |

   Anemoi's field is 2^64−353, so it sits in the sole-engine band — and so does **Goldilocks**, which
   makes this a property of the band rather than an Anemoi peculiarity. The corpus records that case
   as `SoleComparand { tool, reason }`, distinct from `NoComparand`, because the two have different
   fixes: `licenses_timing()` is **true** for a sole comparand (one engine on one machine still gives
   a valid ratio and a checkable invariant) while `is_corroborated()` is false. `NoComparand` narrows
   to the 254/255-bit fields, and a test asserts no ladder rung uses it.

   **Corroboration is task-specific, and the table above is the _basis_ table.** Conversion is
   narrower, because Sagebrush exposes **no FGLM route at all** — a missing task, not a field
   ceiling:

   | task | `p < 2^31` | `p ≥ 2^31` |
   |---|---|---|
   | basis | four-way | two-way |
   | **conversion** | **three-way** | **sole engine** |
   | eliminant | two-way (msolve out at `2^31 − 1`) | sole engine |

   This matters more than a refinement, because **conversion is the one stage where M25 measured a
   cross-library deficit at all.** Reading a basis band as a conversion band would overstate what can
   check the very row this milestone most wants checked. The boundary is derived from the engines'
   own constants — `ceilings` re-exports each adapter's `MAX_CHARACTERISTIC` — so one source of truth
   feeds every statement, and `corroboration_for(task, p)` is the task-aware form while
   `corroboration(p)` is the documented basis shorthand. A per-family sentence is exactly how the
   first version of this got it wrong.
3. **The corpus reference field, `2^31 − 1`, is above msolve's eliminant ceiling.** So msolve is a
   basis comparand there and not an eliminant one. Asking it anyway does not fail — it **hangs**:
   the sparse-FGLM `NULL` is laundered into the genericity signal and reaches a `goto restart` loop
   with no exit (`msolve.c:649`, `:482-484`), measured at **25 353 retries and 1.37 M lines in 8 s,
   never exiting**. A hang reads as `StoppedByLimit`, which is timing-adjacent and wrong, so
   `competitive_sweep` **refuses to ask** rather than documenting the hazard.

**Correctness, which is the precondition for any of the above.** Four engines produce a term-for-term
identical basis — every coefficient, not only leading monomials — on a shared system over
GF(1073741827), corroborated by `vdim` / `quotient_basis` / parametrization degree all equal to 12.
Across the corpus, **24 rung/solver pairs agree with Zeebra term for term, every coefficient
included, and not one disagreed** — 12 oracle-bearing reference-characteristic rungs across Groebner.jl
and Sagebrush, with each rung's digest asserted frozen, plus all seven Katsura and Cyclic rungs
through msolve. Neither tool disagreed with Zeebra on any instance at any point in the milestone.

The oracle is built by **parsing the instance's own rendered text** rather than rebuilding from
generator functions, which is what makes that number mean something: the bytes parsed are the bytes
every engine is handed, so a render/parse round-trip failure in either direction surfaces as a
disagreement instead of as a silently different problem. That is the one hazard cross-engine
agreement **structurally cannot catch** — the `x1`/`x10` prefix class, where every engine agrees
because all of them were handed the same malformed text. `mq-planted-14` carrying an oracle makes
the fourteen-variable prefix case a **full basis agreement** rather than "it completed and the echo
matched", and a named assertion refuses to let that specific rung vanish into the oracle budget
while the total stays above its floor.

Six rungs have no oracle for two different reasons, and only one of them is a gap: three Poseidon and
two Anemoi carry other characteristics (KoalaBear, 2^64−353), which is correct; `mq-random-14` crossed
Zeebra's own 120 s oracle budget, which is a fact about Zeebra's F4 and is printed rather than merely
uncounted.

### 13.2 Cryptanalytic position

**Unchanged from M24 on official problems.** The hardest official problem solved remains Fukuoka MQ
III `n = 15`. No official challenge was attempted in M25, and nothing here is a prize claim.

**Faithful reductions: unchanged, and refused deliberately.** `rf4-rp2` was costed against the
calibrated model and **not authorized** — §8.4.1. At ≈2.6 h against a ~2 h ceiling it fails on
**time**, not memory, which only became visible once #289 measured the per-determinant cost at
3.148 s rather than the 2.70 s on record. `rf6-rp0` is 16.15 h and every eight-round row is ≥490 d.

**External calibration: extended from ten registered rows to thirty.** The Anemoi ladder now carries
`N = 1..5` in both models at **three characteristics** — 65537, 2^32−209, 2^64−353 — with the 29
pre-existing digests byte-identical, so the freeze test reports additions rather than redefinitions.

**Anemoi `N = 6` — the rung is reached, and not by Zeebra.** #286 was filed to learn two things: is
the published conversion wall real, and is the rung reachable. **Both are now answered yes by a
same-machine measurement**, and neither answer came from this crate:

| established | by |
|---|---|
| `D = 15 625 = 5^6` | Zeebra, all three characteristics, 36/36 rows |
| `D = 15 625` | the reference's own log — a printed number, not a formula |
| `D = 15 625` | **msolve, independently** — a third witness |
| the rung is reachable | **msolve: 340.66 s, one core, 635 MB** |

#286's premise is also corrected in the crate's favour: the `p = 65537` logs **do** publish an
`N = 6` conversion in both models (23 340 s / 11 775 s), so this is a reproduction target rather
than a produced figure.

**No Zeebra `N = 6` conversion time was obtained**, and the attempt is recorded rather than retried
into one:

- **FCICO refused in 3.8 s on `max_matrix_rows`** — "symbolic preprocessing needed more than the
  200000 rows allowed". Not memory. This is the **third** of F4's four relevant budgets discovered
  by hitting a refusal rather than by reading the struct (#322).
- **And the refusal produced an observation that outlives the fix.** The published Magma run on this
  exact row peaks at **173 808 × 189 401 — inside the 200 000 default Zeebra refused on.** So for a
  problem Magma reduces within a 173 808-row matrix, this crate's symbolic preprocessing enumerates
  more than 200 000 rows. It is **not a budget-tuning problem**: the 200 000 default is not obviously
  wrong for a library, precisely because Magma fits under it on this very row, so raising the
  constant is a workaround that leaves the difference in place.

  Two caveats travel with it and must not be dropped. **The counts are not strictly like for like** —
  Magma reports a peak *reduced* matrix and Zeebra an enumerated row set *before* reduction — so the
  honest claim is a **one-row observation, not a ratio**. And it lands on exactly what #305 bounds,
  so the figure may move; that would be #305 earning its keep rather than the observation
  evaporating. Recorded in #263's gap map as an **F4** row, independent of the FGLM deficit.
- **PCICO is recorded as _not a result_.** It reached 3 177 s of its 5 400 s budget at a flat 4.53 GB
  and was killed by **none of its guards** — see §13.6a item 7.

The authorization is recorded in `anemoi.md` §8a.5 as the **integration agent's** under §9's
approximate threshold, **not** the repository owner's, together with the note that the reproduction
category was decisive and the same cost would not have been authorized for a produce-only run.

Two build-split facts that must travel with any future comparison: `N = 6` figures are **post-#305**,
§8a.3's `N ≤ 5` column is at `eb79e05`, and the two are **not mixable for basis comparisons**. The
conversion figures are unaffected, because #305 is an F4 change.

### 13.3 Computational frontier against M24

| | M24 | M25 |
|---|---|---|
| hardest **official** problem solved | Fukuoka MQ III `n = 15` | unchanged |
| **faithful reduction**, resultant route | 6 rounds, `rf2-rp4`, verified | unchanged — `rf4-rp2` costed and **refused** on time |
| external comparand **on this machine** | none | **four engines**, pinned, one contract |
| registered Anemoi rows | 10, one prime | **30**, three primes |
| F4 peak RSS, `fukuoka-mq-III-n20-seed0` deg 5 | 13 996 MB | **1 496.5 MB** — 9.4x |
| six-round symbolic build transient | 57.0 GB for a 4.3 MB output | **bounded by the output** |
| determinant cost law | 2 points, cubic asserted | **5 orders**, 2.9953 ± 0.0285 fitted |
| off-domain validation at six rounds | 19.97 s, 3.12% of the row | **2.82 s, 0.51%** |
| scoreboards | 1 | **3** |

### 13.4 Performance improvements

**#243 — the multivariate multiply.** On the six-round build's dominant step (`p²·p`, 3 551 768 920
products, 266 815 output terms), three routes measured against the materialize-all baseline, which
was **skipped because its 56.6 GB transient is the defect**:

| route | time | live heap |
|---|---:|---:|
| monomial-keyed map | 103.39 s | 28.4 MiB |
| chunked collect | 84.85 s | 6.5 MiB |
| **dense triangle** | **11.25 s** | **7.5 MiB** |

So this is **not** the memory-win-at-a-time-cost the issue anticipated: the dense triangle is both
bounded in memory and **7.5x faster than the best alternative**, because the product is the dense
`(d+1)(d+2)/2` triangle with zero cancellation and hashing it was pure overhead. Dispatch is on the
**output bound**, not on operand density, with both failure modes recorded.

**#305 — symbolic preprocessing's monomial queue.** Deduplicating on push rather than on pop, which
is the same number of hash operations one step earlier, bounds the queue by the closure instead of by
nothing. Peak RSS **13 996 MB → 1 496.5 MB, 9.4x**; the queue from **88.4% of peak to 0.21%**. The
closure-equivalence risk was discharged by an induction written out, with per-batch row counts,
column counts and the selection-degree sequence asserted identical — the basis alone being too weak
a check, since two closures can reach the same reduced basis by different matrices.

**#285 — off-domain validation.** 8 checks at order 1 458: **19.97 s serial → 2.82 s at 8 workers**,
dropping the six-round row's validation share from 3.12% to **0.51%**. Verdicts and recovered
resultants asserted identical at concurrency 1, 8 and 32, on both the held and the falsified path.

**Stage-level attribution, and the structural finding underneath it.** Removing 88% of a peak
promotes something else, so the attribution was recomputed rather than scaled. At degree 5 the new
peak is **the basis, held twice, at 60.4%** — and that row is a floor by construction, so the true
figure is 1.0–1.5 GB of a 1 496.5 MB process. At degree 4 the binding site is instead **matrix
construction at 51.9%**, with the basis at 19.1%. The reason is structural: **the basis grows with
the whole computation and a batch's matrix grows with that batch**, so which site binds depends on
how far the computation got before it stopped. There is no single answer to "what dominates F4's
memory", and a budget that bounds one structure cannot bound the other.

### 13.5 Research findings

| item | verdict | the measurement that decided it |
|---|---|---|
| **#202 Griffin/FreeLunch** | **no-go for M25**; capability costed as #306, deferred | Fails on *worth*, not expressibility. All five published witnesses lie on **one affine line** whose `(a,b)` the paper does not publish — recovered from two `r=5` witnesses, confirmed **3/3 out of sample** at `r=6,7`. `D_I` reproduces `(6α+3)(α(2α+1))^(r−3)` at 21/441/9261. The blocker is **not** a polynomial-matrix determinant (`D_H ≤ 81`, which the existing parallel sweep already covers) but **weighted monomial orders plus normal form against a given basis** — #306. |
| **#289 determinant law** | **adopt, conservatively** | Cubic to within measurement above L2: **2.9953 ± 0.0285**, worst residual 3.7%, over orders 486 / 1 458 / 4 374. **No cache cliff** — order 4 374's 153 MB matrix exceeds L3 and still gives a local exponent of 3.045, because Crout LU is ~180 ops/byte. `RowCost::of` takes the **larger** of fitted and cubic, since 2.9953 < 3 and a model that under-predicts authorizes a run nobody costed. |
| **#268 compact representations** | **partly rehabilitated — hold for one profile** | The only H-series item that could explain an F4 gap, and loss 2 is **4.11x in F4**. Its two target stages' ceilings are 2.59x and 1.92x, the right order to span it. **First external evidence any H-series item has had** — but the ceilings come from katsura and cyclic and the losing instance is unprofiled, so it is a hypothesis with a named, cheap test. |
| **#58 Wiedemann/Krylov for FGLM** | **reopen the FGLM half** | The larger measured cross-library gap is order conversion, ~30x. #58 is the candidate and **is not in the H-series**. Its deferral was conditional on a named trigger, and a measured gap against a maintained implementation is new evidence. Reopen as *"the measured conversion gap is worth a Krylov route"* — **not** as "sparse-FGLM would be 30x faster", which does not follow. |
| **#269 F4 elimination kernels** | **deprioritize** | Elimination is **7–22%**, not M16's obsolete 65–88%. Amdahl ceiling **1.07x–1.29x**, at or inside the 20% noise band, so no kernel work there can produce a readable end-to-end result before any implementation question arises. |
| **#270 field-width specialization** | **deprioritize or re-scope** | msolve's delayed reduction is active only below `2^18`, so it is **inactive at the compared fields**; all three of its kernels use `int64_t`, so narrow kernels buy lanes rather than accumulator headroom. The gap #270 reasons from does not exist at the corpus's fields. |
| **#271 modular composition** | **settled** | Extraction's ceiling is **1.013x–1.053x** — an *infinitely fast* stage is unmeasurable on every profiled instance. Its univariate-factoring half is a separate claim this screen does not reach. |
| **#272 characteristic-two linear algebra** | **the screen cannot run, and that is the finding** | A ceiling needs a profile and there is no characteristic-two one; extrapolating from the prime-field split would be #269's error exactly. But **`GF(2)` is a prime field, so it can be profiled today** — only `GF(2^e)` is blocked on the defining-polynomial convention. One profile decides it. |
| **#273 adaptive strategy selection** | **vindicated, and bounded by the right quantity** | Selection picks a route; it does not speed a stage. Measured route spread is **70x** (planted-8's lex basis: F4 direct 0.04 ms against a 2.8 ms conversion) against the best stage ceiling anywhere of 2.59x. `fglm::shape` already ships a detector validated against Singular on 26 ideals and **deliberately unwired**. |
| **#287 hybrid / k=3 CICO** | **negative result**, on counting rather than cost | `⟨f,g⟩ ∩ F_p[x] = (0)` for `k = 3`: with two constraints and three parameters the variety is a **curve**, so there is **no univariate polynomial in the ideal** and every root-finding stage in the crate has **no input** — a structural impossibility, not a bad constant. The hybrid is capped by a verification-to-construction ratio of **7 × 10⁻⁸** (µs against 15.2 s), making its largest conceivable saving one part in 1.4 × 10⁷, so `W(b) = W(0)` for every `b`. And the per-family floor is **12.2 s against 15.2 s measured** — the `k = 1` route's last axis is worth 1.25x against a nine-order gap. The product is **not invariant across `k`; it is minimised at `k = c = 2`, where the resultant route already sits.** |
| **#297 structured Sylvester** | **build axis 4 only** (Euclidean remainder sequence); axis 5 ruled out | **1 692x measured** at order 1 458 — the Euclidean route 1.343 ms against dense LU's 2.272 s, the latter cross-checking #312's independent 2.404 s single-worker figure to **5.5%** on a different binary and core. The new evidence that reopens a 2023 rejection: scoping moved from order 18 to order 1 458, taking the operation-count gap from **48x to 3 888x** and the stage from milliseconds to 67% of an unrunnable row. Axis 5's crossover sits at **`R > 8.7`** once LU's 2.20 ns multiply-subtract is charged against the remainder sequence's 5.05 ns multiply-add, which rules out the new subsystem. |

**And axis 4 does not raise the reachable round count — that claim is withdrawn.** The "~99% of the
route is determinants" figure is a **four-round** number, from `rf2-rp2` at order 162 on one core.
At six rounds the resultant degree grows with the sample count, so root finding grows quadratically
in `S` while the determinant stage grows linearly: `rf6-rp0` is **67% determinants**, and *after*
axis 4 it is **78% root finding**. So axis 4 is 1 692x on the stage and **~3x on the row** —
`rf6-rp0`'s determinants fall from 14.5 h to ~31 s and a **5.63 h root-finding tail** then dominates.
Reaching `R = 7` needs axis 4 **and** #243 **and** a sub-quadratic root finder **and** a
sub-quadratic interpolation: four walls, three of them serial quadratic stages with known fast
algorithms the crate has not wired in. That is a better position than needing new mathematics, and
it is **not** the position the stage figure alone describes.

The Amdahl screen's **asymmetry** is why one table closes two issues and vindicates a third: **a
ceiling bounds the conceivable, not the achievable.** That is decisive where even the free case is
unmeasurable (#271), and merely permissive for #268 — whose 2.59x is an upper bound, not a forecast,
so its acceptance test is a before/after on a corpus rung rather than a number read off the table.

### 13.6 Negative results

1. **Zeebra's apparent 479x Anemoi FGLM advantage is the reference's arithmetic, not Zeebra's
   algorithm.** Zeebra's conversion/basis ratio is **flat to 12% across a 47-bit range of primes**
   while Magma's moves **7.3x**; the 507x `N = 5` wall gap collapses to **2.85x** at `p = 65537`;
   and msolve settles it at **1.81 s on one core against Zeebra's 63.7 s on eight**. Candidate (2),
   "FGLM genuinely scaling better", is **ruled out**. A negative result favourable to this crate
   needed more care, not less, and §8a.1's growth finding actually **reverses** at the control prime.
2. **#289's own premise is not reproduced.** The 3.116 exponent came of dividing a **32-worker**
   core-time at order 1 458 by a **single-worker** one at order 162. The width was the excess. At one
   width the same interval gives 2.96. The issue's extrapolation table was also internally
   inconsistent with its own stated fit.
3. **`f4-resource-scaling.md` §6a's refusal-path reading is withdrawn.** Capped and uncapped peak at
   **14 336 724 kB — identical to the kilobyte** across a 50x cap difference and a 3x runtime
   difference, so §6a's 4 978 MB uncapped figure was a measurement error. The exactness was the
   evidence: one `VecDeque` reserve reproduces to the kilobyte; scattered allocations would not.
4. **The pair heap was the top-ranked suspect for F4's memory and is 4.5 MB** — 0.03% of the peak.
   The prior estimate assumed a basis eight times larger than the 1 318 elements reached.
5. **#243 was expected to be a memory win at a possible time cost.** It is a **7.5x speedup** as
   well, because the output is a dense triangle and hashing it was overhead.
6. **Two determinant figures are unexplained and bound every ratio quoted against the older
   records.** Measurements taken now are **~1.2x slower** than the same measurements on record —
   same registered row, same code path, same lock, months apart (#318) — and the width penalty
   measures **31–44%** at 32 workers where §6.6 recorded **4–9%** (#319). Treated as findings rather
   than repaired. A factor spanning §6.5 and today carries a ~20% systematic belonging to neither
   implementation.
7. **Sagebrush agreed with everything and is still not a baseline.** Term-for-term on every family
   tried, including a 62-bit prime — but five weeks old, every crate `0.1.0`, nothing on crates.io,
   six F4 tests, and no oracle run in its own repository exercising the elimination. Reportable with
   its SHA; **never a speedup denominator**.

### 13.6a Six measurement-integrity defects, and the pattern they share

M25 found eight places where a mechanism reported confidently about something other than what the
caller meant. They are listed together because the pattern is the milestone's methodological result
and it is more transferable than any single fix.

| # | the defect | why it was invisible |
|---|---|---|
| 1 | **31 issues had no board row**, so `zb-claim.sh orient` ranked a queue that omitted them — including #243, M24's own first-named next step | `orient` exited **0** with a plausible 36-row queue. `rc=0` does not distinguish "nothing left" from "not joined". |
| 2 | **PR #303 auto-merged and closed three issues with no code on `main`** | Its pushed head became an ancestor of `main` while its real commits sat unpushed in one worktree. A green `main` and three closed issues look exactly like success. |
| 3 | **`max_live_bytes` bounded 1.3% of the peak it was read as bounding** | The budget is a real bound on a real structure. Nothing said *which* structure. |
| 4 | **F4's two memory knobs are numerically identical at the default**, and the error names the limit the caller **set** rather than the one that **bound** (#322) | `320_000_000 / 16` is exactly `20_000_000`, so raising one does nothing and the message confirms the wrong ceiling. |
| 5 | **`pgrep -f` matched a heredoc wrapper on its own script text**, returning two matches for a job that had not started and **zero** for the binary that was running (#328) | Anti-correlated, not merely imprecise. The RSS guard built on it was safe only because a 4 MB wrapper cannot cross a 16 GiB ceiling — a guard correct by accident, in the instrument §9's policy depends on. |
| 6 | **A test that returns early on an absent tool is indistinguishable from one that ran and agreed** (#333, class filed as #339) | `main` was red for ~40 minutes with every check green. #311 and #324 were each green against their own base and red only once combined: **CI tests a PR against its base, not against the merged result.** |
| 8 | **A measurement crate outside the worktree does not inherit `.cargo/config.toml`**, so it silently loses `-C target-cpu=x86-64-v3` with **nobody setting `RUSTFLAGS` at all** | A third route to the failure that has already cost this repository two sets of figures — and the first with **no trigger to avoid**, since the other two are both "someone set `RUSTFLAGS`". Building a harness outside `src/` is good practice, which is what makes it dangerous. Caught only because the corrected build changed the headline: **1 930x → 1 692x**. Both runs kept. |
| 7 | **A harness-killed run records a clean `END status=0` in `benchlock.log`**, so the lock cannot distinguish "the budget stopped it" from "something unrelated stopped it" | The Anemoi PCICO run was stopped at 3 177 s of its 5 400 s budget when the background shell that launched it was terminated, taking `benchlock`, `timeout`, `taskset` and the binary with it. The lock recorded success. Worse than the others, because it consumes an hour of a **serialized mutex** while reporting that a measurement completed — and it makes every historical `END status=0` retroactively ambiguous. Fixed with `setsid`, so the run is its own session leader. |

The common shape: **the dangerous reading is never the one that looks wrong.** Every one of the eight
produced well-formed output. Three were caught only because an agent ran something locally for an
unrelated reason, and that is not a detection strategy. The repository already applies the right
discipline in two places — `zb-claim.sh`'s three outcomes for a board read, and
`Outcome::instead_of_a_time` for a row carrying no wall time — and the lesson is that it belongs
everywhere a mechanism can be silent.

### 13.6b What the benchmark protocol actually bought

One number settles whether `tools/benchlock.sh` is worth its throughput cost, and it is small.

A stray 32-worker job ran for ~2 minutes outside the lock and overlapped an msolve `N = 6`
measurement. Clean re-take: **340.66 s** against the contaminated **353.88 s** — the neighbour cost
**3.9%**.

3.9% is the point. It is far too small to notice by inspection, far too small for any plausibility
check to catch, and comfortably inside the 20% noise band the competitive report works in. **The
correction could only have come from the lock's overlapping-window record**, which is the one
artifact that says *when* each figure was taken rather than what it was. A protocol that caught only
gross contamination would have passed this through, and the figure would have entered the record
beside a reproduction of a published Magma result.

Against that: the lock serialized nine agents, queued fourteen jobs behind one hour-long frontier
run, and cost #263 its cross-library basis-stage row — recorded as partially met for that reason.
Both halves are real. The trade was worth making, and §13.6a item 7 is the repair the log still
needed.

### 13.6c The coordination cost of nine agents, measured

Recorded because the plan's §4.7 predicted the shape and not the size, and because one instance
produced an instruction from the integration owner that was **wrong**.

- **`README.md`'s Status list conflicted on four of nine branches.** §4.7 named it as this
  repository's most frequent conflict and assigned it to the integration owner; what it did not
  anticipate is that every agent earning a measured result also earns a Status line, so the conflict
  rate scales with the number of agents doing work worth reporting.
- **"Keep both sides" is right for an additive conflict and wrong for a reworded neighbour**, and the
  integration owner gave the wrong instruction on the one branch where it mattered. `main` had
  *reworded* the #305 entry — replacing "from 13 996 MB to 1 497 MB" with "peak RSS 9.1x lower and
  its runtime 10% shorter" once the locked A/B landed — so keeping both sides would have carried a
  stale copy of that figure alongside the new bullet and **silently reverted a correction**. The
  agent diagnosed it independently and resolved it correctly: take upstream's wording, append only
  your own line. **A reverted figure passes every check**, which is what makes the frequency of the
  additive case dangerous rather than reassuring. The method that caught it — diffing the Status list
  against `origin/main`'s rather than reading it — is the one to specify next time.
- **`main` moved under one branch three times during close-out alone**, and that branch rebased four
  times. The benchmark lock queued fourteen jobs behind one hour-long frontier run and cost #263 its
  cross-library basis-stage row until the queue drained — recorded as partially met for that reason,
  which is the serialization protocol working rather than failing.
- **Two PRs were auto-closed or false-merged by GitHub** on the strength of a pushed head becoming an
  ancestor of `main`, one of them closing three issues with no code merged (§13.6a item 2).

None of this argues against the fan-out: five workstreams ran concurrently and the two most
consequential findings — the H-series being scoped before its own measurement, and the second deficit
in F4 — came from agents that would not have existed in a serial plan. But the integration overhead is
real, it scales with agent count, and two of its instances were failures that a green CI could not
see.

### 13.7 Cost-model accuracy

Now a durable artifact rather than prose: **#294's register**, 20 sourced rows, with prediction error
**derived** from the predicted and measured columns rather than authored — `history.json` stores no
error column at all, and a test injects a plausible wrong value and asserts the loaded row still
reports the arithmetic. `FigureBasis` labels every number `Measured` / `Fitted` / `Predicted` /
`Extrapolated`; `Fitted` carries its residual **and** its applicability limit, and `Extrapolated` is a
separate variant because #289's law is a 3.7%-residual fit at order 4 374 and a guess at 13 122,
where `times_past_the_evidence()` returns 3.0 — the only honest thing it can report in place of a
residual. Peak allocated and peak resident are **separate columns**, because #237 measured them
21 674 MB against 13 996 MB on one row.

M25's own predictions, scored:

| predicted | prediction | observed | attribution |
|---|---|---|---|
| #243's transient | 56.6 GB | **57.0 GB** | within 1% — the one large memory prediction in this family that held, because it was arithmetic over a measured term count |
| `rf4-rp2` total | ≈1.4 h (two-point) | **≈2.6 h** (calibrated) | the per-determinant anchor was 1.2x stale and the width penalty 4x understated. §13.6 items 6 |
| Anemoi `N = 6` footprint | 3.64 GiB dense blocks | **4.53 GB RSS** | #286's memory projection was **correct** and predicted the **wrong blocker** — F4 binds, not FGLM (#323) |
| #305's new binding site | *not predicted* | basis held twice, 60.4% | removing 88% of a peak promotes something else, and nothing had predicted what |

The sharpest entry is #323: a projection can be numerically right and operationally useless. **FGLM
checks its budgets from `D` before any allocation, so it fails in milliseconds and is cheap to
predict; F4 has no pre-flight and discovers the wall at batch 41 — so the stage that is harder to
budget for is the one that binds first.**

### 13.8 Future work

**23 issues created** (#292–#339, three already closed), all boarded with Priority on project #7.
The register in §11 is reconciled against the tracker; the additions are:

| issue | topic | readiness | milestone |
|---|---|---|---|
| #304 | the basis is held three times at interreduction — now **the** peak | ready | M26 |
| #306 | weighted monomial orders + normal form against a given basis (Griffin's gap) | research needed | M26 |
| #315, #329 | extend the Sagebrush driver; echo its generators so the adapter can check them | ready | M26 |
| #316 | a `RunFailure` variant for an environment that invalidates the measurement | ready | M26 |
| #317 | packed monomial with a cached total degree, gated on a `cmp` microbenchmark | research needed | M26 |
| #318, #319 | the ~1.2x systematic and the 31–44% width penalty | **research needed — both bound existing ratios** | M26 |
| #322, #323 | the `min()` knob trap; F4 binds at Anemoi `N = 6` | ready | M26 |
| #325, #328, #339 | claim markers orphaned by a rename; `pgrep -f`; CI tests against the base | ready | M26 |
| #330, #331 | column indices from symbolic preprocessing; a monomial divmask | research needed | M26 |
| #332, #335 | corrections to the comparand record; no measurement records its commit | ready | M26 |
| #333, #334 | the corpus-rung coverage gap; cost rows emitted by runs rather than transcribed | ready | M26 |

**Independently parallelizable, not M25 completion dependencies:** #262 (F4 matrix corpus), #218/#219
(Boolean importers — and #272 says `GF(2)` can be profiled today), #193/#194 (univariate, independent
files), #205–#207 (MinRank analysis), #199 (classical-collection provenance).

### 13.8a Scored against §10 and §16, criterion by criterion

Scored against the criteria as written before the work, including where they were not met.

**Minimum — met, 7 of 7.**

| criterion | | evidence |
|---|---|---|
| a standardized cross-library protocol | **met** | #257, `external-comparison-protocol.md`; the six-task taxonomy, each field with a stated measurement method, "cannot represent the input" distinguished from "slower" in the type system |
| working adapters for ≥3 comparators, or documented blockers | **met** | **4** — msolve 0.11.0, Groebner.jl 0.10.11, Sagebrush `86d9f1c7`, Singular 4.4.1, all on one frozen contract |
| a validated corpus of ≥6 families | **met** | #261 — six families, nineteen rungs, equivalence a **recorded field** with a `licenses_timing()` gate asserted per rung |
| a first competitive report, identical problems and hardware | **met** | #263, `competitive-baseline.md`; two measured deficits, four-way agreement, three cannot-be-compared results |
| stage-attributed priorities for subsequent optimization | **met** | the six-axis ranking plus the Amdahl screen, which closed #269/#270/#271, held #272 and vindicated #273 |
| a machine-readable record of measured RSS, separate from estimated | **met** | #288 — both populated, ratio recoverable from one record, `measured_peak_rows_in_process` labelling attributability, `RssBasis::AllocatorTracked` keeping allocated and resident apart |
| updated issues and milestone documentation | **met** | 29 issues created, all boarded with Priority; §11's register reconciled both ways |

**Strong — met, 5 of 5, with one of them narrower than the criterion's wording suggests.**

| criterion | | evidence |
|---|---|---|
| a demonstrated improvement to an important core operation, end to end | **met** | #243 — the six-round build 175–179x lower peak **and 7.5x faster**; #305 — F4's peak **9.06x** lower and **10% faster**, both under the lock with the before column reproducing the recorded ladder to 0.013% |
| a completed, resource-attributed Anemoi `N = 6` attempt | **met**, narrowly | FCICO refused in 3.8 s on a **named** budget, with the Magma row-count observation attached; `D = 15 625` witnessed three independent ways; the rung demonstrated reachable at 340.66 s by msolve. **No Zeebra conversion time was obtained**, and PCICO is recorded as *not a result* |
| an explicit explanation of the published-conversion discrepancy | **met** | #283 — candidate (2) ruled out; the ratio flat to 12% across a 47-bit prime range against Magma's 7.3x, the 507x collapsing to 2.85x, and msolve settling it at 1.81 s against 63.7 s |
| a validated, updated Poseidon resultant cost model | **met** | #289 — five orders, 2.9953 ± 0.0285, residuals published, no cache cliff, and `RowCost::of` deliberately keeping the **larger** of fitted and cubic |
| one clear recommendation on the next algorithmic investment, from new measurement | **met**, and **contested** | §13.9 — order conversion, with the contest named and **#349** as the one run that decides it |

**Stretch — not met, 0 of 4**, and the first criterion inverted:

| criterion | | |
|---|---|---|
| a same-machine performance lead over a credible established implementation | **not met — the opposite** | Two measured deficits: ~30x on conversion against msolve, 4.11x on the basis against Singular. Four apparent wins were **disqualified by our own startup-floor rule**, including a 450x |
| a verified cryptanalytic instance beyond M24's measured frontier | **not met** | `rf4-rp2` costed at ≈2.6 h against a ~2 h ceiling and **refused**. §8.4.1 |
| an improvement to a published attack surviving an equivalent comparison | **not met** | Griffin is a **no-go for M25** on worth; the capability it needs is costed as #306 |
| an algorithmic change materially raising the maximum reachable problem size | **not met**, and a claim withdrawn | #305 took 9.06x off F4's working set but the stop reason is **unchanged** — `max_live_nonzeros` at degree 5, so M24's "out of reach, not out of budget" stands. And axis 4's round-count claim was **withdrawn** in §13.5 |

**One deliverable is partially met and it was found by this scoring pass, not reported.**
`research/competitive/results/history.json` holds **zero rows**. Scoreboard A's schema, its
`Outcome::instead_of_a_time` discipline, its `speedups()` single-ratio chokepoint and its renderer
are all on `main` and tested — but the sweep's measurements live in
`docs/research/competitive-baseline.md` as prose, and the board itself was never written to. So
#293's "regenerable from the retained records" is satisfied by a board with nothing to regenerate,
which is not the same thing.

That is the state Scoreboard C was built to end for cost models, and the state M24 §10.1's table was
in before #294 gave it a home — recurring one directory away, inside the milestone that diagnosed it.
It does not change any measurement: the 4.11x, the ~30x, the four disqualified rows and the quotient
dimensions that licensed them are all recorded and reproducible. What is missing is the artifact that
would stop someone recomputing a 450x from the raw numbers next year, which is exactly the job the
board exists for. Tracked rather than asserted away.

**One §16 clause deserves naming because it was the hardest to honour.** "Do not manufacture a stretch
success by choosing an easier benchmark, changing its mathematical identity, or comparing incompatible
computational objectives." The 450x row was available, arithmetically correct, and would have read as
a stretch result. It was disqualified by a rule this milestone wrote against itself — a comparand's
wall within ~2x of its own 36.0 ms floor is not an engine comparison. That rule cost four wins and
kept none.

### 13.9 M26 recommendation

**Run one cheap measurement first, because two deficits are now measured and it decides between
them. Then: order conversion — reopen #58's FGLM half and build a Krylov route.**

**The measurement, and it should happen before anything is committed: profile `mq-random-10`'s stage
split.** Loss 2 is 4.11x in **F4** on the corpus family closest in shape to a cryptanalytic system,
and **#268 is the only H-series item that could plausibly explain an F4 gap** — its two target stages
have Amdahl ceilings of 2.59x and 1.92x, the right order to span 4.11x if both contribute. That would
be the **first external evidence any H-series item has had.** But those ceilings come from katsura
and cyclic, and the losing instance's split is **unprofiled**, so it is a hypothesis. One profile
either points #268 at a measured external gap or rules it out, and it costs a single run.

This is a change from the first draft of this section, which called conversion "the only measured
cross-library gap". It was, until the lock freed.

**Why conversion is still primary if the profile does not rescue #268**, in the order the evidence
was produced:

1. It is **the larger measured gap** — ~30x on conversion against msolve versus 4.11x on the basis
   against Singular, same machine, byte-identical generators — and conversion was **75% of the
   Anemoi solve** where the basis deficit's instance has a conversion that is nearly free.
2. It is **outside the series that was supposed to contain the next optimization.** #263's structural
   finding is that H12–H17 were scoped before any measurement existed, and the measurement says the
   largest lever is not among them. #269 and #270 are falsified on arithmetic; #271 is settled; #272
   cannot be screened; #273 is real but is a routing change rather than a speedup.
3. The Amdahl screen puts **every** stage-level candidate at a ceiling of **1.01x–2.59x**, at or near
   the 20% noise band. A 30x gap is not a stage-share problem and cannot be reached by one.
4. One measurement gates it cheaply, and it should be taken first: katsura-7's conversion is **96%
   border reduction** (§8.5) while Anemoi `N = 5` is **82.8% lex walk and dependence test** — the
   *opposite* split, and the only reason this family is a candidate at all. Confirming it on a second
   Anemoi rung decides whether the rest of the work has a target.
5. Its cost is lower than it looks: §8.5's answer 4 means a Wiedemann variant choosing a random
   linear form can reuse the existing `O(N·D)` verification **unchanged**, so it could ship certified
   rather than conjectural.

6. The published literature agrees on where the bottleneck is: eprint 2026/1905 names the
   change-of-ordering step, performed by FGLM, as the bottleneck for the Gröbner-basis attack. That
   is external corroboration of the stage, independent of Zeebra's own profile.

Stated carefully, because the inference is easy to overdraw: the three engines reach a lex basis by
**three different algorithms** — lex walk, Keller-Gehrig spin, Wiedemann scalar sequence — so the 30x
is Zeebra's conversion against msolve's on one family at one prime. It is evidence that a Krylov
route is worth building. It is **not** evidence that sparse-FGLM would be 30x faster, and
`MILESTONE-FGLM-SCALABILITY.md` §8.5's three measurements against that claim still stand unrefuted.

**And stated as contested, which it was not before.** Loss 2 is in a different subsystem, on a
different family, against a different engine, and it is the family that matters most for the
long-term objective. If the profile implicates #268's two stages, the cheaper and better-targeted
investment is **compact monomial and polynomial representations**, not a Krylov route — and #268
would then be the rare case of an H-series item surviving the screen on *external* evidence rather
than being closed by it. The honest position is that M25 measured two deficits and funded neither
blind.

**Ranked alternatives.** *Structure-exploiting algorithms* (#306 → #202) — the Griffin instance is
now pinned including the attack's input parametrization, and the capability is costed; the obstacle
is that it buys one family. *Harder resultants* (#297) — the only remaining asymptotic axis, but the
baseline is now measurably clean, so there is no implementation slack to recover and `rf4-rp2` needs
only ~1.3x while eight rounds needs three orders. *Boolean/SAT* (#218–#221) — the first same-machine
external baseline outside Gröbner, and #272 notes `GF(2)` is profilable today. *Kernel
specialization* — **not recommended**; that is what the Amdahl screen settled.

**Not recommended for M26:** GPU and out-of-core (#69, #86–#89, #225). Nothing in M25 produced the
named kernel, workload, predicted benefit and benchmark that §3 requires before that work is
scheduled, and #305 just removed 9.4x from the memory pressure that was the main argument for it.
