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
| symbolic build | **48.4 min**, **57 GB** peak RSS | measured, §6.8; identical for every six-round row |
| 59 050 order-1458 determinants, 32 workers | **1.79 h** | model (`RowCost::of`, 10% conservative by construction) |
| the same, from measured core-times alone | **1.61 h** | 59 050 × 3.148 s / 32, measured per-determinant |
| off-domain validation, 8 points | **< 1%** of the row | measured, now on the parallel path (#285) |
| root finding at degree 59 049 | **not estimated** | §6.3 measured 70x for a 9x degree step (729 → 6 561); extrapolating that again is not defensible |
| **total** | **≈ 2.6 h**, **≈ 57 GB** | build + determinants, root finding unpriced |

**Against the §9 ceiling of ~2 h wall and ~64 GB peak RSS, this fails on time.** It is close on memory
too — 57 GB against 64 GB is 89% of the ceiling, with the largest single unpriced term (root finding
at a degree nine times anything measured) sitting on the wrong side of the estimate.

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

To be written by #299 as the workstreams report. Sections reserved: competitive position;
cryptanalytic position; computational frontier against M24; performance improvements with
stage-level attribution; research findings as adopt / reject / defer; negative results; cost-model
accuracy; future work; and the M26 recommendation.
