# M30 — Signature-Based Work Avoidance and Parallel Symbolic F4

**Status:** planning, 2026-11-17. No M30 work has started and no M30 benchmark has been run.
**Predecessor:** M29 — Verified Competitive F4
([`MILESTONE-COMPETITIVE-F4.md`](MILESTONE-COMPETITIVE-F4.md), §14 integration report).
**Planning base:** `main` at `adfa6a60`.
**Measured at:** not measured here — every figure is quoted from the M29 integration report
(measured at `88bc45de`), the [M29 cost model](research/m29-baseline-cost-model.md) (`527a105e`
and the commits in its §6a/§6b), the [C1 attribution](research/m29-grobx-attribution.md)
(`7e18d089`), [#827's report](research/serial-stage-slowdown.md) and
[#223's ceiling](research/signature-based.md), each of which carries its own commit. No timings
were taken for this plan.
**Tracking issue:** [#854](https://github.com/mfaulk/zeebra/issues/854).
**Project:** [Zeebra #7](https://github.com/users/mfaulk/projects/7); label `M30`. Priority is the
Project field (P0 → High, P1 → Medium, conditional P1 → Medium plus the `blocked` label until its
gate passes). There is no native GitHub milestone object.

**Focus:** separate two questions M29 left open and answer each with evidence. Can Zeebra make F4
*do less algebra* (signatures)? Can it make the algebra it does *run in less wall time*
(parallel symbolic preprocessing)?

## 1. Vision and executive summary

> **M30 — Signature-Based Work Avoidance and Parallel Symbolic F4.** Advance Zeebra's Gröbner-basis
> engine beyond parallelizing conventional F4 by investigating algebraically sound mechanisms for
> eliminating unnecessary reductions and by parallelizing symbolic preprocessing. Establish whether
> these improvements can deliver substantial, reproducible gains against leading open-source solvers
> while preserving exact mathematical correctness, predictable resource usage, and Zeebra's
> general-purpose Rust API.

M29 closed with its Minimum met and both quantitative targets missed (§2). Its attribution names
the two mechanisms with enough reach to matter, and they are independent:

1. **Workstream S — signature-based work avoidance.** About 93% of Zeebra's coefficient products on
   Eco-12 and MQ11 are spent on pair rows that end up zero. On MQ11, grobx avoids nearly all of
   those reductions with signature criteria, by a deterministic algorithm. Whether Zeebra can do
   the same soundly, and whether the bookkeeping pays for itself, is unknown. #716 is the gate.
2. **Workstream P — parallel symbolic preprocessing.** Symbolic preprocessing is 23–34% of
   16-worker process wall after M29. A level-parallel prototype stalled at 1.38× on the stage
   because about two-thirds of the stage is a serial commit that interns monomials. #832 is the
   anchor.

The two are kept apart throughout. Workstream P makes the *existing* algorithm faster and changes
no algebraic quantity. Workstream S changes *which* algebra F4 performs. A result in one is never
reported as progress in the other, and the final report scores each separately (§14).

**Order of execution.** M30-0 freezes the baseline. Then four tracks run in parallel: grobx
signature ablations (#716), signature theory and architecture (M30-S2), symbolic reprofiling
(M30-P1), and interning prototypes (M30-P2). Implementation in either workstream waits for its own
gate. Neither workstream waits for the other.

## 2. M29 results and the remaining gaps

### 2.1 Measured (M29 §14, final cohort at `88bc45de`, n=9, process wall)

| Instance | Zeebra (16 workers) | Comparand | Ratio [95%] | Zeebra RSS |
|---|---:|---:|---:|---:|
| MQ10 / GF(32003) | 292.8 ms | msolve 116.6 ms (8w) | 2.51× [2.47, 2.55] | 39 MiB |
| MQ10 / GF(2³¹−1) | 278.7 ms | msolve 165.8 ms (4w) | 1.68× [1.64, 1.78] | 41 MiB |
| Eco-12 / 2⁶⁴−353 | 3,071 ms | grobx 1,634 ms (1w, raw randomized; output identical) | 1.88× [1.67, 1.89] | 199 MiB |
| MQ11 / Goldilocks | 5,720 ms | grobx 2,970 ms (1w, raw randomized; output identical) | 1.93× [1.80, 1.94] | 392 MiB |

These are historical, commit-specific baselines. They are not measurements of any M30 code, and
M30-0 re-freezes them before any M30 comparison (§10.1).

Also measured in M29 and relied on here:

- Forward elimination scales across 16 workers. The remaining serial stages are symbolic
  preprocessing and interreduction.
- Parallel candidate finishing (#845, PR #851) is the default: −13.9% / −22.6% process wall on
  Eco-12 / MQ11 with no RSS growth.
- Duplicate pair-multiple removal (#831, PR #841) is the default (`PairMultiples::Distinct`).
- Post-#851 stage times at 16 workers (cost model §6b, stage clocks on, ms): Eco-12 symbolic 990,
  forward 808, finishing 207, interreduction 520 of a 3,088 ms process; MQ11 symbolic 1,316,
  forward 2,558, finishing 262, interreduction 346 of 5,716 ms. MQ10/2³¹−1's symbolic stage is
  34% of process wall (M29 §14, Target 1).
- At one worker Zeebra is 7.7× (Eco-12) and 13.5× (MQ11) grobx's one-worker wall.

### 2.2 Four quantities that must not be conflated

M29's C1 note and #223's ceiling count different things. This plan uses the following names, and
every M30 issue must say which one it reports.

| Quantity | Definition | Where Zeebra measures it | Example |
|---|---|---|---|
| **Pairs rejected** | critical pairs discarded before any row is built, per mechanism (product, chain, Gebauer–Möller; in a signature engine also low-signature and syzygy/rewrite criteria) | `examples/pair_criteria.rs`; C1 ledger | Zeebra drops 386,626 pairs on Eco-12 by GM/chain; grobx drops 277,271 of 293,761 pair decisions on MQ11 by signature criteria |
| **Reductions to zero** | a selected pair that, once reduced, contributes no new basis element | C1 `--discovery` census | Eco-12: 6,331 of 7,202 reduced pairs (88%); MQ11: 6,293 of 7,059 (89%); grobx MQ11: 26 of 782 |
| **Zero rows** | Macaulay-matrix rows that are zero after elimination; one reduction can produce several, and reducer rows can be zero too | matrix census | grobx MQ11: 26 zero reductions but 562 zero rows |
| **Pair rows adding no rank** | `rank − reducer_rows` accounting, independent of elimination order | `examples/f4_degrees.rs` (#223, M22) | 33–60% on #223's corpus |
| **Coefficient products on zero-ending rows** | multiply-accumulates spent on rows that end zero, including discarded work | `linalg::work` counters (C1 §2) | 5.51 of 5.92 G (93.0%) on Eco-12; 18.92 of 20.38 G (92.9%) on MQ11 |

Two consequences for planning:

- **#223's "≈2× ceiling" and C1's "93% of products" are not in contradiction, and neither settles
  the other.** #223 bounded *rows* (33–60%, on smaller instances with `F4Options::recommended()`).
  C1 weighted by *coefficient products* on the post-M29 default and found that zero-ending rows are
  the expensive ones, because a row that becomes a pivot stops at its first free column while a
  zero row is reduced across its whole width. #223 §5 named exactly this as the condition for
  reopening: "a measurement showing the ≤2× is worth more than it appears because rows dominate
  Zeebra's cost". That condition now has a measurement. Whether the row fractions themselves differ
  (88–89% reductions to zero against 33–60% rows adding no rank) because of instance size, option
  set or definition is unreconciled, and #716 must reconcile it before any gate is read (§6.1).
- **Removing reductions to zero is not the same as removing their products.** A criterion that
  discards a pair saves its row's products only if that row would not have served as a reducer
  elsewhere, and only if signature-safe reduction does not make the surviving rows more expensive.

### 2.3 Distance to M29's targets (derived, not targets for M30)

From the §2.1 walls: Goal A at 2³¹−1 needed ≤248.7 ms (−11%); at 32003 about −40%. Goal B (a 10%
lead over grobx) needs −52.7% on Eco-12 and −53.8% on MQ11 (C1 §5). C1 priced parallel symbolic with
parallel interning at −24% / −17% (Eco-12 / MQ11, hypothetical ≈4× stage) and signature-compatible
criteria at −31% / −46% to −66%. Those are single-mechanism ceilings and estimates, not
predictions, and must not be multiplied.

## 3. Goals and success tiers

M30 has no single headline ratio. It has two workstreams, each with its own evidence gate, and three
tiers fixed now. **They must not be rewritten after measurements.** The final report scores each
criterion as met, missed or not attempted, with the reason.

**Minimum — decisive research and engineering evidence.**

1. M30-0 freezes the post-M29 baseline, protocol and comparand identities.
2. #716 publishes the grobx signature ablation (on / off / no-handover; combinations on/off where
   relevant) with the §2.2 quantities, process wall, RSS and verification for every arm.
3. M30-S2 publishes the signature-F4 correctness and architecture RFC with a go / no-go.
4. M30-P1 publishes the post-M29 symbolic cost model and Amdahl ceiling.
5. M30-P2 evaluates at least one bounded parallel-interning strategy against the P1 baseline.
6. M30-I publishes a reproducible decision report. Negative findings satisfy the Minimum when they
   resolve the hypothesis and are supported.

**Target — meaningful solver improvements.**

1. **Workstream P:** a parallel symbolic path passes the M30-P3 gate (§9.4), including ≥10% complete
   F4 process wall on one substantial public benchmark, and ships.
2. **Workstream S:** a credible, sound reduction in necessary algebraic work, preferably shown by an
   independently implemented bounded prototype (M30-S3) that records reductions to zero and
   coefficient products avoided by sound criteria on at least one substantial instance.

**Stretch — competitive performance.**

Parity with or a reproducible lead over the best comparand on a substantial public benchmark under
the same declared compute budget (§10.5); or an independently certified algorithmic result that
materially moves Zeebra's work frontier (for example, MQ11 coefficient work within 3× of grobx's
signature run, exactly verified).

## 4. Public/private boundary

Zeebra is the public, general-purpose computational-algebra library. M30 covers algorithms that
work for arbitrary polynomial ideals over Zeebra's supported finite fields and their competitive
performance, nothing else.

- Benchmarks are the public generic corpus: random MQ, Katsura, Cyclic, Eco and Noonburg, pinned by
  canonical system SHA-256 as in M29.
- No application-specific systems, challenge instances, datasets, scoreboards or research notes are
  added, cited or copied. Application work lives outside this repository and is out of scope.
- **Licensing.** grobx is GPL-3.0-only; Zeebra is MIT. Papers, algorithms and upstream measurements
  are references. Any grobx instrumentation or patch stays isolated under
  `tools/external/grobx-driver/research/` and follows
  [`external-provenance-policy.md`](research/external-provenance-policy.md). No GPL-covered
  implementation enters the crate. Any Zeebra signature code is implemented independently from the
  published algorithms.

## 5. Workstream S: hypotheses and background

### 5.1 What is already known

- **#223 (closed, won't-do, 2026-11-06)** declined F5/Matrix-F5. Its arguments: a 33–60% row
  ceiling bounds the gain near 2×; F4 and F5 reach the same degree of regularity, so signatures
  remove rows and never columns (Ding–Zhang–Deaton, eprint 2021/051); F5 is expected to do badly on
  overconstrained systems; the F5 guarantee does not cover non-regular inputs; signatures constrain
  the row arrangement and reducer choice F4 exploits. It retracted its own "full rewrite" claim
  after reading Eder–Faugère §13 (F4/5 as "smaller changes … of some subalgorithms"), and it found
  that GVW's rewritable criterion is not a standalone pair criterion: it presupposes signatures on
  every basis element, a module order and a syzygy basis. **M30 preserves all of this.** #223 stays
  closed, and its findings are inputs to M30-S2, not claims to overturn.
- **#713 / #714 / grobx-randomization.md:** grobx's randomized row combinations save real work, but
  the straightforward exact audit erases the saving (1.30× slower than deterministic plain
  reduction at the larger prime). grobx's *signature* zero tests are also a separate, partly
  randomized mechanism. A final global span check cannot certify signature-prefix syzygies.
- **C1 (#835):** on MQ11 grobx runs signature F4 for all 11 rounds with a Schreyer module order and
  does 22.8× less coefficient work (charges, a proxy validated to 2% only on MQ10/GF(2³¹−1)). On
  Eco-12 it hands over to plain F4 at round 2 and reduces with randomized combinations. A
  signatures-on, no-handover run on Eco-12 and a signatures-off run on MQ11 **have never been
  measured.**

### 5.2 Hypotheses (unmeasured)

- **H-S1.** On MQ11, most of grobx's 22.8× work advantage comes from signature criteria, not from
  its plain-F4 engine. *Falsified* if grobx `signatures=false` at the same seed does comparable
  coefficient work to its default.
- **H-S2.** On Eco-12, signatures without handover help less than randomized combinations; Eco-12
  may not be a signature target at all.
- **H-S3.** A signature-compatible F4 (F4/5- or F4-RB-shaped, by increasing degree, sparse) can host
  sound criteria inside Zeebra's batched elimination at bookkeeping cost small relative to the
  products saved on regular-like inputs.
- **H-S4.** On non-regular or overdetermined inputs the bookkeeping is a net loss; an adaptive
  handover is then required, not optional.

## 6. Workstream S: experiments and decision gates

### 6.1 M30-S1 — signature attribution and feasibility (#716)

#716 is reused as M30-S1. It stays a child of #256, where it was filed. Its existing contract
(five interleaved fresh-process repetitions per arm, complete verified answers, discarded work
counted, adopt / reject / defer) stands. M30 extends its corpus and adds a numerical gate.

Arms, same input, seed and pinned grobx:

1. grobx default (signatures with adaptive handover);
2. public `Params.signatures=false` (plain F4);
3. signatures with handover disabled, through an isolated research overlay;
4. on Eco-12 and MQ10/2³¹−1, combinations on and off crossed with arms 1–3, using the existing
   `research/randomization` overlay, so signature criteria are separated from randomized reduction.

Instances, in order: MQ11/Goldilocks, Eco-12/2⁶⁴−353, MQ10/GF(32003), MQ10/GF(2³¹−1). Held-out:
one Katsura and one Cyclic instance from the pinned corpus, with digests and budgets declared
before execution.

Per run: pair decisions by mechanism (signature low-sig, syzygy/rewrite, Koszul, GM/chain, other);
the §2.2 quantities; matrix dimensions, nonzeros, density and rank per round; coefficient work
(products where the observer applies, charges otherwise, stated); process wall, per-stage wall,
peak RSS and temporary workspace; signature/syzygy metadata size and bookkeeping time; solver
configuration, seed, source revision and executable SHA-256; verification status.

Also required before the gate is read: **reconcile #223's row fraction with C1's** by running
`examples/f4_degrees.rs` on MQ11 and Eco-12 and the C1 zero-row census on two of #223's instances,
at one commit.

**Gate A1 (predeclared).** Recommend proceeding to a prototype only if, on at least one substantial
instance (MQ11 or Eco-12), a signature-aware grobx arm against its comparable signature-disabled
arm shows **≥2× less coefficient work and ≥25% less complete process wall**, with peak RSS ≤1.5×
and identical verified output. *Feasibility check of these thresholds:* C1 measured grobx-default
work 22.8× below Zeebra's on MQ11, so if H-S1 holds the 2× bar has an order of magnitude of
headroom; if grobx plain-F4 on MQ11 is already near its default, the gate fails as intended. The
25% wall bar is deliberately lower than the work bar because bookkeeping is unpriced. The gate is
grobx-relative because Zeebra has no signature arm; it says signatures pay in *some* engine, not
that they will pay in Zeebra. If A1 fails, the result is recorded and S3/S4 close as not planned.

### 6.2 M30-S2 — invariants, architecture and implementation RFC (#856)

Runs in parallel with #716; its go / no-go depends on #716's gate. Deliverable:
[`docs/research/signature-f4-rfc.md`](research/signature-f4-rfc.md) (published; it recommends the isolated architecture, F4-RB under Schreyer order, and, applying its predeclared rule to Gate A1, returns **go, narrowed** to Eco-12 primary with `katsura-11` as the second family).

Must cover, from the papers rather than their abstracts: F5 and Matrix-F5; F4/5 and F4-RB;
Schreyer and position-over-term module orders, and signature representation; signature-safe
(regular) reduction and what a matrix row's signature means after elimination; rewrite and syzygy
criteria; Koszul syzygies and the regular-sequence guarantee; incremental versus non-incremental
algorithms; overlap with Gebauer–Möller and chain; behaviour on non-regular, overdetermined,
underdetermined and non-radical ideals; hybrid signature / plain F4 with handover. Sources: the
Eder–Faugère survey (arXiv 1404.1774), Lairez 2022, Roune–Stillman 2012, Arri–Perry 2011,
Ding–Zhang–Deaton (eprint 2021/051), Faugère's F5 paper, grobx's MANUAL (as documentation, not as
code), and [`signature-based.md`](research/signature-based.md).

It must state how each choice interacts with: `src/grobner/pairs.rs` (selection and scheduling);
monomial and polynomial representations; `src/grobner/f4/symbolic.rs` (reducer selection, which a
signature discipline constrains and may invalidate); `macaulay.rs` assembly; structured parallel
elimination (`reduction.rs`, `structured.rs`, `parallel.rs`); candidate finishing and
`interreduce.rs`; `budget.rs` resource enforcement; and the `FiniteField` abstraction and public
`F4Options` API.

**It must not assume signature criteria can be applied to unsigned critical pairs as a filtering
pass.** #223 §5.1 already showed the rewritable criterion presupposes the framework. The RFC models
labelled-polynomial provenance and the restrictions on reduction, and gives a correctness argument
that discarded pairs cannot change the ideal generated or the final reduced basis.

It compares at least two architectures, each with complexity, metadata memory, maintenance cost,
expected performance range and risks:

1. **Integrated:** a signature-aware F4 path sharing pair, symbolic and elimination infrastructure,
   with signatures carried per row.
2. **Isolated:** a separate experimental engine reusing field, monomial, polynomial and matrix
   components, behind its own entry point.

It ends with one recommended architecture and one algorithmic variant, or a no-go. It also
predeclares the S3 evaluation corpus and the S4 thresholds before any code is written.

### 6.3 M30-S3 — conditional bounded prototype (#857)

**Blocked** until #716 passes Gate A1 and #856 returns go. Creating the issue does not authorize
the work.

Scope: one architecture, one variant, opt-in only, behind a research feature or an explicit option.
The existing F4 stays the reference and fallback. Bounds: an explicit effort cap set in S2, at most
two designs, and S2's predeclared corpus. Two failed designs end the line with a documented
negative result.

Correctness: compare against independent Buchberger and Singular references on small systems;
confirm the output is the complete reduced basis of the input ideal, not a set with plausible
leading terms; test non-regular, overdetermined, underdetermined and non-radical inputs where the
variant supports them, at least two fields and every supported monomial order the variant claims.
Reuse budget and cancellation infrastructure.

Report the reductions to zero and coefficient products avoided **by sound criteria**, the
bookkeeping cost separately, and the wall time actually saved.

### 6.4 M30-S4 — conditional production qualification (#858)

**Blocked** on #857 succeeding. Thresholds, predeclared here and to be confirmed (not loosened)
by S2:

- ≥25% better complete F4 process wall on a substantial, independently verified benchmark;
- improvement on a second instance from a different family than the first (MQ10 does not count as
  distinct from MQ11 for this criterion);
- no regression beyond 5% on small controls;
- peak RSS ≤1.25× the shipping baseline, unless a fixed-budget advantage is separately shown;
- correct across the supported fields and monomial orders the path accepts, with a fallback for the
  rest;
- correct cancellation, fallback and typed budget errors;
- documentation that makes no claim that signatures remove all reductions to zero on arbitrary
  inputs.

The path stays opt-in after S4. Changing the default is a separate decision with its own evidence.

## 7. Workstream S: what a prototype would look like

Indicative only; S2 decides. Following #223's retracted note, the plausible shape is sparse F4/5 by
increasing degree (`<d-pot`), not Matrix-F5, because Zeebra's matrices are a fraction of a percent
dense and Matrix-F5 needs dense Macaulay matrices at a fixed degree. Minimum metadata is a module
signature per basis element and per matrix row, a syzygy-signature store seeded with Koszul
syzygies and grown from reductions to zero, and a rewrite rule per signature. The open engineering
questions are what elimination order is admissible for signed rows, and whether parallel forward
elimination over independent targets survives that restriction (§13, risk R3).

## 8. Workstream P: the symbolic bottleneck

### 8.1 Measured

- #827: `symbolic_preprocessing_level_parallel` (`research-work`) on Katsura-11 / 2³¹−1 gave 0.64×
  at one worker, 1.38× at 16 and 1.55× at 32 on the stage. At 16 workers that is −8% of a 1,640 ms
  F4 call, and about 18 ms of MQ10's 275 ms.
- The serial in-order commit (interning new terms, pushing rows, resolving terms first met in the
  level) costs about 300–325 ms, roughly two-thirds of the stage, so the stage ceiling stays near
  1.5× while the commit is serial.
- Those figures predate #841 (dedup) and #851 (parallel finishing). After #851, symbolic is the
  largest serial stage on Eco-12 (32% of process wall) and MQ10/2³¹−1 (34%), and 23% on MQ11.

### 8.2 Derived estimates (Amdahl, not measurements)

With the stage share *f* and stage speedup *s*, the process-wall saving is *f*(1 − 1/*s*). A 10%
whole-task gain needs *s* ≥ 1.45 on Eco-12 (*f* = 0.32), ≥ 1.42 on MQ10/2³¹−1 (*f* = 0.34) and
≥ 1.77 on MQ11 (*f* = 0.23). If the commit stays two-thirds serial after dedup, *s* ≤ 1.5 by
construction, so **a ≥10% result on MQ11 needs a parallel or cheaper commit**, and on Eco-12 and
MQ10 the prototype is only marginal. The cost model's hypothetical ≈4× with parallel interning
gives −20% to −24% on Eco-12 and MQ10 and −13% on MQ11. M30-P1 replaces these with measurements.

### 8.3 M30-P0 — parallel symbolic preprocessing (#832)

#832 is reused as the workstream anchor and is reparented from the closed M29 tracker to
#854. Its children are M30-P1, P2 and P3. It closes when P3 ships or the workstream ends
with a recorded negative result.

## 9. Workstream P: plan

### 9.1 M30-P1 — post-M29 symbolic cost model and Amdahl analysis (#859)

Reprofile the shipping post-M29 F4 path (dedup on, parallel finishing on) at the M30-0 commit, on
MQ10 (both fields), Eco-12, MQ11 and Katsura-11, at 1, 4, 8 and 16 workers. Measure, per batch as
distributions and in total: stage time and share of process wall; monomial lookup, hashing,
insertion and interning; divisor search and divisibility checks; term shifting and duplicate
detection; queue / frontier management; serial commit; allocations and scratch buffers; cache
behaviour where the counters are available; synchronization and work distribution in the
prototype. Deliverables: `docs/research/m30-symbolic-cost-model.md`; the maximum recoverable
whole-task improvement per instance; a classification of each serial part as an algebraic
dependency (FIFO closure order, handle order that column order depends on) or an implementation
artefact. Instrumented counters are a separate campaign from timed walls.

### 9.2 M30-P2 — deterministic parallel interning and dispatch (#860)

May start design and small prototypes in parallel with P1; its gate reads P1's numbers.

Two approaches, each as a small independent prototype under `research-work`:

1. **Local discovery, deterministic merge.** Workers discover, pre-hash and pre-partition candidate
   monomials; a merge commits them in canonical frontier order. The question is how worker-local
   identifiers map to final `MonomialHandle`s without a rewrite pass or repeated allocation.
2. **Sharded interning.** Concurrent insertion into a hash-sharded table with a deterministic
   global order, or a translation layer that restores it. The questions are contention, shard
   balance, duplicate discovery, canonicalization and memory pressure.

Both must answer: which invariants depend on handle order (`Preprocessed::term_handles`, matrix
column order, reducer selection, closure order, basis output); whether exact handle identity is
required or a stable remap suffices; allocations and retained temporaries; live-memory budget
accounting; cancellation and partial-work discard; behaviour at 1, 4, 8 and 16 workers.

Dispatch overhead (the 0.64× one-worker cost) is in scope here too: per-batch scoped worker teams
instead of per-level spawns, coarser tasks on large frontiers, scratch reuse, fewer barriers, and a
serial path for small closures selected by measured batch size. Prefer one adaptive threshold over
new options. Reuse existing concurrency (`linalg::concurrent`, the F4 worker pool) where practical.
`test_level_parallel_symbolic_preprocessing_matches_the_serial_closure` is the equivalence floor;
it must keep passing at every worker count.

Output: a measured comparison and one recommended design, or a negative result. A general-purpose
concurrent monomial subsystem is built only if its whole-task numbers justify it; #268's broader
representation work is not pulled in.

### 9.3 Not in P

Faster symbolic preprocessing that makes complete F4 slower, a new execution runtime, and changes to
reducer *selection policy* (which would change the algebra and belongs to a different question).

### 9.4 M30-P3 — conditional production integration (#861)

**Blocked** until #860 recommends a design that clears its own measurement. Gate, predeclared:

- ≥2× symbolic-stage speedup at 16 workers on a substantial target, **or** a measured profile that
  supports the next criterion by another route;
- **≥10% complete F4 process wall on one substantial public benchmark** — the main adoption
  requirement;
- an improvement on a held-out instance or family;
- no regression beyond 5% on small tasks or at one worker (adaptive serial fallback as needed);
- peak RSS ≤1.15× baseline;
- output identical to the serial reference under every configuration changed, and deterministic
  independent of scheduling;
- correct budget and cancellation behaviour.

A serial path and an explicit fallback remain. A large stage speedup without the whole-task
improvement does not ship.

## 10. Benchmark, correctness and resource protocol

M30 reuses M29's infrastructure (`research/m29-baseline/` scripts, `examples/m29_cost_model.rs`,
`tools/benchlock.sh`, `tools/bench-reserve.sh`, the grobx and groebner-rs drivers, the
`comparand-scaling.py` and `wide-corpus.py` controllers). It does not create another harness.

### 10.1 M30-0 baseline (#855)

Freeze at one commit: Zeebra source and executable SHA-256s; exact external solver versions,
binaries and research overlays; Rust toolchain, profile (release, fat LTO, one codegen unit) and ISA
(`x86-64-v3`); input-system digests; every F4 option and engine configuration; host
(Threadripper PRO 5995WX) and topology; affinity and worker placement. Re-run the §2.1 cohort at
that commit with M29's scripts and publish `research/m30-baseline/`. Comparisons across hardware
or compiler conditions are never treated as paired.

#855 froze this at `4f5784c5`. [`research/m30-baseline/`](../research/m30-baseline/README.md) holds
the cohort, identities, drift and verification. [`docs/research/m30-protocol.md`](research/m30-protocol.md)
is the protocol every M30 issue follows.

### 10.2 Performance method

- Fresh process per run; interleaved, rotated arms; same input and output contract; same resource
  limits; fixed, documented seeds.
- Zeebra worker curves at 1, 4, 8 and 16; each comparand's fastest supported configuration within
  the declared core budget.
- Process wall is authoritative. Stage clocks and work counters run as separate campaigns where
  they perturb timing.
- Peak RSS and live-entry reservations alongside wall.
- n ≥ 5 per arm for ablations, n ≥ 9 for milestone acceptance; medians with 95% bootstrap
  intervals, as `research/m29-final/verdicts.py`.
- Every timeout, refusal, allocation failure and unsupported outcome is recorded. No resampling
  until a result looks good; no inference from incomplete runs.

### 10.3 Correctness

Exact references where they exist (Singular for MQ10). Wider fields need an independent certificate
or exact ideal-containment evidence; agreement of two solvers' outputs is not sufficient alone.
Every accepted output is checked to be reduced, to satisfy Buchberger's criterion, to contain the
input ideal and to generate the same ideal. Verification time is reported outside raw solve time,
and configurations whose certification changes the solver's behaviour (grobx certified mode) are
reported separately.

### 10.4 Resource budgets

Every arm declares wall and memory caps before execution. A prototype that needs a larger cap than
the shipping baseline reports that as a result.

### 10.5 Fair comparison

grobx and groebner-rs run one worker only (their adapters refuse more). A comparison against them at
16 Zeebra workers is reported as such, never as equal-worker. An equal-worker row is reported
separately.

## 11. Work packages and issues

All rows carry the `M30` label and a Project #7 Priority. New issues are native sub-issues of
#854, except P1–P3, which are sub-issues of #832, and #716, which keeps its parent #256.
Dependencies are native "blocked by" relations; conditional issues also carry `blocked`.

| WP | Issue | Priority | Blocked by | Kind |
|---|---|---|---|---|
| M30 tracker | [#854](https://github.com/mfaulk/zeebra/issues/854) | High | — | tracking |
| M30-0 baseline and protocol | [#855](https://github.com/mfaulk/zeebra/issues/855) | High | — | required |
| M30-S1 signature attribution | [#716](https://github.com/mfaulk/zeebra/issues/716) (reused) | High | #855 (measurements only) | required |
| M30-S2 signature RFC | [#856](https://github.com/mfaulk/zeebra/issues/856) | High | — (go/no-go reads #716) | required |
| M30-S3 bounded prototype | [#857](https://github.com/mfaulk/zeebra/issues/857) | Medium | #716, #856 | **conditional** |
| M30-S4 production qualification | [#858](https://github.com/mfaulk/zeebra/issues/858) | Medium | #857 | **conditional** |
| M30-P0 parallel symbolic (anchor) | [#832](https://github.com/mfaulk/zeebra/issues/832) (reused) | High | its children | required |
| M30-P1 symbolic cost model | [#859](https://github.com/mfaulk/zeebra/issues/859) | High | #855 | required |
| M30-P2 parallel interning designs | [#860](https://github.com/mfaulk/zeebra/issues/860) | High | — (gate reads #859) | required |
| M30-P3 adaptive parallel symbolic | [#861](https://github.com/mfaulk/zeebra/issues/861) | Medium | #860 | **conditional** |
| M30-I final report | [#862](https://github.com/mfaulk/zeebra/issues/862) | High | all of the above | closeout |

Reviewed and **not** pulled into M30: #809 (Simplify; C1 §2 shows it cannot remove a zero row),
#268 (compact representations; M30 excludes a representation redesign), #273 (closed; handover
policy is now inside S2), #223 (closed, preserved). The other referenced issues (#713, #714, #827,
#834, #835, #845) are closed and are inputs.

## 12. Parallel development and merge sequencing

Initial independent tracks:

- **Agent A:** M30-0 baseline, protocol and scoreboard setup.
- **Agent B:** #716 grobx ablations and coefficient attribution (external workspace only).
- **Agent C:** M30-S2 literature and architecture (documents only).
- **Agent D:** M30-P1 profiling, then M30-P2 prototypes.

B and C proceed together; the S3 decision waits for both. Workstream P never waits for S.

After the gates: **Agent E** may take S3, **Agent F** may take P3.

Contention: `src/grobner/f4/symbolic.rs`, `src/grobner/f4/macaulay.rs`, `src/grobner/pairs.rs` and
`src/linalg/` are shared by S3 and P3. Only one of them owns a shared interface at a time. If both
run, P3 merges first (smaller, default-path change) and S3 rebases onto it, because S3 is opt-in and
can live behind its own entry point (S2's isolated architecture avoids the overlap entirely). Each
agent works in its own `git worktree` with a private `CARGO_TARGET_DIR` under `/buildcache`. All
timed campaigns run under `benchlock`, with CCD reservations released after each session.

Sequence: freeze → measure (S1, P1) → design (S2, P2) → gates → at most one implementation per
workstream → re-measure after each merge (no multiplied estimates) → final cohort → report.

## 13. Risks, exclusions and stop rules

| # | Risk | Mitigation |
|---|---|---|
| R1 | grobx's MQ11 advantage is mostly its plain engine, not signatures | Gate A1 measures exactly this first; S3/S4 close if it fails |
| R2 | Signature bookkeeping costs more than it saves outside regular sequences | S2 prices it; S4 requires a second family and small-control parity |
| R3 | Signature-safe reduction restricts row order enough to lose parallel forward elimination | S2 must answer explicitly; isolated architecture keeps the shipping path untouched |
| R4 | Unsound criterion silently drops a needed pair | correctness argument in S2; complete-basis checks in S3, not leading-term checks |
| R5 | Parallel interning cannot keep handle order without a serial merge as costly as today's | P2 tests two approaches; P3 stays blocked |
| R6 | One-worker or small-task regression | adaptive serial path; 5% gate |
| R7 | Measurement noise on a shared 64-core host | benchlock, CCD reservation, paired ratios, n ≥ 9 for acceptance |
| R8 | GPL contamination | isolation rules in §4 |
| R9 | Scope drift into a solver rewrite | two-design cap, predeclared gates, stop rules below |

**Exclusions:** application-specific work; FGLM or whole-solving routes; GPU; out-of-core; a new
execution runtime; unbounded F5; a redesign of every polynomial or monomial representation;
uncertified randomized row skipping; field-arithmetic work not tied to an M30 gate.

**Stop rules.** Gate A1 fails → S3 and S4 close as not planned, with the evidence. S2 no-go →
same. Two failed S3 designs → stop and report. P2 finds no design clearing its measurement → P3
closes and #832 closes with a recorded negative result. The milestone does not continue because a
more ambitious hypothesis failed.

## 14. Planned final scoreboards and report

M30-I reports, per primary task (MQ10 at both fields, Eco-12, MQ11) and the held-out instances:

- Zeebra baseline (M30-0), each experimental arm and the shipping configuration;
- msolve exact mode; grobx raw randomized and exact/certified, clearly distinguished; groebner-rs;
- process wall, ratio, 95% interval, peak RSS, verification status, worker count per engine;
- symbolic-stage time, coefficient work, reductions to zero, zero rows and pair rejections by
  mechanism, where available;
- Zeebra worker scaling at 1, 4, 8 and 16;
- every negative, inconclusive and stopped experiment.

Two verdicts, kept apart: **faster execution of existing F4** (Workstream P, scored on wall) and
**less algebraic work** (Workstream S, scored on the §2.2 quantities and then on wall). M30
succeeds scientifically only with credible evidence on both, and technically only if accepted
changes improve complete, verified computations under controlled resource budgets.
