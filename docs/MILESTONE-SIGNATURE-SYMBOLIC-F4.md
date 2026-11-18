# M30 — Signature-Based Work Avoidance and Parallel Symbolic F4

**Status:** complete, 2026-11-18. Minimum met; Target met on both workstreams; Stretch clause 1
missed and clause 2 met by an opt-in research prototype. The integration report is §15 (#862).
§§1–14 are the plan as fixed before measurement, except the outcome notes each gate's issue added.
**Predecessor:** M29 — Verified Competitive F4
([`MILESTONE-COMPETITIVE-F4.md`](MILESTONE-COMPETITIVE-F4.md), §14 integration report).
**Planning base:** `main` at `adfa6a60`.
**Measured at:** not measured here — every figure is quoted from the M29 integration report
(measured at `88bc45de`), the [M29 cost model](research/m29-baseline-cost-model.md) (`527a105e`
and the commits in its §6a/§6b), the [C1 attribution](research/m29-grobx-attribution.md)
(`7e18d089`), [#827's report](research/serial-stage-slowdown.md) and
[#223's ceiling](research/signature-based.md), each of which carries its own commit. No timings
were taken for this plan. §15's figures were measured at `e4826153` (instrument `5515c412`)
beside the freeze `4f5784c5` (`research/m30-final/`). The #887 follow-up in §15.6 was measured at `9548555d`
against `b1d8e36a`. It also quotes #716, #857 and #861, each at
the commits its own report names.
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

**Outcome (#861):** every line met at `ad61fb15`, so `ParallelSymbolic::Auto { max_workers: 16 }`
is the default: Eco-12 0.748× [0.746, 0.749] complete F4 at 16 workers (n = 10), held-out
Katsura-11 0.780×, small tasks and one worker 0.965–1.022×, peak RSS ≤1.069×, bases identical.
Step 0 found the #871 prototype at up to 1.33× on Katsura-7; the adaptive fallback that fixed it
is in [`m30-parallel-interning.md`](research/m30-parallel-interning.md) §11.

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

## 15. Integration report (#862)

**Measured at:** final `main` `e4826153` (instrument `5515c412`; `src/` and `Cargo.lock`
identical), interleaved in one campaign with the M30-0 freeze `4f5784c5`. Evidence and
provenance: [`research/m30-final/`](../research/m30-final/README.md), every table in
[`tables.md`](../research/m30-final/tables.md). 2026-11-18, 00:24–02:06 EST, inside a CCD 1–2
reservation. n = 9 per cell, fresh processes, every attempt retained. No child failed, timed out or
was refused. No compiler was running when any of the 672 Zeebra children started. Medians with 95%
bootstrap intervals (`research/m29-final/verdicts.py`). A ratio is median ÷ median.

**The final `main` is `e4826153`, not `d6aa0526`.** Preparing this cohort found #883. Since #861,
the default 16-thread interning team was not capped by `Limits::workers` in the comparand adapter,
nor by `m29_cost_model`, `wide_corpus` or `sig_f4_study`. `ParallelSymbolic::Auto { max_workers: 16 }`
does not clamp itself to the affinity mask, so a "1-worker" row from those paths could run 16
threads on one CPU. #884 fixed this, and the cohort runs at the fixed `main`. **No published row is
affected.** Every M30 figure before `d6aa0526` ran with `Serial` interning, and #861's gate set the
team explicitly (`--level-workers w`). The library default itself still does not clamp (#886).

### 15.1 Status: Minimum met; Target met on both workstreams; Stretch clause 1 missed, clause 2 met by a research prototype

**Two verdicts, kept apart (§14).**

1. **Workstream P (faster execution of existing F4): success, shipped.** Adaptive parallel interning
   (`ParallelSymbolic::Auto { max_workers: 16 }`, #861) brings complete F4 at 16 workers to
   **0.767×** the freeze on Eco-12 and 0.81× on MQ11. On the held-out instances it is 0.78–0.81×,
   and on Cyclic-7 0.985×. The algebra is unchanged: pairs, reductions to zero, zero rows,
   coefficient products and bases are identical (§15.3).
2. **Workstream S (less algebraic work): positive on work, negative on wall.** A sound,
   independently implemented signature-F4 prototype does 9.7× (Eco-12), 11.7× (MQ11) and 22.8×
   (Katsura-11) fewer coefficient products than shipping F4. Its bases are identical coefficient
   for coefficient. On the primary instance that saving does not become wall time. #858's gate
   (≤0.80 on Eco-12) was missed at 1.010. At the final `main`, design 1 is 1.550× shipping F4 on
   Eco-12, because P made the reference faster. Nothing from S ships.

By §14, M30 succeeds **scientifically**: there is credible evidence on both workstreams. It
succeeds **technically** on Workstream P only. P's accepted change improves complete, verified
computations under the declared budgets. S changed no shipping code.

### 15.2 Primary scoreboard (process wall, final `main`)

Each row gives Zeebra at 16 workers against the comparand each M29/M30 goal names. grobx always runs
one worker, because its adapter refuses more. **Every grobx row is therefore 16 Zeebra workers
against one grobx worker, and none is an equal-worker comparison.** The equal-worker figure is
alongside it. msolve and groebner-rs under `comparand-scaling.py` run at 1, 4, 8 and 16 workers; the
fastest median is used. groebner-rs under `wide-corpus.py` runs one worker.

| Task | Zeebra M30-0 → final (16w) | final ÷ M30-0 [95%] | Comparand (mode, workers) | Zeebra 16w ÷ comparand [95%] | Equal-worker: Zeebra 1w ÷ grobx 1w | Zeebra RSS 16w | Verification |
|---|---:|---:|---|---:|---:|---:|---|
| MQ10 / 32003 | 288.3 → 237.7 ms | 0.825 [0.822, 0.828] | msolve exact 117.0 ms (8w) | **2.03×** [2.00, 2.06] | 3.17× | 43 MiB | Singular reference, every answer |
| MQ10 / 2³¹−1 | 271.9 → 219.8 ms | 0.808 [0.803, 0.816] | msolve exact 158.5 ms (4w) | **1.39×** [1.38, 1.41] | 5.78× | 45 MiB | Singular reference, every answer |
| Eco-12 / 2⁶⁴−353 | 3,065.5 → 2,350.5 ms | **0.767** [0.764, 0.770] | grobx raw randomized 1,613.7 ms (1w) | **1.46×** [1.45, 1.46], 16w vs 1w | 7.76× | 199 MiB | **verified**: one digest across 72 runs, textually identical to grobx certified (743 elements, 283 s, 32 GiB cap, peak 11.4 GB) |
| MQ11 / Goldilocks | 5,728.5 → 4,642.5 ms | 0.810 [0.807, 0.812] | grobx raw randomized 2,914.0 ms (1w) | **1.59×** [1.59, 1.60], 16w vs 1w | 13.6× | 393 MiB | **verified**: one digest across 72 runs, textually identical to grobx certified (767 elements, 456 s, 8 GiB, peak 2.1 GB) |
| Katsura-11 / 2³¹−1 (held out, #861) | 1,426.4 → 1,108.8 ms | 0.777 [0.774, 0.781] | n/a: no comparand reference for this row | — | — | 149 MiB | one digest across all 72 runs |
| Katsura-11 / 2⁶⁴−353 (held out, pinned) | 1,639.5 → 1,326.5 ms | 0.809 [0.806, 0.813] | grobx raw randomized 547.0 ms (1w) | **2.43×** [2.40, 2.43], 16w vs 1w | 16.1× | 149 MiB | **verified**: grobx certified (537 elements, 80 s, 8 GiB) and Zeebra's own certificate (606 s) |
| Cyclic-7 / 2⁶⁴−353 (held out, pinned) | 142.7 → 140.5 ms | 0.985 [0.973, 0.996] | grobx raw randomized 116.3 ms (1w) | **1.21×** [1.20, 1.22], 16w vs 1w | 2.27× | 21 MiB | **verified**: grobx certified (209 elements, 3 s) and Zeebra's own certificate (2 s) |

**The fastest verified comparand on MQ10 is groebner-rs, not msolve.** groebner-rs uses randomized
modular row combinations, and its answers are verified. It takes 83.3 ms at 4 workers on 32003
(Zeebra is 2.85× slower) and 97.6 ms at 4 workers on 2³¹−1 (2.25×). On the wide targets
groebner-rs at one worker is slower than Zeebra at 16. Zeebra ÷ groebner-rs is 0.80 on Eco-12, 0.52
on MQ11, 0.61 on Katsura-11 and 0.81 on Cyclic-7. These are not equal-worker comparisons either. At
one worker Zeebra is 4.1–4.5× slower than groebner-rs on the large wide rows and 1.5× slower on
Cyclic-7. Plan §10.5 says grobx and groebner-rs run one worker only. That holds for grobx
everywhere, but for groebner-rs only under `wide-corpus.py`. This is reported as found, and no
target is changed. The comparand-scaling window has its own Zeebra row, from `zeebra_driver`. It
agrees with the cost-model row within 2%: 240.0 and 224.2 ms at 16 workers.

**Movement over M30.** Against M29's §14 ratios (§2.1), Eco-12 went from 1.88× to 1.46× grobx and
MQ11 from 1.93× to 1.59×. MQ10/32003 went from 2.51× to 2.03× msolve, and MQ10/2³¹−1 from 1.68× to
1.39×. All of this movement is Workstream P. The freeze-to-final figure is the interleaved column.
It is not a comparison against a wall published from another session.

### 15.3 Workstream P, measured

Worker scaling at the final `main`, in ms. The last column is the 16-worker speedup over one worker,
with the freeze in parentheses.

| Instance | 1 | 4 | 8 | 16 | speedup |
|---|---:|---:|---:|---:|---:|
| MQ10 / 32003 | 1,064.9 | 375.6 | 279.3 | 237.7 | 4.48× (3.70×) |
| MQ10 / 2³¹−1 | 910.7 | 321.0 | 246.3 | 219.8 | 4.14× (3.42×) |
| Eco-12 | 12,518.4 | 4,178.0 | 3,014.6 | 2,350.5 | 5.33× (4.11×) |
| MQ11 | 39,669.1 | 11,151.8 | 7,140.7 | 4,642.5 | 8.54× (7.08×) |
| Katsura-11 / 2³¹−1 | 6,795.6 | 2,053.4 | 1,444.4 | 1,108.8 | 6.13× (4.89×) |
| Katsura-11 / 2⁶⁴−353 | 8,810.4 | 2,733.6 | 1,841.9 | 1,326.5 | 6.64× (5.47×) |
| Cyclic-7 / 2⁶⁴−353 | 264.3 | 148.8 | 133.3 | 140.5 | 1.88× (1.87×) |

Final ÷ freeze is 0.975–1.000 at one worker, 0.86–0.96 at 4, 0.81–0.94 at 8 and 0.77–0.99 at 16.
Peak RSS at 16 workers is 1.00× on Eco-12 and MQ11, 1.03× on Katsura-11 and 1.07× on MQ10. All are
inside §9.4's 1.15×.

Symbolic preprocessing comes from a separate stage-clock campaign (n = 5, 16 workers):

- Eco-12: 992.6 → 256.6 ms (3.87×)
- MQ11: 1,315.5 → 297.0 ms (4.43×)
- MQ10: 92.6 → 45.0 ms and 93.4 → 45.3 ms (2.06×)
- Katsura-11: 454.2 → 141.3 ms and 453.5 → 144.4 ms (3.1–3.2×)
- Cyclic-7: 39.9 → 37.3 ms

Its share of 16-worker process wall fell from 32.4% to 10.9% on Eco-12, from 23.0% to 6.4% on MQ11,
and from 32–34% to 19–21% on MQ10.

The serial `research-work` census ran once per build. **Its algebraic quantities are identical at
the freeze and the final `main` on all seven targets.** That covers pairs considered, pair rejections
by mechanism, pairs reduced, reductions to zero, zero rows, pair rows adding no rank, coefficient
products, and products on zero-ending rows. On Eco-12, for example, there are 7,202 pairs reduced,
6,326 reductions to zero and 6,331 zero rows. Coefficient products are 5.924 G, 93.0% of them on
zero-ending rows. Gebauer–Möller rejects 386,626 pairs; product and chain reject none. Workstream P
changed no algebra, as §1 requires.

§9.4's gate, re-read at the final `main`:

| Criterion | Final cohort | Met? |
|---|---|---|
| ≥2× symbolic stage at 16 workers, substantial target | 3.87× Eco-12, 4.43× MQ11 | yes |
| ≥10% complete F4 process wall, substantial public benchmark | −23.3% Eco-12 [−23.6, −23.0], −19.0% MQ11 | yes |
| improvement on a held-out instance or family | Katsura-11 −19.1% (2⁶⁴−353) and −22.3% (2³¹−1); Cyclic-7 −1.5% at 16w, −5.7% at 8w | yes |
| no regression beyond 5% on small tasks or at one worker | one worker 0.975–1.000 on all seven targets; small tasks (Katsura-6/7, cyclic-6) not re-run here, #861's `gate` measured 0.965–1.022 | yes at one worker; small tasks rest on #861 |
| peak RSS ≤1.15× | ≤1.075× | yes |
| identical, deterministic output | one basis digest per target across all 72 runs of both builds | yes |
| budget and cancellation | #872's and #876's tests unchanged and in CI | yes (tests, not timing) |

### 15.4 Workstream S, measured

These figures come from #716, #857 and #858. Only the wall comparison was re-run here, because P
invalidated it.

| Quantity (§2.2) | Eco-12 | MQ11 | Katsura-11 | Source |
|---|---:|---:|---:|---|
| shipping F4: reductions to zero / zero rows | 6,326 / 6,331 | 6,293 / 6,293 | 3,936 / 3,936 | §15.3 census, `e4826153` |
| shipping F4: coefficient products | 5.924 G (93.0% on zero-ending rows) | 20.377 G (92.9%) | 4.556 G (93.1%) | §15.3 census |
| sig-F4 design 1: reductions to zero (= zero rows) | 1,013 | 540 | 145 | #857 §3.1, `2d589a80` |
| sig-F4 design 1: coefficient products | 0.611 G (**9.7×** fewer) | 1.745 G (**11.7×**) | 0.200 G (**22.8×**) | #857 §3.1 |
| sig-F4 pair rejections: product / Koszul / zero-row syzygy / rewrite | 353,641 / 597,883 / 689,359 / 27,951 | 46,183 / 129,273 / 108,247 / 3,293 | 26,177 / 88,498 / 32,474 / 4,577 | #857 §3.1 |
| grobx exact pairing: work with signatures off ÷ on | 6.33× | 8.92× (declared extension) | — | #716 §1, §3.2 |
| grobx default signature run: work | 528.8 M (hands over) | 970.7 M | 166.5 M | #716 §3.1 |

The Katsura-11 rows are at 2³¹−1 or 2⁶⁴−353 for shipping F4 (both give the same counts) and at
Goldilocks for sig-F4 and grobx. These are #857's and #716's rows.

The wall comparison: sig-F4 design 1 (serial) against shipping F4 at 16 workers. `sig_f4_study` was
built at the final `main`, n = 9 (`sigf4-gate.jsonl.gz`).

| Row | design 1 | F4, 1 worker | F4, 16 workers | design 1 ÷ F4-16, final `main` [95%] | at the freeze (#857) |
|---|---:|---:|---:|---:|---:|
| Eco-12 / 2⁶⁴−353 (primary) | 3,625.5 ms | 12,636.0 ms | 2,338.6 ms | **1.550** [1.545, 1.561] | 1.148 |
| Katsura-11 / Goldilocks (second family) | 1,049.2 ms | 9,577.5 ms | 1,342.0 ms | **0.782** [0.774, 0.788] | 0.619 |

Every run's basis equals shipping F4's. Against one-worker F4, design 1 is 0.287× on Eco-12 and
0.110× on Katsura-11, so at equal workers the work saving is real. The S verdict is that sound
criteria remove most of Zeebra's zero-reduction work, and that turning the saving into wall time
needs a signature engine's serial parts parallelized. Those parts are bookkeeping, symbolic
preprocessing, interreduction of a signature basis 2.5× the size of the reduced one, and the
cross-target elimination cascade (#857 §5). Workstream P's speedup of the reference widened the gap.

### 15.5 Success tiers, criterion by criterion (§3, targets as written)

| Tier | Criterion | Status | Evidence |
|---|---|---|---|
| Minimum 1 | M30-0 freezes baseline, protocol, identities | **met** | #855, PR #865, `4f5784c5`; [`m30-protocol.md`](research/m30-protocol.md) |
| Minimum 2 | #716 grobx signature on / off / no-handover ablation with §2.2 quantities, wall, RSS, verification per arm | **met** | PR #867; [`m30-signature-attribution.md`](research/m30-signature-attribution.md), 150 attempts all verified |
| Minimum 3 | M30-S2 RFC with go / no-go | **met**: go, narrowed (Eco-12 primary, `katsura-11` second family) | #856, PR #866; [`signature-f4-rfc.md`](research/signature-f4-rfc.md) §12.1 |
| Minimum 4 | M30-P1 symbolic cost model and Amdahl ceiling | **met** | #859, PR #868; [`m30-symbolic-cost-model.md`](research/m30-symbolic-cost-model.md) |
| Minimum 5 | M30-P2 evaluates ≥1 bounded parallel-interning strategy | **met**: two (serial canonical merge, sharded) | #860, PR #869; [`m30-parallel-interning.md`](research/m30-parallel-interning.md) |
| Minimum 6 | M30-I reproducible decision report | **met**: this section and `research/m30-final/` | #862 |
| Target 1 (P) | a parallel symbolic path passes the §9.4 gate, including ≥10% complete F4 wall on a substantial public benchmark, and ships | **met** | #861, PR #878; re-read in §15.3 (−23.3% Eco-12) |
| Target 2 (S) | a credible, sound reduction in necessary algebraic work, preferably an independent bounded prototype recording reductions to zero and products avoided by sound criteria on ≥1 substantial instance | **met** on work; not shipped | #857: Eco-12 reductions to zero 6,326 → 1,013 and 9.7× fewer products, bases identical; #858 closed not planned |
| Stretch, clause 1 | parity or a reproducible lead over the best comparand on a substantial public benchmark under the same declared compute budget | **missed** | no task at parity. Closest are Cyclic-7 at 1.21× grobx (16w vs 1w) and MQ10/2³¹−1 at 1.39× msolve. At equal workers Zeebra is 2.3–16× behind grobx |
| Stretch, clause 2 | an independently certified algorithmic result that materially moves the work frontier (for example MQ11 work within 3× of grobx's signature run, exactly verified) | **met by the opt-in research prototype, not by shipping code** | #857 design 1 on MQ11 does 1.745 G products against 970.7 M for grobx's default signature run (1.80×) and 1,841.0 M for its exact run (0.95×). Shipping F4 does 20.377 G (21.0×). Its basis digest `ddef89cb` equals the grobx-certified MQ11 basis (§15.2; re-certified in this cohort). Counts are compared as #716 §3.2 compared them: Zeebra coefficient products against grobx `subtracted` charges |

### 15.6 Negative, inconclusive and stopped results

Every attempt below is retained in its evidence directory.

**Stopped at a budget or resource cap.**

1. **Zeebra's own certificate on Eco-12 stopped at the verification budget.** At `4f5784c5`,
   `certify_f4_output` was still checking Buchberger's criterion serially over 743 elements at
   660 s (the 600 s budget plus 60 s grace). No check had failed. MQ11 was not attempted. Neither
   was retried at the final `main`. On the held-out rows the certificate completed. Cyclic-7 took
   2 s. Katsura-11 / 2⁶⁴−353 took 606 s, which is past the declared 600 s but inside the harness's
   660 s stop, and that overrun is recorded rather than rounded away.
   **Follow-up (#887), measured at `9548555d` (tag `measured/887-parallel-certificate`) against
   `b1d8e36a`:** the certificate now prepares the basis's divisors once and runs its reductions on
   the call's workers. With `m29_cost_model --certify --workers 16`, one fresh process each under
   `tools/benchlock.sh` and a 660 s stop, 2026-11-18:

   | row | `b1d8e36a` | `9548555d`, 1 worker | `9548555d`, 16 workers |
   | --- | --- | --- | --- |
   | Eco-12 / 2⁶⁴−353 | stopped at 660 s | stopped at 660 s | 65.5 s, 65.5 s |
   | MQ11 / Goldilocks | stopped at 660 s | not run | 60.8 s, 60.7 s |
   | Katsura-11 / 2⁶⁴−353 | not run | not run | 27.1 s |
   | Cyclic-7 / 2⁶⁴−353 | not run | not run | 0.03 s |

   Each completed certificate passed, on the basis digest recorded in `research/m30-final/`, and
   is reported in `F4Statistics::certification` apart from the solve. Preparing the divisors alone
   is not enough: one worker still stopped at 660 s, so the budget is met by the parallel
   reductions. The certificate is still not bounded by `max_wall_time`.
2. **grobx certified mode on Eco-12 stopped on memory at the declared 8 GiB** (#855): at 94 s, with
   a kernel peak of 8.59 GB and no basis. The one approved retry at 32 GiB admitted it, with 743
   elements, the same digest, 287 s and an 11.4 GB peak. **The cap was raised once, for that row
   only.** This cohort re-ran Eco-12 at the same 32 GiB (admitted again: 743 elements, same digest, 283 s, peak 11.4 GB). No other cap was
   raised, and no other row needed it: MQ11 and both held-out rows were admitted at 8 GiB.

**Gates missed.**

3. **#858 (S4) entry gate missed; closed not planned.** The best design reached 1.010 [1.003, 1.018]
   on Eco-12 against a limit of ≤0.80. The katsura-4 controls' upper bounds were 1.10–1.21 against
   1.05. cyclic-7 ran 5.6–7.0× slower with 3.5× RSS. Both designs the RFC allows were tried, and the
   owner declined a third. At the final `main`, design 1 is 1.550× on Eco-12 (§15.4).
4. **#716 Gate A1 failed on MQ11**: with randomized mechanisms on, the work ratio was 1.69×, below
   the 2× bar. It also failed on every Eco-12 arm except the exact pairing. **Handover was
   net-negative** wherever it fired: MQ10 at both primes (386 against 122 ms, and 175 against 140)
   and Cyclic-7 (120 against 82).
5. **#860's prototypes failed the RSS line** at 1.20–1.31× against 1.15×, which was traced to glibc
   arenas. `MALLOC_ARENA_MAX=1` was not a fix, because it slowed the shipping path 7% on Eco-12.
   #860's wall-time cancellation was not wired; #872 closed that gap.
6. **#861 Step 0: the merged #871 prototype failed the ≤5% small-task line.** At 16 workers,
   Katsura-7 ran 1.330 [1.307, 1.364], Katsura-6 1.163 and cyclic-6 1.068. The fallback threshold
   then went 256 → 512 → `max(512, 48 × workers)`. At 256, Katsura-7 at 16 workers was 1.180. At a
   flat 512, Katsura-8 at 16 workers was 1.064 [1.050, 1.078]. The shipped threshold brings that to
   0.968.

**Approaches that did worse.**

7. **#871's first attempt made memory worse.** Run-long scratch reuse (`--retain run`) measured
   1.16–1.25× RSS, and an earlier unlocked probe with #860's layout read 1.50× on Eco-12. The
   high-water mark is set inside the widest batch's symbolic stage, so any retained scratch adds to
   it.
8. **#860's first `intern` pass** used a 512-seed-row team threshold, and that sent 17 of 23 Eco-12
   batches down the serial path. It is retained as `intern-seed512`.
9. **#827's level-parallel prototype, re-priced by #859**, sped the stage up 1.17–2.01× at 16
   workers but slowed it to 0.56–0.71× at one. That is −3% to −16% of process wall. Parallel
   interning superseded it.
10. **#857 design 2** pre-reduced against the reducer block in parallel. Elimination fell from
    1.70 to 1.22 s, but products rose from 0.611 to 0.743 G. It parallelized the wrong half: the
    cross-target cascade stays serial.

**Errors found and corrected.**

11. **RFC rewrite order.** Taking the least sig-lead ratio lost pairs on katsura-4 (red test,
    `2d589a80`). The canonical rewriter takes the greatest ratio.
12. **#716's pilot.** 11 of its 30 attempts failed on a ledger decoder bug in the study, not in
    grobx. It is retained as a diagnostic.
13. **#883.** The adapters and three instruments did not cap the symbolic team (see the top of
    §15). #884 fixed it, and no published row is affected.

**Inconclusive or unexplained.**

14. **#855's drift against M29.** 15 of 46 cells were slower than M29's intervals. The cause is
    compiler overlap on unreserved CCDs (56% of children, against 6% in M29) and the package power
    budget. The drift is not folded into any figure.
15. **One-worker drift between the freeze and the final `main`, unexplained.** At one worker both
    builds run the serial closure. Even so, process wall is 0.975–0.993× on six of the seven targets
    (MQ10/32003 is 1.000). Yet the serial symbolic stage is 1.035× [1.031, 1.049] on Eco-12 and
    1.011× on MQ11. The suspects are the other source changes between the two commits. This is
    #890. **Attributed** ([`m30-one-worker-drift.md`](research/m30-one-worker-drift.md)): a
    per-commit bisect puts the Eco-12 step at #878 (`d6aa0526`, 1.026–1.035× in three runs). There,
    process wall is unchanged and the serial closure's source is untouched. Forcing the closure
    inline does not recover it. MQ11's +1.1% does not reproduce. The effect is code placement and
    does not matter.
16. **Not attempted.** #857's open questions 1 (displacement scaling) and 4 (Hilbert-series check),
    and the RFC §6.1 item 2 displacement design, which would have been the third design.

### 15.7 Issue dispositions

| Issue | Disposition |
|---|---|
| #855, #856, #716, #859, #860, #857, #871, #872, #861 | closed, completed |
| #858 | closed, not planned (gate missed; item 3) |
| #832 (P0 anchor) | **closed, completed.** Its condition was parallel interning that passes ~1.5×. In the final cohort the stage runs 3.9× faster on Eco-12 and 4.4× faster on MQ11 at 16 workers, and the shipped default takes 19–23% off complete F4 |
| #883 | found and fixed during this closeout (#884) |
| #862 | closed by this report's PR |
| #854 | closes after that PR merges |

### 15.8 Follow-ups (Project #7, sub-issues of #854)

| Issue | Priority | What |
|---|---|---|
| #886 | Medium | the library default's `Auto { max_workers: 16 }`, forward and symbolic, does not clamp to `available_parallelism()`; measure what oversubscription costs, then decide |
| #887 | Medium | Zeebra's own certificate cannot finish Eco-12 in 600 s, and took 606 s on Katsura-11; wide-field verification still rests on grobx certified mode, which needs 32 GiB on Eco-12 |
| #888 | Medium | symbolic preprocessing after #861: the caller's stitch and the merge walk are the serial remainder; the stage is still 19–21% of MQ10's 16-worker wall, and Cyclic-7 gains nothing. Split by component in [`m30-symbolic-remainder.md`](research/m30-symbolic-remainder.md): stitch and merge walk together are 6.6% of MQ10's F4 call, the seed step and the solo steps are larger, and no target cleared the bar |
| #889 | Low (`opportunity`) | signature F4 beyond M30: what turning #857's 9.7–22.8× work saving into wall time would take (the cross-target cascade, parallel bookkeeping and interreduction) |
| #890 | Low | attribute the one-worker drift between `4f5784c5` and `e4826153` (item 15). Done: #878, code placement, immaterial ([`m30-one-worker-drift.md`](research/m30-one-worker-drift.md)) |
| #891 | Low | `batch_order_study`, `parallel_forward_study` and `mq10_profile` still inherit the 16-thread symbolic team |
