# M35 — Exact Finite-Field Competitiveness at One Worker

**Status:** planned, 2026-11-25. No measurement has been run. §§1–16 are fixed before measurement;
the gates in §9–§10 may be revised on the tracker only before the reading they govern.
**Predecessor:** M34 — Generalizable Algorithm Selection and One New Competitive Regime
([`MILESTONE-GENERALIZABLE-SELECTION.md`](MILESTONE-GENERALIZABLE-SELECTION.md); tracker #1043,
report #1046).
**Planning base:** `main` at `aa50a509` (2026-11-25, after #1158). The engine sources are
unchanged from `a980b6c5`; #1158 records only the benchmark-calibration sign-off.
**Competitor:** grobx v0.155.1, `8005a2a1670a7264617a6f49eeb2618d7fa21701`, unmodified.
**Measured at:** not measured here. Every figure below is quoted from the issue, PR or research
document named beside it, and is evidence for a hypothesis, never an M35 finding.
**Tracking issue:** [#1161](https://github.com/mfaulk/zeebra/issues/1161).
**Project:** [Zeebra #7](https://github.com/users/mfaulk/projects/7); label `M35`. Priority is the
Project field. A dependent issue carries `blocked` until its prerequisite posts its evidence.
Milestones are labels and documents, not GitHub milestone objects.

**Focus.** M34 found no selection headroom and no confirmed competitive class. M35 stops choosing
between existing engines and instead improves them: it turns the strongest unfinished engine
work into measured one-worker competitiveness with grobx on useful prime-field computations,
without weakening Zeebra's exact correctness contract.

## 1. Vision and executive summary

> **M35 — Exact Finite-Field Competitiveness at One Worker.** Freeze a fresh baseline and measure
> the remaining one-worker gap to grobx. Qualify exact certified zero skipping, carrying useful
> signature work into conventional F4, and narrower matrix storage. Qualify the small-prime lane's
> dispatch. Finish one structural feasibility decision. Integrate only what survives its own gate
> and confirm it on untouched work.

The primary result is the **complete reduced Gröbner basis at one worker**. Multi-worker latency,
lex conversion and finding a point are valuable results with their own scores (§8.1); none of
them can stand in for the primary score.

The central bet is specific: exact zero-work avoidance (B), retaining useful intermediate algebra
(C) and reducing matrix storage traffic (D) can close a meaningful part of the remaining one-worker
gap. The gates decide whether those mechanisms produce a competitive solver on useful workloads.
A reproducible negative answer is a valid outcome (§10, *research delivered*).

M35 reuses five open research issues as work-package anchors (#1080, #1076, #1078, #1123, #1034)
and keeps their native parents. It adds only a tracker (#1161), a baseline/attribution package
(#1162) and an integration package (#1163).

## 2. Planning base and audit

**Milestone number.** No `M35` label, document or issue existed at `aa50a509` (`git grep M35`
matches nothing; the label was created with this plan).

**State of referenced work at planning time** (read from GitHub on 2026-11-25):

| Work | State | Consequence for M35 |
|---|---|---|
| Same-degree signature reducers, PR #1139 | merged | Reducer rows can become targets inside the same signature-degree batch; affects grevlex too. Large-row performance not freshly qualified. **Rebaseline before reading old signature costs.** |
| Graded-lex completion, PR #1150; #961 | merged; #961 closed with conventional-F4 routing as the final disposition | Preserve that routing. Reuse #1150's exact completion argument as infrastructure for C (a distinct grevlex experiment). |
| Hairer attribution, PR #1146 | merged | The forced-signature pathology is signature-degree work plus an oversized signature basis; linear substitution did not cure it. Do not repeat the diagnosis; Hairer is not an easy forced-engine speedup target. |
| WorkerCrossover, PR #1115, PR #1147 | narrowing merged; a further term-count rule failed held-out (53/60 cells against 90%, four violations beyond 1.25×) | Preserve the accepted narrowing. No fresh global selector, no removal of the band. |
| FGLM planner, PR #1126 | merged | Strategy-aware admission above the classical envelope is part of the baseline. |
| Direct grobx lex, PR #1131 (#1127) | merged | The driver exposes forced F4-lex, which defeats the earlier radical-chain candidate. Every lex claim uses the faster applicable grobx route. #1143's prerequisite is met. |
| Refusal fallback, PR #1152 | merged | Never fired on the 14 new rows: no out-of-sample evidence. Negative disposition retained. |
| Sparse-toric and M5GB screens, PR #1155, PR #1153 | merged | No eligible competitive route for the intended cohort. No new toric or M5GB backend. |
| GF(2) point-solving screen, PR #1157 | merged; opened #1156 | A counted model only; no crossbred speedup measured. Optional, separately scored (§6.3). |
| Calibration sign-off, PR #1158 | merged | Protocol accepted: ±4% 16-worker A/A band, n = 30, restrictions on the memory-traffic control. The deciding calibration (#1107, PR #1160) is still separate work. Approval of the protocol does **not** qualify concurrent measurement. |
| #1080, #1076, #1078, #1123, #1034 | open, unclaimed | Reused as B–F. |
| #1036 | open, `blocked` | Its feature dependency is now available; it stays an alternative to F (§7.6), not an M35 deliverable. |
| #1143 | open | Its blocker (#1131) merged; moved into M35 as optional (§6.3). |
| Open PRs | #1160 (calibration campaign), #1159 (M4GB counters) | Neither touches an M35 file. |

M34's general-selector **Gate H is a no-go** ([findings](research/m34-selection-findings.md)). That
result does not rule out improving the engines, or a cheap decision inside one elimination kernel
(E).

## 3. Objective and success criteria

**Primary objective:** make exact Zeebra competitive with the fastest eligible, unmodified grobx
v0.155.1 route on important prime-field Gröbner-basis problems, with reproducible evidence beyond
the instances used to tune the implementation.

For a matched input, characteristic, variable order, monomial order, output contract and resource
envelope:

> `R = Zeebra complete-task time / grobx complete-task time` (lower is better).

Primary comparisons use **one worker on each side**. grobx computes on one thread even when its
thread allowance is larger. grobx's default may skip zeros probabilistically (§4.4); Zeebra's
stronger guarantee is retained and stated beside every comparison. grobx with its exact checker is
reported separately (§8.1). The contracts are those of
[`adaptive-selection-contracts.md`](research/adaptive-selection-contracts.md).

The four outcomes, each scored by #1163 (§10):

| Outcome | Required evidence |
|---|---|
| **Research delivered** | #1162 and #1163 complete, and each mandatory experiment (B–F) has an evidence-supported adopt, defer or reject disposition; all counts, measurements, provenance and negative results retained. Unperformed necessary work is scored *research incomplete*. Research delivery alone is not a competitive success. |
| **Core improvements qualified** | At least two independent input families improve by ≥ 1.15× over the frozen best qualified Zeebra baseline, upper 95% bound on the time ratio < 1, and all correctness, resource and regression gates (§9) passed. |
| **Competitive target achieved** | Each of two predeclared regimes from distinct input lineages independently has geometric-mean `R ≤ 1.05`, upper 95% timing bound ≤ 1.10, and every declared scale's median `R ≤ 1.10`. Aggregate by base problem, with seeds, characteristics and derived presentations nested under their lineage. Each regime has ≥ 2 nontrivial scales and fresh support or presentation variation. At least one regime has a public application-derived input family. Two characteristic variants of one generator are not two regimes. |
| **Competitive stretch achieved** | One qualifying regime has geometric-mean `R ≤ 2/3` and upper 95% bound < 0.75, with no contributing scale's median above 1 — a reproducible 1.5× class advantage. |

The decisive regimes contain problems whose frozen reference computation takes roughly
**1–300 seconds**. Small controls remain mandatory but do not establish an important competitive
regime. A larger completion frontier under the same budgets is reported separately; a timeout is
never converted into an invented speedup.

## 4. What grobx v0.155.1 teaches

The release reports 1.43× faster prime-field calls and 27% less peak memory over 58 instances
relative to 0.73, and 43.8× faster GF(2) with 79% less peak memory over 16 instances relative to
0.101 ([release](https://github.com/code1-de/grobx/releases/tag/v0.155.1)). These are cumulative
upstream self-comparisons. M34 already used v0.155.1, so they are neither a newly raised competitor
baseline nor predicted Zeebra gains.

Source links below are pinned to `8005a2a1`. Zeebra re-derives mechanisms from their description
and papers under [`external-provenance-policy.md`](research/external-provenance-policy.md); no
grobx code is copied.

### 4.1 Useful work retained across engine changes

grobx observes signature-degree gaps, zero yield, dominated new leads and pair-update work. When
signatures stop paying it can switch to plain F4 and carry useful elements into a compact new
table. Its completed-degree pair omission has a subtle degree boundary, including a possible
adjustment from d to d−1 ([`src/f4.rs`](https://github.com/code1-de/grobx/blob/8005a2a1670a7264617a6f49eeb2618d7fa21701/src/f4.rs)).
This makes **exact carry, separate from the switching rule**, a strong experiment (C). It does not
establish that grobx's thresholds transfer to Zeebra.

### 4.2 Fewer coefficient copies and narrower column arrays

A symbolic matrix row reads coefficients from its source basis element and stores its column
positions separately. A flat column array uses u16 indices through 65,536 columns and u32 beyond
([`src/matrix.rs`](https://github.com/code1-de/grobx/blob/8005a2a1670a7264617a6f49eeb2618d7fa21701/src/matrix.rs),
[`src/columns.rs`](https://github.com/code1-de/grobx/blob/8005a2a1670a7264617a6f49eeb2618d7fa21701/src/columns.rs)).
This can cut allocation and memory traffic before elimination and supports separate representation
ablations (D, #1078). Source-backed coefficients predate v0.155.1; narrower per-matrix indices are
newer.

### 4.3 Arithmetic changes at meaningful characteristic boundaries

grobx's prime-field path is not one uniform modular loop
([`src/field.rs`](https://github.com/code1-de/grobx/blob/8005a2a1670a7264617a6f49eeb2618d7fa21701/src/field.rs)):

- odd primes below 2^31 store u32 coefficients in i64 accumulators;
- below 2^16 it accumulates products without modular reduction until the pivot scan; at larger
  31-bit primes it keeps a bounded redundant accumulator;
- the 64-bit path uses Shoup-style row multiplication below 2^63, with a cheaper redundant range
  below 2^62, and u128 remainder products above 2^63;
- four-row bands use SSE2 where eligible.

The diagnostic **characteristic ladder** is therefore 2, 31, 32003, 65521, 2^31−1, a validated
prime near 2^61, and Goldilocks — in representative subsets, not a Cartesian product. 65521 is
inside grobx's fully delayed path but outside Zeebra's lane (`MAX_LANE_PRIME = 46_337`,
`src/linalg/lane.rs`). Whether a wider Zeebra accumulator pays is a hypothesis admitted only after
#1162 measures the residual gap (§7.5).

### 4.4 Default performance includes probabilistic work avoidance

Conventional grobx F4 can reduce random combinations of row blocks at p ≥ 46341. Signature runs
can test groups at p > 3; GF(2) has a 128-bit sketch path
([`src/matrix.rs`](https://github.com/code1-de/grobx/blob/8005a2a1670a7264617a6f49eeb2618d7fa21701/src/matrix.rs),
[`src/sketch.rs`](https://github.com/code1-de/grobx/blob/8005a2a1670a7264617a6f49eeb2618d7fa21701/src/sketch.rs)).
The source's local test bounds do not establish a whole-call error bound. A fixed seed reproduces a
run but does not change its mathematical guarantee.

Requesting grobx's exact checker also requires cofactor tracking and **changes the route**: input
preprocessing, handover, bands and packed reduction can be disabled alongside random skipping
([`MANUAL.md`](https://github.com/code1-de/grobx/blob/8005a2a1670a7264617a6f49eeb2618d7fa21701/MANUAL.md)).
Default-versus-checker time therefore does not isolate the cost of probability. Acceptance uses
the unmodified release. Diagnostic overlays may disable one mechanism at a time and must identify
their own source, binary and changed behaviour.

### 4.5 GF(2) and bookkeeping need whole-pipeline attribution

grobx combines residual packing, table-based back-substitution, cheap pair criteria, specialised
matrix construction and runtime engine changes
([`src/packed.rs`](https://github.com/code1-de/grobx/blob/8005a2a1670a7264617a6f49eeb2618d7fa21701/src/packed.rs)).
Zeebra already ships residual packing and Four Russians back-substitution
([`gf2-residual-packing.md`](research/gf2-residual-packing.md)). Generic four-row reuse already
failed its Zeebra integration case: 2.47× fewer pivot reads gave about 2% wall
([`multirow-reuse.md`](research/multirow-reuse.md)). M35 looks at the remaining work, not another
implementation of those kernels.

Constructing fewer pairs before allocation, support-indexed divisor lookup, bounded linear
substitution and selective tail interreduction
([`src/pairs.rs`](https://github.com/code1-de/grobx/blob/8005a2a1670a7264617a6f49eeb2618d7fa21701/src/pairs.rs),
[`src/divisors.rs`](https://github.com/code1-de/grobx/blob/8005a2a1670a7264617a6f49eeb2618d7fa21701/src/divisors.rs),
[`src/substitute.rs`](https://github.com/code1-de/grobx/blob/8005a2a1670a7264617a6f49eeb2618d7fa21701/src/substitute.rs))
are candidates only if #1162's profile identifies their cost. Persistent monomial tables,
column-space interreduction, fewest-terms selection and adjacent-row reuse overlap completed Zeebra
work. Upstream use does not invalidate Zeebra's negative experiments.

## 5. Claims kept apart

1. **Internal gain:** a Zeebra configuration beats the frozen best qualified Zeebra baseline.
2. **Competitive ratio:** Zeebra at one worker against grobx at one worker (§8.1).
3. **Other scores:** multi-worker latency, throughput, memory frontier, lex pipeline, one point.
4. **Adoption:** a change is safe and qualified to ship (§11).

Evidence for one never establishes another. An internal 1.15× is not a grobx ratio; a 16-worker
win is not a one-worker score; a memory frontier is not a speedup.

## 6. Scope

### 6.1 Committed (mandatory for *research delivered*)

- **A** (#1162): baseline, panel, gap table, priced manifest.
- **B** (#1080): qualify the implemented certified zero-skipping route.
- **C** (#1076): carry versus restart at a signature → conventional F4 switch.
- **D** (#1078): the four-arm representation ablation.
- **E** (#1123): conversion-aware lane dispatch.
- **F** (#1034): the remaining bilinear counts and the feasibility decision.
- **G** (#1163): integration, untouched confirmation, report.

Each of B–F ends in adopt, defer or reject with evidence. *Defer* at the budget cap is a valid
disposition; an unexecuted mandatory gate is not.

### 6.2 Conditional (gate-controlled)

- **F prototype:** one bounded structural computation, only after F's count gate passes and only
  with time reallocated from a stopped package (§7.6). #1036 is the alternative if #1162 finds a
  meaningful public workload for it. Never both.
- **Design R** under #1080: only if D misses its gate and a credible exact acceptance/recovery
  design exists. Failure of D does not authorise Monte Carlo defaults.
- **Wider delayed accumulator or explicit SIMD** for the lane: only if #1162 finds enough residual
  arithmetic cost and the design differs materially from rejected #715.
- **One GF(2) pipeline replacement experiment:** only if the affected phase passes #1162's headroom
  criterion, and only in place of a stopped package.

### 6.3 Optional, separately scored

These cannot satisfy the M35 Gröbner-basis target and are not free additions to the budget (§12).

- **#1156 GF(2) point solving.** Preserve its sequence: bitsliced Gray-code enumeration, then
  bounded crossbred preprocessing, tested on planted and unplanted MQ. Keep its ≥ 10× complete-task
  gate against the best Zeebra GF(2) configuration (hybrid included) at the declared worker counts.
  Its modelled 305–319× margins are not implementation results. A claim against grobx first needs a
  correct, fully charged point-extraction pipeline around grobx's basis output; equal one-point
  tasks; explicit field equations; and a complete proof before returning *none*.
- **#1143 nonradical box-staircase lex.** Its forced-lex prerequisite (#1131) has merged. Keep its
  own development and untouched support/size gates, against the faster grobx route with all
  conversion and checking costs. The earlier radical rows stay adverse controls. Its M34
  confirmation package has closed; this continuation is M35's, not a retroactive M34 result. It is
  an artificial family until a meaningful outside instance appears and cannot be the
  application-derived regime of §3.

### 6.4 Excluded

- a new global selector program; #1135, #1141 and #1151 stay follow-ups, revisited only after C, D
  or E changes a routing boundary's cost and fresh evidence justifies it;
- toric or M5GB backends; another M4GB attempt;
- reimplementing residual packing, Four Russians or generic multirow / adjacent-round reuse;
- Monte Carlo or otherwise weakened-guarantee defaults;
- re-diagnosing Hairer; signature routing for graded-lex;
- whole-library representation redesign (#268 stays the epic);
- private or attack-specific workloads.

## 7. Work packages

### 7.1 WP A — freeze the baseline and identify the remaining work (#1162)

**Priority: first.** Reuse the existing harness and comparison contract.

Freeze Z0 from current `main` after auditing changes since `aa50a509`. Z0 includes #1139, #1150,
#1115, the planner fix (#1126) and the forced grobx lex driver (#1131). Verify feature paths,
safety tests and comparator build identities before timing. M33 and M34 profiles are hypotheses to
recheck.

A compact panel with three purposes:

1. **Competitive targets.** Dense and sparse MQ, mixed-degree structured systems, a genuinely
   application-derived public family, and GF(2) systems. Favour 1–300 s work, include ≥ 2 scales,
   and state why each family matters. Reuse meaningful public families M34 admitted
   ([panel](../research/m34-public-corpus/README.md)); do not manufacture importance from a large
   variable count.
2. **Adverse controls.** Cyclic, Katsura, Eco, low-term MQ, degree-fall cases, small sparse rows,
   and any earlier failed control a candidate affects.
3. **Frontiers.** Sizes refused under default limits, and sizes admitted under a separately declared
   research envelope. Report both.

At least one third of the target panel lies in the 1–300 s band. Seeds, characteristic variants,
transformed presentations and size rungs are grouped by lineage. Development, validation and
untouched confirmation stay distinct. M34's sealed cohorts stay sealed unless explicitly allocated
to G's confirmation protocol before any result is inspected.

Records: complete-task wall and peak RSS, plus diagnostic phase times and counts — symbolic
construction, coefficient/index copying, forward reduction, zero-producing work, signature/pair
bookkeeping, final interreduction, serialization. For grobx, the actual engines, handovers, field
representation and random-reduction modes. Passive counters must not change the path; grobx
tracing and checker modes are not passive.

**Exit:** a current gap table naming the cost each candidate can plausibly remove, a declared
target panel, and a priced manifest of rows × arms × repetitions plus harness overhead. The
secondary exact-checker panel is priced separately and need not duplicate every default cell. A
conditional new mechanism needs ≥ 20% of current solve time in its affected phase, or a concrete
fixed-budget completion limitation. An operation-count reduction is evidence of mechanism, not a
speedup promise. Stop once panel and attribution are adequate — not another 7,000-attempt
selector campaign.

**Status (#1162):**
- **Done.** Z0 is frozen at `125658bb`. The panel, the development-mode gap table and the priced
  manifest are in [`research/m35-baseline.md`](research/m35-baseline.md).
  - B, C (narrowly) and E clear the 20% rule.
  - D's copying share does not.
  - F has no evidence in this panel.
- **Outstanding.** The publication-mode read of the manifest, about 3.5 h.

### 7.2 WP B — qualify the implemented exact zero-skipping route (#1080)

**Priority: first bench-host opportunity.**

Design D exists as `HilbertSelection::CertifiedZeros { slack }` (#1087), with the later affine
proof extension; proof and scope in [`hilbert-count-acceptance.md`](research/hilbert-count-acceptance.md).
The remaining work is the bench-host gate, the slack sweep and controls
([status](https://github.com/mfaulk/zeebra/issues/1080#issuecomment-7090206762)). Use the current
implementation; do not rebuild it.

Develop slack choices on exposed rows, freeze one rule, then compare against the best qualified
Zeebra route (signature F4 included) and default grobx at one worker. Include dense square MQ over
wide primes, fresh supports and scales. Retain Eco-12, Katsura-11, sparse MQ10 and Cyclic-8 as
controls (slack 0 is known to over-split Katsura-11). Measure oversplitting, skipped-pair counts,
Hilbert-series cost and all conversion/certification overhead.

Count equality must cover the required prior degrees. Affine certified-degree pair drops and final
zero-count completion have different hypotheses; preserve the proved scopes. This does not certify
a signature prefix or permit invented syzygies.

Gate: §9.2.

### 7.3 WP C — carry useful signature work into conventional F4 (#1076)

**Priority: main new algorithm experiment.**

Target grevlex inputs on which signature work begins productively but later spends too much on
dominated elements or on proving completion. #1146 supplies a mechanism, but Adaptive already
avoids Hairer; C must beat the best available entry route on other useful inputs. Cyclic-like
families are development candidates; Eco is an early-switch control; regular MQ and Katsura are
stay-in-signature controls.

Five arms:

1. current Adaptive;
2. pure conventional F4;
3. pure signature F4;
4. **restart** conventional F4 from the original input at the boundary;
5. **continue** conventional F4 from a carried prefix at the same boundary.

Measure carry's intrinsic value first (4 vs 5 at fixed boundaries); only then fit a small online
boundary rule from degree gaps, dominated leads, zero yield or pair work.

Correctness reuses #1150's argument: original inputs plus polynomial combinations of them generate
the same ideal. Initially rebuild all ordinary pair obligations. Dropping obligations by a completed
degree is a separate proof task covering degree falls, partial batches and ties. A quiet lead set is
a cost signal; conventional F4 must still establish completion. Do not repeat the stand-alone
Buchberger certificate #1150 rejected.

The existing grlex helper is not a general handover framework. Propagate workers, row/column/
live-memory limits and remaining wall budget explicitly; charge prefix, conversion, re-entry and
final reduction together; avoid holding two large engine states; keep current error semantics and
cancellation behaviour.

Gate: §9.3.

### 7.4 WP D — reduce matrix copying and storage traffic (#1078)

**Priority: parallel with C after A.**

The four-arm design: current representation; source-backed coefficients for immutable reducer
rows; u16 batch-local indices; both. Materialised new pivots remain owned. Use a separated layout
where required: `(u32, u64)` → `(u16, u64)` does not shrink a 16-byte aligned tuple.

Keep ordering, rows, pivots and polynomial arithmetic fixed for the initial ablations. Measure
build time, coefficient bytes copied, allocated capacities, live copies, index bytes, indirection
cost, final reduction, full solve and peak RSS. Include small, 31-bit and wide primes; a BN254
control is Zeebra-only. Test 65,535, 65,536 and 65,537 columns, widening, sentinels and transient
conversion peaks.

This is a bounded representation experiment — not a library redesign, and not a repeat of the
rejected generic multirow or adjacent-round caches.

Gate: §9.4.

### 7.5 WP E — make the small-prime lane pay after conversion (#1123)

**Priority: qualify the retained kernel.**

The lane delivered 2.81–3.01× full-solve gains against Zeebra at 16 workers on its dense rows, but
failed short sparse controls and remains opt-in
([measurements](../research/945-lane-kernel/README.md)). These are not equal-worker grobx gains. E
is net conversion-aware dispatch, with one-worker competitive attribution added.

Separate conversion, setup, reduction and output conversion. Compare a conservative threshold with
a small cost model over cheap batch properties only — dimensions, active spans/density, predicted
work, worker count, memory. Account for sparse rows that densify. Prefer the simple rule when its
complete-task performance is comparable.

Eligibility stays `p ≤ 46337`. 65521 is a diagnostic boundary, not an implicit scope expansion. A
lane dispatch rule is independent of the selector M34 rejected.

Gate: §9.5.

### 7.6 WP F — finish one structural feasibility decision (#1034)

**Priority: bounded conditional research.**

The bilinear generator, exact multigrading verifier and matrix census are merged. On balanced
affine instances the median largest-matrix-to-largest-block factor S is 14.96 over 36 instances
(5×5 and 6×6), and the median degree-drop share is 0.702 over 18 instances, all 5×5 (max 0.749)
([findings](research/bilinear-feasibility.md); #1034, PR #1112). Every 6×6 control and all affine
7×7 and 8×8 exceeded the live-entry budget on the development machine. This is counting evidence,
not a 15× solver improvement.

Complete the larger controls and comparator arms with declared budgets on the bench host. Register
reproducible inputs with lineage and characteristic-independent integer support where appropriate.

Only after that decision, and only with time reallocated from a stopped package, attempt one
bounded correct computation exploiting the multigrading. On homogeneous inputs the degree blocks
separate; on affine inputs the census duplicates monomials and does not prove the blocks can be
solved independently. Charge homogenisation, additional work, dehomogenisation and conversion to
the requested reduced basis of the original ideal, and prove the construction before claiming its
cost.

#1036 (exact disjoint components) is the alternative if #1162 finds a meaningful public workload;
its existing ≥ 1.5× against both comparators and < 1% detection-cost criteria stand. Do not run two
structural implementations merely to win on constructed easy families; the generic product
criterion may already remove most cross-component work.

Gate: §9.6.

### 7.7 WP G — integrate and qualify on untouched work (#1163)

**Priority: mandatory closing package.**

Merge only individually justified changes into one final candidate **ZF**. Rebaseline any touched
route when an earlier merge changes its cost. Re-measure the combination; never multiply speedups
from different commits, hosts, sessions or thread counts.

Run the correctness suite across every claimed field/order at one and at the maximum supported
worker count. Verify returned reduced bases against independent references on every completed
scored row. Independent validation is recorded separately from timing; certification or recovery
that a candidate's exact algorithm requires belongs inside its complete-task time. Verify the
mathematical invariant behind each optimization; a matching digest is validation, not proof. Trip
wall, matrix, memory, cancellation and worker caps, including transitions and fallbacks. Check
typed failures and the total cost of discarded work.

Freeze the final route and rule **before** opening untouched confirmation data. Run controls and
claimed regimes under one retained protocol. Record individual ratios, family-weighted aggregates,
variability, peak RSS, failure/refusal outcomes and actual route. Evaluate the frozen
implementation a user can call; a per-instance oracle is diagnostic only.

The report (§18) scores every outcome of §3 and publishes each claim's scope (§5).

## 8. Measurement and comparison rules

### 8.1 Comparable tasks

| Score | Required output and comparison |
|---|---|
| **Primary Gröbner-basis score** | Complete canonical reduced basis of the same original ideal and requested order. Zeebra at one worker versus grobx's actual one worker. |
| Exact-guarantee comparison | Zeebra deterministic or exactly certified route versus the separately labelled grobx exact-checker route, each with its verification costs. |
| Machine-latency score | Zeebra at a declared worker cap versus grobx at its actual one worker. Both counts displayed. |
| Throughput, if useful | Equal total core allotment; independent grobx processes allowed for a batch of independent inputs. Not the latency score. |
| Lex score | Entire input-to-lex pipeline: preprocessing, grevlex, change of order, checking, fallbacks, output. grobx automatic and forced F4-lex routes both measured. |
| One-point score | One point verified in the original generators, with all guessing, preprocessing, failed attempts and extraction charged. An exact *no solution* needs a complete argument or exhaustive search. |

Measure the current grobx default and a public grobx route frozen per regime on development data;
report both if they differ. For lex, also retain the predeclared per-instance minimum of automatic
and forced F4-lex as a conservative comparator envelope: a lex competitive claim must beat it, but
it is not described as one callable route. Likewise report the frozen callable Zeebra baseline
separately from the best qualified per-instance Zeebra envelope; issue gates that require "the best
qualified configuration" use the stronger envelope. BN254 and extension fields have no direct grobx
comparator through this release's interface.

### 8.2 Controls and uncertainty

- Fresh processes; paired, interleaved arms on the same pinned hardware in the same session.
- Development, counts and correctness work may run concurrently under their permitted modes.
  **Deciding timings** follow the current publication rules
  ([`benchmarking.md`](guide/benchmarking.md), [`tools/bench-job`](../tools/bench-job)): exclusive
  benchmark lock, machine-wide compiler/runner/background-load refusal, solver CPUs pinned to a CCD
  reservation, a control CPU left for monitoring where needed. Reserve publication windows only when
  an experiment is ready. A concurrent mode may replace this only after #1107's calibration
  qualifies it for that type of claim.
- **9 clean paired repetitions** by default. Predeclare a smaller count for long or frontier rows;
  insufficient precision is *inconclusive*. Any extension rule and maximum count is fixed before the
  read. Interrupted and contaminated attempts are preserved in the record.
- Timing intervals come from paired repetitions within fixed instances, propagated into the
  declared aggregate. The number of independent lineages is reported separately; seeds, field
  variants and two size rungs do not establish population-level confidence. Family-cluster intervals
  only when enough independent families support them.
- #1107's calibration keeps its accepted n = 30; M35 does not revise that protocol.

### 8.3 Envelopes and accounting

- Ordinary targets start in the existing 300 s, 16 GiB research envelope. A larger frontier envelope
  is declared before timing. Every row shows whether it needs Zeebra's shipping internal limits
  raised; a larger allowance is never credited as an algorithmic improvement.
- Complete-task time includes route decisions, failed probes, conversion, required certification,
  final interreduction and serialization. Library-call and process totals are reported separately,
  never mixed.
- Small-process measurements use the established harness with explicit absolute overhead reporting
  so timer granularity is visible.

### 8.4 Splits

Development, validation and untouched confirmation are distinct per lineage. A package may tune
only on development rows. No package tunes on confirmation data, and G opens it once, after ZF is
frozen.

## 9. Numerical gates (pre-declared)

### 9.1 Common default-adoption gate

For any change proposed as a default:

- upper 95% candidate/baseline wall ratio ≤ 1.05 on designated adverse controls;
- no wrong output; no new unsupported behaviour; budgets and cancellation preserved;
- peak RSS ≤ 1.15× unless the anchor issue specifies a stricter limit (the stricter one applies);
- a capacity-oriented exception must be declared in advance, never excused after a failed result.

### 9.2 B — certified zero skipping (#1080)

- ≥ 1.15× complete-task gain against the best qualified Zeebra configuration on each gated row, with
  #1080's stricter no-regression-beyond-noise requirement on its controls. §9.1's 5% control
  allowance does **not** replace it.
- The numerical equivalence and uncertainty treatment of "beyond noise" is fixed on #1080 before the
  deciding read, using §8.2.
- The grobx ratio is reported even if the internal gate passes.
- The gain is reproduced on a held-out scale and support before the route is selected
  automatically.

### 9.3 C — carry (#1076)

- ≥ 1.15× faster than the best qualified Zeebra entry route on two declared scales, upper 95%
  time-ratio bound < 1, with fresh family/support confirmation and §9.1's controls.
- Carry versus restart is reported to explain the mechanism.
- If carry beats only a pathological forced-signature run, reject it as a competitive improvement.
- If switching helps but carrying does not, retain the simpler measured alternative.

### 9.4 D — representation (#1078)

- **Speed:** ≥ 1.10× complete-task gain on a declared nontrivial regime, upper 95% time ratio < 1,
  and §9.1.
- **Memory alternative** (separately labelled): peak live storage cut ≥ 20%, ≤ 3% complete-task
  wall added, and a previously refused declared case completed at an identical budget. A
  memory-only result cannot satisfy any speed outcome.
- Each component is rejected independently if unhelpful; combined adoption follows the factorial
  evidence, not additive guesses.

### 9.5 E — lane dispatch (#1123)

With field-route time F, always-lane time L and dispatched time D:

- on each eligible dense target, `D ≤ L + 0.10(F − L)` (retain ≥ 90% of the lane's saving);
- upper 95% ratio to the field route ≤ 1.05 on short and sparse controls;
- full correctness and the existing lane memory limits;
- unseen small/intermediate rows, supports and scales added; passing the original failed controls
  alone is insufficient.

### 9.6 F — structure (#1034)

- **Count gate** (unchanged from #1034): median split factor ≥ 2 and degree-drop share < 0.75, with
  evidence at more than one balanced size.
- **Prototype gate, if opened:** #1034's own ≥ 1.3× complete-task gate on a held-out block ratio,
  recorded as-is. M35's additional competitive gate is ≥ 1.5× against both the best qualified Zeebra
  configuration and the fastest eligible grobx route, on two scales and new supports, with §9.1.
  The two are recorded separately; the old gate is not rewritten.
- If only the census is favourable, F closes as *feasibility delivered, solver advantage unproven*.

### 9.7 Optional packages

#1156 and #1143 keep the gates stated on their issues (§6.3).

## 10. Success tiers (fixed now; scored by #1163)

| Tier | Definition |
|---|---|
| **Research delivered** (Minimum) | §3 row 1. |
| **Core improvements qualified** | §3 row 2. |
| **Competitive target** (Target) | §3 row 3. |
| **Competitive stretch** (Stretch) | §3 row 4. |

If the performance gates fail but mandatory research is complete, M35 is scored *research
delivered, competitive target missed*, with the remaining gap explained. Otherwise the report names
which research is incomplete.

## 11. Adoption

A research gate (§9.2–§9.6) establishes an internal or competitive claim; it does not change a
default. A default changes only when its change passes §9.1 on ZF in #1163, with the anchor issue's
stricter limits. Opt-in capabilities that pass their research gate but not §9.1 stay opt-in and are
documented as such.

## 12. Budgets and stopping rules

### 12.1 Package budgets

Elapsed benchmark-session hours, including harness time (not CPU-hours):

| A | B | C | D | E | F | G | Total |
|---|---|---|---|---|---|---|---|
| 6 | 4 | 8 | 6 | 4 | 4 | 8 | **40** |

Publication portions need the existing quiet-window conditions until a concurrent mode qualifies.
#1158's pilot found 1.4–1.9 s of harness overhead per attempt; estimate each session from actual
attempted rows and repetitions before reserving time. One 300 s instance with five arms and nine
repetitions already costs 3.75 h before harness and validation, so use a few representative long
rows and broad cheap controls, with repetition counts fixed before the deciding run.

### 12.2 Stopping

- Each package gets one initial experiment and at most one corrective iteration for a specified
  failure.
- Unused time after a stop is reallocated; the total is not silently expanded, and no tuning
  continues on confirmation data.
- Existing stricter issue caps still apply.
- Insufficient evidence at the cap is **defer**, not a pass.
- F's prototype, #1036 and the §6.3 optional packages replace a stopped package within this ceiling
  or carry a separately declared budget.
- An unexecuted mandatory gate remains incomplete even when the cap binds.

All budgets are scope limits, not performance forecasts.

## 13. Dependencies, priorities and contention

### 13.1 Execution order

| Wave | Work | Dependency and limit |
|---|---|---|
| 1 | A (#1162) baseline and panel; B's development slack choices | No untouched data opened. Count and correctness work may run away from the bench host. |
| 2 | C (#1076) and D (#1078); B's (#1080) qualification | C and D share signature-engine code: explicit file ownership and integration points (§13.3). Measurement scheduling avoids overlapping reservations. |
| 3 | E (#1123) lane dispatch; F's (#1034) remaining counts | E uses the rebaselined representation if D changes its economics. F opens at most one structural prototype. |
| 4 | G (#1163) | Only candidates that survived their own gates enter ZF. |

```
#1162 A ─┬─► #1080 B (deciding read) ──────────┐
         ├─► #1076 C ─────────────────────────┤
         ├─► #1078 D ──(economics)──► #1123 E ┼─► #1163 G
         └─► #1123 E ─────────────────────────┤
#1034 F (counts) ··► [one prototype, conditional] ┘
```

### 13.2 Priorities (Project field)

| Issue | Priority |
|---|---|
| #1161 tracker, #1162 A, #1080 B, #1076 C, #1163 G | High |
| #1078 D, #1123 E, #1034 F | Medium |
| #1156, #1143 (optional) | Low |

### 13.3 File ownership (writers)

The contention magnets are `src/grobner/sigf4/`, `src/grobner/f4/` and `src/linalg/`. One writer per
directory at a time:

- **C** owns the signature → conventional handover (`src/grobner/sigf4/` dispatch and completion
  paths, and the F4 entry point it re-enters).
- **D** owns matrix row and column storage (`src/grobner/sigf4/` matrix construction and the shared
  row types in `src/linalg/`). C and D agree integration points on #1076 and #1078 before either
  opens a PR touching the other's files.
- **E** owns `src/linalg/lane.rs` and the lane dispatch site, and starts after D's representation
  decision.
- **B** changes no engine code unless its slack rule needs a new option.

## 14. Issue tracker

| WP | Issue | Labels | Priority | Native parent | Blocked by | Tier |
|---|---|---|---|---|---|---|
| tracker | [#1161](https://github.com/mfaulk/zeebra/issues/1161) | `M35` | High | — | — | — |
| A baseline | [#1162](https://github.com/mfaulk/zeebra/issues/1162) | `M35` | High | #1161 | — | Minimum |
| B zero skipping | [#1080](https://github.com/mfaulk/zeebra/issues/1080) (reused) | `M35` | High | #955 | #1162 (deciding read only) | Minimum |
| C carry | [#1076](https://github.com/mfaulk/zeebra/issues/1076) (reused) | `M35`, `blocked` | High | #1028 | #1162 | Minimum |
| D representation | [#1078](https://github.com/mfaulk/zeebra/issues/1078) (reused) | `M35`, `blocked` | Medium | #1028 | #1162 | Minimum |
| E lane dispatch | [#1123](https://github.com/mfaulk/zeebra/issues/1123) (reused) | `M34`, `M35`, `blocked` | Medium | #1043 | #1162 | Minimum |
| F structure | [#1034](https://github.com/mfaulk/zeebra/issues/1034) (reused) | `M35` | Medium | #1028 | — | Minimum (prototype conditional) |
| G integration | [#1163](https://github.com/mfaulk/zeebra/issues/1163) | `M35`, `blocked` | High | #1161 | #1162; B–F dispositions | Minimum |
| optional | [#1156](https://github.com/mfaulk/zeebra/issues/1156) | `M35` | Low | #1041 | — | separate score |
| optional | [#1143](https://github.com/mfaulk/zeebra/issues/1143) | `M34`, `M35` | Low | #1043 | — | separate score |

- **Parents.** Reused issues keep their native parent; the tracker lists them. New issues are native
  sub-issues of #1161.
- **Related, not M35 deliverables (linked, unlabelled):** #1036 (alternative to F); #1135, #1141,
  #1151 (routing follow-ups, §6.4); #1107 and PR #1160 (concurrent calibration).
- Whoever posts a gate's evidence removes `blocked` from the dependent issue and the blocked-by edge
  with it.

## 15. Public/private boundary and provenance

- Every M35 instance is a public system or an independently written generator. Nothing comes from
  the private `mfaulk/cryptanalysis` repository; no attack-specific workload is admitted.
- grobx and msolve run as pinned subprocesses under `tools/external/`. No external code is copied
  into Zeebra's MIT source; mechanisms in §4 are re-derived under
  [`external-provenance-policy.md`](research/external-provenance-policy.md). Diagnostic grobx
  overlays (§4.4) are built outside the tree and identify their source, binary and changed
  behaviour.
- Published figures carry the `**Measured at:**` header that `tools/check-measurement-provenance.sh`
  checks. Every cited commit is tagged `measured/<issue>-<slug>` so squash merges do not orphan it.

## 16. Planning decisions open for the owner

Settle on #1161 **before** the measurement each affects:

1. The §3 outcome thresholds, and §9's gates where M35 adds to an anchor issue's own.
2. The 40-hour budget split (§12.1).
3. #1080's numerical definition of "no regression beyond noise" (§9.2).
4. Whether any of M34's sealed cohorts is allocated to G's confirmation (§7.1), decided before any
   result is inspected.
5. Whether F's prototype or #1036 opens, after F's count decision and #1162's workload findings.
6. Whether to request adoption (§11) for a candidate that passes its research gate.

## 17. Integration report template (§18, written by #1163)

- **18.0 Header.** ZF commit, Z0 commit, grobx pin, host, `**Measured at:**`, tags.
- **18.1 Status.** One line per outcome in §3: met, missed or incomplete, with the evidence link.
- **18.2 Package dispositions.** B–F: adopt / defer / reject, gate figures, hours used against §12.1.
- **18.3 Competitive scoreboard.** Per regime and scale: `R` (default grobx and frozen public route),
  intervals, lineage count, peak RSS, refusals; the exact-checker panel separately.
- **18.4 Other scores.** Multi-worker latency, memory frontier, lex, one point — each with its scope.
- **18.5 Remaining gap.** What the one-worker gap is now, and which cost it sits in.
- **18.6 Negative results and follow-ups** filed, with issue numbers.

## 18. Integration report (#1163)

Not yet written.
