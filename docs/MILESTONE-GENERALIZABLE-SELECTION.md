# M34 — Generalizable Algorithm Selection and One New Competitive Regime

**Status:** integration report written, 2026-11-25 (§18, M34-I #1046). Minimum met (M-2 under
the owner's two-scale waiver); T-S not attempted (Gate H no-go); T-C missed; no stretch chosen.
§§1–16 were fixed before measurement and are unchanged. §17 is the template §18 follows.
**Predecessor:** M33 — Competitive F4 Performance and Reproducible Benchmarking
([`MILESTONE-COMPETITIVE-BENCHMARKING.md`](MILESTONE-COMPETITIVE-BENCHMARKING.md); tracker #965,
report #975 / PR #1018). M33 Minimum met, T-G and T-M missed.
**Successor:** M35 — Exact Finite-Field Competitiveness at One Worker
([`MILESTONE-FINITE-FIELD-COMPETITIVENESS.md`](MILESTONE-FINITE-FIELD-COMPETITIVENESS.md); tracker #1161).
**Planning base:** `main` at `03e1ab2f` (2026-11-22, after #1042).
**Measured at:** not measured here. Every figure is quoted from M33's integration report (§17 of the
M33 plan; F3 = `db181c51`, `research/m33-final/`) or from the issue that states it, each named
where used. Historical figures are evidence for hypotheses, never M34 findings. §18 measures
nothing either: it quotes M34's tagged records (Z0 `28df047f`, Gate H `36fd4137`, #1033
`00c9f29f`, #945 `e3eec892`, #1039 `5cce19f0`), each named where used.
**Tracking issue:** [#1043](https://github.com/mfaulk/zeebra/issues/1043).
**Project:** [Zeebra #7](https://github.com/users/mfaulk/projects/7); label `M34`. Priority is the
Project field. A dependent issue carries `blocked` until its prerequisite posts its evidence.
Milestones are labels and documents, not GitHub milestone objects.

**Focus.** M33 made Zeebra's measurements reproducible and showed that fixed rules fitted on a
few rows do not transfer. M34 asks two questions on a broader, lineage-aware corpus: does choosing
among Zeebra's *existing* configurations pay, and is there one identifiable regime where Zeebra
beats a pinned competitor by a wide margin? A reproducible "no" answers either question.

## 1. Vision and executive summary

> **M34 — Generalizable Algorithm Selection and One New Competitive Regime.** Freeze task
> contracts, a diverse lineage-aware corpus and an untouched evaluation cohort. Measure whether
> selecting among qualified existing configurations has headroom, and build a simple selector
> only if it does. Rebaseline dense small-prime elimination and prototype it only if its gate
> passes. Benchmark the existing certified-Wiedemann lex pipeline against the pinned competitor.

Four committed workstreams:

1. **Corpus and matrix (A, B).** Contracts, corpus, splits, run records and a qualified performance
   matrix over existing arms, ending in the **headroom gate (Gate H)**.
2. **Selection (C), conditional on Gate H.** Transparent rules and small trees, judged once on
   untouched groups.
3. **Dense small-prime elimination (D).** A rebaseline gate (#1033). At most one bounded prototype
   (#945) runs, and only after the gate passes.
4. **Complete certified lex pipeline (E).** A cross-engine demonstration from existing code (#1039).

M34 promises none of a selector, a dense kernel or a competitive win. Its Minimum is the evidence
for each decision.

M34 reuses the research backlog filed as #1003 (adaptive selection, #1004–#1017) and #1028
(algorithmic advantages over grobx, #1029–#1041). It adds a tracker, a confirmation issue, an
adoption-qualification issue and an integration report (§14). It does not re-parent or narrow
either backlog. Each reused issue keeps its scope, and M34 states which part of it counts here.

## 2. Planning base and audit

**Milestone number.** No `M34` label, document or issue existed at `03e1ab2f`. `git grep M34`
matches only compressed binary research artifacts. #1003 and #1028 both say no milestone is
assigned. M34 is therefore assigned here.

**State of referenced issues at planning time** (read from GitHub, not from the bodies'
"Inspected at" lines):

| Issue | State | What it means for M34 |
|---|---|---|
| #965, #975 | closed | M33 final. #1018 merged the report |
| #1002 team teardown | **closed** by #1042 (`03e1ab2f`) | Every scoped team now joins each thread explicitly (`src/util/team.rs`). A parallel configuration is admissible only at or after `03e1ab2f` (§11.2) |
| #961 graded-lex signature route | open | Mitigated by routing (#986). The engine defect stays open |
| #978 dispatch misroute | open | The incumbent arm has a known held-out failure (§4.2) |
| #990, #1019 | closed | Solver's own peak RSS (#1026) and a usable `bench-job scoreboard` (#1027) are on `main` |
| #954, #999, #1020 | open | Fixed clock unqualified; cycle-count clock rule not done; grobx certified reply too large for the journal |
| #1021 | open, claimed | Archive builds of one commit are not bit-identical across directories |
| #987 | open | The grobx driver's pin is still `1854835d`, not M33's 0.155.1 `8005a2a1` |
| #1009 | open | PR #1025 merged incidence components, elimination width, affine-linear rank and scalar substitutions (`src/grobner/planning/structure.rs`, `docs/research/input-features.md`). Cost table, coverage and scope items 2, 5, 6 remain |
| #1004–#1008, #1010–#1017 | open | No deliverable merged yet. #1006, #1007 and #1011–#1015 carry `blocked` |
| #1029–#1041 | open | None started, none claimed |
| Open PRs | none | At planning time |

## 3. What M33 established

The M33 report (§17 of its plan) gives three findings M34 builds on.

**Fixed configurations win on some regimes and lose on others.** At equal workers:

- **Track M, against msolve.** Zeebra wins Katsura-11 at 8 workers: 0.452 on GF(2³¹−1) and 0.536
  on GF(32003). It loses MQ10 at 4–8 workers by 1.9–2.8×.
- **Track G, against grobx raw.** Zeebra loses every equal-worker row, by 1.077–2.350×.
- **Zeebra at 16 workers against single-threaded grobx.** Zeebra is ahead on the structured rows
  (0.408–0.721) and behind on Cyclic-7 and Noon. This comparison never scores.

The winner depends on the family, the field, the worker count and the engine route.

**Rules fitted to a few rows did not transfer.** Gate D rejected the Katsura win because held-out
mq-random-10-s1 read 1.689 against a bar of 0.602 (owner decision 16). M32's `WorkerCrossover` band
is "fitted to MQ10 alone" (`src/grobner/sigf4/dispatch.rs`). It misroutes two held-out rows of the
same shape by 1.66–1.80× against M31 (#978). No density, term or degree feature separated MQ10
(0.157) from katsura-9 (0.164) (#927).

**The remaining gaps are attributed.**

- **Against grobx on wide primes:** bookkeeping, the digest and in-call glue. Elimination is at
  parity (#992).
- **On MQ11:** elimination. grobx skips most of it with randomized zero tests (#955).
- **Against msolve on MQ10:** elimination work (1.9× msolve's products) and per-product cost at
  GF(32003) (#993).
- **Dense small-prime systems:** #945's profile puts 93.2% of an 832 s serial wall in the forward
  pass. That profile is historical (`e4826153`, pre-M32).

The certified-Wiedemann lex pipeline has never been compared with a competitor's lex route
(#1039).

M34's two questions follow:
- **Selection.** Does picking among existing arms per input pay, on inputs unlike the ones the
  rules were fitted to?
- **Competitive regime.** Is there one class where an existing or bounded new capability beats the
  pinned competitor by ≥ 1.5×?

## 4. Current capabilities, limitations and unresolved safety

### 4.1 Capabilities M34 measures (all on `main`)

- **Graded engines.**
  - Conventional F4, the shipping default.
  - Signature F4 (`f4_signature`), grevlex only.
  - `F4Options::graded_engine = GradedEngine::Adaptive`, the opt-in dispatch, with
    `SignatureDispatch` recorded per run.
- **Memory policy.** `PlanObjective::PeakMemory` caps batches at `MEMORY_PAIR_CAP = 16`.
- **Solve planning.** `SolvePolicy` chooses between `DirectLexF4` and `GrevlexF4ThenFglm`
  (`src/grobner/planning/policy.rs`).
- **Order conversion.** `ConversionStrategy::{Classical, Adaptive, Wiedemann}`.
  - The adaptive rule: D < 128 goes classical; so does an operator with more than D²/4 stored
    cells, or a workspace over budget.
  - Otherwise up to three certified scalar-Wiedemann projections run, with typed
    `WiedemannFallback`.
  - `shape_lex_basis` is the shape-position route.
- **Input features.** `DispatchFeatures` and `SystemShape`, plus #1025's incidence components,
  elimination width, affine-linear rank and scalar substitutions.
- **Measurement.**
  - `tools/bench-job` runs jobs in dev and publication modes, records the solver's own peak RSS and
    produces a paired scoreboard.
  - `tools/bench_stats.py` computes the verdicts.
  - `tools/bench-reserve.sh` and `tools/cpu-context.sh` reserve CCDs and record the CPU context.
  - The M33 safety suites: `tests/m33_safety.rs` and `tests/m33_thread_cap.rs`.

### 4.2 Limitations

- **No independent corpus.** The admitted families are the Katsura, Cyclic, Eco, Noonburg and
  Reimer ladders and seeded MQ. Their lineage (shared supports, formulations, primes) is not
  recorded (#1005).
- **No selection-grade record.** `bench-job` folds typed refusals, unsupported inputs and
  incorrect outputs into `failed`, and has no field for feature or inference cost (#1008).
- **The incumbent dispatcher is fitted to eleven rows in five families**, and #978 shows it
  failing on held-out rows. Rows #978 has read are development data under #1005's cohort rule.
- **The comparand pin is split** between the grobx driver's `1854835d` and M33's 0.155.1 (#987,
  #1029). The pinned grobx computes serially, so the only equal-worker comparison with it is at one
  worker.
- **Not measured on current `main`:** the dense small-prime hotspot (#1033) and the lex pipeline
  against a competitor (#1039).

### 4.3 Safety state

- **#1002 (team teardown): fixed on `main` at `03e1ab2f`.** M34 arms built before that commit are
  not admissible. #1011 re-runs `m33_thread_cap` and the #1042 team test on the M34 freeze
  revision before any parallel arm is qualified.
- **#961 (graded-lex signature engine): open.** The mitigation (#986) routes graded-lex to
  conventional F4 as `ShippingReason::Order`, and it stays. The eligibility matrix (#1004) marks the
  signature engine under graded-lex as **ineligible (routed)**, not as a measured loss. Per M33
  §12.2, no signature-route configuration is called production-safe while #961 is open. M34 makes
  no broader safety claim.
- **#978: open.** M34 measures the dispatch as it ships and does not refit the band. A refit is
  #978's own work. If it uses M34 cohorts, it uses development data and a cohort it has not read.

## 5. Three claims kept apart

Every M34 result states which of these it supports. Evidence for one never stands in for another.

| Claim | Question | Evidence that establishes it | Evidence that does **not** |
|---|---|---|---|
| **C1 — regime win** | Does configuration *a* beat comparand *b* on a named class? | Paired complete-task ratio on predeclared rows of a class defined by an input predicate (§9.5), at equal workers, same contract, guarantees stated | A selector's aggregate gain; a win on rows chosen after reading |
| **C2 — generalization** | Does a selector beat the best fixed configuration on groups it never saw? | Gate A on the sealed untouched cohort (§9.2), with grouped uncertainty | Development cross-validation alone; a regime win on one family |
| **C3 — adoption** | Is a configuration safe and qualified to ship or to become a default? | M34-Q (§11): correctness, budgets, cancellation, worker cap, regression controls, untouched cohort | C1 or C2. A research gate passing never changes a default by itself |

## 6. Scope

### 6.1 Committed (Minimum tier depends on these only)

| WP | Content | Issues |
|---|---|---|
| **A** | Contracts, eligibility, corpus, lineage, splits, run records, evaluation freeze | #1004, #1005, #1006, #1007, #1008, #1029 (comparison contract and pin) |
| **B** | Remaining inexpensive features and their cost table, candidate qualification, performance matrix, **Gate H** | #1009 (remainder), #1011, #1012 |
| **D (gate)** | Dense small-prime rebaseline and go/no-go | #1033 |
| **E** | Complete certified lex pipeline against the pinned competitor | #1039 |
| **F (report)** | Selection findings and M34 integration report | #1015, M34-I #1046 |

### 6.2 Conditional (gate-controlled; never blocks Minimum)

| Work | Opens when | Issue |
|---|---|---|
| Static selectors | Gate H = go or narrow go | #1013 |
| Untouched-cohort qualification (Gate A) | #1013 hands over a frozen policy | #1014 |
| Dense prototype, at most one | #1033 posts "open" or "narrow to D′" on #945 | #945 |
| Lex routing change, at most one PR | #1039's regret > 1.2× on ≥ 2 families | inside #1039 |
| Competitive-claim confirmation | a development row meets §9.5's development bar | M34-C #1044 |
| Adoption qualification | the owner asks for an adoption decision on a candidate that passed its research gate | M34-Q #1045 |

If a gate stops, the issues behind it are closed *not planned*, with a link to the gate result
(#1015's rule). That releases everything that waits on them.

### 6.3 Stretch (at most two, chosen from evidence, recorded on the tracker)

Candidates, none of which is committed:

- **#1016:** one bounded early observation, only after a static selector exists.
- **#1017:** quotient-algebra conversion features, fed by #1039.
- **#1040:** retained M32 parallel symbolic, evidence for #1011.
- **#1036:** exact disjoint-component decomposition.
- **#1030:** M4GB/M5GB reference comparison.
- **#1034:** bilinear feasibility.
- **#955 / #1038:** exact zero acceptance, as a bounded proof-and-cost investigation only.
- **#978:** refit of the crossover band against an M34 cohort it has not read.
- **#1010:** bounded structural features, only if #1009's cheap features leave stable headroom
  unexplained.

The owner chooses them after Gate H and #1033 have posted. Each is scored by its own issue's
predeclared criterion.

### 6.4 Excluded

- Neural-network or reinforcement-learning selectors.
- Broad dynamic control or probing before a static baseline exists. #1016 is the only probing work,
  and it is stretch.
- Implementing M4GB, M5GB, bilinear, toric or chordal engines. Their feasibility issues may run as
  stretch, and none ships an engine in M34.
- A new block-Wiedemann implementation. #731's rejection stands unless #1039 measures an operator
  that contradicts its cost model.
- Uncertified zero-skipping, or any change to a correctness guarantee. #955 and #1038 may produce a
  proof and a cost model. No solver implementation of them is required or scored.
- Default changes. Each is a separate implementation issue after M34-Q (§11).
- Private or attack-specific workloads (§15).
- Repairing #961's engine defect. It stays open, outside M34.

## 7. Work packages

Each issue body carries its own specification. This section states what M34 needs from each and
what it adds.

### 7.1 WP A — contracts, corpus and evaluation freeze

- **#1004 (contracts and eligibility; High).** The task contracts T-GB, T-GB-conv, T-RAD, T-PT1,
  T-PTALL and T-ALG, the exact eligibility matrix and the initial portfolio of six to ten arms.
  - M34 needs at least the full-basis, order-conversion and point-solving contracts written
    **separately** (§8.1).
  - #1029 contributes its rows (structured, sparse/semigroup, algebraic, acceptance modes) to this
    document rather than writing another.
  - **G0:** at least three arms are exactly interchangeable on T-GB. Failing that, the first
    selection target narrows as #1004 states.
- **#1029 (comparison contract and grobx pin; High).** One grobx pin for every deciding M34 run,
  coordinated with #987, plus the capability matrix and the acceptance-mode table. Every deciding
  run in #1012, #1033, #1039 and M34-C waits for it. Exploratory runs do not.
- **#1005 (lineage, splits, cohort sealing; High).** Manifest lineage fields, grouping rules, split
  protocols S1–S5, scripted leakage checks and the sealing procedure. M34 adds the three-cohort
  split of §8.3. The freeze is a separate commit recorded on #1005 **before any fitting and before
  the deciding matrix is read**.
- **#1006 (public applications) and #1007 (controlled families); High.** Together they produce the
  pilot panel to §8.2's composition rule. Frontier inputs and inputs conventional F4 cannot finish
  are kept.
- **#1008 (selection-grade records; High).** The distinct statuses, cost fields and charging rules
  of §8.4, implemented by extending `bench-job` and `bench_stats.py`.

### 7.2 WP B — candidate qualification and performance matrix

- **#1009 (remainder; Medium).** The measured extraction-cost table on the pilot panel, the
  feature-space coverage summary, scope items 2, 5 and 6, and the stop-condition check. Feature
  cost is charged to every policy that reads the feature.
- **#1011 (qualification; High).** Each candidate is correct and budget-safe on the frozen M34
  revision, under a contract. This is **G2 admission**.
  - Candidates: conventional F4 at 1/4/16 w, signature F4 at 1/8/16 w (grevlex), the
    `MEMORY_PAIR_CAP` policy, the current `GradedEngine::Adaptive` dispatch and the `SolvePolicy`
    routes.
  - #940 and #997 are subject to their port-cost time-box.
  - Mathematical eligibility (#1004) is checked first and is never inferred from performance.
- **#1012 (matrix and Gate H; High).** The development-cohort performance matrix, complementarity
  and marginal contribution, and **Gate H under §9.1's thresholds**. These are declared here and
  posted on #1012 before the matrix is read.

### 7.3 WP C — simple selection (conditional on Gate H)

- **#1013 (Medium, conditional).** In this order: transparent rules, a small cost-sensitive tree,
  then per-arm runtime/completion models or pairwise cost models.
  - Grouped nested validation, with all tuning inside the training folds.
  - Compared against the current dispatch and the best fixed configuration chosen on training data.
  - A deterministic fallback (§9.2).
  - If a transparent rule is within uncertainty of a model, the rule is selected.
- **#1014 (Medium, conditional; Gate A).** One read of the sealed untouched cohort under §9.2. The
  outcome is a recommendation, never an integration.
- **#1015 (High).** The selection findings, written whatever happened, including a Gate H no-go.

### 7.4 WP D — dense small-prime elimination

- **#1033 (High; the gate).** Rebaseline on the current best configuration at 1/4/16 w against
  pinned grobx.
  - Phase attribution (forward, reducer block, D′ residual, backward, symbolic, conversion) and a
    density-during-reduction trace.
  - Captured matrices and an arithmetic-bounds table.
  - Its hypothesis, disproof condition, rows and budgets are **preserved unchanged** (§9.3).
  - Its decision goes on #945.
- **#945 (Medium, conditional; the prototype).** At most one bounded prototype, opened only by
  #1033. It is tested at matrix level on #1033's captured matrices before any complete solve.
  §9.3 states how a matrix-level gain must survive representation conversion and memory at
  complete-task level. Sparse and wide-field controls are kept.

### 7.5 WP E — complete certified lex pipeline

- **#1039 (High).**
  - **Zeebra timed region:** grevlex F4, multiplication-operator construction, sequence
    generation, reconstruction, exact certification, retries, fallback and final lex basis
    materialization, all charged and attributed per stage.
  - **Baselines:** Zeebra's `DirectLexF4` as a second baseline, and the pinned grobx's supported
    lex routes (FGLM and F4-lex, as #1029's capability matrix confirms).
  - **Contract:** same ideal, with multiplicities preserved. Shape-position, non-shape and
    nonradical controls.
  - **Workers:** equal workers (one, against the serial pin) score. Zeebra at 16 w is reported
    apart.
  - **Output:** existing code only, at most one routing PR, and features handed to #1017.
- #1017 coordinates but is not committed (stretch). #1039 does not write its selector.

### 7.6 WP F — safety, qualification and report

- **Safety prerequisites (inside #1011):**
  - the freeze revision is at or after `03e1ab2f` (#1002);
  - `m33_safety`, `m33_thread_cap` and the #1042 team test pass on it;
  - #961's routing test passes.
- **M34-C #1044 (conditional).** Confirms a development-row competitive win on untouched supports
  or scales, in publication mode, under §9.5.
- **M34-Q #1045 (conditional).** Adoption qualification (§11) for any candidate the owner asks
  to adopt.
- **M34-I #1046 (High).** The integration report (§17 template) scores every criterion and keeps
  every negative, incomplete or contaminated result.

## 8. Comparison contracts and experimental design (frozen)

### 8.1 Contracts

Three task contracts are compared **separately**. A result on one never appears in another's table.

| Contract | Output | Interchangeable arms (initial; #1004 confirms) | Correctness check |
|---|---|---|---|
| **Full basis (T-GB)** | Reduced GB of the given ideal, given field, variable order and monomial order | Conventional F4 (w ∈ {1, 4, 16}), signature F4 (grevlex; w ∈ {1, 8, 16}), `GradedEngine::Adaptive`, `MEMORY_PAIR_CAP` policy | `m33-basis-v1` digest equal to an independent reference (Singular below 2³¹; groebner-rs or certified grobx on wide fields) |
| **Order conversion (T-GB-conv)** | Lex reduced GB of the same ideal, multiplicities preserved | grevlex F4 + `ConversionStrategy::{Classical, Adaptive, Wiedemann}`; `DirectLexF4`; grobx FGLM / F4-lex | Lex digest equal to an independent reference; Wiedemann's exact certification charged to the arm |
| **Point solving (T-PT1 / T-PTALL)** | One verified base-field point / all base-field points | `SolvePolicy` routes (`solve_one*`, `solve_zero_dimensional*`) | Substitution of every returned point; completeness against a reference enumeration for T-PTALL |

- **Guarantee labels.** Every arm carries one: deterministic, exactly certified randomized, or
  probabilistic (#1029). Head-to-heads compare like with like, or print the difference on the row.
  Raw randomized, deterministic and certified results stay in distinct columns.
- **Radical outputs.** A radical (T-RAD) output never substitutes for a multiplicity-preserving one.
- **Contract changes.** Adding `x_i^q − x_i` changes the ideal, and so changes the contract.

### 8.2 Corpus (#1006, #1007)

- **Base problems.** Target 60–100. Minimum 60 for the pilot, otherwise Gate H is not read
  (§12.2).
  - A base problem is one formulation.
  - Field variants, orders, worker counts and repetitions are measurements of it, not further
    problems.
  - A rational system reduced at a new prime is a new instance of the same `formulation_id`, not a
    new group.
- **Composition rule** (checked by #1005's leakage script before the freeze):
  - ≥ 10 families (`family_id`), of which ≥ 4 come from public applications (#1006) and ≥ 4 are
    controlled structural families (#1007);
  - no family above 15% of base problems;
  - ≥ 2 independent supports for every seeded family;
  - each family covers at least two scales;
  - at least 10% are frontier inputs (no arm finishes within C) and at least 10% are small (best
    arm under 300 ms);
  - the existing ladders (Katsura, Cyclic, Eco, Noonburg, Reimer, seeded MQ) count as families like
    any other.
- **Fields.** Each base problem is measured at ≤ 2 fields: one prime below 2³¹ and one 64-bit
  prime, where the contract allows. Field width is a held-out axis (S5), so the untouched cohort
  includes base problems at a width not seen in development for their family.

### 8.3 Lineage and splits (#1005)

- **Group unit.** Groups are formed at `family_id` for S2. A support (`support_id`), formulation
  (`formulation_id`) and presentation parent never cross a split.
- **Three cohorts, by group:**
  - **Development**, about 50% of groups. Used for fitting and for the matrix behind Gate H, with
    grouped cross-validation inside it.
  - **Validation**, about 20%. Read once, at G4, to choose among #1013's candidates and to decide
    whether to spend the untouched cohort.
  - **Untouched**, about 30%. Read once at Gate A (#1014) and once by M34-C. It must contain:
    - ≥ 2 complete families held out (S2);
    - ≥ 1 scale ladder whose top scales are held out (S3);
    - ≥ 1 field width held out for a development family (S5);
    - presentation transforms of held-out parents only (S4).
- **Draw.** Hash-ordered and committed (M33-0's mechanism). Sealed as a separate commit on #1005
  before #1012 reads the matrix.
- **Leakage.** Coefficient reseeds of a development support never count as untouched.
- **Spent cohorts.** A cohort that has influenced any rule becomes development data. So do rows
  #978 already read.

### 8.4 Records and cost accounting (#1008)

- **Statuses.** Every attempt gets exactly one: `completed-verified`, `completed-unverified`,
  `timeout` (censored, T > C), `memory-refusal` (typed, in-solver), `rss-limit` (external guard),
  `unsupported` (typed, before work), `process-failure`, `incorrect-output`, or `not-run` (with a
  rule; §12.1).
  - A censored attempt has no completion time.
  - No table reports a capped wall as a runtime.
- **Charged to the policy or arm:** feature extraction, inference, probes, discarded work,
  required runtime verification, retries, conversion and fallback, each recorded separately.
- **Recorded, not charged:** the independent-reference audit (digest comparison) common to every
  arm.
- **Eligibility.** Checks are exact and recorded apart from any prediction. An arm that refuses an
  ineligible input records `unsupported`, which is neither a loss nor a win.

### 8.5 Measurement protocol

- **Execution.** Through `tools/bench-job`, statistics from `tools/bench_stats.py`, and the n and
  interleaving rules of `docs/guide/benchmarking.md`.
  - **Dev mode:** exploratory work, the development matrix and validation.
  - **Publication mode:** Gate A, M34-C and every figure M34-I scores.
- **Clock.** Boost, recorded, and the same rule for every arm (per-arm clock rule, #998), because
  #954 is not qualified. If #954 or #999 land and qualify before the freeze, the freeze record
  says which rule applies.
- **Isolation.** CCD reservation only for the measurement window. Private `CARGO_TARGET_DIR` and
  `TMPDIR` on `/buildcache`. One timed campaign at a time.
- **Repetitions.**
  - Matrix cells: n = 5 when the cell median is under 60 s, n = 3 above. One predeclared top-up
    to n = 9 for cells whose paired interval against the per-row best spans 1.
  - Gate A, M34-C and small systems: n = 9.
- **Identity.** Builds record the source commit and binary SHA-256. If #1021 lands, path-remapped
  archive builds are used. Otherwise `src/` identity is recorded as M33 did.
- **Pre-declaration.** Each deciding measurement's thresholds and instance list are posted on its
  issue **before** the measurement is read. The thresholds below are those values, fixed now.
  Gains from different sessions are never multiplied into a combined claim.

### 8.6 Freezes

| Freeze | What | Where recorded | Before |
|---|---|---|---|
| **Z0** | M34 revision (≥ `03e1ab2f`) and binaries; grobx and msolve pins (#1029) | tracker, tag `measured/<issue>-z0` | #1011 qualification runs |
| **S0** | Corpus composition and three-cohort split, sealed | #1005 | #1012 reads the matrix |
| **P0** | Selected policy, model version, fallback | #1013 | validation read, then Gate A |
| **ZF** | Final revision for M34-C and M34-I | tracker | publication sessions |

A revision bump after Z0 (for example, a bug fix) re-qualifies affected arms under #1011.
`git log Z0..ZF --numstat` on measured paths decides whether matrix cells must be re-read (M33
F3 = F2 rule).

## 9. Numerical gates and decision rules (pre-declared)

**Shared definitions:**
- C is the per-attempt wall cap (§12.1).
- cost(π, x) is the total charged wall of policy or arm π on base problem x (§8.4). It is the
  median over repetitions, combined over a base problem's field variants by geometric mean.
- **Penalized cost** (PAR-2): cost = 2·C for every `timeout`, `memory-refusal`, `rss-limit` or
  `process-failure`. Every table labels it as penalized and never as a runtime.
- `incorrect-output` disqualifies the arm or policy outright.
- **Aggregate** = family-weighted geometric mean: each family weighs equally, and so does each base
  problem within its family.
- **Interval** = grouped bootstrap, 20,000 draws, resampling families, then base problems, then
  repetitions.
- **Sensitivity views** at PAR-10 and on the completed intersection are reported beside every
  aggregate. They never decide, and they never replace the completion counts.

### 9.1 Gate H — headroom (#1012)

- **Inputs.** The development cohort only, in two decision contexts: **W = 16** (arms may use ≤ 16
  workers) and **W = 1**.
- **Best fixed (BF).** The arm minimizing the aggregate, chosen by leave-one-family-out, so the
  choice is never read on its own family.
- **Virtual best (VBS⁺).** Per base problem, the cheapest *eligible*, verified-completing arm,
  plus the measured cost of #1009's inexpensive features. It is a noisy empirical comparator, not
  an optimum.
- **Statistic.** H = aggregate of cost(VBS⁺, x) ÷ cost(BF, x).

| Outcome | Rule (all clauses required) |
|---|---|
| **Go** | H ≤ 0.80 and its upper 95% bound ≤ 0.87; ≥ 3 families each with family-level ratio ≤ 0.85; H ≤ 0.85 after removing the family that contributes most; H ≤ 0.85 on each half of a split-half of repetitions |
| **Narrow go** | The Go rule holds only with the arm set restricted to one decision: engine at fixed workers, or worker count at a fixed engine. #1013 is scoped to that decision |
| **No-go** | Anything else. #1013 and #1014 are closed *not planned*. #1015 publishes the matrix and recommends any fixed default or rule the matrix supports |

- **Why 0.80.** T-S needs 0.90 on unseen groups after overhead. Selectors typically recover about
  half of the gap between the best fixed arm and the virtual best, so 20% headroom is the least
  that makes 10% plausible.
- **Context.** The scoring context for T-S is fixed by this gate, before validation or untouched
  data is read. It is W = 16 when both contexts pass, otherwise the one that passes.

### 9.2 Selection objective and Gate A — target T-S (#1013, #1014)

- **Objective.** Penalized cost (above) in the context fixed at Gate H, aggregated as above.
- **Charges.** The policy pays for feature extraction, inference and fallbacks. BF pays only its
  own run.
- **Fallback.** Fixed in P0, deterministic, and charged when it fires: the BF arm whenever
  - feature extraction fails or exceeds its work cap;
  - any feature lies outside the development range;
  - the predicted advantage is within the model's calibrated uncertainty.

| Criterion | Pass (on the untouched cohort, read once, publication mode) |
|---|---|
| **Benefit** | Policy ÷ BF aggregate ≤ **0.90**, with upper 95% bound ≤ 0.95 |
| **Against the incumbent** | Policy ÷ current `GradedEngine::Adaptive` aggregate < 1.00 (point estimate) |
| **Completion** | Policy verified completions ≥ BF's |
| **Severe regressions** | A base problem counts as one if any of these holds: policy ÷ BF > 1.5 where both complete; the policy fails where BF completes; or policy peak RSS > 1.5× BF's. Allowed: at most max(1, ⌊5% of untouched base problems⌋), and no completed ratio above 3.0 |
| **Correctness** | Zero `incorrect-output` |
| **Small systems** (BF median < 300 ms) | Included in the aggregate, measured at n = 9, and reported apart. The median policy overhead on them is ≤ 5% of BF's median wall |
| **Uncertainty** | With fewer than 6 untouched families, the report states that the interval does not support a general claim, even when every criterion passes |

- **Validation (G4)** applies the same rules to the validation cohort. A candidate that fails G4
  is not taken to Gate A, and #1015 records non-adoption.
- **No retuning** after a cohort is read. A met T-S is evidence for claim C2. It is not adoption
  (C3).

### 9.3 Dense small-prime gate (#1033) and prototype (#945)

**Gate D-0, #1033's own rule, unchanged.**
- **Opens** #945 if, on the best current configuration, all three hold:
  - dense GF(31) planted MQ with n ≥ 18 spends ≥ 60% of complete-task wall in forward
    elimination;
  - ≥ half of those products fall on rows above 50% density during reduction;
  - the best Zeebra configuration is ≥ 1.5× slower than pinned grobx on those rows.
- **Defers** if forward elimination is under 40% of wall, or Zeebra is within 1.2× of grobx.
- **Narrows** to the D′ residual if the trace confines fill there.
- **Clarification.** Outcomes between the open and defer bounds **defer**. This adds no new
  threshold: the gate only opens when its hypothesis holds.

**Prototype gates.** #945's own bars are kept, and M34 adds the complete-task bar:

| Gate | Pass |
|---|---|
| **Matrix level** (#1033's captured matrices) | Forward pass at n = 20 ≥ 2× faster serially (#945); coefficient-identical echelon form |
| **Complete task** (same workers, best configuration as baseline, conversion to and from the dense representation charged) | Target rows (dense GF(31), n ≥ 18): paired wall upper bound ≤ 0.87 (≥ 1.15×). The 1.15× floor is M34's addition, at the low end of #1028's 1.15–1.5× range |
| **Memory** | Peak live bytes ≤ 1.15× (#945). Process peak RSS ≤ 1.25× |
| **Sparse controls** (katsura-8, mq-random-10, cyclic-6) | Same basis. Each loses at most 5% (#945) |
| **Wide-field controls** (MQ10 / GF(2³¹−1), one 2⁶⁴−59 row) | Dense path not taken, or identical route; paired wall upper ≤ 1.03 |

- **Iterations.** A failed gate stops the prototype. One corrective iteration is allowed, with a
  written hypothesis and ≤ 2 sessions.
- **Scope.** No dense kernel is committed to ship. A passing prototype becomes a #1011 candidate
  and, if the owner asks, an M34-Q subject.

### 9.4 Lex pipeline (#1039)

- **#1039's rule, unchanged.**
  - **Demonstration:** Zeebra's complete grevlex → certified Wiedemann → lex pipeline is ≥ 1.5×
    faster than pinned grobx's lex route at equal workers, on zero-dimensional families with
    D ≥ 10⁴, sparse operators and shape position.
  - **Disproved** if grobx is within 1.2× or faster across D, or if the advantage exists only
    where Zeebra's grevlex stage already wins on its own.
  - **Routing change** only if the adaptive rule's regret exceeds 1.2× on ≥ 2 families.
- **M34 adds:**
  - The comparand route per row is the *faster* of grobx's supported lex routes (FGLM, F4-lex).
  - Non-shape and nonradical controls are reported with fallback cost included.
  - A demonstration that meets §9.5's development bar goes to M34-C for confirmation.

### 9.5 Competitive claim — target T-C (M34-C)

- **Class.** Defined by an input predicate computable before solving, for example "dense
  quadratic, m ≥ 2n, p < 2¹⁶" or "zero-dimensional, shape position, D ≥ 10⁴". It is declared on
  the issue that produces the candidate before that issue's deciding read.
- **Contract and guarantee.** Same contract. Equal requested workers, with observed threads
  recorded. Zeebra's guarantee must be equal to or stronger than the comparand's, and both are
  printed on the row.
- **Comparand.**
  - pinned grobx in raw and certified modes, kept apart;
  - pinned msolve, where it supports the contract;
  - for msolve, the §8.4 non-anomalous-count rule of M33 applies.
- **Development bar.** ≥ 2 development rows of the class, each with Zeebra ÷ comparand median
  ≤ 0.667 and upper 95% bound < 0.75.
- **Confirmation (scores T-C).** On ZF in publication mode, ≥ 2 untouched rows of the class, at
  least one of them a support or scale no development row used, each with median ≤ 0.667 and upper
  bound < 0.80. No untouched row of the class may be a loss (median > 1 with lower bound > 1).
  Adverse controls are reported beside the claim.
- **Reported, never scored:** Zeebra at 16 w against a serial comparand.

## 10. Success tiers (fixed now; scored by M34-I)

M34-I scores each criterion **met**, **missed** or **not attempted**, with the reason. A missed
Target permits a Minimum closeout, reported as missed.

### 10.1 Minimum

- **M-1. Contracts.** Task contracts, eligibility matrix and portfolio (#1004), with #1029's
  contract rows, capability matrix and recorded grobx pin.
- **M-2. Corpus and freeze.** ≥ 60 base problems meeting §8.2, with manifests, lineage, a passing
  leakage check and the three cohorts sealed at S0 (#1005, #1006, #1007). Selection-grade records
  with every §8.4 status (#1008).
- **M-3. Matrix and headroom.** Qualified arms on Z0 (#1011), the development matrix and a
  published Gate H decision (go, narrow go or no-go) (#1012). The findings are written up (#1015).
- **M-4. Dense go/no-go.** #1033's rebaseline merged and its decision posted on #945.
- **M-5. Lex pipeline.** #1039's cross-engine table merged, with a demonstration, a routing finding
  or a no-opportunity record.
- **M-6. Report.** M34-I keeps every negative, incomplete or contaminated result and a disposition
  for every M34 issue.

### 10.2 Target

- **T-S.** §9.2 met on the untouched cohort, conditional on Gate H. With Gate H no-go, T-S is
  scored **not attempted (gate)**, with the gate record as evidence.
- **T-C.** §9.5 confirmed against a named comparand on one class. The advantage may come from
  existing capabilities (for example #1039) or from the gated prototype (#945).

### 10.3 Stretch

- **S-1, S-2.** At most two §6.3 extensions, chosen on the tracker from evidence after Gate H and
  #1033 post. Each is scored by its issue's predeclared criterion.

## 11. Qualification and adoption (C3; M34-Q)

Nothing in M34 changes a default. A candidate reaches adoption only like this:

1. It passes its research gate (Gate A for a selector, §9.3 for the dense prototype, #1039's
   routing rule for a conversion threshold).
2. The owner asks for an adoption decision on the tracker.
3. **M34-Q** on ZF covers:
   - correctness: digest against an independent reference on the qualification set, at 1 and
     maximum workers, every field class the candidate claims;
   - wall, matrix, live-byte and cancellation budgets each tripped where they bind, with typed
     failures;
   - `m33_safety`, `m33_thread_cap` and the #1042 team test;
   - #961's routing test;
   - M33 §12.2's regression thresholds on controls;
   - the candidate's untouched-cohort evidence (Gate A or M34-C).
4. A **separate implementation issue** follows. It is test-first (Red-Green), has CI coverage, a
   preserved explicit-override option, a stable model or rule version, route explanations,
   recorded extraction timings and a deterministic fallback. Online learning that silently changes
   production behaviour is excluded.

M34-Q not being run is a valid outcome, scored *not attempted*. It never blocks Minimum.

## 12. Budgets and stopping rules

### 12.1 Per-attempt caps

- C = 300 s and 16 GiB for matrix, validation and Gate A attempts.
- #1033 and #1039 keep their own budgets: 900 s / 16 GiB at n = 20 and 180 s / 8 GiB elsewhere
  for #1033, and 600 s / 16 GiB for #1039.
- **Ladder rule.** An arm that times out at scale k of a scale ladder is not run at k + 1 on the
  same support. Those cells are `not-run: ladder-censored` and enter PAR-2 as censored. This is
  imputation, declared here and reported as such. Every other arm still runs.

### 12.2 Package caps

| Package | Cap |
|---|---|
| #1004, #1029 | 3 sessions each; documents and smoke runs only |
| #1005 | 4 sessions; ≤ 800 net lines (schema, leakage checker, tests) |
| #1006 + #1007 | 8 sessions together; ≤ 2,000 net lines of generators and manifests |
| #1008 | 4 sessions; ≤ 1,200 net lines |
| #1009 remainder | 3 sessions; ≤ 600 net lines |
| #1011 | 4 sessions; #940 port time-boxed to 2 sessions, then "deferred: port cost" |
| #1012 | ≤ 40 machine-hours of measurement across ≤ 4 sessions. If the projection exceeds it, reduce repetitions to n = 3 before removing any instance. Removing instances is an owner decision |
| #1013 | 4 sessions; ≤ 4 candidate policy classes |
| #1014, M34-C | 1 publication session each, ≤ 8 h |
| #1033 | its own: one CCD reservation window |
| #945 | 1 prototype; ≤ 1,500 net `src/` lines; ≤ 8 sessions |
| #1039 | its own budget; ≤ 1 routing PR |
| M34-Q | 4 sessions |
| M34-I | 3 sessions; no library change |

- **Pilot size.** If the pilot reaches fewer than 60 base problems or fewer than 10 families within
  #1006/#1007's cap, Gate H is not read. #1012 reports "insufficient corpus" and M-3 is missed.
  Matrix data is still published.
- **Caps.** Exceeding a cap, adding a candidate or a third stretch item, or revising a declared
  threshold is an owner decision recorded on the tracker **before** the affected measurement is
  read.
- **Gate outcomes.** A failed gate stops its line of work, and the negative result is written up
  and closed as a finding.

## 13. Dependencies, priorities and contention

### 13.1 Graph

```
#1004 ─┬─► #1008 ─► #1011 ─────────┐
       └──────────► #1011         │
#1005 ─┬─► #1006 ─────────────────┤
       └─► #1007 ─────────────────┼─► #1012 [Gate H] ─┬─ go/narrow ─► #1013 ─► #1014 ─► #1015 ─┐
#1005, #1008, #1009 ──────────────┘                   └─ no-go: #1013, #1014 not planned ─► #1015 ┤
                                                                                                 ├─► #1046 M34-I
#1033 [D-0] ─ open/narrow ─► #945 (one prototype) ··► #1044 M34-C ··► #1045 M34-Q (on request)   │
#1039 ─ demonstration ··────────────────────────────► #1044 M34-C                                │
#1033, #1039 ────────────────────────────────────────────────────────────────────────────────────┘

#1029 (pin) ··► deciding reads of #1033, #1039, #1044
```

- **Solid arrows** are blocking (`blocked` label plus `blocked_by` edges). **Dotted** are
  conditional or deciding-read-only, and never block M34-I. #1008 also coordinates with #1005 for
  lineage keys. The graph stays acyclic.
- **M34-I is blocked only by** #1015, #1033 and #1039. #1015 is released by #1014 or by a
  *not planned* closure at whichever gate stopped (§6.2).
- **Opened conditional work cannot stall Minimum.** If #1013 or #1014 reaches its §12.2 cap
  without a result, it closes with a stop record, and that releases #1015. #945, #1044 and #1045
  block nothing on the Minimum path.
- **Claimable at planning time:** #1004, #1005, #1008, #1009 (remainder), #1029, and
  #1033/#1039 (exploratory parts).
  - #1033's and #1039's deciding reads wait for #1029's pin.
  - #1006 and #1007 can inventory sources now. Admission waits for #1005's schema.
- **Critical path:** #1005 → #1006/#1007 → #1012 → #1015 → M34-I. #1004 → #1008 → #1011 runs
  beside it and must finish before #1012 reads.

### 13.2 Priorities (Project field)

| Priority | Issues |
|---|---|
| High | tracker, #1004, #1005, #1006, #1007, #1008, #1011, #1012, #1015, #1029, #1033, #1039, M34-I |
| Medium | #1009, #1013, #1014, #945, M34-C, M34-Q |
| Low / unchanged | #1010, #1016, #1017, and the stretch candidates in §6.3 |

Raising #1004–#1008, #1011, #1012, #1015 and #1039 from their pre-M34 priorities is recorded in a
comment on each issue.

### 13.3 File ownership (writers)

These are the contention magnets named in `CLAUDE.md`. Writers follow one writer per checkout,
each WP in its own `git worktree`, with a private `CARGO_TARGET_DIR=/buildcache/cargo-target/zeebra-<issue>`
and `RUSTC_WRAPPER=""`.

| Area | Owner | Rule |
|---|---|---|
| `src/grobner/record/manifest.rs`, lineage schema, leakage checker | #1005 | #1006/#1007 consume it, never edit it |
| `src/grobner/benchmark_systems.rs`, new generators | #1007 | #1034 adds bilinear only to #1007's spec, after #1007's first generator PR merges |
| `src/grobner/planning/structure.rs`, `analysis.rs` | #1009 | #1013 reads features; its selector lives in a new module |
| `tools/bench-job`, `tools/bench_stats.py`, `docs/research/benchmark-schema.md` | #1008 | Additive fields only; #1012/#1014 consume them |
| `src/grobner/f4/` instrumentation | #1033 | Behind existing counters or a research feature |
| `src/linalg/dense/`, `src/grobner/f4/faugere_lachartre.rs`, `src/fields/` kernels | #945 | Only after #1033 opens it, rebased on #1033's merged instrumentation |
| `src/grobner/fglm/` | #1039 (routing PR only) | #1017 does not write here while #1039's PR is open |
| `tools/external/grobx-driver/` | #987 / #1029 | Pin changes only through #987 |
| `research/m34-*/`, `docs/research/m34-*.md` | the WP named in the path | |

## 14. Issue tracker

| WP | Issue | Labels | Priority | Native parent | Blocked by | Tier |
|---|---|---|---|---|---|---|
| tracker | [#1043](https://github.com/mfaulk/zeebra/issues/1043) | `M34` | High | — | — | — |
| A contracts | [#1004](https://github.com/mfaulk/zeebra/issues/1004) (reused) | `M34` | High | #1003 | — | Minimum |
| A comparison contract, pin | [#1029](https://github.com/mfaulk/zeebra/issues/1029) (reused) | `M34` | High | #1028 | — | Minimum |
| A lineage, splits | [#1005](https://github.com/mfaulk/zeebra/issues/1005) (reused) | `M34` | High | #1003 | — | Minimum |
| A applications | [#1006](https://github.com/mfaulk/zeebra/issues/1006) (reused) | `M34`, `blocked` | High | #1003 | #1005 | Minimum |
| A controlled families | [#1007](https://github.com/mfaulk/zeebra/issues/1007) (reused) | `M34`, `blocked` | High | #1003 | #1005 | Minimum |
| A records | [#1008](https://github.com/mfaulk/zeebra/issues/1008) (reused) | `M34` | High | #1003 | — | Minimum |
| B features (remainder) | [#1009](https://github.com/mfaulk/zeebra/issues/1009) (reused) | `M34` | Medium | #1003 | — | Minimum |
| B qualification | [#1011](https://github.com/mfaulk/zeebra/issues/1011) (reused) | `M34`, `blocked` | High | #1003 | #1004, #1008 | Minimum |
| B matrix, Gate H | [#1012](https://github.com/mfaulk/zeebra/issues/1012) (reused) | `M34`, `blocked` | High | #1003 | #1005–#1009, #1011 | Minimum |
| C selectors | [#1013](https://github.com/mfaulk/zeebra/issues/1013) (reused) | `M34`, `blocked` | Medium | #1003 | #1012 (go) | conditional |
| C Gate A | [#1014](https://github.com/mfaulk/zeebra/issues/1014) (reused) | `M34`, `blocked` | Medium | #1003 | #1013 | conditional |
| C findings | [#1015](https://github.com/mfaulk/zeebra/issues/1015) (reused) | `M34`, `blocked` | High | #1003 | #1014 or the stopping gate | Minimum |
| D gate | [#1033](https://github.com/mfaulk/zeebra/issues/1033) (reused) | `M34` | High | #1028 | — (#1029 for the deciding read) | Minimum |
| D prototype | [#945](https://github.com/mfaulk/zeebra/issues/945) (reused) | `M34`, `blocked` | Medium | #1028 | #1033 | conditional |
| E lex pipeline | [#1039](https://github.com/mfaulk/zeebra/issues/1039) (reused) | `M34` | High | #1028 | — (#1029 for the deciding read) | Minimum |
| F confirmation | [#1044](https://github.com/mfaulk/zeebra/issues/1044) M34-C | `M34`, `blocked` | Medium | #1043 | #1005, #1029, #1033, #1039 | conditional |
| F qualification | [#1045](https://github.com/mfaulk/zeebra/issues/1045) M34-Q | `M34`, `blocked` | Medium | #1043 | an owner request (§11) | conditional |
| F report | [#1046](https://github.com/mfaulk/zeebra/issues/1046) M34-I | `M34`, `blocked` | High | #1043 | #1015, #1033, #1039 | Minimum |
| scoped | [#961](https://github.com/mfaulk/zeebra/issues/961) | `M32`, `M33`, `M34` | unchanged | — | — | mitigation preserved (§4.3) |

- **Parents.** Reused issues keep their native parent (#1003 or #1028). The M34 tracker lists them
  rather than re-parenting, because GitHub allows one parent and both backlogs are broader than
  M34.
- **Related, not M34 deliverables (linked, unlabelled):**
  - #978, the incumbent's misroute;
  - #954, #999, #1020 and #1021, measurement follow-ups;
  - #987, the driver pin, needed through #1029;
  - #1010, #1016, #1017 and the §6.3 stretch candidates.
- **#1020** must be resolved before any certified-grobx row is scored in #1039 or M34-C.
- Whoever posts a gate's evidence removes `blocked` from the dependent issue.

## 15. Public/private boundary and provenance

- Every M34 instance is a public system or an independently written generator. Public-application
  sources are admitted under #1006's licensing rules. Nothing comes from the private
  `mfaulk/cryptanalysis` repository, and no attack-specific workload is admitted.
- grobx and msolve run as pinned subprocesses under `tools/external/`. No external code is copied
  into Zeebra's MIT source. Algorithms are re-derived from papers under
  [`external-provenance-policy.md`](research/external-provenance-policy.md).
- Published figures carry the `**Measured at:**` header that `tools/check-measurement-provenance.sh`
  checks. Every cited commit is tagged `measured/<issue>-<slug>` so squash merges do not orphan it.

## 16. Planning decisions open for the owner

These are recorded so they can be settled on the tracker **before** the measurement they affect.

1. **Gate H and T-S thresholds** (§9.1, §9.2) are proposed here. They may be revised on the tracker
   until S0 is sealed, and never after the matrix is read.
2. **The grobx pin** (#1029 with #987): 0.155.1 `8005a2a1` or the driver's `1854835d`.
3. **The per-attempt cap** C = 300 s and the 40 machine-hour matrix budget (§12).
4. **Stretch choices** (§6.3), after Gate H and #1033 post.
5. **Whether to request adoption** (M34-Q) for any candidate that passes its research gate.
6. **Whether #1006 can reach four application sources** within licensing limits. If not, §8.2's
   composition rule needs an owner revision before S0.

## 17. Integration report template (§18, written by M34-I)

- **18.0 Header.**
  - Z0 and ZF commits and tags; binary SHA-256s; comparand pins.
  - Sessions, with mode, reservation and clock rule.
  - Attempt counts by every §8.4 status.
  - Corpus size by family and cohort.
  - Evidence paths under `research/m34-*/`.
- **18.1 Status.** One paragraph per tier, then the three claims kept apart (§5):
  - C1 regime wins;
  - C2 generalization;
  - C3 adoption.
- **18.2 Corpus and splits.** Composition table, lineage summary, leakage-check result, sealing
  commits, and spent cohorts.
- **18.3 Performance matrix.** The arms; completion by status; BF per context; VBS⁺; marginal
  contribution per arm; and the Gate H statistic with every clause's value.
- **18.4 Selection.** For each candidate: G4 and Gate A results against every §9.2 criterion,
  severe regressions listed individually, the small-system table and the fallback rate. Or "not
  attempted (gate)" with the gate record.
- **18.5 Dense elimination.** #1033's table, density trace and decision. If the prototype ran,
  every gate in §9.3 with predicted and measured values.
- **18.6 Lex pipeline.** #1039's per-stage table against grobx's faster lex route, the controls and
  the routing finding.
- **18.7 Competitive claims.** Each row with its contract, both guarantees, equal-worker status, the
  development and confirmation values against §9.5, and the 16 w rows apart.
- **18.8 Safety and qualification.** Safety-suite results on Z0/ZF, the #961 routing test, and the
  M34-Q record or "not attempted".
- **18.9 Success criteria.** A table scoring every §10 criterion met, missed or not attempted,
  with evidence.
- **18.10 Negative, incomplete and contaminated results.** Every failed gate, stopped experiment,
  `not-run` cell, censored cell, contaminated session, refusal and excluded instance.
- **18.11 Dispositions and follow-ups.** Every M34 issue's outcome, an entry in #1028's outcomes
  log for #1033 and #1039, and follow-ups filed on Project #7 with Priority, linked to the
  tracker.

## 18. Integration report (M34-I, #1046)

Written 2026-11-25 from §17's template. No new measurement and no library change (§12.2). Every
figure is quoted from the tagged source named beside it. §10's tiers are scored as declared, with
no threshold revised.

### 18.0 Header

- **Z0:** `28df047f` (tag `measured/1011-z0`), owner decision on #1043 (2026-11-23). It contains
  #1002's fix (its twin of `03e1ab2f` on the rewritten history is `de9d9f2c`).
- **ZF:** not frozen. No session needed one: Gate A (#1014) did not open, and M34-C (#1044) never
  reached a publication session.
- **Comparand pins (#1029, owner decision 2):** grobx 0.155.1 `8005a2a1`; msolve 0.11.0. No M34
  deciding read used msolve.
- **Revisions and binaries per package:**

| Package | Measured at (tag) | Binary SHA-256 |
|---|---|---|
| #1011 qualification | `28df047f` (`measured/1011-z0`); #997 harness `2099df6e` (`measured/1011-harness`) | recorded in `docs/research/m34-qualification.md` §1 |
| #1012 Gate H | harness `6c77117a` (`measured/1012-harness`, `src/` = Z0); records `36fd4137` (`measured/1012-matrix`); S0 `2db433b2` (`measured/1012-s0`) | `m34_matrix` `ee381510…7683` |
| #1009 feature costs | `6d46e583` (`measured/1009-feature-costs`) | `research/1009-feature-costs/` |
| #1033 dense rebaseline | `00c9f29f` (`measured/1033-dense-rebaseline`) | `sig_f4_study` `3a202886…`, `research-work` `a31bbee5…` |
| #945 lane prototype | `e3eec892` (`measured/945-single-copy`), `ef985d5e` (`measured/945-session2`), dev `26dae9ed`, `4b064a84` | `sig_f4_study` `6762da5e…`, `lane_matrix_gate` `9b137adb…` |
| #1039 lex pipeline | `5cce19f0` (`measured/1039-wiedemann-lex`) | `lex_pipeline` `a2b9f5e7…424d`; grobx driver `fdd6aeec…83bc` |

- **Sessions.** All ran on the Threadripper PRO 5995WX bench host, on CCDs 1–2 (CPUs 8–23) reserved
  with `tools/bench-reserve.sh`, with the clock rule `bench-job` applies per arm (§8.5):

| Package | Mode | Sessions |
|---|---|---|
| #1011 (#997 gate) | publication | 1 (jobs `1076f513f424`, `d05e8d60ef86`) |
| #1012 Gate H | dev | 3 passes, 9.98 of 40 machine-hours |
| #1033 | publication (deciding), dev (attribution) | 4 publication (2 jobs void and re-run), 2 dev |
| #945 | as `run.sh` records | void session 1, deciding session 2, corrective session 3 |
| #1039 | publication | 4 (`n9`, `n3`, `classical`, `replace`) |

- **Attempt counts by §8.4 status (Gate H, 7,012 attempts):**

| `completed-verified` | `completed-unverified` | `timeout` | `memory-refusal` | `rss-limit` | `unsupported` | `process-failure` | `incorrect-output` | `not-run` |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 6,558 | 414 | 3 | 37 | 0 | 0 | 0 | 0 | 0 |

- **Corpus by cohort (S0):** development 122 records (64 base problems, 17 families); validation 44
  records (7 groups); untouched 88 records (10 groups plus two carve-outs). Pilot: 127 base problems,
  36 families (§18.2).
- **Evidence:** `research/m34-gate-h/`, `research/m34-selection-findings/`,
  `research/m34-public-corpus/`, `research/m34-structural-corpus/`, `research/m34-qualification/`,
  `research/1033-dense-rebaseline/`, `research/945-lane-kernel/`, `research/1039-wiedemann-lex/`.
  The write-ups are `docs/research/adaptive-selection-contracts.md`, `corpus-lineage.md`,
  `benchmark-schema.md` §8, `input-features.md`, `m34-qualification.md`, `m34-gate-h.md`,
  `m34-selection-findings.md`, `dense-small-prime-rebaseline.md` and
  `wiedemann-pipeline-vs-grobx.md`. No `research/m34-final/` summary was regenerated: every figure
  below is already in a tagged record.

### 18.1 Status

**Minimum: met.** M-2 is met only under the owner's two-scale waiver (#1043, decision 8), and its
S0 seal was executed under #1012 rather than #1005. Every Minimum deliverable is merged: contracts
and the grobx pin, the corpus with its sealed cohorts and selection-grade records, the qualified
matrix and its Gate H decision, the findings (#1015), the dense go/no-go, and the lex-pipeline
table.

**Target: not met.**
- **T-S: not attempted (gate).** Gate H read no-go, so no selector was built and the untouched
  cohort was never read.
- **T-C: missed.** The one candidate (#1039's chain family) met §9.5's development bar against
  grobx's automatic lex route. A development probe of grobx's forced F4-lex route, which §9.4 names
  as the comparand when it is faster, makes the radical rows 93–339× losses. No confirmation was run.
  #1044 stays open for the owner's disposition.

**Stretch: not attempted.** No §6.3 item was chosen on the tracker.

**The three claims, kept apart (§5):**
- **C1, regime win: none established.** #1039's demonstration is a development result against
  grobx's automatic route only, and it does not survive the faster route in development (§18.7).
  The #945 lane kernel's dense gains are measured against Zeebra's own signature route. Against
  grobx they hold only at 16 workers versus grobx's one, which is reported and never scored.
- **C2, generalization: not tested.** Gate H stopped the selection line before any validation or
  untouched read. Both cohorts are sealed and unspent.
- **C3, adoption: none.** M34-Q (#1045) was not requested. No default changed under M34. #945's
  kernel merged opt-in, off by default, by owner disposition, with its failed gate unrevised.

### 18.2 Corpus and splits

- **Composition** (`research/m34-structural-corpus/README.md`, *Pilot composition*): 127 base
  problems in 36 families. 23 families (62 problems) are public applications (#1006, PRs #1094 and
  #1128), and 13 families (65 problems) are controlled structural families and retained ladders
  (#1007, PRs #1129 and #1130). The largest family is 12 of 127 (9.4%). Every seeded family has at
  least two supports, and 13 problems (10.2%) are labelled frontier.
- **§8.2 clause not met: two scales per family.** 13 single-model public families have one scale.
  The owner waived the clause for them before S0 (#1043, decision 8), and they cannot carry a
  scale-generalization claim. Decision 7 counts the corpus line cap on hand-written code only
  (about 1,612 lines).
- **Lineage** (#1005, PR #1062, `docs/research/corpus-lineage.md`): `family_id`, `formulation_id`,
  `support_id` and presentation parent per instance, with a scripted leakage checker.
- **Sealing.** #1005 closed without the freeze commit, so S0 was sealed under #1012 (its J1, declared
  beforehand) with #1005's tool. It was sealed at `2db433b2` (`measured/1012-s0`), before the
  matrix was read, with draw S2, salt `m34-s0-v1` and `hash-groups-v1` over 34 groups.
  - Carve-outs to untouched: `zb/toric` p64 (S5) and `sd-singular-schwarz-11` (S3).
  - The S2, S3 and S5-field checks pass.
- **Spent cohorts:** development only. The five M29–M33 ladders were exposed and forced into
  development. Validation and untouched remain sealed.

### 18.3 Performance matrix

From `docs/research/m34-gate-h.md` and `research/m34-gate-h/results/gate-h.md`. Costs are PAR-2
penalized (2C = 600 s), never runtimes.

- **Arms:** P1/P2/P3 conventional F4 at 1/4/16 w; P4/P5/P6 signature F4 at 1/8/16 w (grevlex);
  P7 `MEMORY_PAIR_CAP` at 1 and 16 w; P8 `GradedEngine::Adaptive` at 1 and 16 w. All are T-GB, and
  every development record is grevlex.
- **Completion by status:** §18.0. Verified cells per arm range from 116 of 122 (conventional and
  cap16) to 120 (signature). No arm was disqualified.
- **BF per context:** P8-w1 is the leave-one-family-out best fixed arm in 16 of 17 families at both
  W16 and W1. P4 is the LOFO best fixed arm when `sd/runge-kutta-order-conditions` is held out.
- **VBS⁺** is charged #1009's measured feature cost. Descriptively, it is 0.645 of P3's
  family-weighted PAR-2 cost, against 0.811 for P8-w1.
- **Marginal contribution:** at most 1.1% per arm at W16. At W1 it is 14.4% for P4, the only W1 arm
  that completes `sd-ellipsoid-m2`.

| Arm set | H | 95% interval | families ≤ 0.85 | H without largest contributor | split halves | Verdict |
|---|---:|---|---:|---|---|---|
| Go rule | ≤ 0.80 | upper ≤ 0.87 | ≥ 3 | ≤ 0.85 | ≤ 0.85 | |
| W16 | 0.703 | [0.392, 0.942] | 6 | 0.895 (`sd/ellipsoid`) | 0.702 / 0.701 | fails upper bound, drop-one |
| W1 | 0.767 | [0.446, 0.988] | 2 | 0.981 (`sd/ellipsoid`) | 0.765 / 0.764 | fails upper bound, families, drop-one |
| engine@1w | 0.767 | [0.446, 0.988] | 2 | 0.981 | 0.765 / 0.764 | fails upper bound, families, drop-one |
| engine@16w | 0.845 | [0.399, 0.975] | 3 | 0.953 | 0.844 / 0.844 | fails H, upper bound, drop-one |
| workers@conv | 0.868 | [0.757, 0.953] | 4 | 0.926 | 0.868 / 0.864 | fails all but families |
| workers@sig | 0.952 | [0.832, 0.998] | 2 | 0.975 | 0.953 / 0.953 | fails all |
| workers@cap16 | 0.894 | [0.802, 0.998] | 5 | 0.953 | 0.871 / 0.901 | fails all but families |
| workers@adaptive | 0.925 | [0.779, 0.985] | 4 | 0.944 | 0.925 / 0.925 | fails all but families |

**Gate H: no-go**, with no context and no single-decision set passing. Sensitivity views (they do
not decide): PAR-10 H is 0.681 (W16) and 0.743 (W1). On the 61-problem completed intersection, H
is 0.898 and 0.980. The headroom is carried by `sd-ellipsoid-m2`, a memory refusal on
conventional F4 and the shipping dispatch, and by the cost of LOFO choosing P4 on the Runge–Kutta
problems. `docs/research/m34-selection-findings.md` §7 has the analysis.

### 18.4 Selection

**Not attempted (gate).** Gate H's no-go (#1012, PR #1132) closed #1013 and #1014 *not planned*
under §6.2. There is no G4 or Gate A result, no severe-regression list, no small-system table and
no fallback rate. The findings and next-stage recommendation are #1015 (PR #1137,
`docs/research/m34-selection-findings.md`):
- stop the general selector;
- keep `GradedEngine::Adaptive` as the reference fixed arm, with adoption blocked on #961 and #978;
- three bounded follow-ups: #1134, #1135 and #1136;
- a corpus richer in 1–300 s problems before any future headroom gate.

### 18.5 Dense elimination

**#1033, Gate D-0: opens #945, not narrowed to D′** (`docs/research/dense-small-prime-rebaseline.md`,
`measured/1033-dense-rebaseline`, PR #1066). Deciding rows are dense planted MQ over GF(31),
m = 2n, at n = 18 and 20. At n = 20 the run used `--live-gib 8` under the owner decision of
2026-11-22: the shipping 32 M-entry live budget refuses that row, and the refusal is reported as
its own status.

| Metric | n = 18 | n = 20 | Bar |
|---|---|---|---|
| F: elimination share of wall, best configuration (`entry` 16 w, signature route) | 0.810 | 0.801 | ≥ 0.60 |
| D: share of products on rows ≥ 50% span density | 0.899 | 0.908 | ≥ 0.50 |
| R: `entry` 1 w ÷ grobx 1 w [95%] | 31.45 [31.33, 32.57] | 32.49 [32.44, 32.55] | ≥ 1.5 |
| Best 16 w ÷ grobx 1 w (reported, not deciding) | 3.15 | 3.08 | — |

grobx 1 w takes 2.03 s (n = 18) and 17.42 s (n = 20). Zeebra's best (`entry` 16 w) takes 6.39 s
and 53.66 s.

**#945 prototype (one corrective iteration; `research/945-lane-kernel/README.md`):**

| Gate | Predicted (#945 / §9.3 bar) | Measured (session 3, `e3eec892`) | Verdict |
|---|---|---|---|
| Matrix: n = 20 serial forward | ≥ 2× | 752.8 s → 144.3 s, 0.192 [0.190, 0.192] (5.2×); echelon identical | pass |
| Complete, gf31 n = 18, 16 w | upper ≤ 0.87 | 0.333 [0.328, 0.338] | pass |
| Complete, gf31 n = 20, 16 w | upper ≤ 0.87 | 0.356 [0.351, 0.357] | pass |
| Complete, gf32003 n = 18, 16 w | upper ≤ 0.87 | 0.345 [0.342, 0.346] | pass |
| Peak live bytes | ≤ 1.15 | 0.87–0.88 | pass |
| Process peak RSS | ≤ 1.25 | 1.05–1.14 | pass |
| Sparse control katsura-8, 16 w | each ≤ 5% loss | gf31 1.045 [1.015, 1.079]; gf32003 1.073 [1.021, 1.089] | **fail** |
| Sparse control cyclic-6, 16 w | each ≤ 5% loss | gf31 1.036 [1.007, 1.064]; gf32003 1.037 [1.016, 1.055] | **fail** (upper) |
| Sparse control mq-random-10, 16 w | each ≤ 5% loss | gf31 0.987; gf32003 1.033 [1.023, 1.040] | pass |
| Wide-field controls | identical route | no lane above p = 46337 | pass by construction |

- **The prototype's gate failed** on the sparse controls, with its one iteration spent.
- **Owner disposition (#1043, 2026-11-24):** merge as an opt-in research capability (PR #1095,
  `48778879`; `SigF4Options::small_prime_lane = false`). The disposition revises no gate and
  authorizes no automatic dispatch. Automatic selection is #1123's question, with its own criteria.
- **Against grobx:** the lane's 1.94 s at 16 w on the n = 18 row is beside grobx's 2.03 s at one
  worker. That is reported, never scored, and no equal-worker advantage is established.

### 18.6 Lex pipeline

**#1039: demonstration holds against grobx's automatic lex route, on an artificial family; no
routing change** (`docs/research/wiedemann-pipeline-vs-grobx.md`, `measured/1039-wiedemann-lex`,
PR #1093). Publication mode, one worker, grobx raw. Zeebra's guarantee is certified randomized
where Wiedemann ran and deterministic otherwise. grobx's is probabilistic, and grobx certified is
not scored.

| Row | Split | D | `adaptive` ÷ grobx (auto route) [95%] |
|---|---|---:|---|
| `wd-4-10` | development | 10,000 | 0.24 [0.24, 0.25] |
| `wdsq-4-10` (nonradical) | development | 20,000 | 0.10 [0.10, 0.10] |
| `wd-3-30` | held out | 27,000 | 0.39 [0.38, 0.39] |
| `wd-4-12` over 2³¹−1 | held out | 20,736 | 0.13 [0.13, 0.13] |
| `wdsq-5-6` (nonradical) | held out | 15,552 | 0.07 [0.07, 0.07] |

- **Per stage:** grevlex takes under a millisecond on every deciding row (the input is already a
  grevlex basis). The whole difference is in conversion.
- **Controls:**
  - non-shape `wdns-4-10` and `wdnr-4-10` are 28× slower (classical fallback);
  - `wd-5-10` (D > 65535, where grobx switches to F4-lex) is 60× slower;
  - Katsura, Cyclic and dense planted quadratics are 2.4–4.6× slower.
- **Zeebra's own `direct-lex`** beats the pipeline by 27–123× on the radical chain rows. The
  pipeline is Zeebra's best route only on the nonradical rows.
- **`FglmOptions::recommended()`** refuses every winning row (D > 4096) before the adaptive rule
  runs. Every figure used a caller-lifted budget.
- **Routing finding:** no change. The adaptive rule's regret exceeds 1.2× on one row only
  (`cyclic-7`, 1.36), not on two families. #731 stands for the family it modelled, with a note for dense-operator shapes.

### 18.7 Competitive claims

| Candidate | Contract | Zeebra / comparand guarantee | Workers | Development (§9.5 bar: ≥ 2 rows, median ≤ 0.667, upper < 0.75) | Confirmation (ZF, publication) |
|---|---|---|---|---|---|
| #1039 chain family, class "box-staircase grevlex input, 10⁴ ≤ D ≤ 65535, last operator ≤ 1 stored entry per column" | T-GB-conv | certified randomized / probabilistic (raw) | 1 vs 1 | met against grobx's auto route (above). **Not met** against grobx's forced F4-lex route in an unpinned development probe (#1044, PR #1131 for #1127): `wd-4-10` 93×, `wd-3-30` 339×, `wd-4-12` 152× slower. Only the nonradical `wdsq-*` rows survive (0.11–0.15) | **not run** |

- §9.4 sets the comparand to the faster of grobx's FGLM and F4-lex routes. #1039 could measure only
  grobx's own choice. The forced F4-lex route became measurable through the driver in PR #1131,
  which is still open at this writing.
- A nonradical-only class would be a new predicate chosen after this read. It cannot inherit
  #1039's declaration.
- **T-C is scored missed.** If the owner wants a nonradical class, it needs a fresh declaration on a
  new producing issue and its own development read before any confirmation.
- **Zeebra at 16 w against a serial comparand (reported, never scored):**
  - #1033's best Zeebra is 3.08–3.15× slower than grobx;
  - #945's lane is 1.94 s against 2.03 s at n = 18 (gf31).

### 18.8 Safety and qualification

- **On Z0** (`docs/research/m34-qualification.md`):
  - `m33_safety` passes 4/4 (cancellation, live bytes, matrix rows, wall);
  - `m33_thread_cap`, the #1042 team test and #961's routing test (graded-lex goes to shipping F4 at
    1/4/8/16 w) pass;
  - correctness is 744 cells with 0 failures (PR #1100).
- **Found after Z0, both fixed on `main`, neither re-qualified for M34:**
  - #1119: `m33_safety`'s wall-budget test raced the signature route at 16 w in release (PR #1120).
  - #1122: shipping F4's parallel teams briefly ran one thread over the worker cap while spawning
    (fixed in `158ff0f0`, #1124). It was present at Z0, so Gate H's parallel conventional cells
    (P2, P3, P7-w16) ran with it. Its timing effect was not measured. It is transient, at about
    6–10 samples in 38,000 on the bench host.
- **#1049** (forced `sig_f4_reported` accepted graded-lex) was fixed before Z0 (`b38bd833`,
  PR #1055). #961's engine defect stays open, and no signature-route configuration is called
  production-safe.
- **M34-Q (#1045): not attempted.** No adoption was requested.

### 18.9 Success criteria

| Criterion | Score | Evidence |
|---|---|---|
| **M-1** Contracts | **met** | #1004: `adaptive-selection-contracts.md` (PR #1051), with G0 passed. #1029: §8 of that document (PR #1054), with the pin moved in #1053 and recorded as owner decision 2 on #1043 |
| **M-2** Corpus and freeze | **met, under waiver** | 127 base problems, 36 families (#1006: PRs #1094, #1128; #1007: PRs #1129, #1130). The two-scale clause fails for 13 families and is waived (decision 8). Lineage and leakage checker in PR #1062. S0 sealed at `2db433b2` under #1012 J1, not #1005. Records with every §8.4 status in PR #1059 (`benchmark-schema.md` §8) |
| **M-3** Matrix and headroom | **met** | #1011 (PR #1100), Gate H no-go (#1012, PR #1132), findings #1015 (PR #1137) |
| **M-4** Dense go/no-go | **met** | #1033 (PR #1066). Decision "open" posted on #945 (2026-11-23) |
| **M-5** Lex pipeline | **met** | #1039 (PR #1093): a demonstration (against the automatic route), no routing change |
| **M-6** Report | **met** | This section, with dispositions in §18.11 |
| **T-S** | **not attempted (gate)** | Gate H no-go (§18.3) |
| **T-C** | **missed** | No confirmation was run. The only candidate fails the development bar against the §9.4 comparand in development (§18.7). #1044 is open for the owner |
| **S-1, S-2** | **not attempted** | No stretch item was chosen on #1043 (decision 10 deferred the picks until Gate H) |

### 18.10 Negative, incomplete and contaminated results

- **Failed gates:**
  - Gate H, no-go (#1012).
  - #945's sparse-control gate (katsura-8 up to 1.073, cyclic-6 up to 1.037 against ≤ 1.05),
    merged opt-in regardless by owner disposition, gate unrevised.
  - #997's Cyclic-8 gate in #1011: 11–19% slower at 4 and 16 w, rejected.
  - #1009's cost bound: `analyze`, `incidence`, `scalar_substitutions` and `support_profile` fail
    on sub-0.4 ms solves and moved to #1010.
- **Stopped or skipped:**
  - #1013, #1014: *not planned* (gate).
  - #1016: closed *not planned* by the #1012 agent, before the owner ruled on stretch picks. The
    owner may reverse it.
  - #940: deferred on port cost. #955: excluded (no exact acceptance rule).
  - M34-C: not run past its prerequisite probe.
- **Censored and penalized cells (Gate H):**
  - `gen-chandrasekhar-h-13`, both fields: penalized on every arm. It has no reference, and no
    signature arm completes it, so J3 cannot verify it. It is the cohort's one frontier problem.
  - `sd-ellipsoid-m2`: memory refusal on conventional, cap16 and adaptive.
  - `zb-col-grid-5x5`: memory refusal on conventional and cap16.
  - 3 timeouts. No `not-run` or ladder-censored cell: all 1,220 cells ran in pass 1.
- **Contaminated sessions:**
  - #1033's first session: two jobs void (`4b101574…`, 13 of 15 contaminated; `214b560f…`, 5 of
    18), re-run clean.
  - #945's session 1 was void (`records-void-1.jsonl`), and its deciding read is session 2 plus
    corrective session 3.
  - #1039's `n9` session was 11.5% contaminated, under the 20% void rule. Its `replace` top-up job
    was **not declared before the read**. It refilled every `n9` cell to at least nine clean
    attempts, and its repetitions are pooled into the medians.
  - Gate H: 173 of 7,012 attempts were flagged. Cells use clean repetitions.
- **Refusals and excluded instances:**
  - #1033 n = 20 is refused by the shipping live budget, and was scored at `--live-gib 8` by owner
    decision.
  - #1039: `FglmOptions::recommended()` refuses D > 4096. The classical walk refuses with
    `SpanStorageExceeded` where its dense blocks exceed 12 GiB.
  - #1006: 3 of 39 `p64` rows have no grobx certificate.
  - Gate H's four `zb-col-grid-4x5`/`5x5` records take the J4 feature-cost fallback.
- **Incomplete:**
  - T-C's forced-route comparison exists only as an unpinned development probe (#1044).
  - #1115, the #978 band fix, was left as a draft with its rule unconfirmed on the bench host. It is
    an owner action.
- **Not reported as a runtime anywhere above:** a capped or penalized cell.

### 18.11 Dispositions and follow-ups

| Issue | Outcome |
|---|---|
| #1004 contracts | closed, met (PR #1051) |
| #1029 pin and contract | closed, met (PRs #1053, #1054) |
| #1005 lineage, splits | closed (PR #1062); S0 executed under #1012 |
| #1006 public panel | closed (PRs #1094, #1128) |
| #1007 controlled families | closed (PRs #1129, #1130) |
| #1008 records | closed (PR #1059) |
| #1009 features | closed (PRs #1025, #1121); four extractors moved to #1010 |
| #1011 qualification | closed (PR #1100); P1–P8 admitted, #997 rejected, #940 deferred |
| #1012 Gate H | closed, no-go (PR #1132) |
| #1013, #1014 | closed *not planned* (gate) |
| #1015 findings | closed (PR #1137) |
| #1033 dense gate | closed, opens #945 (PR #1066) |
| #945 dense prototype | closed; gate failed on sparse controls; merged opt-in by owner disposition (PR #1095) |
| #1039 lex pipeline | closed, demonstration handed to #1044 (PR #1093) |
| #1044 M34-C | **open, owner action**: close *not planned* (T-C missed for this candidate) or declare a fresh nonradical predicate on a new producing issue |
| #1045 M34-Q | open, conditional; not attempted (no adoption request) |
| #1046 M34-I | this report |
| #1049, #1050 | closed (PRs #1055, #1057) |
| #1065 Track Gc re-run | closed (PR #1099; M33 record, `measured/1065-gc-rerun`) |
| #1123 lane dispatch | open, owner-directed research (#945 disposition) |
| #1127 forced grobx F4-lex | open; PR #1131 open |
| #961 | open, outside M34; mitigation preserved |
| #1043 tracker | open; closing is the owner's decision (#1044 is conditional and still open) |

- **#1028 outcomes log:** #1033 (open #945) and #945 (prototype gate failed, merged opt-in) are
  added. #1039's entry is annotated with #1044's forced-route probe.
- **Follow-ups filed** (Project #7, linked to #1043; parent #1003):
  - #1134 (Medium): typed-refusal fallback from conventional F4 to signature F4.
  - #1135 (Low): size-gated worker count for `GradedEngine::Adaptive`.
  - #1136 (Low): attribute the signature engine's slowdown on `sd-hairer-2`.
- **Related, not M34 deliverables:**
  - #1030 (M4GB) rejected against grobx (PR #1125, `measured/1030-m4gb-held-out`), with the M5GB
    licence an owner action;
  - #1092's GF(2) residual sweep became the packed default (PR #1098);
  - #978 and #1115 are open (owner action);
  - #954 and #1103 are measurement infrastructure.
- **Owner actions outstanding:**
  1. #1044: close *not planned*, or declare a new predicate.
  2. PR #1131 (#1127): review and merge the forced F4-lex driver route.
  3. #1016: confirm or reverse the *not planned* closure.
  4. Stretch picks: none were made. Confirm that M34 closes with none.
  5. #1115 / #978: the band fix's unconfirmed rule.
  6. #1030: the M5GB licence.
  7. Whether to spend the sealed validation and untouched cohorts on any follow-up.
  8. Closing #1043.
