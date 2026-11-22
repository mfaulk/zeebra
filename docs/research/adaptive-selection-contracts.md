# Adaptive selection: task contracts, eligibility and the initial portfolio

**Issue:** #1004 (M34 WP A, gate G0). **Inspected at:** `main` `45e9b625`. **Plan:**
[`docs/MILESTONE-GENERALIZABLE-SELECTION.md`](../MILESTONE-GENERALIZABLE-SELECTION.md) §7.1 and §8.1.

This document contains no measurements. Every entry below is a statement about what a configuration
is *allowed* to return, read off the code or a closed issue. Nothing in it says how fast anything
is. #1029's comparison contract is §8: the grobx pin, grobx's capability matrix, the contract rows
that candidate algorithms may produce, and the acceptance modes with their checking costs. Its
smoke runs (`research/m34-grobx-capability/`) establish capability only and record no timings.

## 1. Why contracts come before performance

Zeebra already makes the choice between engines in three places:

| Site | Choice | Code |
|---|---|---|
| Graded engine | conventional F4 or signature F4, for a reduced basis under a graded order | `F4Options::graded_engine = GradedEngine::Adaptive` → `sigf4::dispatch::adaptive_f4` (`src/grobner/sigf4/dispatch.rs`) |
| Solve planner | `DirectLexF4` or `GrevlexF4ThenFglm`, for a point | `SolvePolicy`, `PlanObjective` (`src/grobner/planning/policy.rs`) |
| FGLM conversion | `ConversionRoute::Classical` or `Wiedemann` | `ConversionStrategy::Adaptive` (`src/grobner/fglm/options.rs`, `src/grobner/fglm/wiedemann.rs`) |

A selector picks between arms, and the pick means something only when those arms return the same
object. If one arm returns a full reduced basis and another returns a single point, the selector is
choosing between tasks rather than configurations. A learned score cannot establish properties such
as zero-dimensionality, radicality or whether an order is admissible. Section 3 therefore decides
eligibility exactly, and #1011 and #1012 read it before they read any performance figure.

## 2. Task contracts

Each contract fixes the output, what counts as correct, and which budgets bind. A result under one
contract never appears in another contract's table (plan §8.1).

Shared definitions:

- **Field classes.** `P32` and `P64` are `PrimeFieldElement32/64`. `PW` is the wide primes,
  `PrimeFieldElement128/256`. `B` is `BinaryFieldElement`, i.e. GF(2^m), which includes GF(2).
  `X` is the extension fields `ExtensionFieldElement` (GF(p^n)). All of these implement
  `FiniteField` and `KnownOrder`.
- **Typed stop.** An arm that crosses a budget returns an `F4Error`, `SigF4Error`, `FglmError` or
  `SolveError` and never a result. `F4Error::stop_kind` separates `StopKind::Time` from
  `StopKind::Resource`. #1008 maps these to the statuses in plan §8.4.
- **Reference digest.** `m33-basis-v1` (`tools/external/basis_digest.py`), compared against an
  independent engine: Singular below 2³¹, and groebner-rs or certified grobx on wide fields.

### T-GB: complete reduced Gröbner basis

- **Output.** The reduced Gröbner basis of ⟨generators⟩ under the given `MonomialOrder`, variable
  order and field. It is unique, so every eligible arm must return it coefficient for coefficient.
- **Fields.** All classes. No characteristic restriction appears in any T-GB arm.
- **Orders.**
  - Conventional F4 accepts every `MonomialOrder`.
  - The signature engine accepts graded orders only (`sigf4::engine::graded`).
- **Multiplicity.** Preserved: the ideal itself is computed, not its radical.
- **Correctness check.**
  - Primary: the reference digest.
  - Optional runtime check: `F4Options::certify` runs `certify_f4_output_with_workers`, or
    `certify_f4_output_within` when `max_certify_time` is set. The signature engine runs the same
    certificate when `SigF4Options::certify` is set (`sigf4/engine.rs`, after interreduction).
  - When an arm turns the runtime check on, its cost is charged to that arm (plan §8.4).
- **Budgets.**
  - `max_wall_time`, checked once per batch and cooperative (not a hard bound).
  - Matrix limits: `max_matrix_rows`, `max_matrix_columns`, `max_live_nonzeros` and `max_live_bytes`.
  - Count limits: `max_basis_elements`, `max_batches` and `max_pairs_per_batch`.
  - The certification budget, `max_certify_time`.
  - Under `GradedEngine::Adaptive` all of these keep their meaning. The live budget binds on the
    signature cascade at every team size, a fix from #986.

### T-GB-conv: intermediate basis, then conversion

- **Output.** The same object as T-GB under the *requested* order. In practice that is the lex
  reduced basis of a zero-dimensional ideal. Its cost includes both stages.
- **Precondition.** The ideal is zero-dimensional. FGLM classifies the source basis first
  (`classify_ideal`), and a positive-dimensional input is a typed `PositiveDimensional` refusal, not
  a result.
- **Fields.** All classes for the classical walk.
  - Wiedemann draws three projections from `F` with a fixed seed (`0x368_f61a`).
  - Over a small field the projections fail more often. The arm then falls back to the classical
    walk (`WiedemannFallback::NonCyclicProjection`) and the result does not change.
- **Multiplicity.** Preserved.
  - Wiedemann returns a basis only when deterministic quotient-algebra evaluation verifies the
    shape relations (`shape_relations_vanish`). Otherwise it reports `VerificationFailed` and falls
    back.
  - A nonradical ideal can be in shape position (`fglm/shape.rs` test
    `test_a_nonradical_ideal_can_be_in_shape_position`).
- **Correctness check.** The lex reference digest. Wiedemann's exact verification is part of the
  route and is charged to the arm.
- **Budgets.**
  - The F4 stage: the T-GB budgets.
  - The conversion: `max_quotient_dimension`, `max_operator_entries`, `max_operator_bytes`,
    `max_span_entries` and `max_span_bytes`. These are checked from the counted dimension D before
    allocation.
  - **`FglmOptions` has no wall budget.** A wall budget covers only the F4 stage, so a wall bound
    on the whole contract needs an external supervisor (bench-job's).

### T-RAD: radical or radical-membership representation

- **Output.** A Gröbner basis of √I, or a decision procedure for f ∈ √I.
- **No in-crate arm produces this for an arbitrary I.**
  - The only radical output is from `with_field_equations` (`src/grobner/field_equations.rs`).
  - Adding `x_i^q − x_i` makes I + ⟨field equations⟩ radical, but it is a *different ideal* whose
    variety is the F_q-rational points.
  - Under the plan's §8.1 rule ("adding `x_i^q − x_i` changes the ideal, and so changes the
    contract"), that system is a separate T-GB instance, not a T-RAD answer for I.
- **Interchangeability.** A T-RAD output never substitutes for T-GB or T-GB-conv when
  multiplicities matter.
- **Status.** Recorded for completeness and empty on the Zeebra side. #1029 states whether any
  comparand offers it.

### T-PT1: one verified base-field point

- **Output.** One of three answers (`SolveOutcome`):
  - `Point(p)`, with p already verified against the original generators;
  - `NoBaseFieldPoint`;
  - `Inconsistent` (1 ∈ I).
  Every variant is an answer. A crossed budget is a `SolveError` and can never be read as "no
  solution".
- **Precondition.** A zero-dimensional ideal. `PositiveDimensional` is a typed refusal, and
  `SolveError::is_resource_failure` excludes it, so no fallback retries it.
- **Fields.** Classes with `KnownOrder`, which is every class above. Root finding is randomized
  through the caller's `rng`. The returned point is verified by substitution, so the randomness
  affects cost and never correctness.
- **Multiplicity.** Not part of the output: a point is a point.
- **Correctness check.**
  - Substitute the point into every generator.
  - For `NoBaseFieldPoint` and `Inconsistent`, agree with a reference enumeration or reference
    basis.
- **Budgets.**
  - `SolveOptions.f4` and `SolveOptions.fglm`.
  - `max_branches`.
  - Under the planner, `PlanBudget.max_total_batches` (enforced inside each attempt) and
    `max_elapsed` (only *between* attempts).

### T-PTALL: all base-field solutions

- **Output.** The complete set of F-rational points, or `TooManySolutions { limit }`. The solver
  never returns a truncated list.
- **Precondition, fields and check.**
  - Precondition and fields are as T-PT1.
  - Check: substitute every point, and compare the set for completeness against a reference
    enumeration.
- **Budgets.** As T-PT1, plus `max_solutions`.
- **No planner entry.** `solve_zero_dimensional_with_options` runs an *explicit* `SolveStrategy`.
  T-PTALL has no `SolvePolicy`, so its arms are the two strategies.

### T-ALG: solutions over the algebraic closure

- **Output.** A description of every point over F̄ with its multiplicity, for example a
  shape-position lex basis or a rational univariate representation (RUR).
- **In-crate.**
  - `fglm::shape_lex_basis` returns the lex basis of a shape-position ideal. That is T-GB-conv's
    object, not a separate one.
  - `shape_report` and `separating_variables` diagnose shape position.
  - No arm returns a RUR. A non-shape ideal is answered only by a full lex basis.
- **Status.** Zeebra's T-ALG arms are exactly its T-GB-conv arms, restricted to inputs where the
  lex basis is the description. #1017 (quotient-algebra features) and #1039 (the lex pipeline) are
  where this could widen.

## 3. Eligibility matrix

The matrix records exact eligibility only. Entries are:

- **yes**: the arm returns the contract's object. The reason is a theorem plus a typed refusal path,
  and an in-tree test that asserts equality with the reference arm.
- **yes-with-check**: the same theorem holds, but no in-tree test compares this configuration
  directly. #1011 must confirm by digest before the arm is admitted.
- **ineligible (routed)**: a dispatcher sends the input to another arm, so the arm's own result is
  never produced on that input. Score it as the routed arm's result.
- **no**: the arm refuses with a typed error (`unsupported`) or cannot produce the object.
- **unknown**: not established either way.

No entry is a performance claim.

### 3.1 T-GB by monomial order

Column abbreviations: **grevlex** = `GradedReverseLexicographic`; **grlex** =
`GradedLexicographic`; **lex** = `Lexicographic`; **W/B** = `Weighted` and `Block`.

| Arm (configuration) | grevlex | grlex | lex | W/B | Established by |
|---|---|---|---|---|---|
| Conventional F4, `F4Options::default()` (w = 16 cap) | yes | yes | yes | yes | Uniqueness of the reduced basis. `PairCriteria` are theorems (`src/grobner/pairs.rs`); `PairCriteria::NONE` is the differential reference |
| Conventional F4 at w ∈ {1, 4, 16} (`ParallelForward`/`ParallelSymbolic` caps) | yes | yes | yes | yes | `f4/parallel.rs`: `forced_workers_reproduce_the_serial_basis`, `…_katsura_7`. Field caveat in §3.3 |
| Conventional F4, `max_pairs_per_batch = Some(16)` | yes-with-check | yes-with-check | yes-with-check | yes-with-check | A cap leaves pairs pending and never discards them (`F4Options::hilbert`, `schedule` docs). No differential test at a cap of 16 |
| `GradedEngine::Adaptive` (dispatch) | yes | yes (routes to conventional, `ShippingReason::Order`, #986) | yes (graded engine ignored, conventional F4) | yes (as lex) | `graded_engine_tests.rs`: `test_adaptive_option_equals_conventional_f4_on_every_route`, `test_non_graded_orders_keep_conventional_f4`, `test_adaptive_option_is_deterministic_across_workers` |
| `GradedEngine::Adaptive` + `max_batches` or `max_pairs_per_batch` | yes (stays conventional) | yes | yes | yes | `adaptive_f4` returns `None`; `test_batch_budgets_keep_conventional_f4` |
| `f4_signature_reported` (dispatch entry) | yes | yes (routed, `Order`) | no (`Unsupported`) | no (`Unsupported`) | `signature_route` → `engine::graded` |
| Signature engine forced, `sig_f4_reported` with `SigF4Options { workers ∈ {1, 8, 16} }` (`research-sigf4`) | yes | **ineligible: #961** | no (`Unsupported`) | no (`Unsupported`) | Module contract: the output equals `f4()` (`sigf4/mod.rs`, Lairez Thm 62). For grlex see §5.1 |
| Conventional F4, `ReducerSelection::FewestTerms` (#997) | unknown | unknown | unknown | unknown | Selection changes reducers, not pairs, so a basis change is not expected. Not qualified on M34 inputs; goes to #1011 |
| Retained M32 parallel symbolic (`measured/940-gate-s`, `-s2`) | unknown | unknown | unknown | unknown | Not on `main`. Goes to #1011 |
| Randomized zero-skipping (grobx row combinations, #955) | no | no | no | no | No exact acceptance rule exists (#955, #1038). Not implemented in Zeebra |

**G0.** At least three arms are exactly interchangeable on T-GB under grevlex: conventional F4,
`GradedEngine::Adaptive` and the forced signature engine. That stays true even without counting
the worker variants or the capped arm. **G0 passes.** Under grlex, lex and W/B, only conventional F4
and dispatchers that collapse onto it remain. Selection under those orders is therefore a choice
of worker count and batch cap, not of engine.

### 3.2 T-GB-conv, T-PT1 and T-PTALL

| Arm | T-GB-conv | T-PT1 | T-PTALL | Established by |
|---|---|---|---|---|
| grevlex F4 (any T-GB-eligible grevlex arm) + `ConversionStrategy::Classical` | yes | yes (as a `SolveStrategy::GrevlexF4ThenFglm` stage) | yes | `fglm_to_lex_with_options`; route recorded as `ConversionRoute::Classical` |
| grevlex F4 + `ConversionStrategy::Adaptive` (default) | yes | yes | yes | Wiedemann only on D ≥ 128 with a sparse last operator; every fast basis verified, otherwise fallback (`WiedemannFallback`) |
| grevlex F4 + `ConversionStrategy::Wiedemann` | yes | yes | yes | Up to three projections regardless of size, then the classical walk; every returned basis verified |
| Direct lex F4 (`SolveStrategy::DirectLexF4`) | yes | yes | yes | T-GB under lex; zero-dimensionality classified from the lex basis, or from a grevlex basis after a failure (`explain_lex_failure`, #376) |
| `SolvePolicy::Explicit(s)` | n/a | yes | n/a | Runs exactly `s` |
| `SolvePolicy::ConservativeAuto` | n/a | yes | n/a | One route. A counted D over budget is `ConversionInfeasible`, a typed refusal, not a switch |
| `SolvePolicy::AutoWithFallback` | n/a | yes | n/a | One extra attempt from the shared budget. Charged as discarded work (plan §8.4) |
| `SolvePolicy::ClassifyThenDirectLex` | n/a | yes | n/a | Grevlex classification, then lex; both bases charged |
| `PlanObjective::{PeakMemory, CompletionWithinBudget}` | n/a | yes | n/a | A cap of `MEMORY_PAIR_CAP = 16` changes batches, not the basis. Capped re-attempts are charged |
| `with_field_equations` + any arm | **no** (different ideal) | separate instance | separate instance | Plan §8.1: the contract changes |

**T-ALG** uses the T-GB-conv column restricted to shape-position inputs (§2). **T-RAD** has no
Zeebra arm.

Where T-PT1 and T-PTALL arms differ, they differ only in cost. Every point is verified, and every
non-point answer is typed. The answers agree whenever both arms complete. The point *returned* can
differ, because the search order and `rng` choose which point. A T-PT1 comparison therefore checks
the point by substitution, not by equality.

### 3.3 Field-class caveats (resource contract, not correctness)

- **Concurrent forward elimination needs a field handle.**
  - `P32`, `P64`, `PW` and `B` provide `concurrent_elimination()`.
  - `X` (`ExtensionFieldElement`) uses the trait default, `None`, and runs serially under any worker
    setting (`f4/parallel.rs` test `a_field_without_a_handle_stays_serial`).
  - A "w = 16" arm on an `X` input is a one-worker arm, and the run record must say so.
- **`Backend::Sparse` and `ReductionStrategy::Unstructured` stay serial.** This applies under any
  worker setting (`ineligible_settings_stay_serial`). `F4Options::baseline()` uses both, so a
  baseline-derived arm is serial whatever its label says.
- **The signature team is capped.** Below `SIGNATURE_SMALL_TEAM_VARIABLES = 10` variables, the team
  is capped at `SIGNATURE_SMALL_TEAM = 8`, so a dispatch arm labelled w = 16 runs eight workers
  there. `SignatureDispatch.workers` records the team size actually used.
- **GF(2) elimination.** `Gf2Elimination::Auto` bit-packs characteristic-two batches in
  conventional F4. This affects cost only.

## 4. Where eligibility is enforced, and where it is only documented

| Property | Enforced by | Only documented |
|---|---|---|
| Signature engine refuses non-graded orders | `engine::graded` → `SigF4Error::Unsupported`, reached from both `sig_f4_reported` and the dispatcher | — |
| Signature engine is not used under grlex (#961) | `signature_route` → `ShippingReason::Order` (dispatch); since #1049, `engine::run` → `SigF4Error::Unsupported` unless `SigF4Options::allow_graded_lex` | At `45e9b625`, forced `sig_f4_reported` accepted grlex and `GradedEngine::Adaptive`'s rustdoc described the pre-#986 state. #1049 closed both |
| Batch-counted budgets keep conventional F4 | `adaptive_f4` returns `None` when `max_batches` or `max_pairs_per_batch` is set | — |
| Pair criteria are sound | Theorems plus the differential corpus against `PairCriteria::NONE` | — |
| FGLM needs a zero-dimensional source | `classify_ideal` → `PositiveDimensional` | — |
| Wiedemann output is exact | `shape_relations_vanish` before return | — |
| A conversion out of budget is refused, not attempted | `ConversionInfeasible` (planner) and the span checks from D (FGLM) | — |
| Point answers are verified | `SolveOutcome::Point` only after substitution | — |
| A budget stop is never "no solution" | Types: `SolveError` vs. `SolveOutcome` | — |
| Plan wall budget | `PlanBudget.max_elapsed` gates *between* attempts | The `PlanBudget` rustdoc says this is because "F4 has no cooperative time check". `F4Options::max_wall_time` now is one, and the planner does not pass the remaining `max_elapsed` into it. See §6 |
| FGLM stage wall budget | none | Needs an external supervisor (§2, T-GB-conv) |
| Worker labels on fields without a handle | none: silently serial | §3.3 |

## 5. Initial portfolio

There are eight arms, built from merged code at `45e9b625`. Each arm names its contract and the
regime it is expected to cover. The regime is a hypothesis for #1012 to test, not a performance
claim. Worker counts follow plan §7.2 rather than a Cartesian product.

| # | Arm | Contract | Configuration | Regime it is expected to cover | Resource contract |
|---|---|---|---|---|---|
| P1 | `conv-w1` | T-GB | `F4Options::default()`, `ParallelForward::Serial`, `ParallelSymbolic::Serial` | Small inputs, where dispatch and team setup dominate; the equal-worker comparison with the serial grobx pin | T-GB budgets; w = 1 |
| P2 | `conv-w4` | T-GB | default with `ParallelForward::Auto { max_workers: 4 }` and `ParallelSymbolic::Auto { max_workers: 4 }` | Mid-size matrices where 16 workers oversubscribe; a common laptop-class budget | T-GB budgets; w ≤ 4 |
| P3 | `conv-w16` | T-GB | `F4Options::default()` (`Auto { max_workers: 16 }`) | Large matrices; the shipping default | T-GB budgets; w ≤ 16; serial on `X` |
| P4 | `sig-w1` | T-GB (grevlex only) | `sig_f4_reported`, `SigF4Options { workers: 1, .. }` | Regular, equal-degree systems with many reductions to zero | T-GB budgets; live budget charged at w = 1 (#986); unsupported off grevlex |
| P5 | `sig-w8` | T-GB (grevlex only) | as P4, workers 8 | Fewer than ten variables, where the dispatcher caps the team at 8 anyway | as P4; w ≤ 8 |
| P6 | `sig-w16` | T-GB (grevlex only) | as P4, workers 16 | Ten or more variables, equal-degree inputs | as P4; w ≤ 16 |
| P7 | `conv-cap16` | T-GB | `F4Options::default()` with `max_pairs_per_batch: Some(16)` | Inputs refused by matrix-size limits; the `PeakMemory` objective's arm | T-GB budgets; peak bounded at the cost of batches |
| P8 | `adaptive` (incumbent) | T-GB | `F4Options::default()` with `GradedEngine::Adaptive` | The current dispatcher. The baseline any selector must beat, with its dispatch time charged | T-GB budgets; `graded_route` recorded |

The point-solving arms are kept apart and scored only against each other (plan §8.1):

| # | Arm | Contract | Configuration |
|---|---|---|---|
| S1 | `lex-direct` | T-PT1 / T-PTALL / T-GB-conv | `SolveStrategy::DirectLexF4` |
| S2 | `grevlex-fglm` | T-PT1 / T-PTALL / T-GB-conv | `SolveStrategy::GrevlexF4ThenFglm`, `ConversionStrategy::Adaptive` |
| S3 | `plan-conservative` | T-PT1 | `SolvePolicy::ConservativeAuto`, `PlanObjective::Time` |
| S4 | `plan-fallback` | T-PT1 | `SolvePolicy::AutoWithFallback`, `PlanObjective::CompletionWithinBudget` |

### 5.1 Arms deliberately left out

- **Signature arms under grlex.** Ineligible while #961 is open (plan §4.3). P4–P6 are grevlex-only
  arms. Since #1049, `sig_f4_reported` refuses a grlex input with `SigF4Error::Unsupported` unless
  `SigF4Options::allow_graded_lex` is set, so a harness records that refusal as `unsupported`. It
  must not set the opt-in.
- **`adaptive` + cap.** This collapses onto P7 (§3.1), so it is not a distinct arm.
- **`ConversionStrategy::Classical` and `Wiedemann` as separate S-arms.** They are ablations of S2's
  conversion stage, not distinct T-GB-conv answers. #1039 measures them.
- **`F4Options::baseline()`.** It is a historical reference and serial by construction (§3.3). It
  answers the same contract, but no selector would choose it.

### 5.2 Objectives per contract

Every objective names its budget C, which #1008 records per attempt.

| Contract | Objectives | Budget |
|---|---|---|
| T-GB | expected wall time; completion within C; peak RSS | wall C per attempt (bench-job), plus the T-GB in-solver limits at their defaults unless the arm overrides them |
| T-GB-conv | expected wall time of both stages; completion within C | as T-GB for F4; the FGLM limits at `FglmOptions::recommended()`; external wall C (§2) |
| T-PT1 | expected wall time, including every planner attempt (`SolvePlan::total_elapsed`); completion within C | `PlanBudget` plus external wall C |
| T-PTALL | expected wall time; completion within C | `SolveOptions` plus external wall C |

No risk-sensitive objective is adopted here. If one is wanted, it is the penalized cost of plan
§9 (PAR-k on censored attempts), defined there and not redefined here.

## 6. Candidates requiring further qualification (to #1011)

| Candidate | Why it is not admitted here |
|---|---|
| `measured/940-gate-s`, `measured/940-gate-s2` (M32 parallel symbolic) | Not on `main`; subject to the port-cost time-box (plan §7.2) |
| `ReducerSelection::FewestTerms` + FL order (#997) | On `main` as an option; T-GB eligibility unknown on M34 inputs |
| P7 `conv-cap16` | yes-with-check: needs a digest check at a cap of 16 |
| Every parallel arm (P2, P3, P5, P6, P8) | Built after #1002's fix (`03e1ab2f`). #1011 re-runs `m33_thread_cap` and the #1042 team test on the freeze revision (plan §4.3) |
| Forced-signature harness guard | Resolved by #1049: the guard is in `sig_f4_reported` (§5.1) |

### Follow-ups found while inspecting

- `GradedEngine::Adaptive`'s rustdoc still says not to use it under grlex. Since #986 the
  dispatcher routes grlex to conventional F4, so the warning now applies only to the forced engine.
- The `PlanBudget` rustdoc's reason for `max_elapsed` not interrupting an attempt ("F4 has no
  cooperative time check") is stale since `F4Options::max_wall_time` landed.

Both are filed, as #1049 and #1050, rather than changed here, to keep this a documentation change.

## 7. Answers to the issue's research questions

- **Which routes are genuinely interchangeable for T-GB?**
  - Under grevlex: conventional F4 at any worker count, any batch cap, `GradedEngine::Adaptive`
    and the signature engine.
  - Under grlex: conventional F4 and dispatchers that route to it. The forced signature engine is
    excluded.
  - Under lex, W and B: conventional F4 only.
- **Which routes are interchangeable only for T-PT1 and T-PTALL?** The `SolvePolicy` routes and
  `PlanObjective` variants. They return verified points, not a basis the caller chose. Direct-lex
  and grevlex-plus-FGLM are interchangeable on T-GB-conv as well.
- **Where is eligibility enforced, and where is it only documented?** See §4. Every correctness
  property is enforced in types or refusals. The gaps are:
  - one eligibility gap: the forced signature engine accepts grlex;
  - two resource-contract gaps: no FGLM wall budget, and silent serial execution on fields with no
    concurrent handle.

## 8. Comparison contract against grobx (#1029)

**Issue:** #1029 (tracker #1028; M34 M-1). **Inspected at:** `main` `3fc16682`, with grobx upstream
read at `8005a2a1` (`MANUAL.md`, fetched as a tarball and not vendored). **Smoke runs:**
`research/m34-grobx-capability/smoke.jsonl`, produced by `smoke.py` in the same directory. They are
capability runs on tiny instances and publish no timing or memory figure.

### 8.1 Pin decision

M34 adopts **grobx 0.155.1 `8005a2a1670a7264617a6f49eeb2618d7fa21701`** for every deciding run.
This is the M33 comparand pin (`research/m33-baseline/pins.json`, #966).

- **Why not `1854835d` (0.73.3).** That revision is the repository driver's pin, kept for M31
  continuity. M33 published its head-to-heads against 0.155.1. A tracker that compared against
  0.73.3 would be measuring a competitor that M33 had already replaced.
- **It builds reproducibly.** `research/m33-baseline/grobx-pin.sh`'s recipe builds the driver
  against `research/m33-baseline/grobx-0.155.1.Cargo.lock` with `--locked`, Rust 1.99.1, release,
  fat LTO, one codegen unit and `-C target-cpu=x86-64-v3`, and the repository's driver source needs
  no change. A private rebuild from `main` gives the same binary bit for bit as M33's (§8.2).
- **The repository driver is this pin.** #987 moved the repository's four pin sites to `8005a2a1`
  (#1053), and this issue made no driver change of its own. `tools/external/provision-grobx.sh`
  now builds this pin. Its manifest, lock, toolchain file, `src/main.rs` and `build.rs` are byte
  for byte the sources of the private rebuild in §8.2. Every deciding run records the driver's
  `--version` identity (#1008).
- **Threads.** 0.155.1 computes on one thread: `Params::threads` is accepted and ignored (upstream
  `MANUAL.md`, *Rust*; the `pins.json` census). The driver refuses `workers ≠ 1` (§8.3). The only
  equal-worker head-to-head with grobx is therefore at one worker, against Zeebra's P1 and P4 arms
  (§5).

### 8.2 Driver identity

| Build | Driver source | grobx | Driver SHA-256 | `build` id |
|---|---|---|---|---|
| M33 (#966), 2026-11-20 | #966's branch | 0.155.1 `8005a2a1` | `fdd6aeecac466d3702f1e459f1e1456b72f5444d3563f193b5693df44ce183bc` | `7028b2213283e107…` |
| This issue, private rebuild, 2026-11-22 | `main` `3fc16682` | 0.155.1 `8005a2a1` | `fdd6aeecac466d3702f1e459f1e1456b72f5444d3563f193b5693df44ce183bc` | `7028b2213283e10744394725e5e6142c07cd192e09d55f1689e863c1b3b21f8f` |

The `build` id hashes the driver's manifest, lock, toolchain file, `src/main.rs`, `build.rs` and the
effective compiler settings (`tools/external/grobx-driver/README.md`). The two builds agree on all
of them, and on the binary's hash. The driver's `src/main.rs` has not changed since M33 except for
the pinned revision string.

### 8.3 grobx capability matrix

Legend:

- **smoke**: confirmed by a completed run in `smoke.jsonl`.
- **refused**: the driver or engine returns a typed error, also confirmed by a run.
- **upstream only**: documented in upstream `MANUAL.md`, but not reachable through the driver.

| Axis | Cell | Through the driver | Upstream (0.155.1) | Smoke cell(s) |
|---|---|---|---|---|
| Field | GF(2) | smoke | the `Gf2` kernel, byte coefficients | `gf2` |
| Field | GF(3) | smoke | `Gf31` | `gf3` |
| Field | prime p < 2³¹ | smoke | `Gf31` | `p32003`, `p2^31-1` |
| Field | prime 2³¹ ≤ p < 2⁶⁴ | smoke | `Gf64` | `p2^32+15`, `p2^64-59`, `lex-wide` |
| Field | extension GF(pⁿ), n > 1 | refused (`characteristic 4: …`) | **not supported** | `gf4-as-modulus` |
| Field | ℚ | refused (`invalid modulus`) | upstream only (multi-modular lift) | `rationals` |
| Order | grevlex | smoke | yes | every field cell |
| Order | lex | smoke | yes: grevlex then FGLM when zero-dimensional and D ≤ 65535, else F4 in lex | `lex-zero-dim`, `lex-wide`, `lex-positive-dim` |
| Order | deglex (graded-lex) | refused (`unsupported order`) | upstream only | `deglex` |
| Order | block | refused (`unsupported order`) | upstream only (`block:k1,…`) | `block` |
| Order | weighted | — | no; only the checker takes a weight matrix | — |
| Output | reduced GB | smoke, including a nonradical ideal and the unit ideal | the only output | `nonradical`, `unit-ideal` |
| Output | points, radical, RUR, triangular set | — | none | — |
| Workers | 1 | smoke | computes on one thread | every completed cell |
| Workers | > 1 | refused (`this revision computes on one thread`) | accepted and ignored | `workers-16` |
| Mode | raw | smoke | the default | every completed cell |
| Mode | certified (cofactors plus the exact checker) | smoke; `certified = true` on all 11 completed cells | `CheckerMode::Exact` | every completed cell |
| Mode | cheap (checker at k random points) | refused (`unsupported objective`) | upstream only (`CheckerMode::Cheap { points }`) | `cheap` |

What this means for head-to-heads:

- **Extension fields are never grobx head-to-heads.** A GF(pⁿ) row, for n > 1, compares Zeebra with
  Singular or with nothing.
- **Graded-lex is outside the driver.** That is also where the Zeebra signature engine is ineligible
  (§3.1). A grlex comparison would need a driver change and is not needed for M34.
- **A lex row's grobx cost includes its grevlex run and FGLM.** Zeebra's comparable arm is S2
  (`grevlex-fglm`), which also pays both stages, not a lex-F4 arm alone.
  - On positive-dimensional input, grobx restarts in lex after the grevlex run, and both runs are
    its cost. The `lex-positive-dim` cell's report shows the grevlex signature run followed by a
    plain lex run.

### 8.4 Acceptance modes

Every attempt carries exactly one label. Head-to-heads compare like with like, or print the
difference on the row (plan §8.1).

| Mode | Meaning | Zeebra arms | grobx | Checking cost the arm pays |
|---|---|---|---|---|
| **deterministic** | No random choice can change the output | Conventional F4 and the signature engine (every T-GB arm in §5); classical FGLM | **raw**, but only when every `run` line of the call report says `reduce=rows` (in the smoke set, only `gf3`) | none, or `certify_f4_output` when the arm turns it on |
| **exactly certified randomized** (Las Vegas) | A random step whose result is verified exactly, with a retry or a deterministic fallback | `ConversionStrategy::{Adaptive, Wiedemann}` when the route is Wiedemann (shape relations verified, otherwise classical); root finding in `solve_one*` and `solve_zero_dimensional*` (every point substituted) | **certified**: tracking cofactors turns off random tests and combinations (`reduce=rows` on every certified smoke cell), then the exact independent `grobx-checker` runs | Wiedemann: the shape-relation evaluation, inside the route. grobx: cofactor tracking plus the exact check, inside `solve_ns` |
| **probabilistic** (Monte Carlo) | The output may be wrong, with a stated bound | none on `main` (#955 and #1038 study one) | **raw** when any `run` line says `reduce=tests` (signature rounds, p ≥ 5), `sketches` (GF(2)) or `combinations` (plain rounds, p ≥ 46341) | none. Error bound ≤ 2⁻³¹ per test or sketch (upstream *Matrices and reduction*, *Signatures*). Upstream states no bound for block combinations |

Rules:

- **grobx raw is not deterministic.** Label it from the call report, per attempt, not from the
  field. The driver keeps the report, so #1008 can derive the label mechanically. In the smoke set:
  - every raw cell with p ≥ 5 reported `reduce=tests`;
  - the GF(2) raw cell ran the plain engine with `reduce=sketches`;
  - only GF(3) raw reported `reduce=rows`.
- **A fixed seed does not make raw deterministic.** The driver fixes the seed at 0, so a run is
  reproducible. The error bound is still a probability over seeds, and a fixed seed can be wrong on
  some input every time.
- **What each check establishes.**
  - `certify_f4_output` (Zeebra) checks I ⊆ ⟨G⟩, Buchberger's criterion and reducedness. It takes
    ⟨G⟩ ⊆ I from F4's row derivation, so it is complete only for Zeebra's own output.
  - `certify_submitted_basis` runs the same checks but leaves `is_complete` false on a foreign
    basis. A foreign basis needs `certify_submitted_basis_with_witnesses` and its cofactors.
  - `grobx-checker`'s exact mode expands every cofactor row, so it establishes both inclusions on
    grobx's own output.
  - Both engines report the certificate's cost separately: roughly |G|²/2 normal forms, plus
    cofactor expansion. The cost is charged to the arm that asks for the certificate.
- **A digest match is validation, not proof.** An equal `m33-basis-v1` digest against an
  independent reference shows that two engines agree on that instance.
  - It is the common correctness audit, recorded and not charged (plan §8.4).
  - It is not an algorithmic correctness argument, and it never upgrades an arm's acceptance mode.
- **Historical cost of the gap.** On MQ10, at pin `1854835d`, grobx certified took about 16 s and
  raw about 0.16 s (#714, #955; historical, not re-measured here). A raw grobx row never stands in
  for a certified one, in either direction.

### 8.5 Contract rows for candidate algorithms

These rows extend §2 for outputs that #1028's candidates may produce. Only the first five are
produced by any Zeebra arm or grobx cell today.

| Contract | Coefficient field | Solution field | Multiplicity | Supported operations | Cost of a conventional output from it |
|---|---|---|---|---|---|
| Complete reduced GB (T-GB) | as given | — | preserved | membership, normal form, Hilbert series, conversion | — |
| Order conversion (T-GB-conv) | as given | — | preserved | as T-GB | both stages charged |
| Radical representation (T-RAD) | as given | — | removed | radical membership | none: it is not convertible to T-GB when I ≠ √I |
| One base-field point (T-PT1) | F_q | F_q | — | substitution check | — |
| All base-field points (T-PTALL) | F_q | F_q | — | complete enumeration | — |
| Algebraic solution representation (T-ALG) | F_q | F̄_q, stated | stated (RUR or shape form) | points over extensions, degree | to a lex GB: interpolation, which must be counted |
| **Structured representation** | as given | F̄_q | stated per component | triangular set or chordal network: membership per component, point enumeration | to a GB of I: recombining the components. This is not free, and it is charged whenever a head-to-head needs a GB |
| **Sparse/semigroup basis** | as given | (F̄_q^*)ⁿ for Laurent formulations | stated | normal form in the semigroup algebra | **not an ordinary GB.** A Laurent formulation omits the coordinate-zero solutions, which must be accounted for separately, for example by saturation or by recovering those components |

Fixed facts:

- **Adding x_i^q − x_i changes the ideal.** It keeps the base-field solution set but generally
  changes the ideal, and so changes the contract (§2 T-RAD, §3.2).
- **A black-box linear solve is not F4 echelonization (#58).** A nullspace vector or a black-box
  solve does not give the reduced row echelon form whose pivots the next batch depends on.
- **A digest match on benchmark instances is validation, not a correctness argument** (§8.4).

### 8.6 What a deciding run must record (to #1008)

- **The comparand identity**, from the driver's `--version`: revision, version, `build` id and
  SHA-256.
- **The acceptance mode**, per attempt, derived from the call report (§8.4).
- **grobx's `stopped` reason** (`deadline`, `cancel` or `memory`), kept distinct from a driver
  refusal, which is `unsupported`.
- **`certified = false` is `incorrect-output`**, not a timeout.
