# M34 adaptive-selection findings and next-stage recommendation (#1015)

**Measured at:** `36fd4137` (tag `measured/1012-matrix`; the Gate H records, built from harness
`6c77117a` = tag `measured/1012-harness`, `src/` identical to Z0 `28df047f` = tag `measured/1011-z0`).
No new measurement: every figure is quoted from a tagged source named where it is used, or re-read
from the retained #1012 records by [`research/m34-selection-findings/cells.py`](../../research/m34-selection-findings/cells.py).
**Status:** complete, 2026-11-25. **Recommendation: stop building a general selector on this
evidence**; keep `GradedEngine::Adaptive` as the reference fixed arm; run three bounded follow-ups
(§8).
**Plan:** [`docs/MILESTONE-GENERALIZABLE-SELECTION.md`](../MILESTONE-GENERALIZABLE-SELECTION.md)
§5, §9.1, §10.1 (M-3). **Tracker:** #1043. **Claims (plan §5):** none of C1–C3 is established
here. Gate H decides whether a selector is worth building. It is not a regime win (C1), not a
generalization result (C2), and not an adoption (C3).

Every conclusion below is labelled:
- **generalizes**: it held on untouched families or scales;
- **distribution-specific**: it held only on the named families, fields or cohort;
- **hypothesis**: it has not been tested out of sample.

No conclusion in this report is labelled **generalizes**. The untouched cohort was sealed and never
read (§4), so nothing here was tested on it.

## 1. Revisions, data and tools

| What | Revision | Tag / record |
|---|---|---|
| Plan, thresholds | `03e1ab2f` planning base; Gate H thresholds of 2026-11-22 (plan §9.1) | PR #1048 |
| Z0 (every arm) | `28df047f` | `measured/1011-z0`; owner decision on #1043 (2026-11-23) |
| Comparand pins | grobx 0.155.1 `8005a2a1`; msolve 0.11.0 | #1029, `adaptive-selection-contracts.md` §8 |
| Corpus catalogs | `3d21098c` (#1128), canonical catalog sha `95e4523e…` | `research/m34-public-corpus/`, `research/m34-structural-corpus/` |
| S0 seal | `2db433b2` | `measured/1012-s0`, `research/m34-gate-h/s0/` |
| Gate H harness | `6c77117a`; `m34_matrix` SHA-256 `ee381510…7683` | `measured/1012-harness` |
| Gate H records | `36fd4137` (identical to `main` at `80703092`) | `measured/1012-matrix`, `research/m34-gate-h/results/` |
| Feature costs | `6d46e583` (#1009 table); `3d21098c` (Gate H's VBS⁺ charge) | `measured/1009-feature-costs`; `research/m34-gate-h/results/features.jsonl` |
| Qualification | `28df047f`; #997 gate harness `2099df6e` | `measured/1011-harness`, `measured/1011-results` |

Tools: `tools/bench-job` (selection-grade records, #1008), `tools/corpus_lineage.py` (#1005),
`research/m34-gate-h/{campaign,analyse,summary}.py` (#1012), and `cells.py` here.

## 2. Contracts and eligibility (#1004, #1029)

- **Contracts.** T-GB, T-GB-conv, T-RAD, T-PT1, T-PTALL and T-ALG are written separately in
  [`adaptive-selection-contracts.md`](adaptive-selection-contracts.md) §2. Gate H used **T-GB only**.
  Every development record was grevlex: the forced signature engine refuses grlex and lex
  (`Unsupported`, #1049), and it completed or was penalized on all 122 records, never refused.
- **G0 passed.** Under grevlex, three arms are exactly interchangeable on T-GB: conventional F4,
  `GradedEngine::Adaptive` and the forced signature engine. Under grlex, lex and weighted orders only
  conventional F4 remains, so selection there is a choice of workers or batch cap, not of engine.
- **#961** keeps the signature engine ineligible (routed) under graded-lex. No signature-route
  configuration is called production-safe here.
- **#1029** fixed one grobx pin for every deciding M34 run, and the capability and acceptance-mode
  tables. Gate H had no external comparand. The pin matters to #1033, #1039 and #1044 only.

## 3. Corpus, lineage and splits (#1005, #1006, #1007)

- **Pilot:** 127 base problems in 36 families (23 public-application families from #1006, 13
  controlled structural families from #1007). Composition table:
  [`research/m34-structural-corpus/README.md`](../../research/m34-structural-corpus/README.md#pilot-composition-1006--1007).
- **§8.2 composition.** Met on every clause except two scales per family: 13 single-model public
  families have one scale. The owner waived that clause for them (#1043, decision 8, recorded before
  S0). Those families, `sd/ellipsoid` among them, **cannot carry a scale-generalization claim**.
- **Lineage and leakage.** `family_id`, `formulation_id`, `support_id` and the presentation parent
  are recorded per instance (#1005, [`corpus-lineage.md`](corpus-lineage.md)). The S2, S3 and
  S5-field checks pass on the sealed split.
- **S0.** #1005 closed without the freeze commit, so S0 was sealed under #1012 (its J1) with #1005's
  own tool, before the matrix was read. Draw: S2, salt `m34-s0-v1`, `hash-groups-v1`, over 34
  groups.

| Cohort | Groups | Records | Status |
|---|---:|---:|---|
| Development | 17 families | 122 (64 base problems) | read by Gate H |
| Validation | 7 | 44 | **sealed, unspent** |
| Untouched | 10, plus carve-outs `zb/toric` p64 (S5) and `sd-singular-schwarz-11` (S3) | 88 | **sealed, unspent** |

- **Exposure.** The Katsura, Cyclic, Eco, Noon and Reimer ladders are M29–M33 relatives and were
  forced into development. #978 had already read some of their rows.

## 4. Records and statuses (#1008)

Every attempt carries one `selection-outcome-v1` status
([`benchmark-schema.md`](benchmark-schema.md) §8). Gate H's 7,012 attempts:

| Status | Attempts |
|---|---:|
| `completed-verified` | 6,558 |
| `completed-unverified` | 414 |
| `memory-refusal` | 37 |
| `timeout` | 3 |
| `rss-limit`, `unsupported`, `process-failure`, `incorrect-output`, `not-run` | 0 |

- **Unverified completions.** All 414 are on the nine records without a panel reference. Gate H's J3
  verifies such a cell when a conventional and a signature arm agree on its digest. That holds on
  every one except `gen-chandrasekhar-h-13`, which no signature arm completes. It is penalized on
  every arm and is the cohort's only frontier problem.
- **No ladder-censored cells.** All 1,220 cells (122 records × 10 configurations) ran in pass 1.
- **Contamination.** `bench-job` flagged 173 attempts as contaminated. A cell uses its clean
  repetitions, and falls back to all of them only when none is clean.
- **No `incorrect-output`**, so no arm was disqualified (distribution-specific: development cohort,
  Z0).

## 5. Features and their cost (#1009; #1010 not run)

From [`input-features.md`](input-features.md) §8–§10 (`measured/1009-feature-costs`, `6d46e583`,
public pilot panel):

- **Bound:** 1% of the cheapest arm's solve per feature, and 2% for the set, at the worst small input.
- `is_homogeneous` (0.07%), `leading_profile` (0.48%) and `linear_subsystem` (0.99%, at the margin)
  pass.
- `analyze` (2.5%), `incidence` (1.5%), `scalar_substitutions` (1.1%) and `support_profile` (6.5%)
  fail, every failure on inputs solved in under 0.4 ms. They moved to #1010. They are not dropped,
  and a policy that reads them is charged their measured cost. The set fails at 10.5%.
- **Gate H's VBS⁺** is charged the full set's measured cost per record (`features.jsonl`). Four
  `zb-col-grid` records could not be instantiated by `feature_costs` and take the J4 fallback, the
  largest measured cost.
- **#1010** (bounded structural features) was a stretch candidate and did not run.

**Classification: distribution-specific.** Cheap features are not cheap relative to sub-millisecond
solves, so any future selector needs a size gate before extraction.

## 6. Candidate qualification (#1011)

From [`m34-qualification.md`](m34-qualification.md) (Z0 `28df047f`):
- **Safety prerequisites on Z0:** `m33_safety` (4/4), `m33_thread_cap`, the #1042 team test and
  #961's routing test all pass.
- **Correctness:** 744 cells, 0 failures (PR #1100).
- **Admitted to Gate H**, on the regimes #1004 pre-declared (owner decision of 2026-11-24 on #1043):
  - P1/P2/P3: conventional F4 at 1/4/16 workers. P3 is the shipping default.
  - P4/P5/P6: signature F4 at 1/8/16 workers, grevlex only.
  - P7: the `MEMORY_PAIR_CAP` policy, at 1 and 16 workers.
  - P8: `GradedEngine::Adaptive`, at 1 and 16 workers.
- **Rejected:** #997 `FewestTerms`, 11–19% slower on Cyclic-8 at 4 and 16 workers under the
  pre-registered 1.05 bar.
- **Deferred:** #940 (retained M32 parallel symbolic), on port cost.
- **Excluded:** #955 (no exact acceptance rule).

## 7. Performance matrix and Gate H (#1012)

The full read is [`m34-gate-h.md`](m34-gate-h.md) and
[`research/m34-gate-h/results/gate-h.md`](../../research/m34-gate-h/results/gate-h.md). Costs are
PAR-2 penalized (2C = 600 s), not runtimes.

| Arm set | H | 95% interval | families ≤ 0.85 | H without largest contributor | split halves | Clauses failed |
|---|---:|---|---:|---|---|---|
| **Go rule** | ≤ 0.80 | upper ≤ 0.87 | ≥ 3 | ≤ 0.85 | ≤ 0.85 each | |
| W16 | 0.703 | [0.392, 0.942] | 6 | 0.895 (`sd/ellipsoid`) | 0.702 / 0.701 | upper bound, drop-one |
| W1 | 0.767 | [0.446, 0.988] | 2 | 0.981 (`sd/ellipsoid`) | 0.765 / 0.764 | upper bound, families, drop-one |
| engine@16w | 0.845 | [0.399, 0.975] | 3 | 0.953 | 0.844 / 0.844 | H, upper bound, drop-one |
| workers@conv | 0.868 | [0.757, 0.953] | 4 | 0.926 (`katsura`) | 0.868 / 0.864 | all but families |
| workers@adaptive | 0.925 | [0.779, 0.985] | 4 | 0.944 (`katsura`) | 0.925 / 0.925 | all but families |

**Verdict: no-go.** No context and no single-decision arm set meets every Go clause, so narrow go
fails too. Under plan §6.2, #1013 and #1014 closed *not planned*. No threshold was changed. Sensitivity
views, which do not decide: PAR-10 H is 0.681 at W16 and 0.743 at W1. On the 61 problems every arm
completes, H is 0.898 at W16 and 0.980 at W1.

### 7.1 What carries the headroom

Two families carry the W16 point estimate: `sd/ellipsoid` (family ratio 0.120) and
`sd/runge-kutta-order-conditions` (0.116). The other 15 families sit between 0.65 and 1.00, most of
them above 0.9. The cells behind the two families
([`cells.md`](../../research/m34-selection-findings/cells.md); medians in ms, **pen** = PAR-2
penalty, not a time):

| Record | conv 1 w (P1) | sig 1 w (P4) | adaptive 1 w (P8-w1) | adaptive 16 w (P8-w16) |
|---|---:|---:|---:|---:|
| `sd-ellipsoid-m2@p31` | **pen** (`TooManyColumns`) | 1,112 | **pen** | **pen** |
| `sd-ellipsoid-m2@p64` | **pen** | 1,116 | **pen** | **pen** |
| `sd-hairer-2@p31` | 49 | 17,462 | 49 | 48 |
| `sd-hairer-2@p64` | 52 | 17,713 | 52 | 50 |
| `sd-butcher@p31` | 12 | 139 | 12 | 12 |

The two families **do not share a structure that one rule could exploit**. They are opposite tail
risks of the engine choice:

- **`sd/ellipsoid` is one problem.** On `sd-ellipsoid-m2` (4 generators of degrees 4, 4, 4 and 6, 13
  terms, non-homogeneous), conventional F4 stops with a typed memory refusal (`TooManyColumns`) at
  every worker count. So do the capped arm and the shipping dispatch, which routes it to
  conventional F4. The signature engine completes it in about 1.1 s. The other two ellipsoid
  problems take 6–8 ms on every arm. This is the only development problem on which the shipping
  dispatch fails while an eligible arm completes. (`zb-col-grid-5x5` is also refused by
  conventional F4, but the dispatch already routes it to the signature engine.)
- **`sd/runge-kutta-order-conditions` is the cost of the wrong fixed arm, not headroom over the
  incumbent.** Leave-one-family-out picks P4 (forced signature, one worker) as the best fixed arm
  when this family is held out. P4 is 390–400× slower than conventional F4 on `sd-hairer-2` and
  12× on `sd-butcher`. The shipping dispatch already routes both to conventional F4 and stays within
  1.15× of the cheapest arm.
- **Both families are single public models** from SymbolicData. `sd/ellipsoid` is single-scale under
  decision 8's waiver.

**Classification:** distribution-specific (two named families, development cohort).

### 7.2 The best fixed arm is the incumbent dispatch

- **P8-w1 is close to the oracle.** `GradedEngine::Adaptive` at one worker is the
  leave-one-family-out best fixed arm in 16 of 17 families, at both W16 and W1. Its family-weighted
  PAR-2 cost is 0.811 of P3's, the shipping conventional F4 at 16 workers (`results/summary.md`;
  descriptive, decides nothing). VBS⁺ is 0.645 of P3.
- **No arm is indispensable at W16.** Removing any one arm moves VBS⁺ by at most 1.1%. At W1,
  removing P4 costs 14.4%, because it is the only W1 arm that completes `sd-ellipsoid-m2`.
- **Where the incumbent is ≥ 1.5× off.** Across all 122 development records, P8-w1 is penalized or
  at least 1.5× the cheapest arm on 12 records, six problems at both fields (`cells.md`, which also
  lists the rows where only P4 is off):
  - `sd-ellipsoid-m2`, penalized;
  - four larger ladder problems (`zb-cyclic-7`, `zb-eco-12`, `zb-katsura-12`, `zb-reimer-6`), where
    the same dispatch at 16 workers is 1.5–2.2× cheaper;
  - `zb-col-ktree2-12-s1`, by 1.57–1.59× on a 9–13 ms solve.

**Classification:** distribution-specific. This development cohort is 87.5% small problems (56 of
64 under 300 ms on their best arm), and one is frontier (1.6%). The composition read labelled 13
pilot problems (10.2%) frontier, but in the matrix only one development problem was frontier under
C = 300 s (no arm completes it). The finding is about this cohort.

### 7.3 Workers, not engines, are where the residual is

At W16, the per-row misses of P8-w1 that are not `sd-ellipsoid-m2` are worker-count misses on the
larger ladder rows; the one other miss, `zb-col-ktree2-12-s1`, is 4 ms on a 9 ms solve. The `workers@adaptive` arm set isolates that decision and reads H = 0.925
[0.779, 0.985], which is no aggregate headroom on this cohort. The cost of the wrong worker count on
a single row is up to 2.2×, though, and the corpus has few rows above 100 ms where it would show.
**Classification: hypothesis** that a size-gated worker count captures most of it (§8, #1135).

## 8. Next-stage recommendation

Plan §9.1's no-go branch asks #1015 to "recommend any fixed default or rule the matrix supports".
The recommendation is to **stop** the general selector line and run three bounded follow-ups, each
with its own predeclared rule.

1. **Stop: no general selector on this evidence.** Gate H failed robustly, not marginally. The
   upper bound is 0.942 against 0.87, and without one family H is 0.895. The narrow single-decision
   sets fail too. A selector would be fitted to two problems. Re-reading Gate H on this corpus
   with different thresholds is excluded (plan §12.2).
2. **Fixed default: `GradedEngine::Adaptive` is the reference arm, not yet a default.** On this
   development cohort it is the best fixed arm (0.811 of the shipping default). Making it the
   default is an adoption question (C3, plan §11). It is not a finding of this report, and it is
   blocked on two things:
   - #961 is open, and no signature-route configuration is called production-safe while it is;
   - #978's misroute is open, and #1115's fix was left unconfirmed (owner action).

   **Classification: distribution-specific.**
3. **Specific further research**, each filed on Project #7 and linked to #1043 and #1003:
   - **A. Signature-engine pathology, #1136.** Attribute the 390–400× slowdown of the
     forced signature engine on `sd-hairer-2`. It is the clearest structural signal in the matrix:
     mixed degrees 1–4 with four linear generators, and 16 workers do not help. It matters to any
     future dispatch that sends more grevlex input to the signature engine. **Hypothesis.**
   - **B. Typed-refusal fallback, #1134.** On a typed resource refusal from the conventional route
     under grevlex, re-run the signature engine with the discarded work charged. This is a
     completion (robustness) rule, so Gate H's average-cost no-go does not decide it. The one
     development instance is `sd-ellipsoid-m2`, and it must be judged on rows it was not designed
     on. **Hypothesis.**
   - **C. Size-gated worker count, #1135.** One worker below a cheap predeclared size
     predicate, the caller's workers above it (§7.3). It must be read on 100 ms–300 s rows, which
     this corpus lacks. It relates to #978 and to the size gate §5 already requires for feature
     extraction. **Hypothesis.**
4. **Corpus coverage before any future selection gate.**
   - The development cohort is small-dominated: the family-weighted PAR-2 aggregate is 21.9 ms for
     VBS⁺ and 27.6–48.9 ms across the arms (`results/summary.md`). Problems of 1–300 s were barely
     sampled: 8 of 64 development problems are not small, and one of those is frontier.
   - A future Gate H should be preceded by a corpus with at least a third of its base problems in
     the 1–300 s band, and at least two scales for every family that carries a family-level
     ratio.
   - Until then the **validation and untouched cohorts stay sealed and unspent** (§3), so a later
     milestone can still read them once. Spending them on any follow-up above is an owner decision.

#1016 (bounded early observation) depended on a static selector. The #1012 agent closed it *not
planned*. That closure is consistent with plan §6.3, which allows #1016 "only after a static
selector exists", but #1016 was a stretch candidate the owner had not yet ruled on, so the owner
may reverse it. #1017 (quotient-algebra conversion features) did not run and stays open outside
M34.

## 9. Negative results and remaining uncertainties

- **Gate H no-go** (#1012); #1013 and #1014 *not planned*; #1016 *not planned* (§8).
- **Four of seven inexpensive features fail their cost bound** on sub-0.4 ms solves (§5).
- **#997 rejected, #940 deferred on port cost, #955 excluded** (§6).
- **The interval is wide** (W16 [0.392, 0.942]). With 17 development families, two of which carry
  the point estimate, the bootstrap cannot support a general claim either way.
- **Single-run harness.** Every Gate H cell was measured in dev mode on CCDs 1–2 in one campaign
  (9.98 of 40 machine-hours). Contamination was handled per cell, not by re-running sessions.
- **Feature-cost fallback.** Four records take the J4 fallback cost, an over-charge to VBS⁺ that
  can only raise H.
- **Untested out of sample:** every hypothesis in §8. No validation or untouched row has been read.

## 10. Reproduction

```sh
# The Gate H read, from the retained records (no solver run):
python3 research/m34-gate-h/analyse.py           # writes results/gate-h.{json,md}
python3 research/m34-gate-h/summary.py           # per-arm aggregates and cohort composition
python3 research/m34-gate-h/test_analyse.py
# This report's per-record table:
python3 research/m34-selection-findings/cells.py > research/m34-selection-findings/cells.md
```

Re-measuring the matrix from scratch follows
[`research/m34-gate-h/README.md`](../../research/m34-gate-h/README.md#reproduce): build
`m34_matrix` from `git archive` of `measured/1012-harness`, then run the three `session.sh`
passes under a CCD reservation, then `collect`. `campaign.py seal` rewrites `s0/` byte for byte from
the catalogs at `3d21098c`.
