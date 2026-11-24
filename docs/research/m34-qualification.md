# M34 candidate qualification (G2)

**Issue:** #1011 (tracker #1043, plan [`docs/MILESTONE-GENERALIZABLE-SELECTION.md`](../MILESTONE-GENERALIZABLE-SELECTION.md)
§7.2, §7.6, §8.6). **Measured at:** Z0 = `28df047f` (tag `measured/1011-z0`). **Status:** complete. Every candidate has a decision (§3, §7). The only timed figures are #997's
gate ratios (§7.1), measured at Z0 `28df047f` with harness `2099df6e`, jobs `1076f513f424` and
`d05e8d60ef86` (2026-11-24).

## 1. Z0 freeze

The owner decision is on #1043 ([comment](https://github.com/mfaulk/zeebra/issues/1043#issuecomment-7108344406),
2026-11-23).

- **Revision:** `main` at `28df047f28a87ab2da3e2077e07c56833d0cb0e1`, tag `measured/1011-z0`.
- **Why this commit.**
  - It descends from the #1002 fix. The plan names that fix by its pre-rewrite hash `03e1ab2f`. Its
    twin on the rewritten `main` is `de9d9f2c`, with an identical `src/` tree.
  - It also contains the #1049 graded-lex refusal (`b38bd833`), the grobx pin move (`036c1de2`),
    #1084's forward-pass fix (`4bd502cb`) and #1022's canonical serialization (`2d85c480`).
  - The only later measured-path change is #1080 (`1e3aaf39`). Its Hilbert-count skipping is opt-in
    and off by default, so no arm differs from the commit before it.
  - Freezing at the head avoided an immediate re-qualification under §8.6's revision-bump rule.
- **Comparand pins:** grobx 0.155.1 `8005a2a1670a7264617a6f49eeb2618d7fa21701` (#1029 §8.1) and
  msolve 0.11.0. #1043 records both as owner decisions.
- **Binaries.** Built from `git archive measured/1011-z0` with
  `cargo build --locked --release --features research-sigf4 --example sig_f4_study --example m33_qualify`.
  The flags are fat LTO, one codegen unit and x86-64-v3 (from the archived `.cargo/config.toml`),
  with `RUSTC_WRAPPER=""` and `CARGO_INCREMENTAL=0`.

| Binary | SHA-256 |
|---|---|
| `sig_f4_study` | `93463c2ba800517233dde3c4a2835879d47367c5d9e8cd77b2b5b7c02d5f0d49` |
| `m33_qualify` | `11e52687b86dcf998debe12276ee2b0a7bd5e1a85f5be2145e906ea76254c817` |

Toolchain: rustc 1.99.1 (58cf8f9c3 2026-10-13).

## 2. Safety prerequisites (plan §7.6)

These ran at Z0 with `cargo test`, in the debug test profile, on 2026-11-23. They must pass before
any parallel arm is admitted.

| Check | Test | Result |
|---|---|---|
| `m33_safety`: every budget M33 relies on, tripped at 1 and 16 workers | `tests/m33_safety.rs` (4 tests: cancellation, live bytes, matrix rows, wall) | pass, 4/4 |
| `m33_thread_cap`: thread high-water within the worker cap | `tests/m33_thread_cap.rs` | pass |
| #1042 team test: no more than `workers` live worker threads across back-to-back teams | `grobner::f4::tests::test_parallel_f4_teams_never_exceed_the_worker_cap` | pass |
| #961 routing: graded-lex goes to the shipping F4 on every #961 row shape, at 1/4/8/16 workers | `grobner::sigf4::dispatch::tests::test_graded_lex_routes_to_shipping_on_every_961_row` | pass |

The parallel arms P2, P3, P5, P6 and P8 are therefore cleared on safety at Z0. Correctness and the
regime question are still open for every arm.

## 3. Candidates and status

The candidates come from #1004 (`docs/research/adaptive-selection-contracts.md` §5, §6) and plan
§7.2. Eligibility is checked from #1004's matrix first and is never inferred from performance.

| Candidate | Port cost | Correctness (digest vs reference, 1 and max w) | Budgets and threads | Regime | Decision |
|---|---|---|---|---|---|
| P1 `conv-w1` | none (on Z0) | **pass**, 61 of 62 rows; 1 typed stop (§4.1) | `m33_safety` pass | #1004 §5 (pre-declared; #1012 tests it) | **admit to #1012** (owner decision, §7) |
| P2 `conv-w4` | none | **pass**, 61/62; 1 typed stop | `m33_safety`, thread cap, #1042 pass | #1004 §5 (pre-declared; #1012 tests it) | **admit to #1012** (owner decision, §7) |
| P3 `conv-w16` | none | **pass**, 61/62; 1 typed stop | as P2 | #1004 §5 (pre-declared; #1012 tests it) | **admit to #1012** (owner decision, §7) |
| P4 `sig-w1` (grevlex) | none | **pass**, 40/40 grevlex; `Unsupported` on all 22 grlex/lex rows | `m33_safety` pass; grlex refused (#1049) | #1004 §5 (pre-declared; #1012 tests it) | **admit to #1012** (owner decision, §7) |
| P5 `sig-w8` (grevlex) | none | **pass**, as P4 (team of 8) | as P2 | #1004 §5 (pre-declared; #1012 tests it) | **admit to #1012** (owner decision, §7) |
| P6 `sig-w16` (grevlex) | none | **pass**, as P4 (team of 16) | as P2 | #1004 §5 (pre-declared; #1012 tests it) | **admit to #1012** (owner decision, §7) |
| P7 `conv-cap16` | none | **pass**, 122/124 cells at 1 and 16 w; 2 typed stops. Cap-16 digest check done | `m33_safety` pass | #1004 §5 (pre-declared; #1012 tests it) | **admit to #1012** (owner decision, §7) |
| P8 `adaptive` | none | **pass**, 122/124 at 1 and 16 w; 2 typed stops. Signature route on 60 grevlex cells | as P2; #961 routing pass | #1004 §5 (pre-declared; #1012 tests it) | **admit to #1012** (owner decision, §7) |
| #940 parallel symbolic (`measured/940-gate-s2`) | beyond the 2-session time-box (§6) | — | — | #1040's recommendation not posted | **deferred: port cost** |
| #997 fewest-terms + FL order | none (options on Z0, §5) | **pass**, 122/124 at 1 and 16 w; 2 typed stops. Eligible | the shipping F4's budgets | MQ10 / GF(2³¹−1) at 4 w (#993), preregistered (§7) | **reject**: Cyclic-8 regresses in 5 of 6 cells (§7.1) |
| #955 randomized zero-skipping | — | — | — | — | excluded: no exact acceptance rule (#1004) |

## 4. Correctness harness

- **Harness.** `examples/m33_qualify.rs` gains the #1011 engines, each `f4` with one option changed
  over the shared wall and worker settings:
  - `cap16`: `max_pairs_per_batch = Some(16)`, for P7;
  - `adaptive`: `GradedEngine::Adaptive`, for P8, with `graded_route` recorded;
  - `fewest-fl`: `ReducerSelection::FewestTerms` with `BatchOrder::FaugereLachartre`, for #997;
  - `sig`: the forced signature engine, `sig_f4_reported` with the dispatch's team options, for P4–P6
    (`research-sigf4` builds only).
- **Campaign.** `research/m34-qualification/campaign.py` runs each arm on M33-Q's 62 correctness rows
  on the five fields: 40 grevlex, 10 grlex, 12 lex, 744 cells in all. Every cell is one fresh process.
  - **Workers.** Conventional arms run at 1, 4 and 16, signature arms at 1, 8 and 16, and P7, P8 and
    #997 at 1 and 16.
  - **References.** Each digest is compared with M33-Q's independent reference
    (`research/m33-qualification/references.json`): Singular below 2³¹, groebner-rs on the wide
    fields. The input digest must match the reference's input.
  - **Off grevlex.** Here the signature arms are checked for their typed `Unsupported` refusal, not
    run for a basis.
  - **Stops.** A typed budget stop is reported as `stopped`, never as a pass.

### 4.1 Correctness result

- **Run.** All 744 cells ran on 2026-11-23, untimed, at Z0 `src/` with harness commit `2099df6e`.
  - **Binary:** `m33_qualify` release with `research-sigf4`, SHA-256
    `e4df6228cfb8b0ddb0948e532e75a15b37cf4e4d3fbe08bd0a14d9a2fe812ae4`.
  - **CPUs:** three arm groups in parallel on CPUs 24–47, 48–71 and 88–127.
  - **Records:** `research/m34-qualification/results/correctness.jsonl` and `correctness.md`.
- **Totals.** 669 basis passes, 66 expected refusals and 9 typed budget stops. **No failure:** no
  digest differs from its reference, no input drifted, nothing crashed, and nothing was refused
  unexpectedly.

| Arm | GF(32003) | GF(2³¹−1) | 2⁶⁴−59 | 2⁶⁴−353 | Goldilocks |
|---|---|---|---|---|---|
| P1 conv-w1 | pass 13 | pass 14 | pass 7 | pass 16 | pass 11, stopped 1 |
| P2 conv-w4 | pass 13 | pass 14 | pass 7 | pass 16 | pass 11, stopped 1 |
| P3 conv-w16 | pass 13 | pass 14 | pass 7 | pass 16 | pass 11, stopped 1 |
| P4 sig-w1 | pass 13 | pass 14 | pass 7 | pass 16 | pass 12 |
| P5 sig-w8 | pass 13 | pass 14 | pass 7 | pass 16 | pass 12 |
| P6 sig-w16 | pass 13 | pass 14 | pass 7 | pass 16 | pass 12 |
| P7 conv-cap16 (1 and 16 w) | pass 26 | pass 28 | pass 14 | pass 32 | pass 22, stopped 2 |
| P8 adaptive (1 and 16 w) | pass 26 | pass 28 | pass 14 | pass 32 | pass 22, stopped 2 |
| #997 fewest-fl (1 and 16 w) | pass 26 | pass 28 | pass 14 | pass 32 | pass 22, stopped 2 |

- **Signature arms.** Their passes include the 22 grlex and lex rows, each refused with
  `Unsupported` as the contract requires. The engine ran at its requested team on every grevlex
  cell: 1, 8 and 16.
- **The 9 stops.** All are on one row, graded-lex Goldilocks MQ11.
  - Eight are `TooManyNonzeros` at the default 32 M budget: P1–P3, P7 at 16 w, P8 at both counts,
    and #997 at both counts.
  - One is P7 at 1 w, which reached the 180 s wall budget (`TimeBudgetExceeded`).
  - This row is M33-Q's documented budget stop (#961's table), where the reference is recorded but
    nothing is compared with it. P8 routes it to the shipping F4 by rule (`Shipping(Order)`), and
    the signature arms refuse it.

## 5. #997 (fewest-terms reducer rule with the FL batch order)

- **Port cost:** none. Both options are on Z0 (`ReducerSelection::FewestTerms`,
  `BatchOrder::FaugereLachartre`).
- **Eligibility.** The reducer rule changes which reducer row covers a column, not the pair set. The
  FL order changes how a batch is eliminated, not its row space (`BatchOrder` docs: both orders give
  the same candidate rows). The reduced basis is unique, so the arm is T-GB-eligible under every
  order in principle. The harness confirms it by digest on the qualification set (§4.1), so it is
  **eligible** on T-GB under grevlex, grlex and lex.
- **Already in tree.** `FewestTerms` alone is already in the differential sweep (`differential/mod.rs`).
  The combination is not.
- **Regime.** #997's own gate (gated by monomial order, no Cyclic-8 regression) is a timed read, so
  it waits for a quiet window.

## 6. #940 port-cost estimate (time-box: 2 sessions, plan §12)

- **Ref.** `measured/940-gate-s2` = `62cbe4de`, on base `ce67df76` (2026-11-19).
- **Its change:** +1,489 / −30 in `src/grobner/sigf4/`. That is a new `symbolic.rs` (882 lines), its
  tests (468), `engine.rs` +147 and `mod.rs` +22.
- **Drift since that base.** Z0 has changed the same module by +1,829 / −123 across 10 files:
  - #994's run-wide monomial table (`table.rs`, and `engine.rs` +501);
  - #1001's interreduction in engine column space (`interreduce.rs`);
  - the dispatch rework (`dispatch.rs` +290).
- **Textual merge** (`git merge-tree 28df047f 62cbe4de`): three conflicted hunks in `src/`, two in
  `engine.rs` and one in `mod.rs`, plus two documents.
- **Semantic conflict.** This is the real cost. #940's closure keys columns by `Monomial<N>` with
  per-batch maps, and takes the reducer cache as a separate `&mut MonomialMap`. Z0's batch closure
  interns into the run-wide `MonomialTable`, which is single-writer (`intern(&mut self)`,
  `set_reducer(&mut self)`) and holds that reducer cache itself. A port therefore has to
  redesign the parallel closure around concurrent (or per-level merged) interning into the
  run-wide table. That is a new design. It also has to re-establish:
  - #940's matrix and cache identity oracle (`check_signatures`);
  - its wall and live-byte budgets;
  - Gate P's digest equality.
- **Estimate.** Larger than the original #940 implementation (11 commits), so beyond the 2-session
  time-box.
- **Decision under the plan's stop condition:** **deferred: port cost.** The M32 rejection as a
  default stands (`research/m32-gate-s/README.md`).
- **If #1040 posts a feature-predicted regime here,** that changes the case for a port, not this
  estimate.

## 7. Owner decision, admissions and the #997 gate

The owner adopted the proposal on #1043
([comment](https://github.com/mfaulk/zeebra/issues/1043#issuecomment-7135042005), 2026-11-24),
before any deciding read.

- **P1–P8: admitted to #1012** on the regimes #1004 pre-declared
  (`adaptive-selection-contracts.md` §5). There is no new timed read in #1011.
  - Each passed correctness (§4.1) and the safety prerequisites (§2) on Z0.
  - Admission makes no performance claim. #1012's matrix and Gate H test the regimes.
- **#940: deferred, port cost** (§6).
- **#955: excluded.** No exact acceptance rule exists (#1004).
- **#997: rejected** by its preregistered gate (§7.1). The rule is
  [`research/m34-qualification/gate997.json`](../../research/m34-qualification/gate997.json),
  committed before the read.
  - **Statistic.** `fewest-fl` ÷ the shipping F4, process wall, paired per repetition, with a 95%
    bootstrap interval. Only clean attempts whose digest equals an independent reference count.
  - **Run.** n = 9 in publication mode on CCDs 1–2, with the arms rotated.
  - **No-regression gate.** Cyclic-8 (grevlex) on GF(32003) and 2⁶⁴−353 at 1, 4 and 16 workers. It
    passes only if every upper bound is ≤ 1.05. This is job `1076f513f424`, 108 attempts.
  - **Regime read.** MQ10 (`mq-random-10-s10`) on GF(2³¹−1) at 4 workers. It passes only if the
    upper bound is < 1. This is job `d05e8d60ef86`, 18 attempts.
  - **Decision.** Admit only if both pass. Reject if any Cyclic-8 cell fails. Otherwise (no MQ10
    win, or a cell short of 9 counted pairs) defer.
  - **References** (`gate997-references.json`, untimed, CPUs 24–39):
    - Cyclic-8 on GF(32003): Singular `std`/`redSB` in `dp`.
    - Cyclic-8 on 2⁶⁴−353: grobx 0.155.1 in certified mode, a proof-checked basis. The groebner-rs
      driver is not provisioned on this machine.
    - MQ10: M33's Singular reference, with the same input digest.
  - **Committed manifests:** `research/m34-qualification/manifests/`.
- **How it ran:**
  `ZB975_THREADS=0 ZEEBRA_BENCH_JOBS=<jobs> research/m33-final/session.sh 997 1076f513f424 d05e8d60ef86`
  (one reservation for both jobs), then `gate997.py verdict --job-dir <jobs>/1076f513f424 <jobs>/d05e8d60ef86`.

### 7.1 #997 gate result

- **Run.** 2026-11-24 19:12–19:20Z, publication mode, CCDs 1–2 reserved and then released. Measured
  at Z0 `28df047f` with harness `2099df6e` (`m33_qualify` SHA-256 `e4df6228…`). The table is
  [`research/m34-qualification/gate997.md`](../../research/m34-qualification/gate997.md), and the
  journals are retained under `research/m34-qualification/journals/`.
- **Cyclic-8 job `1076f513f424`:** 108 of 108 attempts clean, and every one equals its reference.
- **MQ10 job `d05e8d60ef86`:** 16 of 18 clean. Two were flagged by the clock rule, which is 11%, under
  the 20% void limit. Every digest equals its reference.

| Row | Workers | Pairs | fewest-fl ÷ f4 [95%] | Rule | Verdict |
|---|---:|---:|---|---|---|
| Cyclic-8 / GF(32003) | 1 | 9 | 1.028 [1.018, 1.034] | upper ≤ 1.05 | pass |
| Cyclic-8 / GF(32003) | 4 | 9 | 1.114 [1.102, 1.117] | upper ≤ 1.05 | fail |
| Cyclic-8 / GF(32003) | 16 | 9 | 1.193 [1.183, 1.203] | upper ≤ 1.05 | fail |
| Cyclic-8 / 2⁶⁴−353 | 1 | 9 | 1.056 [1.054, 1.060] | upper ≤ 1.05 | fail |
| Cyclic-8 / 2⁶⁴−353 | 4 | 9 | 1.122 [1.110, 1.126] | upper ≤ 1.05 | fail |
| Cyclic-8 / 2⁶⁴−353 | 16 | 9 | 1.185 [1.172, 1.192] | upper ≤ 1.05 | fail |
| MQ10 / GF(2³¹−1) | 4 | 7 | — | upper < 1 | short |

- **Decision: reject #997** under the preregistered rule, which rejects on any Cyclic-8 failure.
  - The candidate regresses Cyclic-8 by 11–19% at 4 and 16 workers on both fields. At 1 worker it
    reads 1.028 (a pass) on GF(32003) and 1.056 (a fail) on 2⁶⁴−353.
  - The MQ10 cell has 7 counted pairs, so it is short and was not read. No extension was run,
    because no MQ10 outcome could change a reject.
- **Scope.** The reject applies to #997's candidate as one portfolio arm (fewest-terms with the FL
  order, ungated). An order- or family-gated variant would be a new candidate.
- **After the squash merge,** tag the cited commits as `measured/1011-*`: Z0 is already tagged
  `measured/1011-z0`, and the harness `2099df6e` needs its own tag.
