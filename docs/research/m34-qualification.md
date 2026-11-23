# M34 candidate qualification (G2)

**Issue:** #1011 (tracker #1043, plan [`docs/MILESTONE-GENERALIZABLE-SELECTION.md`](../MILESTONE-GENERALIZABLE-SELECTION.md)
§7.2, §7.6, §8.6). **Measured at:** Z0 = `28df047f` (tag `measured/1011-z0`). **Status:** in progress.
The safety prerequisites are recorded below. No timed qualification run has been made yet, and this
document publishes no timing or memory figure.

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
| P1 `conv-w1` | none (on Z0) | pending | `m33_safety` pass | pending | pending |
| P2 `conv-w4` | none | pending | `m33_safety`, thread cap, #1042 pass | pending | pending |
| P3 `conv-w16` | none | pending | as P2 | pending | pending |
| P4 `sig-w1` (grevlex) | none | pending | `m33_safety` pass; grlex refused (#1049) | pending | pending |
| P5 `sig-w8` (grevlex) | none | pending | as P2 | pending | pending |
| P6 `sig-w16` (grevlex) | none | pending | as P2 | pending | pending |
| P7 `conv-cap16` | none | pending (#1004: needs a digest check at a cap of 16) | pending | pending | pending |
| P8 `adaptive` | none | pending | as P2; #961 routing pass | pending | pending |
| #940 parallel symbolic (`measured/940-gate-s2`) | beyond the 2-session time-box (§6) | — | — | #1040's recommendation not posted | **deferred: port cost** |
| #997 fewest-terms + FL order | none (options on Z0, §5) | pending (yes-with-check) | pending | timed, quiet window | pending |
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

## 5. #997 (fewest-terms reducer rule with the FL batch order)

- **Port cost:** none. Both options are on Z0 (`ReducerSelection::FewestTerms`,
  `BatchOrder::FaugereLachartre`).
- **Eligibility.** The reducer rule changes which reducer row covers a column, not the pair set. The
  FL order changes how a batch is eliminated, not its row space (`BatchOrder` docs: both orders give
  the same candidate rows). The reduced basis is unique, so the arm is T-GB-eligible under every
  order in principle. It is "yes-with-check" until the harness confirms it by digest on the
  qualification set.
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

## 7. Remaining work

- **Build and run the harness.**
  - The harness change is written but not yet compiled or committed: `cargo test --example
    m33_qualify`, with and without `research-sigf4`.
  - Then build at Z0 plus this harness and run `campaign.py run`, all 744 cells. This covers the P7
    cap-16 check and #997's digest check.
  - **Why it waits.** Compiling or running it adds compiler processes and load that #1039's
    publication job (`05a26851f550`, 486 attempts) flags as contamination on its attempts. So the
    build waits until that job and #945's queued run finish. Nothing here is timed, so the result
    does not depend on a quiet machine. Only the other sessions' measurements do.
- **Timed, needs a quiet machine.** Bounded regime reads for P1–P8 and #997 that the M32 records do
  not already answer, plus #997's own gate (Cyclic-8 no-regression). Before each run, load and other
  sessions' compilers are re-checked inside the bench lock.
