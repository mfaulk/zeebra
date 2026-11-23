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
| `sig_f4_study` | Z0_SIG_SHA |
| `m33_qualify` | Z0_QUAL_SHA |

Toolchain: Z0_RUSTC.

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
| #940 parallel symbolic (`measured/940-gate-s2`) | pending (time-box: 2 sessions, then "deferred: port cost") | — | — | #1040's recommendation | pending |
| #997 fewest-terms + FL order | pending | — | — | — | pending |
| #955 randomized zero-skipping | — | — | — | — | excluded: no exact acceptance rule (#1004) |

## 4. Remaining work

- **Untimed, can run on a busy machine.**
  - A harness that runs P1–P8 on the qualification set, comparing each digest with an independent
    reference at one worker and at the maximum. The fields are GF(32003), GF(2³¹−1), 2⁶⁴−59 and
    2⁶⁴−353, and Goldilocks.
  - The P7 cap-16 digest check.
  - The #940 port-cost estimate against current `src/grobner/sigf4/` and `src/grobner/f4/`.
  - The #997 eligibility check.
- **Timed, needs a quiet machine.** Any bounded regime read that the M32 records do not already
  answer. Before each run, load and other sessions' compilers are re-checked inside the bench lock.
