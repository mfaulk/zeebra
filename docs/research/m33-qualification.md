# M33-Q: qualifying F2 against F0

**Measured at:** F2 `db181c51` (tag `measured/974-f2`) against F0 `31e334bd`, in two bench-job
sessions on CPUs 8–23 under the CCD 1–2 reservation (`tools/bench-reserve.sh`), dev mode, with the
clock rule judged per arm (#998). Binaries are built by `research/m33-qualification/campaign.py
build`.

| Session | When (UTC) | Harness | F0 sha256 | F2 sha256 | Used for |
|---|---|---|---|---|---|
| 1 | 2026-11-21 17:58–23:01 | `dd57bc4e` | `fe8fe83cb14a861b` | `b14b4680e3221daa` | correctness (superseded) and regression |
| 2 | 2026-11-22 00:24–04:03 | `accae594` (correctness), `dd57bc4e` (regression top-up) | `e562ea30cd462eee` / `fe8fe83cb14a861b` | `6902bdc942139bf7` / `b14b4680e3221daa` | correctness and regression top-up |

The regression top-up reused session 1's binaries, so its repetitions pool with session 1's. The
correctness re-run needed harness `accae594`, which samples thread states per team. That harness
differs from `dd57bc4e` only in its thread sampler.

Result: **Q did not pass.**
- Safety passes.
- Correctness fails on 2 of 71 rows under owner decisions 11 and 12 (#965).
- Regression has no failing cell, but 3 cells cannot reach n.

Gate D was therefore **not run**, and the held-out rows were never timed. Nothing was reverted.

## Safety (at F2)

| Suite | Result |
|---|---|
| `tests/m33_safety.rs` (wall, row, byte budgets and observer stop; 1 and 16 w) | 4 / 4 pass |
| `tests/m33_thread_cap.rs` (caps 3 and 16) | 1 / 1 pass |
| `sigf4::cascade_tests` (`--features research-sigf4`) | 9 / 9 pass |

## Correctness (session 2): 69 of 71 rows pass

Full table: `research/m33-qualification/results/session2-correctness.md`. Every digest matches its
reference, and every lex entry call refuses.

The two checks that session 1 failed were amended under owner decisions 11 and 12 (#965):

- **(12) Route.** Under graded-lex, an F2 entry call passes on any `Shipping(_)` reason.
  grlex/gf2/cyclic-6 ships by `DegreeSpread`, because `src/grobner/sigf4/dispatch.rs` tests degree
  spread before order, and now passes.
- **(11) Thread cap, thread-state form.** The harness's sampler reads each worker's state from
  `/proc/self/task/*/stat` and groups workers into teams: a birth after a team member is gone starts
  the next team (`Teams` in `examples/m33_qualify.rs`, the rule from
  `research/m33-qualification/thread-diag/`). Two checks apply:
  1. Within each team, workers in state R must stay ≤ the worker count. No attempt broke this.
  2. A finished team's threads can outlive its join (#1002). So on a path whose thread lifecycle is
     unchanged, F2's count of running workers above the cap may be no larger than F0's for the
     same engine and workers. That path is the shipping F4, or an entry call that ships by the same
     route at both versions.

  Attempts without thread states fall back to listed threads with F0 parity. Every session-2
  attempt carried thread states, so the fallback was not used.

The two failing rows both fail check 2, on the shipping F4 at 16 workers:

| Row | Verdict |
|---|---|
| grevlex/gf32003/noon-7 | f4 at 16 w: running threads over the cap, F2 1 > F0 0 |
| grlex/m31/mq-random-10-s10 | f4 at 16 w: running threads over the cap, F2 1 > F0 0 |

The thread-state diagnosis (`thread-diag/`, 20 runs per arm, not a timing session) points the same
way. There, F2's shipping F4 reached 17–18 running workers on wide64 noon-8, cyclic-7 and eco-12,
while F0's never went above 16.

## Regression: no failing cell, 3 cells short of n

Full tables: `research/m33-qualification/results/session2-regression.md`, over session 1's jobs plus
the top-up jobs listed in `results/session2-jobs.txt`. Of 56 cells, 53 pass and none fail. The
largest wall upper bound is 1.027 (goldilocks katsura-11, f4, 1 w), and the largest peak-RSS ratio
is 1.022.

The top-up (`results/session2-topup.py`) ran one job per short row and applied the void rule (more
than 20% of attempts contaminated) per job. A void job was left out of the pool and re-run whole.
Two void jobs ran while the F0 and F2 binaries for harness `accae594` were building on the
unreserved CPUs; their re-runs were valid.

The grevlex/wide64/katsura-9 warm-call job was void on all three runs, at system load about 2. Its
contamination concentrates in the same arms every time: the shipping F4 at 16 w (about 70% flagged,
F0 and F2 alike) and F0 entry at 1 w (about 45%). Every flag comes from the clock-deviation rule.
Its three cells therefore stay below n:

| Cell | n |
|---|---|
| wide64/katsura-9, entry, 1 w | 20 of 31 |
| wide64/katsura-9, entry, 16 w | 7 of 31 |
| wide64/katsura-9, f4, 16 w | 5 of 31 |

## Session 1 (superseded correctness)

Session 1 failed correctness on 6 of 71 rows: five on listed threads over the cap, one on the
graded-lex route. Its tables are kept in `results/correctness.md` and `results/regression.md`.

## Gate D

Not run. The plan reads it only after safety, correctness and regression all pass.

## Raw data

Jobs live under `/buildcache/cargo-target/zeebra-974/jobs/`. Session 1's ids are in
`results/jobs.txt` and session 2's in `results/session2-jobs.txt`.
