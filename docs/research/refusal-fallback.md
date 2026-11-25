# Typed-refusal fallback from conventional F4 to signature F4 (#1134)

**Measured at:** branch `research/1134-refusal-fallback` from `main` `5451e9f8`. Apple M-series
laptop (macOS, 14 cores), release build, `--features research-sigf4`, unpinned, one solve per cell.
**Status:** complete, 2026-11-25. **Parent:** #1003. **Found by:** #1015.

The outcomes that decide this report are which attempts complete and which refuse, and those are
typed budget refusals. Wall times are for scale only. They are not Threadripper figures, and Gate
H's 16-worker arms are not reproduced: the most this machine runs is 8 workers.

Data, scripts and the full cell table:
[`research/1134-refusal-fallback/`](../../research/1134-refusal-fallback/README.md).

## 1. Result

**Predeclared decision: no out-of-sample evidence.** The rule fired on none of the 14 out-of-sample
rows, because conventional F4 completed every one of them at 1 and 8 workers. The README fixed the
rows and the decision before any row was solved. So the fallback stays a research arm and goes to
no qualification on this evidence.

On the development rows the rule does what it was designed to do, and its cost there is as expected:

| record | w | adaptive (P8) | discarded attempt | fallback | signature engine alone | fallback ÷ signature |
|---|---:|---|---:|---:|---:|---:|
| `sd-ellipsoid-m2@p31` | 1 | `TooManyColumns` | 894 ms | 1,417 ms, complete | 516 ms | 2.75 |
| `sd-ellipsoid-m2@p31` | 8 | `TooManyColumns` | 524 ms | 1,045 ms, complete | 517 ms | 2.02 |
| `sd-ellipsoid-m2@p64` | 1 | `TooManyColumns` | 905 ms | 1,421 ms, complete | 523 ms | 2.71 |
| `sd-ellipsoid-m2@p64` | 8 | `TooManyColumns` | 542 ms | 1,066 ms, complete | 524 ms | 2.03 |

Each completed basis equals the signature engine's.

## 2. The rule as built

`examples/m34_matrix.rs --engine fallback` is Gate H's `adaptive` arm followed by one rule. When
the dispatcher's conventional route (`Shipping(reason)` for any reason except `Fallback`) stops
with `TooManyRows`, `TooManyColumns`, `TooManyNonzeros` or `TooManyLiveBytes`, it runs the forced
signature engine (`sig`'s options) on the same workers with the wall that remains. The discarded
attempt is charged to `call_ns` and reported as `fallback_from`.

- **No cost on a completion.** A completed result is returned as it is, so on every row where P8
  completes, the fallback is P8. This holds by construction and is tested
  (`fallback_reruns_the_signature_engine_after_a_size_refusal`). Wherever the rule did not fire,
  fallback ÷ adaptive is 0.97–1.03 across separate single runs. The one exception is a 1–2 ms row
  at 0.91, which is clock noise.
- **No second signature attempt.** A refusal from the signature route, or from the dispatcher's
  existing signature→F4 size fallback (#905), is returned unchanged. `gen-chandrasekhar-h-13` at
  8 workers is that case. The signature engine stops on `TooManyLiveBytes` (512.1 MB against
  512 MB), the existing fallback runs conventional F4, and conventional F4 stops on
  `TooManyNonzeros`. The new rule does not fire, and it should not: both engines have already
  refused. At 1 worker the dispatcher sends the row to the signature engine, which completes.
- **Time and batch budgets never trigger it.** They are the caller's limits, not engine sizes.

## 3. Development rows (the rows the rule was designed on)

These are the rows where any conventional arm refused in #1012:

- **`sd-ellipsoid-m2`.** The dispatcher routes it to conventional F4 (`DegreeSpread`: degrees 4, 4,
  4, 6), which refuses at `TooManyColumns` after 0.5–0.9 s. The fallback completes it. The
  discarded attempt makes the fallback 2.0–2.75× the cost of the signature engine alone. This
  matches #1012's Threadripper record (conventional refusal after about 2 s, signature engine
  1.1 s). It does not change Gate H's reading that a dispatch feature routing this row up front
  would be cheaper than any fallback.
- **`gen-chandrasekhar-h-13`.** See §2. It is out of reach at 8 workers for both engines under the
  default budgets.
- **`zb-col-grid-5x5`.** Already routed to the signature engine, which completes. The rule never
  fires.

## 4. Out-of-sample rows

There are 14 rows from the #1007 generators at parameters in no M34 cohort
([`candidates.py`](../../research/1134-refusal-fallback/candidates.py)). The list leans towards
wide degree profiles, because those are what the dispatcher keeps on conventional F4:

- Reimer 5 and 7; cyclic 8; Katsura 11; Eco 11; Noon 8.
- 3-colouring of the 4×4 grid and of G(16, 24).
- Planted dense systems with degree profiles (2⁴, 4⁴), (2⁴, 4³), (2³, 5²) and (3⁴, 5²).
- Two quadratic-entry determinantal systems.

Every conventional attempt completed, so the rule had nothing to act on. That is the predeclared
"no out-of-sample evidence" outcome. It does not show that the rule is harmless on a row where it
fires and the signature engine then fails. `oos-reimer-7` is the shape of that risk: conventional F4
completes it in 0.5–1.6 s, and the signature engine alone stops on `TooManyLiveBytes`. Had
conventional F4 refused it, the fallback would have paid for two refusals.

## 5. Observation outside the question (hypothesis, filed as #1151)

The dispatcher kept all four planted mixed-degree rows on conventional F4: three by `DegreeSpread`,
and `oos-pd-5-5-d2d5-s1` by `Small` (5 variables). There it cost 1.7–3.1× the signature engine
alone, at both worker counts:

| row | w | adaptive (conventional) | signature engine |
|---|---:|---:|---:|
| `oos-pd-6-6-d3d5-s1` | 1 | 1,880 ms | 726 ms |
| `oos-pd-7-7-d2d4-s1` | 1 | 514 ms | 165 ms |
| `oos-pd-6-6-d3d5-s1` | 8 | 482 ms | 206 ms |

On `cyclic-8` at 8 workers and on `reimer-7`, the same rule is right: the signature engine is
2.8× slower or refuses. These are single unpinned Mac runs on rows that were not built to test the
rule, so the observation is labelled **hypothesis**. It bears on the alternative #1134 names, a
dispatch feature that routes rows like `sd-ellipsoid-m2` up front. `DegreeSpread` does not separate
"mixed degrees, dense" (the signature engine wins) from "graded ladder of degrees, cyclic-like" (it
loses).

## 6. What this does not change

- No default changes and no dispatch changes. `fallback` is an engine name in a research harness.
- #961's routing is untouched. The rule reads only grevlex rows here, and graded-lex never reaches
  the signature engine.
