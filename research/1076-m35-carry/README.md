# #1076: M35 WP C, carrying signature work into conventional F4

**Measured at:** `37ffd88f` (tag `measured/1080-1076-harness`). Its `src/` is identical to Z0 `125658bb` (tag `measured/1162-z0`); it adds only `m34_matrix --research-envelope`.

**Plan:** [`MILESTONE-FINITE-FIELD-COMPETITIVENESS.md`](../../docs/MILESTONE-FINITE-FIELD-COMPETITIVENESS.md) §7.3, Amendment 1.

## Step 1: the limit check (predeclared on #1076)

`limit_check.py --binary BIN --commit SHA --inputs DIR` writes the dev-mode bench-job manifest. The inputs are #1200's per-record `record.json` files. It has three arms:

- `sig-research`: the forced signature engine under the research envelope;
- `f4`: shipping F4;
- `adaptive`: shipping Adaptive.

The job ran on the panel's two exposed sparse-MQ development rows, with 3 interleaved repetitions, CCDs 1–2 reserved, and a 900 s cap.

| Row | `sig-research` (s) | `f4` (s) | `adaptive` (s) | sig / min(f4, adaptive) | Peak RSS sig / f4 (MiB) |
|---|---:|---:|---:|---:|---|
| `mq-random-11-s11@m31` | 19.54 | 69.19 | 82.89 | 0.28 | 804 / 469 |
| `mq-random-12-s12@m31` | 19.81 | 53.12 | 68.50 | 0.37 | 1335 / 409 |

Bench-job `1902757da789`; library-call seconds, medians. Digests agree on all 18 attempts. Adaptive falls back on `TooManyRows { limit: 200000 }`, and the signature engine needs more than the 512 MB shipping live-byte budget.

**Decision, by the predeclared rule (≤ 1.15 × min):**
- The default limit is the cause on sparse MQ.
- Those rows move to #1186, as a dispatch and limit question.
- C continues on Cyclic-like inputs only.
- Raising a limit is not credited as an algorithmic improvement (plan §8.3).
