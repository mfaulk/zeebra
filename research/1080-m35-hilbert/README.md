# #1080: M35 WP B, exact certified zero skipping

**Measured at:** `35aa01ab` (tag `measured/1080-harness`). Its `src/` is identical to Z0 `125658bb` (tag `measured/1162-z0`). It adds only harness changes to `m34_matrix`: `--hilbert` and the Goldilocks and 2⁶⁴ − 353 instantiations.

**Plan:** [`MILESTONE-FINITE-FIELD-COMPETITIVENESS.md`](../../docs/MILESTONE-FINITE-FIELD-COMPETITIVENESS.md) §7.2 and §9.2, Amendment 1. The predeclaration is on #1080.

B uses the existing `HilbertSelection::CertifiedZeros { slack }` and changes no engine code.

## Development slack sweep (dev mode; decides nothing)

`sweep.py` has three subcommands:
- `sweep.py catalog --qualify BIN --study BIN --out DIR` writes the development records. `mq-full-N-s0` is the frozen wide-corpus `mq-random-N`.
- `sweep.py manifest --binary BIN --commit SHA --inputs DIR` writes the job. It runs shipping F4 with `--hilbert off` and with `certified-zeros+{0,2,8,32}`, 3 repetitions, on the development regime rows and #1080's four adverse controls.
- `sweep.py extract --job-dir DIR` emits one line per attempt with the Hilbert counters.

Controls measured with the mechanism forced on are diagnostic only (plan §9.1). Held-out rows are generated only after the rule is frozen.

### Results (bench-job `f9874321f431`)
180 of 180 cells complete; digests agree across every arm on every row. Shipping F4 on one worker; library-call seconds, medians of 3. Ratios are against `off` on the same row.

| Row | role | off | cz0 | cz2 | cz8 | cz32 |
|---|---|---:|---:|---:|---:|---:|
| mq-full-10-s0 @ Goldilocks | regime | 5.59 | 0.12 | 0.13 | 0.14 | 0.18 |
| mq-full-11-s0 @ Goldilocks | regime | 40.98 | 0.10 | 0.10 | 0.10 | 0.13 |
| mq-full-12-s0 @ Goldilocks | regime | stopped (300 s) | 25.89 s | 26.27 s | 27.06 s | 30.86 s |
| mq-full-10-s0 @ 2⁶⁴ − 353 | regime | 5.39 | 0.13 | 0.13 | 0.14 | 0.18 |
| mq-full-11-s0 @ 2⁶⁴ − 353 | regime | 39.53 | 0.10 | 0.10 | 0.11 | 0.13 |
| mq-full-12-s0 @ 2⁶⁴ − 353 | regime | stopped (300 s) | 26.41 s | 26.79 s | 27.65 s | 31.31 s |
| mq-dense-15-s15 @ m31 | regime | 2.17 | 0.89 | 0.96 | 1.05 | 0.75 |
| mq-dense-18-s18 @ m31 | regime | 157.78 | 1.01 | 0.94 | 0.91 | 0.99 |
| Katsura-11 @ m31 | control | 6.88 | 1.72 | 0.98 | 0.60 | 0.40 |
| Cyclic-8 @ m31 | control | 4.83 | 1.06 | 1.04 | 1.01 | 1.00 |
| mq-random-10-s10 @ m31 | control | 0.92 | 1.12 | 1.13 | 1.10 | 1.12 |
| Eco-12 @ 2⁶⁴ − 59 | control | 12.54 | 1.00 | 1.00 | 1.00 | 1.01 |

## The frozen rule (posted on #1080 before any held-out row existed)
`predicate.py` implements it.
- **Selection:** `CertifiedZeros { slack: 2 }` when all three hold, otherwise `Off`:
  1. m = n;
  2. every generator has the same total degree;
  3. mean support density ≥ 0.5, where a generator's density is its term count over C(n + d, d).
- **Development rows:** it admits exactly the six `mq-full` rows. It declines every control, and `mq-dense` (m = 2n).
- **Why slack 2:** it is within 3% of slack 0 where admitted. On a misfire it is far safer: Katsura-11 runs 1.72× at slack 0 and 0.98× at slack 2.

## Best Zeebra arm on mq-full (bench-job `1f9557dc94f2`, dev)
Ratios are against `f4` with `certified-zeros+2`.

| Row | f4 + cz2 (s) | adaptive | adaptive + cz2 | sig |
|---|---:|---:|---:|---:|
| mq-full-10-s0 @ Goldilocks | 0.70 | 0.99 | 0.99 | 0.99 |
| mq-full-11-s0 @ Goldilocks | 4.01 | 1.04 | 1.04 | 1.04 |
| mq-full-12-s0 @ Goldilocks | 26.14 | 1.03 | 1.03 | 1.03 |
| mq-full-11-s0 @ 2⁶⁴ − 353 | 4.09 | 0.97 | 0.97 | 0.97 |

- **Why Adaptive already matches:** Adaptive routes these rows to the signature engine. A dense square system is regular, and its signature criteria leave no reduction to zero. So certified zeros only bring conventional F4 up to the route Adaptive already takes.
- **No effect under Adaptive:** with `--hilbert` set, Adaptive certifies no pairs (z = 0), because the selection applies only on the conventional route.
- **Consequence:** against the best qualified configuration (§9.2), the development data shows about 1.0×, far from the 1.15× gate.

## Held-out rows (generated after the freeze)
`sweep.py catalog --held-out` writes:
- `mq-full-11-s1` and `mq-full-13-s1` at Goldilocks, both admitted;
- `mq-dense-16-s16` at m31, declined (m = 2n).

Following #1195, B *defers* on `mq-dense` rather than rejecting it.

## Deciding read
`decide.py` writes it. Publication mode, one worker, 9 interleaved repetitions, on the admitted held-out rows; the arms are `adaptive`, `rule` (F4 + cz2) and grobx's default.

Bench-job `9c040f298bdf`: 54 of 54 attempts, none contaminated. Library-call seconds (grobx: its own `solve_ns`), medians of 9. Each interval is `bench_stats.independent_ratio`'s.

| Row | adaptive | rule (F4 + cz2) | grobx | rule gain over adaptive | rule ÷ grobx |
|---|---:|---:|---:|---:|---:|
| mq-full-11-s1 @ Goldilocks | 4.17 (Signature route) | 4.00 | 2.78 | 1.042 (1.031–1.045) | 1.44 (1.42–1.45) |
| mq-full-13-s1 @ Goldilocks | stopped at 149 s on `TooManyNonzeros` (50.4 M > 32 M), after the signature engine fell back on `TooManyLiveBytes` | stopped at 39 s on `TooManyNonzeros` (34.1 M > 32 M) | 134.3 | — | — |

- **Digests:** they agree across all three arms on `mq-full-11-s1`, and every grobx attempt on `mq-full-13-s1` agrees with the others.
- **Peak RSS:**
  - `mq-full-11-s1`: adaptive 0.37 GiB, rule 0.63 GiB, grobx 0.09 GiB;
  - `mq-full-13-s1`: adaptive 1.00 GiB, rule 1.38 GiB, grobx 1.28 GiB.

## Decision (§9.2)
**B fails its gate. Its certified zero skipping is not selected automatically.**
- **`mq-full-11-s1`:** the rule gains 1.04× over the best qualified configuration, against the 1.15× required.
- **`mq-full-13-s1`:** neither Zeebra arm completes under shipping limits, so there is no complete-task gain to credit.
- **Mechanism:** on dense square systems, Adaptive already takes the signature route, which has no reductions to zero for certified zeros to skip. The noise question (§16 item 3) does not arise, because the gain clause fails at any noise allowance below 10%.
- **What stays:** `HilbertSelection::CertifiedZeros` remains an opt-in option. Nothing changes in the dispatcher.

**Limit observation, not credited (plan §8.3):** at n = 13 the rule's F4 route stops only 7% over the 32 M nonzero limit, at 39 s, where grobx takes 134 s. Whether a raised limit completes it is #1186's question.
