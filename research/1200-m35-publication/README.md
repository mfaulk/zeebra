# #1200: M35 WP A's publication-mode read

**Measured at:** `ee691468` (tag `measured/1200-harness`). Its `src/` is identical to Z0 `125658bb` (tag `measured/1162-z0`); it adds only the BabyBear and KoalaBear instantiations in `examples/m34_matrix.rs` and `examples/m33_qualify.rs`. grobx 0.155.1 is at `8005a2a1`, re-provisioned with `research/m33-baseline/grobx-pin.sh` because #1162's build had been pruned. Its `grobx-driver` sha256 is `9dcb4f14c92feb8a…`, against #1162's `e2572de9…`: the same rev, built again.

**Plan:** [`MILESTONE-FINITE-FIELD-COMPETITIVENESS.md`](../../docs/MILESTONE-FINITE-FIELD-COMPETITIVENESS.md) §7.1, Amendment 1.

**Development read:** [`docs/research/m35-baseline.md`](../../docs/research/m35-baseline.md) (#1162).

Every figure is library-call seconds (`call_ns`) at one worker, publication mode: an exclusive CCD 1–2 reservation, with no compiler on the machine at the start of each attempt.

## Files

| File | What |
|---|---|
| `campaign.py` | Writes the per-record inputs and the four bench-job manifests, and extracts the journals |
| `table.py` | The row table and the regime scores below: `table.py <records>` |
| `records.jsonl.gz` | One line per attempt from the four jobs that produced data: digest, contamination flag, call and process wall, peak RSS |
| `probe-dev-ao.jsonl` | The dev-mode probe of the twelve new BabyBear and KoalaBear rows that preceded the read |

## Jobs and sessions

| Job | What | Session | Attempts | Outcome |
|---|---|---|---:|---|
| `f96330fe9802` | arms ≥ 60 s, 3 reps | 1 (13:39–15:42 EST) | 45 / 45 | done |
| `14f157e49150` | frontier rows, 1 rep | 1 | 18 / 18 | done |
| `a3c093b7f544` | arms < 60 s, 9 reps | 2 (15:45–18:50) | 1091 / 1161 | stopped on `mode-refused` |
| `7f36f63984a5` | grobx exact checker (`grobx-certified`), 3 reps | 2 | 24 / 24 | done |
| `17601959f68c`, `ef41f5e1e96f` | the first 9-rep and exact jobs | 1 | 189 / 1161 and 2 / 24 | stopped on `output-bytes`; **not used** |

**What went wrong, and what it costs the read:**

- **The output budget.** grobx prints its whole basis, which is 137 MB gzipped for Chandrasekhar-H 13 at p64. The journal's default 1 GiB retained-output budget stopped the first 9-rep and exact jobs. Both were resubmitted unchanged except for `output_bytes = 32 GiB`. grobx is timed by its own `solve_ns`, so printing does not enter its figure.
- **The last repetition is short.** After 1091 cells, another session's `cargo build` held a compiler on the machine past the 3600 s publication wait, and the job stopped. The 70 missing cells are all repetition 8, on 27 instances. Those rows have **8** clean repetitions rather than 9. They include R1's Chandrasekhar-H 13 at p64 and R2's Katsura-12 at 2⁶⁴ − 59. Every R1 and R2 interval below is far narrower than any gate margin, so the ninth repetition was not taken in a third session.
- **Two sessions.** Where a row's arms fall in different jobs, `R` pairs figures from two sessions. This happens when one arm is over 60 s and another under it: `mq-random-11/12` and `mq-dense-18`'s Zeebra arm against grobx. `R` is an independent ratio of medians, so it does not depend on pairing.
- **Contamination.** 2 attempts are flagged and excluded, on `cyclic-8@m31` and `eco-13@m31`. That is well under the 20% session-void fraction.
- **Budget.** The four jobs that produced data used 4.55 h, and the two discarded jobs 0.59 h: 5.14 h of machine time against the 4.94 h priced on #1161.

## Regime scores (plan §3; Amendment 1 declarations in `panel.json`)

`R` = best Zeebra arm ÷ default grobx, per row. A regime's score is the geometric mean within each lineage (base problem), then across lineages. The 95% interval is a percentile bootstrap over each row's attempts.

| Regime | Rows | Lineages | Geometric-mean R | 95% interval | Largest row median R | Target (§3) |
|---|---:|---|---:|---|---:|---|
| **R1** Chandrasekhar-H 11–13 @ p64 | 3 | chandrasekhar-h | **1.13** | 1.13–1.14 | 1.20 | ≤ 1.05, bound ≤ 1.10, every scale ≤ 1.10 |
| **R2** Katsura-12, Eco-12, Eco-13 @ 2⁶⁴ − 59 | 3 | eco, katsura | **1.14** | 1.13–1.15 | 1.43 | the same |
| **R3** R1 and R2 families at 2³¹ − 1, BabyBear, KoalaBear | 18 | chandrasekhar-h, eco, katsura | **4.27** | 4.26–4.28 | 6.62 | secondary only (conditional on E2) |

Neither primary regime meets the competitive target at Z0. Both are within 15% at the geometric mean.

- **R1:** Chandrasekhar-H 13 (1.08) is already close. Chandrasekhar-H 11 (1.20) is the worst scale.
- **R2:** Katsura-12 is at parity (1.01). Eco-12 is at 1.16 and Eco-13 at 1.43, so Eco is R2's gap.
- **R3:** this is the 31-bit lane: 2.7–6.6× on every row, with BabyBear and KoalaBear 5–10% above 2³¹ − 1.

## Rows

Seconds are medians of clean completed attempts. `n` is grobx's clean count. "Zeebra arm" is the faster median of `f4` and `adaptive`, a per-row choice; `adaptive R` is the shipping Adaptive engine alone. RSS is the median observed peak. 72.86 MiB is the floor of the RSS reporter on these small rows, not a measurement of either solver.

| Row | n | f4 (s) | adaptive (s) | grobx (s) | Zeebra arm | R | 95% interval | adaptive R | Peak RSS Zeebra / grobx (MiB) | Digests | Contaminated |
|---|---:|---:|---:|---:|---|---:|---|---:|---|---|---:|
| `cyclic-7@m31` | 9 | 0.219 | 0.219 | 0.029 | adaptive | 7.67 | 7.66–7.77 | 7.67 | 72.86 / 72.86 | agree | 0 |
| `cyclic-8@m31` | 8 | 4.76 | 4.77 | 0.325 | f4 | 14.64 | 14.54–14.81 | 14.66 | 144.55 / 72.86 | agree | 1 |
| `eco-12@babybear` | 9 | 11.49 | 1.79 | 0.358 | adaptive | 5.00 | 4.90–5.02 | 5.00 | 144.38 / 72.86 | agree | 0 |
| `eco-12@koalabear` | 9 | 11.51 | 1.78 | 0.361 | adaptive | 4.94 | 4.85–5.02 | 4.94 | 145.71 / 72.86 | agree | 0 |
| `eco-12@m31` | 9 | 10.02 | 1.62 | 0.360 | adaptive | 4.50 | 4.45–4.55 | 4.50 | 159.64 / 72.86 | agree | 0 |
| `eco-12@w59` | 9 | 12.89 | 1.80 | 1.55 | adaptive | 1.16 | 1.16–1.17 | 1.16 | 166.61 / 72.86 | agree | 0 |
| `eco-13@babybear` | 9 | 104.00 | 11.50 | 1.74 | adaptive | 6.62 | 6.59–6.69 | 6.62 | 570.30 / 93.97 | agree | 0 |
| `eco-13@koalabear` | 9 | 103.76 | 11.51 | 1.74 | adaptive | 6.60 | 6.55–6.64 | 6.60 | 569.85 / 93.80 | agree | 0 |
| `eco-13@m31` | 9 | 92.16 | 10.79 | 1.74 | adaptive | 6.22 | 6.10–6.26 | 6.22 | 647.53 / 94.29 | agree | 1 |
| `eco-13@w59` | 9 | 117.18 | 12.09 | 8.47 | adaptive | 1.43 | 1.42–1.43 | 1.43 | 675.25 / 114.34 | agree | 0 |
| `eco-8@m31` | 9 | 0.007 | 0.003 | 0.002 | adaptive | 1.59 | 1.58–1.60 | 1.59 | 26.30 / 26.39 | agree | 0 |
| `eco-8@w59` | 9 | 0.007 | 0.003 | 0.002 | adaptive | 1.41 | 1.41–1.42 | 1.41 | 26.39 / 26.31 | agree | 0 |
| `gen-chandrasekhar-h-11@babybear` | 9 | 6.56 | 1.15 | 0.383 | adaptive | 3.00 | 2.98–3.02 | 3.00 | 214.61 / 53.73 | agree | 0 |
| `gen-chandrasekhar-h-11@koalabear` | 9 | 6.57 | 1.15 | 0.380 | adaptive | 3.01 | 2.95–3.03 | 3.01 | 214.64 / 64.12 | agree | 0 |
| `gen-chandrasekhar-h-11@p31` | 9 | 5.95 | 1.06 | 0.381 | adaptive | 2.78 | 2.74–2.79 | 2.78 | 247.64 / 64.22 | agree | 0 |
| `gen-chandrasekhar-h-11@p64` | 9 | 7.29 | 1.18 | 0.980 | adaptive | 1.20 | 1.20–1.21 | 1.20 | 265.58 / 67.14 | agree | 0 |
| `gen-chandrasekhar-h-12@babybear` | 9 | 39.27 | 5.44 | 1.77 | adaptive | 3.06 | 3.04–3.10 | 3.06 | 771.42 / 178.62 | agree | 0 |
| `gen-chandrasekhar-h-12@koalabear` | 9 | 39.22 | 5.41 | 1.77 | adaptive | 3.05 | 3.04–3.07 | 3.05 | 770.63 / 178.86 | agree | 0 |
| `gen-chandrasekhar-h-12@p31` | 9 | 35.64 | 5.07 | 1.77 | adaptive | 2.86 | 2.85–2.87 | 2.86 | 855.05 / 179.04 | agree | 0 |
| `gen-chandrasekhar-h-12@p64` | 9 | 43.80 | 5.53 | 4.91 | adaptive | 1.13 | 1.12–1.13 | 1.13 | 913.14 / 220.64 | agree | 0 |
| `gen-chandrasekhar-h-13@babybear` | 9 | stopped | 27.30 | 9.59 | adaptive | 2.85 | 2.83–2.86 | 2.85 | 2803.88 / 546.68 | agree | 0 |
| `gen-chandrasekhar-h-13@koalabear` | 9 | stopped | 27.21 | 9.57 | adaptive | 2.84 | 2.83–2.85 | 2.84 | 2805.56 / 547.90 | agree | 0 |
| `gen-chandrasekhar-h-13@p31` | 8 | stopped | 25.69 | 9.56 | adaptive | 2.69 | 2.67–2.70 | 2.69 | 3211.51 / 548.06 | agree | 0 |
| `gen-chandrasekhar-h-13@p64` | 8 | stopped | 27.97 | 25.99 | adaptive | 1.08 | 1.07–1.08 | 1.08 | 3414.24 / 773.21 | agree | 0 |
| `gen-phosphorylation-7@p31` | 8 | 0.009 | 0.007 | 0.003 | adaptive | 2.72 | 2.70–2.73 | 2.72 | 69.46 / 69.20 | agree | 0 |
| `katsura-12@babybear` | 8 | 72.38 | 3.51 | 0.708 | adaptive | 4.96 | 4.94–4.99 | 4.96 | 376.21 / 88.04 | agree | 0 |
| `katsura-12@koalabear` | 8 | 72.41 | 3.51 | 0.707 | adaptive | 4.96 | 4.93–5.01 | 4.96 | 377.19 / 87.94 | agree | 0 |
| `katsura-12@m31` | 8 | 63.46 | 3.17 | 0.709 | adaptive | 4.47 | 4.43–4.52 | 4.47 | 415.67 / 88.18 | agree | 0 |
| `katsura-12@w59` | 8 | 82.43 | 3.64 | 3.60 | adaptive | 1.01 | 0.99–1.03 | 1.01 | 443.13 / 115.19 | agree | 0 |
| `katsura-9@m31` | 8 | 0.125 | 0.018 | 0.007 | adaptive | 2.75 | 2.72–2.76 | 2.75 | 26.31 / 26.31 | agree | 0 |
| `katsura-9@w59` | 8 | 0.155 | 0.019 | 0.016 | adaptive | 1.22 | 1.21–1.22 | 1.22 | 26.78 / 26.21 | agree | 0 |
| `mq-dense-15-s15@gf32003` | 8 | 2.52 | 4.21 | 0.122 | f4 | 20.60 | 20.33–20.78 | 34.47 | 59.07 / 27.21 | agree | 0 |
| `mq-dense-15-s15@m31` | 8 | 2.14 | 3.62 | 0.158 | f4 | 13.55 | 13.35–13.70 | 22.90 | 63.25 / 27.21 | agree | 0 |
| `mq-dense-18-s18@m31` | 8 | 152.94 | 62.67 | 2.69 | adaptive | 23.28 | 22.53–23.49 | 23.28 | 475.81 / 77.12 | agree | 0 |
| `mq-dense-20-s20@m31` | 1 | stopped | stopped | 22.71 | - | - | - | - | - / 283.52 | agree | 0 |
| `mq-random-10-s10@gf2` | 8 | 0.160 | 0.084 | 0.012 | adaptive | 6.81 | 6.77–6.84 | 6.81 | 27.21 / 27.21 | agree | 0 |
| `mq-random-10-s10@m31` | 8 | 0.917 | 0.258 | 0.118 | adaptive | 2.18 | 2.16–2.20 | 2.18 | 35.88 / 27.21 | agree | 0 |
| `mq-random-11-s11@m31` | 8 | 70.32 | 83.86 | 6.86 | f4 | 10.25 | 10.17–10.28 | 12.23 | 468.87 / 163.76 | agree | 0 |
| `mq-random-12-s12@gf2` | 8 | 10.15 | 15.66 | 0.448 | f4 | 22.64 | 22.41–22.74 | 34.94 | 197.56 / 26.36 | agree | 0 |
| `mq-random-12-s12@m31` | 8 | 54.28 | 69.67 | 4.24 | f4 | 12.80 | 12.64–12.86 | 16.44 | 409.00 / 120.59 | agree | 0 |
| `mq-random-14-s14@gf2` | 1 | stopped | stopped | 95.19 | - | - | - | - | - / 713.14 | agree | 0 |
| `mq-random-14-s14@m31` | 0 | stopped | stopped | stopped | - | - | - | - | - / - | - | 0 |
| `mq-random-16-s16@gf2` | 0 | stopped | stopped | stopped | - | - | - | - | - / - | - | 0 |
| `mq-random-16-s16@m31` | 0 | stopped | stopped | stopped | - | - | - | - | - / - | - | 0 |
| `noon-10@m31` | 1 | stopped | stopped | 16.12 | - | - | - | - | - / 778.48 | agree | 0 |
| `noon-9@m31` | 8 | stopped | 1.77 | 0.552 | adaptive | 3.20 | 3.18–3.23 | 3.20 | 611.51 / 131.78 | agree | 0 |
| `sd-butcher@p31` | 8 | 0.005 | 0.005 | 0.004 | f4 | 1.22 | 1.22–1.23 | 1.23 | 72.86 / 72.86 | agree | 0 |
| `sd-butcher@p64` | 8 | 0.005 | 0.005 | 0.007 | f4 | 0.81 | 0.80–0.81 | 0.81 | 72.86 / 72.86 | agree | 0 |
| `sd-ellipsoid-m2@p31` | 8 | stopped | stopped | 0.458 | - | - | - | - | - / 90.13 | agree | 0 |
| `sd-hairer-2@p31` | 8 | 0.040 | 0.040 | 0.008 | adaptive | 5.07 | 5.04–5.09 | 5.07 | 72.86 / 72.86 | agree | 0 |
| `sd-hairer-2@p64` | 8 | 0.043 | 0.043 | 0.013 | f4 | 3.33 | 3.32–3.34 | 3.35 | 72.86 / 72.86 | agree | 0 |
| `zb-col-grid-4x5@p31` | 8 | 0.780 | 0.074 | 0.111 | adaptive | 0.67 | 0.66–0.68 | 0.67 | 72.86 / 72.86 | agree | 0 |
| `zb-col-grid-5x5@p31` | 8 | stopped | 0.983 | 2.24 | adaptive | 0.44 | 0.44–0.44 | 0.44 | 214.25 / 365.67 | agree | 0 |
| `zb-toric-segre-4x4-slice-s1@p31` | 8 | 0.003 | 0.003 | 0.001 | adaptive | 2.01 | 2.00–2.02 | 2.01 | 72.86 / 72.86 | agree | 0 |

**Against #1162's development table.** The regime rows reproduce:
- R1's rows read 1.1–1.2 in both reads, and R2's 1.0–1.4.
- At 2³¹ − 1 the structured rows read 2.7–6.2, against 2.5–6.6.

The MQ rows moved more, as expected of a development probe run under load 10–19:
- dense MQ n = 15 at 2³¹ − 1 is 13.6 here against 17.8;
- sparse MQ n = 11 and 12 are 10.3 and 12.8, against 8.4 and 10.3.

**Correctness.** On every row with a completion, every completed attempt's `reduced-basis-v1` digest agrees across arms, grobx and grobx-certified included.

## grobx's exact checker (`grobx-certified`, 3 reps)

| Row | grobx default (s) | grobx certified (s) | certified / default | Digests |
|---|---:|---:|---:|---|
| `cyclic-7@m31` | 0.029 | 2.898 | 101 | agree |
| `eco-12@w59` | 1.552 | 268.193 | 173 | agree |
| `eco-8@m31` | 0.002 | 0.072 | 38 | agree |
| `gen-chandrasekhar-h-11@p31` | 0.381 | 113.958 | 299 | agree |
| `gen-chandrasekhar-h-11@p64` | 0.980 | 118.025 | 120 | agree |
| `katsura-9@m31` | 0.007 | 1.095 | 168 | agree |
| `katsura-9@w59` | 0.016 | 1.132 | 71 | agree |
| `mq-dense-15-s15@m31` | 0.158 | 9.386 | 59 | agree |

On these eight rows the default grobx basis is the exact one. Exact grobx costs 38–300× its default. Zeebra's exact result beats it on every one of these rows. For example, Chandrasekhar-H 11 at p64 takes 1.18 s in Zeebra against grobx's 118 s.

## What this read decides

- **The deciding baselines.** Each package's deciding read compares against the "best qualified Zeebra configuration" per row (§9.2), meaning the `Zeebra arm` column above. On R1, R2 and R3 that is Adaptive on every row.
- **Regime targets.** To meet §3 on R1 and R2, a mechanism must take R1 from 1.13 to ≤ 1.05 and R2 from 1.14 to ≤ 1.05. It must also bring Eco-13 at 2⁶⁴ − 59 from 1.43 to ≤ 1.10, and Chandrasekhar-H 11 at p64 from 1.20 to ≤ 1.10.
