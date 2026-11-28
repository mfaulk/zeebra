# #1183: M35 WP E2, the 31-bit lane on the bench host

**Measured at:**
- dev read: `9c8e88c6` (tag `measured/1183-lane31`), main with #1210's lane.
- deciding read: `f04b2ad1` (tag `measured/1183-adaptive-lane`), which also carries `prime31_lane` into the signature engine Adaptive runs.

**Plan:** [`MILESTONE-FINITE-FIELD-COMPETITIVENESS.md`](../../docs/MILESTONE-FINITE-FIELD-COMPETITIVENESS.md) §7.8 and §9.8, Amendment 1. The lane and its overflow proof are in [`docs/research/31-bit-lane.md`](../../docs/research/31-bit-lane.md) (#1210).

## Development read (dev; decides nothing)
`dev.py manifest|extract|table` writes, extracts and tabulates it. Bench-job `6f8402532c82`:
- 189 of 189 cells; digests agree on every row;
- one worker, shipping limits, medians of 3, CCDs 1–2 reserved;
- inputs are #1200's records.

| Row | adaptive | f4 | sig | f4 `--lane31` | sig `--lane31` | gain | Zeebra 2³¹/2⁶⁴ |
|---|---:|---:|---:|---:|---:|---:|---|
| Ch-H-12 @ p31 | 4.792 | 37.096 | 4.754 | 25.495 | 3.621 | 1.31× | 0.92 → 0.70 |
| Ch-H-12 @ BabyBear | 5.068 | 39.733 | 5.057 | 26.129 | 3.539 | 1.43× | 0.98 → 0.68 |
| Ch-H-12 @ KoalaBear | 4.863 | 40.538 | 4.842 | 25.636 | 3.556 | 1.36× | 0.94 → 0.69 |
| Katsura-12 @ m31 | 3.165 | 67.162 | 3.193 | 37.791 | 1.770 | 1.79× | 0.88 → 0.49 |
| Katsura-12 @ BabyBear | 3.551 | 73.276 | 3.496 | 39.479 | 1.728 | 2.02× | 0.97 → 0.48 |
| Katsura-12 @ KoalaBear | 3.286 | 75.386 | 3.296 | 38.457 | 1.719 | 1.91× | 0.91 → 0.48 |
| Eco-12 @ m31 | 1.668 | 11.431 | 1.654 | 6.548 | 1.178 | 1.40× | 0.95 → 0.67 |
| Eco-12 @ BabyBear | 1.723 | 11.755 | 1.753 | 6.913 | 1.106 | 1.56× | 0.99 → 0.63 |
| Eco-12 @ KoalaBear | 1.656 | 11.946 | 1.679 | 6.534 | 1.095 | 1.51× | 0.95 → 0.63 |

- **Columns:** library-call seconds. The gain is the best lane arm over the best arm without the lane. The 2³¹/2⁶⁴ ratio divides by the best arm on the same generators at p64 or 2⁶⁴ − 59: 5.167 s for Ch-H-12, 3.613 s for Katsura-12, 1.746 s for Eco-12.
- **The wiring gap:** `adaptive --lane31` measured the same as `adaptive` on every row, 1.637–5.050 s. The dispatcher built the signature engine's options without `prime31_lane`, so the lane reached only conventional F4, which Adaptive does not take on these rows. `f04b2ad1` fixes it, with a red-green test: `test_prime31_lane_reaches_the_dispatched_signature_engine`.
- **Peak RSS:** on the signature route it is unchanged with the lane, within 1 MiB on every row. F4's lane pass costs up to +9% (for example Katsura-12 @ BabyBear, 501 → 548 MiB), the reducer-block copy the design note flags; F4 is not the best route on these rows.

## Deciding read (§9.8 regime gate, declared on #1183 before it ran)
`decide.py inputs|manifest|extract` writes and extracts it. Bench-job `05b64244475f`:
- publication mode, one worker, 9 interleaved repetitions, CCDs 1–2;
- 297 of 297 attempts; 1 contaminated attempt excluded (Ch-H-12 @ p31, `lane`);
- digests agree across `adaptive`, `lane` (= `adaptive --lane31`) and grobx on every row.

Library-call seconds (grobx: its own `solve_ns`), medians. Each interval is `bench_stats.independent_ratio` on lane ÷ adaptive. The 2³¹/2⁶⁴ ratio divides by `adaptive` on the same generators at p64 or 2⁶⁴ − 59.

| Row | role | adaptive | lane | gain | lane ÷ adaptive (95%) | Zeebra 2³¹/2⁶⁴ | grobx | lane ÷ grobx |
|---|---|---:|---:|---:|---|---|---:|---:|
| Ch-H-12 @ p31 | regime | 4.739 | 3.641 | 1.30× | 0.768 (0.767–0.772) | 0.91 → 0.70 | 1.774 | 2.05 |
| Katsura-12 @ m31 | regime | 3.172 | 1.756 | **1.81×** | 0.554 (0.548–0.557) | 0.88 → 0.49 | 0.704 | 2.49 |
| Eco-12 @ m31 | regime | 1.559 | 1.116 | 1.40× | 0.716 (0.712–0.724) | 0.90 → 0.64 | 0.359 | 3.10 |
| Ch-H-12 @ BabyBear | reproduction | 4.865 | 3.543 | 1.37× | 0.728 (0.723–0.732) | | 1.768 | 2.00 |
| Katsura-12 @ BabyBear | reproduction | 3.279 | 1.691 | **1.94×** | 0.516 (0.510–0.517) | | 0.702 | 2.41 |
| Eco-12 @ BabyBear | reproduction | 1.625 | 1.078 | 1.51× | 0.664 (0.662–0.667) | | 0.357 | 3.02 |
| Ch-H-13 @ p31 | held-out scale | 23.251 | 18.192 | 1.28× | 0.782 (0.779–0.784) | 0.88 → 0.68 | 9.554 | 1.90 |
| Katsura-13 @ m31 | held-out scale | 21.986 | 13.462 | **1.63×** | 0.612 (0.609–0.614) | 0.83 → 0.51 | 4.894 | 2.75 |
| Eco-13 @ m31 | held-out scale | 10.027 | 6.808 | 1.47× | 0.679 (0.676–0.681) | 0.85 → 0.58 | 1.734 | 3.93 |

- **Wide-row `adaptive` times:**
  - Ch-H-12 / 13 @ p64: 5.182 / 26.558 s;
  - Katsura-12 / 13 @ 2⁶⁴ − 59: 3.610 / 26.456 s;
  - Eco-12 / 13 @ 2⁶⁴ − 59: 1.737 / 11.794 s.
- **Route:** Adaptive took the signature route on every row.
- **Peak RSS:** the lane's maximum equals Adaptive's to within 1 MiB on every row but one. On Eco-12 @ BabyBear a single lane attempt peaked at 162 MiB; its other eight were 145–147 MiB, the same as Adaptive's nine.

## Decision
**E2 fails its §9.8 regime gate as declared, and the lane stays opt-in.**
1. **Gain:** at least 1.5× is needed on two R3 families at 2³¹ − 1. Only Katsura passes (1.81×), and it reproduces at BabyBear (1.94×) and on the held-out scale (1.63×). Eco reaches 1.40×, and Chandrasekhar-H 1.30×.
2. **Ratio clause:** with the lane, Zeebra's 2³¹/2⁶⁴ ratio is at most 0.70 on every row (0.49–0.70), against 0.83–0.91 without it.
3. **The rest:** bases are identical. On the per-row median, peak RSS is within 1.0× on every row.

**For the owner:**
- The lane is a uniform 1.28–1.94× win on every R3 row measured, with identical bases and no memory cost on the route Adaptive takes. It misses the declared margin, not the direction.
- Whether to enable it by default under §9.1 alone, together with E's dispatch gate (#1123), is a decision this read does not make.
- grobx stays 1.9–3.9× ahead on these rows with the lane.
