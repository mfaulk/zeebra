# M33-M2: bounded small-prime experiments (#973)

**Measured at:** `159f1958` (tag `measured/973-k-ir-split`: merge base `b14196fb` plus the
`ZB_IR_SPLIT` sub-stage clocks, binary SHA-256 `341d650c…`), bench-job `3468877ae5a1`, dev mode,
CPUs 8–23 (CCDs 1–2), n = 9 per cell.

Plan: [`docs/MILESTONE-COMPETITIVE-BENCHMARKING.md`](../MILESTONE-COMPETITIVE-BENCHMARKING.md)
§§9.8, 13. Gate A records: #973 (from [`m33-msolve-attribution.md`](m33-msolve-attribution.md) §8).
Data and scripts: [`research/m33-small-prime-experiments/`](../../research/m33-small-prime-experiments/).

## 1. Summary

| Candidate | Row | Verdict |
|---|---|---|
| **K-IR**: the signature route's final interreduction on the engine's workers | Katsura-11 / GF(2³¹−1), 8 w | **Abandoned at the stop rule.** Parallelizable share 30.3% [29.9, 31.2] < 35%. Even a perfect 8-way split caps the stage speedup at 1.36× (Gate A needs 1.53×) and the wall cut at 5.9% (Gate A needs 8%). No library change. |
| W: grevlex fewest-terms + FL order on MQ10 / GF(2³¹−1) | — | Not started: an owner decision on #965. |

## 2. K-IR

### 2.1 Gate A record and stop rule (restated on #973 before measurement)

The stage is 114.9 ms, 23.1% of the Katsura-11 / GF(2³¹−1) wall at 8 w, and serial at every count
(#972). The mechanism was #845-style candidate finishing: the `TailsOnly` per-seed loop in
`reduce_tails_against_fixed_rows` (`src/grobner/f4/interreduce.rs`), where each seed's tail is swept
against the fixed matrix independently. The stop rule: **abandon if the stage's parallelizable share
is under 35%**.

### 2.2 The first measurement

The measured commit times each sub-stage of `sigf4::engine::interreduce`. The per-seed loop, which
is both the tail sweep and the conversion of each reduced row back into a polynomial, is the part
the workers could take. The other parts are the minimal-basis selection, the closure
(`interreduction_rows` → `close_over_rows`, the symbolic preprocessing machinery), the matrix build
and the final sort. They stay serial. Shares are per attempt against the sum of the sub-stages. That
sum is about 5 ms less than the engine's own stage clock, so the true share is slightly lower still.

| row | w | wall | minimal | closure | build | loop (conversion) | sort | stage | **loop share** | max stage speedup |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Katsura-11 / GF(2³¹−1) | 1 | 742.7 | 7.1 | 54.6 | 2.9 | 32.3 (28.9) | 5.5 | 102.4 | 0.315 [0.312, 0.319] | — |
| | 4 | 512.3 | 7.2 | 57.1 | 2.7 | 32.8 (29.3) | 5.5 | 105.3 | 0.314 [0.301, 0.318] | 1.307 |
| | **8** | 487.2 | 7.8 | 57.8 | 2.9 | 32.6 (29.2) | 5.5 | 109.8 | **0.303 [0.299, 0.312]** | **1.361 [1.354, 1.375]** |
| | 16 | 495.4 | 8.0 | 57.9 | 2.9 | 32.3 (28.9) | 5.5 | 106.7 | 0.305 [0.299, 0.311] | 1.401 |
| Katsura-11 / GF(32003) | 8 | 473.8 | 7.8 | 59.5 | 2.8 | 29.7 (26.2) | 5.2 | 104.9 | 0.282 [0.281, 0.287] | 1.328 |

The full table, at every worker count and with the wall-cut bound, is
[`tables.md`](../../research/m33-small-prime-experiments/tables.md). Milliseconds are medians.
Intervals are 95% percentile bootstraps (20,000 draws, `tools/bench_stats.py`). Digests are
identical within every cell. 10 of 72 attempts carry a bench-clock contamination flag (13.9%, under
the 20% void line). They are kept, as plan §11.6 requires. With them excluded the 8 w share is
0.302 [0.299, 0.308], and the verdict is the same. The session ran one solver, so the 3% clock rule
for mixed-solver sessions (#965) does not apply to it.

### 2.3 Verdict

- **Stop rule: fired.** The loop is 30% of the stage at every worker count and on both fields.
- **Falsifier: hit.** Gate A's 8% needs a 1.53× stage speedup. With the loop divided perfectly by 8
  workers the stage gets at most 1.36× faster, and the process wall loses at most 5.9% [5.8, 6.3].
  The 18% "scales like elimination" figure assumed the whole stage was elimination-shaped. It is not:
  the sweep itself is about 3.5 ms. The rest of the loop is the row-to-polynomial conversion.
- No parallel code was written, so there is no Gate B A/B. The Katsura-11 Zeebra ÷ msolve estimate
  stays at #972's 0.699 at 8 w. A perfect K-IR would have moved it to about 0.66.

### 2.4 What the measurement shows instead (not pursued)

These are recorded for the owner. None of them is K-IR, and each would be a new candidate.

- **The closure is the stage's largest part**, at 55–58 ms (54%). It adds **no** reducer rows: the
  matrix is the 537 seeds alone (537 × 1561, 387 371 entries). The time goes on interning the seeds'
  387 k terms and testing 1561 columns for divisibility. This code is shared with batch symbolic
  preprocessing, which #994 (G2) is changing.
- **Row conversion is 29 ms**, about 75 ns per term, and 90% of the loop. It is serial today and
  per-row independent, but it is too small to reach 8% on its own.
- The minimal-basis selection (7 ms) and the final sort (5.5 ms) are serial and small.

## 3. Reproduction

```sh
export CARGO_TARGET_DIR=/buildcache/cargo-target/zeebra-973 RUSTC_WRAPPER=""
git checkout measured/973-k-ir-split
cargo build --release --features research-sigf4 --example sig_f4_study
cp "$CARGO_TARGET_DIR/release/examples/sig_f4_study" "$CARGO_TARGET_DIR/sig_f4_study-159f1958"
export ZEEBRA_BENCH_JOBS=/buildcache/cargo-target/zeebra-973/jobs
research/m33-small-prime-experiments/campaign.py manifest --commit 159f19587abb32f30a78307c90805a601b287015 > manifest.json
tools/bench-job submit manifest.json
ZB_IR_SPLIT=1 tools/bench-job run <id>        # inside the CCD 1-2 reservation; the clocks go to stderr
research/m33-small-prime-experiments/campaign.py extract --job "$ZEEBRA_BENCH_JOBS/<id>"
research/m33-small-prime-experiments/summarize.py
```
