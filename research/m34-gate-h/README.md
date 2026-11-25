# #1012 Gate H: development-panel performance matrix

**Measured at:** harness `6c77117a` (tag `measured/1012-harness`; `src/` identical to Z0
`28df047f`), binary `m34_matrix` SHA-256 `ee381510e63c0037d90fce74f9a2ff026d84f048dd7029980ca3eeb62c9a7683`;
feature costs at `3d21098c`; S0 at `2db433b2` (tag `measured/1012-s0`). Dev mode, CCDs 1–2 reserved
with `tools/bench-reserve.sh`, 2026-11-25. The write-up and verdict are in
[`docs/research/m34-gate-h.md`](../../docs/research/m34-gate-h.md).

The rules are the ones recorded on #1012 before any cell ran: the 2026-11-22 Gate H declaration,
judgement calls J1–J8 and the two J6 refinements.

| File | What it is |
|---|---|
| `s0/` | The S0 three-cohort seal (#1005's procedure, executed under #1012 J1): `cohorts.json` (every record's cohort, group table, carve-outs), `exposed.json`, and the S2, S3 and S5-field splits that `tools/corpus_lineage.py check` accepts |
| `campaign.py` | `seal`, `plan`, `drive` (bench-job jobs in scale tiers, so the ladder rule sees the rung below), `features`, `collect` |
| `session.sh` | One timed session: waits for a free reservation, reserves CCDs 1–2, drives one pass, releases on every exit |
| `analyse.py` | The Gate H read: PAR-2 cells, leave-one-family-out best fixed, VBS⁺ with #1009's feature cost, grouped bootstrap (20,000 draws), split-half, largest-contributor removal, narrow-go arm sets, PAR-10 and completed-intersection views |
| `test_analyse.py` | Unit tests of the read on synthetic matrices |
| `results/attempts.jsonl` | One selection-grade record per attempt (`selection-outcome-v1` status, wall, digest), collected from the bench-job reports |
| `results/jobs.json` | Every bench-job this campaign submitted, in run order |
| `results/features.jsonl` | `feature_costs --skip-solve` per development record |
| `results/gate-h.json`, `results/gate-h.md` | The read |

## Reproduce

```sh
export CARGO_TARGET_DIR=/buildcache/cargo-target/zeebra-1012/archive RUSTC_WRAPPER="" CARGO_INCREMENTAL=0
git archive 6c77117a | tar -x -C <dir> && (cd <dir> && cargo build --release --locked --features research-sigf4 --example m34_matrix)
python3 research/m34-gate-h/campaign.py seal            # rewrites s0/ byte for byte from the merged catalogs
research/m34-gate-h/session.sh 1 <m34_matrix>           # pass 1, one repetition per cell, in scale tiers
research/m34-gate-h/session.sh 2 <m34_matrix> <feature_costs>   # top-up to n = 5 / 3, then feature costs
python3 research/m34-gate-h/campaign.py collect
python3 research/m34-gate-h/analyse.py
python3 research/m34-gate-h/test_analyse.py
```
