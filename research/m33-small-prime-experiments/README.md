# #973 M33-M2: bounded small-prime experiments

Write-up: [`docs/research/m33-small-prime-experiments.md`](../../docs/research/m33-small-prime-experiments.md).
Plan: [`docs/MILESTONE-COMPETITIVE-BENCHMARKING.md`](../../docs/MILESTONE-COMPETITIVE-BENCHMARKING.md) §9.8.

**Measured at:** `159f1958` (tag `measured/973-k-ir-split`: merge base `b14196fb` plus the
`ZB_IR_SPLIT` interreduction sub-stage clocks, binary SHA-256 `341d650c…`).

## Files

| File | What |
|---|---|
| [campaign.py](campaign.py) | the K-IR stop-rule manifest (`irsplit` arm, Katsura-11 at GF(2³¹−1) and GF(32003), 1/4/8/16 w) and `extract` of its journal |
| [manifests/](manifests/) | the submitted manifest |
| `records-<job>.jsonl.gz`, `.session.json` | one record per attempt: wall, RSS, contamination, digests and the parsed sub-stage clocks |
| [summarize.py](summarize.py) → [tables.md](tables.md) | the split table and the stop-rule verdict, from the records alone (`--check` verifies) |
| [test_campaign.py](test_campaign.py) | unit tests for the clock parser and the row set; run in CI |

Reproduction is in the write-up's §3.
