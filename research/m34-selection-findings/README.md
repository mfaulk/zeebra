# #1015: M34 selection findings, per-record table

**Measured at:** `36fd4137` (tag `measured/1012-matrix`). No new measurement: `cells.py` re-reads the
retained Gate H records in [`../m34-gate-h/results/`](../m34-gate-h/results/) through
`analyse.py`'s own cell rule. The write-up is
[`docs/research/m34-selection-findings.md`](../../docs/research/m34-selection-findings.md).

| File | What it is |
|---|---|
| `cells.py` | Lists the development records where `GradedEngine::Adaptive` at one worker (P8-w1) or the forced signature engine at one worker (P4) is penalized or at least 1.5× the cheapest arm |
| `cells.md` | Its output |

```sh
python3 research/m34-selection-findings/cells.py > research/m34-selection-findings/cells.md
```
