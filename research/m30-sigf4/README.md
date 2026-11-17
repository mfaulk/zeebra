# #857 signature-F4 prototype: campaign and evidence

Findings: [`docs/research/m30-sigf4-prototype.md`](../../docs/research/m30-sigf4-prototype.md).
**Measured at:** `2d589a80` (design 1) and `7d85eee5` (design 2), 2026-11-17, one
`tools/benchlock.sh zb-857` window per suite ([benchlock.log](benchlock.log)).

| file | what |
|---|---|
| [campaign.sh](campaign.sh) | suites: `gate`, `controls`, `census` (design 1, shipping-F4 census) and `gate2`, `controls2` (design 2) |
| [run.py](run.py) | fresh-process `sig_f4_study` children, arms rotated per repetition, CCD-aligned `taskset`, `timeout --signal=INT --kill-after=60s` |
| [summarize.py](summarize.py) → [tables.md](tables.md) | medians, 95% bootstrap intervals of median ratios, basis-digest agreement |
| [test_run.py](test_run.py) | unit tests for the plan and the interval; run in CI |
| `*.jsonl.gz` | one record per child: process wall, load, and the example's full JSON |
| [binaries.sha256](binaries.sha256) | the three executables measured |

Regenerate the tables:

```sh
python3 research/m30-sigf4/summarize.py research/m30-sigf4/{gate,controls,gate2,controls2}.jsonl.gz \
  > research/m30-sigf4/tables.md
```
