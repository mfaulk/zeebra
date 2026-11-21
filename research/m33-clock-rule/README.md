# #996: the retained M33 sessions re-judged per arm

**Measured at:** not measured here. Nothing was re-run. The figures are attempt counts produced by
re-judging the journaled contamination metrics of the sessions below, whose own READMEs give their
commits: [`../m33-baseline/`](../m33-baseline/README.md) (M33-0, #991),
[`../m33-grobx-attribution/`](../m33-grobx-attribution/README.md) (M33-G1, #992) and
[`../m33-msolve-attribution/`](../m33-msolve-attribution/README.md) (M33-M1, #993). The rule is
`tools/bench-job` session verdict v2 as of this directory's commit.

`tools/bench-job` used to judge the 3% clock rule against one median per cell (instance and worker
count, all arms). Different solvers sample different clocks inside one cell, so every mixed-solver
session came out void while foreign load stayed low. Verdict v2 judges each arm against its own
median within the cell. The foreign and sibling thresholds are unchanged. See
[`docs/guide/benchmarking.md`](../../docs/guide/benchmarking.md), where it describes the `complete`
stop's session verdict.

```bash
python3 research/m33-clock-rule/reverdict.py --write   # regenerates verdicts.md
```

The script reads the retained journals (M33-0, G1) or, where the study kept no journal, the
extracted records (M1). It judges them through bench-job's own `session_verdict_of`, once per cell
and once per arm. The per-cell replay must reproduce the verdict on record, and the script exits
non-zero if it does not. All nine do.

## Verdicts

[`verdicts.md`](verdicts.md) holds the table. "v2 reasons" counts reasons, not attempts: one attempt
can carry several.

| Study | Job | Track / session | v1 per cell (on record) | v2 per arm |
|---|---|---|---|---|
| M33-0 | `00881e3bf16c` | G / baseline | 165/567 void | 50/567 valid |
| M33-0 | `8a0630174500` | G / rerun | 156/567 void | 106/567 valid |
| M33-0 | `2fb61582468a` | M / baseline | 163/648 void | 96/648 valid |
| M33-0 | `5d986752d34a` | M / rerun | 131/648 void | 57/648 valid |
| M33-G1 | `4004a790e353` | G / g1-s1 | 78/162 void | 35/162 **void** (21.6%) |
| M33-M1 | `0ec6dad86c92` | M / k | 110/144 void | 23/144 valid |
| M33-M1 | `1df3100aa22a` | M / mq | 24/342 valid | 24/342 valid |
| M33-M1 | `9de09467ead1` | M / fl | 19/54 void | 20/54 **void** |
| M33-M1 | `b35504942e78` | M / rd | 24/216 valid | 24/216 valid |

Seven of the nine sessions are valid under v2, including all four M33-0 baseline sessions. Two
stay void, and on the clock rule alone:

- **G1** (21.6%, threshold 20%): the residual flags are spread over five arms, Zeebra's as well as
  grobx's. That is within-arm scatter in the sampled `scaling_cur_freq`, which #992's cycle counts
  showed does not track the effective clock.
- **M1 `fl`** (16-worker arms only): `forward` carries 14 of the 20 flags.

Both are the case #996's optional item 2 addresses: judging the clock from per-process cycle counts
rather than sampled frequency. A session void under both rules is still void. Nothing here edits a
published M33 table. Those tables and their write-ups stand as written, under the verdict that was
on record when they were written.
