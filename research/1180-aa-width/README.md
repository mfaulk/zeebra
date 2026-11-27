# #1180: idle-vs-idle check of A/A width criteria

**Measured at:** nothing was run here. Every figure is recomputed from #1107's retained records,
whose binaries are at `C` = `5451e9f853c8f24bafed6875218a175de441e3f0`.

This is the laptop stage of #1180: the idle-vs-idle false-failure rate of each candidate replacement
for #1107's H1 width clause, computed on the records in
[`../concurrent-calibration/data/`](../concurrent-calibration/data/). The write-up and the draft
amendment are in
[`docs/research/aa-width-criterion-preregistration.md`](../../docs/research/aa-width-criterion-preregistration.md).
These data are a check for sense only and do not decide anything (#1180).

| File | What |
|---|---|
| `analyze.py` | the candidates, the observed closing-vs-opening check, and the resampled idle null |
| `test_analyze.py` | unit tests (CI). They also reproduce #1107 §5's 4 / 14 and 6 / 22 from the records, and check `tables.md` against `results.json` |
| `results.json`, `tables.md` | the output of the run below |

## Reproduce

```bash
python3 -I research/1180-aa-width/analyze.py --sims 200 --draws 2000 --perms 1000 --observed-perms 20000 \
    --jobs 12 --json research/1180-aa-width/results.json --out research/1180-aa-width/tables.md
```

Every random draw is seeded by its unit's key, so `--jobs` does not change the output. The run took
5.5 minutes on 12 processes of an M4 Pro laptop.
