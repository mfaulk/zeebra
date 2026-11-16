# #821 Zeebra wide ladder at current code

**Measured at:** `00aacbbf` (base `7104d8bc`, patch id `8abf09a1c1de…`; production source of
`7104d8bc` plus the `--workers` runner flag), 2026-11-16. Host `fedora`, Threadripper PRO 5995WX,
release, fat LTO, one codegen unit, `x86-64-v3`. The runner's SHA-256 (`711eb8a7…`) is in both
archives.

Zeebra only, on the frozen #738 catalog, under the controller's unchanged 60 s / 2 GiB limits and
65 s tree watchdog. There were two cohorts:

| cohort | affinity | lock | elapsed | Zeebra outcomes |
|---|---|---|---:|---|
| `--workers 1` | CPU 2 | `wide-821`, 10:50:23–11:07:30 EST | 1027 s | 20 complete, 13 internal limits, 6 watchdog |
| `--workers 16` | CPUs 2–17 | `wide-821-16`, 11:07:49–11:16:19 EST | 510 s | 23 complete, 14 internal limits, 2 watchdog |

The first launch ran both cohorts in sequence ([run.sh](run.sh)). When the serial cohort finished,
the controller regenerated the published `../BOARD.md` from it, as it does at the end of every
campaign. The 16-worker cohort then refused the dirty tree, which is the lock's `status=1`. The
board was restored, and the 16-worker cohort was relaunched alone with the same command line
([relaunch-16.sh](relaunch-16.sh)) at the same commit and binary. `run.sh` now restores the board
between cohorts. Neither cohort's solver attempts were affected. Lock lines: [benchlock.log](benchlock.log).

The comparand rows are the retained #738 cohort (`../campaign.json.gz`), with unchanged binaries;
they were not re-run. [summarize.py](summarize.py) compares every new Zeebra completion with every
other complete answer for its input, coefficient for coefficient, through the board's own
`verify_bases`. It applies the board's own 2× startup gate to ratios and writes
[cohort.md](cohort.md). `--check` fails if a 64-bit completion has no other answer to agree with.

```sh
python3 research/wide-corpus/current-821/summarize.py --check > research/wide-corpus/current-821/cohort.md
```

Archives: `workers-{1,16}.json.gz` with content-addressed chunks in `workers-{1,16}-payloads/`,
packed by `wide-corpus.py --pack`, and read back by `load()`, which checks every chunk's hash.
