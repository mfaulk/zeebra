# #971 M33-G2: records for the wide-field one-worker experiments

Write-up: [`docs/research/m33-wide-experiments.md`](../../docs/research/m33-wide-experiments.md).

**Measured at:** Gate B, merge base `261b17f1` and candidate G2-1 `fa868367` (tag `measured/971-g2-1-table`);
Gate C, merge base `93f2853a` and candidate `32864419` (tag `measured/971-g2-1-gatec`); G2-2 Gate B, #994 head
`32864419` and candidate `cba1ee89` (tag `measured/971-g2-2-columns`); G2-2 Gate C, main `2f8253f3` and
candidate `6f5466b0` (tag `measured/971-g2-2-gatec`);
grobx 0.155.1 `8005a2a1` as pinned in [`../m33-baseline/pins.json`](../m33-baseline/pins.json). One
`tools/bench-job` dev-mode session per job listed in [tables.md](tables.md), CPUs 8–23 of reserved CCDs 1–2.

## Files

| File | What |
|---|---|
| [build.sh](build.sh) | the timed `research-sigf4` study at each named commit, from `git archive`, in parallel; `ZB_ALIGN_LOOPS=64` builds the loop-aligned placement control |
| [campaign.py](campaign.py) | `manifest` (arms `base`, `head`, `grobx155`; `--gate b`, `c`, `c-warm` (cells under 300 ms, 21 calls per process) or `c-dev` (development rows at 1 w); `--align-loops 64` for the control builds), `extract` (#970's extractor plus the worker count and per-call times), `retain` |
| [noon8-probe.sh](noon8-probe.sh) → [noon8-probe.txt](noon8-probe.txt) | untimed Noon-8 stage clocks under both allocators, and page faults by function (`perf`) |
| [summarize.py](summarize.py) → [tables.md](tables.md) | every table and the Gate B and Gate C verdicts (G2-2 Gate B in §6, Gate C in §7), regenerated from the files here alone; `--check` exits 1 when stale |
| `manifests/*.json` | the submitted manifests |
| `records-<job>.jsonl.gz`, `.session.json` | one record per attempt: wall, peak RSS, contamination metrics, Zeebra's statistics, grobx's report summary, the basis digest |
| `journals/<job>/` | the hash-chained journal, payloads under 64 KiB |

## Reproduce

```sh
research/m33-wide-experiments/build.sh 261b17f1 fa868367   # /buildcache/cargo-target/zeebra-971/bin
export ZEEBRA_BENCH_JOBS=/buildcache/cargo-target/zeebra-971/jobs
research/m33-wide-experiments/campaign.py manifest --base 261b17f1 --head fa868367 --gate b \
    --agent "$(scripts/agent/zb-claim.sh id)" --session g2-1-b1 > research/m33-wide-experiments/manifests/g2-1-b1.json
tools/bench-job submit research/m33-wide-experiments/manifests/g2-1-b1.json
tools/bench-job run <job>                                    # inside a CCD 1–2 reservation
research/m33-wide-experiments/campaign.py extract --job "$ZEEBRA_BENCH_JOBS/<job>"
research/m33-wide-experiments/campaign.py retain --job "$ZEEBRA_BENCH_JOBS/<job>"
research/m33-wide-experiments/summarize.py
```

Inputs are #966's request files (`/buildcache/cargo-target/zeebra-966-p2/inputs`), hashed in the
manifest. `campaign.py` refuses a held-out row (`../m33-baseline/held-out.json`).
