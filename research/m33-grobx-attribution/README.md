# #970 M33-G1: records for the one-worker grobx attribution

Write-up: [`docs/research/m33-grobx-attribution.md`](../../docs/research/m33-grobx-attribution.md).

**Measured at:** study builds `a13983d6` (tag `measured/970-g1-build`), `hwcount.py` at `b518248e`
(tag `measured/970-g1-hwcount`), grobx 0.155.1 `8005a2a1` as pinned in
[`../m33-baseline/pins.json`](../m33-baseline/pins.json). One `tools/bench-job` dev-mode session,
job `4004a790e353`, 2026-11-21, CPU 8 of reserved CCDs 1–2, load 1.3–4.0.

## Files

| File | What |
|---|---|
| [campaign.py](campaign.py) | `manifest` (the session's six arms), `extract` (journal → records, with grobx's stock report summarized per run), `retain`, `work` (untimed conventional-F4 counters) |
| [build.sh](build.sh) | the three study builds from `git archive` of one commit, in parallel |
| [hwcount.py](hwcount.py) | user-mode hardware counters of one child process by `perf_event_open`; `perf` is not installed on this host |
| [summarize.py](summarize.py) → [tables.md](tables.md) | every table, regenerated from the files here alone; CI runs `--check` |
| `test_*.py` | unit tests for the report parser, the counter wrapper's ABI layout and its derived rates; run in CI |
| [manifests/g1-s1.json](manifests/g1-s1.json) | the submitted manifest |
| `records-4004a790e353.jsonl.gz`, `.session.json` | one record per attempt: wall, contamination metrics, Zeebra statistics (split ledger included), grobx's per-run clocks and charges, hardware counts |
| [journals/4004a790e353/](journals/4004a790e353/) | the hash-chained journal, payloads under 64 KiB; grobx's basis texts are listed in `omitted.json` |
| [work.json](work.json) | conventional F4's serial work ledger per row (`--discovery`), untimed on CPU 40 |

## Reproduce

```sh
research/m33-grobx-attribution/build.sh a13983d6        # git archive; sig (research-sigf4), split (research-sigf4-split),
                              # work (research-sigf4,research-work), each in /buildcache/cargo-target/zeebra-970/target-<arm>
export ZEEBRA_BENCH_JOBS=/buildcache/cargo-target/zeebra-970/jobs
research/m33-grobx-attribution/campaign.py manifest --commit a13983d6 --agent "$(scripts/agent/zb-claim.sh id)" \
    --session g1-s1 > research/m33-grobx-attribution/manifests/g1-s1.json
tools/bench-job submit research/m33-grobx-attribution/manifests/g1-s1.json
tools/bench-reserve.sh reserve && tools/bench-job run <job>     # then release
research/m33-grobx-attribution/campaign.py extract --job "$ZEEBRA_BENCH_JOBS/<job>"
research/m33-grobx-attribution/campaign.py retain --job "$ZEEBRA_BENCH_JOBS/<job>"
research/m33-grobx-attribution/campaign.py work --commit a13983d6 --cpu 40
research/m33-grobx-attribution/summarize.py
```

`build.sh` runs `git archive | tar -x; cargo build --release --locked --features …
--example sig_f4_study` per arm, with `RUSTC_WRAPPER="" CARGO_INCREMENTAL=0`; the manifest records
each recipe and SHA-256. Inputs are #966's request files (`/buildcache/cargo-target/zeebra-966-p2/inputs`),
hashed in the manifest. No held-out row is timed.
