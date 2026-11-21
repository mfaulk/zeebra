# #972 M33-M1: attributing the equal-worker gap to msolve

Write-up: [`docs/research/m33-msolve-attribution.md`](../../docs/research/m33-msolve-attribution.md).
Plan: [`docs/MILESTONE-COMPETITIVE-BENCHMARKING.md`](../../docs/MILESTONE-COMPETITIVE-BENCHMARKING.md) §9.7.

**Measured at:** F0 `31e334bd` (the `entry`, `sigf4` and `sigf4claim` arms run the #966 baseline
binary, SHA-256 `d00a6baf…`, tag `measured/966-baseline-harness`) and `a81627e6` (tag
`measured/972-instrumented`: the `f4stages`, `f4fl`, `forward` and `fl` arms of sessions `mq` and
`fl`, F0 plus this issue's instrumentation, SHA-256 `7782fce5…`) and `358fec73` (tag
`measured/972-reducer-rule`: every arm of session `rd`, which adds `--reducer`, SHA-256 `63b3ce27…`). msolve 0.11.0 as pinned in
[`research/m33-baseline/pins.json`](../m33-baseline/pins.json).

## Files

| File | What |
|---|---|
| [campaign.py](campaign.py) | the four bench-job manifests (`mq`, `k`, `fl`, `rd`), `extract` of each journal, and `counts`, msolve's work counts |
| [manifests/](manifests/) | the submitted manifests |
| `records-<job>.jsonl.gz`, `.session.json` | one record per attempt, with Zeebra's statistics and msolve's `-v 2` rounds and timings |
| [msolve-counts.json](msolve-counts.json) | msolve's pivot applications and coefficient products per row and worker count, from a counting copy built by `tools/external/msolve-count.py` |
| [summarize.py](summarize.py) → [tables.md](tables.md) | every table, from the files above alone (`--check` verifies) |
| [test_campaign.py](test_campaign.py) | unit tests for the msolve `-v 2` parser and the FL manifest; run in CI |

## Reproduction

```sh
export ZEEBRA_BENCH_JOBS=/buildcache/cargo-target/zeebra-972/jobs   # /buildcache/bench-jobs is root-owned
S=/buildcache/cargo-target/zeebra-972/sig_f4_study-a81627e6          # cargo build --release --features research-sigf4 --example sig_f4_study
research/m33-msolve-attribution/campaign.py inputs --study "$S"     # cyclic-8 / GF(32003); the rest reuse #966's request files
research/m33-msolve-attribution/campaign.py manifest --job mq --study "$S" --commit <sha> > manifests/mq.json   # likewise k, fl, rd
tools/bench-job submit manifests/mq.json && tools/bench-job run <id>  # inside the CCD 1-2 reservation
research/m33-msolve-attribution/campaign.py extract --job "$ZEEBRA_BENCH_JOBS/<id>"
python3 -I tools/external/msolve-count.py <msolve-0.11.0 source, configured> <scratch>   # the counting copy
research/m33-msolve-attribution/campaign.py counts --msolve-count <scratch>/.libs/msolve  # untimed, CPUs 24-39
research/m33-msolve-attribution/summarize.py
```

The counting msolve is a modified GPL program used only as a private measurement instrument; this
directory holds none of its source.
