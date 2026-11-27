# #1075 flat adjacent-round buffer

**Measured at:** `206d2bf8`, binary `--features research-adjacent` (sha256 prefix
`7b1f65b4450abdd0`), `examples/reuse_census.rs`, release profile with
`CARGO_PROFILE_RELEASE_LTO=thin CARGO_PROFILE_RELEASE_CODEGEN_UNITS=16`, 2026-11-27, on a 14-core
macOS/arm64 laptop: one worker, unpinned, one process at a time, while other agents' builds kept
the load average at 8–17. Development figures only: peak RSS is not recorded (macOS). Report:
[`docs/research/adjacent-round-reuse-census.md`](../../docs/research/adjacent-round-reuse-census.md) §6.

Build (private target, `RUSTC_WRAPPER=""`):

```sh
CARGO_PROFILE_RELEASE_LTO=thin CARGO_PROFILE_RELEASE_CODEGEN_UNITS=16 \
  cargo build --release --features research-adjacent --example reuse_census
```

| File | What it is | Reproduce |
|---|---|---|
| `rows.txt` | seven development rows (MQ10 first, then the census rows and M35's two symbolic-heavy rows), the Cyclic-7 control, the Noon-8 adverse control and two held-out rows, named before any run | |
| `run.sh` | each row in `--adjacent off`, `flat-count`, `flat` and `reuse`, fresh processes, serial, arm order rotated per repetition | `run.sh <binary> rows.txt <out.jsonl> 9` |
| `runs.jsonl.gz` | the 396 records; every buffered arm carries its per-batch counters under `adjacent` | `gzip -9 <out.jsonl>` |
| `summarize.py` | the census table, the paired ratios and the decision; its docstring fixes the decision rules | `python3 summarize.py runs.jsonl.gz > tables.md` |
| `tables.md` | its output | |
