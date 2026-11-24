# #1075 adjacent-round reuse census

**Measured at:** `9cf271a7`, binary `--features research-adjacent` (sha256 prefix
`c34be87888ab77af`), `examples/reuse_census.rs`, on a macOS/arm64 laptop: one worker, unpinned, one
process at a time. Report: [`docs/research/adjacent-round-reuse-census.md`](../../docs/research/adjacent-round-reuse-census.md).

Build (private target, `RUSTC_WRAPPER=""`):

```sh
cargo build --release --features research-adjacent --example reuse_census
```

| File | What it is | Reproduce |
|---|---|---|
| `rows.txt` | six development rows (with Cyclic-7 as the upstream control) and three held-out rows, named before any run | |
| `run.sh` | each row in `--adjacent off`, `count` and `reuse`, fresh processes, serial, arm order rotated per repetition | `run.sh <binary> rows.txt <out.jsonl> 9` |
| `runs.jsonl.gz` | the 243 records; `count` and `reuse` carry the per-batch census under `adjacent` | `gzip -9 <out.jsonl>` |
| `summarize.py` | the census table, the paired ratios and the decision; its docstring fixes the decision rules | `python3 summarize.py runs.jsonl.gz > tables.md` |
| `tables.md` | its output | |
