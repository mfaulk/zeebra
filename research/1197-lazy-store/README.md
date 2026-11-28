# #1197 eager against lazy store updates

**Measured at:** `ff333703`. Census binary `--features research-reuse`, release with thin LTO and
16 codegen units (sha256 prefix `e337e31dd088`), `examples/reuse_census.rs`, one worker, macOS
arm64. Report: [`docs/research/lazy-reductor-updates.md`](../../docs/research/lazy-reductor-updates.md).

```sh
CARGO_PROFILE_RELEASE_LTO=thin CARGO_PROFILE_RELEASE_CODEGEN_UNITS=16 \
  cargo build --release --features research-reuse --example reuse_census
```

| File | What it is | Reproduce |
|---|---|---|
| `run.sh` | one `--census` run per (row, engine), (14, 25) on two seeds and two fields, (16, 29) and (18, 32) | `run.sh <bin> <out>` |
| `runs.jsonl.gz` | the 10 reports; `reuse.summary.store` is the store ledger, `reuse.batches[]` its per-batch columns | `cat <out>/*.json \| gzip -9` |
| `summarize.py` | the tables, with the definitions in its docstring | `python3 summarize.py runs.jsonl.gz > tables.md` |
| `tables.md` | its output | |

The census runs are untimed replays. Their counts are deterministic and do not depend on the build
profile or the machine.
