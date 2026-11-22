# #1031 reduced-multiple reuse census

**Measured at:** `f6cafd44` (tag `measured/1031-reuse-census`). Census binary
`--features research-reuse` (sha256 prefix `9bcbcb6bafebe6cc`), timed binary
`--features research-sigf4` (sha256 prefix `98e6ca5b3e66361e`), both `examples/reuse_census.rs`.
Report: [`docs/research/reduced-multiple-reuse-census.md`](../../docs/research/reduced-multiple-reuse-census.md).

Build (private target, `RUSTC_WRAPPER=""`):

```sh
CARGO_TARGET_DIR=/buildcache/cargo-target/zeebra-1031 cargo build --release -j24 \
  --features research-reuse --example reuse_census        # census binary
CARGO_TARGET_DIR=/buildcache/cargo-target/zeebra-1031-plain cargo build --release -j24 \
  --features research-sigf4 --example reuse_census        # timed binary
```

| File | What it is | Reproduce |
|---|---|---|
| `rows.txt` | the 57 rows: five pinned M29 rows, #1030's dense planted cohort (4 m/n × 4 fields × 3 supports), four unplanted controls | |
| `run.sh` | one timed and one `--census` run per (row, engine), 12 at a time | `run.sh <census-bin> <timed-bin> rows.txt <out> 12` |
| `runs.jsonl.gz` | the 228 records: per-run summary, per-batch census, conventional work ledger | `cat <out>/*.json \| gzip -9` |
| `summarize.py` | the census table and §6.1 verdicts | `python3 summarize.py runs.jsonl.gz > tables.md` |
| `tables.md` | its output | |
| `overhead.txt` | the instrumentation-off overhead check, n=5 interleaved: timed binary against the census binary without `--census` | |

The timed runs in `runs.jsonl.gz` ran 12 at a time beside each other: their walls set the
symbolic share (a ratio within one run) and the peak RSS, not a timing claim.
