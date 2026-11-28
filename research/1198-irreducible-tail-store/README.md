# #1198: a dense tail store over irreducible monomials, counted

The data behind [`docs/research/irreducible-tail-store.md`](../../docs/research/irreducible-tail-store.md).
Counts and byte totals computed from counts; no timing. Runs at `74065694`
(tag `measured/1198-tail-store-count`), bench host, one worker, unpinned.

| File | What it is |
|---|---|
| `rows.txt` | The rows; `<row>+lane` runs with the opt-in lanes on |
| `run.sh` | One `examples/reuse_census --engine sigf4 --tail-store` process per row |
| `runs.jsonl.gz` | One record per row, in `rows.txt` order; `tail_store.batches` is the count |
| `summarize.py` | `tables.md` from `runs.jsonl.gz` |
| `tables.md` | Generated |

```sh
cargo build --release --features research-reuse --example reuse_census
research/1198-irreducible-tail-store/run.sh target/release/examples/reuse_census \
  research/1198-irreducible-tail-store/rows.txt /tmp/1198-runs
for r in $(grep -v '^#' research/1198-irreducible-tail-store/rows.txt); do cat "/tmp/1198-runs/$r.json"; done \
  | gzip -n > research/1198-irreducible-tail-store/runs.jsonl.gz
python3 research/1198-irreducible-tail-store/summarize.py > research/1198-irreducible-tail-store/tables.md
```

A rerun reproduces every count. `call_ns`, the stage clocks and `peak_rss_bytes` in each record
are that run's and differ between runs; `tables.md` reads none of them.
