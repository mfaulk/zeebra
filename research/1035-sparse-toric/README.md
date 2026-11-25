# #1035: sparse (toric) Gröbner bases, matrix counts

**Measured at:** branch `research/1035-sparse-toric` from `main` `04d949ff`. Apple M-series laptop,
release build. Every figure is a count; `call_ns` in the raw data is for scale only.

Findings and decision: [`docs/research/sparse-toric-feasibility.md`](../../docs/research/sparse-toric-feasibility.md).
The decision rule was posted on #1035 before any count was read.

## Files

| File | Role |
|---|---|
| `counts.py` | The sparse side: `paper` → `paper.json`, `survey` → `survey.json`, `public` → `public.json` |
| `run.sh` | Conventional F4 on the paper's shapes (`examples/sparse_toric_counts.rs`) → `f4.jsonl` |
| `run-public.sh` | Conventional F4 on the eligible panel records (`examples/sig_f4_study.rs --catalog`) → `public-f4.jsonl` |
| `tables.py` | `tables.md`: both comparisons and the predeclared decision |

## Reproduce

```sh
export CARGO_TARGET_DIR=...   # see CLAUDE.md
cargo build --release --example sparse_toric_counts
cargo build --release --features research-sigf4 --example sig_f4_study
python3 research/1035-sparse-toric/counts.py paper  > research/1035-sparse-toric/paper.json
python3 research/1035-sparse-toric/counts.py survey > research/1035-sparse-toric/survey.json
python3 research/1035-sparse-toric/counts.py public > research/1035-sparse-toric/public.json
research/1035-sparse-toric/run.sh        > research/1035-sparse-toric/f4.jsonl
research/1035-sparse-toric/run-public.sh > research/1035-sparse-toric/public-f4.jsonl
python3 research/1035-sparse-toric/tables.py > research/1035-sparse-toric/tables.md
```

`run.sh` runs four solves at a time and writes them in completion order. `tables.py` does not
depend on that order.
