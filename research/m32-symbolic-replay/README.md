# #933 symbolic replay (exploratory)

Data for [`docs/research/m32-parallel-symbolic.md`](../../docs/research/m32-parallel-symbolic.md) §4–§6.

- `replay.jsonl.gz` — one line per fresh `sig_f4_study --symbolic-replay` process: Eco-12 / 2⁶⁴−353
  and MQ10 / 32003, engine at 16 workers (`--claim`) and at 1, five processes each, interleaved.
- `replay.sh` — the session (`replay.sh <binary> <out.jsonl> <n>`), run as
  `tools/bench-reserve.sh run zb-933 8-23 replay.sh …`.
- `summarize.py` — the §4 and §6 tables.
- `conventional.jsonl.gz`, `conventional.sh` — §5's conventional-F4 serial closure at `7b25a1ee`
  (`m29_cost_model --workers 1 --stages`, MQ10 / 32003 and Eco-12, n = 5, CPU 8), run as
  `tools/bench-reserve.sh run zb-933 8-23 conventional.sh <m29_cost_model> <out.jsonl> 5`.
- `binaries.sha256`, `benchlock.log` — the binaries and the lock records.

Build (commit `8694d172`, tagged `measured/933-symbolic-replay`), from a `git archive` of it:

```sh
CARGO_TARGET_DIR=/buildcache/cargo-target/zeebra-933/rel RUSTC_WRAPPER="" CARGO_INCREMENTAL=0 \
  cargo build -j16 --release --locked --features research-sigf4-replay --example sig_f4_study
```
