# Parallel forward elimination evidence (#752)

The report is [`docs/research/parallel-forward.md`](../../docs/research/parallel-forward.md).

| Path | What it is |
|---|---|
| `run-calibration.sh` | Per-batch replay campaign: each default-F4 batch matrix, serial kernel vs `linalg::concurrent` at 2–32 workers, three interleaved repeats |
| `analyze-calibration.py` | Scores a gate's constants against the replay, per family, against the per-batch oracle |
| `calibration/` | Replay output (`train-*` fitted the gate, `heldout-*` did not), campaign log and binary hash |
| `run-study.py` | Complete-task campaign: one F4 call per fresh process, five interleaved repetitions with rotated arm order, pinned to one logical CPU per physical core |
| `summarize-study.py` | Median [min,max] F4 call, process wall, CPU, peak RSS per arm; `--check` requires every attempt to complete and every arm to produce one basis digest |
| `design1/`, `design2/` | Complete-task cohorts for the two declared designs, with binary hashes |
| `benchlock.log` | This study's lock records |

Reproduce from a checkout of the commit named in the report:

```sh
export CARGO_TARGET_DIR=/buildcache/cargo-target/zeebra-752 RUSTC_WRAPPER=""
cargo build --release --features research-work \
  --example parallel_forward_calibration --example parallel_forward_study
tools/benchlock.sh zb-752 research/parallel-forward/run-calibration.sh \
  $CARGO_TARGET_DIR/release/examples/parallel_forward_calibration OUT_DIR
python3 research/parallel-forward/analyze-calibration.py OUT_DIR 8000 1500 8 32
tools/benchlock.sh zb-752 python3 research/parallel-forward/run-study.py \
  $CARGO_TARGET_DIR/release/examples/parallel_forward_study scaling.jsonl scaling
python3 research/parallel-forward/summarize-study.py scaling.jsonl --check
```

Offline verification of the retained cohorts runs no solver:

```sh
python3 research/parallel-forward/summarize-study.py research/parallel-forward/design2/adoption.jsonl.gz --check
```
