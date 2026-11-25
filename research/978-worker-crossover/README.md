# #978: held-out check of the narrowed `WorkerCrossover` band

**Measured at:** `e3a25264` (PR #1115 rebased onto `main` `48778879`; tag `measured/978-held-out`),
AMD Threadripper PRO 5995WX, rustc 1.99.1, `sig_f4_study` built `--release --features
research-sigf4`. CCDs 1–2 reserved with `tools/bench-reserve.sh`; each child pinned to CPUs
8..8+w−1 (`provenance.txt`). The set, protocol and rule were posted on #978 before any timed run
(issue comment 7149570887).

| File | What |
| --- | --- |
| `run.py` | The controller: `--probe` (input digest and one `entry` solve at 16 w per row, to fix the grouping and the floor), then the timed suite: `f4`, `sigf4`, `entry` at 4/8/16 w, 9 fresh processes each, arms rotated per repetition |
| `probe.jsonl.gz`, `held.jsonl.gz` | Every child, with `cpu-context` before and after and the 1-minute load at its start |
| `summarize.py` → `tables.md` | Per-cell medians, sigf4 ÷ f4 with a 95% bootstrap CI, entry route and the pre-declared verdict |
| `provenance.txt` | Commit, binary SHA-256, placement, session start and end |

Reproduce:

```bash
export CARGO_TARGET_DIR=<private dir> RUSTC_WRAPPER=""
cargo build --release --features research-sigf4 --example sig_f4_study
tools/bench-reserve.sh reserve
tools/bench-reserve.sh run 978 8-23 python3 research/978-worker-crossover/run.py \
    --sig "$CARGO_TARGET_DIR/release/examples/sig_f4_study" --output held.jsonl --reps 9 --rows <rows>
tools/bench-reserve.sh release
python3 research/978-worker-crossover/summarize.py held.jsonl
```

**Dropped by the pre-declared 20 ms floor:** the four dense planted rows (`mq-dense-10-s1`/`-s2` over
GF(32003) and GF(2³¹−1)). In the probe their `entry` run, the signature engine, took 15.5 ms of
process wall at 16 workers. They were not timed and not replaced.
