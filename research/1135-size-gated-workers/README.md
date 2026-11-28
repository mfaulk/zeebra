# #1135: size-gated worker count for `GradedEngine::Adaptive`, laptop stage

The write-up, the predeclared gate and the criterion are in
[`docs/research/1135-size-gated-workers.md`](../../docs/research/1135-size-gated-workers.md).

| File | What |
| --- | --- |
| `study.py` | The gate (`bezout_bound`, `GATE`), the development re-read (`dev`), the fresh catalog (`catalog`), the controller (`run`), and the tables (`summarize`) |
| `test_study.py` | Unit tests of the gate and of the read |
| `dev.md` | The gate on Gate H's development P8 cells (tag `measured/1012-matrix`); the fitting data |
| `catalog.json`, `predictions.md` | The fresh rows (`corpus-instance-v1`, GF(2³¹−1)) and the gate's prediction for each |
| `attempts.jsonl.gz` | Every timed attempt: process wall, route, team, basis digest, 1-minute load at start |
| `tables.md` | `study.py summarize` over the attempts: medians, the pre-declared read (not supported) |
| `provenance.txt` | Commit, host, binary SHA-256, session start and end |

Reproduce:

```bash
export CARGO_TARGET_DIR=<private dir> RUSTC_WRAPPER=""
cargo build --release --locked --features research-sigf4 --example m34_matrix
python3 research/1135-size-gated-workers/study.py dev        # rewrites dev.md
python3 research/1135-size-gated-workers/study.py catalog    # rewrites catalog.json, predictions.md
python3 research/1135-size-gated-workers/study.py run --bin "$CARGO_TARGET_DIR/release/examples/m34_matrix" --out attempts.jsonl
gzip -n -c attempts.jsonl > research/1135-size-gated-workers/attempts.jsonl.gz
python3 research/1135-size-gated-workers/study.py summarize   # rewrites tables.md
python3 -m unittest discover -s research/1135-size-gated-workers -p 'test_*.py'
```
