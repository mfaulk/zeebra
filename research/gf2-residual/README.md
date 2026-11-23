# Residual-width packed GF(2) replay (#1077)

Evidence for `docs/research/gf2-residual-packing.md`. The commit, machine and load are in that
document's header and in `provenance.txt`.

| File | What it is |
| --- | --- |
| `batches-dev.tsv`, `batches-heldout.tsv` | `gf2_residual_replay batches {dev,heldout} 7` at `2ac6488f`: one row per batch, every arm's candidates asserted equal |
| `solve-dev.tsv`, `solve-heldout.tsv` | `gf2_residual_replay solve {dev,heldout} 7` at `2ac6488f`: whole solves, bases asserted equal |
| `provenance.txt` | Commit, host, repetitions, and load at START and END of each run |
| `run.sh` | Runs all four, recording `provenance.txt` |
| `analyze.py` | Arm totals, the per-batch oracle, banding by residual fraction, pivot share and cost |

Reproduce:

```bash
export CARGO_TARGET_DIR=<private dir> RUSTC_WRAPPER=""
cargo build --release --features research-gf2-residual --example gf2_residual_replay
bash research/gf2-residual/run.sh "$CARGO_TARGET_DIR/release/examples/gf2_residual_replay" <out-dir> 7
python3 -I research/gf2-residual/analyze.py <out-dir>/batches-dev.tsv <out-dir>/batches-heldout.tsv
```

On the bench host, wrap the binary in `taskset -c <core> tools/benchlock.sh 1077`.
