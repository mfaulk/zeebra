# Residual-width packed GF(2) replay (#1077)

Evidence for `docs/research/gf2-residual-packing.md`. The commit, machine and load are in that
document's header and in `provenance.txt`.

| File | What it is |
| --- | --- |
| `batches-dev.tsv`, `batches-heldout.tsv` | `gf2_residual_replay batches {dev,heldout} 7` at `2ac6488f`: one row per batch, every arm's candidates asserted equal |
| `solve-dev.tsv`, `solve-heldout.tsv` | `gf2_residual_replay solve {dev,heldout} 7` at `2ac6488f`: whole solves, bases asserted equal |
| `provenance.txt` | Commit, host, repetitions, and load at START and END of each run |
| `run.sh` | Runs all four, recording `provenance.txt` |
| `analyze.py` | Arm totals, the per-batch oracle, banding by residual fraction, pivot share and cost, and an entry-floor sweep |
| `fresh.sh` | Whole solves, one per fresh pinned process, arms rotated (`gf2_residual_replay one`) |
| `analyze_fresh.py` | Fresh-solve totals, per-instance ratio ranges and peak RSS |
| `bench-host/` | The bench host's runs at `7f223df4`: the four tables above, `solve-fresh-1w.tsv` and `solve-fresh-16w.tsv`, and both provenance files |
| `bench-host-1092/` | #1092's confirmation at `7ceea6fd` (`measured/1092-residual-sweep`): `fresh-1w.tsv`, `fresh-16w.tsv` (`auto` against `auto-eager`) and `provenance.txt` |

Reproduce. `run.sh` and `analyze.py` need the example's `batches` and `solve` modes and its
`lazy` arm, which #1092 removed with the `research-gf2-residual` feature; check out `7f223df4` for
them:

```bash
export CARGO_TARGET_DIR=<private dir> RUSTC_WRAPPER=""
git switch --detach 7f223df4
cargo build --release --features research-gf2-residual --example gf2_residual_replay
bash research/gf2-residual/run.sh "$CARGO_TARGET_DIR/release/examples/gf2_residual_replay" <out-dir> 7
python3 -I research/gf2-residual/analyze.py <out-dir>/batches-dev.tsv <out-dir>/batches-heldout.tsv
```

The fresh-process solves run at any later commit, with no feature: the arm names are unchanged
(`packed` and `auto` are the full-width `FullWidth` and `AutoFullWidth`; `eager` and `auto-eager`
are `Packed` and the default `Auto`). On the bench host (what `bench-host/` holds):

```bash
cargo build --release --example gf2_residual_replay
B=$CARGO_TARGET_DIR/release/examples/gf2_residual_replay
tools/benchlock.sh 1077 research/gf2-residual/fresh.sh "$B" <out-dir>/solve-fresh-1w.tsv 5 1 5 dev heldout big
tools/benchlock.sh 1077 research/gf2-residual/fresh.sh "$B" <out-dir>/solve-fresh-16w.tsv 8-23 16 5 dev heldout big -- auto auto-eager
python3 -I research/gf2-residual/analyze_fresh.py <out-dir>/solve-fresh-*.tsv
```
