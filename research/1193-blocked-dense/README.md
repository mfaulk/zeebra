# #1193: blocked dense elimination on F4's dense residual (laptop stage)

The data behind [`docs/research/blocked-dense-elimination.md`](../../docs/research/blocked-dense-elimination.md).
**Development figures only**: Apple M4 Pro laptop, unpinned, other agents' builds running. They
decide nothing.

| File | What it is |
|---|---|
| `run.sh` | The campaign: `lane` and `split --lane-residual` on four captured batches, as separate processes, arm order rotated per rep, 1-minute load recorded beside each line |
| `summarize.py` | The tables of the note from the JSON lines |
| `campaign-<commit>.jsonl` | One line per process of the campaign |
| `counts.jsonl` | Product counts of the shipped kernels (`counts` arm, `--features research-work`) |
| `tune-<commit>.jsonl` | Leaf size × Winograd crossover on one `D'`, three rotated rounds in one process |
| `gemm-<commit>.jsonl` | Square products, classical and with Winograd from 512, 1024, 2048 |
| `verify-<commit>.jsonl` | One `split --verify --accumulator-sweep --lane-residual` run per row: the blocked result against the whole batch's lane forward pass and full back-substitution |
| `provenance.txt` | Binary SHA-256s, build settings, dates and loads |

## Reproduce

Captures (the GF(31) SHA-256s match `research/1033-dense-rebaseline/captures.json`):

```sh
export CARGO_TARGET_DIR=<private dir> RUSTC_WRAPPER="" \
  CARGO_PROFILE_RELEASE_LTO=thin CARGO_PROFILE_RELEASE_CODEGEN_UNITS=16
cargo build --release --features research-sigf4 --example sig_f4_study
P=$CARGO_TARGET_DIR/release/examples/sig_f4_study
for f in gf31 gf32003; do
  $P --field $f --name mq-dense-18-s18 --generate --engine f4 --workers 1 --capture DIR --batches 3,2
  $P --field $f --name mq-dense-20-s20 --generate --engine f4 --workers 4 --live-gib 8 --capture DIR --batches 3
done
```

Campaign, verification, tuning and products:

```sh
cargo build --release --example blocked_dense_study
B=$CARGO_TARGET_DIR/release/examples/blocked_dense_study
research/1193-blocked-dense/run.sh $B DIR campaign.jsonl 3
$B split DIR/gf31__mq-dense-18-s18__b3.zmat 18 gf31 --lane-residual --accumulator-sweep --verify
$B tune DIR/gf31__mq-dense-18-s18__b3.zmat 18 gf31
$B gemm gf31 512,1024,2048,4096 [--winograd-from N]
cargo build --release --features research-work --example blocked_dense_study
$CARGO_TARGET_DIR/release/examples/blocked_dense_study counts DIR/<archive> <vars> <field>
research/1193-blocked-dense/summarize.py campaign.jsonl counts.jsonl
```

The `split` process at n = 20 peaks at about 8.4 GB resident with `--lane-residual`.
