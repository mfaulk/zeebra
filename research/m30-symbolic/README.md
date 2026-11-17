# M30 symbolic preprocessing cost model (#859)

Findings: [`docs/research/m30-symbolic-cost-model.md`](../../docs/research/m30-symbolic-cost-model.md).
Every child's record is kept, failures included; campaigns are never pooled.

| file | what |
|---|---|
| [campaign.py](campaign.py) | the suites below, run through #834's `costmodel.run_one` (fresh process, CCD-aligned `taskset` from CPU 8, `tools/cpu-context.sh` before/after, clock sampling, rotated arm order) |
| [run.sh](run.sh) | one lock acquisition per suite: `bench-reserve.sh run` when CCDs 1-2 are reserved, `benchlock.sh` otherwise |
| [summarize.py](summarize.py) → [tables.md](tables.md) | every #859 table |
| [test_campaign.py](test_campaign.py) | plan and Amdahl unit tests; run in CI |
| `*.jsonl.gz` | one record per child: CPU context, process wall, the instrument's full JSON |

Suites:

| suite | binary | what |
|---|---|---|
| `walls` | `m29_cost_model` | process wall, 5 targets × 1/4/8/16 workers, stage clocks off |
| `stages` | `m29_cost_model --stages` | the same arms with stage clocks on |
| `components` | `symbolic_cost_model --replay components` | the shipping closure and each of its parts, replayed per live batch |
| `level` | `symbolic_cost_model --replay level` | #827's level-parallel prototype per live batch, teams 1/4/8/16 |

Targets: the four M29 targets of `m29_cost_model` plus `katsura11-m31` (Katsura-11 / 2³¹−1, the
instance #827 priced on).

Reproduce (never put target dirs under `$HOME` or `/tmp`):

```sh
T=/buildcache/cargo-target/zeebra-859
export RUSTC_WRAPPER="" CARGO_TARGET_DIR=$T TMPDIR=$T/tmp CARGO_INCREMENTAL=0
cargo build -j24 --release --locked --features external-runners --example m29_cost_model
cargo build -j24 --release --locked --features external-runners,research-work --example symbolic_cost_model
mkdir -p $T/bin && cp $T/release/examples/{m29_cost_model,symbolic_cost_model} $T/bin/
T=$T OUT=$T/m30 REPS=5 setsid bash research/m30-symbolic/run.sh walls stages components level
gzip -k $T/m30/*.jsonl && cp $T/m30/*.jsonl.gz research/m30-symbolic/
python3 research/m30-symbolic/summarize.py research/m30-symbolic > research/m30-symbolic/tables.md
```
