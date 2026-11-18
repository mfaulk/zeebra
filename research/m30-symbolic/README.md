# M30 symbolic preprocessing: cost model (#859), parallel interning (#860), its scratch (#871) and its integration (#861)

Findings: [`docs/research/m30-symbolic-cost-model.md`](../../docs/research/m30-symbolic-cost-model.md)
(#859) and [`docs/research/m30-parallel-interning.md`](../../docs/research/m30-parallel-interning.md)
(#860). Every child's record is kept, failures included; campaigns are never pooled.

| file | what |
|---|---|
| [campaign.py](campaign.py) | the suites below, run through #834's `costmodel.run_one` (fresh process, CCD-aligned `taskset` from CPU 8, `tools/cpu-context.sh` before/after, clock sampling, rotated arm order) |
| [run.sh](run.sh) | one lock acquisition per suite: `bench-reserve.sh run` when CCDs 1-2 are reserved, `benchlock.sh` otherwise |
| [summarize.py](summarize.py) → [tables.md](tables.md) | every #859 and #860 table |
| [test_campaign.py](test_campaign.py) | plan and Amdahl unit tests; run in CI |
| `*.jsonl.gz` | one record per child: CPU context, process wall, the instrument's full JSON |
| `scratch.jsonl.gz` | #871's `scratch` suite (7d0ac698) |
| `small.jsonl.gz` | #861 Step 0: the #871 prototype on the small tasks (55147884) |
| `gate-256.jsonl.gz` | #861 `gate` suite with the team threshold at 256 and the caller-alone path (ddac56a9) |
| `gate-512.jsonl.gz` | #861 `gate` suite with the threshold at 512 (155216f5) |
| `gate.jsonl.gz` | #861 `gate` suite as shipped: threshold `max(512, 48 * workers)` (ad61fb15) |
| `frontier-probe-*.txt` | #861 unscripted threshold probes (`--min-frontier` sweeps, F4 call µs); not acceptance data |
| `intern-seed512.jsonl.gz` | the first `intern` pass, with a 512-seed-row team threshold (bcf5af6a); retained as a negative ablation |
| `suite-starts.jsonl` | `tools/cpu-context.sh` at each suite's lock acquisition |

Suites:

| suite | binary | what |
|---|---|---|
| `walls` | `m29_cost_model` | process wall, 5 targets × 1/4/8/16 workers, stage clocks off |
| `stages` | `m29_cost_model --stages` | the same arms with stage clocks on |
| `components` | `symbolic_cost_model --replay components` | the shipping closure and each of its parts, replayed per live batch |
| `level` | `symbolic_cost_model --replay level` | #827's level-parallel prototype per live batch, teams 1/4/8/16 |
| `intern` | `symbolic_cost_model --replay intern` | #860's two interning prototypes per live batch, teams 4/8/16 |
| `live` | `symbolic_cost_model --replay live` | complete F4 with a prototype serving every batch, against `--merge off` in the same binary |
| `scratch` | `symbolic_cost_model --replay live` | #871: shipping and the serial merge at 1 and 16 workers with caller-owned scratch, and `--retain run` at 16 |
| `small` | `symbolic_cost_model --replay live` | #861 Step 0: shipping and the serial merge on Katsura-6/7 and cyclic-6 at 1/4/8/16 workers |
| `gate` | `symbolic_cost_model --replay live --merge auto` | #861 acceptance: the shipped `ParallelSymbolic::Auto` against the serial closure; small and mid-size targets at 1/4/8/16 workers, the substantial ones at 1 and 16 |

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
# #860: build symbolic_cost_model at the #860 head into its own target dir, then
T=$T860 T860=$T860 TAG=zb-860 OUT=$T860/m30 REPS=5 setsid bash research/m30-symbolic/run.sh intern live
# #871: likewise at the #871 head
T=$T871 T860=$T871 TAG=zb-871 OUT=$T871/out REPS=5 setsid bash research/m30-symbolic/run.sh scratch
# #861: build at each head into its own bin dir; `small` at 55147884 (REPS=15), `gate` at ddac56a9,
# 155216f5 and ad61fb15 (REPS=10, SUITE_WALL=14400)
T=$T861 T860=$T861/gatebin TAG=zb-861 OUT=$T861/gate REPS=10 SUITE_WALL=14400 bash research/m30-symbolic/run.sh gate
gzip -k $T/m30/*.jsonl && cp $T/m30/*.jsonl.gz research/m30-symbolic/
python3 research/m30-symbolic/summarize.py research/m30-symbolic > research/m30-symbolic/tables.md
```
