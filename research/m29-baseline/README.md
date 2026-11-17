# #834 M29 frozen baseline: campaign and evidence

Findings: [`docs/research/m29-baseline-cost-model.md`](../../docs/research/m29-baseline-cost-model.md).
Two campaigns are kept here and never pooled.

- **[`quiet/`](quiet/tables.md), the reported one.** **Measured at:** `7251e775`, production source
  `60e99587`; the #828 cross-check (`fl.jsonl.gz`, `flstages.jsonl.gz`) at #843's head `6e2b93ea`
  with this example overlaid. 2026-11-16, 19:59–20:57 EST, no compiler running at any child's start
  or end, five repetitions, one `tools/benchlock.sh zb-834` window per suite
  ([quiet/benchlock.log](quiet/benchlock.log)). The census was not rerun: it counts operations, not
  time.
- **This directory, the superseded first pass.** Measured at `847c4030`, and `772be618` for MQ10
  window 3. Both have the production source of `main` at `da5b658c`. The executables were built at
  `fde57ab4`, whose example and library sources are identical to both (`identities.json` records
  that build head). 17:00–18:59 EST, three repetitions, beside another worktree's fat-LTO builds
  ([benchlock.log](benchlock.log)).

| file | what |
|---|---|
| [run.sh](run.sh) | one suite per lock: `identities`, `walls`, `stages`, `ab831`, `census`, `wide`, `mq10`, and the #828 cross-check `fl`, `flstages` |
| [costmodel.py](costmodel.py) | fresh-process `m29_cost_model` children, CCD-aligned `taskset`, `tools/cpu-context.sh` before/after, 25 ms clock sampling, rotated arm order |
| [identities.py](identities.py) → [identities.json](identities.json) | every executable's path, size, SHA-256 and version |
| `walls.jsonl.gz`, `stages.jsonl.gz`, `ab831.jsonl.gz`, `census.jsonl.gz` | one record per child: CPU context, clock summary, process wall and the instrument's full JSON |
| [suite-starts.jsonl](suite-starts.jsonl) | the CPU context each suite started at, inside the lock |
| [extract.py](extract.py) → `mq10-attempts.json`, `wide-attempts.json` | the controller archives reduced to identity, status, wall and basis digest, with each archive's SHA-256 |
| [summarize.py](summarize.py) → [tables.md](tables.md), [quiet/tables.md](quiet/tables.md) | every table in the report |
| [test_costmodel.py](test_costmodel.py) | unit tests for the campaign plan; run in CI |

The controller archives themselves are 4–67 MB each (full inputs and bases) and are kept outside
the repository. `mq10-attempts.json` and `wide-attempts.json` name each one by SHA-256.

Reproduce on a clean committed tree:

```sh
T=/buildcache/cargo-target/zeebra-834      # never under $HOME
export RUSTC_WRAPPER="" CARGO_TARGET_DIR=$T TMPDIR=$T/tmp CARGO_INCREMENTAL=0
cargo build -j24 --release --locked --features external-runners,research-work --example m29_cost_model
mkdir -p $T/bin && cp $T/release/examples/m29_cost_model $T/bin/m29_cost_model_work
cargo build -j24 --release --locked --features external-runners \
  --example m29_cost_model --example zeebra_driver --example wide_corpus
cp $T/release/examples/{m29_cost_model,zeebra_driver,wide_corpus} $T/bin/
cargo build -j24 --locked --features external-runners --example competitive_sweep
# grobx-driver and groebner-rs-driver: build with tools/external/provision-{grobx,groebner-rs}.sh's
# flags (ZEEBRA_GROBX_TARGET / ZEEBRA_GROEBNER_RS_TARGET) and copy both binaries into $T/bin.
for s in identities walls stages ab831 census wide mq10; do
  OUT=$T/m29 tools/benchlock.sh zb-834 timeout --signal=INT --kill-after=60s 3600 \
    bash research/m29-baseline/run.sh $s
done
python3 research/m29-baseline/extract.py $T/m29 research/m29-baseline
python3 research/m29-baseline/summarize.py research/m29-baseline > research/m29-baseline/tables.md
```

The #828 cross-check needs `m29_cost_model` built on #843's library in its own target dir (build it
before taking the lock): `git archive` #843's head into `$T-fl/src`, copy this branch's
`examples/m29_cost_model.rs` and its `[[example]]` entry over it, build as above with
`CARGO_TARGET_DIR=$T-fl`, then run `FL_BIN=<that binary> REPS=5 run.sh fl` and `run.sh flstages`
under the lock. The quiet campaign wrote to `OUT=$T/m29-quiet` with `REPS=5 MQ10_TRY=quiet`;
gzip its `*.jsonl` into `quiet/` and point `extract.py` and `summarize.py` at that directory.

`comparand-scaling.py` stops a window as soon as any compiler starts on the machine (exit 75).
`run.sh mq10` therefore takes `MQ10_TRY=n` and writes `mq10-try<n>.json.gz`. Windows are reported
separately and never pooled.
