# #834 M29 frozen baseline: campaign and evidence

**Measured at:** `847c4030`, and `772be618` for MQ10 window 3. Both have the production source of
`main` at `da5b658c`. The executables were built at `fde57ab4`, whose example and library sources
are identical to both (`identities.json` records that build head). Run on 2026-11-16
on host `5995wx`, one `tools/benchlock.sh zb-834` window per suite ([benchlock.log](benchlock.log)).
Findings: [`docs/research/m29-baseline-cost-model.md`](../../docs/research/m29-baseline-cost-model.md).

| file | what |
|---|---|
| [run.sh](run.sh) | one suite per lock: `identities`, `walls`, `stages`, `ab831`, `census`, `wide`, `mq10` |
| [costmodel.py](costmodel.py) | fresh-process `m29_cost_model` children, CCD-aligned `taskset`, `tools/cpu-context.sh` before/after, 25 ms clock sampling, rotated arm order |
| [identities.py](identities.py) → [identities.json](identities.json) | every executable's path, size, SHA-256 and version |
| `walls.jsonl.gz`, `stages.jsonl.gz`, `ab831.jsonl.gz`, `census.jsonl.gz` | one record per child: CPU context, clock summary, process wall and the instrument's full JSON |
| [suite-starts.jsonl](suite-starts.jsonl) | the CPU context each suite started at, inside the lock |
| [extract.py](extract.py) → `mq10-attempts.json`, `wide-attempts.json` | the controller archives reduced to identity, status, wall and basis digest, with each archive's SHA-256 |
| [summarize.py](summarize.py) → [tables.md](tables.md) | every table in the report |
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

`comparand-scaling.py` stops a window as soon as any compiler starts on the machine (exit 75).
`run.sh mq10` therefore takes `MQ10_TRY=n` and writes `mq10-try<n>.json.gz`. Windows are reported
separately and never pooled.
