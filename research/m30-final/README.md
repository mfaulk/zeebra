# M30 final cohort (#862)

**Measured at:** final `main` `e4826153` (#884, which includes #878's adaptive parallel interning
and #884's symbolic worker cap), with the instrument at `5515c412`. That commit is `e4826153` plus
`examples/m29_cost_model.rs` targets for the two held-out rows and this directory's controller. Its
`src/` and `Cargo.lock` are identical to `e4826153` (`identities.json`
`production_diff_vs_merge_base` is empty). **Baseline:** the M30-0 freeze `4f5784c5` (#855). Its
library is `git archive 4f5784c5`, built with the same `examples/m29_cost_model.rs`, minus the one
`parallel_symbolic` assignment the freeze library has no field for (`ParallelSymbolic` does not
exist there; every batch is serial). Executables and SHA-256s are in [`identities.json`](identities.json)
(final) and [`identities-base.json`](identities-base.json) (baseline).

**Session:** 2026-11-18, 00:24–02:06 EST. The timed suites ran inside a CCD 1–2 reservation
(`tools/bench-reserve.sh`, CPUs 8–23 and siblings), one `bench-reserve.sh run zb-862 8-23`
window per suite ([benchlock.log](benchlock.log)). The reservation was released at 02:06. Wide-field
verification then ran under unscoped `tools/benchlock.sh` windows. **No compiler ran at the start of
any of the 672 cost-model children.** The one-minute load was 0.78–4.85 at child starts
([suite-starts.jsonl](suite-starts.jsonl) and each record's `before`).
**Host:** Threadripper PRO 5995WX, `ZEEBRA_MACHINE=5995wx`. Protocol:
[`docs/research/m30-protocol.md`](../../docs/research/m30-protocol.md).

Report: [`docs/MILESTONE-SIGNATURE-SYMBOLIC-F4.md`](../../docs/MILESTONE-SIGNATURE-SYMBOLIC-F4.md) §15.
Every table: [tables.md](tables.md).

## Files

| File | What |
|---|---|
| [campaign.py](campaign.py), [test_campaign.py](test_campaign.py) | the freeze and final builds interleaved through #834's `costmodel.run_one`; `walls` (7 targets × 1/4/8/16 × 2 builds × 9), `stages` (`--stages`, 1 and 16 workers, × 5), `census` (`--work` and `--discovery` at one worker, one run per build) |
| [run.sh](run.sh) | one lock acquisition per suite |
| `walls.jsonl.gz`, `stages.jsonl.gz`, `census.jsonl.gz` | one record per child: CPU context, clock samples, process wall, the instrument's full JSON (504, 140, 28; all complete) |
| `wide-attempts.json` | [extract.py](extract.py) over nine `wide-corpus.py` passes (#834's `run.sh wide` with `WIDE_CELLS` set to Eco-12, MQ11 and the two pinned held-out rows): grobx raw and groebner-rs, one worker, 36 of 36 complete |
| `mq10-attempts.json` | the same extract over `comparand-scaling.py` window `mq10-try1` (288 attempts: 234 verified, 54 grobx `unsupported` above one worker; no compiler interruption) |
| `sigf4-gate.jsonl.gz` | #857's `research/m30-sigf4/campaign.sh gate`, unchanged, run with `sig_f4_study` built at the instrument commit, `FIRST=8` (54 of 54 complete) |
| [verification.json](verification.json), [verification-eco12-32g.json](verification-eco12-32g.json), [verification-held-out.json](verification-held-out.json) | `research/m30-baseline/verify_wide.py`: grobx certified mode on every wide target (Eco-12 at the 32 GiB cap #855 declared for it, the rest at 8 GiB), and Zeebra's own `--certify` on the held-out rows |
| [summarize.py](summarize.py) → [tables.md](tables.md) | every table |

`extract.py` is #834's `research/m29-baseline/extract.py` plus each attempt's peak RSS, which #834's
extract did not keep. The controller archives (`mq10-try1.json.gz`, `wide-*-pass*.json.gz`) hold full
inputs and bases and stay outside the repository. The extracts name each one by SHA-256.

## Reproduce

```sh
T=/buildcache/cargo-target/zeebra-862      # never under $HOME or /tmp
export RUSTC_WRAPPER="" CARGO_TARGET_DIR=$T TMPDIR=$T/tmp CARGO_INCREMENTAL=0
# final: at this branch
cargo build -j24 --release --locked --features external-runners,research-work --example m29_cost_model
cp $T/release/examples/m29_cost_model $T/bin/m29_cost_model_work
cargo build -j24 --release --locked --features external-runners \
  --example m29_cost_model --example zeebra_driver --example wide_corpus
cp $T/release/examples/{m29_cost_model,zeebra_driver,wide_corpus} $T/bin/
cargo build -j24 --locked --features external-runners --example competitive_sweep
cargo build -j24 --release --locked --features research-sigf4 --example sig_f4_study && cp $T/release/examples/sig_f4_study $T/bin/
# baseline: git archive 4f5784c5 into $T/base-src, copy this branch's examples/m29_cost_model.rs over it
# with the `parallel_symbolic: ...` assignment and the `ParallelSymbolic` import removed, then build both
# m29_cost_model variants there with CARGO_TARGET_DIR=$T/base-target into $T/bin/base/
# comparand drivers: #855's builds (same SHA-256s), copied into $T/bin
tools/bench-reserve.sh reserve
T=$T OUT=$T/m30 REPS=9 bash research/m30-final/run.sh walls census
T=$T OUT=$T/m30 REPS=5 bash research/m30-final/run.sh stages
tools/bench-reserve.sh run zb-862 8-23 env CARGO_TARGET_DIR=$T OUT=$T/m30 REPS=9 TMPDIR=$T/tmp \
  WIDE_CELLS="wide64:eco-12 goldilocks:mq-random-11 wide64:katsura-11 wide64:cyclic-7" \
  timeout --signal=INT --kill-after=60s 7200 bash research/m29-baseline/run.sh wide
tools/bench-reserve.sh run zb-862 8-23 env BIN=$T/bin/sig_f4_study OUT=$T/m30/sigf4 FIRST=8 REPS=9 \
  bash research/m30-sigf4/campaign.sh gate
# wait for zero compilers; on exit 75 increment MQ10_TRY and keep every window
tools/bench-reserve.sh run zb-862 8-23 env CARGO_TARGET_DIR=$T OUT=$T/m30 MQ10_REPS=9 MQ10_WALL=3600 \
  MQ10_TRY=1 TMPDIR=$T/tmp timeout --signal=INT --kill-after=60s 5400 bash research/m29-baseline/run.sh mq10
tools/bench-reserve.sh release
V="python3 research/m30-baseline/verify_wide.py --walls $T/m30/walls.jsonl --grobx $T/bin/grobx-driver --scratch $T/m30/verify"
tools/benchlock.sh zb-862 $V --targets katsura11-wide64,cyclic7-wide64 --certifier $T/bin/m29_cost_model \
  > research/m30-final/verification-held-out.json
tools/benchlock.sh zb-862 $V --targets mq11-goldilocks > research/m30-final/verification.json
tools/benchlock.sh zb-862 $V --targets eco12-wide64 --grobx-rss-gib 32 > research/m30-final/verification-eco12-32g.json
python3 research/m30-final/extract.py $T/m30 research/m30-final
gzip -n -c $T/m30/walls.jsonl > research/m30-final/walls.jsonl.gz      # likewise stages, census
gzip -n -c $T/m30/sigf4/gate.jsonl > research/m30-final/sigf4-gate.jsonl.gz
python3 research/m30-final/summarize.py research/m30-final > research/m30-final/tables.md
```
