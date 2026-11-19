# #906 M31-I final cohort: campaign and evidence

Report: [`docs/MILESTONE-COMPETITIVE-SIGNATURE-F4.md`](../../docs/MILESTONE-COMPETITIVE-SIGNATURE-F4.md) §15.
Every table: [tables.md](tables.md).

**Measured at:** final `main` `8715c8ed` (#926), every final executable built from a `git archive`
of that commit. **Baseline:** the M31-0 freeze `acbaf12c`, built from a `git archive` of #901's
instrument commit `5919caaa`, whose library differs from the freeze only in code behind
`research-sigf4-split`, which the timed build does not enable (`research/m31-baseline/README.md`).
Executable SHA-256s: [binaries.sha256](binaries.sha256). Comparand executables are M30-0's, by
digest (`research/m30-baseline/identities.json`): grobx driver `40035ef8`, groebner-rs driver
`81dc5c4c`, msolve `557470de`.

SESSION

## Files

| File | What |
|---|---|
| [campaign.py](campaign.py), [test_campaign.py](test_campaign.py) | the controller (#901's child runner) and its unit tests, run in CI |
| [run.sh](run.sh) | one session: reserve CCDs 1–2 if free, each suite under `bench-reserve run zb-906 8-23`, release on any exit |
| `walls.jsonl.gz` | wall cohort, n = 9: 11 `sig_f4_study` rows × 12 arms and 2 MQ10 rows × 12 arms (campaign.py docstring) |
| `certify.jsonl.gz` | the entry point with `--certify` at 16 workers, one per row; certification outside the solve wall |
| `census.jsonl.gz` | shipping F4 work counts (`--discovery`, one worker, research-work build), one per row |
| `certified.jsonl.gz` | grobx certified mode, one worker, n = 9 on the four wide rows (Eco-12 at the 32 GiB cap #855 declared) |
| `wide-attempts.json` | `research/m30-final/extract.py` over nine `wide-corpus.py` passes (grobx raw, groebner-rs; one worker) |
| `mq10-attempts.json` | the same extract over `comparand-scaling.py` (msolve exact, grobx raw, groebner-rs, Zeebra's driver; 1/4/8/16 workers) |
| `session.log`, `benchlock.log` | the session's console and lock records |
| [summarize.py](summarize.py) → [tables.md](tables.md) | every table |

The controller archives (`wide-*-pass*.json.gz`, `mq10-try*.json.gz`) hold full inputs and bases and
stay outside the repository; the extracts name each by SHA-256.

## Reproduce

```sh
T=/buildcache/cargo-target/zeebra-906/target    # never under $HOME or /tmp
export RUSTC_WRAPPER="" CARGO_INCREMENTAL=0 TMPDIR=/buildcache/cargo-target/zeebra-906/tmp
# final: git archive 8715c8ed, extracted, then inside it
CARGO_TARGET_DIR=$T cargo build -j16 --release --locked --features research-sigf4 \
  --example sig_f4_study --example m29_cost_model --example zeebra_driver --example wide_corpus
CARGO_TARGET_DIR=$T cargo build -j16 --locked --features external-runners --example competitive_sweep
CARGO_TARGET_DIR=/buildcache/cargo-target/zeebra-906-work cargo build -j16 --release --locked \
  --features research-sigf4,research-work --example sig_f4_study
# freeze: git archive 5919caaa, extracted, then inside it
CARGO_TARGET_DIR=/buildcache/cargo-target/zeebra-906-freeze/target cargo build -j8 --release --locked \
  --features research-sigf4 --example sig_f4_study --example m29_cost_model
# $T/bin: the four final examples; freeze/{sig_f4_study,m29_cost_model}; work/sig_f4_study;
# grobx-driver and groebner-rs-driver copied from M30-0's builds (same SHA-256s)
setsid -w research/m31-final/run.sh OUT walls certify census wide mq10 certified
python3 research/m30-final/extract.py OUT research/m31-final
for s in walls certify census certified; do gzip -n -c OUT/$s.jsonl > research/m31-final/$s.jsonl.gz; done
python3 research/m31-final/summarize.py research/m31-final > research/m31-final/tables.md
```
