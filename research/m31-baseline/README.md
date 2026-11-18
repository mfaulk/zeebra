# #901 M31-0 baseline: campaign and evidence

Findings: [`docs/research/m31-baseline.md`](../../docs/research/m31-baseline.md).
**Measured at:** `5919caaa` (the source of every executable; later branch commits touch only
`research/` and docs), library identical to the freeze `acbaf12c` in every timed binary. One
`tools/bench-reserve.sh` session per suite, CCDs 1-2, under `benchlock` ([benchlock.log](benchlock.log)).

| file | what |
|---|---|
| [pins.py](pins.py) → [pins.json](pins.json) | the freeze and every corpus row's canonical SHA-256, held-out rows included; committed (`956a5b17`) before any timing |
| [identities.py](identities.py) → [identities.json](identities.json) | head, freeze, `src/` diff against it, toolchain, build, options, executable SHA-256s, host; comparands reused from M30-0 by digest |
| [campaign.py](campaign.py) | the controller: `sig_f4_study` (#857's command line) and `m29_cost_model` (MQ10) children in one rotation, with #834's `cpu-context` and frequency sampling, `timeout --signal=INT`, `rss-guard` at 8 GiB |
| [run.sh](run.sh) | one session: reserve (only if free), `bench-reserve run zb-901 8-23`, release on any exit |
| [summarize.py](summarize.py) → [tables.md](tables.md) | medians with 95% bootstrap intervals, paired per-repetition ratios, digest agreement, stage decomposition, elimination split, the §6.3 table |
| [test_campaign.py](test_campaign.py) | unit tests for the plan, pairing and interval; run in CI |
| `probe.jsonl.gz` | eco-14 drop test (plan §10.3): one repetition of F4-16, design 1, F4-1 |
| `walls.jsonl.gz` | wall cohort, n = 9: F4 at 1/4/8/16 workers, design 1, design 2 at 16 workers |
| `split.jsonl.gz` | stage-clock campaign, n = 5, from the `research-sigf4-split` binary |

Build (two private target directories; the split binary is never timed against the cohort):

```sh
CARGO_TARGET_DIR=/buildcache/cargo-target/zeebra-901 RUSTC_WRAPPER="" TMPDIR=$CARGO_TARGET_DIR/tmp \
  cargo build --release -j24 --features research-sigf4 \
  --example sig_f4_study --example m29_cost_model --example zeebra_driver --example wide_corpus
CARGO_TARGET_DIR=/buildcache/cargo-target/zeebra-901-split RUSTC_WRAPPER="" TMPDIR=$CARGO_TARGET_DIR/tmp \
  cargo build --release -j24 --features research-sigf4-split --example sig_f4_study
```

Run (one suite per session; `setsid` so a session survives its launcher):

```sh
setsid -w research/m31-baseline/run.sh probe OUT --reps 1
setsid -w research/m31-baseline/run.sh walls OUT --reps 9
setsid -w research/m31-baseline/run.sh split OUT --reps 5
```

Regenerate the tables:

```sh
python3 research/m31-baseline/summarize.py research/m31-baseline/walls.jsonl.gz \
  research/m31-baseline/split.jsonl.gz > research/m31-baseline/tables.md
```
