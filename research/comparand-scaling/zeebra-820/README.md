# #820 Zeebra fresh-process cohort

**Measured at:** controller and driver source `cda4ef80` (production source of `4eaa07f1`),
2026-11-16, under `tools/benchlock.sh zeebra-820` ([benchlock.log](benchlock.log)). Host
`5995wx` (Threadripper PRO 5995WX); child `p` runs on the first `p` physical cores. Rust 1.99.1,
release, fat LTO, one codegen unit, `x86-64-v3`. The driver's SHA-256 is in the archive.

| file | what |
|---|---|
| [run.sh](run.sh) | the campaign, exactly as run, including the reference archives it trusts |
| [cohort.json.gz](cohort.json.gz) | the full controller archive: every attempt, request, raw driver output, basis and identity |
| [summarize.py](summarize.py) | Zeebra medians against the retained `native-resume-v1` comparand cohort, plus the agreement check |
| [cohort.md](cohort.md) | its output: `python3 research/comparand-scaling/zeebra-820/summarize.py research/comparand-scaling/zeebra-820/cohort.json.gz` |

Reproduce the cohort on a clean committed tree:

```sh
export CARGO_TARGET_DIR=/buildcache/cargo-target/zeebra-820 RUSTC_WRAPPER='' CARGO_INCREMENTAL=0
cargo build --release --locked --example zeebra_driver
cargo build --locked --example competitive_sweep        # debug input-only exporter
mkdir -p "$CARGO_TARGET_DIR/bin" && cp "$CARGO_TARGET_DIR/release/examples/zeebra_driver" "$CARGO_TARGET_DIR/bin/"
ZEEBRA_DRIVER="$CARGO_TARGET_DIR/bin/zeebra_driver" OUT="$CARGO_TARGET_DIR/cohort" \
  tools/benchlock.sh zeebra-820 bash research/comparand-scaling/zeebra-820/run.sh
```

The findings are in [`docs/research/comparand-scaling.md`](../../../docs/research/comparand-scaling.md#zeebra-on-the-same-boundary-820).
