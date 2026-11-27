# #1192: weight-vector detector and weighted grading, counts

**Measured at:** `1b0bab73` (branch `research/1192-weight-detector`). macOS M4 Pro laptop, release,
`lto=thin`, `codegen-units=16`, unpinned. Every figure is a count; the `_ns` fields in the raw data
are for scale only.

Findings and recommendation: [`docs/research/weight-vector-detector.md`](../../docs/research/weight-vector-detector.md).

| File | Role |
|---|---|
| `panel.jsonl` | `weight_detector_study --panel research/m34-public-corpus/catalog.json --solve`: one line per `p31` record of the #1006 panel |
| `families.jsonl` | `weight_detector_study --families`: the `chain` and `power-map` rows, F4 and FGLM to lex from each source |
| `tables.py` | `tables.md` from the two files |

## Reproduce

```sh
export CARGO_TARGET_DIR=...  RUSTC_WRAPPER=""   # see CLAUDE.md
cargo build --release --example weight_detector_study
B=$CARGO_TARGET_DIR/release/examples/weight_detector_study
$B --panel research/m34-public-corpus/catalog.json --solve > research/1192-weight-detector/panel.jsonl
$B --families > research/1192-weight-detector/families.jsonl
python3 research/1192-weight-detector/tables.py > research/1192-weight-detector/tables.md
```

The counts reproduce exactly; the `_ns` fields do not.
