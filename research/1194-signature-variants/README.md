# #1194: signature variants counted against the current engine

Counts for [`docs/research/signature-variants.md`](../../docs/research/signature-variants.md).

| File | What |
|---|---|
| `run.sh` | Five rows under conventional F4 and seven signature cells (three module orders × two rewrite orders, plus `<pot>` with the generators reversed), one worker, one solve per process, 6 GiB live budget, into `runs.jsonl.gz` |
| `runs.jsonl.gz` | `sig_f4_study` records, one per cell |
| `extra.jsonl.gz` | The one cell rerun under a 14 GiB live budget because 6 GiB stopped it: `sd-hairer-2@p31`, Schreyer / newest |
| `tables.py` | `tables.md` from both record files |

## Reproduce

```sh
export CARGO_TARGET_DIR=...   # see CLAUDE.md
CARGO_PROFILE_RELEASE_LTO=thin CARGO_PROFILE_RELEASE_CODEGEN_UNITS=16 \
  cargo build --release --features research-sigf4-variants --example sig_f4_study
research/1194-signature-variants/run.sh "$CARGO_TARGET_DIR/release/examples/sig_f4_study" 600 6
"$CARGO_TARGET_DIR/release/examples/sig_f4_study" --field m31 \
  --catalog research/m34-public-corpus/catalog.json --name sd-hairer-2@p31 --engine sigf4 \
  --module schreyer --rewrite newest --workers 1 --wall-s 900 --live-gib 14 --digest-only \
  | gzip -n -9 > research/1194-signature-variants/extra.jsonl.gz
python3 research/1194-signature-variants/tables.py > research/1194-signature-variants/tables.md
```

Every count is deterministic: the build profile and the machine change only the clocks. The live
budget decides only whether a run finishes.
