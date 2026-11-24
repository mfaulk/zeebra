# #1009 input-feature extraction cost on the M34 pilot panel

**Measured at:** `6d46e583` (tag `measured/1009-feature-costs`), binary sha256 prefix
`d094179ce86f0f13`, `examples/feature_costs.rs`, 2026-11-24. Dev mode: CCDs 1–2 reserved with
`tools/bench-reserve.sh`, every process pinned to CPUs 8–23 under `benchlock` (`lock=ccd:1,2`),
builds allowed on the other CCDs, nothing compiled during the runs. Absolute walls were taken beside
builds; the verdicts read paired ratios taken inside one process. Report:
[`docs/research/input-features.md`](../../docs/research/input-features.md) §8–§10.

Build (private target, `RUSTC_WRAPPER=""`):

```sh
cargo build --release --example feature_costs
```

| File | What it is | Reproduce |
|---|---|---|
| `run.sh` | every record of `research/m34-public-corpus/catalog.json` in its own fresh process, serial, catalog order | `tools/bench-reserve.sh run zb-1009 8-23 run.sh <binary> research/m34-public-corpus/catalog.json <out.jsonl> 60` |
| `records.jsonl.gz` | session 1, the 78 records: per extractor the cold first call and the median per-call time over 7 batches of ≥ 2 ms; both arms' calls; the feature values | `gzip -9 -n <out.jsonl>` |
| `records-repeat.jsonl.gz` | session 2, the same campaign repeated straight after, as a stability check | as above |
| `summarize.py` | the cost table, the coverage summary and the stop-condition verdicts. Its docstring holds the rules, declared on #1009 before the timed run | `python3 summarize.py records.jsonl.gz records-repeat.jsonl.gz > tables.md` |
| `test_summarize.py` | its unit tests, run in CI with `summarize.py --check` | `python3 -m unittest discover -s research/1009-feature-costs -p 'test_*.py'` |
| `tables.md` | its output | |

One record, by hand:

```sh
feature_costs --catalog research/m34-public-corpus/catalog.json --id sd-caprasse@p31 --wall-s 60
```

The arms are `entry` (`f4_signature_reported`, the dispatch) and `f4` (`f4_reported`), both on
`F4Options::default()` with `max_wall_time`, called alternately up to 5 times or 10 s each. The
cheapest arm is the faster median of the two.
