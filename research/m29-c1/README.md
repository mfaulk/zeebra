# M29-C1 evidence (#835)

**Measured at:** Zeebra counter binary built from `2fe11b8d` (production source identical to
`7e18d089`), with `examples/m29_cost_model.rs` as committed alongside this directory; grobx reports
from the #738 campaign at controller `fa7cc30d`, grobx pin `1854835d`. Report:
[`docs/research/m29-grobx-attribution.md`](../../docs/research/m29-grobx-attribution.md).

Build (private target, as every M29 measurement):

```sh
RUSTC_WRAPPER="" CARGO_INCREMENTAL=0 CARGO_TARGET_DIR=/buildcache/cargo-target/zeebra-835 \
  cargo build --release --features external-runners,research-work --example m29_cost_model
```

| File | What it is | Reproduce |
|---|---|---|
| `discovery-<target>.json.gz` | one serial `--workers 1 --discovery` record per target, with the per-batch zero-row census | `m29_cost_model --target <t> --workers 1 --discovery --wall-s 900` |
| `ledger.py` | prints §2's ledger from one discovery record | `python3 research/m29-c1/ledger.py <(zcat discovery-mq11-goldilocks.json.gz)` |
| `grobx-report-<field>-<name>.json.gz` | the grobx attempt's metadata and stock engine report, basis dropped | `strip_grobx.py` over an attempt extracted from `research/wide-corpus/campaign.json.gz` with `wide-corpus.py`'s `load` |
| `grobx_rounds.py` | sums the report's per-round `rows`/`reductions`/`subtracted` and prints the handover lines | `python3 research/m29-c1/grobx_rounds.py grobx-report-goldilocks-mq-random-11.json.gz` |
| `hilbert-serial.jsonl.gz` | §4's serial counter rows, one per `--hilbert` mode, with `HilbertCounts` | `m29_cost_model --target <t> --workers 1 --work --hilbert <mode>` (runs overlapped, so their walls are not comparable) |
| `hilbert-timed.sh`, `hilbert-timed.jsonl.gz` | §4's timed MQ10 arms, n=5 at 16 workers and n=3 at one, rotated | `tools/benchlock.sh zb-835 research/m29-c1/hilbert-timed.sh out.jsonl 5 16` |
| `benchlock.log` | the two `zb-835` windows | |
