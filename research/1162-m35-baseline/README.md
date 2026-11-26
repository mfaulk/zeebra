# #1162: M35 baseline, panel and one-worker gap to grobx

The data behind [`docs/research/m35-baseline.md`](../../docs/research/m35-baseline.md).

**Measured at:** `184b5555` (tag `measured/1162-harness`; `src/` identical to Z0 `125658bb` = tag
`measured/1162-z0`). grobx 0.155.1 at `8005a2a1`. Development mode only; no figure here decides a gate.

| File | What it is |
|---|---|
| `panel.json` | The declared panel: families, roles, splits, envelopes, why each family matters, characteristic-ladder gaps |
| `catalog.py` | Writes the panel as `corpus-instance-v1` records. M34 rows are copied from the M34 catalogs; ladder, MQ and GF(2) rows come from the Z0 generators via `--input-only` |
| `catalog-digests.json` | The rebuilt catalog's SHA-256 and every record's `normalized_input_digest`. The catalog itself (about 3 MB) is not committed |
| `probe.py` | Development-mode probe. Runs each record in fresh processes pinned to one CPU, with arms `f4-stages`, `f4`, `adaptive`, `sig-stages`, `grobx` and `grobx-certified` |
| `probe-dev.jsonl` | Every probe attempt (204 records), stopped and timed-out attempts included |
| `summarize.py` | Band and ratio table (default), `--phases` (F4 stage shares), `--signature` (signature-engine shares), `--price panel.json` (the manifest) |

## Reproduce

Keep target, temporary and output directories on `/buildcache`, never `$HOME`.

```sh
git archive measured/1162-harness | tar -x -C "$SRC" && cd "$SRC"
export RUSTC_WRAPPER="" CARGO_INCREMENTAL=0 TMPDIR=/buildcache/cargo-target/zeebra-1162/tmp
export CARGO_TARGET_DIR=/buildcache/cargo-target/zeebra-1162-pub
cargo build --release --features research-sigf4 --example m34_matrix --example m33_qualify --example sig_f4_study
B=$CARGO_TARGET_DIR/release/examples
python3 research/1162-m35-baseline/catalog.py build --qualify $B/m33_qualify --study $B/sig_f4_study \
  --out /buildcache/cargo-target/zeebra-1162/catalog.json     # rewrites catalog-digests.json; diff it
python3 research/1162-m35-baseline/probe.py --matrix $B/m34_matrix \
  --grobx "$(readlink -f ~/.local/opt/zeebra-ext/bin/grobx-driver)" \
  --catalog /buildcache/cargo-target/zeebra-1162/catalog.json --cpu 40 \
  [--ids a@m31,b@p31] [--arms f4-stages,f4,adaptive,sig-stages,grobx,grobx-certified] --out probe.jsonl
python3 research/1162-m35-baseline/summarize.py research/1162-m35-baseline/probe-dev.jsonl [--phases | --signature]
python3 research/1162-m35-baseline/summarize.py research/1162-m35-baseline/probe-dev.jsonl --price research/1162-m35-baseline/panel.json
```

The committed records came from eight shards on CPUs 40–47, plus later shards for `sig-stages`,
`grobx-certified` and four added rows. The probe was run without a reservation, at a load average
of 10–19, while another agent held CCDs 1–2.

`probe.py` gained `--arms` and the `grobx-certified` arm after the harness tag. The edits are to
the script only; every Zeebra attempt ran the `m34_matrix` binary built from `measured/1162-harness`.

## Not done here

- The publication-mode read of the priced manifest (`docs/research/m35-baseline.md` §5). It needs
  `tools/bench-job` with the exclusive lock and a CCD reservation.
- The research-envelope frontier run (900 s, 64 GiB).
