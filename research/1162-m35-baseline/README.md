# #1162: M35 baseline, panel and one-worker gap to grobx

The data behind [`docs/research/m35-baseline.md`](../../docs/research/m35-baseline.md).

**Measured at:** `184b5555` (tag `measured/1162-harness`; `src/` identical to Z0 `125658bb` = tag
`measured/1162-z0`). grobx 0.155.1 at `8005a2a1`. Development mode only; no figure here decides a gate.

| File | What it is |
|---|---|
| `panel.json` | The declared panel: families, roles, splits, envelopes, why each family matters, characteristic-ladder gaps, and (#1200) the R1/R2/R3 regime declaration of plan Amendment 1 |
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

## Amendment 1 additions (#1200)

#1200 changed the panel before the publication read, as plan §7.1 (Amendment 1) requires:

- The R1 family (Chandrasekhar-H 11–13) and the R2 rows (Katsura-12, Eco-12, Eco-13) are added at
  BabyBear (2013265921) and KoalaBear (2130706433) as R3 targets. `catalog.py` reduces the M34
  public problems at those primes with `m34_public_corpus.reduce_record`, the same reduction that
  made the p31 and p64 records. `m33_qualify --field babybear|koalabear` generates Katsura and Eco.
- Eco-13 moves from the eco family's frontier to its rows: it completes under default limits on
  both fields, so it is an R2 row rather than a frontier.
- `panel.json` gains a `regimes` block naming every R1, R2 and R3 record id.

`catalog-digests.json` is rebuilt from `measured/1200-harness`, whose `src/` is still Z0's. The
publication read itself is in [`research/1200-m35-publication/`](../1200-m35-publication/).

## Not done here

- The publication-mode read of the priced manifest (`docs/research/m35-baseline.md` §5). It needs
  `tools/bench-job` with the exclusive lock and a CCD reservation.
- The research-envelope frontier run (900 s, 64 GiB).
