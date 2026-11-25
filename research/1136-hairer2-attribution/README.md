# #1136: why the signature engine is 400× slower than F4 on `sd-hairer-2`

**Measured at:** `research/1136-hairer2-attribution` branch from `main` `a63c5568`, Apple M-series
laptop (macOS), release build, 1 worker, unpinned. The deciding quantities are deterministic
operation counts (coefficient products, elements, batches, signature degrees). Wall times are medians
of 5 solves in one process. They are given for scale only and are not a Threadripper measurement.

Findings are in [`docs/research/sigf4-hairer2-attribution.md`](../../docs/research/sigf4-hairer2-attribution.md).

## Predeclared out-of-sample test (written before the development read below)

The cause found on `sd-hairer-2@p31` and `sd-butcher@p31` (the fitted rows) is this. On a
non-homogeneous input, the signature engine does the same work as on the input homogenized by one
extra smallest variable `h`. Its coefficient products on the two presentations agree to 0.02%.

**T1.** For every M34 **development** record at `p31` that is non-homogeneous and grevlex, has at
most 13 variables, and is outside `sd/runge-kutta-order-conditions` (47 records): run the signature
engine (1 worker, 60 s wall) on the record and on its homogenization. On every record where both
runs complete, `coefficient_products(affine) ÷ coefficient_products(homogenized)` lies in
[0.99, 1.01]. Any record outside the band falsifies the claim as a general rule. A run that does not
complete within the wall is reported and counts neither way.

The validation and untouched cohorts are not read.

## Files

| File | Role |
|---|---|
| `derive.py` | Derived presentations of the two fitted rows (`derived.json`), and with `--development` the T1 pairs (`development.json`) |
| `run.sh` | Every `derived.json` record under F4 and the signature engine, 5 solves each, into `results.jsonl.gz` |
| `run-development.sh` | T1: every `development.json` record under the signature engine and F4, once, into `development.jsonl.gz` |
| `tables.py` | `tables.md` from both result files |

## Reproduce

```sh
export CARGO_TARGET_DIR=...   # see CLAUDE.md
cargo build --release --features research-sigf4-usage --example sig_f4_study
python3 research/1136-hairer2-attribution/derive.py > research/1136-hairer2-attribution/derived.json
python3 research/1136-hairer2-attribution/derive.py --development > research/1136-hairer2-attribution/development.json
research/1136-hairer2-attribution/run.sh
research/1136-hairer2-attribution/run-development.sh
python3 research/1136-hairer2-attribution/tables.py > research/1136-hairer2-attribution/tables.md
```
