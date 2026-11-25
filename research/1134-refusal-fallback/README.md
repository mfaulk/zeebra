# #1134: typed-refusal fallback from conventional F4 to signature F4

**Measured at:** branch `research/1134-refusal-fallback` from `main` `5451e9f8`. Apple M-series
laptop (macOS, 14 cores), release build, `--features research-sigf4`, unpinned, one solve per cell.
Wall times are for scale, not Threadripper figures. What decides is which attempts complete and
which refuse. Those outcomes are typed, and budget refusals do not depend on the machine.

Findings: [`docs/research/refusal-fallback.md`](../../docs/research/refusal-fallback.md).

## The rule

`examples/m34_matrix.rs --engine fallback` is Gate H's `adaptive` arm (P8) followed by one rule:

> When the dispatcher's **conventional** route (`Shipping(reason)`, any reason except `Fallback`)
> stops with a size refusal (`TooManyRows`, `TooManyColumns`, `TooManyNonzeros` or
> `TooManyLiveBytes`), run the forced signature engine (Gate H's `sig` options, P4/P5/P6) on the
> same workers, with the wall budget that remains. The discarded attempt is charged.

Time and batch budgets never trigger it. Neither does a refusal from the signature route: the
signature engine has already run there. A completion is returned unchanged, so on every row where
P8 completes, the fallback costs nothing. This holds by construction and is tested
(`fallback_reruns_the_signature_engine_after_a_size_refusal`).

## Predeclared reading (written before any row below was solved)

**Rows.**
- *Development:* every M34 development record on which any conventional arm refused in #1012:
  `sd-ellipsoid-m2`, `gen-chandrasekhar-h-13` and `zb-col-grid-5x5`, at `p31` and `p64`.
- *Out of sample:* the 14 rows of `candidates.py`. They are built by the #1007 generators at
  parameters that are in no M34 cohort, and the list is fixed. No validation or untouched record is
  read.

**Cells.** `adaptive`, `fallback` and `sig` at 1 and 8 workers, with a 120 s wall each. Eight is
the most this machine runs without oversubscribing its 10 performance cores. Gate H's 16-worker
arms are not reproduced here.

**Reported per cell.** Whether the rule fired. The discarded attempt's wall (the wasted work). The
fallback's outcome. Its total wall against the signature engine alone.

**Decision.**
- The fallback is worth carrying into an M34-Q-style qualification if, on the out-of-sample rows,
  it fires at least once **and** completes at least one row that `adaptive` refuses at the same
  worker count.
- If it never fires out of sample, the record is "no out-of-sample evidence", whatever it did on
  the development rows.
- If it fires but never completes, the rule is rejected as written.

## Files

| File | Role |
|---|---|
| `candidates.py` | The out-of-sample rows, written to `candidates.json` |
| `run.sh` | Every cell into `cells.jsonl` |
| `tables.py` | `tables.md` from `cells.jsonl` |

## Reproduce

```sh
export CARGO_TARGET_DIR=...   # see CLAUDE.md
cargo build --release --features research-sigf4 --example m34_matrix
python3 research/1134-refusal-fallback/candidates.py > research/1134-refusal-fallback/candidates.json
research/1134-refusal-fallback/run.sh
python3 research/1134-refusal-fallback/tables.py > research/1134-refusal-fallback/tables.md
```
