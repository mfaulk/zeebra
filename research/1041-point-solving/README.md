# #1041: point-solving feasibility screen

**Measured at:** branch `research/1041-point-solving` from `main` `04d949ff`. Apple M-series laptop
(48 GiB), release build, one worker, unpinned, one fresh process per solve. This is a development
screen; the walls are not bench-host figures.

Findings and decision: [`docs/research/point-solving-screen.md`](../../docs/research/point-solving-screen.md).
The decision rule was posted on #1041 before any measurement.

## Files

| File | Role |
|---|---|
| `model.py` | Crossbred and XL + block Wiedemann counts (`counted.json`); `check` runs the published-figure self-checks |
| `run.sh` | Zeebra's pipeline, the hybrid branches and the rate calibration (`examples/point_solving_screen.rs`) → `measured.jsonl` |
| `tables.py` | `tables.md`: the comparison and the predeclared decision |

## Reproduce

```sh
export CARGO_TARGET_DIR=...   # see CLAUDE.md
cargo build --release --example point_solving_screen
python3 research/1041-point-solving/model.py > research/1041-point-solving/counted.json
research/1041-point-solving/run.sh > research/1041-point-solving/measured.jsonl
python3 research/1041-point-solving/tables.py > research/1041-point-solving/tables.md
```

`run.sh` runs one solve at a time, for about 15 minutes in total. Its slowest rows are A at 18 × 36
and C at 28 × 56.
