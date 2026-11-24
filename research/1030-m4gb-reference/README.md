# #1030: M4GB reference, development evidence

**Measured at:** `52268421` (planted rows), `4d1ec9b7` (unplanted rows). macOS arm64, 14 cores,
unpinned, no RSS figure, one worker, 2026-11-24. Development only: nothing here decides #1030.
Analysis: [`docs/research/m4gb-m5gb-reference.md`](../../docs/research/m4gb-m5gb-reference.md).

| file | what |
|---|---|
| `planted.jsonl.gz` | 384 runs: 64 cells (n ∈ {12, 14} × m/n ∈ {1.5, 2, 3}, plus n = 16 × m/n ∈ {2, 3}; × GF(31), GF(32003) × density 1000/500 × seeds 1/2), 2 engines, 3 repetitions |
| `unplanted.jsonl.gz` | 24 runs: n = 12, seed 1, density 1000, both variants, 1 repetition, 20 s cap |
| `tables.md` | `m4gb-cohort.py --summarize` over both files |

One JSON object per run: the row, its input digest, engine, status, process wall (M4GB) or
in-process wall (Zeebra), and M4GB's own `engine-solve` and `engine-cpu` stages.

## Reproduce

```sh
tools/external/provision-m4gb.sh "12 14 16" "31 32003"
CARGO_TARGET_DIR=<private> cargo build --release --features external-runners --example m4gb_comparison
B=<private>/release/examples/m4gb_comparison
tools/external/m4gb-cohort.py --binary $B --output planted.jsonl \
  --sizes 31:12,14 --sizes 32003:12,14 --densities 1000,500 --seeds 1,2 --reps 3 --wall 180
tools/external/m4gb-cohort.py --binary $B --output planted.jsonl \
  --sizes 31:16 --sizes 32003:16 --ratios 2.0,3.0 --densities 1000,500 --seeds 1,2 --reps 3 --wall 180
tools/external/m4gb-cohort.py --binary $B --output unplanted.jsonl \
  --sizes 31:12 --sizes 32003:12 --densities 1000 --seeds 1 --reps 1 --wall 20 --unplanted
tools/external/m4gb-cohort.py --summarize planted.jsonl
```

On the bench host, pin the launcher and add the grobx arm and Zeebra's best qualified
configuration before any ratio is quoted (note §7).
