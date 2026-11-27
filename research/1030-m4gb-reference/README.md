# #1030: M4GB reference, development evidence

**Measured at:** `52268421` (planted rows), `4d1ec9b7` (unplanted rows). macOS arm64, 14 cores,
unpinned, no RSS figure, one worker, 2026-11-24. Development only. The deciding run is in
`bench-host/`, measured at `41a36e93` (tag `measured/1030-m4gb-held-out`) on the bench host.
Analysis: [`docs/research/m4gb-m5gb-reference.md`](../../docs/research/m4gb-m5gb-reference.md).

| file | what |
|---|---|
| `planted.jsonl.gz` | 384 runs: 64 cells (n ∈ {12, 14} × m/n ∈ {1.5, 2, 3}, plus n = 16 × m/n ∈ {2, 3}; × GF(31), GF(32003) × density 1000/500 × seeds 1/2), 2 engines, 3 repetitions |
| `unplanted.jsonl.gz` | 24 runs: n = 12, seed 1, density 1000, both variants, 1 repetition, 20 s cap |
| `tables.md` | `m4gb-cohort.py --summarize` over both files (development, macOS) |
| `bench-host/held-out.jsonl.gz` | The deciding run: 384 runs, 32 held-out cells (m/n = 1.8; GF(31), GF(65521); n = 14, 16; density 1000/500; seeds 1/2; planted and unplanted), 4 engines, 3 repetitions, pinned to CPU 8 on reserved CCDs 1–2 |
| `bench-host/decide.py` → `bench-host/tables.md` | The pre-declared rule over that run: per-cell medians, M4GB's speedup over the best Zeebra arm and over grobx, and the verdict |
| `bench-host/provenance.txt`, `bench-host/held-out.console.gz` | Commit, binary SHA-256, grobx driver identity, placement, START/END with load; the run's console |
| `counters/held-out.jsonl.gz`, `counters/development.jsonl.gz` | Note §9: M4GB's iteration counters (`counters`) and phase totals (`stages`) over 128 runs, measured at `6c07b4e8` (tag `measured/1030-m4gb-counters`), bench host unpinned, 1 repetition |
| `counters/summarize.py` → `counters/*.md` | One row per cell: counters (a range where seeds or densities disagree), verified basis length, selection's share of the phase time |

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

The deciding run (bench host, reserved CCDs; needs `tools/external/provision-grobx.sh` and the
M4GB binaries for n = 14, 16 at 31 and 65521):

```sh
tools/bench-reserve.sh reserve
tools/bench-reserve.sh run 1030 8-23 tools/external/m4gb-cohort.py --binary $B \
  --output held-out.jsonl --reps 3 --cpus 8 --engines zeebra,zeebra-adaptive,m4gb,grobx \
  --deciding-run --sizes 31:14,16 --sizes 65521:14,16 --ratios 1.8 --unplanted --wall 180
tools/bench-reserve.sh release
python3 research/1030-m4gb-reference/bench-host/decide.py held-out.jsonl
```

M4GB's iteration counters (note §9; needs M4GB binaries for n = 14, 16 at 31, 32003 and 65521):

```sh
tools/external/m4gb-cohort.py --binary $B --output counters/held-out.jsonl --engines m4gb --reps 1 \
  --sizes 31:14,16 --sizes 65521:14,16 --ratios 1.8 --unplanted --deciding-run
tools/external/m4gb-cohort.py --binary $B --output counters/development.jsonl --engines m4gb --reps 1 \
  --sizes 31:14,16 --sizes 32003:14,16 --ratios 1.5,2,3 --unplanted
counters/summarize.py counters/held-out.jsonl
```
