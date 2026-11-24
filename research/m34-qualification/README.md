# #1011 M34 G2: portfolio candidate qualification

**Measured at:** Z0 = `28df047f` (tag `measured/1011-z0`), harness `2099df6e`. The report is
[`docs/research/m34-qualification.md`](../../docs/research/m34-qualification.md). Nothing in this
directory is timed, and no wall or memory figure is read from it.

| File | What |
|---|---|
| [campaign.py](campaign.py) | `run`: one fresh `examples/m33_qualify.rs` process per arm, worker count and row. `summarize`: verdicts per arm and field |
| [test_campaign.py](test_campaign.py) | Plan and verdict rules. Run in CI |
| `results/correctness.jsonl` | One line per cell: the arm, row, verdict, reference and the harness's typed outcome |
| `results/correctness.md` | The per-arm, per-field verdict table `summarize` writes |

```bash
python3 -m unittest discover -s research/m34-qualification -p 'test_*.py'
# Z0 + the harness, release, research-sigf4 (cap builds at -j24, private CARGO_TARGET_DIR):
#   git archive <harness commit> | tar -x; cargo build -j24 --locked --release --features research-sigf4 --example m33_qualify
python3 research/m34-qualification/campaign.py run --harness <m33_qualify> [--arms "P1 conv-w1" ...]
python3 research/m34-qualification/campaign.py summarize
```

`run` resumes: a cell already in `correctness.jsonl` is skipped.
