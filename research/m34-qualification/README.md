# #1011 M34 G2: portfolio candidate qualification

**Measured at:** Z0 = `28df047f` (tag `measured/1011-z0`), harness `2099df6e`. The report is
[`docs/research/m34-qualification.md`](../../docs/research/m34-qualification.md). The correctness
campaign is untimed. The only timed read is #997's preregistered gate (`gate997.*`), and every
figure it publishes carries Z0 and the harness commit.

| File | What |
|---|---|
| [campaign.py](campaign.py) | `run`: one fresh `examples/m33_qualify.rs` process per arm, worker count and row. `summarize`: verdicts per arm and field |
| [test_campaign.py](test_campaign.py) | Plan and verdict rules. Run in CI |
| `results/correctness.jsonl` | One line per cell: the arm, row, verdict, reference and the harness's typed outcome |
| `results/correctness.md` | The per-arm, per-field verdict table `summarize` writes |
| [gate997.json](gate997.json) | #997's preregistered gate (owner decision on #1043): rows, workers, n, thresholds, decision rule |
| [gate997.py](gate997.py) | `references` (untimed), `manifest --job cyclic8\|mq10`, `verdict --job-dir …` → `gate997.md` |
| [test_gate997.py](test_gate997.py) | The preregistration, manifests and verdict rules. Run in CI |
| `gate997-references.json` | Independent references for the gate's rows |
| `manifests/` | The two submitted #997 job manifests (`1076f513f424`, `d05e8d60ef86`) |

```bash
python3 -m unittest discover -s research/m34-qualification -p 'test_*.py'
# Z0 + the harness, release, research-sigf4 (cap builds at -j24, private CARGO_TARGET_DIR):
#   git archive <harness commit> | tar -x; cargo build -j24 --locked --release --features research-sigf4 --example m33_qualify
python3 research/m34-qualification/campaign.py run --harness <m33_qualify> [--arms "P1 conv-w1" ...]
python3 research/m34-qualification/campaign.py summarize
```

`run` resumes: a cell already in `correctness.jsonl` is skipped.
