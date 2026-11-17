# M29 final cohort (#837)

**Measured at:** `88bc45de`. Production source (`src/`, `examples/`, `Cargo.lock`) is identical to
`main` at `438c0816` (#852), which includes #851's parallel candidate finishing. 2026-11-17,
01:51–02:32 EST, one `tools/benchlock.sh zb-837` window per suite ([benchlock.log](benchlock.log)),
one-minute load 1.4–5.9. Executables and their SHA-256s are in [identities.json](identities.json).
grobx-driver and groebner-rs-driver are the #834 builds (same pins), copied in.
**Host:** Threadripper PRO 5995WX, `ZEEBRA_MACHINE=5995wx`. The #834 suites were run unchanged by
`research/m29-baseline/run.sh` with `REPS=9 MQ10_REPS=9 MQ10_WALL=3600` (see that directory's
README for the build recipe).

| File | What |
|---|---|
| `walls.jsonl.gz` | `costmodel.py` walls suite: four targets × 1/4/8/16 workers × 9, fresh process, CCD-aligned `taskset`, the instrument's full JSON per child |
| `wide-attempts.json` | `extract.py` over nine `wide-corpus.py` passes: grobx and groebner-rs, one worker, Eco-12 / 2⁶⁴−353 and MQ11 / Goldilocks |
| `mq10-attempts.json` | `extract.py` over the `comparand-scaling.py` windows: Zeebra, exact-mode msolve, grobx, groebner-rs on MQ10 at 32003 and 2³¹−1, answers checked against #739's references |
| `suite-starts.jsonl` | CPU context at each suite's start, inside the lock |
| `tables.md` | `python3 research/m29-baseline/summarize.py research/m29-final` |
| `verdicts.py` → `verdicts.md` | the Goal A and Goal B ratios with 95% bootstrap intervals |

**MQ10 windows.** `comparand-scaling.py` stops a window when any compiler starts on the machine.
`mq10-try1` stopped on its last repetition, so every 32003 cell has n=9, and the 2³¹−1 cells at
4/8/16 workers have n=8. Tries 2–4 stopped on their first child: other sessions' `cargo check` /
`clippy-driver` runs, recorded in each attempt. They are kept in `mq10-attempts.json` and not
pooled. Try 1 is the reported window. Further retries were stopped rather than resampled, because a
complete window cannot move either Goal A ratio across 1.5 (the intervals are [2.47, 2.55] and
[1.64, 1.78]).

Every Zeebra run returned one basis digest per target. grobx's basis text is identical to
Zeebra's on both wide targets, and groebner-rs agrees canonically (the controller's
`verify_bases`). The MQ10 answers are verified against the Singular references.
