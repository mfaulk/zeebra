# M33 calibration: isolation, contamination and dev-mode tolerance (#968)

**Measured at:** binary `31e334bd` (M32 final, F0; `sig_f4_study --features research-sigf4`, release, fat LTO,
1 CGU, x86-64-v3, from `git archive`), harness `c1d94d39` (idle) and `0f5a8f89` (build, stream) of
`feat/968-bench-job-wiring`, tagged `measured/968-calibration`. 2026-11-21, 00:07–00:28 local, on the
5995WX, CCDs 1–2 reserved (`tools/bench-reserve.sh`), dev mode, one session per condition.

## What was run

- `run.sh <condition>` submits one dev-mode `tools/bench-job` job per condition. The job covers
  `wide64/eco-12` and `gf32003/mq-random-10`, each at 1 and 16 workers (`--engine entry`), with
  n = 9 repetitions per cell. Each repetition runs three arms, rotated:
  - `a` and `a2`: the same binary, giving the A/A pair;
  - `s5`: the same binary followed by a sleep of 5% of its own wall, giving a known slowdown.
- The background load runs on the non-bench CPUs (`0-7,24-71,88-127`) and starts only once the job
  holds its benchlock:
  - **idle**: nothing of ours.
  - **build**: `cargo clean; cargo build -j48 --tests` of zeebra in a loop.
  - **stream**: `stream.c`, a triad on 32 threads over 192 MiB per thread.
- `summarize.py` builds `table.md` from the three journals. `attempts.jsonl` is the per-attempt
  export the table is computed from. Intervals are percentile-bootstrap 95% intervals of the median
  paired ratio. "Contaminated" applies `tools/bench_contamination.py`'s dev rules, with the clock
  rule taken per cell.
- Condition (d), other repositories' CI, did not occur: `runner_workers` was 0 throughout.
  Condition (e), fixed clock against boost, was not run because #954 needs the owner's root step.

## Results

| condition | cell | A median s | abs drift vs idle | A/A median [95% CI] | 5% arm [95% CI] | contaminated |
|---|---|---:|---:|---|---|---:|
| idle | eco-12 1w | 2.549 | 1.000x | 0.999 [0.986, 1.011] | 1.056 [1.053, 1.062] | 11/27 |
| idle | eco-12 16w | 1.715 | 1.000x | 0.997 [0.981, 1.002] | 1.053 [1.035, 1.056] | 11/27 |
| idle | mq10 1w | 0.459 | 1.000x | 1.001 [0.985, **1.036**] | 1.063 [1.050, 1.098] | 0/27 |
| idle | mq10 16w | 0.240 | 1.000x | 0.989 [0.983, 1.002] | 1.086 [1.069, 1.091] | 0/27 |
| build | eco-12 1w | 2.775 | 1.088x | 0.994 [0.985, 1.008] | 1.050 [1.041, 1.063] | 0/27 |
| build | eco-12 16w | 1.757 | 1.024x | 1.005 [0.995, **1.027**] | 1.057 [1.042, 1.082] | 18/27 |
| build | mq10 1w | 0.490 | 1.069x | 1.002 [0.997, **1.034**] | 1.067 [1.057, 1.417] | 8/27 |
| build | mq10 16w | 0.240 | 1.002x | 0.999 [0.980, 1.020] | 1.087 [1.076, 1.093] | 7/27 |
| stream | eco-12 1w | 2.996 | **1.175x** | 1.005 [**0.970**, 1.012] | 1.048 [1.038, 1.065] | 0/27 |
| stream | eco-12 16w | 1.936 | **1.129x** | 0.993 [0.982, 1.003] | 1.046 [1.035, 1.054] | 8/27 |
| stream | mq10 1w | 0.495 | 1.078x | 1.001 [0.997, 1.007] | 1.066 [1.063, 1.075] | 1/27 |
| stream | mq10 16w | 0.256 | 1.067x | 1.000 [0.990, 1.014] | 1.095 [1.074, 1.123] | 0/27 |

Contamination per session, from `table.md`:

| condition | contaminated | void (> 20%) | reasons | max sibling busy | p90 bench foreign | median rest load |
|---|---:|---|---|---:|---:|---:|
| idle | 22/108 (20.4%) | yes | clock ×22 | 0.64% | 0.40% | 1.7 |
| build | 33/108 (31%) | yes | clock ×28, sibling ×14, bench foreign ×3 | 100% | 2.53% | 6.9 |
| stream | 9/108 (8%) | no | clock ×9 | 1.16% | 0.87% | 36.4 |

## What it sets

- **Paired ratios survive every condition.** All twelve A/A medians lie within 1.1% of 1.0. Every
  5% arm is detected, with each interval's lower end above 1.03. Three of twelve A/A intervals
  cross ±2.5% (bold above), one in each condition, idle included. At n = 9 that is the width of the
  interval, not a load effect. #848's earlier finding, A/A within about 2.5% under builds, stands.
- **Absolute walls do not survive.** The bandwidth load costs up to 17.5% (Eco-12 1 w) and builds
  up to 9%, with the CCDs fenced. A dev-mode absolute wall is not a publication figure. §11.2
  already says so, and this table is the evidence for it.
- **The dev rules do not see bandwidth load.** Under STREAM, siblings stayed below 1.2% busy and
  bench-CPU foreign time below 0.9%, yet walls moved 7–17%. Publication mode does catch it: the
  rest-load rule (busy-CPU equivalents ≥ 4) reads 36 there and refuses. The issue's go/no-go
  ("refuse dev beside bandwidth jobs if (c) moves the A/A interval outside ±2.5%") is **not
  triggered**: STREAM's one wide interval is matched by idle's. So no dev refusal is added.
- **Sibling and foreign rules catch real events.** Under builds, the siblings of bench CPUs hit
  6–100% busy in the first ~20 s of the loop, while `cargo clean` deleted a target directory. The
  build itself was pinned to the rest CPUs. The likely source is unbound kernel workers, which a
  user cpuset does not fence. They also reached 30–50% sporadically. Idle and STREAM never exceeded
  1.2%.
- **The clock rule voids a quiet session.** At 3% against the cell median, it flagged 11/27 of
  each idle Eco-12 cell, enough to void the idle session (20.4% > 20%). Those flags are real
  frequency differences, not sampler noise: an Eco-12 arm that runs straight after a 16-worker
  MQ10 burst runs at the all-core 3.99 GHz instead of 4.54 GHz (#827's hysteresis). Arm rotation
  balances that across arms, which is why the ratios hold.

## Threshold recommendation (§11.2)

- **Sibling and bench-foreign busy: tighten 5% → 2%** once a second idle/STREAM session confirms
  it. The quiet maxima were 0.64% (idle) and 1.16% (STREAM), against 6–100% for the build events.
  The thresholds are not changed in this PR, because one session per condition is thin.
- **Clock deviation: do not tighten.** In dev mode it already voids an idle session, because of a
  physical effect that the paired design cancels. Loosening it or changing its scope (for example,
  dev mode reporting it as a note, or measuring the clock over the attempt's busy CPUs only) needs
  an owner decision on #965. Until then dev sessions will often read as void on the clock rule
  alone.
- **Publication rest-load < 4: keep.** It is the only rule that sees bandwidth load (36 under
  STREAM, 1.7 idle).
- **Void fraction 20%: keep.** The clock rule decides it, see above.

## Caveats

- `s5` adds a shell, `date` ×2, `awk` and `sleep`: about 10–25 ms of fixed cost. That is why it
  reads 1.06–1.09 rather than 1.05 on the 0.24–0.5 s MQ10 cells. Detection is unaffected.
- One session per condition and n = 9 are the plan's budget. The three sessions took about 15
  minutes of reservation in total. The idle and build sessions ran under zb-962's reservation,
  queued behind its benchlock. STREAM ran under a reservation taken after zb-962 released, and
  released at the end.
- Job `a01c00dc4b0d` under the job root is a STREAM submit that never ran. Its first runner found
  no reservation.
