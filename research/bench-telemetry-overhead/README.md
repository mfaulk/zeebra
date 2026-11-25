# #1105 telemetry overhead

**Measured at:** harness `34ae04f8` (`tools/cpu-context.sh` with the `ZEEBRA_CPU_CONTEXT_TELEMETRY`
toggle; `bench_campaign.py` as on `main`). Subject `sig_f4_study` (`--features research-sigf4`, fat
LTO), built from the `1c44aac6` library tree, SHA-256 `f417ef81483e05d4…` (`session-1/binary.sha256`).
2026-11-25, 13:18:21–13:19:53 EST, CCDs 1–2 reserved, announced as `#1105-telemetry-aa` in
`benchlock.log`, load 4.7 at start, nothing else on the bench.

Is recording #1105's telemetry worth what it costs? Telemetry is gathered only in the before/after
snapshots, outside the timed region. So the question is whether those snapshots move the timed wall
through cache, boost or scheduling, and what they cost the harness.

## Gate: timed walls (`aa.py`, `summarize.py`)

Each attempt is what `tools/bench-job`'s `run_attempt` does: snapshots, frequency sampler,
`perf stat -p`, `rss-guard`, GNU time, and the harness on the spare CPUs of `run.cpus=8-23` where
there are any (15 for 1 worker, none for 16). The two arms differ only in
`ZEEBRA_CPU_CONTEXT_TELEMETRY` (1 = on, 0 = off). The order alternates per pair, and there are 9 pairs
per cell. Gate (#1105): the median off/on ratio is within 1.000 ± 0.005, and the 95% CI covers 1.0.

| cell | pairs | median on s | median off s | off/on median [95% CI] | gate |
|---|---:|---:|---:|---|---|
| gf32003/mq-random-10 @ 16w (no spare CPU) | 9 | 0.2522 | 0.2537 | 1.0036 [0.9830, 1.0167] | pass |
| wide64/eco-12 @ 1w | 9 | 2.1401 | 2.1537 | 1.0034 [0.9905, 1.0238] | pass |

No signal is dropped. The CIs are about ±2% wide at n = 9, so the gate rules out a large effect, not a
0.5% one. The medians are its evidence. The calibration protocol (#1106 §7.2) sizes n for a 1%
half-width.

## Harness cost (not gated)

`cpu-context.sh 8-23`, 5 snapshots × 2 alternations, on the rest CPUs:

| telemetry | wall per snapshot | CPU per snapshot |
|---|---:|---:|
| on | 0.60 s | 0.70 CPU-s |
| off | 0.46 s | 0.52 CPU-s |

The fields add about 0.14 s and 0.18 CPU-s to each snapshot (+31%), twice per attempt. That lands
on the attempt's CCD when the harness shares it, and on its CPUs when there is no spare. #1104
(`docs/research/bench-isolation-audit.md` §5) recommends moving the harness off the reservation
for #1108, which makes this cost the harness's alone.

## Reproduce

```bash
bash research/bench-telemetry-overhead/run.sh "$PWD" <sig_f4_study> research/bench-telemetry-overhead/session-N 9
python3 -I research/bench-telemetry-overhead/summarize.py "$PWD" research/bench-telemetry-overhead/session-N/attempts.jsonl
```

`run.sh` waits until no reservation is up and `zbbench.slice` is empty, reserves CCDs 1–2, runs
`aa.py` under `bench-reserve run`, and releases.
