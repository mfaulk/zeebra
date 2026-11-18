# Symbolic preprocessing after #861: what is left (#888)

**Measured at:** `c49479bb` — `main` `b1d8e36a` plus the two `InternReport` fields this note adds
(`seed_step`, `solo`) and their `symbolic_cost_model --replay live` output; the shipped closure is
otherwise unchanged. Executable `symbolic_cost_model` (features `external-runners,research-work`),
SHA-256 `fd2742eb02a54a23…`. 2026-11-18, 09:19–09:27 EST, inside a CCD 1–2 reservation
(`tools/bench-reserve.sh run zb-888 8-23`, children `taskset` to CPUs 8..8+w−1), one-minute load
6.0–12.4 at child starts with compilers running on other CCDs. Host: Threadripper PRO 5995WX.

Records, runner and summarizers: [`research/m30-symbolic-remainder/`](../../research/m30-symbolic-remainder/).

## 1. Result

**No target clears the bar, so nothing is implemented.** The two serial remainders #888 names are
small against process wall. On MQ10 at 16 workers the stitch is 7.4 ms and the merge walk 6.4 ms.
Together they are 31% of a 45 ms stage but **6.6% of the 208 ms F4 call**. Removing both entirely
would buy at most that much. The largest single slice is the **seed step**: 36% of the stage on MQ10,
52% on Cyclic-7, 34% on Eco-12 and 56% on MQ11. It is mostly dispatched scan, not serial code. Next
comes the caller-alone (solo) steps under the frontier threshold, 26% on MQ10 and 79% on Cyclic-7.
A smaller symbolic team (12 rather than 16) cuts the stage 4–10% on every target except Katsura-8,
where it costs 5–9%. It moves the F4 call by only 0–2%.

## 2. Component split (live, every batch served by the shipped closure, n = 10)

`--replay live --merge serial --level-workers w --min-frontier max(512, 48w)` is the shipped
`ParallelSymbolic::Auto { max_workers: w }` configuration (serial merge, 4 slices per worker, no
seed-row floor, per-batch retention), served through `with_live` so the report is collected. Medians
in ms, summed over the F4 call. `symbolic` is the stage clock. `other` is the stage minus
seed + spawn + scan + merge + emit + stitch: dispatch through `run_concurrent`, the `live` hook, and
the clock reads. `seed step` and `solo` cut across the phases. `seed step` is the whole first step of
every batch: interning the seed rows' terms. `solo` is the part of `scan` spent in steps below the
threshold, which the caller runs alone, interning as it scans.

| Target | w | F4 call | symbolic | seed step | solo | scan | merge walk | stitch | emit | spawn | other | steps / dispatched |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| MQ10 / 32003 | 16 | 207.8 | 45.2 | 16.2 | 11.7 | 23.7 | 6.4 | 7.4 | 1.1 | 2.1 | 4.1 | 121 / 22 |
| MQ10 / 32003 | 8 | 248.0 | 35.2 | 14.1 | 8.5 | 20.6 | 3.8 | 6.6 | 0.7 | 1.0 | 2.2 | 121 / 27 |
| MQ10 / 2³¹−1 | 16 | 190.1 | 44.6 | 16.1 | 11.6 | 23.2 | 6.3 | 7.6 | 1.0 | 2.0 | 4.1 | 121 / 22 |
| MQ10 / 2³¹−1 | 8 | 219.1 | 35.1 | 14.0 | 8.5 | 20.5 | 3.9 | 6.7 | 0.6 | 1.0 | 2.2 | 121 / 27 |
| Cyclic-7 / 2³¹−1 | 16 | 119.1 | 38.3 | 20.0 | 30.1 | 33.5 | 0.1 | 1.5 | 0.2 | 1.5 | 1.1 | 101 / 6 |
| Cyclic-7 / 2³¹−1 | 8 | 109.1 | 30.8 | 17.2 | 21.3 | 25.3 | 0.3 | 2.1 | 0.2 | 1.2 | 1.4 | 101 / 12 |
| Katsura-8 / 2³¹−1 | 16 | 13.9 | 4.1 | 1.3 | 4.0 | 4.0 | 0.0 | 0.0 | 0.0 | 0.0 | 0.1 | 46 / 0 |
| Katsura-8 / 2³¹−1 | 8 | 12.7 | 3.9 | 1.2 | 2.7 | 3.1 | 0.0 | 0.1 | 0.0 | 0.3 | 0.2 | 46 / 3 |

Every run of a target produced one basis digest.

Reading it:

- **MQ10's stage is slower at 16 workers than at 8: 45.2 against 35.2 ms.** The 768 threshold
  leaves more steps solo (+3.2 ms). The merge walk covers 64 slices rather than 32 (+2.5 ms), and
  cross-slice repeats are counted once per slice. Spawn (+1.0) and `other` (+1.9) are also larger. The
  16-worker F4 call is still faster, because elimination scales.
- **Cyclic-7 is the solo path.** 95 of 101 steps run on the caller at 16 workers. The stage is
  the serial closure in all but name. That is why #861 moved the cohort's Cyclic-7 / 2⁶⁴−353 stage only from 39.9 to 37.3 ms.
- **Katsura-8 dispatches nothing at 16 workers**, so it is entirely the solo path. Its stage is
  4 ms of a 14 ms call.

## 3. A smaller symbolic team (16-worker F4, team of 16 / 12 / 8, n = 5)

The same executable with `--workers 16 --level-workers {16,12,8}` (threshold `max(512, 48 × team)`),
arms interleaved with the order reversed on alternate repetitions. Ratios are per repetition against
the 16-team run of the same repetition: median [min, max] over the five pairs, not a confidence
interval.

| Target | team 12: stage | team 12: F4 call | team 8: stage | team 8: F4 call |
|---|---:|---:|---:|---:|
| MQ10 / 32003 | 0.952 [0.890, 0.989] | 0.991 [0.976, 1.003] | 0.943 [0.879, 0.966] | 0.987 [0.966, 0.997] |
| MQ10 / 2³¹−1 | 0.941 [0.930, 0.960] | 0.982 [0.980, 0.990] | 0.951 [0.931, 0.959] | 0.983 [0.981, 0.999] |
| Cyclic-7 / 2³¹−1 | 0.955 [0.931, 0.973] | 0.982 [0.962, 1.000] | 0.906 [0.887, 0.910] | 0.968 [0.950, 0.982] |
| Katsura-8 / 2³¹−1 | **1.085** [1.050, 1.100] | 1.029 [0.995, 1.056] | **1.056** [1.047, 1.103] | 1.009 [0.979, 1.041] |
| Eco-12 / 2⁶⁴−353 | 0.929 [0.904, 0.957] | 0.999 [0.991, 1.005] | 1.035 [1.013, 1.047] | 1.007 [1.004, 1.025] |
| MQ11 / Goldilocks | 0.898 [0.869, 0.901] | 0.987 [0.976, 0.991] | 0.979 [0.971, 1.002] | 1.001 [0.984, 1.003] |
| Katsura-11 / 2³¹−1 | 0.957 [0.930, 0.980] | 0.986 [0.981, 0.994] | 0.939 [0.917, 0.975] | 0.988 [0.987, 1.000] |

At 16 workers, a team of 12 runs MQ11's seed step in 140.6 ms rather than 171.7, and Eco-12's in
75.6 rather than 86.5. The cause is not established. One candidate is CPU contention between the
team and other threads on the same 16 CPUs. Katsura-8 is §11's 512-wide step again: a lower
threshold dispatches it, and the team start costs more than the step. A cap at 12 is therefore
**not** a clean win under #861's gates. It costs a small task 3% of process wall to save 1–2%
elsewhere. Separating the team size from the threshold might avoid that, but it is a tuning
experiment, not a structural target.

## 4. Where a next step would have to come from

| Remainder | MQ10 / 32003, 16 w | Best case if removed, F4 call |
|---|---:|---:|
| stitch (rows, leads, handle append) | 7.4 ms | −3.6% |
| serial merge walk | 6.4 ms | −3.1% |
| spawn + `other` | 6.2 ms | −3.0% |
| solo steps (serial by design) | 11.7 ms | not removable without dispatching narrow steps, which #861 §11 measured as a small-task regression |
| seed step (mostly dispatched scan) | 16.2 ms | a parallel scan already; what is left is its merge and stitch, counted above |

Each item is a few percent of process wall at most. None meets the "clear target" bar #888 set.
The issue stays open with this split recorded. A future attempt should start with the stitch's
`leads` hash inserts and row pushes, the one remainder that grows with the wide targets (61 ms on
Eco-12, 77 ms on MQ11 in §3's team-16 runs). That work should be judged by the F4 call, not the stage.

## 5. Reproduce

```sh
T=/buildcache/cargo-target/zeebra-888
RUSTC_WRAPPER="" CARGO_TARGET_DIR=$T TMPDIR=$T/tmp cargo build -j24 --release --locked \
  --features external-runners,research-work --example symbolic_cost_model
tools/bench-reserve.sh reserve
tools/bench-reserve.sh run zb-888 8-23 python3 -I research/m30-symbolic-remainder/run.py \
  $T/release/examples/symbolic_cost_model split.jsonl 10 mq10-32003,mq10-m31,cyclic7-m31,katsura8-m31 16,8
tools/bench-reserve.sh run zb-888 8-23 python3 -I research/m30-symbolic-remainder/run.py \
  $T/release/examples/symbolic_cost_model teams.jsonl 5 \
  mq10-32003,mq10-m31,cyclic7-m31,katsura8-m31,eco12-wide64,mq11-goldilocks,katsura11-m31 16 16,12,8
tools/bench-reserve.sh release
python3 -I research/m30-symbolic-remainder/summarize_split.py split.jsonl
python3 -I research/m30-symbolic-remainder/summarize_teams.py teams.jsonl
```
