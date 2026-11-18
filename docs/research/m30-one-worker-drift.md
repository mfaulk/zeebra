# The one-worker drift between the M30 freeze and final `main` (#890)

**Measured at:** each of `4f5784c5` (the M30 freeze), `f4d4ae8e`, `53af1dde`, `833bb6bb`, `a3524d66`,
`a5089c5c`, `5452ae13`, `28e4e063`, `d6aa0526` and `e4826153` (final `main`): every commit between
the freeze and final `main` that touches `src/`, all on `main`. Each library is a `git archive` of its
commit. All are built with one instrument, `examples/m29_cost_model.rs` at `b1d8e36a`, minus the
`parallel_symbolic` assignment before `d6aa0526`, as [`research/m30-final/`](../../research/m30-final/README.md)
built the freeze. Also measured: one control, `d6aa0526` with `#[inline(always)]` on
`symbolic_preprocessing_seeded` (§3). Executable SHA-256s are in `identities.sha256` in
[`research/m30-one-worker-drift/`](../../research/m30-one-worker-drift/) with the records.
2026-11-18, 09:38–10:07 EST, inside a CCD 1–2 reservation. Eco-12 ran under
`tools/bench-reserve.sh run zb-890 8` and MQ11 concurrently under `run zb-890b 16`, one CCD each.
One-minute load 1.5–20.1 at child starts, with compilers on other CCDs. Host: Threadripper PRO 5995WX.

## 1. Result

**The Eco-12 serial-closure regression is real and comes from #878 (`d6aa0526`).** In the full
bisect, that commit's stage clock against its predecessor is **1.027 [1.004, 1.041]** (n = 7).
In two focused re-runs of that one step it is **1.026 [1.018, 1.032]** (n = 10) and
**1.035 [1.018, 1.046]** (n = 10). Freeze to final measures 1.024 [1.019, 1.042] here, against the
cohort's 1.035. No other commit moves it outside noise.

**It does not matter.** The extra time is 25–35 ms of a 12.4 s process. Process wall at the step is
0.997–1.005, and freeze to final it is 0.998 [0.993, 1.001]. The issue's MQ11 symbolic +1.1% does not
reproduce: final ÷ freeze is 0.993 [0.972, 0.999], and #878 alone is 0.969 [0.963, 0.986]. Both are
far inside #861's ≤5% one-worker line. No change is recommended, and the issue can close.

**The mechanism is not established, and it is not inlining.** The serial closure's source did not
change in #878. What changed is the call around it:

- `live()` is now always compiled and called, and returns `None` at `Serial`.
- The `shipping` closure.
- An `InternScratch` field in `ReducerCache`.
- `symbolic_intern` compiled into every build, which adds 560 KB to the executable.

`symbolic_preprocessing_seeded` went out of line at #878: there are no standalone symbols before it
and six after. Forcing it back inline leaves the regression unchanged (§3). What remains is code
placement of an unchanged hot loop. That is the same size as the ±2–3% process-wall swings below,
between commits that change nothing on the one-worker path.

## 2. Per-commit bisect (one worker, `--stages`)

Builds were interleaved, each repetition rotating the order and alternate repetitions reversing it.
Each figure is the median of the per-repetition ratios, paired by repetition, with a 95% bootstrap
interval over those pairs. "prev" is the commit before, in `main` order. Every run of a target
produced one basis digest.

**Eco-12** (CPU 8, n = 7):

| Commit | PR | symbolic ms | symbolic ÷ freeze | symbolic ÷ prev | process ÷ freeze | process ÷ prev |
|---|---|---:|---:|---:|---:|---:|
| `4f5784c5` | freeze | 898.1 | 1 | — | 1 | — |
| `f4d4ae8e` | #868 | 895.8 | 0.999 [0.986, 1.001] | 0.999 [0.986, 1.001] | 1.000 [0.994, 1.004] | 1.000 [0.994, 1.004] |
| `53af1dde` | #869 | 888.9 | 0.993 [0.982, 1.017] | 0.994 [0.990, 1.016] | 0.998 [0.987, 1.007] | 1.002 [0.992, 1.006] |
| `833bb6bb` | #870 | 896.3 | 0.998 [0.982, 1.014] | 1.005 [1.000, 1.010] | 0.997 [0.988, 1.011] | 0.999 [0.992, 1.004] |
| `a3524d66` | #874 | 889.8 | 0.991 [0.986, 1.001] | 0.993 [0.986, 1.004] | 0.999 [0.991, 1.009] | 1.001 [0.998, 1.002] |
| `a5089c5c` | #876 | 884.0 | 0.982 [0.974, 0.997] | 0.993 [0.981, 0.997] | 0.981 [0.976, 0.986] | 0.984 [0.978, 0.989] |
| `5452ae13` | #879 | 889.3 | 0.991 [0.974, 1.004] | 1.007 [0.997, 1.011] | 0.998 [0.994, 1.005] | 1.016 [1.013, 1.022] |
| `28e4e063` | #882 | 892.5 | 0.993 [0.983, 1.021] | 1.020 [0.998, 1.026] | 0.999 [0.990, 1.009] | 1.005 [0.995, 1.011] |
| `d6aa0526` | #878 | 921.7 | **1.025** [1.009, 1.033] | **1.027** [1.004, 1.041] | 0.998 [0.989, 1.000] | 0.999 [0.992, 1.003] |
| `e4826153` | #884 | 919.6 | **1.024** [1.019, 1.042] | 1.005 [0.994, 1.014] | 0.998 [0.993, 1.001] | 1.001 [1.001, 1.005] |

**MQ11** (CPU 16, n = 5; one repetition (rep 3) ran about 10% slow in most builds, which widens the
freeze-relative intervals):

| Commit | PR | symbolic ms | symbolic ÷ freeze | symbolic ÷ prev | process ÷ freeze | process ÷ prev |
|---|---|---:|---:|---:|---:|---:|
| `4f5784c5` | freeze | 1,187.3 | 1 | — | 1 | — |
| `f4d4ae8e` | #868 | 1,190.7 | 1.008 [0.994, 1.020] | 1.008 [0.994, 1.020] | 1.000 [0.996, 1.017] | 1.000 [0.996, 1.017] |
| `53af1dde` | #869 | 1,200.9 | 1.004 [1.001, 1.052] | 1.002 [0.986, 1.031] | 1.000 [0.997, 1.024] | 1.000 [0.998, 1.008] |
| `833bb6bb` | #870 | 1,201.5 | 1.007 [1.002, 1.133] | 1.006 [0.952, 1.129] | 0.998 [0.993, 1.122] | 1.002 [0.969, 1.124] |
| `a3524d66` | #874 | 1,192.3 | 1.004 [0.985, 1.110] | 0.997 [0.979, 1.025] | 1.001 [0.983, 1.084] | 0.999 [0.966, 1.003] |
| `a5089c5c` | #876 | 1,202.6 | 1.018 [0.981, 1.099] | 0.996 [0.920, 1.014] | 0.975 [0.961, 1.075] | 0.977 [0.953, 0.992] |
| `5452ae13` | #879 | 1,181.3 | 0.994 [0.978, 1.114] | 0.995 [0.976, 1.013] | 1.002 [0.990, 1.125] | 1.030 [1.028, 1.046] |
| `28e4e063` | #882 | 1,205.7 | 1.021 [0.989, 1.130] | 1.017 [1.012, 1.065] | 1.005 [0.991, 1.126] | 1.002 [1.001, 1.023] |
| `d6aa0526` | #878 | 1,169.8 | 0.985 [0.975, 1.110] | 0.969 [0.963, 0.986] | 0.997 [0.990, 1.103] | 0.992 [0.979, 0.998] |
| `e4826153` | #884 | 1,179.4 | 0.993 [0.972, 0.999] | 0.997 [0.899, 1.011] | 0.998 [0.984, 1.014] | 0.994 [0.919, 1.001] |

Reading the process-wall columns: #876 is −1.6% (Eco-12) and −2.3% (MQ11) against its predecessor,
and #879 is +1.6% and +3.0%. Neither commit touches the one-worker path. #876 charges scratch the
serial closure never allocates, and #879 is an opt-in route that is off here. Swings of that size
between neighbouring builds are layout, and they cancel. #882 (`28e4e063`, poly only) moves MQ11's
stage by +1.7% for the same reason. #878's Eco-12 step is the only one that reproduces, in all three runs.

## 3. Is it the inlining? (Eco-12, `28e4e063` / `d6aa0526` / `d6aa0526` + `#[inline(always)]`, n = 10)

| Build | symbolic ms | symbolic ÷ `28e4e063` | process ÷ `28e4e063` |
|---|---:|---:|---:|
| `28e4e063` | 897.4 | 1 | 1 |
| `d6aa0526` | 932.6 | 1.035 [1.018, 1.046] | 1.005 [0.993, 1.008] |
| `d6aa0526`, closure forced inline | 936.0 | 1.038 [1.026, 1.046] | 1.003 [0.992, 1.007] |

Inlined again, as `nm` confirms, the closure is just as slow. The earlier focused re-run of the
first two rows alone gave 1.026 [1.018, 1.032] (`eco12-step.jsonl.gz`).

## 4. Reproduce

```sh
T=/buildcache/cargo-target/zeebra-890
bash research/m30-one-worker-drift/build.sh 4f5784c5 f4d4ae8e 53af1dde 833bb6bb a3524d66 \
  a5089c5c 5452ae13 28e4e063 d6aa0526 e4826153
B=4f5784c5,f4d4ae8e,53af1dde,833bb6bb,a3524d66,a5089c5c,5452ae13,28e4e063,d6aa0526,e4826153
tools/bench-reserve.sh reserve
tools/bench-reserve.sh run zb-890 8 python3 -I research/m30-one-worker-drift/run.py --bindir $T/bin \
  --builds $B --target eco12-wide64 --reps 7 --output eco12.jsonl &
tools/bench-reserve.sh run zb-890b 16 python3 -I research/m30-one-worker-drift/run.py --bindir $T/bin \
  --builds $B --target mq11-goldilocks --reps 5 --output mq11.jsonl
wait; tools/bench-reserve.sh release
python3 -I research/m30-one-worker-drift/summarize.py eco12.jsonl mq11.jsonl
```
