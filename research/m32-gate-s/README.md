# #940 M32-S1b Gate S: campaign and evidence

**Result: Gate S fails.** T1 and T2 pass with wide margins, but three dev-corpus cells exceed
head ÷ base 95% upper 1.05 (below). Per the plan (`docs/MILESTONE-ADAPTIVE-F4.md` §8.2), #940
closes with this negative result, and a second design needs an owner decision on #938.
**Measured at:** `592653ee` (head: the parallel closure, tagged `measured/940-gate-s`) against its
merge base `ce67df76`. Each `sig_f4_study` was built from a `git archive` of its commit into its own
target directory (release, `--features research-sigf4`). SHA-256 in
[binaries.sha256](binaries.sha256). Later branch commits touch only `research/`.
Gate S is read once: n = 9 fresh processes per cell (n = 31 for the rows under 50 ms, read on the
in-process call time), head and base interleaved and rotated in one session per suite, under
`benchlock` on CPUs 8–23 ([benchlock.log](benchlock.log), [sessions.txt](sessions.txt)).

| file | what |
|---|---|
| [campaign.py](campaign.py) | the controller: M31's `run_one` child runner over the head and base arms; suites `gate`, `small`, `mq10`, `curve` |
| [run.sh](run.sh) | one session: stage both arms' binaries on tmpfs, reserve CCDs 1–2 before each suite unless another session holds them, `bench-reserve run zb-940 8-23`, release on exit |
| [summarize.py](summarize.py) → [tables.md](tables.md) | paired per-repetition ratios with 95% bootstrap intervals, the §10.3 precision rule, the worker curve and the MQ10 re-read |
| [test_campaign.py](test_campaign.py) | unit tests for the plan and the summary; run in CI |
| `gate.jsonl.gz` | Eco-12 `cl:16` and `en:1/16`, and the dev rows at or above 50 ms at `en:1/16` |
| `small.jsonl.gz` | the dev rows under 50 ms at `en:1/16`, n = 31 |
| `mq10.jsonl.gz` | MQ10 at both fields: `en` at 1/4/8/16 workers on both builds, and the head's shipping F4 |
| `curve.jsonl.gz` | `cl` at 1/2/4/8/16 workers on Eco-12 and MQ10 / GF(32003), with stage clocks |

## Gate S

| Criterion | Cell [95%] | Threshold | Result |
|---|---|---|---|
| T1 Eco-12 symbolic, base ÷ head, `cl:16` | 2.630 [2.585, 2.649] | ≥ 1.5, lower ≥ 1.4 | met |
| T2 Eco-12 process wall, head ÷ base, `en:16` | 0.819 [0.813, 0.824] | ≤ 0.90, upper ≤ 0.92 | met |
| Dev corpus head ÷ base, upper ≤ 1.05 at 1 and 16 workers | 3 of 26 cells missed, 3 imprecise | every cell | **missed** |
| Peak RSS ≤ 1.10× base | max 1.085 (MQ10 / GF(32003), 16 workers) | every cell | met |
| §9.2 tests T1–T6 | `src/grobner/sigf4/symbolic_tests.rs`, 10 tests | all pass | met |

The cells that miss:

| Row | Workers | Head ÷ base [95%] | Why |
|---|---:|---|---|
| goldilocks/katsura-11 | 1 | 1.044 [1.020, 1.068] | the serial closure, unchanged in algorithm, is slower in this build |
| goldilocks/mq-random-11 | 1 | 1.037 [1.033, 1.054] | the same |
| goldilocks/noon-7 | 16 | 1.055 [1.040, 1.071] | the team starts on 19 levels of a closure too small to repay it |

At 1 worker the engine takes the serial closure, which only moved into its own function. The
`cl:1` stage clocks still show its symbolic stage 3.6% slower on Eco-12 (458 against 442 ms) and on
MQ10 (206 against 198 ms). Elimination and the other stages match. That is a code-generation
effect on the serial path, not extra work. On Noon-7 / Goldilocks at 16 workers the team runs on 19
levels, and the symbolic stage goes from 22–24 to 29–30 ms of a 70 ms solve. These two runs per
arm are diagnostic only: CPUs 32–47, after the campaign, not timed for the gate.

The imprecise cells (half-width above 0.025) are wide64/cyclic-7 at 1 worker, wide64/noon-8 at 1,
and goldilocks/katsura-4 at 1. Their medians are 0.980, 1.003 and 1.007.

## Worker curve (`cl`, medians, ms)

| Row | Workers | Symbolic base → head | Base ÷ head | Wall base → head |
|---|---:|---|---|---|
| Eco-12 | 1 | 442 → 458 | 0.969 | 2,822 → 2,835 |
| Eco-12 | 2 | 453 → 326 | 1.385 | 2,143 → 2,017 |
| Eco-12 | 4 | 469 → 224 | 2.072 | 1,820 → 1,601 |
| Eco-12 | 8 | 492 → 183 | 2.687 | 1,728 → 1,440 |
| Eco-12 | 16 | 532 → 201 | 2.642 | 1,721 → 1,418 |
| MQ10 / GF(32003) | 1 | 198 → 206 | 0.955 | 472 → 479 |
| MQ10 / GF(32003) | 2 | 202 → 150 | 1.346 | 395 → 341 |
| MQ10 / GF(32003) | 4 | 212 → 116 | 1.809 | 369 → 273 |
| MQ10 / GF(32003) | 8 | 217 → 99 | 2.196 | 360 → 242 |
| MQ10 / GF(32003) | 16 | 231 → 120 | 1.918 | 379 → 273 |

The symbolic stage stops scaling past 8 workers on both rows. On Eco-12 it reaches 2.6–2.7×, close
to #933's replay ceiling of 2.95×.

## MQ10 re-read (for #927)

Through `f4_signature` (`en`), the head is 0.68–0.74× the base at 4–16 workers on both fields. It is
still slower than the shipping F4 at 16 workers: 1.134 [1.120, 1.154]× on GF(32003) and
1.265 [1.245, 1.284]× on GF(2³¹−1), against M31's 1.6–1.75×. At 8 workers it is 0.88× and 1.00×.
The full table is in [tables.md](tables.md).

## Method notes

- **Binary staging.** A binary's mapped text counts toward peak RSS. On XFS, how much of it a run
  maps depends on the file's page-cache folios: a freshly linked head measured 2 MB above a
  byte-identical copy of itself, which is +40% on the 5 MB rows. `run.sh` therefore runs both arms
  from one tmpfs copy.
- **Reservation.** The `gate` suite ran under another session's CCD reservation, which ended before
  `mq10` started. The first attempts at `mq10`, `small` and `curve` therefore refused to start
  (`sessions.txt`) and recorded nothing. `run.sh` now checks before each suite, and the three suites
  ran under this session's own reservation, released at the end.
- **Memory.** Before the cap on step size and the slice buffers allocated on the caller, MQ10 /
  GF(32003) at 16 workers peaked at 37–43 MB against the base's 29–30 MB. The cause was scratch freed
  in the workers' malloc arenas, which the caller's later allocations cannot reuse. Those
  measurements were exploratory and are not Gate S cells.

Build, run, summarize:

```sh
scratch=/buildcache/cargo-target/zeebra-940
for arm in head:592653ee base:ce67df76; do
  name=${arm%%:*}; commit=${arm#*:}
  mkdir -p $scratch/$name/src && git archive $commit | tar -x -C $scratch/$name/src
  (cd $scratch/$name/src && CARGO_TARGET_DIR=$scratch/$name/target RUSTC_WRAPPER="" \
     TMPDIR=$scratch/tmp cargo build --release --locked --features research-sigf4 \
     --example sig_f4_study --example m29_cost_model)
  mkdir -p $scratch/bin/$name && cp $scratch/$name/target/release/examples/{sig_f4_study,m29_cost_model} $scratch/bin/$name/
done
BINS=$scratch/bin setsid -w research/m32-gate-s/run.sh OUT gate mq10 small curve
python3 research/m32-gate-s/summarize.py research/m32-gate-s > research/m32-gate-s/tables.md
```
