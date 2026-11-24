# #945: dense small-prime lane kernel, gate data

**Measured at:** `ef985d5e` (deciding session 2 and void session 1: `sig_f4_study --features
research-sigf4` SHA-256 `cd04d5d5…`, `lane_matrix_gate` `628b6537…`), `26dae9ed` (matrix dev pair),
`4b064a84` (complete-task dev pair). Every
binary was built in release with the repository's `x86-64-v3` floor, `RUSTC_WRAPPER=""`, and a
private target dir on `/buildcache`. **Host:** Threadripper PRO 5995WX.

**Status: decided 2026-11-23 (session 2, `records-2.jsonl`, `tables.md`).** The speed gates pass
by a wide margin. **The memory gate fails**, and so does the strict upper bound on one sparse
control. Under M34 §9.3 a failed gate stops the prototype. One corrective iteration (memory) is
proposed below.

Session 2 ran on CCDs 1–2 (CPUs 8–23), in a reservation `run.sh` took and released itself, on a
quiet machine. Each row's arms ran from the same frozen binary, interleaved in alternating order.
Paired ratios are lane ÷ field: the median of per-pair ratios and a 95% bootstrap CI
(`tools/bench_stats.paired_ratio`). Rows under 1 s use the solve call's own clock, not process
wall.

| Gate | Result | Bar | Verdict |
|---|---|---|---|
| Matrix: n = 20 b3 serial forward | 753.3 s → 144.1 s; **0.192** [0.189, 0.192], n = 3 (5.2×); echelon digests identical | ≥ 2× | **PASS** |
| Complete: gf31 dense n = 18, 16 w | 5.83 s (`entry` 5.84 s) → 1.95 s; **0.334** [0.333, 0.336], n = 9 | upper ≤ 0.87 | **PASS** |
| Complete: gf31 dense n = 20, 16 w, `--live-gib 8` | 48.43 s (`entry` 48.50 s) → 17.41 s; **0.359** [0.357, 0.363], n = 5 | upper ≤ 0.87 | **PASS** |
| Complete: gf32003 dense n = 18, 16 w | 5.92 s → 2.07 s; **0.350** [0.348, 0.359], n = 5 | upper ≤ 0.87 | **PASS** |
| Bases | identical on every pair; n = 18 and n = 20 are grobx's digests | same basis | **PASS** |
| Peak live bytes (`claim_peak_live_bytes`), target rows | 1.23 / 1.23 / 1.22 | ≤ 1.15 | **FAIL** |
| Process peak RSS, target rows | 1.24 / 1.09 / **1.27** (gf32003 n = 18) | ≤ 1.25 | **FAIL** (one row) |
| Sparse controls, 16 w | cyclic-6 and mq-random-10 at both fields: upper ≤ 1.033. katsura-8 (6 ms solves): 1.031 [1.003, 1.067] and 1.025 [0.997, 1.059] | each loses ≤ 5% | medians pass; katsura-8 upper bounds exceed 1.05 |
| Wide controls | no lane above p = 46337 | identical route | **PASS** by construction |

The matrix ratio in a quiet reservation (0.19) is much better than the dev pair's (0.35). The dev
pair ran its two arms concurrently next to other sessions, and the lane arm, being bandwidth-bound,
lost more to that.

### Why memory fails, and the corrective iteration

In lane mode every pivot is held twice, as its field-form `Vec<(u32, F)>` and as its lane form:
- the reducer block and every new element, for the length of the batch;
- the lane copy is charged on top of the field rows (`lane_bytes` in `engine.rs` and `claim.rs`).

That accounts for the 1.22–1.23× in live bytes. **Hypothesis:** keep only the lane form while a
batch reduces. Drop the reducer block's field rows once they are converted, and materialize each
element's field row only at settlement, as `LaneKernel` already does at matrix level, where peak RSS
is 0.85×. Live bytes should then fall below 1.0×, since a dense `u16` cell (2 B) at span density
≥ 25% costs at most 8 B per nonzero against a field entry's 8 B. The speed should not move.
Budget: one corrective session, under §9.3's one-iteration, ≤ 2-session rule.

## What is measured

| Gate (M34 §9.3) | Arm A | Arm B | Bar |
|---|---|---|---|
| Matrix level | accumulator (`Backend::Adaptive`, shipped) | lane, conversions charged | n = 20 b3 forward ≥ 2× serially; identical echelon digest |
| Complete task | `sigf4 --claim --workers 16` (the `entry` mirror) | the same with `--lane` | paired upper ≤ 0.87, same basis |
| Memory | | | process peak RSS ≤ 1.25× |
| Sparse controls | katsura-8, cyclic-6, mq-random-10 at GF(31) and GF(32003), 16 w | `--lane` | same basis, upper ≤ 1.05 |
| Wide controls | — | — | The lane does not exist above p = 46337 (`Lane::new` returns `None`). The route is identical by construction; tested in `test_only_small_primes_get_a_lane` and `test_small_prime_lane_is_ignored_on_a_wide_field` |

## Development reads (unreserved cores, one pair each; decide nothing)

| Row | Arm A | Arm B | B ÷ A | Digest | Peak RSS B ÷ A |
|---|---|---|---|---|---|
| n = 18 b3 forward, serial, 1 CPU | 322.25 s | 69.37 s | 0.215 | `ff3a86d2…` both | 0.96 |
| n = 20 b3 forward, serial, 1 CPU (`dev-matrix-n20.jsonl`) | 887.94 s | 310.35 s | 0.350 | `a1404183…` both | 0.85 |
| gf31 dense n = 18, 16 w (call wall) | 6.30 s | 2.31 s | 0.367 | `dd5e5b1a…` both (grobx's) | — |

The two n = 20 arms ran concurrently, on CPUs 40 and 56 (separate CCDs). Row operations were equal
(215,411,910), and so was rank (24261).

Profile of the lane arm at n = 18 (`perf`, one run):
- 82% of samples are in the kernel;
- of those, about 56% are in the sparse-pivot scatter (the reducer rows, about 231 entries each), and
  about 35% in the vectorized dense `u16 × u32` axpy.

The scatter is now the kernel's ceiling.

## Void session 1 (`records-void-1.jsonl`)

`run.sh` rode another agent's CCD reservation through `bench-reserve.sh run`. That reservation was
released after five attempts: three `entry` n = 18 (5.85 s median), one `entry` n = 20 (48.81 s) and
one field-arm n = 18 (5.89 s). Every later attempt was refused at once (rc 2, no output), so 151 of
156 records are refusals, and no lane attempt ran in the session. The five clean records tie the
`sigf4 --claim` mirror to `entry` (5.89 s vs 5.85 s), and nothing else. `run.sh` now reserves when
nobody has, releases on exit, keeps a failed attempt's log, and stops if the reservation is gone.

## Reproduce

```sh
export CARGO_TARGET_DIR=/buildcache/cargo-target/zeebra-945 RUSTC_WRAPPER="" TMPDIR=$CARGO_TARGET_DIR/tmp
cargo build --release --features research-sigf4 --example sig_f4_study --example lane_matrix_gate
cp $CARGO_TARGET_DIR/release/examples/{sig_f4_study,lane_matrix_gate} $RUNS/   # freeze
setsid nohup research/945-lane-kernel/run.sh $RUNS/records.jsonl $RUNS/sig_f4_study \
  $RUNS/lane_matrix_gate /buildcache/cargo-target/zeebra-1033/captures > $RUNS/runner.log 2>&1 < /dev/null &
research/945-lane-kernel/summarize.py $RUNS/records.jsonl
```

The captures are #1033's, pinned by SHA-256 in `research/1033-dense-rebaseline/captures.json`.
