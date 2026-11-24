# #945: dense small-prime lane kernel, gate data

**Measured at:** `26dae9ed` (matrix dev pair, `lane_matrix_gate`), `4b064a84` (complete-task dev
pair, `sig_f4_study --features research-sigf4`), `ef985d5e` (void session 1: both binaries). Every
binary was built in release with the repository's `x86-64-v3` floor, `RUSTC_WRAPPER=""`, and a
private target dir on `/buildcache`. **Host:** Threadripper PRO 5995WX.

**Status: the gate is undecided.** The development reads below clear every bar by a wide margin,
but they ran on unreserved cores beside other sessions. They decide nothing. The deciding session
(session 1) went void before any lane attempt ran (see *Void session 1*). A deciding re-run is
pending. It needs a quiet machine and one CCD reservation of about 75 minutes.

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
