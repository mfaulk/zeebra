# The concurrent forward kernel at one CPU: the same arithmetic as the serial kernel (#894)

**Measured at:** `63696c08` plus `examples/forward_kernel_study.rs` from this branch, which adds no
library code. Neither forward kernel has changed since `b1d8e36a`, the build #894 measured:
`git diff b1d8e36a 63696c08` is empty for `src/linalg/dense/accumulator.rs`,
`src/linalg/echelon.rs`, `src/linalg/pivots.rs` and `src/grobner/f4/structured.rs`, and
`src/linalg/concurrent.rs` changed only in its two thread-spawn calls (#1042). The machine was an Apple M4 Pro
(14 cores, macOS), **unpinned**, release profile (fat LTO), with a load average of 7–23 from
other sessions, on 2026-11-22. That macOS host has no `taskset` and no `/proc`, so the timings
below are not the pinned measurement #894 took. The counts are deterministic and do not depend on
the host. Raw output is in
[`research/forward-kernel-one-cpu/`](../../research/forward-kernel-one-cpu/).

## Question

#894 found that `m29_cost_model --target katsura11-m31 --workers 16` under `taskset -c <one cpu>`
spent 5.6–5.7 s in forward elimination with sixteen time-sliced workers, and 6.3–6.4 s with the
#886 clamp, which runs the serial kernel. The whole F4 call was 0.906×. Eco-12 and MQ10 showed no
such gap. The issue asked what the concurrent kernel does differently, and whether `Auto` at one
worker should run it or the serial kernel should adopt the difference.

## Method

`examples/forward_kernel_study.rs` runs one F4 call with the forward pass serial and receives every
batch matrix before elimination (`BatchObserver::matrix`). On a copy of each matrix it runs:

1. the serial kernel (`eliminate_to(ReducersFirstBlock, Echelon, Adaptive)`);
2. the concurrent kernel at one worker (`concurrent::reduce`, `workers = 1`, dynamic schedule);
3. the concurrent kernel at 14 real workers;
4. a deterministic model of 16 workers time-sliced on one CPU (`--slices`). The concurrent kernel's
   dynamic schedule runs round-robin, and each worker spends up to `S` coefficient products per
   turn. A preempted row is overtaken by every row the other fifteen finish meanwhile. That is
   the reordering threads on one CPU see, and it is far larger than the reordering 14 real cores
   produce. With one worker, or a slice that no row exhausts, the model is the serial kernel. The
   example's tests pin that equivalence and check that preemption keeps the rank.

It times arms 1 and 2 as the best of seven runs in alternating order, and counts row operations and
coefficient products for every arm.

```
cargo build --release --example forward_kernel_study
target/release/examples/forward_kernel_study --problem=katsura-11 --modulus=2147483647 \
  --workers=14 --reps=7
target/release/examples/forward_kernel_study --problem=katsura-11 --modulus=2147483647 \
  --workers=14 --reps=1 --sim-workers=16 --slices=1e3,1e4,1e5,1e6,1e7,1e8,1e12
```

## 1. At one worker the two kernels do identical arithmetic

The two kernels run the same algorithm. Each takes the lower rows in index order, subtracts the
pivot of the current leading column until the lead has none, then normalizes and claims that
column. In both, the tail right of the new lead is left unreduced. The concurrent kernel reads
pivots from `known[...]` or a `OnceLock` slot instead of a `PivotIndex`, and frees the input rows
at the end instead of one at a time. Nothing else differs.

The output confirms it. On all 11 Katsura-11 batches, at both moduli, the one-worker concurrent
result equals the serial result entry for entry. Each arm performs 21,745,358 row operations and
4,376,252,738 coefficient products at p = 2³¹−1, and 4,375,969,390 products at 32003.

| p | serial forward, ms | concurrent, 1 worker, ms | concurrent / serial |
|---|---:|---:|---:|
| 2³¹−1 | 5,065.4 | 5,089.8 | 1.005× |
| 32003 | 4,848.7 | 4,890.1 | 1.009× |

These are sums of per-batch best-of-7 times. The six batches above 50 ms range from 0.965× to
1.059× each, with no consistent sign at either modulus. On this host there is no gap.

## 2. Reordering changes the work by less than 0.5%

If threads changed which row claims each pivot, the work could change. It barely does:

| arm (p = 2³¹−1) | coefficient products | vs. serial |
|---|---:|---:|
| serial kernel | 4,376,252,738 | 1 |
| 14 real workers (617 lost publications) | 4,371,638,141 | 0.9989 |
| 16 time-sliced, slice 10³ products | 4,355,936,557 | 0.9954 |
| slice 10⁴ | 4,365,043,611 | 0.9974 |
| slice 10⁵ | 4,360,268,305 | 0.9963 |
| slice 10⁶ | 4,374,375,493 | 0.9996 |
| slice 10⁷ | 4,378,327,474 | 1.0005 |
| slice 10⁸, 10¹² | 4,376,252,738 | 1 |

The serial kernel performs about one product per nanosecond here, so a 0.75–3 ms Linux timeslice is
about 10⁶–3·10⁶ products. In that range the model's work is within 0.05% of serial. In the separate
14-worker timing runs, the ratio was 0.9974 at 2³¹−1 and 0.9989 at 32003.

## Answers

- **What the concurrent kernel does differently:** nothing that changes the arithmetic. At one
  worker it is the serial kernel. Time-sliced or truly parallel, its pivot choices change the
  coefficient products by at most 0.5%, and by 0.05% at realistic timeslices. A 10% forward-stage
  gap on Katsura-11 therefore cannot be algorithmic, and the hypothesis #894 stated ("the concurrent
  kernel's *algorithm* is cheaper") is refuted.
- **Whether `Auto` at one worker should run the concurrent kernel:** not on this evidence. There is
  no algorithm for the serial kernel to adopt, and on this host the concurrent kernel at one worker
  is 0.5–0.9% slower, which is within noise. The #886 clamp stands.

## What is left for the bench host

The gap #894 timed was not reproduced here, and the arithmetic cannot explain it. If it is real, it
is a property of the 5995WX/Linux execution. Candidates are allocator behaviour, since the serial
kernel frees and allocates one row per row while the concurrent kernel frees the inputs in one
batch at the end, and the other differences between the two `m29_cost_model` builds #894 compared.
The 16-worker arm also ran the symbolic team and candidate finishing on workers. One pinned run
settles the kernel-level question:

```
taskset -c 8 target/release/examples/forward_kernel_study --problem=katsura-11 \
  --modulus=2147483647 --workers=16 --reps=7
```

If `concurrent_ns / serial_ns` comes out near 0.9 there, the effect is in execution, not
arithmetic, and the next step is to profile allocations in the serial kernel. If it comes out near
1, the gap in #894 belonged to the rest of the F4 call, and nothing in the forward kernels needs to
change.
