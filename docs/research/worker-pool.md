# Persistent workers: dispatch is cheaper, small border batches still bind (#592)

**Measured at:** runner `6360904ab06f9ed773a530da3314ecfaef3d5837`; Rust instrument/source
`81aaa1be098e67ed3d4ede23123404f5668fa54a`, based on main `c5f7ecdb`. Later changes harden
supervision/storage only. All accepted arms use executable SHA-256
`15d210a48755f1a6be1c327ac7e2e6eb3aa231d10dd790d305958fe3ac64b698`.
No timing below pools the interrupted first campaign or the historical #167 cohort.

## Decision

**Accept the dispatch premise; defer production runtime/FGLM integration.** A safe persistent
pool materially lowers this task pipeline's warm dispatch cost. It does not make dispatch
constant or nanosecond-sized, and it does not make every default border batch worth threading.
The minimal pool is research code in an example; Rayon remains a dev dependency. Solver defaults,
conversion field bounds, arithmetic and production resource budgets are unchanged.

The next use is #728's bounded F4 prototype, where useful residual work must independently pay
for dispatch, retries and scratch. Nothing here measures F4 parallelism, removes coefficient
work or proves a larger solvable instance. #269 still owns work removal; #50/#51/#52 and #167
remain closed with their original scoped-thread evidence.

## Protocol, identity and reproducibility

Machine: actual AMD Ryzen Threadripper PRO 5995WX, 64 physical cores/128 hardware threads,
64 distinct core IDs on one socket and one reported NUMA node. The runner uses CPUs 0–63 before
SMT siblings 64–127, without per-worker binding beyond each process's selected mask. Default
NUMA/first-touch policy is not tuned or credited with a causal effect. Full `lscpu`, kernel,
source blobs, patch hashes and Cargo fingerprint are in
[provenance.json](../../research/worker-pool/provenance.json).

Rust 1.99.1, release, fat LTO, one codegen unit, x86-64-v3, no `RUSTFLAGS` override,
`RUSTC_WRAPPER=''`, inherited `-C link-arg=-fuse-ld=mold` (recorded in the Cargo fingerprint),
private `/buildcache/cargo-target/zeebra-592`. All border fixtures use
`Zp2147483647` (u64 Montgomery), grevlex source bases. Names follow
`examples/fglm_parallel.rs`: e.g. `katsura-7` is `katsura::<7,F>()`; do not substitute an
external corpus alias with a different variable-count convention. Planted points are `2*i+3`.
Full input/source polynomial text and sorted-text SHA-256 identities are retained, not just paths.
These text hashes are not the competitive corpus's canonical-system digest format.

Five interleaved fresh processes per cell, rotating backend order, workers 1/2/4/8/16/32/64,
with 128 as an SMT diagnostic. Each dispatch process records construction, first dispatch and 32
warm samples. Each border process first computes/checks a scalar reference, then cold and warm
owned-task passes; the second pass is primary. The existing scalar reference is an earlier
first-pass correctness control, **not a matched warm performance baseline**. Warm scoped p=1
uses the same owned-task/closure/result pipeline inline and is the matched sequential control.
All speedups below use the same backend's warm p=1, with the inline control shown separately.

The [predeclared protocol](../../research/worker-pool/README.md) fixes the gates. All 2,280
accepted attempts complete: 360 dispatch attempts and 1,920 border attempts, 456 distinct cells.
Every border digest agrees with the existing scalar entry point, every synthetic checksum and
result order is checked, and source/remainder identities agree across worker counts. Exact
coefficient and scalar-normal-form tests cover the arithmetic separately, including both prime
widths, GF(2) and GF(2^8). No external cross-engine timing or new full-conversion verification
claim is made.

The successful [lock window](../../research/worker-pool/benchlock.log) is 2026-11-13
00:30:40–00:31:18 America/New_York, `status=0 end=exited`, after 205s queued behind another
study. Start load 1.48, end 2.87; maximum per-attempt 1-minute load 2.87. The runner refused active
compilers at startup, and no compilers were observed in the surrounding checks. No local
builds/tests ran during this window. Every child has a 60s/2GiB process-tree guard and the parent
a 900s watchdog; no accepted attempt hits either. Samples include process wall, CPU time,
observed process RSS, stage times, clear counts, jobs and capacities. Physical bandwidth,
cache misses and per-stage CPU time were not measured; no bandwidth diagnosis follows.

[Raw cohort](../../research/worker-pool/results.json.gz),
[validated complete table](../../research/worker-pool/summary.csv),
[structured summary](../../research/worker-pool/summary.json) and
[reconstruction instructions](../../research/worker-pool/README.md) retain the result.
Publication recompresses gzip losslessly; provenance binds decoded bytes as well as the archive.

## Dispatch pipeline: useful reduction, not a constant-time wakeup

Microseconds; each entry is the median of five process medians of 32 warm samples. Scoped p=1
runs inline. Each submitted task has an owned job/result and one scratch-cell write. Thus this
is the measured dispatch/ownership/synchronization pipeline, not a bare OS primitive.

| Workers | Scoped warm | Parked warm | Rayon warm | Parked first dispatch |
|---:|---:|---:|---:|---:|
| 1 | 0.04 | 7.01 | 14.06 | 47.01 |
| 2 | 66.22 | 8.34 | 6.41 | 53.14 |
| 4 | 75.11 | 18.68 | 6.80 | 53.12 |
| 8 | 130.38 | 16.89 | 9.83 | 93.73 |
| 16 | 302.64 | 27.44 | 16.21 | 80.21 |
| 32 | 795.82 | 53.49 | 27.53 | 91.42 |
| 64 | 2073.63 | 103.46 | 64.70 | 171.22 |
| 128 | 4634.13 | 201.50 | 110.42 | 301.44 |

The static pool clears the predeclared 4x warm-dispatch gate at 2/8/32 workers by about
7.9x/7.7x/14.9x. At 64 workers it is 20.0x below scoped dispatch, but still 103µs, and at 128
it is 202µs. The issue body's constant/nanosecond expectation is rejected for this implementation.
Constructor cost and first-dispatch cost are separate in the summary; a short-lived pool is not
free. The 256/65,536-total-update controls are retained without treating synthetic scaling as a
finite-field solver gain.

Rayon's lower empty-task latency is not proof of a cheaper all-worker barrier. At 2 workers all
observed empty batches execute on just one Rayon worker; at 32 the observed active-worker range
is 9–23 and at 64 it is 12–43. The static pool visits every requested worker. Runtime, scheduling,
scratch reuse and activation differ, so these are alternative pipelines rather than an isolated
work-stealing optimization.

## Border results and the batch-size trap

Milliseconds, warm whole-border regions. Best observed median through 64 workers is exploratory
selection over the declared grid, not a validated adaptive policy. Ranges and all alternatives
remain in the complete table. `inline` is the warm scoped p=1 control at the same batch size.

| Fixture | Batch | Inline | Best parked (workers) | Best Rayon (workers) |
|---|---|---:|---:|---:|
| katsura-5 | 64 | 0.057 | 0.073 (1) | 0.072 (1) |
| katsura-5 | all | 0.057 | 0.073 (1) | 0.071 (1) |
| katsura-6 | 64 | 0.207 | 0.240 (1) | 0.237 (2) |
| katsura-6 | all | 0.196 | 0.209 (2) | 0.215 (4) |
| katsura-7 | 64 | 1.138 | 1.081 (4) | 1.004 (8) |
| katsura-7 | all | 1.087 | 0.770 (8) | 0.708 (8) |
| cyclic-5 | 64 | 0.215 | 0.266 (1) | 0.271 (4) |
| cyclic-5 | all | 0.220 | 0.239 (2) | 0.220 (4) |
| cyclic-6 | 64 | 0.879 | 0.863 (4) | 0.892 (2) |
| cyclic-6 | all | 0.894 | 0.653 (8) | 0.705 (4) |
| planted-6 | 64 | 0.159 | 0.192 (1) | 0.212 (1) |
| planted-6 | all | 0.164 | 0.184 (8) | 0.180 (2) |
| planted-8 | 64 | 0.936 | 1.093 (1) | 1.167 (2) |
| planted-8 | all | 1.324 | 0.992 (8) | 1.011 (16) |
| planted-10 | 64 | 5.383 | 6.211 (1) | 6.787 (2) |
| planted-10 | all | 21.394 | 6.628 (64) | 6.340 (32) |

- **A narrow default-batch opportunity exists on Katsura-7:** Rayon 8 takes 1.004ms
  [0.947,1.102] versus its own p=1 at 1.233ms [1.219,1.247], 1.23x speedup/15.3% efficiency.
  The matched inline p=1 is 1.138ms [1.134,1.143]; the median difference is 11.7%, with
  nonoverlapping ranges. This clears the declared whole-border time gate for this diagnostic,
  not a complete-conversion integration gate. Parked 4's median 1.081ms has a broad
  [1.011,1.276] range overlapping p=1; do not promote its best-median selection to a robust win.
- **Unbounded dense-enough borders expose more useful work:** Katsura-7 Rayon 8 is 0.708ms
  versus 0.983ms at its own p=1; Cyclic-6 parked 8 is 0.653ms versus 0.856ms. These remain border
  measurements; Cyclic-6 parked ranges overlap, so its selected median is directional evidence,
  not a resolved adoption verdict. Different batch sizes change closure work and must be assessed together.
- **The tempting larger parallel result does not beat the default:** planted-10 unbounded
  Rayon 32 takes 6.340ms [6.065,6.662], 3.39x over its own 21.506ms p=1, but only 10.6%
  efficiency. The bounded 64 inline border is 5.383ms [5.276,5.593], faster than that whole
  unbounded border. At the default batch size the best parked median uses one worker, 6.211ms;
  scoped 32 is 74.367ms and parked 32 is 12.160ms. Cheaper dispatch removes much spawning waste
  without making threading profitable there.

At the frozen Katsura-7/batch 64 inline baseline the reduction phase is 0.401ms of 1.138ms:
removing that phase entirely bounds this **whole-border** speedup near 1.54x. This is not an
Amdahl bound for FGLM or F4. The full conversion's remaining walk/certificate cost is outside
this instrument. Intermediate cache state, owned task setup, capacity tracking and scratch
allocation policy also differ; the early scalar reference timings must not be used to claim
that owned jobs improve the old sequential algorithm.

All backends use the same fixed immutable reducers and per-target arithmetic. They do not
reduce targets against one another. Grouping increases buffer clears and loses the previous
`dirty_from` carry at group boundaries; recorded `zeroed_cells` exposes that work. Coefficient
products and allocator-call counts are not newly instrumented in this experiment, so no
coefficient-work or allocation-count saving is claimed. Static scheduling versus Rayon's work
stealing is not independently ablated from runtime/scratch costs. Cold/warm passes retain that
uncertainty rather than pretending these are identical memory-access schedules.

## Memory, failure and runtime ownership

Every attempt records full-process wall and CPU time; those boundaries include source F4,
reference checking, runtime construction, both border passes and output, and are not conversion
speedups. Stage/whole-border scaling uses the narrower matched region. Process CPU time must
not be divided by the hot region's wall to infer core use. Observed process-tree and final
self-reported high waters cover setup too; maxima are sampled measurements, not byte-exact
allocator bounds. Largest observed accepted process RSS is 16.73MiB, below the 2GiB guard.

For planted-10/unbounded, parked scratch retention is 3MiB at 64 workers and 6MiB at 128.
Whole-border medians 6.628ms and 6.575ms have overlapping ranges; this does not establish an SMT
benefit. At fixed 64, Rayon's union of workers retains about 245KiB at 128 versus 120KiB for
static mailboxes. Active-batch scratch allowance and retained capacity are different quantities.
A production runtime would need an explicit retention/nesting/oversubscription policy; the
experimental 64MiB active-cell allowance is not a process memory guarantee.

The custom pool has no unsafe code. Owned jobs, immutable `Arc` closure sharing, private scratch
and ordered result collection avoid borrowed-lifetime extension. Mailboxes have capacity one;
batch count is refused before submission. Cancellation is cooperative between jobs, task panics
cancel/drain the batch and reset scratch, and dropping the pool joins workers. Tests cover
failure recovery and subsequent reuse. A mutable submitting owner prevents recursive dispatch
through the same pool; independently constructed/nested pools remain the caller's responsibility.
No global pool, core binding, work stealing or production cancellation API is introduced.

The 8-million-cell research allowance is checked before handing a closure to workers. Existing
closure limits still fail before dispatch. The scope of production entry/byte budgets is not
expanded or weakened. Tests verify dirty scratch, shrinking buffers, missing results and exact
normal forms across fields. No partially computed result is accepted after failure.

## Interrupted campaign and durable evidence

The first runner (`81aaa1be`) repeatedly recompressed its entire growing checkpoint. After 366s
it was deliberately interrupted during compression to fix that quadratic bookkeeping, with
`status=130 end=signalled-child(INT)` in the lock log. The available
[checkpoint bytes](../../research/worker-pool/interrupted-checkpoint.gz) are corrupt gzip and
are **not a readable or accepted cohort**; the [complete available log](../../research/worker-pool/interrupted-checkpoint.log)
is retained. No attempt from it contributes to a table or speedup; unrecoverable output is not
represented as verified retained evidence. This disclosed failed run is not an optimization result.

The accepted restart uses the unchanged Rust executable with an append-only flushed journal and
one compressed cohort at completion/failure. A Red–Green supervisor regression additionally
requires interrupting a live child to kill/reap its owned process group before returning an
interrupted attempt. The accepted 2280-attempt cohort is complete and independently revalidated
from raw records; this is a single declared bounded restart, not pooling selected historical runs.

## Consequences

- #592's principal premise is now measured. Use the explicit pipeline floor and constructor/scratch
  costs to size #728 work, not the old 21µs/worker slope or an assumed nanosecond wakeup.
- Preserve #50's zero-work structured-prefix rejection; dispatch alone cannot create useful work.
  #51/#52's tiny phases are not implementation priorities without a new workload-level bound.
- Keep #167's scoped-thread verdict. Its extension has a narrow pool-based border opportunity on
  Katsura-7 and broad small-batch negatives, not a general FGLM default change. Full conversion
  and a matched warm original-entry control are prerequisites to any future integration claim.
- Do not select 64/128 workers from core count alone. Measure usable work and skew in #728,
  coordinate #269's reduced-row necessity proof, and test the combined algorithm/runtime only
  after isolated work and correctness gates. This study does not establish F4 multicore speedup.
