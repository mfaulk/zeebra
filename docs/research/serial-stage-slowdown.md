# Serial stages in the 16-worker arm, and the price of symbolic preprocessing (#827)

**Measured at:** `de02e8d2` (stage arms, stock `mq10_profile`) and `8912ce17` (the research-gated
replay and the `--symbolic` policies; the library's default path is unchanged from `de02e8d2`).
AMD Threadripper PRO 5995WX, release, `amd-pstate-epp` with the `performance` governor, boost on.
Process pinned with `taskset -c 2-17` unless stated otherwise. These are exploratory paired runs
made **outside benchlock**, at load 3.5–6.4 from other sessions. Every comparison below is between
arms run back to back in one session. Read the ratios, not the absolute values, and do not pool
them with the #822 cohort. Each row is one run. Repeats are given where they were taken, and they
agreed within 3%.

## Finding

The serial stages slow down in the 16-worker arm for three separate reasons:

1. **Core clock (all stages).** After a burst of 16 busy cores, this part keeps every core at its
   all-core boost, about 3.99 GHz instead of 4.54 GHz, for **200–500 ms** after the burst ends. That
   holds even when the burst lasted only 50 ms. Katsura-11's batches are much shorter than that
   window, so every serial stage in the 16-worker arm runs at the reduced clock. On its own this
   accounts for the 10–14% that symbolic preprocessing, sort and backward lose.
2. **Cross-CCD placement (MQ10 symbolic and scatter).** Rows written by workers on another CCD's L3
   are read back from there. With the worker count fixed at 8 (so the same clock), keeping the
   workers on one CCD instead of two takes MQ10 symbolic from 96.6 to 89.3 ms and scatter from 14.5
   to 11.5 ms.
3. **glibc malloc arenas (Katsura-11 construction).** Katsura-11's construction excess is all in
   the scatter (44 → 70 ms). `MALLOC_ARENA_MAX=1` brings it to 51 ms, which is the clock factor
   alone. It also costs forward elimination 30–180 ms of lock contention, so it is not a fix.

**Pricing symbolic preprocessing on the Katsura-11 basis:**

- **Reduced:** removing duplicate pair multiples (#742's `dedup`) is the cheaper win. It takes the
  16-worker F4 call from 1645 to 1485 ms (**−10%**) and returns the identical 537-element reduced
  basis. Most of the gain is in forward elimination (−115 ms); symbolic preprocessing itself drops
  only 7%. Sorting the input generators (`order`) changes nothing on Katsura-11.
- **Parallel:** a level-synchronous closure that returns exactly the serial result is
  **1.38x faster at 16 workers** (482 → 348 ms replayed) and 1.55x at 32. That saves about 135 ms of
  the 1640 ms call (8%). Its serial in-order commit is about 325 ms, so it cannot get much past 1.4x
  unless interning is also parallelized.

## 1. Reproduction

The arms are `mq10_profile --stages --forward-workers=1|16` on 2^31−1, in ms:

| Cell | arm | symbolic | construction | of which scatter | sort | forward | backward |
|---|---|---:|---:|---:|---:|---:|---:|
| Katsura-11 | serial | 436–455 | 56–63 | 44–45 | 10.7 | 7388–7922 | 255–276 |
| Katsura-11 | 16 workers | 484–493 | 82–90 | 70–71 | 11.1–11.3 | 525–543 | 283–294 |
| MQ10 | serial | 83–85 | 16.5–17.9 | 9.3–10.8 | 6.9–7.0 | 821–829 | 37.7–39.6 |
| MQ10 | 16 workers | 95.9–96.5 | 21.9–22.2 | 14.0–14.2 | 7.6 | 73.7–75.6 | 41.5–42.8 |

These are the same shifts #822 reported: symbolic +12–14%, construction +30–50%.

## 2. Core clock

**Sampling the main thread's core.** A sampler read the main thread's CPU from
`/proc/<pid>/task/<pid>/stat` every 2 ms. When the main thread was running and was the only task
in the process (a serial stage), the sampler read that CPU's `scaling_cur_freq`. Two runs per arm on
Katsura-11:

| arm | single-threaded samples | median MHz | mean MHz |
|---|---:|---:|---:|
| serial | 4012–4064 | 4538 | 4358–4403 |
| 16 workers | 598 | 3992 | 4066–4067 |

The ratio 4538 / 3992 = 1.137 matches the symbolic slowdown.

**C-states.** The idle worker cores are not stuck in a shallow state. In a 16-worker run, CPUs 3–17
spent 28.0 s in C2 and 1 ms in C1.

**Recovery, from timed work rather than sysfs.** A fixed integer loop on CPU 2 was timed in ~0.73 ms
chunks while 15 spinners ran on CPUs 3–17, and again after they were killed. Chunk time is shown
relative to the median before the burst:

| burst | during | 0–200 ms after | 200–500 ms after | 500+ ms after |
|---:|---:|---:|---:|---:|
| 1000 ms | 1.109x | 1.110–1.114x | 0.982x | 0.994–1.000x |
| 50 ms | 1.115x | 1.113–1.120x | 0.984x | 0.986–1.010x |

The sysfs readout gives the same window: 3992 MHz until 200 ms after the burst and 4538 MHz from
500 ms on.

**Co-runner control.** The serial arm was run on CPU 2 with 15 integer spinners on CPUs 3–17. The
spinners use almost no cache or memory bandwidth. Symbolic went from 431–449 to 481–483 ms, forward
from 7380–7532 to 8132–8295 ms, and backward from 260–273 to 281–290 ms, each about 10%. The clock
on its own reproduces the size of the effect.

## 3. Cross-CCD placement

CPUs 2–17 cover three L3 domains: 2–7, 8–15 and 16–17. On MQ10 at 2^31−1, `--forward-workers=8`
was run on one CCD (`8-15`) and on two (`4-7,12-15`). Three repeats of each:

| arm | symbolic | sort | scatter | forward |
|---|---:|---:|---:|---:|
| serial, `8-15` | 82.0–83.9 | 6.7–7.0 | 8.8–10.2 | 818–838 |
| 8 workers, one CCD | 88.9–89.6 | 7.6 | 11.0–11.9 | 124.6–125.0 |
| 8 workers, two CCDs | 95.9–97.7 | 7.6–7.7 | 14.1–14.7 | 126.6–127.2 |

Sort reads only the batch's own column list, and it is equal in both 8-worker arms, so the clock
is the same in both. The remaining 7 ms of symbolic and 3 ms of scatter come from reading data
that workers wrote on the other CCD. Any 16-worker run on this part spans at least two CCDs.

## 4. Allocator arenas

Katsura-11, 16 workers, two repeats of each:

| arm | symbolic | construction | scatter | forward | minor faults |
|---|---:|---:|---:|---:|---:|
| serial | 436–441 | 55.7–57.0 | 43.5–44.9 | 7388–7391 | 36.1 k |
| 16 workers | 484–489 | 82.4–83.8 | 69.6–70.7 | 525–526 | 42.5–43.1 k |
| 16, `MALLOC_ARENA_MAX=1` | 489–494 | 64.6 | 51.3–51.4 | 555–708 | 35.5–35.6 k |
| 16, no trim, no mmap | 482–484 | 82.3 | 69.0–69.1 | 526 | 36.8–38.2 k |

The "no trim, no mmap" arm sets `trim_threshold` and `mmap_threshold` to 4 GiB through
`GLIBC_TUNABLES`.

- **Katsura-11:** a single arena removes the scatter excess beyond the clock. Disabling trimming
  does not, and system time stays at 0.06–0.11 s, so the cost is not page faults or `madvise`.
- **MQ10:** a single arena does not help (scatter 14.0 → 13.1–13.3 ms against 9.3–10.8 serial).
  MQ10's residue is the cross-CCD placement in §3.
- **Cost:** in that arm, workers contend on one arena and forward elimination loses 30–180 ms. The
  arena effect is real, but this setting is the wrong lever.

## 5. Price of reduced symbolic preprocessing

These runs use the live research policies from #742 (`mq10_profile --symbolic=…`, `research-work`),
on Katsura-11 at 2^31−1 with 16 forward workers and two repeats:

| policy | symbolic | construction | forward | backward | F4 total |
|---|---:|---:|---:|---:|---:|
| original | 489.6–490.1 | 87.4–89.0 | 569–578 | 262–263 | 1645–1647 |
| order (sorted input leads) | 491.1–492.8 | 80.6–82.2 | 569–571 | 263 | 1634–1641 |
| dedup (one copy per pair multiple) | 453.5–459.0 | 81.1–83.2 | 454 | 264–267 | 1489–1491 |
| both | 457.6–458.4 | 77.8–80.4 | 452–453 | 263 | 1478–1484 |

The `dedup` run returns the same reduced basis, string for string, as `original` (537 elements).
Deduplication is still not proved to preserve the result in general. Shipping it needs the
closure-equivalence argument that `symbolic.rs` makes for push-time deduplication, or a
corpus-wide differential.

## 6. Price of parallel symbolic preprocessing

`symbolic_preprocessing_level_parallel` (`research-work` only) runs the FIFO closure one
breadth-first level at a time. A level's monomials are distinct, so processing one cannot change
whether another is covered. Workers take contiguous chunks of the frozen level and do four things
for each monomial:

- the covered check;
- the divisor search;
- building the reducer multiple's terms;
- looking up each term's handle in the interner as it was before the level.

The caller then commits in frontier order. It interns only the terms that are new to the level and
pushes the rows. This reproduces the serial rows, row order, column order, term handles and every
counter. `test_level_parallel_symbolic_preprocessing_matches_the_serial_closure` checks this on
every traced batch of Katsura-6 and Cyclic-5 under all three orders, at 1, 2, 5 and 16 workers.

`examples/symbolic_parallel_price.rs` replays each live batch both ways, in alternating order,
inside the production F4 run. It asserts that the two results are equal before keeping either
time. The replays therefore run at the same clock and cache state as the live stage. Katsura-11 has
11 batches, and its replayed serial total (449–489 ms) matches the live stage (436–452 ms). A level
smaller than the dispatch threshold (default 256 monomials) runs on the calling thread.

| workers (threshold) | serial replay | level-parallel | ratio |
|---|---:|---:|---:|
| 1 (256) | 449–451 | 698–701 | 0.64x |
| 4 (256) | 469 | 497 | 0.94x |
| 8 (256) | 473 | 390 | 1.21x |
| 16 (4096) | 467–475 | 386–387 | 1.21–1.23x |
| 16 (256) | 482 | 348 | **1.38x** |
| 32 (256), CPUs 2–33 | 487–489 | 313–316 | 1.54–1.56x |
| MQ10, 16 (256) | 95 | 77 | 1.23x |

**What limits it.** The 1-worker row is the restructuring alone: it buffers terms and looks each
one up twice, which makes it 1.55x slower than the serial closure. If the 1-worker cost (700 ms) is
split into a parallel part *p* and a serial commit *s*, the 16- and 32-worker rows give
*s* ≈ 300–325 ms. The serial commit is therefore roughly two-thirds of today's serial stage, and the
ceiling stays close to 1.5x until the commit is cheaper, either through sharded interning or by
pre-hashing the new terms in the workers. At 16 workers this prototype would save about 135 ms of
Katsura-11's 1640 ms call (8%). On MQ10 it would save about 18 ms of a 275 ms F4 call (7%).

## Decision

- **No change to the default here.** The clock effect belongs to the hardware and is a fair cost of
  using 16 cores: Amdahl ceilings should keep using the stage times from the 16-worker arm, as #822
  does. The arena and cross-CCD effects add up to about 20 ms on Katsura-11 and 10 ms on MQ10.
  Neither has a lever that pays for itself yet.
- **Next for symbolic preprocessing:** the live `dedup` policy (−10% on the F4 call) is worth more
  than the parallel prototype (−8%) and uses no extra cores. It needs a correctness argument before
  it can ship. The two gains overlap only partly: dedup mostly removes forward work, while
  parallelism shortens the symbolic stage. Parallel symbolic is worth revisiting only together with
  parallel interning.
- **Benchmarking note:** a serial stage's absolute time on this machine depends on whether a
  multicore burst ended in the previous ~200–500 ms. Stage times taken from the 16-worker arm already
  include this. A "serial" figure measured just after a parallel phase in another process does too.

## Reproduction

The probe scripts (frequency sampler, recovery timer, C-state residency, and stage arms with fault
counts) are small and were run from a scratch directory. Their method is fully described in §§2–4.
The instruments in the tree are:

```bash
CARGO_TARGET_DIR=/buildcache/cargo-target/zeebra-827 RUSTC_WRAPPER="" \
  cargo build -j24 --release --features external-runners,research-work \
  --example mq10_profile --example symbolic_parallel_price
# stage arms
taskset -c 2-17 $CARGO_TARGET_DIR/release/examples/mq10_profile 2147483647 \
  --problem=katsura-11 --stages --forward-workers=16 [--symbolic=original|order|dedup|both]
# parallel price: PROBLEM MODULUS WORKERS [MIN_FRONTIER=256] [FORWARD_WORKERS=16]
taskset -c 2-17 $CARGO_TARGET_DIR/release/examples/symbolic_parallel_price katsura-11 2147483647 16
```
