# Adaptive parallel F4 forward elimination (#752)

**Measured at:** gate calibration from a binary built on the tree committed as `8ccea616`
(SHA-256 in `research/parallel-forward/calibration/binary.sha256`); design 1 at `46867c14`;
design 2 at `f45bcc47`. The adopting commit `394a9ca1` changes only the default value, docs
and tests, not the measured route. Threadripper PRO 5995WX, 64 physical cores, one logical CPU
per physical core (CPUs 2–65, no SMT); rustc 1.99.1, release, fat LTO, one codegen unit,
x86-64-v3, system allocator.

**Decision: adopted.** `F4Options::recommended` (the default) now uses
`ParallelForward::Auto { max_workers: 16 }`. The second declared design passed all five
predeclared gates. The first failed two of them and is recorded below.

## Route

`F4Options::parallel_forward` dispatches a batch's reducer-block forward pass to
`linalg::concurrent` (#728's safe concurrent pivot discovery: immutable `OnceLock`
publication, private dense scratch, scoped joins). Candidate-only backward reduction (#749)
then finishes the candidates exactly as after the serial pass. The echelon rows differ from the
serial ones; pivot columns and fully reduced candidates do not, so the basis is identical.

`Send + Sync` is proved by each concrete field through `FiniteField::concurrent_elimination`,
not added to `FiniteField` or to any F4 signature. Extension fields return `None` and stay serial.
A dispatch whose reservation (published rows plus two full-width rows per worker) would cross
the live-entry budget, or whose workspace exceeds 64 MiB, falls back to the serial kernel on the
untouched matrix, so no computation serial admits is refused. A worker panic propagates; nothing
partial is returned.

## Predeclared gates

Declared at commit `8ccea616`, before any complete-task campaign:

1. **Named large-task gain:** at least 10% complete F4-call improvement over the shipping
   serial route on MQ10 at both small primes, non-overlapping five-run ranges.
2. **Small controls:** cyclic-5/6 and katsura-6/7 at both primes under the selected `Auto`
   setting regress no more than 5% in F4-call median against serial.
3. **Memory:** process peak RSS no more than 1.25x serial on every task.
4. **Held-out validation:** the gate is fitted on per-batch replays of mq-random-10/32003,
   katsura-9/32003 and cyclic-7/32003 only; katsura-8, cyclic-8, mq-planted-10 at
   2147483647, mq-planted-wide-10 at 2^64-353 and katsura-10/32003 are scored but not used
   to choose constants, and must not regress beyond gate 2's 5%.
5. **Exactness:** every attempt's basis digest equals the serial arm's for the same task.

If gates 1–5 pass, `Auto { max_workers: 0 }` becomes the default in `F4Options::recommended`;
otherwise the default stays `Serial` and the route remains opt-in, with the failing gate named.

### Design 1 verdict (`Auto { max_workers: 0 }`, binary from `46867c14`): rejected

Measured 2026-11-16 01:00 under one bench-lock window; gate 1 and gate 5 pass, **gates 2
and 3 fail**:

- Gate 2: cyclic-5 0.69 → 1.82 ms, katsura-6 0.94 → 1.47 ms, cyclic-6 4.20 → 5.66 ms,
  katsura-7 4.42 → 5.11 ms, with **zero batches dispatched**. The cost is per batch, not
  threading: the route called `std::thread::available_parallelism` (which reads cgroup files)
  and permuted the matrix reducers-first on every batch before the gate said serial.
- Gate 3: MQ10 peak RSS 37.28 → 48.96 MiB (1.31x) and 38.28 → 51.80 MiB (1.35x) at up to 62
  workers per batch.

### Design 2, declared at the commit that introduces it, before measurement

Changes: the gate reads lower rows and entries off the row kinds without permuting, returns
before asking for parallelism when a batch is below `MIN_LOWER_NONZEROS`, and caches the
parallelism once per process. The candidate default is `Auto { max_workers: 16 }`, because
`Forced { workers: 16 }` held MQ10 RSS to 1.19x/1.21x in design 1's scaling run.

Gates 1–5 apply unchanged to `Auto { max_workers: 16 }` in a fresh campaign. If they pass it
becomes the default; if they fail, the default stays `Serial`, the route ships opt-in and the
investigation stops at two designs as #752 requires.

## Gate calibration

Every batch matrix that default F4 builds was cloned before elimination and replayed: the serial
reducer-block kernel against `linalg::concurrent` at 2, 4, 8, 16 and 32 workers, with three
interleaved repeats per batch (medians below). The constants were chosen on the three
training families only.
[Raw replays](../../research/parallel-forward/calibration/).

Even small batches scale. Lower blocks of 10 000–14 000 entries (0.7–1.3 ms serial) are
fastest at eight workers, at 1.8–3x. Blocks of 30 000 entries or more keep scaling to 16 or 32. MQ10's dominant
batch (1468 lower rows, 12 020 columns) goes from 779.6 ms to 28.3 ms at 32 workers. Spawning and
joining costs 0.2–0.4 ms, so batches below a few thousand lower entries stay serial. The chosen
gate is: serial below 8000 lower entries; otherwise one worker per 1500 entries, at least eight
rows per worker, and at most `max_workers`.

| Family | Role | Serial forward, ms | Gate, ms | Per-batch oracle, ms | Dispatched batches slower than serial |
|---|---|---:|---:|---:|---:|
| mq-random-10 / 32003 | training | 1068.36 | 54.61 | 46.32 | 0 |
| katsura-9 / 32003 | training | 131.90 | 11.35 | 9.85 | 0 |
| cyclic-7 / 32003 | training | 200.20 | 21.15 | 20.32 | 0 |
| cyclic-8 / 2147483647 | held out | 4628.52 | 191.99 | 189.65 | 0 |
| katsura-10 / 32003 | held out | 1071.27 | 47.67 | 44.69 | 0 |
| katsura-8 / 2147483647 | held out | 13.63 | 4.18 | 2.99 | 0 |

These are forward-pass sums only. The analyzer snaps to the measured worker count at or below
the gate's choice and caps at 32. Symbolic preprocessing, candidate reduction and final
interreduction are still serial and are not included here. mq-planted-10 and mq-planted-wide-10
have two trivial batches each and give the gate nothing to decide.

## Design 2 results

Complete F4-call medians [min, max] in ms over five fresh processes per arm, interleaved, with arm
order rotated per repetition. Process wall is measured outside the child and covers startup,
input parsing, F4 and rendering. RSS is the largest self-reported high-water mark of the five.
Every attempt completed; every arm of every task produced the same basis digest.
Lock window: 2026-11-16 02:43:30–02:46:00, 150 s, `end=exited`, load 1.35 → 3.14.
[Raw cohorts](../../research/parallel-forward/design2/).

### Forward × backward, MQ10

| Arm | GF(32003) F4 ms | x | GF(2147483647) F4 ms | x |
|---|---:|---:|---:|---:|
| serial forward / full backward | 3002.39 [2958.54, 3209.01] | 0.41 | 2671.48 [2661.16, 2705.90] | 0.40 |
| 16 workers / full backward | 2103.50 [2076.27, 2128.20] | 0.58 | 1941.30 [1919.70, 1959.75] | 0.55 |
| serial forward / selected backward (previous default) | 1225.94 [1214.04, 1259.11] | 1.00 | 1062.93 [1059.56, 1075.67] | 1.00 |
| concurrent kernel, 1 worker / selected | 1254.30 [1236.11, 1283.93] | 0.98 | 1033.07 [1023.82, 1053.94] | 1.03 |
| 16 workers / selected | 304.76 [302.03, 311.07] | 4.02 | 281.56 [278.80, 286.37] | 3.78 |
| **`Auto { max_workers: 16 }` / selected (new default)** | **305.73 [303.84, 306.19]** | **4.01** | **280.78 [280.40, 283.32]** | **3.79** |

The two optimizations compound because candidate-only reduction (#749) removed the serial backward
pass that limited #728's prototype, which had 1830 ms of serial backward at 16 workers.
Parallel forward work alone is worth 1.4x with full backward. With selected backward it is
worth 4x. The one-worker concurrent kernel is within the run-to-run range of the serial kernel,
so the gain comes from threads and not from a different single-thread algorithm. Process wall
for the new default is 329.20 / 304.72 ms, against 1246.57 / 1083.73 ms for serial.

### Worker scaling, MQ10, selected backward

| Workers | 32003 F4 ms | x | RSS MiB | 2147483647 F4 ms | x | RSS MiB |
|---:|---:|---:|---:|---:|---:|---:|
| serial | 1225.94 | 1.00 | 37.63 | 1062.93 | 1.00 | 38.17 |
| 2 | 752.89 | 1.63 | 43.46 | 632.25 | 1.68 | 44.36 |
| 4 | 521.50 | 2.35 | 43.69 | 456.78 | 2.33 | 44.20 |
| 8 | 376.61 | 3.26 | 43.80 | 338.35 | 3.14 | 44.64 |
| 16 | 304.76 | 4.02 | 44.34 | 281.56 | 3.78 | 46.32 |
| 32 | 272.45 | 4.50 | 46.35 | 259.83 | 4.09 | 48.07 |
| 64 | 264.48 | 4.64 | 48.57 | 254.05 | 4.18 | 51.86 |

Going from 16 to 64 workers saves another 10–13% at 1.29x/1.36x serial RSS, which fails gate 3.
That is why the default caps at 16. The curve flattens because what remains is mostly serial.
The calibration replay puts MQ10/32003's summed gated forward time near 55 ms, against a
272 ms call at 32 workers. The rest is symbolic preprocessing, candidate reduction, final
interreduction and batches too small to dispatch. These two figures come from different
harnesses, so treat the split as approximate. The RSS growth is not attributed further:
dense rows, thread stacks and allocator arenas were not measured separately.

### Adoption set, selected backward, serial vs `Auto { max_workers: 16 }`

| Task | Role | Serial F4 ms | Auto F4 ms | Change | RSS ratio | Batches dispatched |
|---|---|---:|---:|---:|---:|---:|
| cyclic-5 / 32003 | small control | 0.682 | 0.689 | +1.13% | 1.01 | 0 |
| cyclic-5 / 2147483647 | small control | 0.710 | 0.688 | −3.10% | 1.07 | 0 |
| cyclic-6 / 32003 | small control | 4.178 | 4.142 | −0.86% | 0.99 | 0 |
| cyclic-6 / 2147483647 | small control | 4.008 | 3.995 | −0.34% | 0.95 | 0 |
| katsura-6 / 32003 | small control | 0.941 | 0.950 | +0.89% | 1.02 | 0 |
| katsura-6 / 2147483647 | small control | 0.910 | 0.913 | +0.40% | 1.03 | 0 |
| katsura-7 / 32003 | small control | 4.447 | 4.377 | −1.58% | 1.01 | 0 |
| katsura-7 / 2147483647 | small control | 4.143 | 4.144 | +0.02% | 0.92 | 0 |
| katsura-9 / 32003 | training | 166.17 | 64.20 | −61.36% | 1.16 | 5 |
| cyclic-7 / 32003 | training | 277.44 | 139.51 | −49.71% | 1.12 | 18 |
| katsura-8 / 2147483647 | held out | 22.23 | 14.52 | −34.68% | 1.08 | 4 |
| cyclic-8 / 2147483647 | held out | 5509.58 | 1741.18 | −68.40% | 1.16 | 27 |
| katsura-10 / 32003 | held out | 1190.03 | 307.90 | −74.13% | 1.24 | 8 |
| mq-planted-10 / 2147483647 | held out | 0.125 | 0.128 | +2.28% | 1.03 | 0 |
| mq-planted-wide-10 / 2^64−353 | held out | 0.123 | 0.128 | +3.44% | 0.98 | 0 |

Changes are of medians. The two sub-0.2 ms planted tasks have overlapping ranges
([115.7, 128.8] vs [124.5, 131.4] µs and [117.9, 172.6] vs [125.7, 132.6] µs), and no batch was
dispatched on them. katsura-10's 1.24x RSS is the closest any task came to gate 3.

### Gate scorecard

| Gate | Design 1 (`max_workers: 0`) | Design 2 (`max_workers: 16`) |
|---|---|---|
| 1. ≥10% MQ10 gain, non-overlapping | pass (4.99x / 4.39x) | **pass** (4.01x / 3.79x) |
| 2. Small controls ≤5% regression | **fail** (up to +164%, zero batches dispatched) | **pass** (worst +1.13%) |
| 3. RSS ≤1.25x | **fail** (1.31x / 1.35x on MQ10) | **pass** (worst 1.24x, katsura-10) |
| 4. Held-out ≤5% regression | pass on large tasks; small held-out tasks paid design 1's per-batch cost | **pass** (worst +3.44%, sub-0.2 ms) |
| 5. Identical bases | pass | **pass** |

## Work, contention and resources

`F4Statistics::parallel_forward` reports dispatched and fallen-back batches, the largest worker
count, lost publications, the conservative entry reservation and workspace. A lost publication
is a row that reached an already-claimed pivot and reduced further. #728 measured these losses
and changed work counts on this kernel. They are not re-derived here. Changed pivot winners mean
the parallel arms do not execute the same instruction stream as serial. The bases are identical
because candidates are unique after full reduction.

Under dispatch, a batch's `peak_nonzeros` is the reservation, meaning published rows plus two
full-width rows per active worker. It depends on thread timing. `max_live_nonzeros` is
therefore an upper bound that varies between runs, so the live-budget regression now pins peaks
on the serial route. Budget admission is unchanged. A batch whose reservation does not fit runs
serially, and below the serial peak both routes refuse with the same error. Both properties are
tested.

## Not claimed

- No result off this machine and core layout. `max_workers: 0` respects affinity through
  `available_parallelism`, read once per process. The default's cap of 16 does not.
- No SMT arm, NUMA study or persistent runtime. Scoped spawn per batch was cheap enough for
  every batch the gate dispatches. #592's pool is not needed for this route.
- No wider-field speedup claim. The only 64-bit task, mq-planted-wide-10, has nothing to dispatch.
  #738's hard wide rungs are the place to measure that.
- No new fixed-budget completion. MQ14 was not attempted.
- Extension fields (`Gf13Pow4` and the like) stay serial, because their `IrreduciblePolynomial`
  marker carries no `Send + Sync`.
- The scoreboards and the M28 report are #754's. Any F4 timing recorded before `394a9ca1` was
  taken with serial forward elimination.

## Reproduce

Commands are in [`research/parallel-forward/README.md`](../../research/parallel-forward/README.md).
`summarize-study.py --check` re-verifies the retained cohorts offline, without running a solver.
