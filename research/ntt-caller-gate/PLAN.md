# Serial caller gate, declared before measurement

Source: `e22b9b58cd29fd074a4234593d8790303a99c5f5`, 2026-11-13.
Research only for #732. No threaded transform or algorithm change.

Use the existing `graeffe_root` example and its planted-root input generator:

| case | selector | degree | RNG seed before generation | bytes/coefficient |
|---|---|---:|---|---:|
| koala64-small | koalabear | 6561 | `0x4b0a ^ 6561` | 8 |
| koala64-large | koalabear | 1594323 | `0x4b0a ^ 1594323` | 8 |
| koala32-large | koalabear32 | 1594323 | `0x4b32 ^ 1594323` | 4 |

These are complete **one-root polynomial calls**, using the public large-degree
example's input family, not a recovered cryptanalytic eliminant or an all-roots
solve. Four distinct nonzero roots are planted in a random cofactor. Check the
returned root by direct evaluation of the original input; no claim of all roots.
Do not compare widths as identical-input speedups: their historical example
seeds differ.

One identity execution per case writes canonical decimal coefficients, lowest
power first, one ASCII line ending in LF per coefficient. Bind each SHA-256 to
its field/degree/seed/source/lockfile in the manifest before the timing cohort.
The serialized inputs are regenerable from the pinned generator and lockfile;
retain digest, byte count and coefficient count rather than duplicate large
text inputs. Retain the returned field root in every raw profile.

Five interleaved fresh processes per case, one physical CPU (CPU2 after topology
verification), no standalone NTT sweep. Private target/TMPDIR on `/buildcache`,
empty wrapper, release/fat LTO/one codegen unit, `x86-64-v3`. Build/test before
locking. Hold the repository benchmark lock for all identities and timings.
Each child: external 60-second stop, hard 2 GiB address-space limit (stronger
than a resident-only cap for these single-process calls). Whole campaign:
360-second stop. Retain every attempt including nonzero exits. Full-process
wall/CPU/peak RSS come from `/usr/bin/time`; algorithm stage clocks/heap peaks
are the existing example's counters. Identity execution includes file I/O and
is excluded from timing medians. No subprocess is created by the timed probe.

`probe.patch` changes only pre-timer identity output and post-verification
reporting in the example. All arithmetic and timed call code stays pinned.
Forward time includes domain construction, transforms, pointwise arithmetic,
folding and retained polynomials. Treat forward/total as an **upper bound** on
transform-eligible share, never as measured transform-only elapsed time.

Decision thresholds for a later separately scoped prototype: at least 10%
median improvement in complete one-root call time against the same algorithm
at p=1 and the existing serial caller, with worst repeated regression at most
5% on the small control, no verification failures, and process RSS at most
1.25x serial and below 2 GiB. Require five interleaved fresh-process repetitions
at p=1,2,4,8,16,32,64, matched budgets/builds; no inference from timeouts.
Prototype requires #592's measured per-worker batch/barrier table and a task
size estimate allowing at most 5% dispatch/barrier time. Refuse if those bounds
or scratch cannot be met. No threshold in this plan asserts a measured gain.

Gate verdict here may nominate this caller but defers implementation while
runtime cost or exact eligible share remains unknown. #606 independently owns
whether transforms should enter the generic subproduct tree. This study neither
implements that path nor borrows its hypothetical work as an NTT workload.
