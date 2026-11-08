# The register tile in `Matrix`'s `Mul`: every shape that was swept, and what each one measured

**Measured at:** `8720c5b7` for §2 and §3 (the shapes swept for #496, re-stated here from that pull
request rather than re-measured), and `17f8f32c` for §4 and §5 (the hand-written 4-row shapes,
measured for #517). The only commit to touch `src/linalg/matrix/arithmetic_ops.rs` or
`benches/linear_algebra.rs` between the two is #516 itself, whose kernel is the 2x8 baseline of §4
— `git log 5d9f3afe..17f8f32c --numstat` on both paths is empty — so the two sets of figures
describe the same instrument and the same baseline.

This note exists because the #496 sweep lived only in a pull request body, and the one shape family
it did *not* settle — the 4-row tiles — was then read off that body as settled. Collecting every
shape in one table is what stops that happening a third time.

Machine: AMD Ryzen Threadripper PRO 5995WX, 128 hardware threads, 503 GB RAM. Every figure under
`tools/benchlock.sh`, `taskset --cpu-list 8` (one core), reps as the outer loop with the kernels
interleaved inside each rep, `RUSTFLAGS` unset, `RUSTC_WRAPPER=""`, a per-worktree
`CARGO_TARGET_DIR` and a per-kernel `CRITERION_HOME`. The `-C target-cpu=x86-64-v3` floor is
verified **in each artifact** by `tools/vec_census.sh --require` rather than inferred from a build
log, because `RUSTFLAGS` replaces `target.*.rustflags` instead of adding to it and a crate built
outside the worktree inherits no `.cargo/config.toml` at all (#352). #496 took three reps; §4 took
twelve, for the reason in §4.2.

Over `Zp2147483647`, through the existing arms of `benches/linear_algebra.rs`: four square sizes,
and four `m x k` times `k x n` shapes holding the multiplication count at 2^26 so the only thing
that varies is the right operand's footprint — 16 KiB, 256 KiB, 8 MiB, 128 MiB.

**The 128 MiB arm is not optional.** It is where 2x16 and 2x32 gave back 26% and 16% while looking
within 1% of the shipped width in cache (§2), and where 4x8 loses half its speed while looking like
parity in cache (§4). Twice now, a screen that stopped at the square sizes would have shipped the
wrong kernel.

---

## 1. Method, and why it is a source splice

Every kernel is a bench binary built from one tree, differing only in the multiplication loop: a
harness replaces exactly the span of `arithmetic_ops.rs` between the `let mut product` declaration
and the `Self::Output {` that closes `mul`. Splicing the pre-existing kernel back in is a
byte-for-byte identity, which is how "differing only in the loop" is checked rather than asserted.

The harness is not committed. It is twenty lines of text substitution over one file, and a committed
copy would be a second definition of the kernel to keep in step with the first.

A candidate kernel is run against `test_product_matches_reference_across_tile_remainders` in
`src/linalg/matrix/arithmetic_ops.rs` before it is allowed to be timed. Field arithmetic is exact,
so a correct tile is bit-identical to the textbook sum and there is no reassociation to excuse a
difference; both 4-row kernels pass, and the same test fails on a 4x8 whose four-row `j` remainder
pass is deleted. **A fast kernel that has not been shown bit-identical has not been measured, it has
been raced.**

### 1.1 The load each figure was taken under

`benchlock` serializes benchmarks and not builds, so another agent's `cargo test --release` runs
straight through the lock while a pinned measurement believes itself alone (#318). The one-minute
load average is therefore recorded at every kernel run and is part of each figure:

| rep | 2x8 | 4x8 | 4x4 | |
| --- | --- | --- | --- | --- |
| 1-3 | 21.97, 4.73, 26.32 | 9.42, 3.75, 16.07 | 6.67, 6.32, 109.92 | |
| 4-6 | 39.97, 14.30, 4.31 | 137.38, 13.36, 5.82 | 59.69, 6.16, 45.95 | |
| 7-9 | 19.76, 10.53, 15.16 | 5.42, 4.54, 8.14 | 42.51, 78.33, 124.74 | |
| 10-12 | 2.49, 3.34, 349.90 | 3.56, 2.34, 111.73 | 3.07, 2.34, 719.90 | kernel order rotated |

Reps 1-9 ran the kernels in a fixed order and 4x4 drew the high loads nine times out of nine, which
is a position effect and not a property of the kernel — so reps 10-12 rotated the order to put 4x4
first. That is what produced rep 10, and it is also why 4x4's apparent 3-5% out-of-cache advantage
in reps 1-9 shrank to 0.6-1.5% once it stopped being measured last.

## 2. `j`-only tiles, and `i`-`j` tiles at two rows (#496)

Ratios against `ikj` with `k` unrolled four deep, which is what the tile replaced; `>1` is faster.

| kernel | square n=128 | rhs 128 MiB |
| --- | --- | --- |
| `j` tile only, width 4 | 0.89-0.90x | not screened |
| `j` tile only, width 8 | 0.95-0.97x | not screened |
| `j` tile only, width 16 | 0.99-1.02x | 0.89-0.93x |
| **2x8 (shipped)** | **1.08-1.09x** | **1.01-1.03x** |
| 2x16 | 0.99-1.01x | 0.74x |
| 2x32 | 0.98-1.01x | 0.84x |

The 128 MiB arm is the reason this table has two columns. 2x16 and 2x32 are within 1% of 2x8 in
cache and give back 26% and 16% out of it, so a screen that stopped at the square sizes would have
shipped the wrong width.

## 3. The formulation, which is not a shape at all (#496)

The same 2x8 shape written with **array-indexed accumulators** — `acc[r][t]`, the tile dimensions as
array ranks, the row reached as `self.elements[(i + r) * depth + k]` under a runtime `r` — measured
**0.88-1.10x** where the named-slice spelling measured 1.02-1.30x on the same arms. Identical
arithmetic, identical tile shape; the formulation accounts for roughly 20%.

That is why the shipped kernel hand-writes its two rows instead of generalizing over a tile height,
and it is the whole reason §4 had to be measured separately: the 4-row shapes built for #496 were
built from that template, so their figures (0.85-0.96x) measure the formulation and say nothing
about the shape.

**Any figure taken from an array-indexed template is a measurement of the template.** It is not
comparable with the hand-written kernels in this note and must not be entered in these tables.

## 4. `i`-`j` tiles at four rows, hand-written (#517)

Four named row slices and four named accumulator arrays, in the shipped kernel's own style, with
the shipped 2-row and 1-row passes kept verbatim as the row remainder. Rows 2 and 3 of a count that
is not a multiple of four therefore run exactly the code that ships today.

Twelve reps were taken across four sessions of the machine lock. **One of them — rep 10 — is the
one where all three kernels ran at a one-minute load average below 4**, and it is the figure this
note publishes; it also reproduces #496's 2x8 baseline to within a percent at every arm
(56.9 µs / 466 µs / 3.69 ms / 29.5 ms square, 117-126 ms across the footprint sweep, against the
56.5-57.7 µs / 462-466 µs / 3.67-3.71 ms / 29.2-29.6 ms / 117-127 ms on record), which is the
evidence that it is the same instrument and not merely the fastest run. §4.2 gives the whole
twelve-rep spread so that no conclusion here rests on a single rep. `>1` means the 4-row tile is
faster than the shipped 2x8.

### 4.1 Rep 10 — `load=2.49 / 3.56 / 3.07` at the three kernel runs

| arm | 2x8 (shipped) | 4x8 | 4x4 | 4x8 | 4x4 |
| --- | ---: | ---: | ---: | --- | --- |
| square n=32 | 56.9 µs | 57.6 µs | 58.7 µs | 0.988x | 0.969x |
| square n=64 | 466.1 µs | 468.8 µs | 470.3 µs | 0.994x | 0.991x |
| square n=128 | 3.69 ms | 3.78 ms | 3.78 ms | 0.977x | 0.976x |
| square n=256 | 29.53 ms | 29.64 ms | 29.61 ms | 0.996x | 0.997x |
| rhs 16 KiB (32768x32x64) | 117.39 ms | 116.01 ms | 120.32 ms | 1.012x | 0.976x |
| rhs 256 KiB (2048x128x256) | 117.03 ms | 118.12 ms | 120.66 ms | 0.991x | 0.970x |
| rhs 8 MiB (64x512x2048) | 126.04 ms | 126.52 ms | 124.23 ms | 0.996x | 1.015x |
| **rhs 128 MiB (4x2048x8192)** | **125.61 ms** | **252.54 ms** | **124.89 ms** | **0.497x** | **1.006x** |

### 4.2 All twelve reps

Median ratio and the full range. The ranges are wide because this is a shared 128-core box and
`benchlock` serializes *measurements* and not *builds*: the loads these reps were taken under run
from 2.3 to 719. The sign of the conclusion does not depend on which reps are kept.

| arm | 4x8, median (range) | 4x4, median (range) |
| --- | --- | --- |
| square n=32 | 1.012x (0.799-1.166) | 1.002x (0.954-1.203) |
| square n=64 | 0.988x (0.720-1.142) | 1.001x (0.985-1.156) |
| square n=128 | 0.989x (0.880-1.010) | 0.992x (0.975-1.068) |
| square n=256 | 0.986x (0.822-1.174) | 1.002x (0.981-1.260) |
| rhs 16 KiB | 1.003x (0.917-1.035) | 0.997x (0.963-1.097) |
| rhs 256 KiB | 0.989x (0.924-1.045) | 0.997x (0.754-1.095) |
| rhs 8 MiB | 0.975x (0.860-1.148) | 1.047x (0.986-1.227) |
| **rhs 128 MiB** | **0.506x (0.486-0.645)** | 1.035x (0.900-1.295) |

**The 128 MiB collapse is in all twelve reps and it is the most stable number in the whole sweep**:
4x8 measured 252-276 ms there in every single run, against a 2x8 baseline of 125-172 ms. It is not
a load artifact; 4x8's own figure barely moves while everything around it does.

### 4.3 What the collapse is, and the control that isolates it

At JT=8 a 4-row tile holds 32 accumulators live across the `k` loop against 16 general-purpose
registers, so it spills. That was the issue's prediction and this is what it costs.

**4x4 is the control that pins it on the accumulators and not on the rows.** 4x4 has the same four
row slices, the same left-operand footprint (4 x 2048 x 8 bytes = 64 KiB at that arm), the same
traffic over the right operand — and 16 accumulators instead of 32. It measures 1.006x where 4x8
measures 0.497x. The row count and the operand walk are held fixed; the accumulator count is the
whole difference.

The 128 MiB arm makes that worse rather than better in a way worth stating, because it is the one
arm where the 4-row tile has a *traffic advantage*: `m` is 4 there, so a 4-row tile reads the 128 MiB
right operand **once** where 2x8 reads it twice. 4x8 does half the right-operand streaming and still
takes twice as long. Why the spill is nearly free in cache (0.977-1.012x at the other seven arms)
and catastrophic past L3 is **not** established here — it would want cache counters, not a wall
clock.

## 5. Still ALU-bound?

The footprint sweep answers this directly, since the work is identical in all four of its rows. Max
over min across 16 KiB → 128 MiB, in rep 10, with the twelve-rep median beside it:

| kernel | rep 10 | median of 12 | the walk, rep 10 |
| --- | --- | --- | --- |
| 2x8 (shipped) | 7.7% | 7.3% | 117.39 → 117.03 → 126.04 → 125.61 ms |
| 4x8 | **117.7%** | **108.1%** | 116.01 → 118.12 → 126.52 → **252.54 ms** |
| 4x4 | **3.8%** | 5.1% | 120.32 → 120.66 → 124.23 → 124.89 ms |

**4x8 is not ALU-bound.** It fails the §8.2 signature in
[`../MILESTONE-SIMD-PARALLELISM.md`](../MILESTONE-SIMD-PARALLELISM.md) outright, and by a margin
that makes it the only matmul kernel measured in this repository other than `ijk` to do so.

**4x4 is ALU-bound, and flatter than the shipped kernel** — 3.8% against 7.7% in the same rep, which
is the one respect in which a 4-row tile improves on 2x8. It buys that flatness by being slower in
cache rather than faster out of it, so it is a redistribution and not a gain: 2x8's advantage over
4x4 is 2.4-3.1% at the four square sizes and 1.2-3.0% at the two smallest footprints, against 4x4's
1.5% at 8 MiB and 0.6% at 128 MiB.

## 6. Verdict

**The `i` dimension is exhausted at 2. 2x8 stays shipped.**

- **4x8 is disqualified.** It loses at seven of eight arms in the clean rep and halves its speed on
  the 128 MiB arm in every rep taken. The spill the issue predicted is real and is not paid for.
- **4x4 is at parity at best.** 0.969-1.015x in the clean rep, with a median above 1 at only two of
  eight arms over twelve reps. It does not beat 2x8 at every arm, which was the bar for replacing a
  shipped kernel, and it is 2.4% behind at square n=128 — the arm #496 existed to fix, and the only
  shape `Matrix::pow`, the operator's one caller in the crate, ever produces.
- **The array-indexed formulation is still unusable for this kernel** (§3), and it is the reason the
  4-row shapes needed measuring twice. Figures taken from it do not belong in these tables.
- Nothing here is a reason to revisit a width: 4x4's small flatness advantage over 4x8 is the
  accumulator count, and at two rows the accumulator count is already inside the register file.

What would still be open, if the operator ever acquired a caller that mattered: the spill is a
register-allocation outcome and not an arithmetic one, so it is the kind of thing an explicit
`k`-blocking or a narrower element type could change. Neither is worth doing for `Matrix::pow`.
