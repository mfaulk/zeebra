# Packing only the residual columns over GF(2) (#1077)

**Measured at:** `2ac6488f`. Every figure below is from that commit. The binary is
`examples/gf2_residual_replay.rs`, built `--release --features research-gf2-residual` with the
repository's `.cargo/config.toml` and `RUSTC_WRAPPER=""`. **Unpinned macOS laptop**
(Apple M4 Pro, 14 cores, Darwin arm64, rustc 1.95.0). One worker. No `taskset`, no
`tools/benchlock.sh`, no RSS readout. A second agent was building in a sibling worktree, so the
1-minute load was 3.7–4.1 at START and END of every run (`research/gf2-residual/provenance.txt`).
Each per-batch cell is the minimum over 7 repetitions in one process, arms interleaved with a
rotating order. Each solve cell is the minimum over 7 interleaved in-process solves. Read every
timing as a ratio between arms of the same run, not as an absolute.

Parent #1028. Related: #777 (packed dispatch), #794 (threshold), #816 (Faugère–Lachartre order).
Instrument, raw tables and scoring script: [`research/gf2-residual/`](../../research/gf2-residual/README.md).

## Decision (provisional)

- **Provisional adopt, pending pinned bench-host whole-solve measurement.** Use the residual-width
  kernel in place of the full-width reducer sweep inside the packed route. **Until that
  measurement lands, defer: no default changes.** On replayed batches it is **1.35x** (development)
  and **1.46x** (held out) faster than the shipped full-width packed kernel in total. It is
  **1.42x and 1.49x** faster in total on the batches that cost the packed route over 1 ms, and at
  least 10% faster on each of those 32 batches. It writes 0.59x the `xor` words. Every batch it loses by 10% or more costs the packed route under 75 µs, and
  those losses sum to 117 µs over 231 development batches.
- **Reject lazy tail construction.** On every one of the 293 F4 batches replayed, a pair row reaches
  every reducer's tail, directly or through another tail: lazy built 43 143 of 43 143 tails
  (development) and 29 021 of 29 021 (held out). Symbolic preprocessing adds a reducer only because
  some row names its leading monomial, so the closure is the whole block by construction. Lazy is
  eager plus a closure pass, and is 1.2%–2.6% slower in total. The lazy/eager split only differs
  on the synthetic test batches.
- **Whole solves gain less than batches** (Amdahl). At one worker: 1.05x in total on development
  (per instance 0.98x–1.10x) and 1.09x on the held-out set (1.02x–1.22x). The elimination stage
  alone is 1.00x–1.53x and 1.15x–1.71x.
- **Residual width predicts where there is nothing to gain. Batch cost predicts the losses
  better.** Batches whose residual is at least 75% of their columns break even (1.00x–1.02x in
  total) and hold most of the losses. Batches whose residual is 25%–50% gain the most (1.47x,
  1.60x). But every loss is under 75 µs, at any residual fraction, so a size floor separates the
  two sides as well as a width rule.

## 1. The kernel

A structured batch is `[A B; C D]`. The reducer rows are `[A B]`, with `A` unit upper triangular
on the columns the reducers lead. The pair rows are `[C D]`. The shipped packed route
(`src/grobner/f4/packed.rs`) packs `[C D]` at the full width and sweeps it against the sparse
reducers, a group of 8 at a time (`linalg::gf2::reduce_against_pivots`). Every target row's word
scan therefore covers the known-pivot columns too.

Over `GF(2)` the swept pair block is exactly `D + C·A⁻¹B`, and it lives on the residual columns
alone. The prototype (`src/grobner/f4/packed_residual.rs`, `Gf2Elimination::Residual`):

1. **Maps** each column to the reducer it leads or to its residual index, and checks every
   coefficient is one (the shipped eligibility check, unchanged: a `GF(2^e)` batch with a
   non-binary coefficient declines to the generic route).
2. **Packs `D`** at the residual width. `C` is never packed. It stays in the sparse rows.
3. **Builds tails** back to front. A reducer's tail, its row of `A⁻¹B`, is its residual entries
   plus the tails of the reducers its row names. Every named reducer comes later, so its tail is
   already built. *Lazy* builds only the tails some pair row reaches. *Eager* builds all of them.
4. **Applies tails.** The referenced tails are taken in ascending groups of 8. Each pair row waits
   in the queue of the next group it names, with a cursor into its sparse `C` entries. A group
   uses a Gray-code table of its 2^k sums when that costs fewer `xor`s than adding tails one at a
   time, which is `reduce_against_pivots`' rule.
5. **Hands off** the result to the shipped Four Russians echelon with selective back substitution,
   on the residual columns. It then writes the rows back with their columns mapped home. The
   write-back and its budget checks are the packed route's.

The working set is charged to `max_live_bytes` beside the sparse matrix before anything is
allocated at width. It is the maps, the packed `D`, and the larger of the tails plus the queues
plus one table, or the echelon's workspace. A batch that does not fit declines to the generic
route, as the packed route's does.

At `e22ea7b6` the uses of `C` were a list of (row, group) pairs, 16 bytes per `C` entry. That was
3.2 MB of the largest batch's 4.7 MB working set, and 1.5x–3.9x the packed route's on every batch
over 1 ms. `2ac6488f` replaced the list with the per-row queues above. That change was made on
working-set grounds, after seeing both sets' figures at `e22ea7b6`. It tunes no parameter. The
packed-over-residual totals at `e22ea7b6` were 1.38x (development) and 1.51x (held out), within
4% of those below. Their raw tables were not kept.

## 2. Correctness

`grobner::f4::packed_residual::tests` and `linalg::gf2::tests`. The tests were written before the
kernel and seen failing against a stub.

- **Coefficient for coefficient against an independent sweep.** Synthetic batches have residual
  widths 0, 1, 63, 64, 65, 127, 128 and 129, with 0–130 reducers at three densities, and are rank
  deficient. Every pair row of `D + C·A⁻¹B` equals both the shipped full-width sweep's and a naive
  set-based sweep's, under both tail modes.
- **After the echelon**, the selected rows equal the full-width route's and the rank is the same,
  at residual widths 63–129 and 300, on rank-deficient batches.
- **Randomized.** 200 random shapes (0–200 reducers, 0–200 residual columns, 0–80 pair rows,
  random densities, half of them rank deficient). Lazy and eager agree. Eager builds every tail.
  Lazy builds at least the referenced ones.
- **Per batch against both other arms.** On a traced 10-variable MQ run, every batch's candidates
  equal the full-width packed route's and the Faugère–Lachartre route's, with rank, zero rows and
  back-substituted rows equal too. Rank-deficient and candidate-free batches are included.
- **Full reduced bases.** Under lex, grlex and grevlex, the route returns the generic basis on
  dense, overdetermined and sparse MQ, cyclic-6 and katsura-6 over `GF(2)`, and on cyclic-5 over
  `GF(2^8)` with binary coefficients.
- **Eligibility preserved.** Odd characteristic runs generic. A `GF(2^8)` system with coefficient
  2 declines exactly the batches the packed route declines and returns the generic basis. Echelon
  output never packs.
- **Budgets.** The working set is admitted at exactly the reported figure and declined one byte
  below. The route is admitted at the exact byte peak, and one byte under the admitted bound it
  declines or refuses with `TooManyLiveBytes`. The entry allowance binds at exactly the reported
  peak. A budget the generic route refuses stays refused.
- **Degenerate batches.** An empty batch passes unchanged, and so does a batch whose pair rows all
  reduce to known leads.
- **Default untouched.** `F4Options::default()` is `Auto`, and a default solve records no residual
  batch.
- **In the replay itself.** Every arm's candidates equal the packed route's on every repetition of
  all 293 batches, and every solve's basis equals the packed arm's.

## 3. Per batch

`gf2_residual_replay batches {dev,heldout} 7`. The arms are `packed` (shipped, full width), `fl`
(Faugère–Lachartre order, generic sparse kernel), and `lazy` and `eager` (residual width). Times
are F4's elimination stage, conversion and write-back included.

**Sets.** Development is #777's instances (seed 272) and #794's grid at n = 12, 13, 14 (seed
794). **Held out**, named before any measurement, is #794's grid at **n = 15 on a fresh seed,
1077**: square and overdetermined MQ at densities 0.05–0.3, 62 batches. Nothing in the kernel was
tuned on either set. The table width 8 is the forward sweep's.

| set | batches | packed ms | fl ms | lazy ms | eager ms | packed/lazy | packed/eager | xor words lazy/packed |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| development | 231 | 89.37 | 143.70 | 66.06 | 64.34 | 1.35x | 1.39x | 0.59x |
| held out | 62 | 138.88 | 165.68 | 95.33 | 94.18 | 1.46x | 1.47x | 0.60x |

Against the per-batch oracle of the two shipped kernels, packed or FL, whichever is faster per
batch, the residual arm alone is 24.4% (development) and 25.7% (held out) cheaper. FL is the
slowest arm in total. The residual arm beats it on 174 of 231 and 55 of 62 batches.

**By residual fraction** (residual columns / columns):

| set | residual fraction | batches | packed ms | lazy ms | packed/lazy | lazy wins ≥10% | lazy loses ≥10% |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| development | 0–0.25 | 12 | 0.29 | 0.32 | 0.90x | 1 | 7 |
| development | 0.25–0.5 | 57 | 43.26 | 29.36 | 1.47x | 40 | 6 |
| development | 0.5–0.75 | 74 | 42.97 | 33.51 | 1.28x | 45 | 7 |
| development | 0.75–1 | 88 | 2.86 | 2.86 | 1.00x | 2 | 52 |
| held out | 0–0.25 | 5 | 0.44 | 0.38 | 1.15x | 4 | 0 |
| held out | 0.25–0.5 | 11 | 68.21 | 42.72 | 1.60x | 9 | 1 |
| held out | 0.5–0.75 | 23 | 68.51 | 50.55 | 1.36x | 11 | 0 |
| held out | 0.75–1 | 23 | 1.72 | 1.68 | 1.02x | 1 | 11 |

**By batch cost** (the packed route's time):

| set | packed time | batches | packed ms | lazy ms | packed/lazy | lazy loses ≥10% |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| development | under 100 µs | 159 | 3.25 | 3.15 | 1.03x | 72 |
| development | 100 µs–1 ms | 54 | 15.86 | 13.38 | 1.19x | 0 |
| development | over 1 ms | 18 | 70.26 | 49.53 | 1.42x | 0 |
| held out | under 100 µs | 28 | 1.01 | 0.95 | 1.06x | 12 |
| held out | 100 µs–1 ms | 20 | 7.06 | 6.51 | 1.08x | 0 |
| held out | over 1 ms | 14 | 130.82 | 87.88 | 1.49x | 0 |

The largest batches of each set:

| instance | batch | pair rows | columns | residual | reducers | D ppm | swept ppm | tail fill | uses per tail | xor words lazy/packed | packed µs | fl µs | lazy µs | packed/lazy |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| overdetermined-mq-16 | 2 | 4525 | 3146 | 1848 | 1298 | 10093 | 56805 | 2.6 | 167.7 | 0.80 | 15865.5 | 14113.8 | 11558.3 | 1.37x |
| mq-14-d0.15-s794 | 3 | 3563 | 2092 | 1303 | 789 | 11335 | 41457 | 2.2 | 145.3 | 1.00 | 8023.3 | 9122.8 | 6028.8 | 1.33x |
| mq-14-d0.15-s794 | 2 | 1089 | 2513 | 880 | 1633 | 32157 | 229883 | 2.3 | 50.0 | 0.38 | 4201.1 | 6569.5 | 2624.5 | 1.60x |
| mq-13 | 2 | 954 | 1906 | 676 | 1230 | 33051 | 209030 | 2.3 | 47.6 | 0.46 | 2648.3 | 3873.2 | 1791.1 | 1.48x |
| mq-15-d0.05-s1077 (held out) | 5 | 4645 | 2862 | 1794 | 1068 | 8310 | 34250 | 2.8 | 137.2 | 1.04 | 14478.4 | 12006.2 | 9986.4 | 1.45x |
| overdetermined-mq-15-d0.10-s1077 (held out) | 2 | 4045 | 3012 | 1627 | 1385 | 5845 | 32370 | 4.2 | 89.4 | 0.89 | 13276.3 | 10349.2 | 8680.6 | 1.53x |
| mq-15-d0.10-s1077 (held out) | 3 | 2190 | 3187 | 1086 | 2101 | 41008 | 161363 | 4.2 | 68.9 | 0.48 | 10276.1 | 9005.3 | 6125.8 | 1.68x |
| mq-15-d0.10-s1077 (held out) | 2 | 1116 | 3331 | 1080 | 2251 | 30038 | 257699 | 3.1 | 42.9 | 0.32 | 6161.8 | 10652.1 | 3218.9 | 1.91x |

"D ppm" is the pair rows' density on the residual columns before the sweep, and "swept ppm" is
`D + C·A⁻¹B`'s. "Tail fill" is set bits in the built tails over `B`'s nonzeros. "Uses per tail"
counts the tail references served (`C`'s entries plus references between tails) per built tail.

What the counters say:

- **Fill-in is moderate and the tails are heavily reused.** Over the batches above 1 ms the tails
  hold 1.4x–4.9x `B`'s entries (median 2.3x development, 2.5x held out). Each tail serves 15–192
  references (median 48 and 95). Precomputing the tails pays for itself many times over, which is
  why their build is 3% of the route's time.
- **`xor` words fall most where pair rows are few against many reducers.** Batches with 1–4
  reducers per pair row write 0.45x (development) and 0.39x (held out) the packed route's words,
  and run 1.44x and 1.64x faster. With fewer than a quarter of a reducer per pair row the words
  are about equal (0.97x, 1.02x), yet those batches still run 1.22x and 1.32x faster. The
  many-pair-row batches (3500–4650 pair rows against a sixth to a third as many reducers) write
  0.80x–1.04x the words and run 1.25x–1.53x faster. They apply their tails through 62–120 tables
  each, and overdetermined-mq-16's swept block is 29 words wide instead of 50. Word count is not
  the whole cost model.
- **Where the time goes** (lazy, all batches): echelon 58% (development) and 61% (held out). The
  multiply, including the `C` scan, is 21%. Packing `D` is 9%–11%, write-back 6%–7%, tails 3%.
  The echelon is the shipped kernel, so further gains need a faster echelon of the swept block,
  not a better sweep.
- **Bytes.** The largest tail store is 301 KB (development) and 306 KB (held out). The largest
  multiply table is 58 KiB, with 610 and 1099 tables built. On batches over 1 ms the charged
  working set is 0.86x–1.14x the packed route's (development) and 0.82x–1.15x (held out). On
  small batches it is up to 2.3x, because the per-column maps dominate there. The route's largest
  working set is 1.67 MB, and the packed route's largest is 1.96 MB. Simultaneous sparse and packed storage is charged
  as §1 describes. Peak RSS was not measured.

## 4. Whole solves

`gf2_residual_replay solve {dev,heldout} 7`. All three arms are forced (`Packed`,
`Residual(Lazy)`, `Residual(Eager)`), so they are not compared against `Auto`.

| set | instances | packed ms (sum) | lazy ms (sum) | eager ms (sum) | packed/lazy | per instance | elimination stage per instance |
| --- | ---: | ---: | ---: | ---: | ---: | --- | --- |
| development | 38 | 439.57 | 419.22 | 416.96 | 1.05x | 0.98x–1.10x | 1.00x–1.53x |
| held out | 10 | 505.55 | 463.44 | 462.78 | 1.09x | 1.02x–1.22x | 1.15x–1.71x |

| held-out instance | basis | packed ms | packed elim ms | lazy ms | lazy elim ms | packed/lazy |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| mq-15-d0.05 | 15 | 69.92 | 19.74 | 63.04 | 12.96 | 1.11x |
| overdetermined-mq-15-d0.05 | 15 | 13.36 | 1.46 | 13.05 | 1.27 | 1.02x |
| mq-15-d0.10 | 16 | 85.46 | 16.69 | 78.36 | 9.74 | 1.09x |
| overdetermined-mq-15-d0.10 | 15 | 26.50 | 12.98 | 21.71 | 8.35 | 1.22x |
| mq-15-d0.15 | 15 | 79.74 | 14.86 | 73.57 | 9.61 | 1.08x |
| overdetermined-mq-15-d0.15 | 15 | 24.12 | 10.71 | 21.45 | 8.08 | 1.12x |
| mq-15-d0.20 | 15 | 79.19 | 15.02 | 74.34 | 9.72 | 1.07x |
| overdetermined-mq-15-d0.20 | 15 | 24.22 | 10.75 | 21.78 | 8.16 | 1.11x |
| mq-15-d0.30 | 15 | 79.11 | 13.93 | 74.49 | 9.54 | 1.06x |
| overdetermined-mq-15-d0.30 | 15 | 23.93 | 10.61 | 21.65 | 8.15 | 1.11x |

The development rows are in `research/gf2-residual/solve-dev.tsv`. The whole-solve gain is
bounded by the elimination share. On square MQ-15 that share is 17%–28% of the solve.

## 5. What remains for the bench host

The decision above is provisional until these are measured:

1. **Pinned whole solves.** Fresh processes, `taskset` and `tools/benchlock.sh 1077`, arms
   interleaved across processes, peak RSS recorded. This includes the two-binary A/B of `main`
   against a branch where the residual kernel replaces the full-width sweep inside `Auto`'s packed
   route, since `Auto` is what the default runs.
2. **Sizes the laptop did not reach:** n = 16 square MQ, whose 12 840 × 9 622 batch dominates
   #794's sweep, and n ≥ 17.
3. **Multiworker.** Report one worker first, as here, and any worker count separately (#1028's
   rules).
4. Whether a **size floor** (about 100 µs of packed work, or an entry count) should keep small
   batches on the full-width sweep. The development losses are 117 µs in total, so this is a
   tidiness question, not a performance one.

## 6. Not done

- The FL arm is the generic sparse kernel in FL order. A packed FL arm is what this prototype is.
- No `GF(2^e)` slicing. Binary-coefficient `GF(2^e)` batches pack as before, and the rest decline.
- No SIMD, cache blocking or threads in the new loops. The `xor`s are left to the autovectorizer,
  as in the shipped kernel.
