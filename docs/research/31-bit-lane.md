# M35-E2: a delayed-reduction lane for 31-bit primes (#1183)

**Status:** laptop stage complete, 2026-11-27. The kernel, the overflow proof and the
bit-identical tests are in, opt-in on both engines. **No timing is published here.** Every
deciding read (§9.8 of the [M35 plan](../MILESTONE-FINITE-FIELD-COMPETITIVENESS.md)) is the
bench host's; §6 lists them.

## 1. What it is

`src/linalg/lane.rs` now has two widths that share one generic kernel:

| Lane | Primes | Pivot values | Working cells | Remainder |
|---|---|---|---|---|
| small (#945) | p ≤ 46,337 | `u16` | `u32` | Lemire multiply-high |
| 31-bit (#1183) | 46,337 < p < 2³¹ | `u32` | `u64` | Barrett, one correction |

Mersenne31 (2³¹ − 1), BabyBear (2³¹ − 2²⁷ + 1) and KoalaBear (2³¹ − 2²⁴ + 1) are in range, over both
`PrimeFieldElement32` and `PrimeFieldElement64` (`Zp2147483647`, the panel's 2³¹ − 1 type).
`FiniteField::prime31_lane` returns the lane; it is disjoint from `small_prime_lane`, so a field
has at most one.

A row operation multiplies a raw pivot value (the field's stored representative, canonical or
Montgomery) by a canonical multiplier. Both representations are linear, so the product is the raw
form of the field product, and the kernel never reduces a product. It adds it to a `u64` cell and
keeps the cell in a redundant range `[0, B)` with one branchless conditional subtract. A cell is
reduced to a residue once, when the left-to-right scan reaches its column. The output and the work
counters (rank, zero rows, row operations, pivot inversions, final nonzeros) are those of
`Backend::Adaptive`, entry for entry.

**Where it is wired (opt-in, no default change):**

- **Signature engine:** `SigF4Options::prime31_lane`. The batch's reducer block and each new element
  are held in lane form only, and `Workspace::reduce_pivots` reduces through the lane workspace, on
  design 1, design 2 and the parallel cascade. The live budget now charges a lane workspace at its
  cell width (8 bytes per column) where that is wider than `F`.
- **Conventional F4:** `F4Options::prime31_lane`. It replaces the structured serial forward pass
  (`BlockPlan::ReducersFirstBlock` and `InterreducedBlock`) under `Backend::Adaptive`. Worker
  passes (`ParallelForward` when its gate admits workers) and the Faugère–Lachartre order are
  unchanged. A one-worker run (`ParallelForward::Serial`) takes the lane.
- **Harness:** `examples/m34_matrix.rs --lane31` sets both options and records `lane31` in its
  output line. It also instantiates BabyBear and KoalaBear records.
  `examples/sig_f4_study.rs --lane` now sets both lanes, and `examples/lane_matrix_gate.rs` accepts
  `m31`.

Dispatch, meaning when to turn the lane on, is #1123's (E). Its rule covers both lanes.

## 2. The overflow proof

Let 2 ≤ p ≤ 2³¹ − 1 and let `B = ⌊(2⁶⁴ − 1 − (p − 1)²) / p⌋ · p`, the lane's `bound`.

**(a) `B ≡ 0 (mod p)`.** By construction.

**(b) `B + (p − 1)² ≤ 2⁶⁴ − 1`.** The floor gives `B ≤ 2⁶⁴ − 1 − (p − 1)²`.

**(c) `B ≥ (p − 1)²`, and so `B ≥ p − 1`.** Rounding down to a multiple of p loses at most p − 1, so
`B ≥ 2⁶⁴ − 1 − (p − 1)² − (p − 1)`. That is at least `(p − 1)²` exactly when
`2(p − 1)² + p ≤ 2⁶⁴`. The left side increases with p. At p = 2³¹ − 1 it is
`2(2³¹ − 2)² + 2³¹ − 1 = 2⁶³ − 2³⁴ + 2³¹ + 7 < 2⁶³`. So it holds for every admitted prime, with half
of the `u64` range to spare.

**Step lemma.** Let a cell `c < B`, let a pivot value `v ≤ p − 1` and let the multiplier
`m ≤ p − 1`. The step computes `s = c + v·m`, then `c' = min(s, s − B mod 2⁶⁴)`.

- **No overflow.** `s ≤ B − 1 + (p − 1)² ≤ 2⁶⁴ − 2` by (b). A debug build would panic on overflow,
  and every test below runs in one.
- **If `s < B`:** the wrapped difference is `s − B + 2⁶⁴ > s`, because `B < 2⁶⁴`. So `c' = s < B`.
- **If `s ≥ B`:** `s − B ≤ (p − 1)² − 1 < B` by (c), and `s − B < s`. So `c' = s − B < B`.
- In both cases `c' ≡ s (mod p)` by (a).

A cell is loaded with a raw value `< p ≤ B`, so the invariant `c < B` holds from the start and
after every product. When `p + columns · (p − 1)² ≤ 2⁶⁴ − 1`, the subtract is compiled out. A cell
then takes at most one product per row operation, and a row applies each pivot at most once, so
the cell cannot pass that sum. At 2³¹ − 1 this holds only up to 4 columns, bounds.py's λ = 4.

**Remainder lemma.** `reduce_wide` takes `m = ⌊(2⁶⁴ − 1)/p⌋` and `q = ⌊x·m / 2⁶⁴⌋`. Since
`2⁶⁴/p − 1 ≤ m ≤ 2⁶⁴/p`, the quotient satisfies `⌊x/p⌋ − 1 ≤ q ≤ ⌊x/p⌋` for every `x < 2⁶⁴`. So
`x − q·p ∈ [0, 2p)` and one subtract finishes. The only other product the kernel reduces, the
normalization `v · inverse`, is below 2⁶² and goes through the same function. The negated multiplier
`p − canonical(r)` lies in `[1, p − 1]` because `r ≠ 0`.

**Storage.** Raw values are below p < 2³¹, so they fit `u32`. Column indices are `u32`, and the
kernel asserts that the matrix width fits.

| Prime | (p − 1)² | B / 2⁶² | (2(p − 1)² + p) / 2⁶⁴ | λ from a residue (bounds.py) |
|---|---:|---:|---:|---:|
| 46,349 (smallest admitted) | 2.15 × 10⁹ | 4.000 | ≈ 0 | 8.6 × 10⁹ |
| BabyBear 2,013,265,921 | 4.05 × 10¹⁸ | 3.121 | 0.439 | 4 |
| KoalaBear 2,130,706,433 | 4.54 × 10¹⁸ | 3.016 | 0.492 | 4 |
| Mersenne31 2,147,483,647 | 4.61 × 10¹⁸ | 3.000 | 0.500 | 4 |

The table is exact integer arithmetic, and `test_31_bit_bound_holds_for_every_admitted_prime`
re-derives (a)–(c) in `u128`.

## 3. How it differs from #269, #715 and the M33 refutation

M33 §4.3 lists "delayed reduction at 31 bits or wider (#270)" as refuted. The refuted thing is
#269's schedule carried to 31 bits. This lane differs from it in three ways, which is what the plan
(§7.8) asks a reopening to state.

1. **`u32` storage, not widened cells.** #269's pilot kept split `u16` pivot coefficients and
   widened the working sums to `u64` at GF(32003), where `u32` cells suffice (the small lane uses
   them). Here pivots are stored as raw `u32`. That is half the coefficient bytes of `Zp2147483647`
   (16-byte entries become 8 sparse, 4 dense) and equal to the `u32`-backed fields. Only the one
   working row per workspace is `u64`, which a 31-bit product requires.
2. **A redundant-range accumulator, not a fold every four products.** #269 folded the whole active
   row after λ updates. At 2³¹ − 1, λ = 4 (bounds.py, `dense-small-prime-rebaseline.md` §7), so its
   schedule degenerates into a full-row fold every fourth row operation. That is why it stopped at
   the small prime. This lane keeps each cell below `B ≈ 3 · 2⁶²` with a per-product `min`. There is
   no schedule, no fold pass and no counter. A cell is reduced to a residue once, at its column.
   A signed, centred accumulator (|r| ≤ (p − 1)/2) was considered and not taken: it quadruples λ to
   about 16 at 2³¹, but it still needs a fold schedule, and the redundant range removes the schedule
   outright.
3. **Conditional dispatch, not a global default.** #269 failed a no-material-regression gate for
   broad dispatch: Noon-6 regressed 4–8.5% in every pair. #945's lane failed the sparse controls
   (Katsura-8, Cyclic-6, mq-random-10). This lane is opt-in on both engines and changes no
   default. Whether and where it is dispatched is #1123's gate, with Noon-6 and those sparse
   controls among its controls (§9.8, §9.5).

**#715** (`multirow-reuse.md`) shared each sparse pivot's reads across four target rows and tried
an interleaved four-lane layout. Four-row scalar reuse was rejected at about 2%, and the layout was
slower outright. This lane is a single-row scalar kernel. It reads every pivot exactly as the field
route does, with identical row-operation and product counts. What it changes is the arithmetic per
product: a `u32 × u32 → u64` multiply-add and a conditional subtract, with no modular reduction.
#1162 attributed the 2³¹ gap to that cost, not to pivot reads. Nothing here is a band or explicit
SIMD; those remain #1196's, under §6.2's conditions.

## 4. Correctness evidence (all in CI's debug test run)

- **Kernel against the accumulator** (`linalg::lane`). Random reducer blocks with fill-in and a
  duplicate row, under every storage policy (dense_percent 0, 25 and 101):
  - over Mersenne31, BabyBear, KoalaBear, `Zp2147483647` and GF(46,349): rows equal
    `Backend::Adaptive`'s entry for entry, and the work counters are equal;
  - the same at GF(31) and GF(32003) on a canonical 31-bit lane, where cancellation to zero is
    frequent and GF(31)'s correction compiles out.
- **Worst-case accumulator inputs.**
  - A cell at `B − 1` takes the maximal product `(p − 1)²` ten thousand times at 46,349, BabyBear,
    KoalaBear, 2,147,483,629 and 2³¹ − 1. There is no overflow, the invariant holds and the
    residue is exact (`u128` reference).
  - The same holds for 10⁴ random cells and products per prime.
  - A 400-column matrix puts 399 maximal products on one cell, through the kernel.
- **Remainder.** `reduce_wide` is exact on edge values, including `B − 1`, `B`, 2⁶³, `u64::MAX`
  and `(p − 1)²`, and on 10⁴ random `u64` values per prime, for p from 2 to 2³¹ − 1.
- **Range.** The 31-bit lane is offered exactly for 46,337 < p < 2³¹: not for the small lane's
  primes, not for primes above 2³¹, and not for 64-bit primes.
- **F4 echelon forms** (`grobner::f4::structured`). Every batch of Katsura-6/Mersenne31,
  Cyclic-5/BabyBear, Katsura-5/KoalaBear and Cyclic-5/`Zp2147483647`, under both block plans and
  both row forms, leaves the matrix bit-identical to the adaptive backend's, with equal counters.
- **F4 reduced bases.** With and without the lane, the bases and counters (batches, elements,
  row operations, initial and final nonzeros) are identical under lex, grlex and grevlex. This
  covers Katsura-6, Cyclic-5, Eco-6 and Katsura-5 over the four 31-bit types, and the option is
  ignored over GF(13).
- **Signature-engine bases** (`grobner::sigf4`, `research-sigf4`). On dense quadratics over
  Mersenne31, BabyBear and KoalaBear, Katsura-5 and Eco-6, the bases equal the field route's, with
  equal targets and elements. This holds on design 1, design 2 and the parallel cascade, with
  signature checks on. Over `Zp2147483647`, peak live bytes are no more than the field route's. The
  option is ignored over Goldilocks and GF(32003).
- **Harness.** `m34_matrix --lane31` leaves the reduced-basis digest unchanged at all three primes,
  for `f4` and `sig`.

## 5. Memory

- **Signature engine.** Each pivot is held once, in lane form, as #945's corrective iteration
  arranged. Over `Zp2147483647` that halves coefficient bytes, and the test above checks that peak
  live bytes do not rise. Over the `u32`-backed fields a sparse lane row has the same bytes as a
  field row, and a dense one has fewer. The workspace's `u64` cells cost 4 bytes per column more
  than a `u32` field's accumulator. The live budget charges them.
- **F4 forward pass.** The lane kernel converts the reducer block into lane pivots while the matrix
  still holds its field rows, as #945's kernel does. The pass's peak therefore adds the lane pivots'
  bytes, at most 8 per reducer entry. That copy is outside the live-entry budget, like #269's pivot
  cache was. The §9.8 RSS clause (≤ 1.0× the field route) is the bench host's to measure. If it
  fails, the conversion would have to release field rows as it goes.

## 6. Left for the bench host

None of these is measured here. Laptop figures would be unpinned development figures and would
decide nothing.

- Zeebra's own 2³¹/2⁶⁴ time ratio on Eco-12, Katsura-12 and Chandrasekhar-H 12 at one worker, before
  and after, at 2³¹ − 1, BabyBear and KoalaBear (`m34_matrix --engine sig|f4 [--lane31]
  --workers 1`).
- §9.8's regime clauses: ≥ 1.5× complete-task gain on two R3 families with an upper 95% bound
  below 1, a ratio ≤ 0.70, and reproduction at BabyBear or KoalaBear and on one held-out scale.
- Sparse controls (Katsura-8, Cyclic-6, mq-random-10) and Noon-6, measured with the lane forced on.
  They specify #1123's dispatch rule and decide nothing; the dispatch gate is scored with that rule
  applied (plan §9.1).
- Peak RSS against the field route on the regime rows (§5).
- Optionally, the matrix-level read: `lane_matrix_gate <archive> <vars> m31 accumulator|lane` on a
  captured 2³¹ − 1 batch.
- The deciding read also waits on #1200.

## 7. Reproduce (correctness)

```bash
cargo test --lib linalg::lane
cargo test --lib grobner::f4::structured
cargo test --lib --features research-sigf4 prime31_lane
cargo test --features research-sigf4 --example m34_matrix
```
