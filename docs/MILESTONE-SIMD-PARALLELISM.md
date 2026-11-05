# Milestone: Hardware-Efficient Arithmetic — SIMD and Parallelism

**Status:** complete — M19-0 through M19-D landed; M19-E, M19-F and M19-G closed won't-do on
measurements recorded in §6; #62 landed afterwards and is recorded in §8, which corrects §5.3's
bandwidth reading and reopens the SIMD question at eight lanes
**Prerequisite:** M16 for the stage attribution this milestone targets; independent of M18, which
runs in parallel on the quotient-algebra side and touches none of the same files
**Objective:** remove the software division under every field multiplication, then vectorize and
parallelize the elimination it feeds
**Tracking issue:** [#44](https://github.com/mfaulk/zeebra/issues/44)

## 1. Why

The crate used no multithreading and no SIMD: no `rayon`, no `std::thread`, no `std::arch`, no
`portable_simd`, no `#[target_feature]`. There was also no `.cargo/config.toml` and no
`[profile.release]`, so release builds targeted the baseline x86-64 ISA with LTO off and sixteen
codegen units.

M16 §6.2 established where the time goes: **elimination is 65% to 88%** of an F4 computation on
every instance above a millisecond, and symbolic preprocessing is 2% to 15%. M19 works on the
arithmetic under the elimination, and then on the elimination itself.

The entry point was not SIMD. `PrimeFieldElement64::mul` computed
`(a as u128 * b as u128) % P as u128`, and a const-generic modulus does not rescue that: LLVM does
not strength-reduce a 128-bit remainder. Six calls to `__umodti3` — compiler-rt's *software*
128-bit division — appeared in the `field_arithmetic` bench binary. Since x86 has no SIMD integer
division, nothing could be vectorized until that was gone.

## 2. Sub-milestones

| Issue | Scope | State |
| --- | --- | --- |
| [#45](https://github.com/mfaulk/zeebra/issues/45) M19-0 | Build configuration and a re-measured baseline | done |
| [#46](https://github.com/mfaulk/zeebra/issues/46) M19-A | Division-free prime field arithmetic | done, 64-bit only |
| [#47](https://github.com/mfaulk/zeebra/issues/47) M19-B | Carry-less multiplication for the binary field | done, 105x on the operation |
| [#48](https://github.com/mfaulk/zeebra/issues/48) M19-C | Delayed reduction in extension-field multiplication | done |
| [#49](https://github.com/mfaulk/zeebra/issues/49) M19-D | SIMD axpy kernels for dense elimination | done by autovectorization; explicit intrinsics measured slower |
| [#50](https://github.com/mfaulk/zeebra/issues/50) M19-E | Parallel block update in structured elimination | **won't do** — §6.1 |
| [#51](https://github.com/mfaulk/zeebra/issues/51) M19-F | Parallel Macaulay matrix construction | **won't do** — §6.3 |
| [#52](https://github.com/mfaulk/zeebra/issues/52) M19-G | Parallel critical-pair criteria | **won't do** — §6.2 |
| [#62](https://github.com/mfaulk/zeebra/issues/62) | A 32-bit prime field, which §5.3 identifies as the remaining lever | done — §8, and it reopens #49 |

## 3. What landed

### 3.1 Build configuration (M19-0)

`.cargo/config.toml` sets `-C target-cpu=x86-64-v3` for `x86_64` targets, scoped by
`cfg(target_arch)` so a cross build to aarch64 is not handed an invalid CPU name.
`[profile.release]` sets `lto = "fat"` and `codegen-units = 1`.

`[profile.bench]` is deliberately not restated. `bench` inherits `release` including these
overrides, verified with `cargo build --profile bench -v`, which shows `-C lto` and
`-C codegen-units=1`.

One trap, which cost a silent regression had it gone unnoticed: **`RUSTFLAGS` replaces
`target.*.rustflags` rather than merging with it.** Cargo takes the first source it finds. The CI
workflow set `RUSTFLAGS: -D warnings`, which would have discarded the ISA floor entirely and built
CI at the baseline x86-64 level while every local build used v3. Confirmed by inspecting the
emitted rustc invocation with and without the variable set. The workflow now states both flags.

### 3.2 Montgomery form for 64-bit prime fields (M19-A)

Elements of `PrimeFieldElement64<P>` are stored as `a * 2^64 mod P` when P is odd. Addition and
subtraction are untouched — the map is linear, so `aR + bR = (a + b)R`. Only multiplication and
the conversions changed.

- **An even modulus keeps the wide-remainder path.** R = 2^64 is not invertible modulo an even
  number, and `PrimeFieldElement64<2>` is a real instantiation: `grobner::f4::tests` uses it for
  GF(2). The predicate is on a const generic, so the branch folds at compile time.
- **The representation is not observable.** `value()`, `Display`, and the serialized bytes all
  give the canonical residue. This needed a `serialize_with` to pair with the existing validating
  `deserialize_with`; without it the derived implementation would have emitted Montgomery form and
  silently changed the wire format.
- **`value()` is now a reduction, not a field read.** A hot loop should hold field elements and
  convert at the boundary.

`PrimeFieldElement128` is unconverted and still reduces a 256-bit product by software long
division. It is the only remaining reference to a 128-bit division routine reachable from the
field benchmark.

#### Test strategy

`mul` had **no test against a wide-reduction oracle** — only `add` and `sub` did, added in M16.
That gap was filled before the change, since a representation change with no oracle for the
operation it alters is not a safe refactor. The new tests cover an even modulus (the fallback
path), Goldilocks, the largest 64-bit prime, small fields exhaustively, and random input.

Two further tests exist because the obvious ones would not have caught the likely failures:

- `test_the_wire_format_is_the_canonical_residue` pins the serialized bytes against a plain `u64`.
  The pre-existing round-trip test would have passed even if the format had become Montgomery
  form, because it only checks that encoding and decoding compose to the identity.
- `test_construction_paths_agree` compares elements built by `new`, `from_str`, arithmetic, and
  deserialization. A path that forgot to convert would still produce a reduced-looking value, so
  agreement across paths is what catches it.

`test_pow` was reading the private field directly and comparing against canonical constants; it
now uses `value()`. The expected numbers are unchanged.

## 4. Measurements

Machine: AMD Ryzen Threadripper PRO 5995WX, 64 cores, AVX2/BMI2/FMA/ADX/PCLMULQDQ, no AVX-512.
`rustc 1.97.0`. Release profile. `cargo run --release --example f4_profile`, the M16 instrument.

### 4.1 Artifact check

The requirement was not a time but the absence of a call. In the `field_arithmetic` bench binary:

| | `__umodti3` references |
| --- | --- |
| before | 6 |
| after | 0 |

The one remaining 128-bit division reference is `__udivti3` inside `PrimeFieldElement128`,
confirmed by disassembling and reading the enclosing symbol.

### 4.2 Elimination, attributed to each change

katsura-7 grevlex and katsura-6 lex, the two largest instances in the profile. Milliseconds.
Outer rows are the mean of three runs, which agreed to within 0.5%; the two middle rows are single
runs.

| configuration | k7-grevlex elim | k7-grevlex total | k6-lex elim | k6-lex total |
| --- | --- | --- | --- | --- |
| original | 824.7 | 921.1 | 423.5 | 526.6 |
| build configuration only | 701.2 | 793.9 | 381.2 | 482.2 |
| Montgomery only | 751.5 | 849.1 | 363.2 | 464.2 |
| both | **634.5** | **735.2** | **340.5** | **450.1** |

Elimination improves **23.1%** on katsura-7 grevlex and **19.6%** on katsura-6 lex. Whole-
computation wall clock improves 20.2% and 14.5%.

The two changes are of comparable size and neither dominates. The build configuration is worth
slightly more on katsura-7 and slightly less on katsura-6, which is consistent with its effect
being inlining across codegen units rather than anything specific to the arithmetic.

### 4.3 Field multiplication in isolation

`cargo bench --bench field_arithmetic -- field/mul`, both runs under the new build configuration,
so this isolates Montgomery alone. Lower is better; the benchmark multiplies over an array, so it
includes the loads.

| field | before | after | speedup |
| --- | --- | --- | --- |
| p31 — 2^31 - 1 | 522.9 ns | 445.4 ns | 1.17x |
| p64 — largest 64-bit prime | 708.8 ns | 460.5 ns | **1.54x** |
| p68 — 128-bit field, unconverted | 33.0 µs | 34.4 µs | 0.96x |

The p68 row is unchanged code; the 4% difference is run-to-run variation and code layout, not a
regression in anything that was edited.

### 4.4 Why the F4 gain is a fifth and not a factor of three

An isolated micro-benchmark of the two reduction formulas gives 2.0x to 2.4x, and an out-of-cache
axpy gives more. The F4 improvement is smaller, for two reasons that are worth recording because
they shape M19-D and M19-E.

**F4 runs over `Zp2147483647`**, a 31-bit prime. The product of two residues is at most 62 bits,
so the high limb of the `u128` is zero and `__umodti3` took its early-out path for a zero high
word. The baseline was never paying for a full 128-bit software division on this field — which is
exactly why the p64 row above improves 1.54x while the p31 row improves 1.17x. A measurement taken
on p64 and quoted as an F4 speedup would have been wrong by a wide margin.

**Multiplication is a fraction of the elimination loop.** `subtract_scaled` also loads and stores,
subtracts, tests for zero twice per entry to maintain the nonzero counts, and on the sparse path
chases pointers and consults a `HashMap` for the pivot of a column.

A 16 MB out-of-cache axpy runs at 0.59 ns/entry after the change, roughly 40 GB/s on one core,
already near single-core DRAM bandwidth. katsura-7 grevlex peaks at 1 390 812 live nonzeros, about
11 MB, which is out of L2. **For working sets that size, multithreading buys more than SIMD**,
because it aggregates bandwidth across cores while SIMD only helps the cache-resident blocks. That
is the ordering argument for M19-E over M19-D, and it is why every measurement in those issues is
required to name which bound it hit.

## 5. Acceptance criteria

| Criterion | State |
| --- | --- |
| Release builds select a modern ISA baseline, documented and CI-portable | met — `x86-64-v3`, README "Build configuration" |
| No field operation on the F4 hot path calls a software division routine | met for 64-bit — verified on the artifact, 6 references to 0 |
| Every change attributed to a stage, not only as a whole-computation delta | met — §4.2 |
| Field semantics unchanged; property tests pass unmodified | met — 854 tests pass; only `test_pow`'s private-field read changed |
| Montgomery form not observable through the public API | met — §3.2, two tests pin it |
| Each measurement states whether it was ALU-bound or bandwidth-bound | met — §4.4 |

Outstanding: `PrimeFieldElement128` is unconverted, and the six remaining sub-milestones are open.


## 5. The field work, M19-B through M19-D

### 5.1 GF(2^m): one instruction for sixty-four iterations (#47)

`multiply_polynomials` tested one bit of an operand per iteration, sixty-four times, and
`long_divide` then iterated once per degree the product had to come down, recomputing a
leading-zero count each time. Carry-less multiplication is a single instruction and the reduction
is three of them.

| | ns per multiply over GF(2^63) |
| --- | --- |
| bitwise loop + long division | 212.70 |
| `PCLMULQDQ` + Barrett | 2.02 |

**105x.** Not a criterion benchmark: `fields::binary_field` is a private module with no `pub use`,
so no bench target can reach the type. The figure is from a standalone program replicating both
implementations, which also cross-checks them on 1024 pairs.

`pclmulqdq` is probed at run time, not assumed. It is **not** implied by the `x86-64-v3` floor —
it arrived with the AES-NI generation and belongs to none of the microarchitecture levels.

Barrett needs the product's degree below 2m, and the type already guarantees it: `new` rejects any
pattern at or above `2^m`, so an element has degree at most m - 1. That is why `new` checks against
`2^m` and not against P, whose range admits degree-m patterns.

### 5.2 Extension fields: O(N) reductions instead of O(N^2) (#48)

Schoolbook multiplication reduced after every multiply-add. It now accumulates and reduces each
coefficient once, licensed by an explicit bound: a slot takes at most N products of two residues,
so the sum is below `N(P-1)^2`, checked against `u128::MAX` at compile time. A prime near 2^64
fills a u128 with one product and keeps the old per-step path; no modulus in this crate reaches it,
the largest declared being P = 251 at N = 4.

The per-multiplication heap allocation is gone — `[u128; 2N-1]` needs const-expression arithmetic
but two `[u128; N]` arrays do not.

Also not benchmarked, for the same reason as §5.1: `fields::extension_field` is private.

### 5.3 The SIMD question answered in the negative (#49)

After the de-branching in #60, LLVM vectorizes the kernel unaided: in `row_echelon_with` over the
31-bit prime, vector instructions go 71 to 175, `vpmuludq` 0 to 9, `vpsrlq` 0 to 4.

Hand-written AVX2, matching the shipped kernel's cells and counters exactly, at equal storage
width:

| working set | autovectorized | hand-written AVX2 | ratio |
| --- | --- | --- | --- |
| L1, 8 KB | 0.543 ns/entry | 0.631 ns/entry | **0.86x** |
| L2, 512 KB | 0.553 | 0.566 | 0.98x |
| out of cache, 32 MB | 0.750 | 0.699 | 1.07x |

Slower in cache. No intrinsics were added.

**The correction that produced the real finding.** A first version of this measurement showed 1.18x
to 1.59x for AVX2 and was wrong: the scalar path ran over `u64` arrays and the AVX2 path over
`u32`, so AVX2 moved half the bytes. At equal width the advantage disappears — the gain had been
the narrower *type*, not the wider instruction.

So the lever is **storage width**. A 31-bit residue in a `u64` wastes half of every cache line, and
this kernel is bandwidth-bound out of cache. That is #62, and it would make the SIMD question worth
asking again at eight lanes.

> #62 did both, and corrected half of this paragraph: see §8. The lever is real — 2.36x on this
> kernel — but the scalar kernel is ALU-bound at both widths rather than bandwidth-bound, and the
> 32 MB working set called "out of cache" above is inside this machine's 256 MB L3. The SIMD
> question, asked again at eight lanes, now answers 1.7x to 3.0x in favour of the intrinsics.

## 6. Parallelism: three won't-dos and one reason

All three parallelism sub-milestones closed without shipping code. They fail for one shared
structural reason, which is the most useful thing this milestone learned.

### 6.1 The block update has no work in it (#50)

The two-phase split was built and verified: identical matrices, `rank`, `row_operations`,
`pivot_inversions`, `zero_rows` and `final_nonzeros` against the sequential path over ten shapes
and six seeds each, deterministic over sixteen runs, budget enforced. Then measured, on batches
replayed from real computations, at 128 threads:

| system | order | batches | red% | seq/ms | par/ms | x |
| --- | --- | --- | --- | --- | --- | --- |
| cyclic-5 | lex | 32 | 71.8 | 9.45 | 26.17 | **0.36** |
| katsura-6 | lex | 114 | 80.0 | 32 337.66 | 32 694.89 | 0.99 |
| cyclic-5 | grevlex | 22 | 65.5 | 13.61 | 27.10 | **0.50** |
| katsura-6 | grevlex | 10 | 95.9 | 673.45 | 697.68 | 0.97 |
| katsura-7 | grevlex | 12 | 97.0 | 31 561.85 | 31 633.65 | 1.00 |

Never faster. The phase boundary says why:

```
phase1 ops: 0   lower rows: 3632   of which lead in reducer map: 0
```

**The parallel phase performs zero row operations, because not one lower row has a leading column
that a reducer pivot owns.** The echelon loop only ever examines a leading column, and the reducer
block's pivot columns are disjoint from the lower rows' leading columns — a pair row leads with its
lcm, and the reducer multiples exist to cancel monomials to the *right* of it. In block terms
`D -= C A^-1 B` has `C = 0` at every leading position.

What `BlockPlan::ReducersFirstBlock` buys is therefore **avoided work** — not echelonizing the
reducer block against itself — and not a parallel phase. The real work is
lower-row-against-lower-row, which is the sequential dependence chain #50 correctly identified as
unparallelizable. The `peak_nonzeros` semantics the issue asked to settle first never needed
settling.

One wrong diagnosis is worth recording: the first implementation updated a global live count and
peak as atomics per row operation, which at 128 threads is three read-modify-writes on one cache
line in the hot path and looked like the obvious cause. Replacing them with per-task locals changed
the result not at all — 0.36x to 0.36x.

### 6.2 Pair criteria are under one percent (#52)

The `other` bucket, which is where the criteria live, as a share of total: **0.3% and 0.6%** on the
two katsura-7 instances, 0.7% on katsura-6 lex, rising to 3.2% only where the absolute time is
milliseconds. That is the ceiling on the whole stage, of which the parallelizable part is a
fraction. M16-C already took the real win here by moving the criteria onto leading monomials.

### 6.3 Construction is big but its batches are small (#51)

Two measurements bound this without an attempt. Instrumenting `build_within`: **row filling is 47%
of construction** (177.2 ms against 203.0 ms for column discovery and the sort), and only the
filling is per-row independent. And from §6.1, rayon's per-invocation overhead here is about
**0.52 ms** — measured cleanly, since that phase did no work at all.

Giving the fill phase perfect speedup:

| system | order | total/ms | fill/ms | fill per batch | best case |
| --- | --- | --- | --- | --- | --- |
| katsura-7 | grlex | 486.02 | 20.38 | 1.853 ms | **+3.0%** |
| katsura-7 | grevlex | 759.49 | 18.95 | 1.579 ms | **+1.7%** |
| katsura-6 | lex | 452.92 | 39.09 | 0.343 ms | **-4.5%** |
| katsura-6 | grevlex | 25.53 | 2.10 | 0.210 ms | **-12.1%** |
| cyclic-5 | lex | 21.72 | 2.54 | 0.079 ms | **-64.9%** |

### 6.4 The shared reason

**F4 spreads its work over many small, sequentially-dependent batches.** What matters is not a
stage's share of the total but its size *per batch*, and that is at or below the cost of handing
work to a thread pool. katsura-6 lex is the clearest case: construction is 83 ms, the largest
anywhere in the profile, spread over 114 batches at 0.34 ms of parallelizable work each. Batches
cannot be parallelized against each other either, because each one's candidates change the basis
the next sees.

Parallelism is not ruled out for this project — it is ruled out *at this granularity*. A decom-
position that aggregates work across batches, or a single instance large enough that one batch is
substantial, would change the arithmetic. Anyone revisiting this should start from a measurement of
per-batch phase size, not from the block structure, which misled this milestone three times.

## 7. Acceptance criteria, closed out

| Criterion | State |
| --- | --- |
| Release builds select a modern ISA baseline, documented and CI-portable | met — `x86-64-v3` |
| No field operation on the F4 hot path calls a software division routine | met for 64-bit; `PrimeFieldElement128` unconverted and off the hot path |
| Every change attributed to a stage | met — §4.2, §6 |
| Field semantics unchanged; property tests pass unmodified | met — 977 tests, release and debug |
| Montgomery form not observable through the public API | met — two tests pin it |
| Each measurement states its bound | met — §4.4, §5.3 |

Outstanding: `PrimeFieldElement128` is unconverted. #62 landed afterwards and is recorded in §8;
it changed two of this milestone's conclusions.

## 8. The 32-bit prime field (#62), and what it corrected

`PrimeFieldElement32<P>` is the same field as `PrimeFieldElement64<P>` for any modulus both can
hold, in four bytes rather than eight. Montgomery form with R = 2^32, the representation
unobservable in the same two ways §3.2 established, and the instrument is
`examples/field_width.rs`.

Machine and profile as §4. `taskset`-pinned to one core; the axpy figures reproduced within 3%
across two runs, unpinned and pinned.

### 8.1 The arithmetic, in isolation

`cargo bench --bench field_arithmetic -- field/<op>/p31`, which now has a `p31_u32` arm over the
same modulus, so the pair is storage width at a fixed field. Per operation:

| | mul | add | sub | inverse |
| --- | ---: | ---: | ---: | ---: |
| `Zp2147483647`, 8 bytes | 1.809 ns | 1.041 ns | 0.984 ns | 262.1 ns |
| `Mersenne31`, 4 bytes | **1.351** | **0.751** | **0.752** | **226.8** |
| ratio | 1.34x | 1.39x | 1.31x | 1.16x |

### 8.2 The kernel, and the premise this corrects

`target -= factor * source` with the two zero tests the dense backend maintains, at a fixed *entry*
count so both widths perform the same number of cell updates. Bytes moved per entry is exact: two
cells read, one written, so 24 bytes at eight bytes a cell and 12 at four.

| working set (u32/u64) | u64 ns/entry | u32 ns/entry | u32 GB/s | AVX2 8 lanes | AVX2 GB/s |
| --- | ---: | ---: | ---: | ---: | ---: |
| 8 / 16 KB | 1.802 | 0.765 | 15.7 | **0.264** | 45.4 |
| 256 / 512 KB | 1.770 | 0.751 | 16.0 | **0.253** | 47.5 |
| 16 / 32 MB | 1.783 | 0.753 | 15.9 | **0.262** | 45.8 |
| 128 / 256 MB | 1.897 | 0.786 | 15.3 | **0.446** | 26.9 |

**The scalar kernel is ALU-bound at both widths.** ns/entry is flat to within 7% across a working
set spanning four orders of magnitude — the last u64 row is the only one outside 2%, and re-ran at
1.804 — and 15.9 GB/s is far under what one core can pull. #62 was
opened on the premise that the kernel is bandwidth-bound and that halving the cell width therefore
halves the time; on this instrument that premise is wrong, and the 2.36x has a different cause —
a 64-bit Montgomery reduction is 128-bit arithmetic that LLVM does not vectorize, and a 32-bit one
is 64-bit arithmetic that it does.

Two details make that reading defensible rather than convenient. The last row exists because this
machine has **256 MB of L3**: §5.3's "out of cache, 32 MB" is out of L2 and still in L3, so no
figure at that size can support a DRAM-bandwidth claim, including the 0.750 ns/entry this issue
quoted. And this instrument's u64 kernel runs at 1.78 ns/entry where §5.3's reported 0.750; that
harness was not committed, so the two are not the same program — only within-table ratios should
be read across, which is why every arm here is measured at both widths in one run.

### 8.3 The SIMD question, reopened at eight lanes

§5.3 closed #49 in the negative at four lanes over `u64`: 0.86x to 1.07x. At eight lanes over
`u32`, against a scalar comparand LLVM also vectorized — `vpmuludq` present in both, confirmed by
an instruction census over the artifact, with each kernel `#[inline(never)]` so the attribution is
unambiguous — the hand-written kernel runs **1.7x to 3.0x** faster. It is the only kernel measured
here fast enough for the bytes to bind: 45 GB/s in cache falling to 26.9 GB/s out of it, which at
24 bytes an entry would have been 0.89 ns rather than 0.446.

No intrinsics are shipped. The kernel lives in the example, checked cell for cell and counter for
counter against the scalar one at seven lengths including a non-multiple of eight, and the
Montgomery replica it runs over is checked against the shipped type before any timing is taken. A
shipped version would have to answer where the cells come from, since `DenseRows` is generic over
`FiniteField` and an intrinsic kernel is not.

### 8.4 Where the width pays, per backend

katsura-6 grevlex, F4's elimination stage, and two dense echelons over the same matrices:

| | u64 | u32 | ratio |
| --- | ---: | ---: | ---: |
| dense echelon, 1500x1500 at 5% | 2515.6 ms, 17.2 MB | 882.9 ms, 8.6 MB | 2.85x |
| dense echelon, 3000x3000 at 2% | 19789.6 ms, 68.7 MB | 6868.0 ms, 34.3 MB | 2.88x |
| F4 elimination, `Backend::Dense` | 70.78 ms | 25.27 ms | 2.80x |
| F4 elimination, `Backend::Sparse` | 35.03 ms | 25.90 ms | 1.35x |
| F4 elimination, `Backend::Adaptive` | 6.60 ms | 6.41 ms | **1.03x** |

**The benchmarks were deliberately not switched to the narrow field.** The issue anticipated that
the win only materializes where a caller selects the type; the measurement says something sharper.
`Backend::Adaptive` is what `F4Options::default()` selects, it is 4x faster than the dense backend
at either width, and it gains nothing — its cost is sparse-index traversal and scatter/gather into
a buffer, not cell traffic. The sparse backend gains little for a related reason: a sparse entry is
`(usize, F)`, which the index's alignment pads to **16 bytes at either width**, so sparse storage
does not shrink and `F4Options::live_entry_allowance` is unchanged. Switching
`benchmark_systems`'s callers would have moved the headline figures by 3% and invalidated every
number recorded against them.

The dense entry-budget conversion the issue asked about does move: `cells_per_entry` goes from two
to **four**, not three, because the entry cost is pinned at 16 bytes by the index while the cell
cost halves. Pinned by a test, with the stale comment that said three corrected.

### 8.5 Acceptance

| Criterion | State |
| --- | --- |
| Montgomery form not observable, serialized bytes pinned against a plain `u32` | met — the two tests from #46, plus one pinning four bytes on the wire |
| Field property tests pass over the new type unmodified | met — 1281 lib tests, 30 doc tests |
| No software division reachable from multiplication, verified on the artifact | met — `__umodti3` 0, `__umoddi3` 0, and no `div` instruction in any zeebra symbol of the `field_arithmetic` binary; the one `__udivti3` is §4.1's `PrimeFieldElement128` |
| Dense elimination at both widths on the same matrices, bytes-moved stated | met — §8.2, §8.4 |
| The SIMD question revisited at 8 lanes | met — §8.3, and the answer flips |
