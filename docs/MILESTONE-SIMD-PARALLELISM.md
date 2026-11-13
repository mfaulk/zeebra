# Milestone: Hardware-Efficient Arithmetic — SIMD and Parallelism

**Measured at:** publication bound `ef639645`…`c28b77f4` — the commits that published these figures,
recovered from git rather than recorded at the time ([§10](research/external-comparison-protocol.md#10-the-commit-and-what-a-publication-bound-is)).

**Status:** complete — M19-0 through M19-D landed; M19-E, M19-F and M19-G closed won't-do on
measurements recorded in §6; #62 landed afterwards and is recorded in §8, which corrects §5.3's
bandwidth reading and reopens the SIMD question at eight lanes; #159 landed after that and is
recorded in §9, which acts on the `HashMap` §4.4 named; and #149 closed the question §8.3 reopened
won't-do in §10, on all three of its routes
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
| [#159](https://github.com/mfaulk/zeebra/issues/159) | The pivot-of-column `HashMap` §4.4 names, indexed by column instead | done — §9, 28% of the default's elimination stage |
| [#149](https://github.com/mfaulk/zeebra/issues/149) | Whether the 8-lane AVX2 kernel §8.3 reopened should ship | **won't do** — §10; it fits only a backend nothing selects, and the shipped backend's loop would cost 9.81x the cells to make contiguous |

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

> The `HashMap` named in the sentence above was replaced by a direct-indexed store in #159. §9
> measures what that was worth, per backend. The paragraph is left as it was written: it was the
> state of the code when the 23.1% was taken, and §4.2's figures were measured against it.

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
It stays unconverted: #163 resolved it by deprecating the type in favour of `PrimeFieldElement256`,
on the grounds that it had no non-test caller. `Proth68Fr` is the same 68-bit prime over the
converted 256-bit field, and measures 9.8x faster at multiplication.


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

**105x.** Not a criterion benchmark: at the time, `fields::binary_field` was a private module with
no `pub use`, so no bench target could reach the type. The figure is from a standalone program
replicating both
implementations, which also cross-checks them on 1024 pairs.

> **The reason given above expired, 2026-11-08 (#218).** `src/fields/mod.rs` has exported
> `BinaryFieldElement` since `8757b4a` (2026-11-05), so privacy is no longer what keeps this off
> the bench harness — `benches/` simply has no characteristic-two target yet. The 105x stands; only
> its stated obstacle was stale. §5.2's identical claim is corrected the same way.

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

Also not benchmarked, for the same reason as §5.1 — and with the same correction: at the time
`fields::extension_field` was private, and it has been exported since `8757b4a`. What is missing is
a characteristic-two bench target, not an export (#218).

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

**That escape was taken, outside F4.** #166 parallelized the differential sweep's independent
*systems* — `SweepOptions::jobs`, one `SingularOracle` per worker, the report assembled in index
order — where the unit is a whole Gröbner basis plus an FGLM conversion plus a blocking Singular
subprocess rather than one of F4's batch phases. That is the "aggregates work across batches"
case: milliseconds to seconds against the 0.52 ms the three won't-dos above could not clear, so
the overhead argument does not reach it. It leaves #50, #51 and #52 closed on exactly the
measurements in §6.1 to §6.3: nothing was parallelized *inside* a Gröbner basis, and no figure in
this document was remeasured. The sweep's product is an agreement verdict and not a timing, which
is why concurrency is admissible there and why `tools/scoreboard.sh` (moved out in #668) — whose product *is* the
timing — was left sequential.

**And taken a second time, where the product *is* a timing.** #180 parallelized the resultant
route's Sylvester determinants — 16 384 independent evaluations of one matrix at one field element,
3.0 ms each against the 0.52 ms per-invocation overhead above — and measured **92–95% parallel
efficiency out to 32 cores**, taking a four-round CICO row from 49.7 s to 2.16 s. Because that
figure is a solver speedup rather than a verdict, it needed the recording discipline the paragraph
above said `tools/scoreboard.sh` would: `Environment::concurrency` on every run,
`Comparison::of` refusing a cross-concurrency ratio, and `Scoreboard::best` quoting uncontended
runs only. The scoreboard *runner* is still sequential and every row it writes still carries
concurrency 1. See [`docs/research/resultant-elimination.md`](research/resultant-elimination.md)
§6.6, which also records the granularity rule biting from the other side: the two-round row's
order-18 determinants are 8.6 µs each and get **slower** at 32 workers.

**And a fourth won't-do, outside F4, where the independence this section looked for does exist.**
#167 took the batched border reduction in FGLM — whose target loop *is* per-iteration independent,
the pivots being fixed before any target is touched, which is precisely what §6.1 failed to find in
the block update. The granularity rule held anyway. The target loop's largest single batch is
**210 µs on katsura-7 and 8 to 69 µs on every other system in the corpus** at the recommended batch
size of 64, against a measured **21 µs per worker** for `std::thread::scope` on this machine — so
one worker is the fastest row everywhere and the best multi-worker figure is 0.68x, the dispatch
being paid once per batch. One *unbounded* batch on planted-10 is large enough to reach **7.73x at
32 workers** at 24% efficiency; substituted back into the conversion that contains it, that route is
1.25x on katsura-7, parity on planted-10 and **0.92x on planted-8** — not safe everywhere, which is
the criterion the batch size itself was chosen against.
§6.8 of [`MILESTONE-FGLM-SCALABILITY.md`](MILESTONE-FGLM-SCALABILITY.md) has the four tables, the
projection, and the `dirty_from` accounting — including that the carry #167 named as the crux costs
1.00x to 1.02x of the cells on the batches large enough to matter, and the dispatch it did not name
costs everything.

So the shared reason now reads with a correction rather than an exception: independence is
necessary, the §6.4 rule is what decides, and the rule is about **the size of the unit of work** —
not about where the work sits in the algorithm. It also names the one thing that would move every
figure here, which neither this section nor #167 tested: 21 µs per worker is an OS thread spawn, and
a persistent pool is a different floor.

### 6.5 The persistent-pool premise, measured (#592)

**Measured at:** `6360904a`, Rust instrument `81aaa1be`. The
[worker-pool report](research/worker-pool.md) tests the shared dispatch premise with scoped
threads, a safe parked pool and a pinned Rayon dev comparand. Warm task dispatch is materially
cheaper with persistent workers, but still grows with worker count; the constant/nanosecond
expectation is not supported. Default border batches remain too small on most controls, with a
narrow Katsura-7 opportunity and no general conversion/default recommendation.

These are new matched-build measurements, not revised historical ratios. Preserve #50's zero-work
prefix result and the original #51/#52/#167 verdicts. A different kernel needs its own useful-work,
whole-route and resource gate; fewer spawning microseconds cannot create absent work. #728 consumes
the runtime evidence for concurrent residual pivots, independently of those decompositions.

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
it changed two of this milestone's conclusions. The unconverted field was later deprecated rather
than converted (#163), so the `__udivti3` this milestone leaves behind stays in the binary and is
no longer tracked as outstanding work.

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

> That question became #149 and is answered in §10, in the negative. The representation problem
> turned out not to be the binding one: the loop this kernel fits is `Backend::Dense`'s, no
> configuration selects that backend, and a *perfect* 2.9x on it still leaves it 1.78x behind the
> backend `F4Options::default()` does select on the largest instance measured here.

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

## 9. The pivot lookup, indexed (#159)

§4.4 named a `HashMap<usize, usize>` consulted once per row operation as part of why the Montgomery
win did not carry into F4. The keys are dense column indices in `0..num_columns`, so the table was
keyed by an integer that is already its own slot number. `PivotIndex` replaces it with a `Vec<u32>`
and `u32::MAX` as the vacant marker, in all four elimination paths.

§4.2's figures are **not** superseded: they were taken on the code §4.4 describes, and this section
measures the difference between that code and the code that replaces it. Both stand.

Machine and protocol: as §4. `rustc 1.97.0`, release profile, `taskset --cpu-list 0-7`, the two
binaries built from one tree with only `src/` swapped, runs interleaved, and an exclusive lock
held for the whole suite so nothing else on the workstation was running.

### 9.1 Elimination per backend, with the per-operation cost

`cargo run --release --example elimination_density -- katsura-6/grevlex` and `katsura-7/grevlex`.
Milliseconds over every matrix the instance builds; the mean of three runs on katsura-6 and two on
katsura-7, which agreed to within 1.4%. The dense rows exclude the conversions the backend pays
around the algorithm, in the milliseconds and in the per-operation figure alike; the harness reports
the conversion-inclusive figure, and `examples/elimination_density.rs` says so where it prints it.

| instance | backend | row operations | before | after | before ns/op | after ns/op | change |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| katsura-6 grevlex | `Sparse` | 44 023 | 17.42 | 15.71 | 395.7 | 356.8 | **−9.8%** |
| katsura-6 grevlex | `Adaptive` | 44 023 | 10.31 | 9.43 | 234.3 | 214.2 | **−8.6%** |
| katsura-6 grevlex | `Dense` | 44 023 | 44.41 | 43.84 | 1008.8 | 995.8 | −1.3% |
| katsura-7 grevlex | `Sparse` | 608 356 | 658.58 | 594.00 | 1082.6 | 976.4 | **−9.8%** |
| katsura-7 grevlex | `Adaptive` | 608 356 | 295.40 | 280.11 | 485.6 | 460.4 | **−5.2%** |
| katsura-7 grevlex | `Dense` | 608 356 | 1346.72 | 1327.05 | 2213.3 | 2181.9 | −1.5% |

`row_operations` is **identical on both sides and across all three backends**, which is what makes
the nanoseconds-per-operation column a statement about the cost of an operation rather than about
how many there were. That the three backends agree on it at all is the pre-existing contract; that
the two sides agree on it is the acceptance criterion, and it is pinned by
`test_every_path_reproduces_the_pre_indexed_pivot_oracle` rather than left to this table.

### 9.2 Storage

The index is one allocation per elimination, freed with it, so its peak is the widest matrix of the
instance.

| instance | widest matrix | indexed, `4 * num_columns` | the hash table it replaces |
| --- | ---: | ---: | ---: |
| katsura-6 grevlex | 1412 columns | 5.5 KiB | ~34 KiB at 1388 pivots |
| katsura-7 grevlex | 6862 columns | 26.8 KiB | ~136 KiB at 6810 pivots |

The second column is measured; the third is hashbrown's floor at that occupancy — 2048 and 8192
buckets of `(usize, usize)` plus a control byte each — not a measurement. **Both indexed figures
fit in a 32 KiB L1d; neither hashed figure does.** That is the mechanism §9.4 argues for.

### 9.3 Whole computations

`cargo run --release --example f4_profile -- baseline`, which selects `Backend::Sparse`. The
elimination stage and the whole computation, milliseconds, mean of four runs. Every instance whose
elimination stage exceeds a millisecond.

| instance | elim before | elim after | elim | total before | total after | total |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| katsura-7 grevlex | 623.41 | 603.07 | −3.3% | 726.42 | 704.07 | −3.1% |
| katsura-7 grlex | 390.27 | 377.24 | −3.3% | 482.82 | 469.56 | −2.7% |
| katsura-6 lex | 335.86 | 315.95 | −5.9% | 451.04 | 431.80 | −4.3% |
| katsura-6 grevlex | 16.38 | 15.34 | −6.3% | 24.74 | 23.72 | −4.1% |
| cyclic-5 grevlex | 15.39 | 13.71 | **−10.9%** | 21.13 | 19.42 | −8.1% |
| cyclic-5 grlex | 13.30 | 11.46 | **−13.9%** | 20.02 | 18.03 | −10.0% |
| katsura-6 grlex | 12.87 | 11.95 | −7.1% | 21.85 | 21.07 | −3.6% |
| cyclic-5 lex | 12.86 | 11.26 | **−12.4%** | 21.68 | 19.91 | −8.2% |
| katsura-5 lex | 5.63 | 4.96 | −11.9% | 11.83 | 11.09 | −6.3% |
| random-4 lex | 3.65 | 3.17 | **−13.2%** | 7.38 | 6.85 | −7.2% |

The two katsura-7 rows gain least, and they are the rows where the stage is largest. §9.4 reads
that as the elimination's own working set having pushed past the level the pivot store competes in,
not as the change being worth less there.

`cargo run --release --example f4_profile -- recommended` is the configuration
`F4Options::default()` selects: `Backend::Adaptive`, structured elimination, preprocessing. Mean of
three runs; the reps agreed to within 1.5%. Every instance whose elimination stage exceeds a
millisecond — the configuration is fast enough that most are below it.

| instance | elim before | elim after | elim | total before | total after | total |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| katsura-7 grlex | 7.05 | 5.69 | **−19.2%** | 45.66 | 44.53 | −2.5% |
| katsura-7 grevlex | 6.62 | 4.76 | **−28.1%** | 34.22 | 32.36 | −5.4% |
| katsura-6 lex | 1.14 | 0.96 | −15.7% | 21.14 | 20.63 | −2.4% |

This is the largest proportional gain in the milestone, and it is on the default. Two things make
the totals move much less. First, the elimination stage is no longer where the time is under this
configuration: katsura-7 grevlex spends 18.28 ms of its 34.17 in the final interreduction, which is
untouched. Second, the structured path's own `interreduce_prefix` still keeps a local
`HashMap<usize, usize>` of the same shape — it is in `src/grobner/f4/structured.rs`, outside the
elimination layer, and outside #159. The 28.1% is therefore a lower bound on what the change is
worth to that stage.

`cargo run --release --example scoreboard -- stable` (an example moved out in #668), whole solves, and
`scoreboard row poseidon31-cico-t16-rf2-rp0 --slice 0`, a registered full-width Poseidon reduction
at a precommitted specialization seed. **Three runs each side, and every run is listed**, because
these rows are whole solves and run-to-run variation is several percent — on a single pair the
Fukuoka row read −13.5%, which three runs do not support.

| row | before, ms | after, ms | mean | outcome |
| --- | --- | --- | ---: | --- |
| `poseidon31-cico-t16-rf2-rp0`, slice(12 fixed, seed 0) | 31 144, 30 512, 29 697 | 29 023, 28 904, 27 632 | **−6.3%** | the slice is empty — mathematically complete, not resource-limited, on all six runs |
| `poseidon-t3-rf2-rp1-planted` | 18 964, 19 021, 18 931 | 18 514, 19 315, 17 853 | −2.2% | **resource-limited**: `max_matrix_columns` at degree 11, the same bound at the same degree on all six runs. The spread is wider than the effect; this row says nothing. |
| `fukuoka-mq-III-n15-seed0` | 9912, 9577, 8864 | 8579, 8930, 8111 | **−9.6%** | verified witness, all six runs |
| `poseidon-t2-rf4-rp0-planted` | 388.1, 381.2, 398.8 | 374.1, 389.6, 373.8 | −2.6% | verified witness; the ranges overlap |
| `poseidon-t2-rf2-rp2-planted` | 151.4, 151.9, 156.9 | 148.1, 148.7, 146.1 | −3.8% | verified witness, all six runs |
| `fukuoka-mq-III-n10-seed0` | 124.2, 127.6, 123.3 | 110.4, 120.3, 110.0 | **−9.2%** | verified witness, all six runs |
| `poseidon-t2-rf2-rp0-planted` | 0.9, 1.0, 0.9 | 1.2, 0.9, 0.9 | — | verified witness; under a millisecond, so the sign is not meaningful |

The two Fukuoka rows are the largest whole-solve gains, at −9.2% and −9.6%, and they are over
GF(31) with 30 quadratic equations in 15 variables — the shortest pivot support of anything here.
The issue predicted the share the lookup takes is largest where pivots are short, and that is where
it is largest.

The full-width Poseidon reduction's slice gains 6.3% and reaches the same verdict on both sides. It
is the only row here with no overlap between the two triples.

### 9.4 The bound: memory, not ALU

**Memory-bound, and specifically a cache-footprint effect rather than a removed instruction.**

A `SipHash-1-3` over eight bytes plus one probe is on the order of 15 to 25 cycles, so removing a
fixed per-lookup cost would subtract a **constant** number of nanoseconds per row operation. It
does not. On `Backend::Sparse` the saving is **−9.8% on both instances**, at per-operation costs
that differ by 2.7x — 38.9 ns on katsura-6 and 106.2 ns on katsura-7. A constant would have read
−9.8% and −3.6%. The saving is proportional to the operation's own cost, which a removed
instruction cannot produce and a removed competitor for cache can: the hash table's 34 KiB and
136 KiB displaced row data, and the 5.5 KiB and 26.8 KiB arrays that replace them do not.

Three further readings line up with that and not with the ALU account:

- **`Backend::Dense` is the null result**, −1.3% and −1.5%. Its per-operation cost is 2.2 µs, a
  scan of a full dense row, so the pivot store is a vanishing share of both its time and its cache
  footprint. This is the bound the issue warned about, and it is where it predicted it.
- **`Adaptive` gains less on katsura-7 (−5.2%) than on katsura-6 (−8.6%)**, the reverse of the
  sizes. §4.4 measured katsura-7's live working set at 11 MB, out of L2; once the row data itself
  is out of L2, what the pivot store displaces matters less.
- **The whole-computation gains are largest on the smallest instances** — cyclic-5 and katsura-5 at
  11% to 15% of the elimination stage, katsura-7 at 3% — which is the same ordering.

One reading looks like a counterexample and is not. §9.3's default configuration gains **28.1%** of
its elimination stage on katsura-7 grevlex, far more than the 5.2% §9.1 measures for `Adaptive` on
the same instance. The two are not the same work: the default takes the reducer rows as established
pivots, so its loop performs a lookup for every column it visits while doing arithmetic for only
the few that are not already pivots. The issue put the share the lookup takes at
`lookup / (support * cost-per-entry)`, and the structured path shrinks the denominator without
shrinking the numerator. That is the ratio behaving as predicted, not a second mechanism.

Two instance sizes is two points, so the proportionality is an inference rather than a fit. What it
does rule out is the reading that the lookup's cost was the hash: the hash is a constant and the
measurement is not.

### 9.5 What this does not change

`EliminationStatistics` is identical in every counter, which is the acceptance criterion and is
pinned rather than asserted in prose. No `pub` signature moved: `PivotIndex` is `pub(crate)` and
every signature it appears in was already `pub(crate)` or private. `src/grobner/f4/structured.rs`
keeps a local map of the same shape — it is outside the elimination layer and outside this issue.

Two shapes fall back to hashing rather than indexing, and both are tested at the boundary:
`u32::MAX` rows or more, because a row index there would alias the vacant marker, and more than
`1 << 26` columns, because the sparse backend has no existing per-column buffer against which
`4 * num_columns` would be free. Nothing measured comes within four orders of magnitude of either.
`Vec<Option<u32>>` was checked rather than assumed: a `u32` has no invalid bit pattern for a
discriminant to occupy, so `Option<u32>` is eight bytes and the sentinel is what shipped.

## 10. The 8-lane kernel, and the backend it cannot reach (#149)

**Won't do.** §8.3 reopened #49 in the positive: eight lanes over a four-byte cell run 1.76x to
2.90x against the autovectorized comparand. #149 asked whether that kernel should ship, and the
answer is no — not because the lane win is not real, but because **the only loop it fits is in a
backend nothing selects, and the backend that is selected has no contiguous loop to put it in.**
This section is the measurement that decided it.

Machine and protocol: as §4 — AMD Ryzen Threadripper PRO 5995WX, AVX2/BMI2/FMA, no AVX-512, 256 MB
of L3. `rustc 1.97.0`, release profile, `taskset --cpu-list 0-7`, every run under
`tools/benchlock.sh`. Taken at **`1695fb9f`**, which is stated because §9.1's figures are not
comparable with these across the changes between the two and the commit is what says so.

### 10.1 Nothing selects the dense backend, and a perfect lane win would not change that

[`Backend`](../src/linalg/echelon.rs) is a *static* parameter, not a runtime policy:
`F4Options::recommended()` — which is what `F4Options::default()` returns — names
`Backend::Adaptive`, and `F4Options::baseline()` names `Backend::Sparse`. **No configuration in the
repository selects `Backend::Dense`**, which exists so that a sparse/dense comparison measures
storage rather than algorithm.

`cargo run --release --example elimination_density`, every Macaulay matrix each instance builds,
the mean of three runs (1-minute load average 4.1 to 7.6 at `START`; the lock serializes benchmarks
and not builds):

| instance | `Sparse` | `Dense` | `Adaptive` | dense conversion | `Dense` at a perfect 2.9x, conversion included | against `Adaptive` |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| cyclic-4/lex | 0.03 | 0.03 | 0.03 | 0.01 | 0.02 | too small to divide |
| katsura-5/grevlex | 0.48 | 0.55 | 0.34 | 0.10 | 0.29 | 1.18x faster |
| katsura-5/lex | 4.52 | 5.65 | 3.28 | 0.52 | 2.47 | **1.33x faster** |
| katsura-6/grlex | 11.46 | 19.04 | 6.14 | 1.31 | 7.88 | 1.28x slower |
| cyclic-5/grevlex | 13.04 | 21.92 | 7.43 | 1.14 | 8.70 | 1.17x slower |
| katsura-6/grevlex | 14.85 | 40.01 | 8.87 | 1.95 | 15.75 | **1.78x slower** |

Milliseconds, ordered by what the shipped backend costs. The `Dense` column is elimination alone;
densifying and sparsifying is its own column because SIMD does not touch it and a caller pays it,
so the sixth column divides only the elimination by the **best** ratio §8.2 measured — in cache, a
ceiling and not a prediction — and adds the conversion back unchanged.

The three runs reproduce to within **2.9%** on every backend and instance **except `Dense` on
katsura-6 grevlex**, which spans 38.73 to 40.77 ms, a 5.0% spread — the one arm whose working set
is a 1388 x 1410 dense matrix, and the one the conclusion rests on. Taken at its *fastest* run it
is still 1.72x behind `Adaptive`, so the margin survives the spread rather than depending on which
end of it is read.

**The sign of the result tracks instance size, and it is negative where the time is.** A perfect
2.9x on the dense kernel would beat the shipped backend on the two smallest instances measured, by
1.18x and 1.33x on eliminations costing 0.34 ms and 3.28 ms; it loses on all three larger ones, by
up to 1.78x on katsura-6 grevlex, the largest instance §8.4 and §9.1 both report. Tying `Adaptive`
there needs **4.51x** on the kernel comparing elimination with elimination, and **5.78x** to cover
the conversion as well — both above anything §8.2 measured at any working set.

That is not a win worth a specialization mechanism. Realizing even the small end of it needs the
`DenseRows` representation problem solved — a sealed trait or a `TypeId` path exposing raw
Montgomery `u32` cells, with a guarantee that `P` is odd and at most 2^31 — **plus** a runtime
policy to select `Backend::Dense`, which no configuration does today, and the reward is a fraction
of a millisecond on instances that are not the bottleneck while the same policy loses 1.78x on the
ones that are. This is the outcome #149 predicted from §8.4's pre-#159 figures; it is re-measured
here because §9.1 moved all three backends, and the re-measurement moves the margin without
changing the sign.

Bound: `Dense`'s kernel is **ALU-bound** — §8.2 measured ns/entry flat to within 7% across a
working set spanning four orders of magnitude, at 15.9 GB/s. That is why the lane win exists there,
and it is the one place in this section where it does.

### 10.2 The shipped backend's inner loop is a gather and a scatter

`DenseAccumulator::subtract_scaled` walks the **pivot's** sparse entries and indexes
`cells[*column]`. AVX2 has `vpgatherdd` and **no scatter at all** — that arrived with AVX-512,
which this machine does not have — so the kernel cannot be dropped in. The only route to a
contiguous span is to update `cells[pivot.lead .. pivot.tail)` whole, treating the pivot as dense
within its own span, which does

    span = trailing_column - leading_column + 1

cell updates where the shipped loop does `support = nonzeros`. **`span / support` is the work
multiplier a wide kernel must beat with its lane win**, and it is a property of the matrices rather
than of a timing, so it reproduces exactly.

`cargo run --release --example accumulator_span`, weighted by row operations because that is where
the time is. **Both reduction strategies**, because they do not see the same matrices:
`ReductionStrategy` changes which candidates come out of each batch and hence every later batch, so
the unstructured plan is the instrument §9.1 used and the structured one is what
`F4Options::default()` runs.

| instance | plan | row operations | mean support | mean span | span / support | span < 8 cells | 2.9x / multiplier |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| cyclic-4/lex | unstructured | 278 | 5.0 | 12.4 | 2.47x | 12.6% | 1.17x |
| cyclic-5/grevlex | unstructured | 79 775 | 34.2 | 88.6 | 2.59x | 0.5% | 1.12x |
| katsura-5/lex | unstructured | 27 922 | 30.8 | 64.7 | 2.10x | 0.0% | 1.38x |
| katsura-5/grevlex | unstructured | 3 179 | 24.9 | 53.3 | 2.14x | 0.0% | 1.36x |
| katsura-6/grlex | unstructured | 50 043 | 47.4 | 118.4 | 2.50x | 0.0% | 1.16x |
| katsura-6/grevlex | unstructured | 44 023 | 73.5 | 221.3 | 3.01x | 0.0% | 0.96x |
| katsura-7/grevlex | unstructured | 608 356 | 198.1 | 821.0 | **4.14x** | 0.0% | **0.70x** |
| **all** | **unstructured** | **813 576** | 159.6 | 644.3 | **4.04x** | 0.1% | **0.72x** |
| cyclic-4/lex | **structured** | 49 | 4.2 | 10.3 | 2.44x | 26.5% | 1.19x |
| cyclic-5/grevlex | **structured** | 3 929 | 10.2 | 26.6 | 2.60x | 1.9% | 1.11x |
| katsura-5/lex | **structured** | 551 | 16.8 | 25.0 | 1.49x | 0.0% | 1.95x |
| katsura-5/grevlex | **structured** | 1 609 | 9.4 | 37.1 | 3.95x | 0.0% | 0.73x |
| katsura-6/grlex | **structured** | 8 541 | 22.6 | 69.3 | 3.07x | 0.0% | 0.94x |
| katsura-6/grevlex | **structured** | 11 885 | 14.1 | 96.7 | **6.85x** | 0.0% | **0.42x** |
| katsura-7/grevlex | **structured** | 82 082 | 22.2 | 245.3 | **11.04x** | 0.0% | **0.26x** |
| **all** | **structured** | **108 646** | 20.7 | 203.0 | **9.81x** | 0.1% | **0.30x** |

**The multiplier grows with the instance, crosses the lane ceiling exactly where the time is, and is
worst under the strategy that ships.** Unstructured it is 2.1x on the smallest instance and 4.14x on
katsura-7 grevlex, which carries 75% of that half's row operations — a **28% loss** weighted the way
the clock weights it. Structured it is **9.81x**, and **11.04x** on katsura-7: a contiguous rewrite
would do eleven cell updates for each one the shipped loop does, against a kernel worth 2.9. That is
a **3.3x to 3.8x loss**, an order of magnitude clear of the break-even, and the trend runs the wrong
way on both axes — bigger instances are worse, and the shipped strategy is worse than the baseline.

The reason the structured plan is worse is the reason it is fast. Its pivots are the reducer rows
**as symbolic preprocessing produced them**, sparse and wide, rather than rows an echelon pass has
already filled in; that is what takes katsura-7's peak live entries from 1 390 812 to 63 087
(`docs/MILESTONE-F4-OPTIMIZATION.md` §7.1) and its accumulator traffic here from 156 M cells to
1.9 M. Sparser pivots over the same spans is precisely a higher `span / support`.

The loss is not a short-vector artifact. **0.1% of row operations have a span under one vector** and
0.7% under one cache line, so the lanes would fill; the extra cells are simply extra cells. The
occupancy histogram says where they come from:

| | plan | 0-10% | 10-20% | 20-30% | 30-40% | 40-50% | 50-60% | 60-70% | 70-80% | 80-90% | 90-100% |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| katsura-7/grevlex | unstructured | **51.4%** | 3.5% | 4.7% | 2.5% | 4.1% | 2.8% | 5.8% | 13.2% | 11.2% | 0.8% |
| **all** | unstructured | **41.9%** | 5.0% | 6.1% | 4.4% | 5.6% | 4.5% | 6.8% | 12.6% | 10.9% | 2.3% |
| katsura-7/grevlex | **structured** | **71.3%** | 12.3% | 4.8% | 3.8% | 2.7% | 2.0% | 1.0% | 0.8% | 1.0% | 0.4% |
| **all** | **structured** | **60.3%** | 14.2% | 7.5% | 5.3% | 3.9% | 2.9% | 1.8% | 1.5% | 1.6% | 1.0% |

Share of row operations, by decile of the pivot's occupancy within its own span. Unstructured the
distribution is **bimodal** — over 40% of row operations apply a pivot under 10% occupied in its
span, against about 24% in the 70-90% band — so a density-keyed representation switch would have to
predict which mode a pivot is in, which is the same negative result `Backend::Adaptive`'s own doc
comment records for global density. Structured there is no second mode at all: **74.5% of row
operations are under 20% occupied** and 4.1% are above 70%. Nothing is dense enough for a
contiguous kernel to be the right shape, and that is the configuration that ships.

Bound: the shipped path is **memory-bound, and specifically cache-footprint-bound**, which §9.4
established on independent evidence — the pivot-lookup saving was proportional to the operation's
own cost rather than constant, which a removed instruction cannot produce. A wider ALU has nothing
to widen there, which is the second, independent reason this route does not pay.

### 10.3 The loops that are already contiguous, and the strategy that shrinks them

`normalize` and the gather in `take` both run over `[lead, tail)` **today**, so they could be
widened with no restructuring at all, and that is the one route §10.2 does not close. Accounting
for every cell the accumulator reads or writes:

| instance | plan | cells touched | `subtract_scaled` | `normalize` | the gather in `take` |
| --- | --- | ---: | ---: | ---: | ---: |
| cyclic-5/grevlex | unstructured | 3 285 936 | 83.1% | 6.2% | 10.7% |
| katsura-6/grevlex | unstructured | 4 866 144 | 66.5% | 7.8% | 25.7% |
| katsura-7/grevlex | unstructured | 156 226 795 | 77.2% | 4.1% | 18.8% |
| **all** | unstructured | **168 817 833** | **76.9%** | **4.4%** | **18.7%** |
| cyclic-5/grevlex | **structured** | 48 047 | 83.4% | 5.0% | 11.6% |
| katsura-6/grevlex | **structured** | 178 456 | 93.9% | 1.6% | 4.4% |
| katsura-7/grevlex | **structured** | 1 894 168 | 96.2% | 1.3% | 2.5% |
| **all** | **structured** | **2 353 693** | **95.5%** | **1.4%** | **3.1%** |

**This route closes too, and on the same mechanism that closed §10.2.** Unstructured, 23.1% of the
cell traffic is already in a contiguous loop and three quarters of that is the gather rather than
the scale, which would have been worth costing. Under the strategy that ships it is **4.5%** —
1.4% scale and 3.1% gather — because the structured plan reduces the accumulator's total traffic
82-fold on katsura-7 and takes almost all of that out of the per-row loops rather than the
per-row-operation one. Fewer, sparser rows reach the accumulator; each still pays one
`subtract_scaled` per pivot.

So the ceiling on widening both contiguous loops is **4.5% of the accumulator's cell traffic**, and
that is an upper bound on a time share rather than an estimate of one — cells are not nanoseconds,
the gather is a compaction rather than an axpy (a left-pack, which without AVX-512's `vpcompressd`
costs a `movemask` and a `vpermd` through a lookup table), and §10.2's memory bound applies to it
as well. A 4.5% ceiling is below the 5.0% run-to-run spread §10.1 measured on its own widest arm.
**Won't do**, and #539 — filed from the unstructured figure before the structured one was taken —
is closed with this table as the reason rather than left on the board at a premise its own
instrument contradicts.

### 10.4 Acceptance

| Criterion | State |
| --- | --- |
| The decision recorded with the measurement that produced it | met — outcome 3 on all three routes: §10.1 for shipping it to `Dense`, §10.2 for restructuring the shipped loop, §10.3 for the loops that are contiguous already |
| Each figure states whether it was ALU-bound or bandwidth-bound | met — §10.1 ALU-bound (§8.2), §10.2 and §10.3 memory-bound (§9.4) |
| Measured on a workload that actually selects the backend | met — §10.2 and §10.3 report both reduction strategies, and the one `F4Options::default()` runs is the one the decision turns on |
| If shipped: identical matrices and `EliminationStatistics`, runtime probe, exercised fallback | n/a — nothing ships |
| If shipped: a specialization that cannot select the kernel for an even or above-2^31 modulus | n/a — nothing ships |
| No regression on `Backend::Adaptive` | met — no `src/` change, and `examples/accumulator_span.rs` asserts per matrix that its replay applies the same pivots the backend does, by `row_operations` and `pivot_inversions` |

What ships is the instrument. `examples/accumulator_span.rs` reports the span-against-support
statistic, and it is **self-checking**: for every matrix it replays, it also runs
`row_echelon_with(Backend::Adaptive, ..)` and asserts that its own pivot-application count and
normalization count equal `EliminationStatistics::row_operations` and
`EliminationStatistics::pivot_inversions`. A replay that drifted from the shipped loop would report
a real histogram of the wrong population, and that assertion is what rules it out. The counts also
match §9.1's independently — 44 023 on katsura-6 grevlex and 608 356 on katsura-7.
