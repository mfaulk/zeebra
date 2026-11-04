# Milestone: Hardware-Efficient Arithmetic — SIMD and Parallelism

**Status:** in progress — M19-0 and M19-A complete; M19-B through M19-G outstanding
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
| [#47](https://github.com/mfaulk/zeebra/issues/47) M19-B | Carry-less multiplication for the binary field | open |
| [#48](https://github.com/mfaulk/zeebra/issues/48) M19-C | Delayed reduction in extension-field multiplication | open |
| [#49](https://github.com/mfaulk/zeebra/issues/49) M19-D | SIMD axpy kernels for dense elimination | open |
| [#50](https://github.com/mfaulk/zeebra/issues/50) M19-E | Parallel block update in structured elimination | open |
| [#51](https://github.com/mfaulk/zeebra/issues/51) M19-F | Parallel Macaulay matrix construction | open |
| [#52](https://github.com/mfaulk/zeebra/issues/52) M19-G | Parallel critical-pair criteria | open |

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
