# Field arithmetic specialization: which reduction per width (H14, #270)

**Measured at:** `0dc61474` (microbenchmark binary, and the end-to-end baseline arm, whose
`src/fields/prime_field_64.rs` is `2ec9d3af`'s) and `9860988e` (the adopted end-to-end arm; the
binary was built from the same logic before the constant was named). The narrow-only middle arm is
an uncommitted overlay of `9860988e` without the Mersenne branch. 2026-11-14 UTC. §3b (#780) at
`a9421093` (before) and `fa27467a` (after), whose trees differ only in `src/fields/prime_field_32.rs`.

## Decision

| Width | Shipped before | Verdict | Evidence |
|---|---|---|---|
| 31-bit in `PrimeFieldElement64` (`Zp2147483647`, every `P < 2^32`) | Montgomery, R = 2^64 | **Adopted: canonical residues, `u64` remainder by the constant; shift-and-add for 2^31 − 1** | MQ10/2^31−1 F4 call **0.748x** paired, identical basis (§3) |
| 31-bit in `PrimeFieldElement32` (32003, BabyBear, KoalaBear) | Montgomery, R = 2^32 | Keep | No candidate wins every kernel; Montgomery is the only one that vectorizes `map` well (§2.1) |
| `Mersenne31` (`PrimeFieldElement32<2^31−1>`) | Montgomery, R = 2^32 | **Adopted (#780): canonical residues, shift-and-add** | Wins all four kernels (0.56–0.83x); F4 forward elimination 0.77–0.78x on the adaptive backend, identical RREFs (§3b) |
| 62/64-bit, `P ≥ 2^32` | Montgomery, R = 2^64 | Keep the representation; **Shoup in the scatter kernel deferred: #779** | Shoup scatter 0.52–0.64x of Montgomery for `P < 2^63`, but it needs a prepared-factor API in `src/linalg` |
| Goldilocks 2^64 − 2^32 + 1 | Montgomery | Deferred: #781 | Special reduction 0.67x `map`, 0.69x `scatter`, 0.92x `chain` |
| 2^64 − 59 and other top-bit primes | Montgomery | Keep | Möller–Granlund pre-inverse is 0.79x on throughput kernels and 1.22x on latency; mixed |
| 68-bit (`PrimeFieldElement128`) | `u128` long division | Excluded: deprecated by #163 | `Proth68Fr` over `PrimeFieldElement256` is 9.8x faster; `docs/guide/finite-fields.md` |
| 254/255-bit (`PrimeFieldElement256`) | 4-limb CIOS Montgomery | Keep | Within 4% of ark-ff 0.6 on every kernel (§2.3) |
| GF(2^e), extension fields | PCLMULQDQ + Barrett; built over base-field ops | Excluded | #272 owns characteristic two; an extension field inherits its base field's reduction |

Delayed reduction inside elimination is **not re-measured here**. #269's H13 remainder
([elimination-kernels.md](elimination-kernels.md), "What delayed reduction actually buys") built
the GF(32003) prototype this issue asked for, found a 28% arithmetic win, and rejected it at the
full-solve gate (Noon-6 regressed in every pair). Its headroom table is the reason it stops at the
small prime: a `u64` cell holds 4 raw products at 2^31 − 1 and none at 2^64 − 59. The dot-product
arm below reproduces those bounds.

## 1. Protocol

`examples/field_reduction.rs`, one binary, every arm a same-build control. Each width runs the
shipped type through its public operators, a raw-word replica of its algorithm, and each candidate,
through the same four generic kernels over 4,096 cache-resident operands:

- `chain` — `x = x * y[i] + z[i]`, dependent: latency.
- `map` — `c[i] = a[i] * b[i]`: throughput, and the case LLVM can vectorize.
- `scatter` — `row[col[i]] -= f * coef[i]` into a 16,384-cell row: the shape of
  `DenseAccumulator::subtract_scaled`, which is where F4's elimination time goes.
- `dot` — `sum a[i] * b[i]`, reduced per product, or delayed into a wide accumulator.

Before any timing, every arm's result on every kernel is compared with `u128` arithmetic (254-bit:
with ark-ff 0.6 declared from the modulus, the oracle `prime_field_256`'s tests already use). The
operands include 0, 1, p − 1 and p − 2 at both ends of each array. The same checks are unit tests,
run in CI (`[[example]] test = true`), plus exact boundary products for the Mersenne and Goldilocks
reductions and the exact headroom bounds.

Ryzen Threadripper PRO 5995WX, rustc 1.99.1, release profile (fat LTO, one codegen unit),
`x86-64-v3`, `CARGO_TARGET_DIR` private to this issue with no compiler wrapper. Seven fresh
processes pinned to CPU 3 under `tools/benchlock.sh` (owner `zb-270-micro`, 1-minute load 7.6 at
start, 9.7 at end). Each cell is the median over processes of the in-process minimum of 31
repetitions; ns per element. Binary SHA-256 `47cebb79…`.

## 2. Per-width microbenchmark

### 2.1 32-bit storage (`PrimeFieldElement32`)

| p | arm | chain | map | scatter | dot |
|---|---|---:|---:|---:|---:|
| 32003 | shipped Montgomery | 4.00 | 0.264 | 1.26 | 1.25 |
| | raw Montgomery replica | 4.01 | 0.262 | 1.51 | 1.25 |
| | canonical, `%` by constant | 3.75 | 0.427 | 1.12 | 0.99 |
| | canonical, explicit Barrett | 4.01 | 0.430 | 1.23 | 1.18 |
| | Shoup (scatter only) | | | 1.25 | |
| | delayed `u64`, one fold per 4,096 | | | | 0.076 |
| 2^31 − 1 | shipped Montgomery | 3.75 | 0.316 | 1.30 | 1.01 |
| | canonical, `%` by constant | 4.01 | 0.530 | 1.35 | 1.12 |
| | canonical, explicit Barrett | 4.01 | 0.430 | 1.15 | 1.18 |
| | **canonical, Mersenne** | **2.50** | **0.177** | **1.00** | **0.83** |
| | Shoup (scatter only) | | | 1.18 | |
| | delayed `u64`, fold every 4 | | | | 1.63 |
| BabyBear | shipped Montgomery | 4.00 | 0.266 | 1.26 | 1.25 |
| | canonical, `%` by constant | 4.51 | 0.513 | 1.29 | 1.22 |
| | canonical, explicit Barrett | 4.01 | 0.437 | 1.24 | 1.15 |
| | Shoup (scatter only) | | | 1.25 | |
| | delayed `u64`, fold every 4 | | | | 1.75 |

At 32 bits Montgomery is already the right general choice. A canonical representation trims
`scatter` 12% at 32003 but loses 1.6x on `map`, which is the case 32-bit Montgomery is fast at
because its reduction is 64-bit arithmetic that vectorizes at eight lanes. Shoup's precomputed
multiplier buys nothing here: the product is already one 64-bit multiply. Delayed reduction is a
16x win on a 32003 dot product, a shape F4 does not run, and a loss at every 31-bit prime, where
the fold comes every four products.

The exception is **2^31 − 1**, where the Mersenne identity beats Montgomery on all four kernels.
#780 shipped it for `Mersenne31` after the end-to-end gate in §3b. In that build the shipped arm at
2^31 − 1 reads 2.50 / 0.213 / 0.956 / 0.830 ns, against 2.50 / 0.187 / 0.996 / 0.835 for the
candidate arm and 3.75 / 0.330 / 1.29 / 1.01 for the raw Montgomery replica (one process, same
protocol, `fa27467a`). Its `map` kernel stays vectorized: `vpmuludq` and `vpsrlq` over `ymm`
registers in the `map::<Shipped32<2147483647>>` symbol.

The raw replica's 32003 `scatter` (1.51 against the shipped 1.26) is code layout, not
representation: the two run the same algorithm, and the replica matches the shipped type to 1% in
every other cell. Treat ±20% on a single scatter cell as within this harness's codegen noise.

### 2.2 64-bit storage (`PrimeFieldElement64`)

| p | arm | chain | map | scatter | dot |
|---|---|---:|---:|---:|---:|
| 2^31 − 1 | shipped Montgomery | 4.51 | 2.33 | 2.14 | 1.53 |
| | `u128 %` (control: `__umodti3`) | 5.76 | 2.08 | 2.13 | 2.31 |
| | Möller–Granlund pre-inverse | 6.01 | 2.39 | 2.07 | 2.52 |
| | **canonical, `u64 %` by constant** | 4.51 | **0.711** | **1.28** | 1.34 |
| | **canonical, Mersenne** | **2.76** | **0.368** | **0.96** | **1.10** |
| | Shoup (scatter only) | | | 1.11 | |
| | delayed `u128`, one fold per 4,096 | | | | 0.63 |
| 1481823929 | shipped Montgomery | 4.51 | 2.17 | 2.15 | 1.51 |
| | **canonical, `u64 %` by constant** | 4.76 | **0.824** | **1.29** | 1.34 |
| | Shoup (scatter only) | | | 1.23 | |
| 4611624995532046337 (62-bit) | shipped Montgomery | 4.63 | 2.20 | 2.37 | 1.76 |
| | `u128 %` | 7.24 | 3.37 | 3.64 | 3.54 |
| | Möller–Granlund pre-inverse | 6.26 | 2.20 | 2.08 | 2.40 |
| | Shoup (scatter only) | | | 1.51 | |
| | delayed `u128`, fold every 16 | | | | 0.88 |
| Goldilocks | shipped Montgomery | 4.62 | 1.99 | 2.39 | 1.77 |
| | Möller–Granlund pre-inverse | 5.51 | 1.77 | 1.77 | 2.06 |
| | Goldilocks reduction | 4.26 | 1.33 | 1.64 | 1.71 |
| | delayed `u128`, fold every product | | | | 4.51 |
| 2^64 − 59 | shipped Montgomery | 4.51 | 2.16 | 2.14 | 1.52 |
| | `u128 %` | 6.09 | 2.64 | 2.66 | 2.60 |
| | Möller–Granlund pre-inverse | 5.51 | 1.71 | 1.70 | 1.90 |
| | delayed `u128`, fold every product | | | | 4.68 |

The finding with leverage: **below 2^32, Montgomery form in 8-byte storage pays for a 128-bit
product it never needed.** The canonical arm's product fits a `u64`, LLVM turns `%` by the constant
into a reciprocal multiply, and `map` runs 3.3x faster and `scatter` 1.7x. The Mersenne reduction
adds another 1.3x on `scatter`. `Zp2147483647` is the type the corpus maps 2^31 − 1 to
(`src/fields/mod.rs`), so this is the arithmetic MQ10/2^31−1 actually runs.

Above 2^32, Montgomery stays. The 128-bit remainder control confirms why it was adopted, 1.2–2.0x
slower on every kernel at the 62- and 64-bit primes. Möller–Granlund's pre-inverse (FLINT `nmod`,
NTL `zz_p`) is faster on throughput kernels and 1.2–1.35x slower on the latency chain, which is
not a clear win.

Shoup is the 64-bit opportunity. With the factor's `floor(f * 2^64 / p)` computed once per row
operation (included in these timings), the scatter kernel runs at 0.52–0.64x of Montgomery for
every `p < 2^63`. Shoup's product of a Montgomery-form coefficient and a canonical factor is
already the Montgomery-form product, so it does not need a representation change. It needs a
prepared-factor hook on `FiniteField` and a change to `DenseAccumulator::subtract_scaled` in
`src/linalg`, which several open issues touch, so it is filed as #779 rather than done here.
It also has to be gated on #269's full-solve protocol, since an arithmetic win on that kernel has
already failed to survive once.

### 2.3 254 bits (`PrimeFieldElement256`, Bn254 Fr)

| arm | chain | map | scatter |
|---|---:|---:|---:|
| shipped 4-limb CIOS | 20.9 | 20.2 | 25.7 |
| ark-ff 0.6 `MontBackend` (no `asm` feature) | 20.8 | 19.4 | 26.2 |

Within 4% either way, and results agree limb-for-limb on every kernel. No change. Arkworks'
`asm` feature (inline `mulx`/`adcx` assembly) is not measured: it is nightly-gated in 0.6, and
Zeebra's policy is to measure the in-crate option before considering a dependency.

### 2.4 Does generic `FiniteField` dispatch cost anything?

No. Each shipped type runs through the kernels' trait-generic path and its raw-word replica
through the same kernels on bare integers. Of 32 paired cells, 28 agree within 3% and the rest
within 4.2%, except two where the bare replica is the *slower* one: 32003 `scatter` (1.20x) and
2^31 − 1 `dot` (1.12x). A wrapper cost cannot make the shipped type faster than its replica, so
those two cells are code layout (§2.1). The kernels are
monomorphized under `lto = "fat"` and `codegen-units = 1`, so nothing is dispatched at run time.

## 3. End-to-end gate: F4 over `Zp2147483647`

Three binaries from one tree, differing only in `src/fields/prime_field_64.rs`: **base**
(Montgomery for every odd `P`), **cand** (canonical `u64 %` below 2^32) and **mers** (cand plus the
Mersenne branch, which is what ships). Six rounds, with arm order rotated each round, pinned to
CPU 3 under `tools/benchlock.sh` (owner `zb-270-e2e`, load 3.5 at start and 3.7 at end).
`examples/mq10_profile 2147483647` runs the digest-pinned MQ10 (`72d0ad31…`), and
`examples/field_width f4` runs cyclic-5 lex and katsura-5/6 grevlex at both storage widths.

| MQ10 / 2^31 − 1 | F4 call ms, median (range) | Paired / base, median (range) | Peak RSS MiB |
|---|---:|---:|---:|
| base | 1457.9 (1395.3–1493.9) | — | 37.6 |
| cand | 1370.1 (1281.9–1373.0) | 0.932 (0.892–0.946) | 35.8 |
| **mers** | **1098.1 (1021.7–1103.7)** | **0.748 (0.704–0.789)** | 37.8 |

All 18 runs produce the same complete reduced basis (one SHA-256 over the emitted basis across
arms). The paired ranges do not overlap parity or each other.

`field_width`'s F4 elimination stage over `Zp2147483647`, median ms, with the `Mersenne31` column,
whose code is unchanged, as an in-process control:

| system, backend | base | cand | mers | `Mersenne31` (control), base → mers |
|---|---:|---:|---:|---:|
| katsura-6, adaptive (shipping) | 2.12 | 2.01 | 1.74 | 2.02 → 1.99 |
| katsura-6, dense | 11.70 | 5.95 | 4.76 | 4.20 → 4.24 |
| katsura-6, sparse | 6.78 | 6.66 | 6.51 | 6.64 → 6.56 |
| katsura-5, adaptive | 0.29 | 0.27 | 0.24 | 0.27 → 0.28 |
| cyclic-5, adaptive | 0.17 | 0.16 | 0.15 | 0.16 → 0.16 |

The control stays flat, which puts the moves in the changed type. The dense backend gains most
(2.5x) because it performs the most multiplications per stored entry. A side effect is that 8-byte
`Zp2147483647` now beats the 4-byte Montgomery `Mersenne31` on the shipping adaptive backend
(1.74 against 1.99 ms on katsura-6). That is the argument for #780.

## 3b. End-to-end gate: `Mersenne31` (#780)

Two binaries of each example, **before** (`a9421093`, Montgomery) and **after** (`fa27467a`, the
Mersenne branch), built from one worktree with the same flags as §1. Fifteen rounds, arm order
alternating each round, every process pinned to CPU 3 under `tools/benchlock.sh` (owner
`zb-780-ab`; 1-minute load 14.7 at start and 12.5 at end, so the absolute figures are noisier than
§3's and the paired ratios are the evidence). Cells are medians over rounds; the ratio is the median
of per-round after/before pairs, with its range.

`examples/field_width f4`, elimination stage in ms. The `Zp2147483647` column is unchanged code and
is the in-process control:

| system, backend | `Mersenne31` before → after | paired | `Zp2147483647` control |
|---|---:|---:|---:|
| katsura-6, adaptive (shipping) | 2.02 → 1.73 | 0.856 (0.84–1.36) | 1.75 → 1.75 |
| katsura-6, dense | 4.23 → 3.72 | 0.877 (0.86–1.16) | 4.78 → 4.79 |
| katsura-6, sparse | 6.76 → 6.19 | 0.913 (0.82–1.38) | 6.52 → 6.53 |
| katsura-5, adaptive | 0.27 → 0.24 | 0.889 (0.55–1.37) | 0.24 → 0.24 |
| cyclic-5, adaptive | 0.16 → 0.15 | 0.938 (0.62–1.50) | 0.15 → 0.15 |

`examples/elimination_kernel_study m31 <shape> 8 <backend>`, the density-curve sources at full
density (8/8). Forward elimination ms, and the whole elimination including back-substitution:

| m31 shape, backend | forward before → after | paired forward | elimination before → after |
|---|---:|---:|---:|
| k7, adaptive | 0.792 → 0.623 | 0.781 (0.76–1.25) | 1.807 → 1.606 |
| k7, dense | 1.887 → 1.711 | 0.901 (0.86–1.23) | 2.891 → 2.702 |
| k7, sparse | 2.574 → 2.544 | 0.988 (0.89–1.59) | 3.660 → 3.590 |
| c6, adaptive | 0.315 → 0.245 | 0.767 (0.75–0.79) | 0.701 → 0.622 |
| c6, dense | 0.344 → 0.306 | 0.890 (0.68–0.93) | 0.723 → 0.680 |
| c6, sparse | 0.588 → 0.573 | 0.966 (0.70–1.00) | 0.992 → 0.972 |
| k6lex, adaptive | 7.810 → 6.049 | 0.771 (0.70–0.80) | 10.884 → 9.004 |
| k6lex, dense | 28.890 → 25.782 | 0.890 (0.88–0.93) | 31.969 → 28.760 |
| k6lex, sparse | 19.661 → 19.325 | 0.982 (0.93–1.02) | 22.930 → 22.468 |

Every source matched its pinned corpus fingerprint, and each shape and backend produced one RREF
hash across all 30 runs. No median regressed; the control column moved by at most 1.8%. The
4-byte type is back level with or ahead of the 8-byte one on the shipping backend (1.73 against
1.75 ms on katsura-6), which §3 had inverted. The sparse backend gains least, as in §3, because its
cost is index traversal rather than multiplication.

## 4. Dispositions

- **#163** (closed): `PrimeFieldElement128` was deprecated rather than converted. This study
  confirms there is no width between 2^64 and 2^128 that needs its own representation.
- **#244** (closed): a compiler-flag problem, not a representation one. `RUSTFLAGS` replaces
  `target.*.rustflags`, so the `x86-64-v3` floor disappeared. This study's binary prints its ISA
  floor, and the `map` gap between 32-bit Montgomery (vectorized) and 64-bit Montgomery (not) is
  the representation-dependent part #244's discussion identified.
- **Delayed reduction**: rejected for elimination by #269's measured gate (above). The exact
  headroom bounds (`u64`: 18,012,146,920 products at 32003, 4 at 2^31 − 1, 0 at 2^64 − 59; `u128`:
  1 at Goldilocks and 2^64 − 59) are unit-tested in the example.

## 5. Reproduce

```text
export CARGO_TARGET_DIR=/buildcache/cargo-target/zeebra-270 RUSTC_WRAPPER=""
cargo build --release -j24 --example field_reduction
tools/benchlock.sh <owner> taskset -c 3 $CARGO_TARGET_DIR/release/examples/field_reduction
```

For the end-to-end gate, build `mq10_profile` and `field_width` (`--features external-runners`)
once per variant of `src/fields/prime_field_64.rs`, then run the three binaries interleaved and
pinned as in §3. §3b is the same with `field_width` and `elimination_kernel_study` built at
`a9421093` and `fa27467a`.
