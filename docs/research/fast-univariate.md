# Fast univariate algorithms: the wide-field root of unity, and what each stage costs

Reference for D2 (#83), a child of the #68 epic and a prerequisite for D3.

Both routes into #68 end in the same place: one univariate polynomial of very large degree over a
large prime field, whose roots are wanted. This records what Zeebra's univariate layer can actually
do there — measured, not estimated — and what it would need to go further.

Every number below comes from

```text
cargo run --release --example univariate_scaling
cargo run --release --example univariate_scaling -- koalabear points=250,500,1000,2000,4000,8192,13123
```

on the development workstation (64 cores, 300 GB RAM; the measurements are single-threaded). The
sweeps shown used `budget=1.0`, one second of wall clock per measurement. The release profile is
the one in `Cargo.toml` — `lto = "fat"`, `codegen-units = 1` — with `-C target-cpu=x86-64-v3` from
`.cargo/config.toml`. Figures added by #162 stage 1 were taken on the same workstation, pinned to
cores 0–7 with `taskset` per `tools/scoreboard.sh`, with the before and after binaries built from
one tree and run interleaved.

**Figures marked superseded are kept rather than overwritten.** Where a later issue re-measures a
stage, the earlier number stays with a pointer to the newer one, because the rest of the table it
sits in was taken in the same run. §3's `lagrange` row, §3.1, §3.2 and §5 all carry such a marker,
all from #162 stage 1.

## 1. The blocker, cleared

`primitive_element` and `root_of_unity` aborted the process for `PrimeFieldElement256`, because
finding a generator of the multiplicative group means factoring a 254-bit `q - 1`
(`MILESTONE-LARGE-PRIME-FIELDS.md` §7, open item 6). **There was therefore no NTT over either wide
field**, and the FFT's only callers were its own tests.

The way out needs no factorization. The multiplicative group of GF(q) is cyclic of order
`q - 1 = 2^s * m` with m odd, so its 2-Sylow subgroup is cyclic of order `2^s`: a primitive
`2^k`-th root of unity exists for `k <= s` and for no larger k. For any non-square z, `z^m`
generates that subgroup, and `z` is a non-square exactly when `(z^m)^(2^(s-1)) != 1` — one test,
passed by half the field, so two draws on average. Both s and m are read off `q - 1` by shifting.

That is `src/fields/two_adic.rs`. `KnownOrder` gained `two_adicity()` and
`two_adic_root_of_unity(log_n, rng)`, `FiniteField` gained `pow_limbs` (the exponent m is 226 bits
for BN254, so `pow`'s `u128` cannot hold it), and `PrimeFieldElement256::root_of_unity` now serves
any power-of-two order. A non-power-of-two order still needs the factorization and still panics;
`primitive_element` is still `unimplemented!()`, because nothing needs it.

### 1.1 The two-adicity figures, verified rather than quoted

§7's note records 28 for BN254 and 32 for BLS12-381. Those values are no longer taken on trust:
`two_adicity()` derives s from the compiled-in modulus, and three independent checks pin the
derivation.

| field | q | s | odd part m | element |
|---|---|---|---|---|
| Mersenne-31 | `2^31 - 1` | **1** | 30 bits | 8 B |
| BabyBear | `2^31 - 2^27 + 1` | **27** | 4 bits | 8 B |
| KoalaBear | `2^31 - 2^24 + 1` | **24** | 7 bits | 8 B |
| Goldilocks | `2^64 - 2^32 + 1` | **32** | 32 bits | 8 B |
| BN254 `Fr` | 254 bits | **28** | 226 bits | 32 B |
| BLS12-381 `Fr` | 255 bits | **32** | 223 bits | 32 B |

1. `test_decomposition_reconstructs_the_group_order` recomputes `2^s * m` with `BigUInt` shifting
   and compares it to `q - 1`, and asserts m odd. It shares no code with the limb walk.
2. `test_two_adicity_agrees_with_the_oracle` compares both wide-field values against
   `ark_ff::FftField::TWO_ADICITY`, which `ark-ff`'s own derive computes from the same decimal
   modulus. This is the oracle check, in the role `ark-ff` already plays for the arithmetic.
3. `test_the_powers_of_a_root_sum_to_zero` checks the cyclotomic identity
   `1 + w + ... + w^(n-1) = 0` and the distinctness of the n powers over BN254 — the property the
   transform actually depends on, which a non-primitive n-th root would fail.

**Mersenne-31 has two-adicity 1.** The field almost every F4 benchmark in this crate runs over
admits no power-of-two transform above size two. That is why the sweep includes KoalaBear. #62's
"equivalent small NTT-friendly prime field" turned out to need no new mathematics: #62 is about
storage width, and `two_adicity` is a property of the order, so `fields::KoalaBear` and
`fields::BabyBear` (now 32-bit backed, s = 24 and 27) report the same values as the 64-bit-backed
types of the same moduli. The sweep uses the 64-bit backing throughout so that
`size_of::<F>()` is 8 across all three narrow fields and the byte figures are comparable; over the
32-bit types every peak figure halves and nothing else changes, since each stage is linear in
`size_of::<F>()`.

### 1.2 The transform is now real over the wide fields

Three new tests exercise what was previously impossible:

- `fft::evaluate::tests::test_evaluate_agrees_with_direct_evaluation_over_bn254_fr` — the
  transform against Horner evaluation at each point, one at a time. No shared code.
- `fft::interpolate::tests::test_evaluate_then_interpolate_over_the_wide_fields` — the round trip
  over both BN254 and BLS12-381.
- `prime_field_256::tests::test_root_of_unity_over_a_wide_field` — exact order `2^k` for
  `k <= 12`, and a panic beyond `2^28`.

Finding the root of unity itself is free relative to the transform it enables: a primitive
`2^20`-th root took **9 µs** and 64 peak bytes over BN254, 1 µs over KoalaBear.

## 2. A defect found by the measurement: division was cubic

The first sweep returned a measured scaling exponent of **2.99** for `div_with_remainder` against
a predicted 2. The cause was in the source rather than in the mathematics: each long-division step
formed `c * x^e` as a polynomial and multiplied it by the divisor through the generic operator, so
the schoolbook product ran over all `e + 1` coefficients of a term that has one. A step cost
`(e + 1) * (deg(divisor) + 1)` rather than `deg(divisor) + 1`, and the sum over e was `d^3 / 2`.

`pow_mod_limbs` reduces once per squaring, so every caller inherited it — root finding over a
254-bit field paid `254 * d^3 / 2`. It is now in-place long division at `d^2`, with one inversion
for the whole division instead of one per step. What it bought:

| field | div reached, before | after | roots reached, before | after |
|---|---|---|---|---|
| KoalaBear | 1 024 | **32 768** (32x) | 512 | **4 096** (8x) |
| Goldilocks | 1 024 | **32 768** (32x) | 256 | **2 048** (8x) |
| BN254 `Fr` | 512 | **8 192** (16x) | 64 | **256** (4x) |

The regression guard is `test_division_at_a_degree_the_cubic_implementation_could_not_reach`:
degree 6 000 by degree 3 000, which does not finish in a 180-second test run against the old code
and takes milliseconds against the new one. A wall-clock assertion would be flaky and nothing in
the suite can count field multiplications, so size is the guard; the `exponent` column of the
example is the direct evidence.

## 3. Measured cost curves

The **exponent** column is `log2(t_i / t_(i-1))` at a doubling size: 1 is linear, 2 quadratic, 3
cubic. It is what makes each complexity claim below a measurement rather than a reading of the
source.

| stage | measured exponent | what it is |
|---|---|---|
| mul | 1.93 – 2.14 → **2** | schoolbook, which is what `Mul` does |
| fftmul | 0.90 – 1.15 → **1** | `multiply` through the transform — **measured separately**, §4.1 |
| div | 1.63 – 2.12 → **2** | in-place long division, after §2 |
| ntt | 0.97 – 1.18 → **1** (n log n) | `fft::evaluate`, recursive — **superseded, see §3.3** |
| intt | 0.92 – 1.18 → **1** | `fft::interpolate`; §3 on what #118 then removed — **superseded, see §3.3** |
| lagrange | 2.68 – 2.98 → **3** | arbitrary abscissae — **superseded, see §4.3** |
| roots | 1.64 – 2.01 → **2** | `roots`, dominated by `x^q mod f` |

**The `lagrange` row is superseded.** #162 stage 1 rewrote `lagrange_interpolate` around one
numerator product and synthetic division; the exponent is now **1.86 – 2.12 → 2** and the figure
above is the pre-#162 measurement, kept because every other row in this table was taken in the same
run. §4.3 has the new curves.

**The `fftmul` row was not taken in that run**, since the stage did not exist then: it is a
`budget=0.25` sweep over KoalaBear backed by a `u64`, which reached size `2^18`. The exponent is
what the row is for and it does not depend on the budget; the reach is not comparable with §3.1's
figures, so it is not entered there. §4.1 has the crossover, which is the measurement that matters
for this stage and which a doubling sweep is too coarse to resolve.

### 3.1 Largest size reached in one second per measurement

| stage | Mersenne-31 | KoalaBear | Goldilocks | BN254 `Fr` |
|---|---|---|---|---|
| mul | 32 768 | 32 768 | 32 768 | 8 192 |
| div | 32 768 | 32 768 | 32 768 | 8 192 |
| ntt | **2** — s = 1 | 8 388 608 | 8 388 608 | 2 097 152 |
| intt | **2** — s = 1 | 4 194 304 | 2 097 152 | 262 144 |
| lagrange | 1 024 | 1 024 | 1 024 | 512 |
| roots | 4 096 | 4 096 | 2 048 | **256** |

**The `lagrange` row is superseded by #162 stage 1**, re-measured in the same way and on the same
workstation. The figures above are the pre-#162 ones; they are kept rather than overwritten because
the rest of the table was taken in the same run:

| stage | Mersenne-31 | KoalaBear | Goldilocks | BN254 `Fr` |
|---|---|---|---|---|
| lagrange, before #162 | 1 024 | 1 024 | 1 024 | 512 |
| lagrange, after #162 | **16 384** | **16 384** | **16 384** | **4 096** |
| factor | 16x | 16x | 16x | 8x |

Absolute cost at the largest size reached, and the peak bytes there:

| field | stage | size | seconds | ns/element | peak bytes |
|---|---|---|---|---|---|
| KoalaBear | mul | 2^15 | 2.19 | 66 821 | 1 048 560 |
| KoalaBear | div | 2^15 | 2.30 | 70 109 | 1 572 848 |
| KoalaBear | ntt | 2^23 | 1.94 | **232** | 469 762 016 |
| KoalaBear | intt | 2^22 | 2.03 | 485 | 301 989 856 |
| KoalaBear | lagrange | 2^10 | 2.74 | 2 677 318 | 65 544 |
| KoalaBear | lagrange, after #162 | 2^14 | 2.39 | 146 044 | 655 368 |
| KoalaBear | roots | 2^12 | 1.72 | 418 695 | 393 176 |
| BN254 `Fr` | mul | 2^13 | 1.59 | 193 550 | 1 048 512 |
| BN254 `Fr` | div | 2^13 | 1.64 | 199 615 | 1 572 800 |
| BN254 `Fr` | ntt | 2^21 | 2.16 | **1 032** | 469 761 920 |
| BN254 `Fr` | intt | 2^18 | 1.89 | 7 209 | 75 497 344 |
| BN254 `Fr` | lagrange | 2^9 | 3.16 | 6 167 733 | 131 104 |
| BN254 `Fr` | lagrange, after #162 | 2^12 | 1.34 | 327 072 | 655 392 |
| BN254 `Fr` | roots | 2^8 | 1.04 | 4 074 934 | 98 144 |

The NTT is the stage in good shape: 232 ns per element over a 31-bit field at size 2^23, 1 032 ns
over a 254-bit one at 2^21 — a 4.5x ratio against the 4x element-width ratio, so the transform is
paying for the wider arithmetic and almost nothing else.

At a matched size of `2^18`, `intt` cost **2.4x** `ntt` over KoalaBear, 5.2x over Goldilocks and
**8.6x** over BN254 when these rows were taken. The gap was inversions: `FFTDomain::inverse`
inverted every one of the n powers individually, and `interpolate` divided each of the n
coefficients by n — which, since `Div` is `mul` by `inverse`, is a second inversion per
coefficient. 2n inversions where two would do, and inversion is the operation whose cost relative
to multiplication grows most with field width, which is why the penalty was largest on the wide
field.

**#118 has since removed it.** Batch inversion in `FFTDomain::inverse` and one hoisted `1/n` in
`interpolate` bring that ratio to **1.02x, 1.07x and 1.10x** respectively, and the largest `intt`
this budget reaches to `2^23`, `2^23` and `2^20`. The `intt` rows in §3.1 are therefore the
pre-#118 figures, kept because every other row in the table was taken in the same run; peak bytes
are unchanged at `9 n B`. See [`batch-inversion.md`](batch-inversion.md) §2.3.

**#161 has since replaced the transform itself.** Every `ntt` and `intt` figure in §3.1 and §3.2
is therefore a pre-#161 figure, kept here because the other four stages' rows were taken in the
same run and are unaffected. §3.3 is the current measurement.

### 3.2 Memory as a function of degree, in bytes

The measured peak is exactly proportional to `n * size_of::<F>()` in every stage, with an integer
constant:

| stage | peak bytes | 64-bit field | BN254 `Fr` |
|---|---|---|---|
| mul | `4 n B` | 32 n | 128 n |
| div | `6 n B` | 48 n | 192 n |
| ntt | `7 n B` — **superseded, now `1 n B`; see §3.3** | 56 n | 224 n |
| intt | `9 n B` — **superseded, now `2 n B`; see §3.3** | 72 n | 288 n |
| lagrange | `8 n B` | 64 n | 256 n |
| roots | `12 n B` | 96 n | 384 n |

The `lagrange` row is **superseded by #162 stage 1 at `5 n B`** — 40 n over a 64-bit field and
160 n over BN254 — and the constant is still exactly integral. It falls rather than rises because
the cubic form held a growing numerator polynomial and its quotient per basis polynomial, where the
quadratic form holds the one numerator product `M` of degree n, the n denominators, the result, and
a copy of the input points. Memory was not the constraint before and is not now; the row is updated
only so that the constant is not quoted stale.

`B = size_of::<F>()`, which is **8 bytes for a 64-bit field and 32 for a 254-bit one — 4x**. That
is deliberately not the **2.5x** `MILESTONE-LARGE-PRIME-FIELDS.md` §5.2 records for the sparse
`(usize, F)` entries the F4 budgets are written in: there the 8-byte index word is paid whatever
the field is, and it dilutes the ratio. A dense univariate coefficient array has no index word, so
the wide field costs the full 4x. **Any byte budget carried over from the F4 side will
under-estimate the univariate layer by 1.6x.**

The constants are unsurprising once named — `mul` holds two inputs and a product of twice the
length, and `UnivariatePolynomial::new` copies the product once; `ntt`'s 7 is the recursive split's
live coefficient and domain vectors summing to a geometric series over the recursion path. They
are reported as measured rather than derived because the measurement is the claim.

**#161 has since removed the transform's share of this.** The two `n B` constants above were the
recursion's, and §3.3 records what replaced them, measured the same way.

### 3.3 The iterative transform (#161), measured against the recursion it replaced

The recursive Cooley–Tukey split in `src/fft/evaluate.rs` was replaced by an iterative in-place
radix-2 kernel: a bit-reversal permutation, then `log n` passes of butterflies over `FFTDomain`'s
own powers read with a stride. `evaluate` and `interpolate` share that kernel, the inverse
direction being the same pass over the batch-inverted domain.

Three costs went with the recursion. Two `i % k` operations per output element per level, where
`k = n / 2` is a runtime value LLVM cannot see is a power of two; `n` twiddle multiplications per
level where `n / 2` suffice, since `w[i + k] = -w[i]`; and an allocation per level, per split half,
and per `UnivariatePolynomial::new` copy.

**Protocol.** Two instances built from one tree — `origin/main` at `418d080` and the same tree with
the kernel replaced — run interleaved as `before, after, before, after`, each `cargo run --release
--example univariate_scaling` with `budget=1.0`, pinned with `taskset --cpu-list 0-7` per
`tools/scoreboard.sh`, `RUSTC_WRAPPER=""` and a private `CARGO_TARGET_DIR`. Release profile,
`-C target-cpu=x86-64-v3` from `.cargo/config.toml`. Each cell below is the **minimum of the two
rounds**, the convention `examples/batch_inversion.rs` already uses: on a shared workstation the
minimum is the least contaminated estimate. `mul`, `div`, `lagrange` and `roots` reached identical
sizes on both sides in both rounds, which is the control.

The pair sits at `418d080` rather than at the merge commit because the two sides have to differ only
by the kernel. Nothing merged after `418d080` touches the measured path: #124 adds `src/fft/multiply.rs`
as a new file and does not rewire `DensePolynomial`'s `Mul`, #165 adds `src/poly/univariate/karatsuba.rs`
and likewise does not, and #159 is linear algebra. The `ntt` and `intt` stages call neither.

#### Peak live heap bytes — measured, not estimated

From the counting global allocator in the example, attributed to the measured call alone. The
constant is exact in every row, as it was before:

| field | stage | before B/element | after B/element | before | after |
|---|---|---|---|---|---|
| KoalaBear (`u64`-backed) | ntt | 56.0 | **8.0** | `7 n B` | **`1 n B`** |
| KoalaBear (`u64`-backed) | intt | 72.0 | **16.0** | `9 n B` | **`2 n B`** |
| Goldilocks | ntt | 56.0 | **8.0** | `7 n B` | **`1 n B`** |
| Goldilocks | intt | 72.0 | **16.0** | `9 n B` | **`2 n B`** |
| BN254 `Fr` | ntt | 224.0 | **32.0** | `7 n B` | **`1 n B`** |
| BN254 `Fr` | intt | 288.0 | **64.0** | `9 n B` | **`2 n B`** |

`1 n B` for `evaluate` is the one `vec![F::zero(); n]` that is zero-padded, transformed in place,
and returned — the output buffer and the only allocation. `2 n B` for `interpolate` is that buffer
plus the inverse domain, which `FFTDomain::inverse` still produces by batch inversion; the
inversion is taken *before* the coefficient buffer exists, so `batch_invert`'s prefix-product
scratch never becomes the maximum. The old `7` and `9` are §3.2's, kept there.

**Estimated, for contrast, and reported separately because it is not a measurement:** a dense
coefficient array of `n` elements is `n * size_of::<F>()` bytes, so a forward transform that writes
into one buffer has a floor of `1 n B` and an inverse that also holds the inverse domain a floor of
`2 n B`. The measured figures are exactly those floors. Nothing above the floor remains to remove
without changing `FFTDomain` — see the follow-up note at the end of this section.

#### Time, and the local scaling exponent

Seconds, and the speedup as the ratio. A dash is a size the side did not reach inside the budget.

| field | log2 n | ntt before | ntt after | speedup | intt before | intt after | speedup |
|---|---|---|---|---|---|---|---|
| KoalaBear | 18 | 0.0472 | 0.0077 | **6.13x** | 0.0414 | 0.0110 | **3.76x** |
| KoalaBear | 19 | 0.0971 | 0.0162 | **5.99x** | 0.0850 | 0.0232 | **3.66x** |
| KoalaBear | 20 | 0.1983 | 0.0358 | **5.54x** | 0.1917 | 0.0444 | **4.32x** |
| KoalaBear | 21 | 0.4046 | 0.0778 | **5.20x** | 0.3914 | 0.1037 | **3.77x** |
| KoalaBear | 22 | 0.8505 | 0.2004 | **4.24x** | 0.8606 | 0.2707 | **3.18x** |
| KoalaBear | 23 | 1.7392 | 0.4536 | **3.83x** | 1.9688 | 0.6110 | **3.22x** |
| KoalaBear | 24 | — | 1.0157 | — | — | 1.3437 | — |
| Goldilocks | 18 | 0.0410 | 0.0076 | **5.39x** | 0.0412 | 0.0104 | **3.96x** |
| Goldilocks | 19 | 0.0915 | 0.0159 | **5.75x** | 0.0925 | 0.0230 | **4.02x** |
| Goldilocks | 20 | 0.1847 | 0.0372 | **4.97x** | 0.1817 | 0.0498 | **3.65x** |
| Goldilocks | 21 | 0.4090 | 0.0838 | **4.88x** | 0.3854 | 0.1077 | **3.58x** |
| Goldilocks | 22 | 0.8236 | 0.2033 | **4.05x** | 0.8363 | 0.2810 | **2.98x** |
| Goldilocks | 23 | 1.7348 | 0.4705 | **3.69x** | 2.0329 | 0.6241 | **3.26x** |
| Goldilocks | 24 | — | 1.0399 | — | — | 1.3648 | — |
| BN254 `Fr` | 18 | 0.1974 | 0.0755 | **2.61x** | 0.2034 | 0.1016 | **2.00x** |
| BN254 `Fr` | 19 | 0.4252 | 0.1607 | **2.65x** | 0.4436 | 0.2145 | **2.07x** |
| BN254 `Fr` | 20 | 0.9169 | 0.3505 | **2.62x** | 0.9861 | 0.4751 | **2.08x** |
| BN254 `Fr` | 21 | 1.9630 | 0.7377 | **2.66x** | 2.2704 | 0.9897 | **2.29x** |
| BN254 `Fr` | 22 | — | 1.5558 | — | — | 2.0691 | — |

The local exponent is unchanged, as it should be — the asymptotic class was never the problem:

| field | stage | before | after |
|---|---|---|---|
| KoalaBear | ntt | 1.03 – 1.21 | 1.07 – 1.37 |
| KoalaBear | intt | 0.91 – 1.19 | 0.94 – 1.38 |
| Goldilocks | ntt | 1.01 – 1.21 | 1.04 – 1.28 |
| Goldilocks | intt | 0.97 – 1.28 | 1.07 – 1.38 |
| BN254 `Fr` | ntt | 0.93 – 1.12 | 1.06 – 1.15 |
| BN254 `Fr` | intt | 1.03 – 1.20 | 1.06 – 1.15 |

Over `2^16` and above, so that the timer resolution does not dominate. The upper end rises on the
narrow fields: at 30 to 60 ns per element the transform is now close enough to memory-bandwidth
bound that the last few doublings cost slightly more than a doubling. That is the right problem to
have next, and it is not this one.

The gain is **3.7x to 6.1x on the narrow fields and 2.0x to 2.7x on BN254**, and the ratio between
those is the point: the recursion's overhead was index arithmetic and allocation, which is a fixed
cost per element, so it is a larger fraction of a cheap field multiplication than of a 254-bit one.
BN254 was already paying mostly for arithmetic, exactly as §3.1 read off the 4.5x-against-4x ratio.

#### Largest size reached in one second

§3.1's figures for the other stages stand; these are the `ntt` and `intt` rows re-measured. The
budget is one second and the reported size is the first one to exceed it.

| field | stage | before | after |
|---|---|---|---|
| Mersenne-31 | ntt / intt | **2** — s = 1 | **2** — s = 1, unchanged |
| KoalaBear | ntt | 2^23 | **2^24** — the field's whole two-adic range, in 1.02 s |
| KoalaBear | intt | 2^23 | **2^24** |
| Goldilocks | ntt | 2^23 | **2^24** |
| Goldilocks | intt | 2^23 | **2^24** |
| BN254 `Fr` | ntt | 2^21 | **2^22** |
| BN254 `Fr` | intt | 2^21 | **2^22** |

KoalaBear's forward transform no longer stops on the budget at all: it stops because
`two_adicity()` is 24 and there is no primitive `2^25`-th root of unity, and `2^24` lands within a
percent of the one-second budget either way. Goldilocks straddles the budget at `2^24` — 1.04 s in
one round and 0.97 s in the other, so the sweep went on to `2^25` in the second. `2^24` is the
figure to quote and the straddle is the honest qualification on it.

The sweep starts at `2^6`, which is above Mersenne-31's maximum transform size of 2, so the example
reports that field as unreachable rather than measuring it. `src/fft/transform.rs`'s tests derive
the highest size from `F::two_adicity()` and so do cover Mersenne-31 at sizes 1 and 2; a request for
a primitive 4th root of unity there panics in `two_adic_root_of_unity`, which is where the bound
belongs.

#### The instruction census

The issue's first claim is about an instruction, not a time, so it is checked the way
`MILESTONE-SIMD-PARALLELISM.md` §4.1 checks for `__umodti3`: disassemble the release artifact,
split it by symbol, and count. `tools/div_census.sh` does it, restricted to symbols under
`zeebra::fft` because a whole-binary count also sees divisions in unrelated code and would not be
attributable.

Over `target/release/examples/univariate_scaling`:

| | `div`/`idiv` under `zeebra::fft` |
|---|---|
| before | **4** — one in each of the four `evaluate` monomorphizations |
| after | **0**, over 17 matching symbols |

One instruction per monomorphization, not two: x86's `div` yields quotient and remainder together,
so LLVM computes `i / k` and `i % k` with a single 32-bit `div` and derives the rest. It sits in the
output loop, so it executes `n` times per level — `n log n` divisions over the transform, about 193
million at `n = 2^23`. The symbols after the change include the four `evaluate` instances and four
new `transform_in_place` instances, so the kernel is a real out-of-line symbol in each
monomorphization and the count is looking at the code that does the work. The counts were taken on
`574a53c`, after #124; the four before-side divisions are the same four at every base since
27cc999.

#### The multiplication crossover moves down one doubling

`fft_multiplication_crossover<F>()` (#124) is a width-indexed threshold on *product* degree —
16384 for a 4-byte element, 2048 for 5–8 bytes, 512 above — and its own doc comment attributes the
lateness to the transform being "bound by allocation and recursion rather than by field
arithmetic". That is the property this change removes, so the threshold is now too high. Measured
the same way #124 measured it, from the example's `mul` and `fftmul` rows:

```text
cargo run --release --example univariate_scaling -- koalabear budget=0.02
cargo run --release --example univariate_scaling -- bn254 budget=0.02
```

A small budget deliberately: the `fftmul` stage asserts its product against `&a * &b`, so its
verification is quadratic in the operand degree and a one-second budget pushes that verification
past operand `2^20`, which does not finish. Milliseconds, minimum of two interleaved rounds,
`taskset --cpu-list 0-7`:

| element | side | operand `2^8` | `2^9` | `2^10` | `2^11` | crossing |
|---|---|---|---|---|---|---|
| 8 B (KoalaBear in `u64`) | before | 0.10 / 0.20 | 0.50 / 0.40 | 1.80 / 0.80 | 7.70 / 1.90 | product degree **1022** |
| 8 B | after | 0.10 / 0.00 | 0.50 / 0.10 | 2.10 / 0.10 | 8.00 / 0.30 | product degree **510** |
| 8 B (Goldilocks) | before | 0.20 / 0.20 | 0.50 / 0.40 | 2.20 / 0.90 | 8.60 / 1.80 | product degree **1022** |
| 8 B (Goldilocks) | after | 0.10 / 0.00 | 0.50 / 0.10 | 2.10 / 0.10 | 8.60 / 0.30 | product degree **510** |
| 32 B (BN254 `Fr`) | before | 1.50 / 0.80 | 6.10 / 1.50 | 24.80 / 3.20 | — | product degree **510** |
| 32 B (BN254 `Fr`) | after | 1.50 / 0.30 | 6.00 / 0.60 | 23.20 / 1.30 | — | product degree **254** |

Each cell is `mul / fftmul`. The `mul` column is unchanged code and agrees between the two sides to
within the print precision, which is the control for this table.

**The crossing moves down exactly one doubling on every field measured.** Rounded up to the next
power of two as #124 does, so the dispatcher never picks the slower route, the thresholds become
**512** for a 5–8 byte element (from 2048) and **256** above 8 bytes (from 512). The 4-byte row is
not measurable from this example — it sweeps the `u64`-backed narrow fields so that
`size_of::<F>()` is 8 throughout — so 16384 is left for whoever re-measures `fields::KoalaBear`
directly. Recalibrating the constant is #124's number and is not changed here; #185's
schoolbook → Karatsuba → NTT dispatch depends on it, and its Karatsuba band narrows at the top by
the same doubling.

#### What is left, and what it would need

`FFTDomain::inverse` is now the only remaining `n`-element allocation in `interpolate`, and
[`batch-inversion.md`](batch-inversion.md) §4 already names the way to remove it: for a domain that
really is the `n` powers of a primitive `n`th root, `w^-i = w^(n-i)`, so the inverse is a
permutation of the domain — zero inversions and zero multiplications. That note recorded the
identity as unavailable "because `FFTDomain` does not record whether it is geometric". The kernel
now *requires* it to be, and checks a necessary condition (`w^(n/2) = -1`) in O(1), so the argument
has changed; making the domain inverse free is a change to a public type's shape and belongs to
whatever next needs `intt` faster. It would take `interpolate` from `2 n B` to `1 n B`.

## 4. The gap list

### 4.1 Multiplication: a quasi-linear path, and a very late crossover

**Closed by #124.** `multiply`, `multiply_above` and `multiply_over_domain` in `src/fft/multiply.rs`
pad to a power of two, transform both inputs, multiply pointwise and invert. The sweep's `fftmul`
row measures exponent 0.90–1.15, against 1.93–2.14 for schoolbook.

`Mul` itself stays schoolbook, and cannot do otherwise: choosing a domain needs a primitive
`2^k`-th root of unity, so it needs `KnownOrder` and a source of randomness, neither of which
`Mul`'s signature can carry — and `KnownOrder` is exactly what the Gröbner core refuses to require
of a coefficient type (`test_the_grobner_stack_needs_no_field_cardinality`). Mersenne-31, whose
two-adicity of 1 rules the transform out entirely, needs no CRT or Kronecker fallback for
correctness: `multiply` falls back to the schoolbook product on precisely that failure.

**The crossover is much later than the asymptotics suggest, and it is not one number.** Medians of
21 interleaved runs pinned to one core, as the ratio of schoolbook time to transform time against
the degree of the product:

| product degree | KoalaBear (4 B) | Zp65537 (8 B) | Goldilocks (8 B) | BN254 `Fr` (32 B) |
|---:|---:|---:|---:|---:|
| 256 | 0.03x | 0.23x | 0.20x | 0.61x |
| 1024 | 0.10x | 0.84x | 0.73x | **2.1x** |
| 2048 | 0.19x | **1.5x** | **1.4x** | 4.1x |
| 8192 | 0.70x | 5.7x | 5.5x | 12.7x |
| 16384 | **1.3x** | 11.7x | 10.4x | 23.6x |

Schoolbook wins until degree ~460 over a 254-bit field, ~1500 over a 64-bit one and ~12000 over a
32-bit one — a 26x spread. `fft_multiplication_crossover::<F>()` is therefore indexed by
`size_of::<F>()`, at 512, 2048 and 16384, each rounded up from the measurement so the dispatcher
never picks the slower route.

**The spread is a finding about the transform, not about the fields.** At degree 16384 it takes the
same 13 ms over KoalaBear, Zp65537 and Goldilocks, three fields whose schoolbook times there differ
by 9x. So this NTT is bound by allocation and recursion rather than by field arithmetic: `evaluate`
rebuilds coefficient vectors and re-splits the domain at every level of the recursion. `fftmul`'s
peak is **208 bytes per element** — 26 `n B` — against 32 for schoolbook and 56 for a single
`evaluate`, for a computation that is three transforms. An in-place iterative transform would move
all three crossovers at once, and is now the highest-value piece of work in the layer.

**#165 adds the third route, between the two.** Karatsuba is `n^log2(3)`: subquadratic, not
quasi-linear, so the heading above still holds and the transform is still the only quasi-linear
path. What it does is own the band `fft_multiplication_crossover` leaves to schoolbook. Its own
crossover is 48 coefficients at 4 bytes an element, 16 at 8 and 4 above that, against the
transform's 16384, 2048 and 512 — so the band Karatsuba owns is **three orders of magnitude wide
on the narrow fields** and it includes every degree `pow_mod`, `gcd` and `separate_equal_degree`
reach today. It also needs nothing from the field but a ring, so unlike the transform it is
available over Mersenne-31 without falling back. §4.1.1 measures it.

The transform-size ceiling is worth stating as a real bound rather than an asymptotic one: `2^24`
for KoalaBear, `2^28` for BN254, `2^32` for Goldilocks and BLS12-381. At `7 n B`, BN254's full
`2^28` ceiling was **60 GB** and, extrapolating from 1 032 ns/element, about **5 minutes** — so
even then the two-adicity bound, not this workstation, was what bound BN254; BLS12-381's `2^32`
would have needed 962 GB, so there memory bound first, at roughly `2^30`.

**Both figures are superseded by §3.3.** At `1 n B` and 366 ns/element, BN254's `2^28` ceiling is
**8.6 GB** and about **100 seconds**, and BLS12-381's `2^32` is **137 GB** — which fits on this
workstation, so **memory no longer binds anywhere**: every field's transform is bound by its own
two-adicity. KoalaBear's whole range now runs in under a second (§3.3).

#### 4.1.1 Karatsuba, measured per element width (#165)

`src/poly/univariate/karatsuba.rs` multiplies two coefficient slices by recursive three-way
Karatsuba down to a schoolbook base case. It is a standalone helper, called from nothing yet:
`Mul` is untouched and `fft::multiply`'s two `a * b` call sites — below its crossover, and on the
no-suitable-domain fallback — are where it belongs and are left for the follow-up. So every
`mul`, `div` and `roots` figure in §3 stands unchanged and is **not** superseded. What follows
measures the helper directly.

`examples/karatsuba_crossover.rs` is the instrument. Both arms are the same code differing only in
the base case — `usize::MAX` never recurses and so is plain schoolbook — so the inner kernel is
identical on both sides and the measured difference is the recursion and nothing else. Each
figure is an arm's fastest over up to 9 interleaved passes, `taskset`-pinned to cores 0–7, release
profile (fat LTO, one codegen unit, `-C target-cpu=x86-64-v3`):

```
cargo run --release --example karatsuba_crossover
```

The base case is **not one number**, and that is the result worth recording:

| field | element | base case = crossover | first measured win | speedup at `2^14` | `(n/B)^0.415` predicts |
|---|---|---|---|---|---|
| Mersenne-31 / KoalaBear (`u32`) | 4 B | **48** | n = 64, 1.14x | **10.7x** | 11.3x |
| Mersenne-31 (`u64`) | 8 B | **16** | n = 16, 1.18x | **17.9x** | 17.8x |
| Goldilocks | 8 B | **16** | n = 16, 1.10x | **16.9x** | 17.8x |
| BN254 `Fr` | 32 B | **4** | n = 16, 1.70x | **22.9x** | 31.6x |

The crossover *is* the base case, by construction rather than by measurement: below it the helper
takes the schoolbook branch and is the same code, so there is nothing to cross. The column beside
it is the smallest **measured** size at which the fastest Karatsuba arm beat schoolbook; the sweep
doubles, so it brackets rather than lands on the base case.

The base case falls **12x** across the widths, in the direction the cost of one field
multiplication predicts: a 4-byte multiply is cheap and its schoolbook inner loop vectorizes, so
the extra additions have to be amortized over a much larger leaf than they do over a 254-bit
field, where the measurement wants to recurse almost all the way down. Carrying one threshold
across the widths is not free — at `2^14`, using 16 everywhere costs **1.53x** on the 4-byte field
and 1.21x on BN254; using 48 everywhere costs 1.46x on the 8-byte fields and **1.84x** on BN254.

Scaling exponents, least-squares over `2^9 … 2^14` at the base case above:

| field | schoolbook | Karatsuba |
|---|---|---|
| Mersenne-31 (4 B) | 2.001 | **1.595** |
| Mersenne-31 (8 B) | 1.989 | **1.589** |
| Goldilocks | 1.990 | **1.584** |
| BN254 `Fr` | 2.015 | **1.613** |

Against schoolbook's 2.00 and `log2(3) = 1.585`. The exponent has moved, and the measured
speedups track `(n/B)^(2 - log2(3))` to within 5% on three of the four fields, which is the check
that the recursion is firing all the way down rather than being a constant-factor win mislabelled.
BN254 is 28% under its prediction, and that residue is the per-level additions and the
`z1 = t - z0 - z2` passes, which are relatively dearer there because a base case of 4 makes the
recursion 12 levels deep rather than 10.

Peak live heap bytes, same counting allocator as §3.2, measured at `n = 1024`:

| path | estimated | measured at `n = 1024` |
|---|---|---|
| slice schoolbook | `2 n B` | 2.00 `n B` |
| slice Karatsuba | `6 n B` | 5.93–5.96 `n B` |
| `Mul` (§3.2's `mul` row) | `4 n B` | 4.00 `n B` |
| Karatsuba through `UnivariatePolynomial::new` | `6 n B` | 5.93–5.96 `n B` |

The measured column approaches the estimate from below and reaches it: 5.47 `n B` at n = 128,
5.93 at 1 024, 6.00 at 16 384, the shortfall being the `-1` per recursion level.

The `6 n B` is the `2 n B` output plus a `4 n B` scratch arena: one allocation for the whole
recursion rather than a `Vec` per node, with each level carving `4 ceil(m/2) - 1` elements for
`a0 + a1`, `b0 + b1` and their product, and the series summing to `4 m`. It is **1.5x** `Mul`'s
`4 n B`, not more, because the arena is freed before `UnivariatePolynomial::new` copies — so the
two peaks do not stack. Whole-process peak resident for the sweep over all four fields was 7.7 MB.

No null result to report: Karatsuba wins on every field measured, including the 4-byte narrow one,
once the base case is the measured one. The honest limit is the one the issue stated in advance —
at the degrees this crate reaches today the gain is a constant-factor 10–23x, not a change in
which degrees are reachable, and `div` is not Karatsuba and will not move.

### 4.2 Modular composition: absent

`Polynomial::compose` computes `f(g)` **unreduced**, as `sum a_i * g^i` with `g.pow(i)` recomputed
per term. Its output has degree `deg(f) * deg(g)`, so it cannot be used where `f(g) mod h` is
wanted, and its only caller is `shift` (composition with `x + k`). There is no Brent–Kung, no
baby-step/giant-step structure, and no modular composition of any kind. Brent–Kung would need
`sqrt(d)` modular powers of g held at once — `sqrt(d) * d * B` bytes, which at `d = 2^20` over
BN254 is 34 GB against the 0.4 GB a multiplication at that degree needs. The issue's note that
composition's memory profile is worse than multiplication's is borne out by that arithmetic.

### 4.3 Multipoint evaluation and interpolation: quadratic, no longer cubic

Two things exist and neither is quasi-linear:

- `fft::evaluate` / `fft::interpolate` are `O(n log n)` but only over a **geometric power-of-two
  domain** `1, w, w^2, ...`. They cannot evaluate at an arbitrary point set, which is what an
  evaluation–interpolation resultant needs.
- `lagrange_interpolate` handles arbitrary abscissae and is **quadratic**, measured at 1.86 – 2.12
  across the four fields. It was cubic at 2.97 when this section was first written; #162 stage 1
  changed that and §4.3.1 is the measurement.

There is still **no subproduct tree**: no routine builds `prod (x - x_i)` as a balanced binary
tree, no simultaneous remaindering down such a tree, and no fast transposed form for interpolation.
That machinery — a subproduct tree plus fast division by Newton iteration — is what would make this
`O(n log^2 n)`, it is what D1's evaluation–interpolation route wants for the degrees §5 is about,
and it does not exist in any partial form. #162 remains open for it. Nor is there multipoint
*evaluation* at arbitrary points in any form better than `n` separate Horner passes.

#### 4.3.1 What #162 stage 1 changed, measured

The cubic form built each of the n Lagrange basis polynomials by multiplying up `n - 1` linear
factors against a product that grows to degree `n - 1` — `O(n^2)` apiece, `O(n^3)` for the n of
them. The quadratic form builds `M(x) = prod_i (x - x_i)` **once** and recovers each basis
polynomial as `M(x) / (x - x_j)` by synthetic division by the linear factor, which is `O(n)` each.
The denominator is `M'(x_j)`, taken as the equivalent product `prod_{k != j} (x_j - x_k)` so that
all n of them are in hand before the divisions and can go through `batch_invert` — one field
inversion rather than n, which is worth most over BN254, where the ratio of inversion to
multiplication is largest.

Same command, `budget=1.0`, the two binaries built from the same tree and interleaved:

| field | before | after | exp. before | exp. after | bytes before | bytes after |
|---|---|---|---|---|---|---|
| Mersenne-31 | 2.67 at 1 024 | 2.38 at 16 384 | 2.96 | 1.90 | 65 544 | 655 368 |
| KoalaBear | 2.54 at 1 024 | 2.39 at 16 384 | 2.89 | 2.00 | 65 544 | 655 368 |
| Goldilocks | 2.71 at 1 024 | 2.75 at 16 384 | 2.93 | 2.12 | 65 544 | 655 368 |
| BN254 `Fr` | 2.80 at 512 | 1.34 at 4 096 | 3.03 | 2.00 | 131 104 | 655 392 |

The exponent column is the last row's, `log2(t_i / t_{i-1})` at a doubling size, and the peak-bytes
columns are at each side's own largest n — a 16x larger n at `5 n B` against `8 n B`, so ten times
the bytes for sixteen times the degree. At **matched** n the memory falls: `8 n B` to `5 n B`,
§3.2.

The exponent is the figure that matters, not the speedup: a measured 2.97 moving to a measured
2.00 is what distinguishes this from a constant-factor win that would wash out at larger n. At
n = 1 024 over KoalaBear the speedup is **270x** (2.541 s to 0.0094 s) and it grows with n, which
is what an exponent that moved by one means.

Two things pin correctness. Duplicate abscissae were previously rejected only incidentally, by an
`assert_eq!(remainder, zero)` after dividing by the scalar denominator; the quadratic form divides
by the *product* of the differences and `batch_invert` leaves a zero alone, so the check is now an
explicit pass over the abscissae before any arithmetic, and two tests pin it. And the cubic form is
kept as `interpolate_reference`, `#[cfg(test)]`, which the new tests diff against over all four
fields and exhaustively over GF(7) — and which the subproduct tree of stage 2 can use the same way.

#### 4.3.2 At the point counts the resultant actually needs

`resultant-elimination.md` §4.1 measures this function at 250 / 500 / 1 000 / 2 000 points over
KoalaBear and finds the four-round CICO row needs **13 123**. Those counts are not powers of two,
so they are measured directly:

```text
cargo run --release --example univariate_scaling -- koalabear points=250,500,1000,2000,4000,8192,13123
```

Over the `u32`-backed `KoalaBear` the resultant runs on, two interleaved passes, mean of the two:

| points | §4.1, as recorded | before, here | after | after / before |
|---:|---:|---:|---:|---:|
| 250 | 28.6 ms | 20.7 ms | 0.52 ms | 40x |
| 500 | 219.4 ms | 169.8 ms | 2.05 ms | 83x |
| 1 000 | 1 632 ms | 1 296 ms | 8.30 ms | 156x |
| 2 000 | 12 880 ms | 10 540 ms | 32.1 ms | 328x |
| 13 123 | ~1 hour, extrapolated | 2 978 s, extrapolated | **1.37 s, measured** | **2 170x** |

The `before` column is 20–30% under §4.1's, which was taken on the same workstation at a different
time; the per-doubling factor is the same 7.3x – 8.5x, so the shape agrees and only the constant
differs. The `after` column's per-doubling factor is **3.7x – 4.4x**, i.e. 4x, i.e. an exponent of
2.

The 13 123 row is the useful one, and on the new side it is **measured rather than extrapolated**:
1.37 s. Extrapolating the quadratic growth from 2 000 points predicts 1.38 s, so the extrapolation
and the measurement agree to 1%, which is the check that the curve really is the curve. Over BN254
`Fr` the same count takes **13.2 s** measured, against 48 140 s — 13.4 hours — extrapolated from
the cubic form.

So the hour §4.1 attributes to the interpolation in the four-round row is now **1.4 seconds**, and
its ranked fix-list reorders: the interpolation is no longer first.

### 4.4 Root finding: quadratic, and it is the binding stage

`roots` computes `gcd(f, x^q - x)` with `pow_mod_limbs(&x, F::order_limbs(), f)`, then splits with
`separate_equal_degree`. The cost is `O(log q)` polynomial multiplications and divisions at the
working degree, so with both of those quadratic the whole stage is quadratic — measured at 1.93 on
KoalaBear and 1.97 on BN254 — with a `log q` factor that is 31 for KoalaBear and 254 for BN254.

That factor is visible at matched degree: at d = 256 BN254 takes **1.043 s** against KoalaBear's
**0.0081 s**, a 129x ratio. Two measured quantities predict most of it — the exponent is 254 bits
against 31, so 8.2x the squarings, and a multiplication at that degree costs 11.1x more (the `mul`
stage at the same size) — which together give 91x. The measurement is 1.4x above that, and the
residue is inversions again: the equal-degree splitter and the gcd both invert, and inversion is
relatively dearer over the wide field than multiplication is.

## 5. Largest reachable degree, and the first stage to fail

**The first stage to stop is now `roots` on every field** — 4 096 on KoalaBear, 2 048 on
Goldilocks, 256 on BN254 `Fr` — at one second per measurement. Arbitrary-point interpolation was
the first stage to stop on the three narrow fields when this section was written, at n = 1 024;
#162 stage 1 took it to 16 384 (§4.3.1) and it is no longer the binding stage anywhere. The
pre-#162 conclusion is kept here as the record of what the sweep said then:

> The first stage to stop is **arbitrary-point interpolation** (n = 1 024) on the narrow fields and
> **root finding** (d = 256) on BN254, at one second per measurement.

Both the old and the new binding stage are quasi-linear in the literature and
quadratic-or-worse here, so what changed is which one binds, not the character of the finding. The
NTT, the one stage with a quasi-linear implementation, reaches `2^23` in the same second —
**`2^24` after #161, which is KoalaBear's two-adic ceiling; see §3.3.**

Extrapolating the measured quadratic growth of root finding to `d = 2^20`, which is the order of
degree the resultant route would produce:

| field | from | to `d = 2^20` | memory at `12 n B` |
|---|---|---|---|
| KoalaBear | 1.72 s at 2^12 | 2^16 x → **~31 hours** | 100 MB |
| BN254 `Fr` | 1.04 s at 2^8 | 2^24 x → **~202 days** | 403 MB |

**Memory is not the constraint anywhere.** Every stage is linear in n at a small constant, and this
workstation has 300 GB; root finding at `d = 2^20` over BN254 wants 403 MB. Time is the constraint,
and it is the constraint because the quasi-linear algorithms are missing, not because the degrees
are intrinsically out of reach.

What quasi-linear multiplication is worth, now that it exists: one multiplication at degree `2^20`
over BN254 is three transforms of size `2^21`, so about 6.5 s — **2.2 s after #161, from §3.3's
0.7377 s per transform.** Root finding needs `O(log q)` of them — 254 squarings, each a multiply
plus a reduction, and a Newton-iteration reduction is a few multiplies — so on the order of **1 to
2 hours** before #161 and **25 to 45 minutes** after, against 202 days. A ~3 000x gap before, ~6
000x now, of which #124 takes the multiplication half; the rest is a subproduct tree away.

### 5.1 What this means for D1's reachable degrees, after #162 stage 1

The claim this section used to carry — that the degrees D1's evaluation–interpolation resultant
would produce are out of reach — stands, but **the interpolation is no longer the reason**. The
sample count a resultant of two degree-d bivariates needs is `O(d^2)`; the four-round `t = 16` CICO
row needs 13 123 of them, which was an hour of interpolation (`resultant-elimination.md` §4.1) and
is now **1.37 s** over KoalaBear and **13.2 s** over BN254, measured (§4.3.2). Extrapolating that
quadratically:

| samples | KoalaBear | BN254 `Fr` | what needs it |
|---:|---:|---:|---|
| 13 123 | **1.37 s** | **13.2 s** | four rounds, `t = 16` — measured |
| 2^20 | ~2.4 hours | ~23 hours | the `d = 2^20` row above |
| 2^24 | ~26 days | ~8 months | — |

So the quadratic form carries the four-round row outright and runs out near `2^20` samples, which
is where root finding also runs out — 31 hours on KoalaBear, 202 days on BN254. **The two stages
now bind at comparable degrees**, where before the interpolation bound the narrow fields four
doublings earlier than anything else in the layer. That is the useful change, and it is why §6's
ranked list keeps its order: the subproduct tree stays third because it is now worth what an
asymptotic improvement is worth, and not what a missing implementation is worth.

## 6. Go / no-go for #68

**Superseded in part.** [`elimination-beyond-grobner.md`](elimination-beyond-grobner.md) is the
epic-level assessment, written against six primary sources including the technical disclosures of
two of the three official 2026 CICO-2 solutions. Three things change for this section:

- the transform ceiling is set by the **smooth part** of `q - 1`, not the two-adicity alone, so
  KoalaBear reaches `2^24 · 127` with a mixed-radix FFT rather than stopping at `2^24`;
- **half-gcd** is a fourth gap, since `gcd.rs` is plain Euclid — but the published univariate route
  needs neither it nor Newton division nor a subproduct tree;
- the `R_P = 8` challenge was solved by interpolation plus Graeffe root finding at degree `3^13`,
  which needs a `2^22` transform — **inside** the ceiling this document measured. That named an
  NTT-based multiply as the single blocker; #124 built it, so §5 of that document is the current
  gap list. Two caveats carry over to the multiply: it rounds up to a power-of-two domain, so it
  inherits the two-adicity ceiling rather than the smooth-part one until #125 lands mixed-radix
  sizes, and §4.1's crossover means it is the slower route below degree ~460 to ~12000 depending
  on the field.

**Not a no-go, but the governing constraint is not where the epic placed it.** #68 assumed the
univariate stage would be "FFT/NTT-dominated, and reportedly bound by memory access". On this
codebase it is neither: the NTT is the healthiest stage in the layer, memory is not binding at any
degree reachable in reasonable time, and the cost is in stages that are quadratic or cubic because
no fast algorithm for them has been written.

Concretely, before D1 or D3 can run at interesting degrees:

1. ~~**NTT-based multiplication** (`O(n log n)`), with a fallback for low-two-adicity fields.~~
   Done, #124 — but the measured crossover is degree ~460 to ~12000 depending on element width,
   because the transform is allocation-bound. ~~**An in-place iterative NTT** is what now carries
   this item's value: it would lower every crossover and speed every stage below that uses one.~~
   Done, #161: the transform is no longer allocation-bound (`1 n B` against `7 n B`) and is 3.7x to
   6.1x faster on the narrow fields and 2.0x to 2.7x on BN254 (§3.3). **`fft_multiplication_crossover`
   was calibrated against the recursive kernel and is therefore now too high** — see §3.3's closing
   note.
2. **Fast division by Newton iteration**, which `pow_mod_limbs` would then inherit, taking root
   finding from `log q * d^2` to `log q * d log d`.
3. **A subproduct tree**, for multipoint evaluation and interpolation at arbitrary points, taking
   interpolation from `O(n^2)` to `O(n log^2 n)` and giving multipoint *evaluation* its first
   sub-quadratic path. #162 stage 1 made interpolation quadratic without it, so this is now an
   asymptotic improvement over a working stage rather than the only route to one; it is still what
   D1 wants above `2^20` samples, and §4.3's reference implementation is what a tree would be
   differentially tested against. #162 stays open for it.
4. **Modular composition** (Brent–Kung) only if D3's Graeffe route needs it; its memory profile is
   the one place where this workstation's 300 GB could genuinely bind.

D3's experimental half is unblocked in the narrow sense — there is now an NTT over the wide fields,
which there was not — but the degrees it can reach are set by items 1 and 2.
