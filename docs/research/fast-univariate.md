# Fast univariate algorithms: the wide-field root of unity, and what each stage costs

**Measured at:** publication bound `29ce42b4`…`b9c104be` for everything but §4.3.3 — the commits
that published those figures, recovered from git rather than recorded at the time
([§10](external-comparison-protocol.md#10-the-commit-and-what-a-publication-bound-is)). **§4.3.3
was taken at `1154bf5b` plus the change it measures**, recorded at the time rather than recovered;
its `from_zeros` subsection at `bccad1fc` plus that change.

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
sits in was taken in the same run. §3, §3.1, §3.2, §4.1, §4.1.1, §4.1.2, §5 and §6 all carry such
markers, from #118, #161, #162, #185, #189, #193 and #244 — the marker names the issue that
re-measured, so the enumeration here is a pointer rather than the record.

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
| fftmul | 1.03 – 1.27 → **1** | `multiply` through the transform — **measured separately and re-taken after #189**, below |
| div | 1.63 – 2.12 → **2** | in-place long division, after §2 — **superseded, see §4.5** |
| ntt | 0.97 – 1.18 → **1** (n log n) | `fft::evaluate`, recursive — **superseded, see §3.3** |
| intt | 0.92 – 1.18 → **1** | `fft::interpolate`; §3 on what #118 then removed — **superseded, see §3.3** |
| lagrange | 2.68 – 2.98 → **3** | arbitrary abscissae — **superseded twice, see §4.3.1 then §4.3.3** |
| roots | 1.64 – 2.01 → **2** | `roots`, dominated by `x^q mod f` — **superseded, see §4.5** |

**The `div` and `roots` rows are superseded by #193.** Division now dispatches to Newton inversion
of the reversed divisor above a measured crossover, which takes `div` to **1.52 – 1.61** over
KoalaBear and **1.57 – 1.62** over BN254 `Fr`. `roots` is `O(log q)` multiplications *and*
divisions at the working degree, so it moved with it, to **1.51 – 1.78** and **1.63 – 1.87**. The
figures above are the pre-#193 ones, kept because the rest of the table was taken in the same run.
§4.5 has the new curves, the crossover and the dispatch rule.

**The `lagrange` row is superseded.** #162 stage 1 rewrote `lagrange_interpolate` around one
numerator product and synthetic division; the exponent is now **1.86 – 2.12 → 2** and the figure
above is the pre-#162 measurement, kept because every other row in this table was taken in the same
run. §4.3 has the new curves.

**The `fftmul` row was not taken in that run**, since the stage did not exist then, and it has
been re-taken twice. §4.1 has the crossover, which is the measurement that matters for this stage
and which a doubling sweep is too coarse to resolve.

**The first `fftmul` figure was checker-limited, and is kept labelled as such.** It was a
`budget=0.25` sweep over KoalaBear backed by a `u64`, reaching size `2^18`, exponent
**0.90 – 1.15**. The budget was small by necessity rather than by choice: the stage asserted its
product against `&a * &b`, so its *verification* was `O(n^2)` while its subject is quasi-linear, and
`budget=1.0` drove the check past operand `2^20` — on the order of `10^12` field multiplications,
which never finished. **`2^18` is therefore where the checker stopped, not where the multiply did**,
and the defect got worse as the code improved: #161 made the transform 3.7–6.1x faster on the
narrow fields, so the quadratic check dominated one doubling earlier each time.

**#189 fixed the instrument**: the stage now checks against schoolbook only up to `n = 2^12`,
where that check is milliseconds, and above it checks evaluation agreement at four random points,
`O(n)` a point. The sweep states which it performed, on the line under each curve. Re-taken:

| `fftmul` over KoalaBear in a `u64` | budget | reached | seconds there | peak bytes | exponent | what set the ceiling |
|---|---:|---:|---:|---:|---|---|
| before #189 | 0.25 s | `2^18` | — | — | 0.90 – 1.15 | **the schoolbook check** |
| after #189 | 1.0 s | **`2^22`** | 1.60 | 402 653 184 | 1.03 – 1.27 | the budget, on the multiply |

`2^22` = 4 194 304, a **16x** larger operand than the checker-limited figure, and the stop is
`4194304 exceeded the budget` — the multiply's own 1.60 s, with the two-adicity ceiling of `2^23`
for this stage over this field still unreached. The exponent range excludes the `n = 128` row,
whose 14 µs is dominated by fixed overhead; from `n = 256` up it is 1.03 – 1.27 and the claim the
row makes is unchanged. Peak is exactly `96` bytes per operand element throughout, i.e. `12 n B` at
`size_of::<F>() = 8`.

Correctness coverage is not reduced. Full schoolbook agreement still runs on every row to
`n = 4096`, which is far past the degrees the unit tests use, and
`src/fft/multiply.rs`'s own suite covers the identity directly:
`test_the_transform_agrees_with_schoolbook` checks `try_multiply_via_fft` against `&a * &b` over
five fields including the power-of-two product-length boundary, and
`test_the_dispatcher_agrees_with_schoolbook_either_side_of_the_crossover` covers the route choice.
Above `n = 4096` a wrong product differs from the true one by a nonzero polynomial of degree at
most `2n - 2`, so four independent random points miss the error with probability below `2^-40` at
`n = 2^20` over a 31-bit field.

Protocol for the re-take: the 128-logical-core / 500 GB development workstation, one core
(`taskset --cpu-list 8`), release profile with the repository's default `Cargo.toml` settings (fat
LTO, `codegen-units = 1`) and `-C target-cpu=x86-64-v3` from `.cargo/config.toml`,
`RUSTC_WRAPPER=""` and a private `CARGO_TARGET_DIR`, under [`tools/benchlock.sh`](../../tools/benchlock.sh) — the run
queued 59 s behind another holder and its `START`..`END` window overlaps no other, per the lock's
log. Single-shot: the figure being reported is a 16x change in reach and a scaling exponent, not a
ratio this machine's ~6% run-to-run variation could move.

```sh
tools/benchlock.sh agentD env CARGO_TARGET_DIR="$PWD/target" RUSTC_WRAPPER="" \
  timeout --signal=INT --kill-after=60s 1800 \
  taskset --cpu-list 8 target/release/examples/univariate_scaling koalabear budget=1.0
```

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
| lagrange, after #162 stage 1 | **16 384** | **16 384** | **16 384** | **4 096** |
| factor | 16x | 16x | 16x | 8x |

**And again after #162 stage 2**, the subproduct tree. Only the two fields the absolute-cost table
below reports were re-taken:

| stage | KoalaBear | BN254 `Fr` |
|---|---|---|
| lagrange, after stage 1 | 16 384 | 4 096 |
| lagrange, after stage 2 | **65 536** | **16 384** |
| factor against stage 1 | 4x | 4x |
| factor against the cubic form | **64x** | **32x** |

`roots` is unchanged at 8 192 and 512 by stage 2, because interpolation is not in it — see §4.3.3.

**The `div` and `roots` rows are superseded by #193**, likewise re-measured on the same workstation
under the same protocol. Only the two fields the absolute-cost table below reports were re-taken:

| stage | KoalaBear | BN254 `Fr` |
|---|---|---|
| div, before #193 | 32 768 | 8 192 |
| div, after #193 | **65 536** | **32 768** |
| factor | 2x | **4x** |
| roots, before #193 | 4 096 | 256 |
| roots, after #193 | **8 192** | **512** |
| factor | 2x | 2x |

`roots` doubling is the result the issue was filed for. It is `O(log q)` multiplications **and
divisions** at the working degree — 31 of each over KoalaBear, 254 over BN254 — so division is half
of what the binding stage does, and halving its exponent had to move the stage or the premise was
wrong.

Absolute cost at the largest size reached, and the peak bytes there:

| field | stage | size | seconds | ns/element | peak bytes |
|---|---|---|---|---|---|
| KoalaBear | mul | 2^15 | 2.19 | 66 821 | 1 048 560 |
| KoalaBear | div | 2^15 | 2.30 | 70 109 | 1 572 848 |
| KoalaBear | div, after #193 | 2^16 | 1.07 | 16 302 | 5 242 496 |
| KoalaBear | ntt | 2^23 | 1.94 | **232** | 469 762 016 |
| KoalaBear | intt | 2^22 | 2.03 | 485 | 301 989 856 |
| KoalaBear | lagrange | 2^10 | 2.74 | 2 677 318 | 65 544 |
| KoalaBear | lagrange, after #162 | 2^14 | 2.39 | 146 044 | 655 368 |
| KoalaBear | lagrange, after stage 2 | 2^16 | 2.80 | 42 688 | 19 661 568 |
| KoalaBear | roots | 2^12 | 1.72 | 418 695 | 393 176 |
| KoalaBear | roots, after #193 | 2^13 | 1.25 | 152 537 | 1 048 512 |
| BN254 `Fr` | mul | 2^13 | 1.59 | 193 550 | 1 048 512 |
| BN254 `Fr` | div | 2^13 | 1.64 | 199 615 | 1 572 800 |
| BN254 `Fr` | div, after #193 | 2^14 | 1.00 | 61 011 | 5 242 112 |
| BN254 `Fr` | ntt | 2^21 | 2.16 | **1 032** | 469 761 920 |
| BN254 `Fr` | intt | 2^18 | 1.89 | 7 209 | 75 497 344 |
| BN254 `Fr` | lagrange | 2^9 | 3.16 | 6 167 733 | 131 104 |
| BN254 `Fr` | lagrange, after #162 | 2^12 | 1.34 | 327 072 | 655 392 |
| BN254 `Fr` | lagrange, after stage 2 | 2^14 | 2.87 | 175 084 | 15 467 760 |
| BN254 `Fr` | roots | 2^8 | 1.04 | 4 074 934 | 98 144 |
| BN254 `Fr` | roots, after #193 | 2^9 | 1.87 | 3 650 070 | 262 464 |

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

A small budget deliberately, and at the time necessarily: the `fftmul` stage then asserted its
product against `&a * &b`, so its verification was quadratic in the operand degree and a
one-second budget pushed that verification past operand `2^20`, which does not finish. **#189 has
since removed that constraint** — the stage checks against schoolbook only to `n = 2^12` and by
evaluation agreement above it — so this table's budget is no longer forced, but the figures are
kept as taken. The crossover is a small-degree measurement and a larger budget would not have
changed it. Milliseconds, minimum of two interleaved rounds, `taskset --cpu-list 0-7`:

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

> **#185 recalibrated it, and only one of these two figures survived.** The thresholds above are
> the right answer to *schoolbook* against the transform, and the dispatcher's question turned out
> to be Karatsuba against the transform — a different comparand, moving two of the three tiers in
> directions this note could not predict. 8 bytes did land at 512; 32 bytes did **not** go to 256
> but stayed at 512, because Karatsuba is still 1.18x ahead at product degree 254 over BN254; and
> the 4-byte row this note left open measures **4096**, not 16384. §4.1.2 has the measurement.

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
row measures exponent 0.90–1.15, against 1.93–2.14 for schoolbook — 1.03–1.27 on §3's re-take
after #189, against 1.95–2.01 for schoolbook in the same run.

> **#185 joined the three routes.** `multiply` now dispatches schoolbook → Karatsuba → transform,
> and the fallback for a field that cannot host a domain is Karatsuba rather than schoolbook. The
> schoolbook-versus-transform crossings in this subsection are therefore **no longer the thresholds
> the dispatcher uses**; they are kept because they are what §4.1.1's and §3.3's figures were taken
> against. §4.1.2 has the thresholds that replaced them and the measurement that produced them.

`Mul` cannot reach the transform, and that part has not changed: choosing a domain needs a
primitive `2^k`-th root of unity, so it needs `KnownOrder` and a source of randomness, neither of
which `Mul`'s signature can carry — and `KnownOrder` is exactly what the Gröbner core refuses to
require of a coefficient type (`test_the_grobner_stack_needs_no_field_cardinality`). Karatsuba
carries no such obstacle, and **since #231 the operator dispatches to it**; §4.1.2 has the
measurement and the two things that had to be fixed first. Mersenne-31, whose two-adicity of 1 rules the transform out
entirely, needs no CRT or Kronecker fallback for correctness: `multiply` falls back on precisely
that failure.

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

**#161 did that, and the byte figure moved with it.** §3's re-take measures `fftmul`'s peak at
**96 bytes per operand element** — `12 n B` — flat across every row from `n = 64` to `n = 2^22`.
The 208-byte figure above is the pre-#161 measurement, kept because the rest of this subsection's
argument was built on it.

**#165 adds the third route, between the two.** Karatsuba is `n^log2(3)`: subquadratic, not
quasi-linear, so the heading above still holds and the transform is still the only quasi-linear
path. What it does is own the band `fft_multiplication_crossover` leaves to schoolbook. Its own
crossover is 48 coefficients at 4 bytes an element, 16 at 8 and 4 above that, against the
transform's 16384, 2048 and 512 as those stood here — so the band Karatsuba owns is **three orders
of magnitude wide on the narrow fields** and it includes every degree `pow_mod`, `gcd` and
`separate_equal_degree` reach today. It also needs nothing from the field but a ring, so unlike the
transform it is available over Mersenne-31 without falling back. §4.1.1 measures it.

> #185 narrowed the band at the top, by re-measuring the transform's thresholds against Karatsuba
> rather than against schoolbook: 4096 / 512 / 512. The band is still **85x** wide in degree at 4
> bytes and 32x at 8, and over Mersenne-31 it is unbounded above, since no transform exists there at
> any degree. §4.1.2.

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

> **Superseded as a statement about what runs, not as a measurement.** The sentence below that the
> helper "is a standalone helper, called from nothing yet" was true when written and is false after
> #185: `multiply_dense` is now reached from `fft::multiply`'s two fallbacks. The figures in this
> subsection are unaffected — they measure the kernel, which did not change — and §4.1.2 measures
> the dispatched path.

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

> **The last clause is superseded, and by this kernel.** `div` is Karatsuba now: #231 put the
> dispatcher on `Mul`, which is the condition #193 was waiting on, and #193's Newton inversion
> calls the kernel above. `div`'s exponent moved from 2 to 1.59 and its reachable degree doubled
> over KoalaBear and quadrupled over BN254 `Fr` — so this section's "not a change in which degrees
> are reachable" is also narrower than it reads. See §4.5.

#### 4.1.2 The dispatcher, and the threshold that had to be re-measured (#185)

#165's kernel and #124's transform landed without either calling the other. #185 joined them, and
the work turned out to be less about the wiring than about the constant: **`fft_multiplication_crossover`
could not be inherited from any earlier figure, in either of the two forms it was available in.**

##### The correction

Both earlier calibrations measured **schoolbook against the transform** — #124 at 16384 / 2048 / 512
product degree for 4-, 8- and 32-byte elements, and #161 re-measuring the 8- and 32-byte rows one
doubling lower at 512 / 256 (§3.3). Once Karatsuba sits between them the dispatcher's question is
not that one. Below the threshold the route it takes is `multiply_dense`, which is Karatsuba above
its own base case, and §4.1.1 measures Karatsuba at 10.7x–22.9x schoolbook at `2^14`. A threshold
calibrated against schoolbook is calibrated against a route the dispatcher never takes.

The expected consequence was that the crossing would move *up*, since the comparand got faster. It
does on one tier and down on another, which is why this had to be measured rather than reasoned
about:

| element | #124 | #161, schoolbook-vs-transform | **#185, Karatsuba-vs-transform** | moved |
|---|---:|---:|---:|---|
| 4 bytes | 16384 | not measurable from `univariate_scaling` | **4096** | down 4x |
| 8 bytes | 2048 | 512 | **512** | down 4x |
| 32 bytes | 512 | 256 | **512** | unchanged |

Two of the three rows would have been wrong had either earlier figure been carried over:

- **The 4-byte tier was never measured against anything.** §3.3 says so explicitly — the example
  "cannot reach product degree 16 384 on that field within the budget" — so 16384 stood as an
  unverified bound. At product degree 32766 over KoalaBear the transform is **2.98x** ahead of
  Karatsuba, which the old threshold gave away entirely. This is the tier the F4 and resultant
  workloads run over.
- **The 32-byte tier must not fall to 256.** Karatsuba is still **1.18x** ahead at product degree
  254 over BN254 `Fr`, so taking #161's schoolbook crossing would have moved this threshold the
  wrong way and paid the transform's setup on a band Karatsuba owns.

##### The instrument

`examples/multiplication_dispatch.rs`. Three arms per size, all reached through the shipped public
API rather than through a kernel, so what is timed is the dispatched path:

| arm | call | what it is |
|---|---|---|
| schoolbook | `&a * &b` | `DensePolynomial`'s `Mul`, unchanged |
| dense | `multiply_above(a, b, u32::MAX, rng)` | cannot reach the transform, so exactly `multiply_dense` |
| ntt | `multiply_above(a, b, 0, rng)` | always attempts the transform |

Interleaved within each repetition and the minimum taken over up to seven, `taskset --cpu-list 4`,
under the benchmark lock. The three arms are asserted equal to each other once per size outside the
timing. A field whose two-adicity cannot host the domain takes arm 2 as arm 3's fallback by design,
so those rows are marked `(fallback)` and excluded from the crossing rather than read as transforms.

Microseconds, minimum of the interleaved repetitions. Operand lengths; the product degree is
`2 len - 2`:

| field | operand len | product deg | schoolbook | dense | ntt | school/dense | dense/ntt |
|---|---:|---:|---:|---:|---:|---:|---:|
| KoalaBear | 1024 | 2046 | 294.3 | 81.6 | 98.8 | 3.61x | 0.83x |
| KoalaBear | 2048 | 4094 | 1154.0 | 245.9 | 207.3 | 4.69x | **1.19x** |
| KoalaBear | 8192 | 16382 | 18368.9 | 2280.2 | 1065.2 | 8.06x | 2.14x |
| KoalaBear | 16384 | 32766 | 70613.0 | 6498.6 | 2157.0 | 10.87x | 2.98x |
| KoalaBear | 65536 | 131070 | skipped | 59205.8 | 9535.6 | — | 6.21x |
| Zp65537 | 64 | 126 | 13.0 | 6.1 | 7.8 | 2.13x | 0.78x |
| Zp65537 | 128 | 254 | 41.0 | 14.6 | 13.1 | 2.80x | **1.12x** |
| Goldilocks | 128 | 254 | 33.4 | 13.3 | 14.9 | 2.51x | 0.89x |
| Goldilocks | 256 | 510 | 134.4 | 40.6 | 30.8 | 3.31x | **1.32x** |
| BN254 `Fr` | 128 | 254 | 379.6 | 111.6 | 131.2 | 3.40x | 0.85x |
| BN254 `Fr` | 256 | 510 | 1521.1 | 355.7 | 281.0 | 4.28x | **1.27x** |

The crossings, as the bracket between the two adjacent doublings that straddle them — the sweep
doubles, so it brackets rather than lands on them. Reproduced across three separate pinned runs,
the KoalaBear bracket identical in all three:

| field | crossing | rounded up |
|---|---|---:|
| KoalaBear (4 B) | (2046, 4094] | **4096** |
| Zp65537 (8 B) | (126, 254] | 256 |
| Goldilocks (8 B) | (254, 510] | **512** |
| BN254 `Fr` (32 B) | (254, 510] | **512** |

The two 8-byte fields land in adjacent brackets, so the tier is set to the later of them. Rounding
up is #124's convention and errs toward the route that is cheaper at small sizes; the cost of
erring that way is bounded and visible — on Zp65537 between 256 and 512 the transform is at most
1.60x ahead — where erring the other way pays the transform's fixed setup on every product in the
band.

##### The 4-byte figures and the ISA floor they were taken at (#244)

#244 was filed from this section's own measurements, reporting the 4-byte crossing as "contingent
on a codegen decision" because the same commit measured 4096 in one artifact and 1024 in another.
**That diagnosis was wrong, and the real cause is a trap this repository had already documented.**

The two artifacts differed by whether the shell that built them set `RUSTFLAGS`, not by the build
invocation:

```text
cargo build --release                          -> -C target-cpu=x86-64-v3
RUSTFLAGS="-D warnings" cargo build --release  -> no target-cpu at all
RUSTFLAGS="" cargo build --release             -> no target-cpu at all
```

`RUSTFLAGS` **replaces** `target.*.rustflags` rather than adding to it. `MILESTONE-SIMD-PARALLELISM.md`
§3.1 records this costing a silent CI regression once already — "the CI workflow set
`RUSTFLAGS: -D warnings`, which would have discarded the ISA floor entirely" — and
`.cargo/config.toml` warns about it in a comment. CI states both flags and is correct. The
ad-hoc measurement commands behind #185 and #231 set only one, and so measured a baseline
x86-64 build with no AVX2. A 4-byte Montgomery multiply vectorizes and an 8-byte one does not
(§8.3 of that milestone), which is why only the 4-byte figures moved and why it looked like a
property of the 4-byte kernel.

Verified directly: `cargo build -v | grep target-cpu` shows `x86-64-v3` with no `RUSTFLAGS` and
nothing at all with it set, and `tools/vec_census.sh` counts **65 vector multiplies** in the first
artifact and **0** in the second.

**The crossover constant is unaffected.** #185 shipped 4096 / 512 / 512 from runs that happened not
to set `RUSTFLAGS`, which is the shipped configuration. Re-measured at v3 with a corrected
instrument, the crossings are (2046, 4094], (254, 510] and (254, 510] — **4096 / 512 / 512**,
unchanged. The 1024 figure was the artifact of a build with no AVX2 and is not a property of
anything.

**What changed to stop this recurring.** `tools/vec_census.sh` counts vector multiplies in an
artifact and with `--require` exits nonzero when there are none — whole-artifact rather than
symbol-filtered, because under fat LTO the kernels are inlined and no symbol named for them
survives, so a filter reports a false negative. And `util::isa_floor()` is printed in the header of
every measurement example here, so no figure can be recorded without its ISA beside it:

```text
ISA: x86-64-v3 or better (AVX2)
ISA: baseline x86-64, NO AVX2 — RUSTFLAGS probably displaced the ISA floor
```

Not a `#[test]` asserting AVX2: `.cargo/config.toml` applies only when cargo runs in this directory
and is explicitly not inherited by consumers, so such a test would fail for every downstream build.

##### #231's figures, re-taken at the floor

#231's A/B set `RUSTFLAGS=""`, so its figures are baseline-x86-64 ones. Re-run at v3, three
variants from one tree — **A** pre-#231 entirely, **B** main, **C** main's `Mul` with the pre-#231
loop order — interleaved, `taskset`-pinned, minimum of three rounds. The headline holds; two
details do not.

| field | stage | size | A pre-#231 | B main | A/B | C/B |
|---|---|---:|---:|---:|---:|---:|
| KoalaBear | **roots** | 2048 | 56.181 ms | 35.999 ms | **1.56x** | 1.01x |
| KoalaBear | mul | 4096 | 4.005 ms | 0.644 ms | 6.22x | 1.01x |
| KoalaBear | lcm | 4096 | 10.064 ms | 6.647 ms | 1.51x | 1.00x |
| KoalaBear | **from_zeros** | 512 | 0.393 ms | 0.083 ms | **4.71x** | **5.27x** |
| KoalaBear | div *(control)* | 4096 | 4.564 ms | 4.561 ms | 1.00x | 1.00x |
| BN254 `Fr` | **roots** | 256 | 945.206 ms | 544.186 ms | **1.74x** | 1.01x |
| BN254 `Fr` | mul | 1024 | 21.318 ms | 3.014 ms | 7.07x | 1.01x |
| BN254 `Fr` | lcm | 1024 | 46.942 ms | 29.084 ms | 1.61x | 1.00x |
| BN254 `Fr` | from_zeros | 512 | 5.270 ms | 5.561 ms | **0.95x** | 0.94x |
| BN254 `Fr` | div *(control)* | 1024 | 19.773 ms | 21.968 ms | **0.90x** | 1.00x |

**What holds.** `roots` is 1.28x–1.56x over KoalaBear and 1.39x–1.74x over BN254, against the
1.32x–1.67x and 1.44x–1.66x #231 reported — the same conclusion from different numbers. `mul` and
`lcm` likewise.

**Two corrections to #231.**

The **loop swap is worth about 5x, not 2.5x**, and it is not free. The `C/B` column isolates it:
5.27x on KoalaBear `from_zeros` at 512 zeros, where #231 measured 2.5x at baseline — the swapped
shape has a long inner loop, which is the shape that can vectorize, so the gain is larger exactly
where AVX2 exists. But on BN254 the same column is **0.94x**: the swap costs 6% on a 32-byte
element. #231's commit message and `karatsuba.rs`'s doc comment both say BN254 "does not move
either way", which was true at baseline and is false at the floor. The trade is ~5x on 4-byte
against ~6% on 32-byte, and it is worth making — but it is a trade and was reported as free.

The **control is not flat on BN254**: `div_isolated` is 0.90x at two of three sizes, reproducibly,
where #231 reported "flat to within 1% in 12 of 12 cells". `C/B` is 1.00x there, so the swap is not
the cause; `div_with_remainder` contains no polynomial multiplication, so this is the `Mul` change
perturbing its code layout under fat LTO. It is dominated — `roots` contains `div` and is still
1.74x ahead on the same field — but #231's claim that nothing moved was a claim about the wrong
build, and the honest statement is that a 10% layout effect on long division over a 32-byte element
is present and unexplained.

Everything #185 and #231 concluded survives; what does not survive is the precision several of
their figures were quoted to.

##### Mersenne-31: the fallback measured, since it is the only route there

Two-adicity 1, so no domain exists past two points and `multiply_above` takes its
`unwrap_or_else` arm at every size. Before #185 that arm was schoolbook. The `ntt` column below is
that fallback, and its agreement with the `dense` column to within 1% is the check that it *is* the
fallback:

| operand len | product deg | schoolbook us | dense us | ntt us (fallback) | school/dense |
|---:|---:|---:|---:|---:|---:|
| 16 | 30 | 0.3 | 0.1 | 0.2 | 1.80x |
| 256 | 510 | 22.4 | 10.2 | 10.1 | 2.20x |
| 1024 | 2046 | 338.6 | 91.3 | 91.4 | 3.71x |
| 4096 | 8190 | 5297.6 | 830.2 | 830.6 | 6.38x |
| 16384 | 32766 | 80314.3 | 7176.7 | 7237.7 | **11.19x** |

So on the field every F4 benchmark in this crate runs over, where the transform is unavailable at
every degree, the dispatcher's whole gain is this column: **1.80x at operand length 16 rising to
11.19x at 16384**, from a route that was previously unreachable.

##### `DensePolynomial::Mul`: dispatched, and what it cost to get there (#231)

#185 left this as a separate decision and asked for one with measurement behind it. #231 took it,
in the two steps the issue sequenced, and the second step turned up a regression that had to be
fixed in shared code before the operator could land.

**Step one: an oracle that is not the thing under test.** `&a * &b` was the comparand for *every*
test in `fft::multiply` and for five in `karatsuba`. Dispatching `Mul` to `multiply_dense` would
have made the Karatsuba tests compare Karatsuba against itself and the transform tests compare the
transform against Karatsuba — all still green. `test_support::schoolbook_product` is the definition
written out, sharing code with neither route, and it is itself pinned against products computed by
hand. That commit changed no behaviour: the same tests pass before and after.

**Step two, and the thing that was nearly missed.** #185 named the risk precisely — "small products
dominate by *count* in F4 and FGLM even though large ones dominate by time. A change that adds
overhead to the smallest products can lose overall while winning every individual large product."
It does, and the first A/B found it: `from_zeros`, which folds one linear factor at a time and so
multiplies `len x 2` throughout, measured **0.74x** over KoalaBear.

The cause was not the dispatch. `schoolbook_into` iterated the *longer* operand outside and the
shorter inside, so a `512 x 2` product paid the `out[i..].iter_mut().zip(..)` setup 512 times for
two multiplies each. In-process, both routes in one binary so there is no cross-binary variance:

| shape | inline double loop | `multiply_dense`, long outer | after the swap |
|---|---:|---:|---:|
| KoalaBear 8 x 2 | 36.5 ns | 37.8 ns (0.97x) | 19.9 ns (**1.96x**) |
| KoalaBear 32 x 2 | 99.4 ns | 125.6 ns (0.79x) | 45.4 ns (**2.34x**) |
| KoalaBear 128 x 2 | 356.8 ns | 481.7 ns (0.74x) | 147.7 ns (**2.56x**) |
| KoalaBear 512 x 2 | 1406.4 ns | 1902.7 ns (0.74x) | 589.8 ns (**2.54x**) |
| BN254 512 x 2 | 22236 ns | 22433 ns (0.99x) | 21044 ns (1.08x) |

**BN254 does not move in either direction**, and that is the evidence that the cost was the loop
shape and not the arithmetic: a 254-bit multiply is ~19 ns against ~1 ns of setup, so there is
nothing there for the setup to be a fraction of. On a 4-byte field the multiply is ~1.3 ns and the
setup is the larger half.

The swap is in shared code, so Karatsuba's own leaves get it too, and the old inline `Mul` had the
bad order as well — which is why the fixed dispatched path is 2.5x the operator it replaced on that
shape rather than merely even with it.

**The A/B, re-run against the final tree.** Two binaries from one tree differing only in `Mul`'s
body, built into private target directories, `md5sum`-checked distinct, interleaved under
`taskset --cpu-list 4` and the benchmark lock, minimum of three rounds. `examples/univariate_scaling.rs`
cannot serve as the harness until #189 is fixed — its `fftmul` stage verifies against `&a * &b`, so
the verification is quadratic in the operand degree and the sweep does not terminate at any budget
reaching interesting sizes.

| field | stage | size | `Mul` schoolbook | `Mul` dispatching | ratio |
|---|---|---:|---:|---:|---:|
| KoalaBear | **roots** | 256 | 2.035 ms | 1.538 ms | **1.32x** |
| KoalaBear | **roots** | 1024 | 27.418 ms | 17.359 ms | **1.58x** |
| KoalaBear | **roots** | 2048 | 103.901 ms | 62.154 ms | **1.67x** |
| KoalaBear | mul | 1024 | 0.528 ms | 0.143 ms | 3.70x |
| KoalaBear | mul | 4096 | 8.392 ms | 1.292 ms | 6.49x |
| KoalaBear | lcm | 4096 | 17.696 ms | 10.702 ms | 1.65x |
| KoalaBear | from_zeros | 512 | 0.440 ms | 0.155 ms | **2.83x** |
| KoalaBear | div *(control)* | 4096 | 7.644 ms | 7.751 ms | 0.99x |
| BN254 `Fr` | **roots** | 128 | 269.120 ms | 175.231 ms | **1.54x** |
| BN254 `Fr` | **roots** | 256 | 1084.052 ms | 652.755 ms | **1.66x** |
| BN254 `Fr` | mul | 1024 | 25.665 ms | 3.512 ms | 7.31x |
| BN254 `Fr` | lcm | 1024 | 56.007 ms | 33.768 ms | 1.66x |
| BN254 `Fr` | from_zeros | 512 | 5.856 ms | 5.646 ms | 1.04x |
| BN254 `Fr` | div *(control)* | 1024 | 24.483 ms | 24.380 ms | 1.00x |

`roots` is the binding univariate stage per §5, and it is `O(log q)` products at the working degree
through `pow_mod_limbs`. `lcm` and `from_zeros` are the other two `Mul` callers worth naming;
`Polynomial::pow`, `compose` and `shift` are built on the same operator.

> **This subsection's figures are baseline-x86-64 ones**, taken before #244 found that their build
> commands set `RUSTFLAGS` and so discarded the ISA floor. The conclusions hold; the numbers are
> superseded by "#231's figures, re-taken at the floor" above, which is the table to quote.

**#185's control anomaly, and the part of this paragraph that was also wrong.** #185 reported
KoalaBear `div` at 0.89x–0.91x, unexplained. At the time this read as settled: `div_with_remainder`
is identical in both binaries — same instruction count, 1609, and zero `vpmuludq` in both — so there
seemed to be nothing in the artifact for a 10% effect to live in, and re-measured with an isolated
arm the control was flat in 12 of 12 cells.

**The "zero `vpmuludq` in both" was the symptom, not the control.** Both artifacts lacked AVX2
entirely, which is why neither had a vector multiply anywhere; the observation showed only that the
two builds were equally crippled. Re-measured at the floor, the control is flat on KoalaBear
(1.00x, 0.99x, 1.00x) and **0.90x on BN254** at two of three sizes, reproducibly — so a ~10% layout
effect on long division over a 32-byte element is real and still unexplained. It is dominated:
`roots` contains `div` and is 1.74x ahead on the same field. #185's KoalaBear reading does look
environmental, since it does not reproduce in either ISA state; the claim that nothing moved
anywhere does not survive.

**One instrument needed pinning down afterwards.** `examples/univariate_scaling.rs`'s **mul** row
is the quadratic baseline every crossover in §3.1 and §4.1 is quoted against, and it reached that
baseline through `&a * &b`. With the operator dispatching, that row would silently have started
measuring Karatsuba — the A/B above puts the same product at 3.70x and 6.49x faster at operands
1024 and 4096, a ratio growing with size, so the row's documented exponent of 2.00 would have
drifted toward 1.59 and every crossover quoted against it would have moved for no reason anyone
could see. The row now calls `karatsuba_unstable(.., usize::MAX)` — a base case the recursion never
passes, so the plain double loop — and re-measures at exponent 1.93–2.04 and 32.0 bytes an element
over KoalaBear, which is §3.2's `4 n B` unchanged. The **fftmul** stage's comparand is still the
operator, which is still an independent check but is no longer the same implementation as the
**mul** row; the verification line it prints says so rather than claiming schoolbook.

**The blast radius does not reach the Gröbner core.** F4, Buchberger and FGLM are `SparseMultiPoly`
throughout; the only `Mul` sites under `grobner::` are `Monomial * Monomial` in `f4::symbolic` and
multivariate products in tests, and `research::resultant`'s `&result * p` is multivariate too.
Checked by grep rather than assumed, which is what #231 asked for. So #185's worry about small
products dominating by count in F4 does not apply to this operator — though it did apply, in a
different place, and §4.1.2's step two is where it showed up.

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

**All three now exist — #162 stage 2, and §4.3.3 is the measurement.**
`src/poly/univariate/subproduct_tree.rs` builds `prod (x - x_i)` as a balanced binary tree, pushes
remainders down it for multipoint evaluation at an arbitrary point set, and accumulates the
transposed form upward for interpolation. `lagrange_interpolate` dispatches to it above a measured
crossover and `multipoint_evaluate` is the public entry point for the evaluation half.

The paragraph this replaces named "a subproduct tree plus fast division by Newton iteration" as the
pair, and the pairing was the load-bearing part: with long division the tree does not move the
exponent **at all**, because the levels sum to `n^2 * sum_k 2^-k`. #193 supplied the division and
§4.3.3 has the arithmetic. What it reaches is `O(M(n) log n)` with a Karatsuba `M`, measured at
**1.46 – 1.62**, rather than the `O(n log^2 n)` this paragraph predicted: "near 1" is unreachable
under #162's own `FiniteField` bound, so #559 amended that issue's exponent criterion to ask for
the multiplication exponent instead. §4.3.3's exponent-criterion section is the decision and the
reasoning; #606 holds the `KnownOrder` specialization it deferred.

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

#### 4.3.3 Stage 2: the subproduct tree, and the exponent it actually reaches

**Measured at `1154bf5b` plus the change itself.** Both arms of every table below are entry points
in one binary, so there is no before-side tree to name and nothing merged after `1154bf5b` can have
moved one arm relative to the other; `1154bf5b` is a merge commit on `main` and so stays resolvable
(#505). ISA floor `x86-64-v3 or better (AVX2)`, printed in the run's own header by
`examples/subproduct_crossover.rs`.

`src/poly/univariate/subproduct_tree.rs` builds `prod (x - x_i)` as a balanced binary tree and runs
two algorithms on it: multipoint evaluation by simultaneous remaindering down the tree, and
interpolation as the transposed form accumulated upward,
`T_parent = T_left * M_right + T_right * M_left`, with every denominator `M'(x_i)` coming from one
evaluation of the derivative.

##### Why this could not be written before #193

§4.3 said this machinery "is what would make this `O(n log^2 n)`" and named "a subproduct tree plus
fast division by Newton iteration" as the pair. The pairing was the load-bearing part, and the
reason is worth stating because the tree on its own is **worthless**:

```text
  evaluation cost  =  sum_k 2^k * D(n / 2^k)
```

With `D(d) = d^2` — long division, which is what §4.5 was until #193 — that sum is
`n^2 * sum_k 2^-k = O(n^2)`, and the top level alone is `(n/2)^2` twice. The tree bought a constant
factor of about two over `n` Horner passes and **did not move the exponent at all**. #193 made
`D(d) = O(M(d))`, so the sum telescopes to `O(M(n))`; each node's division is exactly the balanced
shape #193's crossover is read off, so the upper levels take the Newton route and the nodes near
the leaves fall back to long division without being told to.

##### The two arms, measured against each other

`examples/subproduct_crossover.rs`, fastest of up to 7 interleaved repetitions, arms checked equal
before the clock starts:

| field | quadratic at n = 8192 | tree at n = 8192 | | quadratic exp. | tree exp. |
|---|---:|---:|---:|---:|---:|
| Mersenne-31, `u32` | 0.5453 s | **0.0293 s** | **18.6x** | 1.989 | **1.460** |
| Mersenne-31, `u64` | 0.6378 s | **0.1192 s** | 5.35x | 1.989 | 1.596 |
| Goldilocks | 0.7732 s | **0.1092 s** | 7.08x | 2.043 | 1.612 |
| BN254 `Fr` | 5.2884 s | **0.9839 s** | 5.37x | 2.001 | 1.620 |

The exponents are least-squares fits over the top half of the sweep. **The tree's is the
multiplication exponent**, 1.46–1.62 against `log2(3) = 1.585`, which is what a `FiniteField` bound
can reach and is discussed below.

And multipoint evaluation, against the `n`-Horner loop it replaces — there is no second algorithm to
compare against, since `fft::evaluate`'s domain must be geometric, which is the whole gap this
stage fills:

| field | Horner exp. | tree exp. | tree first faster by >10% |
|---|---:|---:|---:|
| Mersenne-31, `u32` | 2.026 | 1.515 | n = 256 |
| Mersenne-31, `u64` | 2.012 | 1.626 | n = 1 024 |
| Goldilocks | 2.052 | 1.629 | n = 512 |
| BN254 `Fr` | 2.001 | 1.607 | n = 2 048 |

##### The crossover is nearly flat across widths, unlike every other one here

| element | field | `t` | first clear win | the shipped rule takes the tree from |
|---|---|---:|---:|---:|
| 4 bytes | Mersenne-31 in a `u32` | **64** | n = 128 | n = 128 |
| 8 bytes | Mersenne-31 in a `u64` | **128** | n = 256 | n = 256 |
| 8 bytes | Goldilocks | **128** | n = 256 | n = 256 |
| 32 bytes | BN254 `Fr` | **128** | n = 256 | n = 256 |

Each `t` is the largest swept `n` at which the tree does **not** win by more than 10%; inside 10%
the two cost the same to within this box's spread and the tiebreak is memory, where the quadratic
form's two flat arrays win decisively. The shipped rule lands on the first clear win on all four
fields, which is the check that the constant is the measurement rather than near it.

§4.1.1's base case falls **12x** across these widths and §4.5's Newton crossover falls **8x**. This
one barely moves: 64 at four bytes and 128 everywhere above. Both arms' cost is field
multiplications in roughly the same proportion, so widening the element scales the two sides
together. The 4-byte tier is kept because it genuinely differs, not for symmetry.

##### The `lagrange` row, re-measured

Same command as §4.3.1, `budget=1.0`, so these compose with that table:

| field | before #162 | after stage 1 | after stage 2 | exp. stage 1 | exp. stage 2 |
|---|---:|---:|---:|---:|---:|
| KoalaBear | 1 024 | 16 384 | **65 536** | 1.86 – 2.12 → 2 | **1.49 – 1.72 → 1.6** |
| BN254 `Fr` | 512 | 4 096 | **16 384** | 2.00 | **1.51 – 1.67 → 1.6** |

A further **4x** in reachable point count on both fields, and **64x / 32x** against the cubic form
this issue started from. Absolute cost at the largest size reached: KoalaBear 65 536 points in
2.80 s at 19 661 568 peak bytes; BN254 16 384 in 2.87 s at 15 467 760.

**`roots` did not move, and should not have.** It is still 8 192 on KoalaBear and 512 on BN254 —
the figures #193 left — because interpolation is not in it. §5's binding stage is unchanged by this
change, which is worth saying because the previous two stages both moved it.

**The crossover is visible in the memory column**, which is the cheapest confirmation that the
dispatch fires where it claims. The `lagrange` row's bytes-per-element over KoalaBear is 40.1 at
n = 128 and 237.5 at n = 256 — `5 n B` below the 8-byte tier's constant and `~30 n B` above it,
with the step exactly at the constant; over BN254 it is 160.2 then 722.8 at the same boundary.
Nothing in this change writes that column.

##### The exponent criterion, amended rather than left unmet (#559)

**The decision, in writing: #162's criterion now asks for an exponent near the multiplication
exponent and measurably below 2, and that is met.** #559 listed three ways out of the tension and
took the first — relax the criterion to what the specified bound can deliver. The criterion is
amended in place, on #162 as well as here, so the closed issue does not read as having shipped
with an acceptance criterion unmet. What follows is why that was the available choice.

The criterion as written asks for a `lagrange` exponent "near 1", and says an exponent that does
not move "is the signal that the implementation is not what it claims to be". The exponent moved,
from 2 to 1.6, which is the signal the criterion was really asking for. It is not near 1, and **it
cannot be under #162's own Scope**, which says:

> `KnownOrder` is not required: nothing here needs the field's order, so the bound should stay
> `FiniteField` as it is today.

Near 1 needs the transform; the transform needs a primitive `2^k`-th root of unity, hence
`KnownOrder` and an RNG, which is precisely why `fft::multiply` carries that bound and `Mul` does
not (§4.1). Under `FiniteField` the fastest product is Karatsuba and the best a tree can reach is
`O(M(n) log n)` with `M(d) = d^1.585`. Of the two requirements in tension, the bound is the one
that was specified, implemented and tested, so the criterion is what gives way. The measured
1.46 – 1.62 against `log2(3) = 1.585` is the amended criterion met *exactly* rather than
approximately: the exponent is the multiplication exponent because the algorithm is
multiplication-bound, which is a stronger statement about the implementation than "below 2" is.

**What the other two options were, and why neither was taken.** Recording near-1 as out of reach
and leaving the criterion standing is the paragraph above — it is the reason, not a decision, and
on its own it leaves #162 reading as unmet, which is the thing this was opened to fix. A
`KnownOrder` specialization beside the `FiniteField` path — the same tree, with the node products
and the remainders going through `fft::multiply` and a transform-based division above a measured
crossover — is the only option that would move a figure, and it is **deferred to #606 rather than
rejected**, because what it is worth is not known:

* A transform-based subproduct tree is `O(n log^2 n)`, not `O(n log n)` — the second log is the
  tree's own levels — so against the measured `n^1.6` the asymptotic gap is `n^0.6 / log2(n)^2`
  before any constants: about **1.7x at `n = 2^14`** and about **10x at `n = 2^20`**. The upper
  end of that span is already past where the route stops for a reason this stage cannot fix —
  §5.1 has root finding binding at comparable degrees, and stage 2 did not move it. #559's own
  estimate of ~40x at `n = 16 384`
  compares `n^1.6` against `n log n`, which is one multiplication rather than the tree, and so
  overstates it by a factor of `log n`.
* The constants run the other way. Karatsuba needs no root of unity, no twiddle tables and no
  rounding up to a power-of-two domain, and §4.1's transform crossover is already degree ~460 to
  ~12 000 depending on width — so the tree's own crossover may sit above every degree §5 says is
  reachable.
* It needs the dispatch question #185 answered for *division* the way #231 answered it for
  multiplication, and §4.5's crossover is asymmetric in a way §4.1's is not, so that answer is not
  a copy of this one.
* **The `FiniteField` path stays whatever #606 concludes.** Mersenne-31 has two-adicity 1 (§1.1),
  so a power-of-two transform is ruled out there at every degree above two and Karatsuba is the
  only route that field has.

##### #560: `from_zeros` gets the tree, and its stated justification was wrong

**Measured at `bccad1fc` plus the change itself**, same protocol and instrument as above.

`DensePolynomial::from_zeros` folded the linear factors in one at a time, and that fold is `O(n^2)`
**however good the multiplication gets**: it multiplies a growing product by a *two-coefficient*
operand, which is below every `karatsuba_base_case` tier, so every step is the schoolbook loop
whatever the product has grown to. #231's measured 2.83x on it came from `schoolbook_into`'s loop
order, not from the recursion. The tree's root is the same product at `O(M(n))`.

`examples/subproduct_crossover.rs` grew a third arm for it, because the work is not interpolation's
— this builds the tree and stops:

| field | fold exponent | tree exponent | n = 4096 | first clear win |
|---|---:|---:|---:|---:|
| Mersenne-31 in a `u32` | 1.872 | **1.295** | **5.63x** | n = 512 |
| Mersenne-31 in a `u64` | 1.971 | **1.464** | **10.37x** | n = 64 |
| Goldilocks | 1.977 | **1.481** | **9.55x** | n = 64 |
| BN254 `Fr` | 1.993 | **1.581** | **12.54x** | n = 4 |

**Three tiers, and a single constant would have been a regression.** Interpolation's crossover is
nearly flat across widths (64/128); this one moves by **32x** — 256 / 32 / 8. The first version of
#560 used 32 everywhere, which over a 4-byte element puts the tree in charge from 33 where the fold
is still 1.6x faster at 64 and 1.25x at 128. The sweep starts at `n = 2` for this arm alone, because
over a 32-byte element the tree already wins at 16, which is the other arms' floor.

**The issue's stated justification does not hold, and the measurement is what found it.** #560 says
`roots`, `fglm` and the graeffe path all call `from_zeros`, putting it "on the critical path of the
stage that binds". They do not. Every occurrence in `src/` outside the definition is a doc comment,
a re-export, or inside a `#[cfg(test)] mod tests` — `from_zeros` has **no library caller at all**,
and its only non-test user in the repository is `examples/graeffe_root.rs`. So:

- `roots` is **not** re-measured, because it cannot have changed. That is #560's last acceptance
  criterion and it is void rather than skipped.
- The change is a public-API improvement, not a stage improvement. There is no stage figure to
  report and this section does not imply one.
- It is still worth having: the API is public, the fold was asymptotically wrong, the per-width
  tiers mean no size regresses, and the tree it needs was already here.

##### What this does not establish

* **The answer.** The tree agrees with the quadratic form exhaustively over GF(7) for every
  abscissa subset of size at most three, at every n to 64 over Mersenne-31 and to 40 over BN254,
  and the dispatcher agrees with both either side of its crossover at degrees derived from the
  constant.
* **That `from_zeros` got faster.** It did not: it is still the quadratic fold, left that way
  deliberately so it stays an independent oracle for the tree's own root. **#560** is the issue to
  change it.
* **Anything about #82.** The degrees D1's evaluation–interpolation resultant wants are §5's
  subject and this measures the stage, not the route. §5.1 is where the 1.6 is carried over to that
  route, and it is carried as an exponent rather than as a re-extrapolated table.
* **`O(n log^2 n)`.** §4.3 predicted that figure for this machinery. What it reaches is
  `O(M(n) log n)` with a Karatsuba `M`, which is not the same thing, and the measured 1.6 is the
  honest version of that prediction. #606 is where `O(n log^2 n)` would be reached, if the
  measurement it asks for says the crossover is inside the reachable range.

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

### 4.5 Division: sub-quadratic since #193, and the GCD that is now unblocked

**Closed by #193.** `div_with_remainder` dispatches between long division and Newton inversion of
the reversed divisor on a measured crossover, and the `div` row of §3 is superseded: its exponent
is **1.52 – 1.61** over KoalaBear and **1.57 – 1.62** over BN254 `Fr`, against the
1.63 – 2.12 → 2 recorded there. The reach at one second doubles over KoalaBear and **quadruples**
over BN254, and `roots`'s doubles on both — which is the point of the issue rather than a side
effect. §4.4 is `O(log q)` multiplications **and divisions** at the working degree, so halving the
division exponent moves the binding stage directly, and it did.

| route | cost | with the `M` available at the operator | measured exponent |
|---|---|---|---|
| long division | `d^2` | `d^2` | 1.95 – 2.03 |
| Newton inversion of `rev(g)` | `O(M(d))` | `O(d^1.585)` | **1.56 – 1.61** |
| classical Euclid | `O(d^2)` | `O(d^2)` | not separately measured |
| half-GCD (#194) | `O(M(d) log d)` | `O(d^1.585 log d)` | **unblocked, unwritten** |

The exponent column is `examples/division_crossover.rs`'s fitted slope over the top half of its
balanced sweep, which is the figure that compares the two routes at the same sizes; §3's per-row
figures are `examples/univariate_scaling.rs`'s and are the ones quoted above. They agree.

#### The gate opened two months before anything noticed

The row above is the same arithmetic the superseded version of this section carried; what changed
is the third column. `M(d)` at the operator is **not** schoolbook any more. #231 put the
schoolbook-or-Karatsuba dispatcher on `DensePolynomial`'s `Mul`
(`src/poly/univariate/dense_polynomial_arithmetic.rs` is one call to `multiply_dense`), which is
precisely the condition #126 and #193 named:

> So the gate is a crossover, not a date, and it is #185's — specifically its open
> `DensePolynomial::Mul` dispatch question rather than its recommended first step.

#193 listed three facts as "verified at the time of #192, not assumed". All three are now false:
`Mul` is not the schoolbook double loop, `multiply_karatsuba` has callers outside its own tests,
and the dispatch that does not exist does. The issue nevertheless carried a `blocked` label
pointing at an issue that had closed, and a label cannot expire — which is the same failure mode
the claim tooling's §4 lease exists to prevent, one level up. **A dependency recorded as a label is
a dependency nobody re-checks.** The arithmetic in this section was correct and current the whole
time; what was stale was the one sentence saying it had not happened yet.

#### The algorithm, and why its crossover is asymmetric

Reversing `f = qg + r` through `x -> 1/x` and multiplying by `x^deg f` gives
`rev(f) = rev(q) * rev(g) + x^k * rev(r)` with `k = deg f - deg g + 1`, so
`rev(q) = rev(f) * rev(g)^-1 mod x^k` and the remainder term is annihilated by the truncation
rather than computed. `rev(g)`'s constant term is `g`'s leading coefficient — non-zero for every
non-zero `g`, and the same quantity long division inverts — so the power series inverse always
exists. The inverse is Newton's `h <- h * (2 - g*h) mod x^(2^i)`, doubling precision per step.

The dispatch rule is **not** a threshold on the divisor's degree, and the measurement is what
established that. Writing `k` for the quotient length and `m` for the divisor length:

```text
  long division   k * m
  Newton          C * M(k)  +  (m/k) * M(k)
```

`k` is the precision, and the iteration's second product multiplies two series that are both as
long as the precision — so Newton pays `M(k)` however long the divisor is. Only the `r = f - q*g`
recovery sees `m`, and it sees it as the *long* operand of an asymmetric product. Dividing through
by `k * m`, the recovery term is `k^(e-1)/k < 1` for every `k` past the Karatsuba base case: the
recovery never blocks the route, only the inversion does, and Newton wins when
`m > C * k^(e-1)` with `e = log2 3`.

That asymmetry is measurable in both directions, and a first implementation of this issue got it
wrong in one of them. A symmetric `min(k, m)` rule sends a **short quotient against a long
divisor** to long division, where Newton is 2.2x to 7.8x faster:

| `k` | `m` | field | long division | Newton | speedup |
|---:|---:|---|---:|---:|---:|
| 1024 | 4096 | Mersenne-31, 4-byte | 1.445 ms | 0.642 ms | **2.25x** |
| 1024 | 65536 | Mersenne-31, 4-byte | 23.18 ms | 6.46 ms | **3.59x** |
| 1024 | 65536 | BN254 `Fr` | 1.634 s | 0.209 s | **7.82x** |
| 4096 | 1024 | Mersenne-31, 4-byte | 1.480 ms | 2.403 ms | 0.62x |
| 65536 | 1024 | Mersenne-31, 4-byte | 23.97 ms | 148.2 ms | **0.16x** |

The last row is the one a `deg(g) >= t` gate would have taken, at six times the cost. The
derivation, including the floor on `k` that is **not** implied by the inequality and is #527's
subject, is in the module comment of `src/poly/univariate/div_with_remainder.rs`.

#### The measured crossover, per element width

Fixing `C = t^(2-e)` makes the balanced case `k = m = d` cross exactly at `d = t`, which leaves one
constant per width — the same three-tier shape as §4.1.1's base case, and the same direction: the
crossover falls 8x across the widths this crate uses, against the base case's 12x.

| element | field measured | `t` | first clear win | speedup there |
|---|---|---:|---:|---:|
| 4 bytes | Mersenne-31 in a `u32` | **1024** | `d = 2048` | 1.31x |
| 8 bytes | Mersenne-31 in a `u64` | **256** | `d = 512` | 1.23x |
| 8 bytes | Goldilocks | **256** | `d = 512` | 1.09x |
| 32 bytes | BN254 `Fr` | **128** | `d = 256` | 1.17x |

Each `t` is the largest swept length at which Newton does **not** win by more than 10%, rather than
the largest at which it loses. Inside 10% the two routes cost the same to within this
workstation's run-to-run variation, and the tiebreak is then memory: long division peaks at `6 n B`
and Newton at `10 n B`. The two 8-byte fields disagreed — 1.23x against 1.09x at `d = 512` — and
256 is the tier that costs neither, winning clearly on one and tying on the other, where 512 would
have forgone the 1.23x.

**The crossover is visible in §3.2's memory column**, which is the cheapest confirmation that the
dispatch fires where it says. The `div` row's bytes-per-element over KoalaBear is 47.9 at `n = 256`
and 79.4 at `n = 512` — `6 n B` below the 8-byte tier's crossover and `10 n B` above it, with the
step exactly at the constant.

#### `Div` does not pay for the remainder

`/` routes through a separate `quotient` entry point rather than projecting `div_with_remainder`,
and the asymmetry above is why. Long division forms the remainder *in* its working array, so
dropping it saves nothing; Newton recovers `r = f - q*g` with a full multiplication, which is about
a third of the route's cost at the balanced shape. `%` cannot have the same treatment, and `gcd`'s
Euclidean loop wants the remainder anyway.

#### What is left

- **#194, half-GCD**, is unblocked by this section's argument and by this issue's product: it needs
  both a sub-quadratic `M` to be worth writing and a fast division to recurse on, and both now
  exist. `d^1.585 log d` against Euclid's `d^2` is a real crossing rather than the
  `d^2 log d`-against-`d^2` non-crossing it was.
- **#527**, the floor on the precision. The rule carries `k > t` as well as the inequality, and
  that floor is the one part of it no measurement here covers. The model puts the true floor near
  `t/68`, which would widen the Newton band by nearly two decades in `k` — in exactly the regime
  where it measured fastest.

#### Protocol

Every figure in this section was taken on **`7af2377` plus the change itself** — the two routes are
two entry points in one binary rather than two binaries, so there is no before-side tree to name
and nothing merged after `7af2377` can have moved one arm relative to the other. That stamp is a
**merge base** rather than a branch commit, which is what makes it resolvable later: #505 found 315
of 387 competitive rows naming branch commits that their own PR's merge destroyed, and the fix
there was to record `git merge-base HEAD origin/main` beside the commit for exactly this reason. A
prose protocol has no `Environment` struct to carry the pair, so the durable half is the one
written down. The
128-logical-core / 500 GB development workstation, one core (`taskset --cpu-list 12`), release
profile with the repository's default `Cargo.toml` settings (fat LTO, `codegen-units = 1`) and
`-C target-cpu=x86-64-v3` from `.cargo/config.toml`, `RUSTC_WRAPPER=""` and a private
`CARGO_TARGET_DIR`, under [`tools/benchlock.sh`](../../tools/benchlock.sh).

Each timed figure is the **fastest** of up to 7 repetitions, with the two routes interleaved
*within* each repetition rather than run arm-by-arm, so a transient on this shared workstation
lands on both. The routes are also checked against each other once per shape, outside the timing:
a crossover measured against a wrong answer is worthless, and `examples/division_crossover.rs`
asserts quotient and remainder equality before it starts the clock.

```sh
tools/benchlock.sh zb-sunny-193 env CARGO_TARGET_DIR="$PWD/target" RUSTC_WRAPPER="" \
  timeout --signal=INT --kill-after=60s 3000 \
  taskset --cpu-list 12 target/release/examples/division_crossover max_log=13
tools/benchlock.sh zb-sunny-193 ... taskset --cpu-list 12 \
  target/release/examples/univariate_scaling koalabear budget=1.0
```

## 5. Largest reachable degree, and the first stage to fail

**The first stage to stop is still `roots` on every field, and it moved** — 8 192 on KoalaBear and
512 on BN254 `Fr` after #193, from 4 096 and 256 — at one second per measurement. It is the only
stage that binds anywhere, and it is now the only one left that is neither quasi-linear nor
sub-quadratic: `div` joined the transforms on the other side of that line in #193 (§4.5), so what
remains is `roots`'s own structure rather than the cost of the division inside it. Goldilocks was
not re-taken; its 2 048 below is a pre-#193 figure.

The figures in the rest of this section are pre-#193 and kept as the record of what the sweep said
then. Arbitrary-point interpolation was
the first stage to stop on the three narrow fields when this section was written, at n = 1 024;
#162 stage 1 took it to 16 384 (§4.3.1) and it is no longer the binding stage anywhere. The
pre-#162 conclusion is kept here as the record of what the sweep said then:

> The first stage to stop is **arbitrary-point interpolation** (n = 1 024) on the narrow fields and
> **root finding** (d = 256) on BN254, at one second per measurement.

Both the old and the new binding stage are quasi-linear in the literature and
quadratic-or-worse here, so what changed is which one binds, not the character of the finding.
**#162 stage 2 has since taken arbitrary-point interpolation to 65 536 and 16 384** at a measured
exponent of 1.6 (§4.3.3), so it is now two doublings further from binding than `div` is and three
further than `roots`; `roots` itself is untouched by that change, since interpolation is not in it. The
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

**Stage 2 moved the exponent this table extrapolates on, so the rows above are an upper bound.**
The table is the quadratic form's, kept as the record of what stage 1 reached; the shipped
dispatcher takes the tree from `n = 128` at four bytes and `n = 256` above (§4.3.3), at a measured
**1.6**, so the real extrapolation to `2^20` samples is shallower than a square. **The number the
D1 route (#82) should be read against is that 1.6, not the "near 1" #162 asked for** — #559
amended that criterion
because near-1 needs the transform and the stage's `FiniteField` bound rules it out, and #606
holds the question of what a `KnownOrder` specialization would buy at exactly the degrees this
section reaches. No figure here is re-measured for stage 2; the shallower row is deliberately not
written down, because extrapolating from a measured exponent onto a table taken at a different one
would put a number on record that no run produced.

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
  NTT-based multiply as the single blocker; #124 built it, and §5.1 of that document — not §5 — is
  the current gap list, every item of which has since landed. Two caveats carry over to the
  multiply, and the first outlived its stated reason: `try_multiply_via_fft` rounds up to a
  power-of-two domain, so it inherits the two-adicity ceiling rather than the smooth-part one —
  **#125 landed the mixed-radix sizes and that function was never changed to use them**, so a caller
  wanting `2^24 · 127` must build the domain and call `multiply_over_domain`. Second, §4.1's
  crossover means the transform is the slower route below degree ~460 to ~12000 depending on the
  field.

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
   6.1x faster on the narrow fields and 2.0x to 2.7x on BN254 (§3.3). ~~**`fft_multiplication_crossover`
   was calibrated against the recursive kernel and is therefore now too high**~~ — recalibrated by
   #185, which also joined Karatsuba into the dispatch and found that the threshold had to be
   measured against Karatsuba rather than against schoolbook: 4096 / 512 / 512, with the 4-byte
   tier falling 4x from a figure that had never been measured. §4.1.2.
2. **Fast division by Newton iteration**, which `pow_mod_limbs` would then inherit, taking root
   finding from `log q * d^2` to `log q * d log d`.
3. ~~**A subproduct tree**, for multipoint evaluation and interpolation at arbitrary points, taking
   interpolation from `O(n^2)` to `O(n log^2 n)` and giving multipoint *evaluation* its first
   sub-quadratic path.~~ Done, #162 stage 2 — but it reaches `O(M(n) log n)` with a Karatsuba `M`,
   measured at **1.46 – 1.62**, not the `O(n log^2 n)` this item predicted, because the stage's
   bound is `FiniteField` and a transform needs `KnownOrder`. #559 amended #162's "near 1" exponent
   criterion to the multiplication exponent on that ground and #606 holds the specialization that
   would change it; §4.3.3 is the measurement and the decision. The quadratic form of stage 1 is
   kept reachable and is what the tree is differentially tested against.
4. **Modular composition** (Brent–Kung) only if D3's Graeffe route needs it; its memory profile is
   the one place where this workstation's 300 GB could genuinely bind.

D3's experimental half is unblocked in the narrow sense — there is now an NTT over the wide fields,
which there was not — but the degrees it can reach are set by items 1 and 2.
