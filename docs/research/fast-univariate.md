# Fast univariate algorithms: the wide-field root of unity, and what each stage costs

Reference for D2 (#83), a child of the #68 epic and a prerequisite for D3.

Both routes into #68 end in the same place: one univariate polynomial of very large degree over a
large prime field, whose roots are wanted. This records what Zeebra's univariate layer can actually
do there — measured, not estimated — and what it would need to go further.

Every number below comes from

```text
cargo run --release --example univariate_scaling
```

on the development workstation (64 cores, 300 GB RAM; the measurements are single-threaded). The
sweeps shown used `budget=1.0`, one second of wall clock per measurement.

## 1. The blocker, cleared

`primitive_element` and `root_of_unity` were `unimplemented!()` for `PrimeFieldElement256`, because
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
| mul | 1.93 – 2.14 → **2** | schoolbook; there is no NTT-based multiply |
| div | 1.63 – 2.12 → **2** | in-place long division, after §2 |
| ntt | 0.97 – 1.18 → **1** (n log n) | `fft::evaluate`, recursive |
| intt | 0.92 – 1.18 → **1** | `fft::interpolate`; §3 on what #118 then removed |
| lagrange | 2.68 – 2.98 → **3** | `lagrange_interpolate` at arbitrary abscissae |
| roots | 1.64 – 2.01 → **2** | `roots`, dominated by `x^q mod f` |

### 3.1 Largest size reached in one second per measurement

| stage | Mersenne-31 | KoalaBear | Goldilocks | BN254 `Fr` |
|---|---|---|---|---|
| mul | 32 768 | 32 768 | 32 768 | 8 192 |
| div | 32 768 | 32 768 | 32 768 | 8 192 |
| ntt | **2** — s = 1 | 8 388 608 | 8 388 608 | 2 097 152 |
| intt | **2** — s = 1 | 4 194 304 | 2 097 152 | 262 144 |
| lagrange | 1 024 | 1 024 | 1 024 | 512 |
| roots | 4 096 | 4 096 | 2 048 | **256** |

Absolute cost at the largest size reached, and the peak bytes there:

| field | stage | size | seconds | ns/element | peak bytes |
|---|---|---|---|---|---|
| KoalaBear | mul | 2^15 | 2.19 | 66 821 | 1 048 560 |
| KoalaBear | div | 2^15 | 2.30 | 70 109 | 1 572 848 |
| KoalaBear | ntt | 2^23 | 1.94 | **232** | 469 762 016 |
| KoalaBear | intt | 2^22 | 2.03 | 485 | 301 989 856 |
| KoalaBear | lagrange | 2^10 | 2.74 | 2 677 318 | 65 544 |
| KoalaBear | roots | 2^12 | 1.72 | 418 695 | 393 176 |
| BN254 `Fr` | mul | 2^13 | 1.59 | 193 550 | 1 048 512 |
| BN254 `Fr` | div | 2^13 | 1.64 | 199 615 | 1 572 800 |
| BN254 `Fr` | ntt | 2^21 | 2.16 | **1 032** | 469 761 920 |
| BN254 `Fr` | intt | 2^18 | 1.89 | 7 209 | 75 497 344 |
| BN254 `Fr` | lagrange | 2^9 | 3.16 | 6 167 733 | 131 104 |
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

### 3.2 Memory as a function of degree, in bytes

The measured peak is exactly proportional to `n * size_of::<F>()` in every stage, with an integer
constant:

| stage | peak bytes | 64-bit field | BN254 `Fr` |
|---|---|---|---|
| mul | `4 n B` | 32 n | 128 n |
| div | `6 n B` | 48 n | 192 n |
| ntt | `7 n B` | 56 n | 224 n |
| intt | `9 n B` | 72 n | 288 n |
| lagrange | `8 n B` | 64 n | 256 n |
| roots | `12 n B` | 96 n | 384 n |

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

## 4. The gap list

### 4.1 Multiplication: no quasi-linear path exists

`DensePolynomial`'s `Mul` is schoolbook, measured at exponent 2.00. There is no Karatsuba, no
Toom–Cook, and **nothing in the crate uses the NTT for multiplication** — `src/fft/` is reachable
only from its own tests and now from `examples/univariate_scaling.rs`. The pieces for an
NTT-based multiply are all present: a two-adic root of unity over every field of interest,
`FFTDomain`, `evaluate`, `interpolate`. What is missing is the wrapper that pads to a power of two,
transforms both inputs, multiplies pointwise and inverts — plus a CRT or Kronecker fallback for
Mersenne-31, whose two-adicity of 1 rules the transform out entirely.

The transform-size ceiling is worth stating as a real bound rather than an asymptotic one: `2^24`
for KoalaBear, `2^28` for BN254, `2^32` for Goldilocks and BLS12-381. At `7 n B`, BN254's full
`2^28` ceiling is **60 GB** and, extrapolating from 1 032 ns/element, about **5 minutes** — so for
BN254 the two-adicity bound, not this workstation, is what binds. BLS12-381's `2^32` would need
962 GB, so there memory binds first, at roughly `2^30`.

### 4.2 Modular composition: absent

`Polynomial::compose` computes `f(g)` **unreduced**, as `sum a_i * g^i` with `g.pow(i)` recomputed
per term. Its output has degree `deg(f) * deg(g)`, so it cannot be used where `f(g) mod h` is
wanted, and its only caller is `shift` (composition with `x + k`). There is no Brent–Kung, no
baby-step/giant-step structure, and no modular composition of any kind. Brent–Kung would need
`sqrt(d)` modular powers of g held at once — `sqrt(d) * d * B` bytes, which at `d = 2^20` over
BN254 is 34 GB against the 0.4 GB a multiplication at that degree needs. The issue's note that
composition's memory profile is worse than multiplication's is borne out by that arithmetic.

### 4.3 Multipoint evaluation and interpolation: present but cubic

Two things exist and neither is quasi-linear:

- `fft::evaluate` / `fft::interpolate` are `O(n log n)` but only over a **geometric power-of-two
  domain** `1, w, w^2, ...`. They cannot evaluate at an arbitrary point set, which is what an
  evaluation–interpolation resultant needs.
- `lagrange_interpolate` handles arbitrary abscissae and is **cubic**, measured at 2.97. It builds
  each of the n Lagrange basis polynomials by multiplying up `n - 1` linear factors, which is
  `O(n^2)` per basis polynomial.

So arbitrary-point interpolation is the **first stage to stop** on all three narrow fields, at
n = 1 024, and the second on BN254 at n = 512. There is no subproduct tree: no routine builds
`prod (x - x_i)` as a balanced binary tree, no simultaneous remaindering down such a tree, and no
fast transposed form for interpolation. That machinery — a subproduct tree plus fast division by
Newton iteration — is what D1's evaluation–interpolation route would need, and it does not exist in
any partial form.

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

The first stage to stop is **arbitrary-point interpolation** (n = 1 024) on the narrow fields and
**root finding** (d = 256) on BN254, at one second per measurement. Both are stages that are
quasi-linear in the literature and quadratic-or-worse here. The NTT, the one stage with a
quasi-linear implementation, reaches `2^23` in the same second.

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

What quasi-linear multiplication would be worth, from the measured NTT: one multiplication at
degree `2^20` over BN254 is three transforms of size `2^21`, so about 6.5 s. Root finding needs
`O(log q)` of them — 254 squarings, each a multiply plus a reduction, and a Newton-iteration
reduction is a few multiplies — so on the order of **1 to 2 hours** against 202 days. A ~3 000x
gap, from machinery that is one wrapper away for multiplication and a subproduct tree away for the
rest.

## 6. Go / no-go for #68

**Superseded in part.** [`elimination-beyond-grobner.md`](elimination-beyond-grobner.md) is the
epic-level assessment, written against six primary sources including the technical disclosures of
two of the three official 2026 CICO-2 solutions. Three things change for this section:

- the transform ceiling is set by the **smooth part** of `q - 1`, not the two-adicity alone, so
  KoalaBear reaches `2^24 · 127` with a mixed-radix FFT rather than stopping at `2^24`;
- **half-gcd** is a fourth gap, since `gcd.rs` is plain Euclid — but the published univariate route
  needs neither it nor Newton division nor a subproduct tree;
- the `R_P = 8` challenge was solved by interpolation plus Graeffe root finding at degree `3^13`,
  which needs a `2^22` transform — **inside** the ceiling this document measured. So an NTT-based
  multiply is the single blocker, and §5 of that document is the current gap list.

**Not a no-go, but the governing constraint is not where the epic placed it.** #68 assumed the
univariate stage would be "FFT/NTT-dominated, and reportedly bound by memory access". On this
codebase it is neither: the NTT is the healthiest stage in the layer, memory is not binding at any
degree reachable in reasonable time, and the cost is in stages that are quadratic or cubic because
no fast algorithm for them has been written.

Concretely, before D1 or D3 can run at interesting degrees:

1. **NTT-based multiplication** (`O(n log n)`), with a fallback for low-two-adicity fields. Every
   prerequisite now exists; this is the highest-value single piece of work in the layer.
2. **Fast division by Newton iteration**, which `pow_mod_limbs` would then inherit, taking root
   finding from `log q * d^2` to `log q * d log d`.
3. **A subproduct tree**, for multipoint evaluation and interpolation at arbitrary points. D1's
   evaluation–interpolation route depends on this and there is nothing to build on.
4. **Modular composition** (Brent–Kung) only if D3's Graeffe route needs it; its memory profile is
   the one place where this workstation's 300 GB could genuinely bind.

D3's experimental half is unblocked in the narrow sense — there is now an NTT over the wide fields,
which there was not — but the degrees it can reach are set by items 1 and 2.
