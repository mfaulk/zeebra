# Univariate primitives against FLINT and NTL, one primitive at a time

**Measured at:** `6b150bd7` for every row except `mulfft`, and `5abda6b3` for the `mulfft` rows.
Both are #1206 branch commits, not on `main`; after the merge they are kept as the tag
`measured/1206-univariate-primitives`. The machine was an M4 Pro laptop (macOS, arm64), **unpinned
and not isolated**: these figures are indicative and are not a workstation qualification. The raw
tables are in
[`research/1206-univariate-primitives/`](../../research/1206-univariate-primitives/README.md).

#784 compared whole factorization against FLINT and found Zeebra 1.4×–7.6× slower
(`modular-composition.md` §6). That figure did not say which primitive carries the gap. This study
times the primitives the solve path calls, one at a time, against FLINT 3.6.0 and NTL 11.6.0, over
four fields at n = 2⁸ … 2²⁰.

## 1. Method

- **Separate processes, same bytes.** `examples/univariate_primitives.rs` exports one job per
  (field, primitive, n), seeded, and runs it with Zeebra's default public entry point. The FLINT
  and NTL drivers in `tools/external/univariate-primitives/` read the same file. Each side times
  only its own call. Parsing, building operands and formatting results are all outside every
  timer.
- **Agreement before timing.** For every row, the harness requires every arm's output to equal
  Zeebra's byte for byte before it times anything; roots are compared as a sorted set. Every
  reported row passed. That includes the monic gcd, the Bézout cofactors of `xgcd`, which are
  unique given their degree bounds, and the resultant, across all three libraries and all four
  fields.
- **Timing.** Three rounds, with the arm order rotated each round. Each process makes 1 to 7 calls,
  enough for about 0.3 s, and reports their median. Each arm's figure is the median over rounds. A
  (field, primitive) pair stops growing once Zeebra or FLINT takes more than 2 s a call. NTL is
  dropped from a row once it does.
- **Fields.** KoalaBear (31-bit, 2-adicity 24), Goldilocks (64-bit, 2-adicity 32), 2⁶⁴ − 59
  (64-bit, 2-adicity 1, so no power-of-two transform exists), and BN254 Fr (254-bit, 2-adicity 28).
- **Operands.** These are the shapes in the driver README: random dense polynomials, monic where
  the primitive needs it, and distinct random points. `roots` runs on a random monic polynomial of
  degree n. That has about one root on average, so its cost is almost entirely the Frobenius power.

### 1.1 The build floor is not symmetric

Zeebra is built `--release` with fat LTO. It sets no `target-cpu` on aarch64
(`.cargo/config.toml` scopes `x86-64-v3` to x86_64), so it compiles for baseline armv8-a, and NEON
is available only where LLVM auto-vectorizes. FLINT and NTL are Homebrew's arm64 bottles. FLINT was
configured with `FLINT_HAVE_FFT_SMALL`, its hand-vectorized small-prime FFT module. The drivers are
built with `-O2 -mcpu=native`, which affects only their own thin code. Each library's reported
figure is the one it ships with, as in #784.

### 1.2 What `mul` measures

`mul` is the `&a * &b` operator. Every univariate algorithm in Zeebra is built on it, including
`pow_mod`, Newton division, `compose_mod`, the subproduct trees and half-GCD's matrix products. It
dispatches only to schoolbook and Karatsuba. It **cannot reach the transform**, because choosing a
domain needs `KnownOrder` and a random source, and `Mul`'s signature carries neither
(`fast-univariate.md` §4.1). `mulfft` is `zeebra::multiply`, the dispatcher that can reach the
transform. FLINT and NTL run their ordinary product in both rows.

An earlier run of this harness timed Zeebra's result formatting along with the call. Decimal
conversion of BN254 elements dominated its small rows, which made BN254 `mul` read 20× at n = 256
where it is 1.04×. That run was discarded, and none of its figures appear here.

## 2. Results

Zeebra ÷ FLINT, given as **n = 2⁸ · n = 2¹² · the largest n both completed**. Above 1 means Zeebra is
slower.

| primitive | KoalaBear | Goldilocks | 2⁶⁴ − 59 | BN254 Fr |
|---|---|---|---|---|
| `mul` | 1.54 · 16.95 · **163.07** (2¹⁹) | 1.07 · 5.20 · 53.58 (2¹⁹) | 1.54 · 6.73 · 71.66 (2¹⁹) | 1.04 · 5.86 · 33.00 (2¹⁷) |
| `mulfft` | 1.53 · 8.57 · 8.35 (2²⁰) | 2.47 · 2.89 · 3.67 (2²⁰) | 1.44 · 6.73 · **74.32** (2¹⁹) | 2.24 · 2.61 · 3.08 (2²⁰) |
| `divrem` | 1.76 · 21.78 · **223.43** (2¹⁸) | 3.74 · 10.35 · 81.38 (2¹⁸) | 4.75 · 13.93 · 75.34 (2¹⁷) | 2.27 · 8.75 · 27.37 (2¹⁵) |
| `gcd` | 2.05 · 2.32 · 9.77 (2¹⁷) | 1.60 · 1.61 · 4.86 (2¹⁷) | 1.99 · 2.04 · 6.27 (2¹⁷) | **0.64** · 1.13 · 2.37 (2¹⁵) |
| `xgcd` | 1.57 · 2.67 · 11.92 (2¹⁷) | 1.32 · 1.70 · 5.71 (2¹⁷) | 1.69 · 2.16 · 7.37 (2¹⁷) | **0.68** · 1.35 · 2.22 (2¹⁴) |
| `powmod` | 2.84 · 27.47 · 72.47 (2¹⁵) | 3.74 · 15.03 · 29.92 (2¹⁴) | 5.88 · 24.08 · 33.17 (2¹³) | 3.01 · — · 6.80 (2¹⁰) |
| `roots` | 2.30 · 10.51 · 22.91 (2¹⁵) | 2.58 · 8.13 · 14.99 (2¹⁴) | 3.34 · 10.84 · 14.37 (2¹³) | 2.92 · — · 6.30 (2¹⁰) |
| `multieval` | 2.83 · 2.96 · 3.79 (2¹⁹) | 3.37 · 2.01 · 2.10 (2¹⁹) | 4.17 · 4.07 · 13.72 (2¹⁷) | 1.55 · 1.36 · 1.47 (2¹⁶) |
| `interpolate` | 2.12 · 2.68 · 3.45 (2¹⁹) | 1.74 · 1.56 · 1.79 (2¹⁹) | 2.17 · 3.27 · 12.05 (2¹⁷) | FLINT has no fast `fmpz_mod_poly` interpolation |
| `compose` | 1.85 · 14.15 · 21.50 (2¹³) | 1.97 · 6.49 · 9.05 (2¹³) | 2.67 · 8.43 · 11.92 (2¹³) | 1.46 · — · 4.20 (2¹¹) |
| `resultant` | 2.01 · 2.31 · 20.72 (2¹⁶) | 1.62 · 1.67 · 12.42 (2¹⁶) | 2.03 · 2.13 · 16.39 (2¹⁶) | **0.64** · 1.94 · 5.41 (2¹⁴) |

Zeebra ÷ NTL, given as **n = 2⁸ · the largest n NTL completed**:

| primitive | KoalaBear | Goldilocks | 2⁶⁴ − 59 | BN254 Fr |
|---|---|---|---|---|
| `mul` | 0.85 · 47.11 (2¹⁹) | 0.52 · 25.24 (2¹⁹) | 0.72 · 33.50 (2¹⁹) | 2.32 · 60.81 (2¹⁷) |
| `mulfft` | 0.85 · 2.38 (2²⁰) | 1.19 · 1.75 (2²⁰) | 0.69 · 33.54 (2¹⁹) | 4.90 · 5.55 (2²⁰) |
| `divrem` | 0.91 · 32.46 (2¹⁸) | 0.80 · 27.01 (2¹⁸) | 1.06 · 24.09 (2¹⁷) | 3.78 · 43.28 (2¹⁵) |
| `gcd` | 1.44 · 7.58 (2¹⁷) | 0.18 · 2.53 (2¹⁷) | 0.22 · 3.29 (2¹⁷) | 0.96 · 7.24 (2¹⁵) |
| `xgcd` | 1.11 · 9.42 (2¹⁷) | 0.30 · 3.46 (2¹⁷) | 0.37 · 4.48 (2¹⁷) | 1.34 · 7.09 (2¹⁴) |
| `powmod` | 2.70 · 44.34 (2¹⁵) | 2.55 · 22.53 (2¹⁴) | 3.92 · 24.40 (2¹³) | 12.01 · 25.33 (2¹⁰) |
| `roots` | 2.57 · 26.22 (2¹⁵) | 2.09 · 15.61 (2¹⁴) | 3.27 · 17.35 (2¹³) | 11.37 · 24.32 (2¹⁰) |
| `multieval` | 0.50 · **0.02** (2¹⁵) | 0.12 · 0.01 (2¹⁴) | 0.15 · 0.02 (2¹⁴) | 0.42 · 0.05 (2¹³) |
| `interpolate` | 0.55 · **0.02** (2¹⁵) | 0.07 · 0.01 (2¹³) | 0.10 · 0.02 (2¹³) | 0.26 · 0.05 (2¹²) |
| `compose` | 3.61 · 31.49 (2¹³) | 1.81 · 12.14 (2¹³) | 2.52 · 15.45 (2¹³) | 9.70 · 31.82 (2¹¹) |
| `resultant` | 1.39 · 16.22 (2¹⁶) | 0.18 · 6.20 (2¹⁶) | 0.22 · 8.23 (2¹⁶) | 0.96 · 15.46 (2¹⁴) |

NTL's vector `eval` and `interpolate` are quadratic, so Zeebra's subproduct trees are 20–100×
faster at the top of those rows. Over BN254 at n ≤ 1 024, Zeebra's gcd, xgcd and resultant beat
FLINT, which runs its 254-bit Euclid on `fmpz` with a reduction per step.

## 3. Where the ratio exceeds 1.5×, ranked

The faster side's technique comes from its documented API (function names and documented
algorithms in the public headers) and from the literature. No library source was read
(`external-provenance-policy.md`).

1. **The product the univariate layer is built on is Karatsuba at every size.** The ratio climbs as
   n^0.58 (KoalaBear `mul`: 1.5× → 163×). Every primitive built on that product inherits the
   climb: `divrem` up to 223×, `powmod` 72×, `compose` 21×, `roots` 23×. FLINT's `nmod_poly_mul`
   goes through Kronecker substitution (`_nmod_poly_mul_KS*`) and the small-prime FFT
   (`_nmod_poly_mullow_fft_small`). Its division is Newton iteration on a precomputed inverse
   (`_nmod_poly_divrem_newton_n_preinv`), and its Frobenius power reuses that inverse
   (`nmod_poly_powmod_x_fmpz_preinv`). NTL multiplies by FFT above a crossover of 20 coefficients
   (`NTL_ZZ_pX_FFT_CROSSOVER`). Zeebra already has a quasi-linear product, `zeebra::multiply`,
   and on KoalaBear `mulfft` holds a flat 8–10× where `mul` climbs to 163×. So most of this
   gap is **routing, not a missing algorithm**: the transform exists and the layer cannot call it.
   #1205's cached inverse (opt-in) is the `powmod` half of the FLINT technique.
2. **No quasi-linear product over a prime without a large power-of-two root of unity.** 2⁶⁴ − 59
   has 2-adicity 1, so `mulfft` falls back to Karatsuba and reaches 74× FLINT and 34× NTL. The
   same holds for every prime whose 2-adicity is too small for the degree. FLINT and NTL multiply
   over any modulus through small word-size NTT primes. FLINT combines Kronecker substitution with
   fft_small. NTL's `FFTRep` holds a polynomial modulo `NumPrimes` FFT primes and recombines by CRT.
   Neither needs a root of unity in the target field.
3. **The transform itself costs a constant factor.** With the transform, Zeebra is 8–10× FLINT on
   KoalaBear and 2.4× NTL, 3.4–3.7× FLINT on Goldilocks, and 2.6–3.1× FLINT and about 5× NTL on
   BN254. FLINT's fft_small is hand-vectorized and works in double precision with a small set of
   primes. That technique is the subject of #1208, which measures packed 31-bit butterflies
   against Plonky3. Over BN254, NTL is 2× FLINT itself, through the multi-modular FFT route of
   item 2, which is cheaper than a 254-bit NTT in the field.
4. **gcd, xgcd and the resultant fall further behind with degree.** Their ratios are about 2× up to
   n = 2¹² and climb to 5–21× at 2¹⁶–2¹⁷. FLINT dispatches gcd, xgcd and the resultant to half-GCD
   (`_nmod_poly_gcd_hgcd`, `_nmod_poly_xgcd_hgcd`, `nmod_poly_resultant_hgcd`). Zeebra's `gcd`
   reaches half-GCD only from degree 6 144 (32-bit), and its half-GCD multiplies through item 1's
   Karatsuba operator. The default `resultant` is Euclidean at every degree. #1207 added a
   half-GCD resultant kernel, but it is opt-in, because the bivariate route never reaches its
   crossover. This item is mostly item 1 again.
5. **Multipoint evaluation and interpolation sit at a steady 2–4×**, or 12–14× on 2⁶⁴ − 59. Both
   sides use the subproduct tree. The tree's products are the transform where Zeebra has one
   (KoalaBear, Goldilocks), and Karatsuba where it does not (2⁶⁴ − 59). The steady factor on the
   NTT fields is item 3's constant, and the climb on 2⁶⁴ − 59 is item 2.
6. **Modular composition: 9–21× FLINT and 12–31× NTL.** All three are Brent–Kung, FLINT's through
   `_nmod_poly_compose_mod_brent_kung*`. Its cost is a matrix product and a set of modular products,
   and the gap is the product of item 1 and the matrix kernel. NTL is fastest here. Its
   `CompMod` works in a transformed representation of the modulus, which #1205's candidate 3
   (transform-domain reuse) also describes.

## 4. Rows a solve-path caller reaches, and the follow-ups

- **`roots` and `powmod`** are the first stage to stop on every field (`fast-univariate.md` §5).
  So are `factorize`'s distinct-degree loop (`powmod`, `compose`) and point solving's root
  extraction. All of them are items 1–2.
- **`gcd`** runs inside `roots` and the equal-degree split. That is item 4, which item 1 mostly
  covers.
- **`multieval` and `interpolate`** are the resultant route's sample and recovery stages
  (`resultant-elimination.md` §4). That is item 5.
- **`resultant`**: the bivariate route evaluates one scalar resultant per sample. #1207 recorded
  that its operand degrees stay below the half-GCD crossover, so no follow-up is filed for it.

Follow-ups filed: #1225 for item 1 (route the layer's products to the transform), and #1226 for
item 2 (a multi-modular product for fields without a usable two-adic root). Item 3 is #1208.

## 5. What this does not establish

- **No workstation figure.** These are unpinned laptop timings on arm64. A deciding comparison
  needs `tools/benchlock.sh` with `taskset` on the bench host, using the README's recipe, and the
  ratios there may differ. The x86 build floor (Zeebra at `x86-64-v3`, FLINT with AVX2
  fft_small) is a different asymmetry from the one §1.1 states.
- **No solve-level claim.** These are per-primitive ratios. Whole `roots`, `factorize` or solve
  figures need their own callers, as `fast-univariate.md` §4.3.4 requires.
