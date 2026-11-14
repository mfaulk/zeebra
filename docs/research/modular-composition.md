# Modular composition and the Frobenius step of univariate factoring (#271)

**Measured at:** `f5c10079` for §2 (the composition kernel; `src/poly/univariate/compose_mod.rs`
is unchanged from there to the merge), and `5c817106` for §3 (whole `factorize`, with the
`Auto` route as shipped). `examples/modular_composition.rs` on the development workstation (AMD
Ryzen Threadripper PRO 5995WX), release profile with the repository's `-C target-cpu=x86-64-v3`,
`RUSTC_WRAPPER=""`, a private `CARGO_TARGET_DIR`, every run under `tools/benchlock.sh` and
`taskset -c 8`, arms interleaved within each repetition with the order rotated. Figures are the
median over repetitions with the minimum in parentheses.

#271 asked whether Brent–Kung modular composition, on Zeebra's existing dense matrix multiply,
beats repeated `pow_mod` at the degrees the resultant route actually produces. It does, by 1.4x to
39x per Frobenius application at degrees 81 and 729 and by 4.5x to 13.9x on whole factorizations of
random polynomials — except over a narrow field at degree 6 561, where the default block loses and
only a grown one wins. `factorize` now applies the Frobenius map by composition behind a
rent-or-buy rule (`FrobeniusRoute::Auto`), which keeps the one regime composition cannot repay —
few applications at high degree over a narrow field — on `pow_mod`.

---

## 1. What was built

`src/poly/univariate/compose_mod.rs`:

- `compose_mod(f, g, h)` — `f(g) mod h` by Brent–Kung baby-step/giant-step. With `m` baby steps
  `1, g, …, g^{m−1} mod h` as the rows of an `m × n` matrix and the length-`m` blocks of `f` as the
  rows of a `k × m` matrix, one `Matrix` product (the existing 2×8 register-tiled kernel,
  [`matmul-register-tiling.md`](matmul-register-tiling.md)) evaluates every block at `g`, and
  Horner in `g^m` joins the `k` blocks.
- `compose_mod_horner(f, g, h)` — the reference: `deg f` modular multiplications.
- `ModularComposer` — the baby steps for a fixed `(g, h)`, built once and reused, with `grow_to`
  extending the table in place. The Frobenius iteration `x^{q^{d+1}} = x^{q^d} ∘ x^q mod h` has a
  fixed inner argument, which is the whole reason this type exists.

The cost model that matters below, in units of one modular multiplication at degree `n`:

| operation | cost |
|---|---|
| `pow_mod` by `q` | `bits(q) + popcount(q) − 2`: 36 for KoalaBear, 95 for Goldilocks, ~380 for BN254 Fr |
| composer build, `m` baby steps | `m` |
| one composition of a reduced `f` | `n/m − 1`, plus a `(n/m) × m × n` matrix product |

The matrix product is `(deg f + 1) · n` multiply-adds **whatever `m` is**, so `m` only moves work
between the one-time build and every composition. §2's `m = 4√n` column is that trade measured.

Factorization over any finite field F_q uses `p(x)^q = p(x^q)`, so `factorize`'s distinct-degree
loop and the norm `h · h^q ⋯ h^{q^{d−1}}` inside its equal-degree splitter both become compositions
with `x^q mod h` — computed once by `pow_mod` — rather than one `pow_mod` each. `x^q mod g` for a
factor `g` of `f` is `(x^q mod f) mod g`, so the splitter needs no fresh exponentiation.

## 2. One Frobenius application at the recorded degrees

The degrees are the measured resultant degrees in
[`resultant-elimination.md`](resultant-elimination.md) §6.3 — 81, 729 and 6 561 — not chosen for
this benchmark. `h` is random monic of degree `n`, `ξ = x^q mod h`, and every arm computes
`ξ^q mod h`; the example asserts every arm returns the same polynomial. `compose_mod` is the
one-shot call (build plus compose); the composer columns are what a loop pays per application once
the composer exists.

| field | n | reps | `pow_mod` | compose, m=√n | build, m=√n | `compose_mod` | compose, m=4√n | Horner | `pow_mod` / compose √n | `pow_mod` / compose 4√n |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| KoalaBear | 81 | 5 | 0.164 (0.163) | 0.038 (0.037) | 0.035 (0.035) | 0.072 (0.072) | 0.012 (0.012) | 0.352 (0.347) | 4.33x | 13.82x |
| KoalaBear | 729 | 5 | 8.444 (8.135) | 6.127 (6.092) | 5.950 (5.205) | 12.026 (11.219) | 1.593 (1.417) | 163.209 (160.616) | 1.38x | 5.30x |
| KoalaBear | 6 561 | 3 | 322.553 (311.420) | 699.716 (687.931) | 712.485 (707.307) | 1 421.317 (1 421.242) | 194.856 (190.009) | — | **0.46x** | 1.66x |
| Goldilocks | 81 | 5 | 2.023 (2.014) | 0.181 (0.181) | 0.170 (0.170) | 0.358 (0.350) | 0.058 (0.058) | 1.746 (1.695) | 11.15x | 34.66x |
| Goldilocks | 729 | 5 | 127.220 (122.147) | 35.857 (34.447) | 35.286 (33.681) | 69.702 (68.592) | 9.098 (8.065) | 974.346 (972.867) | 3.55x | 13.98x |
| Goldilocks | 6 561 | 3 | 3 728.472 (3 684.403) | 3 201.000 (3 111.241) | 3 129.443 (3 098.657) | 6 302.270 (6 276.518) | 849.492 (819.142) | — | 1.16x | 4.39x |
| BN254 Fr | 81 | 5 | 74.768 (69.419) | 1.912 (1.839) | 1.598 (1.503) | 3.604 (3.166) | 0.661 (0.587) | 16.812 (15.462) | 39.11x | 113.06x |
| BN254 Fr | 729 | 5 | 3 816.118 (3 661.136) | 297.872 (289.713) | 280.580 (278.337) | 569.422 (566.982) | 79.648 (76.426) | 7 893.404 (7 808.793) | 12.81x | 47.91x |

Milliseconds. BN254 Fr at 6 561 was not run: one `pow_mod` there extrapolates past a minute and the
three-repetition row would have held the shared lock for the better part of an hour. Benchlock
records: `load=` 4.0–6.0 at the 81/729 run and the KoalaBear 6 561 run, 2.8 at the Goldilocks
6 561 run.

What the table says:

1. **The matrix product is not where the time goes.** At KoalaBear 6 561 the √n composition (81
   giant steps) takes 700 ms and the build (81 baby steps) 712 ms — the same 81 modular
   multiplications either way, so the 81 × 81 × 6 561 product is in the noise of the difference.
   Quadrupling `m` cuts the giant steps to 21 and the composition to 195 ms. This is why a slow
   generic `Ring` matrix kernel was good enough, and why Kedlaya–Umans-style asymptotics in the
   matrix step are not what would move these numbers.
2. **The crossover is `sqrt(n)` against `pow_cost(q)`.** A √n composition costs about `√n`
   modular multiplications against `pow_mod`'s `pow_cost`. KoalaBear's 36 sits between √729 = 27
   and √6 561 = 81, which is exactly where its ratio crosses 1; Goldilocks' 95 sits just above 81,
   and its 6 561 row is a bare 1.16x. BN254's ~380 is above every degree here.
3. **Horner is never the right choice**: it beats `pow_mod` only at degree 81 over Goldilocks and
   BN254 Fr, and loses to Brent–Kung everywhere — at 729 by 13.6x–14.0x even against one-shot
   `compose_mod`, build included.

## 3. Whole factorization

`factorize` with each `FrobeniusRoute` forced, through the `factorize_with_route_unstable` hook. Two
inputs: a random polynomial of degree `n`, whose distinct-degree loop runs to its largest factor's
degree (many Frobenius applications), and `n − 2` random linear factors times an irreducible
quadratic, where the loop applies the map **once** and stops — the shape of an eliminant whose roots
are being sought, and the case a composer can never repay. The example asserts all three routes
return the same factorization before timing.

| field | input | n | distinct factors | largest factor degree | reps | `PowMod` | `Composition` | `Auto` (default) | `PowMod` / `Composition` | `PowMod` / `Auto` |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| KoalaBear | random | 81 | 4 | 47 | 5 | 8.216 (8.118) | 1.818 (1.810) | 1.806 (1.793) | 4.52x | 4.55x |
| KoalaBear | random | 729 | 6 | 286 | 3 | 2 472.577 (2 460.777) | 428.906 (428.122) | 512.053 (495.367) | 5.76x | 4.83x |
| Goldilocks | random | 81 | 5 | 49 | 5 | 100.599 (99.011) | 8.450 (8.428) | 8.449 (8.305) | 11.91x | 11.91x |
| BN254 Fr | random | 81 | 11 | 22 | 5 | 1 758.305 (1 735.217) | 126.824 (124.775) | 127.304 (126.358) | 13.86x | 13.81x |
| KoalaBear | `n − 2` linear × quadratic | 729 | 728 | 2 | 3 | 52.631 (52.451) | 55.356 (55.244) | 52.943 (52.571) | 0.95x | 0.99x |
| KoalaBear | `n − 2` linear × quadratic | 6 561 | 6 560 | 2 | 3 | 2 317.637 (2 270.559) | 3 225.258 (3 159.241) | 2 318.330 (2 297.421) | **0.72x** | 1.00x |

Milliseconds; benchlock `load=` 21.4 at start and 13.5 at end. An earlier run of the same table at
`f3b873a8` — the commit before the rent rule counted the current application — ran at `load=` 1 593
and is not tabulated; its `PowMod` and `Composition` columns agree with these to within 2%.

`Composition` builds an `m = ⌈√n⌉` composer on first use and doubles `m` once the uses so far reach
`2m²/n`. `Auto`, the default, sizes the composer so that one composition costs at most half a
`pow_mod` (`m = max(⌈√n⌉, ⌈2n / pow_cost⌉)`, capped at `n` rows and 64 MiB), and uses `pow_mod`
until the cost already paid plus this application would reach the composer's price — the
ski-rental rule, at most about twice whichever choice hindsight would have made. A wide field buys
at once because its composer is cheaper than one `pow_mod`.

What the table says:

1. **On random polynomials composition wins 4.5x–13.9x end to end**, more the wider the field,
   because the distinct-degree loop applies the Frobenius map up to the largest factor's degree
   (47 to 286 times here) and the composer's growth takes each application well under one `pow_mod`.
2. **Forcing composition from the first application costs 39% at 6 561** on the one-application
   input (3.23 s against 2.32 s): a √n composer is 81 modular multiplications to build and 81 to
   apply, against 36 for the `pow_mod` it replaces. That is §2's 0.46x row arriving in a whole
   factorization, and it is exactly the root-finding shape.
3. **`Auto` keeps both**: parity (0.99x–1.00x) on the one-application input and 4.8x–13.8x on
   random ones. It gives up 19% against `Composition` at KoalaBear 729 (512 ms against 429 ms) —
   its composer is sized for `m = ⌈2n/36⌉ = 41` rather than 27, and each splitter instance rents
   one `pow_mod` first — which is the premium for not losing 39% at 6 561.

**Recommendation: adopt.** `FrobeniusRoute::Auto` is `factorize`'s default as of this change, and
`compose_mod` / `ModularComposer` are public primitives.

## 4. Where this does and does not touch Graeffe

**It does not touch root finding at all.** `roots` computes `gcd(f, x^q − x)` and splits the linear
part; the only Frobenius power it needs is `x^q` itself, which is one `pow_mod` and which
composition cannot produce (composition needs `x^q` as its inner argument). Equal-degree splitting
at `d = 1` has a trivial norm. So the #84 Graeffe route ([`graeffe-root-finding.md`](graeffe-root-finding.md))
and the gcd root finder are both untouched, and the question "is a composition-based root finder
competitive with Graeffe on the CICO eliminants" has the answer that there is no composition-based
root finder to compare: the composition speedup lives entirely in degrees `d ≥ 2` of the
distinct- and equal-degree stages, which root finding skips. The second §3 input is that case seen
from inside `factorize`, and `Auto` keeps it at parity with `pow_mod`.

Where composition **does** apply and Graeffe does not: full factorization of anything with
irreducible factors above degree one, including any eliminant whose interesting factors are not
linear. On random polynomials that is a 4.5x–13.9x speedup of the whole factorization at degree 81
(KoalaBear, Goldilocks, BN254 Fr) and 4.8x at 729 (KoalaBear) (§3).

## 5. What was not done

- **The FLINT same-machine comparison** the issue asks for. `libflint.so.22` is installed here as a
  runtime library (pulled in by Singular) but with no headers, no `pkg-config` entry and no
  `python-flint`, so a harness would mean provisioning FLINT first. Filed as a follow-up.
- **`is_irreducible`** still iterates Frobenius by `pow_mod` (`frobenius_iterated`); the same
  composer would apply. Not measured, so not changed.
- **Shoup's baby-step/giant-step distinct-degree factorization** (interval gcds over composed
  Frobenius powers) and Kaltofen–Shoup equal-degree splitting are the next algorithmic step after
  this one and were not attempted.
- **The eliminants themselves.** The resultant route moved to the private analysis repository in
  #668, so §2 and §3 use the recorded *degrees* over the recorded *field* with random polynomials
  of those degrees, not the eliminants. §4 argues why the root-finding tail is unaffected
  regardless.
