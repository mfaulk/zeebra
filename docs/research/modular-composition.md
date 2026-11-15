# Modular composition and the Frobenius step of univariate factoring (#271)

**Measured at:** `f5c10079` for §2 (the composition kernel; `src/poly/univariate/compose_mod.rs`
is unchanged from there to the merge), `5c817106` for §3 (whole `factorize`, with the `Auto`
route as shipped), `abf6dd0d` for §6 (the same-machine FLINT comparison), and `8b5608a3` for §7
(baby-step/giant-step distinct-degree factorization and the composed irreducibility test, #785).
`examples/modular_composition.rs` on the development workstation (AMD
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

- **The FLINT same-machine comparison** the issue asks for was split out to #784 and is §6.
- **`is_irreducible`** iterated Frobenius by `pow_mod`; #785 moved it onto composition (§7).
- **Shoup's baby-step/giant-step distinct-degree factorization** (interval gcds over composed
  Frobenius powers) was done in #785 (§7). Kaltofen–Shoup equal-degree splitting was not attempted.
- **The eliminants themselves.** The resultant route moved to the private analysis repository in
  #668, so §2 and §3 use the recorded *degrees* over the recorded *field* with random polynomials
  of those degrees, not the eliminants. §4 argues why the root-finding tail is unaffected
  regardless.

## 6. Same-machine comparison against FLINT (#784)

**Measured at:** `abf6dd0d`, one run under `tools/benchlock.sh` (`load=` 28.5 at start, 17.8 at
end), `taskset -c 8`, the four arms interleaved per repetition with the order rotated. FLINT 3.6.0
and GMP 6.3.0 from the comparand prefix (`tools/external/provision.sh`), one FLINT thread, driven
by `tools/external/flint-factor-driver` — a separate process; FLINT is never linked into Zeebra.
Zeebra is §3's `factorize` with the default `Auto` route, from `modular_composition factor-file`.
Each process times its own factorization call, so start-up and parsing are in neither column.

The inputs are §3's, byte for byte: `modular_composition export` writes them and both sides read
the same files. Before timing, the harness requires that Zeebra and all three FLINT arms return
**the same multiset of monic irreducible factors with multiplicity** — they did, on all six inputs.

| input | distinct factors | largest factor degree | reps | Zeebra (`Auto`) | FLINT default | FLINT CZ | FLINT KS | Zeebra / FLINT default |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| KoalaBear random 81 | 4 | 47 | 7 | 1.885 (1.876) | 1.343 (1.338) | 4.423 (4.390) | 1.346 (1.337) | 1.40x |
| KoalaBear random 729 | 6 | 286 | 7 | 521.608 (521.073) | 68.803 (68.686) | 733.587 (732.529) | 68.976 (68.860) | **7.58x** |
| Goldilocks random 81 | 5 | 49 | 7 | 8.980 (8.969) | 2.257 (2.256) | 21.988 (21.969) | 2.259 (2.252) | 3.98x |
| BN254 Fr random 81 | 11 | 22 | 7 | 126.807 (126.630) | 65.945 (65.852) | 502.533 (501.101) | 65.881 (65.772) | 1.92x |
| KoalaBear `n − 2` linear × quadratic 729 | 728 | 2 | 7 | 52.838 (52.789) | 58.770 (58.668) | 27.261 (27.135) | 58.732 (58.488) | 0.90x |
| KoalaBear `n − 2` linear × quadratic 6 561 | 6 560 | 2 | 3 | 2 318.125 (2 317.936) | 1 266.840 (1 265.974) | 690.950 (680.402) | 1 268.838 (1 268.408) | 1.83x |

Milliseconds, median (minimum). The last column is Zeebra's time over FLINT's: above 1 FLINT is
faster. Zeebra's column reproduces §3's `Auto` column to within 2% on every row. "FLINT default" is
`nmod_poly_factor` for the two word-size primes and `fmpz_mod_poly_factor` for BN254 Fr; "CZ" and
"KS" force `*_factor_with_cantor_zassenhaus` / `*_factor_with_kaltofen_shoup` (nmod) and
`fmpz_mod_poly_factor_cantor_zassenhaus` / `_kaltofen_shoup` (fmpz_mod).

**Build floors differ, in FLINT's favour.** FLINT's configure picked `-march=znver3 -O3` for this
host, and GMP is host-tuned; Zeebra is built at the repository's `x86-64-v3` floor. Matching the
floors would make FLINT slower, not faster, so the asymmetry cannot flatter Zeebra.

What FLINT picks, from its documentation (`doc/source/nmod_poly_factor.rst`,
`fmpz_mod_poly_factor.rst`, `nmod_poly.rst` of the 3.6.0 release):

- `nmod_poly_factor`: "first checks for small special cases, deflates `f` if it is of the form
  `p(x^m)`, … performs a square-free factorisation, and finally runs either Cantor-Zassenhaus or
  Berlekamp … Currently Cantor-Zassenhaus is used by default unless the modulus is 2".
- `fmpz_mod_poly_factor`: "choosing the best algorithm for given modulo and degree. Choice is based
  on heuristic measurements" — no algorithm or threshold is named.
- Kaltofen–Shoup is documented as "the fast version of Cantor-Zassenhaus … a baby step/giant step
  strategy for the distinct-degree factorization step"; the Brent–Kung composition entry points
  (`*_compose_mod_brent_kung_precomp_preinv`, with a precomputed `√deg h × deg h` matrix of powers of
  `g`) are documented as "particularly useful if one has to perform several modular composition of
  the form `f(g)` modulo `h` for fixed `g` and `h`" — the Frobenius-iteration use. **No degree or
  modulus threshold is documented** for either the factoring algorithm or the composition method.

The timings contradict the `nmod_poly_factor` sentence: on every input, word-size or BN254, FLINT's
default is within 0.3% of forced Kaltofen–Shoup and 2x–11x away from forced Cantor–Zassenhaus.
At these degrees and moduli the default **behaves as Kaltofen–Shoup**, and the documented
"Cantor-Zassenhaus by default" is evidently stale. That is an inference from timings, not a reading
of FLINT's source, which this comparison deliberately did not consult.

What the table says:

1. **On random polynomials FLINT is 1.4x–7.6x faster**, and the gap grows with the largest factor's
   degree: 1.4x at 81 over KoalaBear, 7.6x at 729. That is the gap between Zeebra's distinct-degree
   loop — one Frobenius application per degree, however cheap the composer makes each — and
   Kaltofen–Shoup's baby-step/giant-step distinct-degree factorization, which needs about `√d`
   giant steps and interval gcds instead of `d` single-degree gcds. §5 already names Shoup's
   baby-step/giant-step DDF as the next step; this is its measured price.
2. **FLINT's own CZ arm is slower than Zeebra everywhere a random polynomial is factored** (1.4x at
   KoalaBear 729, 2.3x–4.0x at degree 81): Zeebra's composition-driven Cantor–Zassenhaus is the
   faster plain CZ. What it lacks is the algorithm, not the arithmetic.
3. **On the one-application input the ranking reverses at 729 and returns at 6 561.** Zeebra beats
   FLINT's default (KS) by 10% at 729 but loses 1.8x at 6 561, and FLINT's forced CZ is fastest of
   all — 1.9x ahead of Zeebra at 729, 3.4x at 6 561. Here there is one Frobenius application, so
   the difference is not composition: it is the root-splitting stage over 727 or 6 559 linear
   factors, i.e. FLINT's base `nmod_poly` multiplication, division and gcd at degree 6 561 against
   Zeebra's. KS's baby-step setup is the overhead its default pays on this shape.
Reproduce with the recipe in `tools/external/flint-factor-driver/README.md`; the factor agreement
check runs on every invocation.


## 7. Baby-step/giant-step distinct-degree factorization and a composed irreducibility test (#785)

**Measured at:** `8b5608a3` (the branch before its rebase past #787, which changed only
re-export lists in `src/lib.rs` and `src/poly/mod.rs`), `examples/modular_composition.rs` modes `irreducible`, `ddf` and
`defaults`, one binary, three consecutive runs under `tools/benchlock.sh` (owner
`zb-785-takeover`) and `taskset -c 8`, 2026-11-15 UTC. `load=` 1.12 at the first START and 1.11 at
the last END. One `cargo clippy` ran niced on cores 32–47 for about ten seconds during `ddf`. Every
mode asserts that all its routes agree (the same verdict, or the same factorization) before
timing, and routes are interleaved within each repetition. A `—` marks an arm skipped because it
would take minutes.

### 7.1 `is_irreducible`

Rabin's test needs `x^(q^(n/p))` for each prime `p | n` and `x^(q^n)`. `Iterate(route)` walks
`k = 1, 2, …, n` with one Frobenius application per step by the given §3 route. `Doubling`, the
new default, reaches `x^(q^k)` by an addition chain on `k`: `x^(q^(2a)) = x^(q^a) ∘ x^(q^a)` by one
one-shot composition, and `x^(q^(a+1))` by one application, so about `2·log2 n` compositions per
power instead of `n` applications. `irreducible` inputs are random irreducibles (by rejection),
and `random` inputs are random monic polynomials.

| field | input | n | reps | `Iterate(PowMod)` | `Iterate(Auto)` | `Doubling` (default) | `PowMod` / `Doubling` | `Iterate(Auto)` / `Doubling` |
|---|---|---:|---:|---:|---:|---:|---:|---:|
| KoalaBear | irreducible | 81 | 7 | 11.306 (11.300) | 1.172 (1.168) | 0.945 (0.943) | 11.96x | 1.24x |
| Goldilocks | irreducible | 81 | 7 | 144.375 (144.271) | 6.795 (6.779) | 5.702 (5.693) | 25.32x | 1.19x |
| BN254 Fr | irreducible | 81 | 7 | 5 354.786 (5 328.444) | 123.594 (123.458) | 105.726 (105.649) | 50.65x | 1.17x |
| KoalaBear | irreducible | 729 | 3 | 5 405.549 (5 388.344) | 584.676 (583.919) | 223.219 (223.090) | 24.22x | 2.62x |
| KoalaBear | random | 81 | 7 | 3.775 (3.753) | 0.622 (0.618) | 0.591 (0.586) | 6.38x | 1.05x |
| Goldilocks | random | 81 | 7 | 48.092 (48.042) | 4.089 (4.084) | 3.986 (3.984) | 12.07x | 1.03x |
| BN254 Fr | random | 81 | 7 | 1 775.858 (1 774.597) | 90.824 (90.650) | 88.256 (88.149) | 20.12x | 1.03x |
| KoalaBear | random | 729 | 3 | 5 406.245 (5 401.248) | 586.094 (585.799) | 130.819 (130.769) | 41.33x | 4.48x |
| Goldilocks | random | 729 | 3 | 27 647.712 (27 561.651) | 1 636.787 (1 636.223) | 842.093 (841.929) | 32.83x | 1.94x |
| BN254 Fr | random | 729 | 3 | — | 18 357.665 (18 355.484) | 9 852.281 (9 851.352) | — | 1.86x |
| KoalaBear | random | 6 561 | 3 | — | — | 17 578.942 (17 556.672) | — | — |

Milliseconds. `Iterate(Composition)` is within 1% of `Iterate(Auto)` except at KoalaBear 729, where it
is 466.8 ms against 585 ms. That is §3's rent premium again, and `Doubling` beats both.

`pow_mod` iteration, the route before this change, loses everywhere: 6.4x–51x. `Doubling` also
beats the best iterated composition route, by 1.03x–1.24x at degree 81 and 1.9x–4.5x at 729,
because its composition count grows as `log n` rather than `n`.

### 7.2 Distinct-degree factorization

`factorize` with each `DistinctDegreeRoute` forced (the Frobenius route is `Auto` throughout):

- `Iterated` is the loop as it was: one application and one gcd per degree.
- `BabyStepGiantStep` is Shoup's method from degree one: `l ≈ sqrt(n/2)` baby steps, then one gcd
  per interval of `l` degrees against `∏ (x^(q^(lj)) − x^(q^i))`.
- `Auto`, the new default, iterates until the degree reaches `sqrt(deg r / 2)` of what remains `r`.
  It then switches to baby-step/giant-step, reusing the powers already computed as baby steps.

| field | input | n | distinct factors | largest factor degree | reps | `Iterated` | `BabyStepGiantStep` | `Auto` (default) | `Iterated` / BSGS | `Iterated` / `Auto` |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| KoalaBear | random | 81 | 4 | 47 | 7 | 0.993 (0.991) | 0.726 (0.720) | 0.801 (0.795) | 1.37x | 1.24x |
| Goldilocks | random | 81 | 5 | 49 | 7 | 5.476 (5.223) | 4.260 (4.119) | 4.420 (4.252) | 1.29x | 1.24x |
| BN254 Fr | random | 81 | 11 | 22 | 7 | 102.156 (102.081) | 98.098 (98.001) | 97.640 (97.584) | 1.04x | 1.05x |
| KoalaBear | random | 729 | 6 | 286 | 3 | 311.563 (311.323) | 178.885 (178.858) | 180.784 (180.355) | 1.74x | 1.72x |
| Goldilocks | random | 729 | 8 | 568 | 3 | 2 029.451 (2 027.882) | 1 114.499 (1 112.219) | 1 090.337 (1 090.039) | 1.82x | 1.86x |
| BN254 Fr | random | 729 | 6 | 653 | 3 | — | 13 262.918 (13 235.469) | 13 363.543 (13 319.696) | — | — |
| KoalaBear | random | 6 561 | 8 | 2 734 | 3 | — | 45 852.307 (45 815.424) | 46 165.488 (46 147.818) | — | — |
| KoalaBear | `n − 2` linear × quadratic | 729 | 728 | 2 | 3 | 36.181 (36.176) | 64.979 (64.964) | 36.243 (36.231) | **0.56x** | 1.00x |
| KoalaBear | `n − 2` linear × quadratic | 6 561 | 6 560 | 2 | 3 | 1 449.798 (1 448.668) | 9 084.677 (9 078.646) | 1 448.437 (1 448.389) | **0.16x** | 1.00x |

Milliseconds.

1. **On random inputs baby-step/giant-step wins 1.04x–1.82x end to end.** The gain grows with the
   largest factor's degree, which sets how many gcds the iterated loop takes: 22 at BN254 Fr 81
   gains least, and 568 at Goldilocks 729 gains most.
2. **Forced from degree one, it loses 1.8x–6.3x on the root-finding shape.** All factors there have
   degree at most two, so the iterated loop is done after two steps, while baby-step/giant-step
   still builds `sqrt(n/2)` baby steps and their giant steps.
3. **`Auto` keeps both, as §3's `Auto` did.** It is at parity (1.00x) on the low-degree shape and
   within 2% of baby-step/giant-step on random inputs. It is 10% behind at KoalaBear 81 (0.801 ms
   against 0.726 ms) and 2% ahead at Goldilocks 729.

Against §3's whole-factorization figures (at `5c817106`, with the iterated loop and Frobenius `Auto`),
KoalaBear random 729 goes from 512 ms to 181 ms. That includes everything else that landed in
between; the paired 1.72x in this table is the part #785 owns.

### 7.3 The public defaults

`defaults` times the public `factorize` and `is_irreducible` only: no route hooks, as a user
would call them. It agrees with the tables above: KoalaBear random 729 is 181.1 ms to factor and
130.8 ms to test, and the low-degree 729 input is 36.1 ms.

| field | n | reps | `factorize` random | `factorize` `n − 2` linear × quadratic | `is_irreducible` random |
|---|---:|---:|---:|---:|---:|
| KoalaBear | 81 | 7 | 0.816 (0.803) | 1.581 (1.523) | 0.676 (0.667) |
| Goldilocks | 81 | 7 | 4.268 (4.265) | 9.296 (9.233) | 4.022 (3.988) |
| BN254 Fr | 81 | 7 | 97.977 (97.905) | 277.705 (277.316) | 88.315 (88.233) |
| KoalaBear | 729 | 3 | 181.098 (180.916) | 36.104 (36.097) | 130.795 (130.701) |
| Goldilocks | 729 | 3 | 1 090.699 (1 089.222) | 393.978 (393.746) | 845.616 (841.975) |

**Recommendation: adopt.** `DistinctDegreeRoute::Auto` and `IrreducibilityRoute::Doubling` are the
defaults as of this change. Not measured: a before/after of the public API against the tree before
#785 (the `defaults` mode builds against an older tree only with the route modes removed). Also
not measured: Kaltofen–Shoup equal-degree splitting, which remains the next step.

Reproduce:

```text
export CARGO_TARGET_DIR=/buildcache/cargo-target/zeebra-785 RUSTC_WRAPPER=""
cargo build --release -j24 --example modular_composition
for m in irreducible ddf defaults; do
  tools/benchlock.sh <owner> taskset -c 8 "$CARGO_TARGET_DIR"/release/examples/modular_composition $m
done
```
