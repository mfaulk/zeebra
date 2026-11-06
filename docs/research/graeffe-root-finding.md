# Graeffe root finding: the published algorithm, the degree it consumes, and whether Zeebra's NTT is access-bound

Reference for D3 (#84), a child of the #68 epic. This is the **reading and scoping half**; the
implementation half is blocked on #124 (polynomial multiplication through the transform).

The issue imposes one evidentiary rule, and this document honours it strictly: *no figure from a
paper is recorded here without having been read in the PDF.* Every paper figure below carries a
section or table reference to a PDF that was obtained and read. Figures that could not be verified
are marked `UNVERIFIED`.

> ## Retraction, 2026-11-05 — §7.2's no-go was wrong on two of its three reasons
>
> This document was written against ePrint 2025/950, 2025/937 and 2025/1916 ("[PC]"). It did not
> have **2026/1254** (Sanso–Vitto, *Top Gun: Degree Annihilation Attacks on Poseidon*) or
> **2026/1905** (Bak–Hostettler), both of which were read for
> [`elimination-beyond-grobner.md`](elimination-beyond-grobner.md) and landed in `ce76647`, one
> merge after this document. Those two sources describe the **actual disclosed solutions** to two of
> the three registered 2026 targets, and they overturn the conclusion here.
>
> **What stands.** §2.1's reading of [PC] is accurate: [PC] really does restrict its own security
> analysis to CICO-1 and really does say that for the CICO-2 Poseidon-31 challenge "the best known
> attack would be the Gröbner basis computation together with the FGLM algorithm, or the mutant XL
> algorithm". The quote is verbatim and correctly placed. §2.3's degree derivation stands and is
> independently confirmed — see below. §5's rejection of the `4/3` model stands. §6's measurement
> that the pre-#161 kernel is allocation-bound stands.
>
> **What is retracted.** The inference from [PC]'s exclusion to "no-go on every registered
> instance". [PC] declining to analyse CICO-2 is a statement about *that paper's* scope, not about
> what is possible — and 2026/1254 §4.2 records that the `R_P = 8` CICO-2 instance **was solved**,
> by a route this document mis-identified. Specifically:
>
> - **§7.2 reason 2 is false.** This document asserted that "the univariate object for CICO-2 is the
>   resultant", of degree `3^16`–`3^20`, needing `2^26`–`2^32`. It is not. 2026/1254 §4.2
>   interpolates `P_1`, the **first constrained output coordinate**, at degree `3^13`, applies
>   Graeffe root finding to it, and then evaluates the full permutation on each root to test the
>   *second* constraint — "instead of computing a resultant", explicitly "to avoid the memory cost of
>   resultant computations while exploiting the FFT-friendly structure of the KoalaBear field". The
>   working degree is `3^13`, not `3^18`, and the required transform is `2^21`–`2^22`, **inside**
>   KoalaBear's `2^24`.
> - **§7.2 reason 3 is irrelevant, not false.** The `≈16·3^{5·rounds}` resultant-construction cost
>   is correct for the *resultant* route and simply does not apply to the route that was used.
> - **§2.4's table** is therefore right about `δ` and wrong about which column matters: its
>   "resultant degree" and "`n` for the resultant" columns describe a route the disclosed attack did
>   not take.
>
> **The degree is not in dispute.** This document derived `δ = α^{R_F+R_P−1}` from [PC] §2.3's
> Poseidon2 one-round-skip rule; `elimination-beyond-grobner.md` §2.1 derives `δ = 3^{R_P+5}` from
> 2026/1254's `(1,[1])` skip. At `R_F = 6` the two exponents coincide identically, and both give
> `3^11`, `3^13`, `3^15` for `R_P = 6, 8, 10`. Two independent readings of two different papers
> agreeing on all three registered targets is the strongest evidence in either document.
>
> **Closed by §9.5, 2026-11-06.** The paragraph below was written before 2026/1254 was read in this
> document. It has since been read directly from the PDF and **§9.5 resolves the discrepancy with
> arithmetic**: the `2^31` family count is confirmed rather than overturned — the paper endorses the
> ≈1-root heuristic and defines its "common-root strategy" as independent filtering, so two of the
> three candidates below are *refuted by the source* — and the apparent four orders of magnitude
> reduce to ~1.1 once §9.2's per-family total is corrected to the stages the published algorithm
> actually runs per family. Read §9.5 instead of the next paragraph; it is retained unedited.
>
> **What was open, and it was the number that decided the gate.** §9.3 estimates ≈`p` ≈ `2^31`
> families for a CICO-2 witness, from ~1 expected `F_p`-root per family times a `1/p` chance that a
> root satisfies the second constraint. That cannot be reconciled with 2026/1254 Table 1, which
> reports the `R_P = 8` CICO-2 instance solved in **7 hours on 96 GPUs** — `2^31` families at §9.2's
> ~2 min each is ~8 100 core-years, and no amount of GPU parallelism closes that. One of the two is
> wrong and this document cannot say which without reading 2026/1254 directly. Candidates: `P_1` is
> not root-count-generic the way §9.3 assumes; the `(1,[1])` parametrization supplies more usable
> freedom per family than one variable; or "common-root strategy" (2026/1254 §4.2's own phrase for
> it) does more than independent `1/p` filtering. **Treat §9.2 and §9.3's family arithmetic as
> superseded-pending-verification, and do not quote `2^31` as settled.**
>
> **Consequence for the gate.** D3's implementation half is *more* valuable than §7.2 concluded, not
> less: the univariate route's degree fits the existing power-of-two NTT ceiling at two of three
> registered targets, and NTT-based multiplication (#124) is the only missing foundational
> primitive. §10's PR decomposition is unaffected in content and rises in priority.
> `elimination-beyond-grobner.md` §0 and §3 are the current authority; read them first.
>
> Retained rather than edited away, per this repository's practice of keeping superseded reasoning
> visible — and because the shape of the error is instructive. It came from treating one paper's
> declared scope as a bound on what is achievable, which is exactly the inference #84 warns against
> when it says not to infer a complete algorithm from a partial reading.

## 1. The papers, and how they were obtained

`eprint.iacr.org/*.pdf` is behind a Cloudflare interstitial that returns HTTP 403 from this
environment — confirmed again on 2026-11-05 with `curl`, a browser `User-Agent` and a `Referer`.
The working route is the Wayback Machine's **raw-content** form,
`https://web.archive.org/web/<ts>id_/https://eprint.iacr.org/<year>/<id>.pdf`; the `id_` suffix is
essential, since without it the rewritten viewer HTML is returned instead of the original bytes.
Wayback rate-limits aggressively and `curl --retry 12 --retry-delay 25 --retry-all-errors` cleared
every 429. This supersedes the "PDF not obtained" note the issue was opened with: **Wayback raw
content is the first thing to try for an ePrint PDF from this environment**, ahead of the HAL and
institutional-page routes that `docs/research/additional-benchmarks.md` §8 records for other papers.

| # | paper | authors | pages | obtained |
|---|---|---|---:|---|
| **[P950]** | *Breaking Poseidon Challenges with Graeffe Transforms and Complexity Analysis by FFT Lower Bounds* (ePrint 2025/950) | Ziyu Zhao (Tsinghua), Jintai Ding (XJTLU / BCAM Bilbao) | 24 | yes, Wayback raw |
| **[P937]** | *Attacking Poseidon via Graeffe-Based Root-Finding over NTT-Friendly Fields* (ePrint 2025/937) | Antonio Sanso (Ethereum Foundation), Giuseppe Vitto (Zircuit) | 14 | yes, Wayback raw |
| **[PC]** | *Graeffe-Based Attacks on Poseidon and NTT Lower Bounds* (ePrint 2025/1916) | Zhao, Sanso, Vitto, Ding | 26 | yes, Wayback raw |
| **[JAZ]** | *Solving CICO-2 bounty instances of Poseidon* (slides, 2025-03-15) | Bak, Bariant, Boeuf, Hostettler, Jazeron (INRIA/DGA/Télécom SudParis) | 24 | yes, direct from `gjazeron.github.io` |

**The Springer DOI in the issue resolves differently than the issue assumed.**
`10.1007/978-3-032-35412-9_16` is *Advances in Cryptology — CRYPTO 2026*, LNCS, pp. 471–498, titled
*Graeffe-Based Attacks on Poseidon and NTT Lower Bounds* — the **merger of [P950] and [P937]**, by
all four authors. Springer's copy is paywalled (Unpaywall reports `is_oa: false`, no OA locations),
so **[PC]** (ePrint 2025/1916) is the usable version of the conference paper and is what is cited
below when the two source papers agree. Where they differ, the source paper is cited.

[JAZ] is not named in #84 but is the **primary source for the attack [PC] improves on** — it is
reference `[7]` in [PC], the "previous record". It is also already cited in #88 for its hardware
line. It was read in full and is the source for the CICO-2 resultant degrees in §2.

The authors' implementation is at `https://github.com/zhaoziyu0008/Goldilocks_solver` ([PC] §1,
C++/CUDA, "about 4,000 to 5,000 lines"). Not read; not needed for this document.

## 2. The problem instance, and its degree

### 2.1 The precise algebraic problem

**Not** CICO in general. [PC] Definition 1 states the CICO problem for `F: F_p^t -> F_p^t` and
`u < t` as finding `X_0..X_{t-1-u}, Y_0..Y_{t-1-u}` with
`F(X_0,…,X_{t-1-u},0,…,0) = (Y_0,…,Y_{t-1-u},0,…,0)`. The attack [PC] accelerates solves the
**univariate** case `u = 1` — CICO-1. [PC] §1 and §4.2 both say so without qualification:

> "It is important to emphasize that the above security analysis only applies when the CICO problem
> requires just the last coordinate to be fixed. For example, the Poseidon-31 challenge in Table 1
> requires `Perm(X_0,…,X_13,0,0) = (Y_0,…,Y_13,0,0)`. Then the best known attack would be the
> Gröbner basis computation together with the FGLM algorithm, or the mutant XL algorithm, where the
> main bottleneck is linear algebra, which is no longer memory-bound." — [PC] §1

That single paragraph decides most of §7's go/no-go and is the most important thing in the paper for
this repository. **Zeebra's three registered 2026 KoalaBear challenges are CICO-2** (`k = 2` in
`src/grobner/research/challenge.rs`), which is the case [PC] explicitly excludes from its own
analysis.

### 2.2 The polynomial representation required

Dense coefficient vectors, padded to the transform size — not sparse, not multivariate, not a
straight-line program. [P937] §5.3 is explicit about the layout: "the interpolated polynomials are
represented as vectors of size `2^28` and `2^31` for instances 6_8 and 6_9, respectively, each entry
occupying 32 bytes", and "we pad polynomials with zeros to the nearest power-of-two length before
applying the NTT". [P937] §5.3 adds that "all implemented polynomial arithmetic primitives are
optimized to use NTTs whose sizes are at most twice the size of their input polynomials."

This is exactly `UnivariatePolynomial<F>`'s representation, so nothing in Zeebra's `poly::univariate`
layer needs a new data structure.

### 2.3 Round skipping, and the degree — derived

[PC] §2.3 gives the rule in two halves, and the halves differ by one round:

- **Poseidon** (no initial linear layer): two rounds can be skipped. "Under these choices, the
  permutation becomes a univariate polynomial in `y_0` of degree `α^{R_F + R_P − 2}`" — [PC] §2.3,
  *The 2-Round Attack for Poseidon*, with the construction given explicitly: let
  `(λ_0,…,λ_{t-1})` be the last row of `M_E^{-1}`, take
  `y_{t-1} = (Σ λ_i/λ_{t-1} · RC_{t+i} + RC^α_{t-1}/λ_{t-1})^α`, set `y_2 = … = y_{t-2} = 0` and
  `y_1 = (λ_0/λ_1)^α · y_0`.
- **Poseidon2** (initial linear layer present): only one round can be skipped, giving degree
  `α^{R_F + R_P − 1}` — [PC] §2.3, *The 1-Round Attack for Poseidon2*. [PC] adds that "the impact
  is less significant for Poseidon2, owing to the presence of the initial linear
  transformation — this is precisely why [21] introduced the initial linear transform in the first
  place."

[PC] attributes the trick to [JAZ]/[7] and [JAZ] slide 17 ("Round skipping trick") describes the
same construction independently. [JAZ] slide 18 gives `δ = d^{R_F − 1 + R_P}` for its CICO-1 attack,
which is the same exponent as [PC]'s Poseidon2 rule.

**The coordinator's figure `3^13`, derived.** The registered `poseidon31-cico-rf6-rp8` has
`alpha = 3`, `t = 16`, `R_F = 6`, `R_P = 8` over `KOALABEAR_PRIME`, and its verifier runs
`permutation_plus_linear` — the variant **with** an initial linear layer
(`src/grobner/research/poseidon.rs:381`). That is the Poseidon2 side of [PC] §2.3's rule, so one
round is skipped and

```
δ = α^(R_F + R_P − 1) = 3^(6 + 8 − 1) = 3^13 = 1 594 323        (log2 δ = 20.60)
```

**`3^13` reproduces.** Two independent cross-checks that the formula and the padding rule are right:

- [JAZ] slide 5 lists the Poseidon2-31k family as `t = 16, d = 3`, matching the registry's
  `alpha = 3`. ([PC] Table 1 lumps "M31 / KoalaBear" under a single `x ↦ x^5` entry; for KoalaBear
  that contradicts both the registry and [JAZ], and is treated here as a Table-1 simplification.
  Flagged as a **discrepancy between sources**, resolved in favour of the registry.)
- [P937] §5.3 states the interpolated vectors for the BLS12-381 `6_8` and `6_9` instances are of
  size `2^28` and `2^31`. Independently: Poseidon, `α = 5`, skip 2, so `δ = 5^12 = 2^27.86` and
  `5^13 = 2^30.19`, whose next powers of two are **`2^28` and `2^31`**. The formula and the
  "pad to the next power of two" rule both reproduce the paper's own vector sizes exactly.

**A caveat on `permutation_plus_linear`.** Zeebra's generator is a hybrid: it has Poseidon2's
initial linear layer but Poseidon's same-MDS-every-round and all-state round constants in the
partial rounds ([PC] §2.2 lists exactly those three differences; `src/grobner/research/poseidon.rs`
applies `self.mds` throughout). The skip count depends only on whether the **initial** linear layer
is present, which it is — so `α^{R_F+R_P−1}` is the right rule and `3^13` the right degree.

> **No longer reconstructed, as of §9.5.** This paragraph previously read "Marked **reconstructed**:
> the paper states the rule for Poseidon and for Poseidon2, not for this hybrid, and no source read
> here states the hybrid case." 2026/1254 has since been read directly, and §9.5.2 derives the
> `(1,[1])` construction for this exact hybrid from §2.2 of that paper — two affine equations in the
> skipped state, in rows `0` and `1` of `M^{-1}`. The *degree* was never the doubtful part; the
> *construction* was, and it is now written out rather than inferred — **and asserted**: §9.5.2's
> oracle is green in `src/grobner/research/univariate_cico.rs`, so the hybrid's `(1,[1])` family is
> verified rather than reconstructed.

### 2.4 Degrees and required transform sizes, for every registered instance

> **PARTLY SUPERSEDED.** The `δ`, "`n` for Graeffe/interp." and "`n` for a product" columns stand and
> are confirmed independently by `elimination-beyond-grobner.md` §2.1. The **"resultant degree" and
> "`n` for the resultant" columns describe a route the disclosed `R_P = 8` attack did not take** —
> it interpolated the first constrained output coordinate at `δ = 3^13` and filtered candidates
> against the second constraint. See the retraction at the head of this document.

`δ` is the degree from §2.3. For CICO-2 the univariate object whose roots are wanted is not `δ` but
the **resultant**, whose degree [JAZ] slide 19 gives as `d^{2(R_F−1)+R_P}` and calls an
*experimental result* — [JAZ] slide 22 expands on it: the expected degree is `d^{2R_F+2R_P}`,
"however, we experimentally noticed that the degree of the resultant is `d^{2R_F+R_P}`", saving a
factor `d^{R_P}`, and "it also corresponds to the degree of the polynomial ideal: why is that?"
**Unproven in the source and recorded as such.** This repository has an independent corroboration at
tiny size: `docs/research/resultant-elimination.md` §2 measures the resultant degree on the
2-round slice as exactly the Bézout bound `d²`, with no collapse — consistent with the loose bound,
not with the tighter experimental one, at a round count too small to separate them.

**That has since been separated.** `resultant-elimination.md` §6.3 measures the resultant's degree
on three registered slices, one of which has `R_P > 0` and therefore distinguishes the two formulas:
`R_F=2 R_P=2` gives **729**, which is slide 22's `d^{2R_F+R_P}` and not slide 19's
`d^{2(R_F−1)+R_P}` (81) nor the Bézout bound (6 561). All three rows agree with slide 22 and none
with slide 19. Still unproven — the confirmation is experimental, as the source's own is — but no
longer unexamined in this repository.

Required radix-2 transform size is `2^ceil(log2(δ+1))` for interpolating or Graeffe-transforming a
degree-`δ` polynomial (an order-2 Graeffe step needs only `n ≥ δ+1`, not `2δ+1` — see §3.2), and
`2^ceil(log2(2δ+1))` for an ordinary product of two degree-`δ` polynomials.

| registered instance | objective | field | α | R_F | R_P | `δ` | `n` for Graeffe/interp. | `n` for a product | resultant degree | `n` for the resultant |
|---|---|---|---:|---:|---:|---|---:|---:|---|---:|
| `poseidon31-cico-rf6-rp6` | CICO-2 | KoalaBear | 3 | 6 | 6 | `3^11` = 177 147 | `2^18` | `2^19` | `3^16` = 4.30e7 | **`2^26`** |
| `poseidon31-cico-rf6-rp8` | CICO-2 | KoalaBear | 3 | 6 | 8 | **`3^13`** = 1 594 323 | **`2^21`** | **`2^22`** | `3^18` = 3.87e8 | **`2^29`** |
| `poseidon31-cico-rf6-rp10` | CICO-2 | KoalaBear | 3 | 6 | 10 | `3^15` = 1.43e7 | `2^24` | `2^25` | `3^20` = 3.49e9 | **`2^32`** |
| `poseidon256-cico-2025-rf6-rp11` | CICO-1 | BLS12-381 `Fr` | 5 | 6 | 11 | `5^15` = 3.05e10 | **`2^35`** | `2^36` | — | — |
| `poseidon256-cico-2025-rf6-rp16` | CICO-1 | BLS12-381 `Fr` | 5 | 6 | 16 | `5^20` = 9.54e13 | `2^47` | `2^48` | — | — |
| `poseidon64-cico-2025-rf6-rp13` | CICO-1 | Goldilocks | 7 | 6 | 13 | `7^18` = 1.63e15 | `2^51` | `2^52` | — | — |

The 2025 rows are CICO-1 (`k: 1` in `challenge.rs`) and are therefore **exactly the shape [PC]
attacks**. They are also the only three registry rows with no public solution recorded. The
Goldilocks row is the **40-bit tier that [PC] did not solve**: [PC] Table 3 reports the 24-, 28- and
32-bit tiers (`R_P = 7, 8, 10`) solved, and [PC] §1 says "none of the Poseidon-64 instances were
solved until our work". `R_P = 13` is the tier above those, at `δ = 7^18 = 2^50.5`.

For context, the instances [PC] actually solved, by the same formulas:

| [PC] instance | field | α | R_F | R_P | skip | `δ` | required `n` | paper's stated size |
|---|---|---:|---:|---:|---:|---|---:|---|
| `P_6_8` | BLS12-381 | 5 | 6 | 8 | 2 | `5^12` | `2^28` | `2^28` ([P937] §5.3) |
| `P_6_9` | BLS12-381 | 5 | 6 | 9 | 2 | `5^13` | `2^31` | `2^31` ([P937] §5.3) |
| `P2_6_7` | Goldilocks | 7 | 6 | 7 | 1 | `7^12` | `2^34` | mixed radix, `q·2^32` with `q = 15` ([P937] §5.3) |
| `P2_6_8` | Goldilocks | 7 | 6 | 8 | 1 | `7^13` | `2^37` | mixed radix ([PC] §4.2) |
| `P2_6_10` | Goldilocks | 7 | 6 | 10 | 1 | `7^15` | `2^43` | `2^32 · 5 · 257` ([PC] §4.2) |

### 2.5 KoalaBear's two-adicity, and the hard ceiling

`docs/research/fast-univariate.md` §1.1 records **24** for KoalaBear and states that the figure was
*derived rather than quoted*: `two_adicity()` reads `s` off the compiled-in modulus, and three
independent checks pin it — a `BigUInt` recomputation of `2^s · m` against `q − 1`, an oracle check
against `ark_ff::FftField::TWO_ADICITY` for the wide fields, and the cyclotomic identity
`1 + w + … + w^{n−1} = 0` with distinctness of the `n` powers. The throwaway run in §6.1 printed
`s = 24` again from the shipped `two_adic_decomposition`.

So, with `p = 2^31 − 2^24 + 1 = 2 130 706 433` and `p − 1 = 2^24 · 127`:

| | KoalaBear | Goldilocks | BN254 `Fr` | BLS12-381 `Fr` |
|---|---:|---:|---:|---:|
| two-adicity `s` | **24** | 32 | 28 | 32 |
| max radix-2 transform | `2^24` | `2^32` | `2^28` | `2^32` |
| odd part of `p − 1` | **127** | `3·5·17·257·65537` | 226 bits | 223 bits |
| max **mixed-radix** transform | `2^24 · 127` ≈ `2^31.0` | `2^64` (`p−1` itself) | — | — |

KoalaBear's odd part is a single prime, 127, so its mixed-radix headroom above `2^24` is a factor of
127 and no more. [PC] §4.1 notes "all prime numbers appearing in the Poseidon Challenge have quite
smooth multiplicative group sizes" and gives the Goldilocks and BLS12-381 factorizations; KoalaBear's
is not given there, and `2^24 · 127` is **smooth but shallow** — it supports the Graeffe iteration
(which wants a large `r = 2^k`, and `k = 24` is available) far better than it supports large
transforms.

## 3. The algorithm, as pseudocode

The issue is emphatic that the transform is not the algorithm, and it is right: the transform is two
half-degree squarings, and the root finder built on it is where all the content is. Everything in
this section was read in [PC] §3–§4 or [P937] §4–§5. Steps marked **(reconstructed)** were not
stated in those sections and are inferred.

### 3.1 Definition and the two lemmas the algorithm rests on

[PC] Definition 2: for `ℓ` coprime to `p`, `GT_ℓ(f)` is the unique `g` with

```
g(x^ℓ) = f(x) · f(x·ω_ℓ) · … · f(x·ω_ℓ^(ℓ−1)),       ω_ℓ a primitive ℓ-th root of unity
```

- **[PC] Lemma 1** — `GT_ℓ(f) ∈ F_p[x]` and `deg GT_ℓ(f) = deg f`. Proof read: the product is
  invariant under `x ↦ ω_ℓ x`, so only exponents divisible by `ℓ` survive; the coefficients are
  fixed by every Galois conjugation, hence lie in `F_p`.
- **[PC] Lemma 2** — `GT_{ℓ_0}(GT_{ℓ_1}(f)) = GT_{ℓ_0 ℓ_1}(f)`. This is what makes the whole
  method work: a transform of smooth order factors into cheap prime-order steps.
- **[PC] §3.2, after Lemma 2** — with `ℓ | p − 1`: if `µ ∈ F_p` is a root of `f` then `µ^ℓ` is a
  root of `GT_ℓ(f)`; **conversely**, if `ν` is a root of `GT_ℓ(f)` and has one (hence all) of its
  `ℓ`-th roots in `F_p`, then at least one of them is a root of `f`. The converse is the direction
  the un-squaring step in §3.3 relies on.
- **[P937] §4.2** gives the same statement as a divisibility: `∏_{i=0}^{r−1}(x − ω_r^{r−i}α) =
  x^r − α^r` divides `G_r(P)(x^r)`.

### 3.2 The order-2 transform, and its cost in NTTs

[PC] §3.2: writing `f(x) = f_0(x²) + x·f_1(x²)`,

```
f(x)·f(−x) = f_0(x²)² − x²·f_1(x²)²    ⇒    GT_2(f)(x) = f_0(x)² − x·f_1(x)²
```

and "this can be computed using two NTTs and one invNTT with any NTT group size larger than `d`."
[P937] §5.3 states the sign convention the issue flagged as open:

```
G_2(P) = (−1)^d · ( P_e(x)² − x·P_o(x)² )          where P(x) = P_e(x²) + x·P_o(x²)
```

and records the cost correction explicitly: their first implementation "followed the original
definition: computing the product of two polynomials of degree `d`, thereby requiring three NTTs of
size `2d`", and the identity above "reduce[s] the computational cost by performing only three NTTs
of size `d` instead. As a result, we expect the total runtime of the attack to be reduced by
approximately half." — [P937] §5.3. **So an order-2 Graeffe step costs three transforms of size
`≥ d+1`, not `≥ 2d+1`.** That is a factor of two in transform size against an ordinary product and
is why §2.4's "`n` for Graeffe" column is one power of two below its "`n` for a product" column.

For `ℓ ≥ 3`, [PC] §3.2 follows [24] (van der Hoeven–Monagan) with a recursive product tree on
`P_h(x) = f(x)f(xω_ℓ)…f(xω_ℓ^{h−1})`:

```
P_h(x) = f(x)                                        if h = 1
       = P_{h/2}(x) · P_{h/2}(x·ω_ℓ^{h/2})           if h even
       = f(x) · P_{(h−1)/2}(x·ω_ℓ^{(h−1)/2}) · P_{(h−1)/2}(x·ω_ℓ^{(h+1)/2})   otherwise
```

[PC] notes this computes `GT_ℓ(f)(x^ℓ)` rather than `GT_ℓ(f)(x)`, which makes it simpler to
implement but costs "roughly `2ℓ` times more memory than the output polynomial size" — acceptable
only because orders above 2 are applied to small-degree polynomials in the final steps.
[P937] §4.1 adds the complexity argument: computing `GT_{r^k}` directly as an `r^k`-fold product
costs `O(r^k d log(r^k d))` against `O(k·r·d·log(rd))` for `k` iterated order-`r` steps.

### 3.3 Algorithm A — the general root finder

[PC] Algorithm 2, transcribed verbatim in structure:

```
ALGORITHM A  (root finding by Graeffe transform)             [PC] Algorithm 2
input   f ∈ F_p[x] of degree d; the factorization p − 1 = q_1 q_2 … q_k
output  a root of f in F_p, if one exists

 1  β ← p − 1 ;  g_0 ← f
 2  for i ← 1 to k:
 3      β ← β / q_i
 4      g_i ← GT_{q_i}(g_{i−1})  mod (x^β − 1)
 5  if g_k has no roots in F_p: return ⊥
 6  µ_k ← a root of g_k
 7  for i ← k down to 1:
 8      µ_{i−1} ← a common root of g_{i−1} and (x^{q_i} − µ_i)
 9  return µ_0
```

Four things the text adds, all read in [PC] §3.2 immediately after the algorithm:

- **The reduction in line 4 is what keeps it cheap.** `GT_{q_i}(g_{i−1})` has the same degree as
  `g_{i−1}` (Lemma 1), but every root that descends from an `F_p`-root of `f` lies in the subgroup
  of order `β`, hence is a root of `x^β − 1`; so reducing modulo `x^β − 1` loses no wanted root and
  caps the degree at `β − 1`. "As soon as `β` drops below the degree of `f`, the subsequent
  computations rapidly become trivial, since the polynomials involved are then of much smaller
  degree."
- **The un-squaring in line 8 is where the sign/root ambiguity is resolved, and it is resolved by a
  gcd, not by a choice.** `µ_i` has `q_i` distinct `q_i`-th roots; the one that is a root of
  `g_{i−1}` is picked out by the common root of `g_{i−1}` and `x^{q_i} − µ_i`. [PC]: "In the
  computation of common roots in line 8, one can first reduce `g_{i−1}` modulo `(x^{q_i} − µ_i)`,
  so that the resulting polynomials have low degree. When `p − 1` is smooth, the cost of these steps
  becomes negligible." There is no ambiguity to resolve by guessing and no sign convention to track
  through the descent — the ambiguity is *decided by the polynomial*.
- **Termination** is by exhaustion of the factor list: `k` forward steps, `k` backward steps. The
  `⊥` branch at line 5 is the only failure mode, and it is exact rather than heuristic: if the
  fully-transformed `g_k` has no `F_p`-root then `f` has none, because the forward direction of the
  §3.1 correspondence maps every `F_p`-root of `f` to an `F_p`-root of every `g_i`.
- **Multiplicity** is not handled and does not need to be in this algorithm: it returns *one* root,
  and line 8's gcd is unaffected by `µ_i` being a multiple root. Multiplicity matters only for the
  *all-roots* variant of §3.6, where [P937] §4.3's tangent method requires `α_i^r` to be a **simple**
  root of `G_r(P)` and the input to split with distinct roots; [P937] §4.4 handles the shortfall by
  randomizing — "the polynomial `P(x)` is first replaced by `P(x + τ)`" for random `τ ∈ F_p` — to
  "ensure a sufficient number of such roots".

### 3.4 Algorithm B — the Goldilocks instantiation

[PC] Algorithm 3, "designed to reduce memory usage and clarify the main idea of Algorithm 2", with
`p_64 − 1 = 2^32 · 3 · 5 · 17 · 257 · 65537`:

```
ALGORITHM B  (root finding over Goldilocks)                  [PC] Algorithm 3
input   f ∈ F_{p64}[x] of degree d           output  a root in F_{p64}, if one exists

 1  β ← p64 − 1 ;  µ ← 1 ;  g ← f
 2  while β is even:                       # 32 order-2 steps
 3      β ← β/2 ;  g ← GT_2(g) mod (x^β − µ)
 5  β ← β/3    ;  g_3   ← GT_3(g)     mod (x^β − µ)
 6  β ← β/5    ;  g_5   ← GT_5(g_3)   mod (x^β − µ)
 7  β ← β/17   ;  g_17  ← GT_17(g_5)  mod (x^β − µ)
 8  β ← β/257  ;  g_257 ← GT_257(g_17) mod (x^β − µ)
 9  if g_257 has no roots in F_{p64}: return ⊥
10  µ ← a common root of g_257 and (x^65537 − µ)
11  µ ← a common root of g_17  and (x^257   − µ)
12  µ ← a common root of g_5   and (x^17    − µ)
13  µ ← a common root of g_3   and (x^5     − µ)
14  µ ← a common root of g     and (x^3     − µ)
15  β ← 2^32 ;  h ← f mod (x^β − µ)
16  return a common root of h and (x^(2^32) − µ)
```

Three details read in [PC] §4.1:

- The residue `µ` tracked through the modulus `x^β − µ` rather than `x^β − 1` is the generalisation
  that lets the descent restart: by line 9 the algorithm holds `λ^{(p64−1)/65537} = λ^{2^32·65535}`,
  and lines 11–14 successively recover `λ^{2^32·255}`, `λ^{2^32·15}`, `λ^{2^32·3}`, `λ^{2^32}`.
- Line 16 recovers `λ` itself from `λ^{2^32}` by "a process similar to that in lines 5 to 14" —
  i.e. the 32 square roots are themselves done by the same gcd descent, not by a square-root
  formula. **(reconstructed detail:** [PC] says "similar to" and does not expand the 32 steps.)
- "The computation is dominated by the first `log2(p64) − log2(d) + 1` order-2 Graeffe transforms",
  and "there is no need to store all intermediate polynomials. We do not even store `f`, but use
  interpolation to recover it each time it is needed."

### 3.5 Algorithm C — the single-root variant that was actually implemented

> ## Correction to this transcription: **lines 14–18 are unusable as written outside an attack.**
>
> The transcription below is faithful to [P937] Algorithm 2. It is also, at lines 14–18, **not an
> implementable root finder**, and this document did not notice when it wrote them down. Line 15's
> loop is `r` candidate tests with `r = 2^k = 2^24` over KoalaBear, and line 17's test is
> `P(α) = 0` — a polynomial evaluation at degree `d`. That is `2^24 × 1 594 323 ≈ 2.6 × 10^13`
> field operations at `δ = 3^13`, **four orders of magnitude more than the Graeffe iteration lines 5
> and 6 are there to make cheap.** The algorithm's own stated cost, `O(M(d) log r + s log s + r)`
> below, silently charges the scan `O(r)` rather than `O(r·d)`.
>
> **Why the paper's version is nevertheless cheap, and the sentence that explains it.** [P937] §5.2,
> quoted in full below: "the last loop is then performed by evaluating the permutation `P2` over an
> input state evaluated at `α`, thus costing `O(r)` operations overall". **The candidate test is one
> permutation call, not one polynomial evaluation.** Lines 14–18 are correct, and `O(r)`, *inside the
> attack they were written for*, where `P` is never evaluated at all; they are `O(r·d)` for anyone
> who has a polynomial and wants its root. This document transcribed the lines without transcribing
> the condition that makes them affordable, which is exactly the failure mode §3.8 exists to catch.
>
> **The replacement.** [PC] Algorithm 2 line 8's gcd descent (§3.3 line 8, §3.9), which needs no
> scan at all: `k = 24` folds, each linear in the degree it folds, **measured at 58.8 ms of a
> 3.11 s call** (§4.4.1). `src/poly/univariate/graeffe.rs` implements Algorithm C's lines 1–8 and
> [PC]'s line 8 in place of lines 14–18. §3.9 also costs out the two batched alternatives that keep
> the scan.

[P937] Algorithm 2, which is what [P937]'s Poseidon2-64 attack ran. Written for `p − 1 = r·s` with
`r = 2^k`:

```
ALGORITHM C  (single root finding)                           [P937] Algorithm 2
input   P ∈ F_p[x] of degree d; r = 2^k and s with p = r·s + 1;
        ω_r, ω_s primitive r-th and s-th roots of unity in F_p
output  α ∈ F_p with P(α) = 0, if one exists

 1  if d = 0: return ∅
 3  if P(0) = 0: return 0
 5  G ← P ;  for i ← 0 .. k−1:  G ← G_2(G)                    # O(M(d) log r)
 6  P̃ ← G mod (x^s − 1)                                      # coefficient folding, max(d−s,0) adds
 7  V ← NTT_s(P̃) using ω_s                                   # O(s log s)
 8  find i with V[i] = 0 ;  if none: return ∅
10  β ← ω_s^i                                                 # β = α^r
14  for i ← 0 .. k−1:  β ← sqrt(β)                            # k square roots in F_p
15  for i ← 0 .. r−1:                                         # O(r)
16      α ← ω_r^i · β
17      if P(α) = 0: return α
19  return ∅
```

Why each step is the way it is, read in [P937] §5.2:

- Line 6's fold is `O(max(d−s,0))` additions, not a division: "this step can be computed in
  `max(d − s, 0)` operations by folding the coefficients of `G(x)` according to the relation
  `x^s = 1 (mod x^s − 1)`."
- Line 7 is the subgroup search: `NTT_s` evaluates `P̃` at every power of `ω_s`, so "a zero entry at
  index `i` indicates that `ω_s^i` is a root" — [P937] §4.2. **The whole point of iterating the
  transform is to push the root into a subgroup small enough to enumerate.** That is the answer to
  the issue's question of how iterating the transform separates roots over a finite field: it does
  not separate them by magnitude, as the real-number original does — it drives every `F_p`-root into
  the order-`s` subgroup, where one NTT finds it.
- Lines 14–18 replace Algorithm A's gcd descent with `k` square roots followed by an `r`-way scan,
  because "the values `ω_r^i · β` represent all roots of the polynomial `x^r − α^r`". [P937] notes
  the scan is nominally `O(dr)` but in an attack "the last loop is then performed by evaluating the
  permutation `P2` over an input state evaluated at `α`, thus costing `O(r)` operations overall" —
  the candidate test is a permutation call, not a polynomial evaluation. **That is the step that
  makes the attack's verification stage free, and it is why §9's component list has the permutation
  evaluator as a load-bearing piece rather than an afterthought.**
- Total cost, [P937] §5.2: `O(M(d) log r + s log s + r)`. **The `r` term is the scan, charged one
  operation per candidate — see the correction at the head of this section for when that holds.**
- [P937] §5.2 states the standing assumption plainly: "for the sake of exposition we will assume
  that it has at most one root and that this is non-zero."

### 3.6 Progressive degree reduction — the memory lever

[P937] §5.3, *Large Input Polynomials*. Since `α^{2^i}` lies in the subgroup of order `(p−1)/2^i`,
it is a root of `x^{(p−1)/2^i} − 1`, hence of

```
G̃_{2^i}(x) = G_{2^i}(x) mod (x^{(p−1)/2^i} − 1),    deg G̃_{2^i} = min( deg G_{2^i}, (p−1)/2^i − 1 )
```

so reduction can begin at iteration `i = ceil(log2((p−1)/d))` and the working degree then **halves
every step** down to `s`. This is the single most important engineering point for Zeebra: it means
the sum of transform sizes over the whole Graeffe iteration is a small constant times the largest
one, not `k` times it.

### 3.7 The all-roots variant, for completeness

Not needed for CICO (one root suffices) but recorded because it is what the literature the papers
build on actually does. [P937] §4.3–§4.4 reviews the **tangent Graeffe** method of Grenet–van der
Hoeven–Lecerf [8], implemented in [9],[10] where "for the prime `p = 5·2^55 + 1`, it was used to
compute the roots of polynomials of degree up to `10^9`":

- Work over `F_p[ε]/(ε²)`. With `P̃(x) = P(x+ε) = P(x) + P'(x)ε`, one gets
  `G_r(P̃)(x) = ∏(x − (α_i − ε)^r)` with `(α_i − ε)^r = α_i^r − r·α_i^{r−1}ε`.
- Write `G_r(P̃) = A + Bε` with `A = G_r(P)`. For a **simple** root `α_i^r` of `A`,
  `r·α_i^{r−1} = B(α_i^r)/A'(α_i^r)`, so `α_i = r·α_i^r · A'(α_i^r) / (r · B(α_i^r))` —
  [P937] §4.3, with the derivation read.
- [P937] Algorithm 1 (from [8]) takes `r` the largest power of two with `r ≤ (p−1)/4d`, sets
  `s = (p−1)/r` so `s = O(d)`, randomizes by `P(x+τ)`, evaluates `A, A', B` on the order-`s`
  subgroup, divides out the roots found and **recurses on the quotient** to catch the ones missed.

**This is the answer to "how are multiplicities resolved".** The order-2 descent of Algorithms A–C
does not resolve them, because it does not need to; the tangent method resolves them by requiring
simplicity and recovering the shortfall through the shift `τ` and the recursion.

### 3.8 What is reconstructed, listed

| step | status | verdict after implementing it |
|---|---|---|
| `GT_2` by three same-size NTTs, with sign `(−1)^d` | read — [P937] §5.3 | **right, and the sign is load-bearing.** Without it a monic input of odd degree transforms to leading coefficient `−1` and Lemma 2 composes only up to a unit. A 16-point domain is asserted sufficient at degree 15 |
| Algorithm A, all lines | read — [PC] Algorithm 2 | **right**; line 8 is what this implementation's descent is |
| Algorithm B, all lines | read — [PC] Algorithm 3 | not implemented — §6.5 is why it would be needed and §10 row 11 tracks it |
| Algorithm C, all lines | read — [P937] Algorithm 2 | **lines 14–18 do not survive as a standalone root finder** — `2.6 × 10^13` operations at `r = 2^24`, and the paper's version is `O(r)` only because its candidate test is a permutation call. The correction block at the head of §3.5 states it; §3.9 states the replacement |
| the gcd un-squaring resolves the root ambiguity | read — [PC] §3.2 commentary on line 8 | **right, and stronger than stated** — §3.9.1 proves the reduction leaves no false candidate, which neither paper claims |
| progressive reduction thresholds | read — [P937] §5.3 | **right, and the constant is not small, and it moves the wrong way** — §6.4 measures 2.00x at `3^13` and only 1.05x at `3^6`. It bounds transform sizes; it does not bound the retained polynomials, which post-#161 is where the entire peak lives |
| tangent Graeffe root recovery formula | read — [P937] §4.3 | not implemented; one root suffices for CICO and for this PR |
| the 32 square roots of Algorithm B line 16, expanded | **reconstructed** — [PC] says "similar to lines 5 to 14" | **the reconstruction was unnecessary.** The descent of §3.9 needs no square root except in one degenerate branch, where `fields::sqrt` (#175) answers it in a single call. The structure removes the step rather than expanding it |
| skip count for Zeebra's hybrid `permutation_plus_linear` | **reconstructed** — §2.3 | **still reconstructed, still untested.** Nothing in this PR touches the permutation; §10 row 8 is where it gets checked |
| the Bluestein sizing for a non-dividing `s` | **partially read** — [P937] §5.3 names Bluestein and `q = 15`; the padding rule "sizes exceeding `2s`" is stated, the full schedule is not | **not needed over KoalaBear, and §9.1 component 10's alternative is the right one.** `s = 127` is enumerated directly at `O(s·d)` — 0.10 ms of a 3.11 s call at `3^13`, 0.003%. No Bluestein, no `O(s^2)`, no transform at all. Over a field whose `s` is large it is the whole cost instead — §6.5 |

### 3.9 Where the implementation departs from Algorithm C, and why

Two departures, both forced by implementing the thing rather than reading it. Recorded here because
§3.8 asks for the reconstructed steps to be validated hardest and these are the two that moved.

**Algorithm C lines 14–18 are not usable in a standalone root finder.** Lines 14–18 take `k` square
roots of `β = α^r` and then scan the `r` candidates `ω_r^i · β^(1/r)`, testing `P(α) = 0`. Over
KoalaBear `r = 2^24`, so that is 16.8 M evaluations of a degree-`3^13` polynomial — `2.6 × 10^13`
field operations, which is four orders of magnitude *more* than the Graeffe iteration it is meant to
finish. [P937] §5.2 says as much about its own algorithm without flagging it as a restriction: the
scan "is then performed by evaluating the permutation `P2` over an input state evaluated at `α`,
thus costing `O(r)` operations overall". **The scan is `O(r)` only because the attack's candidate
test is one permutation call, not one polynomial evaluation.** Outside that setting it is `O(r·d)`.

So this implementation uses **[PC] Algorithm 2 line 8's descent** instead: `µ_{i−1}` is the common
root of `G_{2^(i−1)}` and `x^2 − µ_i`, for `i = k` down to 1. That is `k = 24` folds, each linear in
the degree it folds, and §4.4 measures the whole descent at **58.8 ms** against the iteration's
3.04 s — 1.89% post-#161, and 0.45% of the 13.85 s pre-#161 call. It costs memory rather than time: the descent needs every `G_{2^i}`, which is
§6.4's 384 MB. Two batched alternatives were considered and are cheaper in memory but not in time:
`P(γx) mod (x^r − 1)` followed by one `NTT_r` turns the scan into a single transform of size `2^24`
(3.64 s by §6.1 pre-#161, and ~0.86 s post-#161 at §4.4.3's measured rate, at 134 MB), and `γ = β^(r^{-1} mod s)` gives the `r`-th root in one exponentiation
without any square root at all, since `gcd(r, s) = 1` when `s` is the odd part. **Both are correct; both are
slower than 58.8 ms**, even post-#161 — the batched scan's single `2^24` transform is still an order
of magnitude above the descent. Recorded because the batched scan trades 195 MB and 58.8 ms for
134 MB and ~0.9 s, which is the right answer if the retained polynomials ever become the binding
constraint (§6.4).

#### 3.9.1 An original result: the reduction introduces no surviving false candidate

**Stated in neither [PC] nor [P937], and not attributed to them. This is a contribution of this
repository, and it is offered as a proof sketch rather than a published theorem.**

The un-squaring really is decided by the polynomial, and its degenerate case is common.
`G_{2^(i−1)}` reduced modulo `x^2 − µ_i` is `a x + b` in one pass over the coefficients, and `−b/a`
is the one of `µ_i`'s two square roots that `G_{2^(i−1)}` vanishes at. [PC]'s "there is no ambiguity
to resolve by guessing" holds exactly. But `a = b = 0` — `x^2 − µ_i` dividing `G_{2^(i−1)}` — is not
exotic: it is what `f = x^2 − a^2` produces at the very first level, since `GT_2(f) = (x − a^2)^2`
and both `±a` are roots of `f`. There either square root descends to a genuine root, which needs an
argument rather than an assertion:

> **Claim (this repository's, not either paper's).** For every `i ≤ k`, the roots of `G̃_{2^i}` that
> lie in the subgroup of order `β_i = (q−1)/2^i` are exactly `{α^(2^i) : α ∈ F_p^*, f(α) = 0}` —
> **no root introduced by the reduction modulo `x^(β_i) − 1` survives in the subgroup.**
>
> *Base.* `β_0 = q − 1`, and `ρ^(q−1) = 1` is membership of `F_p^*`, where `G̃_0` agrees with `f`.
>
> *Step.* `G_2(h)(ζ^2) = (−1)^deg h · h(ζ)h(−ζ)`, so `G_2(G̃_{2^i})(ρ) = 0` means `ζ` or `−ζ` is a
> root of `G̃_{2^i}`, for `ζ^2 = ρ`. If `ρ^(β_{i+1}) = 1` then `ζ^(β_i) = 1`, so `ζ` — and `−ζ`,
> since `β_i` is even for `i < k` — lies in `F_p^*` and in the order-`β_i` subgroup. The inductive
> hypothesis then makes it `α^(2^i)` for a base-field root `α` of `f`, and `ρ = α^(2^(i+1))`.
> Reducing modulo `x^(β_{i+1}) − 1` changes nothing on the order-`β_{i+1}` subgroup, where the two
> agree. ∎

**Three consequences, and they are what the claim is for.**

1. The subgroup search produces **no false candidates at all**, so Algorithm C line 8's "find `i`
   with `V[i] = 0`" may take the *first* zero rather than looping over all `s` of them. Neither
   paper says why that is safe; [P937] §5.2 instead assumes it away — "for the sake of exposition we
   will assume that it has at most one root and that this is non-zero."
2. The descent has **at least one valid child at every level and no invalid one**, which is what
   makes it deterministic: no backtracking, no bounded search, and the `a = b = 0` branch may take
   either square root freely.
3. §4.4's `cands` column is therefore the **exact count of distinct base-field roots of the input**,
   not an upper bound on it. Measured at 4–6 against four planted roots plus the random cofactor's
   own, which is the arithmetic check that the claim is not vacuous.

**Caveat, stated plainly.** The step uses `β_i` even for `i < k`, which is where `(−ζ)^(β_i) = 1`
needs `β_i` even; that holds because `β_i = 2^(k−i) · m` with `k − i ≥ 1`. It is a proof sketch
written for this implementation, checked against every test in `graeffe.rs` and against `roots` at
every degree the quadratic finder reaches, and **not peer-reviewed**. If it is wrong, the failure
mode is a returned `None` where a root exists — never a wrong root, since `graeffe_root` verifies
`f(α) = 0` before returning.

#### 3.9.2 The dual failure mode, found and fixed: a reduction that lands on zero

§3.9.1 is a *soundness* claim — the reduction introduces no false candidate. Completeness is the
other half, and it has a degenerate case that neither paper mentions and that the first
implementation here got wrong.

Reduction modulo `x^(β_i) − 1` loses no root **in the subgroup**, but it can lose the polynomial.
If `x^(β_i) − 1` divides `G_{2^i}` then the fold lands on the zero polynomial, and zero is the one
value that cannot carry the information the reduction exists to produce: it means *every* element
of the order-`β_i` subgroup is a root, and it is stored identically to a polynomial with none. Worse,
`DensePolynomial::degree` reports `0` for it (the zero polynomial's degree is undefined, and the type
picks zero), so the `degree() == 0` short-circuit in `subgroup_roots` — correct for a nonzero
constant, which genuinely has no roots — read it as "no candidates" and `graeffe_root` returned
`None`.

The smallest witness is as small as it gets. Over KoalaBear `q − 1 = 2^24 · 127`, so take

```text
f(x) = x^127 − 1
```

which splits into 127 distinct base-field roots, is fixed by the degree-normalized order-two
transform (`GT_2(f)(x^2) = −f(x)f(−x) = x^254 − 1`), and meets `β_k = 127` exactly at the last
step — where the fold sends it to zero. `graeffe_root` reported no root for a polynomial with 127
of them, `x = 1` among them.

**The fix is at the fold, not at the search.** `fold_if_needed` refuses a fold onto zero and returns
`None`, which it already uses for "keep what you have", so the unreduced transform is retained and
the ordinary subgroup routes find the roots. Doing it there rather than in `subgroup_roots` makes it
unconditional: the alternative — reporting all `β_i` subgroup elements as candidates — needs a
generator of that subgroup, and `try_root_of_unity` can fail (`OrderTooWide`) on fields whose order
exceeds a `u128`. The cost is that the degenerate step carries its full degree into the subgroup
search instead of dropping to `β_i`; that is strictly more work than the fold would have been, and
it is confined to inputs divisible by `x^(β_i) − 1`.

Regression tests in `graeffe.rs`: `test_a_subgroup_vanishing_polynomial_still_yields_a_root`
(the bare `x^127 − 1`, through the full descent), `test_a_vanishing_factor_in_a_larger_polynomial_still_descends`
(the same factor inside a degree-131 product, so the retained polynomial sits above the subgroup),
and `test_a_fold_onto_the_zero_polynomial_is_refused` (the fold in isolation, including that a
nonzero remainder is still folded).


## 4. The reported measurements, with hardware

### 4.1 Goldilocks, Graeffe-based — [PC] Table 3

Hardware, [PC] §4.2: "a dual-socket Intel Xeon Platinum 8474C server equipped with several Nvidia
RTX 4090 graphics cards. Each card is connected to the system's 2TB RAM via a PCIe 4.0 interface,
providing a unidirectional bandwidth of roughly 200 GiB/s in total under real-world conditions."

| instance | field | κ | R_F | R_P | degree | time | memory | time [JAZ-method] | memory [JAZ-method] |
|---|---|---:|---:|---:|---|---:|---:|---:|---:|
| `P2_6_7` | Goldilocks | 24 | 6 | 7 | `7^12` | `2^8.56` s | 0.32 TB | `2^21.81` s | 6.1 TB |
| `P2_6_8` | Goldilocks | 28 | 6 | 8 | `7^13` | `2^11.38` s | 1.8 TB | `2^24.83` s | 41 TB |
| `P2_6_10` | Goldilocks | 32 | 6 | 10 | `7^15` | `2^18.35` s † | 90 TB | `2^30.88` s | 1.9 PB |

† "Data swapped to disk" — [PC] Table 3 footnote.

**The `2^13` and `2^4.5` claims, checked against this table.** `2^24.83 − 2^11.38 = 2^13.45` and
`2^21.81 − 2^8.56 = 2^13.25`; `41/1.8 = 22.8 ≈ 2^4.51` and `6.1/0.32 = 19.1 ≈ 2^4.25`. **Both
headline claims reproduce from the table, and both are against an *estimate* rather than a
measurement of the comparand.** [PC] §4.2 is explicit: "For the GCD-based method, direct computation
is infeasible even for the degree `7^12` case. Therefore, we use the fitting curve from Figure 12 of
[7] to estimate the wall time and memory usage… This estimate optimistically assumes that the speed
is not further reduced by accessing petabytes of memory." The right reading is therefore
"`2^13` against an extrapolation of the prior method, which the authors call optimistic", not
"`2^13` measured against a run". Recorded as such.

### 4.2 BLS12-381, GCD-based — [P937] Table 1 and [PC] Table 2

Hardware, [P937] §5.3: "AMD EPYC 9374F 32-core processor, 1.1 TB of RAM, and 8 NVIDIA L4 GPUs, each
with 23 GiB of memory. The AWS cloud instance closest to this hardware configuration is the
g6.48xlarge, featuring 192 vCPUs, 768 GiB of memory, and 8 NVIDIA L4 GPUs, priced at $13.35/h
on-demand."

| instance | κ | R_F | R_P | GPU | interpolation | root finding | other steps ([PC] Table 2) |
|---|---:|---:|---:|---|---:|---:|---:|
| `P_6_8` | 24 | 6 | 8 | no | 1 m 20 s | 3 d 7 h 17 m | `2^18.12` s |
| `P_6_8_GPU` | 24 | 6 | 8 | yes | 45 s | 9 h 17 m | `2^15.03` s |
| `P_6_9` | 28 | 6 | 9 | yes | 6 m 10 s | 2 d 18 h 10 m | `2^17.86` s |

**Interpolation is 0.03%–0.2% of root finding on these rows.** That is the strongest available
evidence for #68's premise that root finding and not elimination is the binding stage, and it is
measured rather than modelled. [P937] §5.3 adds polynomial memory: "approximately 7.3 GiB and
36.4 GiB" for the two instances, and notes the BLS rows used **the classical GCD method, not
Graeffe** — "without employing the potential optimizations afforded by the Graeffe transform…
Investigating the potential improvements achievable through the use of Graeffe-based methods is left
as future work." The GCD step itself: "a few hours of computation on a single CPU core for the 6_8
instance and around 3 days for 6_9", with exact timings "no longer available" ([PC] §4.2).

Dollar cost, [P937] §5.3: `P_6_8` $185 against a $4 000 prize; `P_6_9` $1 101 against $6 000;
`P2_6_8` $133 against $4 000.

### 4.3 Where the time went, per the authors

- [PC] §4.2: "in all the challenges we solved, memory access was the main bottleneck, and GPUs
  played only a minor role in our speedup. For example, in the large degree cases, our toy CPU
  implementation with almost no optimization for field operations (no SIMD, etc.), was only about
  four times slower than the GPU version. During the Radix-2 NTT or invNTT, the typical GPU
  utilization was less than 20%."
- [PC] §4.2, Table 4, measured Goldilocks throughput on their GPU: `float32` FMA 41.3 TOPS,
  `F_p64` addition 3.41, subtraction 2.95, **multiplication 0.76**.
- [PC] §4.2: "the Radix-2 part of our NTT implementation executes roughly 25 field multiplications
  and 25 field additions (or subtractions) each time a field element (8 bytes) is transferred to the
  device. Assuming a ~16GB/s host-to-device bandwidth, this requires only a multiplication
  throughput of 50 GOPS, which is less than 10% of the architecture's capability."
- [PC] §4.2 on the alternative to large radix-2: "we need to compute NTT and invNTT with group sizes
  of at least `7^12`, `7^13`, and `7^15`, all of which are larger than the even part of
  `p64 − 1 = 2^32·3·5·17·257·65537`… Possible approaches include the Schönhage-Strassen algorithm and
  the Elliptic Curve FFT, but we choose to use mixed-radix NTT for simplicity."
- [PC] §4.2 on external memory: "large system RAM is not necessary for running our code. When
  available memory is limited, users can configure the maximum RAM usage, and our implementation
  will automatically swap polynomial coefficients and NTT data to and from disk as needed… overall
  speed will be limited by disk I/O, but still acceptable — in our case it is about 2 ∼ 3 times
  slower than running entirely in RAM." **This is the figure §8 hands to E3.**
- [PC] §4.2's security estimate: `d_c` "well below `7^15`"; "it is possible to execute about `2^59`
  SHA-256 permutations in the same running time as a degree `7^15` root finding over `F_{p255}`";
  128-bit parameters give `R_F = 8, R_P = 56` hence degree `5^63`, and
  `(5^63 / 7^15)^{4/3} × 2^59 ≈ 2^198` SHA-256 permutations. ([PC] §1 quotes the same estimate as
  "about `2^200`"; the arithmetic in §4.2 gives `2^198`. **Discrepancy within the paper**, recorded.)

### 4.4 Measured here: Graeffe root finding at `3^13` over KoalaBear

**Measured, not estimated.** `examples/graeffe_root.rs`, `src/poly/univariate/graeffe.rs`, landing
§10 rows 3, 4 and 6. One core of the 64-core/300 GB workstation, `taskset --cpu-list 8`, under
`tools/benchlock.sh`, release profile with the repository's default `Cargo.toml` settings (fat LTO,
`codegen-units = 1`), `RUSTC_WRAPPER=""` and a private `CARGO_TARGET_DIR`.

**Two revisions are reported, both measured on the same machine with the same binary source.**
The first run predates **#161**, the iterative in-place NTT, and the second follows it. Both are
kept: the pre-#161 figures are a real measurement of a real revision, and the pair is the only
measurement anywhere in this repository of **what #161 was worth to a downstream consumer** rather
than to the transform in isolation.

Reproduce with

```sh
RUSTC_WRAPPER="" CARGO_TARGET_DIR=/path/to/target cargo build --release --example graeffe_root
tools/benchlock.sh agentG taskset --cpu-list 8 \
  /path/to/target/release/examples/graeffe_root koalabear budget=60.0
```

The input at each degree is a random cofactor times four planted linear factors — the shape an
interpolated output coordinate leaves behind — and every returned root is asserted to be one.

#### 4.4.1 Current, post-#161

KoalaBear in a `u64`:

| degree | `log2 d` | steps | transforms | largest `n` | `sum n / max n` | forward | subgroup | descent | **total** |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `3^6` = 729 | 9.51 | 24 | 72 | `2^10` | 68.25 | 0.0015 s | 0.13 ms | 0.05 ms | **0.0017 s** |
| `3^7` = 2 187 | 11.09 | 24 | 72 | `2^12` | 62.81 | 0.0059 s | 0.09 ms | 0.15 ms | **0.0062 s** |
| `3^8` = 6 561 | 12.68 | 24 | 72 | `2^13` | 59.91 | 0.0124 s | 0.10 ms | 0.41 ms | **0.0130 s** |
| `3^9` = 19 683 | 14.26 | 24 | 72 | `2^15` | 53.98 | 0.0537 s | 0.09 ms | 1.12 ms | **0.0551 s** |
| `3^10` = 59 049 | 15.85 | 24 | 72 | `2^16` | 50.99 | 0.1081 s | 0.10 ms | 3.12 ms | **0.1118 s** |
| `3^11` = 177 147 | 17.43 | 24 | 72 | `2^18` | 45.00 | 0.3828 s | 0.09 ms | 7.49 ms | **0.3918 s** |
| `3^12` = 531 441 | 19.02 | 24 | 72 | `2^20` | 39.00 | 1.5019 s | 0.09 ms | 20.70 ms | **1.5272 s** |
| **`3^13`** = 1 594 323 | **20.60** | 24 | 72 | **`2^21`** | **36.00** | 3.0412 s | 0.10 ms | 58.76 ms | **3.1122 s** |

**`3^13` completes in 3.11 s.** The `u32`-backed KoalaBear — the type the registered challenge
actually uses — is **2.2662 s**.

#### 4.4.2 Superseded, pre-#161

The same binary source against the recursive kernel, same core, same protocol. **Retained, marked
superseded.**

| degree | forward | subgroup | descent | **total** | peak heap |
|---|---:|---:|---:|---:|---:|
| `3^11` = 177 147 | 1.9061 s | 0.09 ms | 7.67 ms | **1.9156 s** | 49.9 MB |
| `3^12` = 531 441 | 7.0242 s | 0.09 ms | 20.67 ms | **7.0452 s** | 168.6 MB |
| **`3^13`** = 1 594 323 | 13.7656 s | 0.10 ms | 62.68 ms | **13.8466 s** | 383.9 MB |

`u32` KoalaBear at `3^13`, pre-#161: 12.3349 s and 192.0 MB.

#### 4.4.3 What #161 was worth, here

| at `3^13`, KoalaBear `u64` | pre-#161 | post-#161 | factor |
|---|---:|---:|---:|
| **total wall time** | 13.8466 s | **3.1122 s** | **4.45x** |
| forward iteration | 13.7656 s | 3.0412 s | **4.53x** |
| forward share of the call | 99.4% | **97.7%** | — |
| subgroup search | 0.10 ms | 0.10 ms | 1.0x |
| un-squaring descent | 62.68 ms | 58.76 ms | 1.07x |
| implied `ns/element` at `2^21` | 182.4 | **40.3** | **4.53x** |
| **peak live heap** | 383.9 MB | **194.7 MB** | **1.97x** |
| process peak RSS (`VmHWM`) | 409.5 MB | 225.8 MB | 1.81x |
| `u32` total wall time | 12.3349 s | **2.2662 s** | **5.44x** |
| `u32` peak live heap | 192.0 MB | **97.3 MB** | 1.97x |

**4.53x on the stage that was 99.4% of the call**, which is within the 4.24x `fast-univariate.md`
§3.3 measures for a bare `evaluate` at `2^21`–`2^22` — so #161's gain passes through to this
consumer essentially undiluted, and the small excess is the pointwise combine getting faster too.

Four things the stage split says that no estimate here anticipated:

- **The forward iteration was and is the whole call** — 99.4% pre-#161, 97.7% post. The subgroup
  search is 0.10 ms either side and the descent 59–63 ms. §9.2's component-by-component table does
  not separate these three and could not have said which dominated. The practical consequence is
  that **this stage inherits whatever the NTT kernel does**, which #161 has just demonstrated.
- **The implied per-transform rate tracks a bare `evaluate` to within 6%.** Pre-#161: 0.382 s per
  `2^21`-equivalent against §6.1's 0.361 s, 182.4 ns/element against 172.4. Post-#161: 0.0845 s and
  **40.3 ns/element**. The 5–6% is the parity split, the pointwise `e^2 - w o^2` combine and the
  `(-1)^d` scale; i.e. **the order-2 step costs what three transforms cost and almost nothing
  more**, which is §3.2's claim as an arithmetic fact rather than an operation count, and it holds
  across a kernel replacement.
- **The transform count is 72 at every degree**, because it is `3 * two_adicity` and does not depend
  on the degree. What depends on the degree is the *sizes* — the `sum n / max n` column, 36.00 at
  `3^13` against 72 with no reduction. See §6.4.
- **The descent did not get faster and is now a visible share.** 62.68 ms to 58.76 ms while the
  iteration fell 4.53x, so it went from 0.45% to 1.89% of the call. It is Horner-style folds over
  the retained polynomials, not transforms, so #161 does not touch it. At another 4x on the forward
  stage it would be ~7%.

#### 4.4.4 Memory, measured against estimated

Both at `3^13`, post-#161, with the pre-#161 column beside it:

| | post-#161, `u64` | post-#161, `u32` | pre-#161, `u64` |
|---|---:|---:|---:|
| peak live heap, counting allocator | **194.7 MB** | **97.3 MB** | 383.9 MB |
| estimated: retained `G_(2^i)` + `4 n B` at the largest transform | 211.3 MB | 105.6 MB | 274.4 MB (at `7 n B`) |
| **measured / estimated** | **0.92x** | 0.92x | **1.40x** |
| retained coefficients | 18 023 881 | 18 023 881 | 19 618 205 |
| process peak RSS (`VmHWM`) | 225.8 MB | 114.4 MB | 409.5 MB |

**The sign of the estimate's error flipped, and that is the interesting part.** Pre-#161 the
estimate was **40% low** and the gap was the kernel's temporaries plus one full-degree clone of
every `G_(2^i)` as it left the iteration. #161 took `evaluate` to `1 n B` and `interpolate` to
`2 n B` — their floors, `fast-univariate.md` §3.3 — which removed the kernel half; the clones were
then the **larger** of the two remaining terms and were removed here (`graeffe_2_over_domain` scopes
both halves' value vectors and reuses one as the combine's output; the forward loop moves each
`G_(2^i)` into the retained vector instead of cloning it, and the `beta_0` fold borrows the caller's
`f` rather than copying it when it is a no-op — the 1 594 324-coefficient difference in the row
above is exactly that). What is left is **8% below** a straightforward `stored + 4 n B` estimate,
because the largest transform's `4 n B` and the peak of the retained set do not occur at the same
instant.

So: **the estimate is now a slight over-prediction rather than a 40% under-prediction**, the gap in
both directions is accounted for rather than noted, and the thing that dominates at `3^13` is the
retained `G_(2^i)` — 18.0 M coefficients, 144 MB at 8 bytes, of which 11 copies are at the full
degree because §6.4's schedule keeps 11 steps full-size.

**Not within two orders of magnitude of any limit.** 195 MB against this box's 300 GB, consistent
with `fast-univariate.md` §5's finding that memory is not the constraint anywhere in this layer.

### 4.5 The comparand, measured as far as it goes

`src/poly/univariate/roots.rs` on the same inputs, from the same binary and the same run. `roots`
uses no transform, so #161 does not apply to it; the small change between the two runs is
run-to-run variation and `41d48f3`'s iterative `pow_limbs`. **Post-#161 run:**

| degree | seconds | exponent | peak bytes | pre-#161 seconds |
|---:|---:|---:|---:|---:|
| 256 | 0.0071 | — | 24 536 | 0.0078 |
| 1 024 | 0.1030 | 1.95 | 98 264 | 0.1142 |
| 4 096 | 1.5542 | 1.97 | 393 176 | 1.6652 |
| 16 384 | 23.1219 | 1.96 | 1 572 824 | 24.6018 |
| **32 768** | **86.7786** | 1.91 | 3 145 688 | 93.2490 |

**`roots` reaches degree 32 768 and no further inside a 60 s per-measurement budget**, in both runs.
The exponent column confirms the quadratic growth rather than assuming it (1.91–1.97 over seven
doublings), and extrapolating from the 32 768 row to `3^13` gives

```
86.7786 s * (1594323 / 32768)^2  =  205 431 s  =  57.1 hours
```

**That 57.1 hours is an extrapolation of `roots`, not a measurement of it.** It is consistent with
`fast-univariate.md` §5's independently-derived ~31 hours at `d = 2^20`: `3^13` is 1.52x that
degree, so 2.3x the time. The pre-#161 run's extrapolation was 61.3 hours; **both are
extrapolations and neither is a measurement at `3^13`.**

So the comparison §7.2 sets up, with each half labelled:

| | at `3^13` over KoalaBear | status |
|---|---:|---|
| `graeffe_root`, post-#161 | **3.11 s** | **measured** |
| `graeffe_root`, pre-#161 | 13.85 s | **measured**, superseded |
| `roots` | 57.1 hours | **extrapolated** from a measured curve that stops at degree 32 768 |
| **ratio, post-#161** | **≈66 000x**, `2^16.0` | one measured end, one extrapolated end |
| ratio, pre-#161 | ≈15 900x, `2^13.96` | superseded |

Which is the same shape as [PC] §4.2's own headline: §4.1 records that their `2^13` is likewise
against an extrapolation their authors call optimistic, not against a run. **Between four and five
orders of magnitude, with one end of it extrapolated** is the honest statement, and it is the same
statement the papers make about their own figure.

## 5. The memory-access model, its assumptions, and whether it applies here

### 5.1 The theorem

[PC] §5, Theorem 1: "The arithmetic circuit of NTT over a finite field with input size `n = 2^{e_2}`,
regardless of how it is realized in our three-dimensional world, will incur a data movement cost of
at least `Õ(n^{4/3})`."

The proof, read in full:

- **Fact 1** — "The cost of data movement is proportional to the physical distance over which it is
  transferred (and, of course, the amount of data moved)."
- **Definition 3** — "For two positions `x` and `y` in `R^3`, we define the cost of moving a field
  element from position `x` to position `y` as the Euclidean distance `‖x − y‖`."
- **Fact 2** — "Each bit of data must be stored in a physical volume bounded below by a positive
  constant (i.e. information density is finite)." Used as: there exists `C_0` with at most `C_0 R^3`
  field elements in any ball of radius `R`.
- **Lemma 3** — fixing the radix-2 NTT DAG with nodes `v_{i,s}`, `0 ≤ s ≤ e_2`, and edges
  `v_{i,s} → v_{i,s+1}` and `v_{i,s} → v_{i ⊕ 2^{e_2−1−s}, s+1}`, the movement cost is at least
  `Σ_{i < i⊕2^r} ‖p(i) − p(i ⊕ 2^r)‖` for **any** single `r`, via `n/2` pairwise-disjoint subgraphs
  and the triangle inequality.
- **Lemma 4** — `Σ_{i,j} ‖p(i) − p(j)‖` is `Ω(n^{7/3})`, from Fact 2.
- **Lemma 5** — some `r` achieves at least a `1/(n e_2)` share of that sum.
- Theorem 1 follows: `n^{7/3} / (n log n) = n^{4/3}/log n`.

**A reading note on the statement of Lemma 4 and Theorem 1.** Lemma 4 is *stated* as
`Σ ‖p(i) − p(j)‖ = O(n^{7/3})` and Theorem 1 as "at least `Õ(n^{4/3})`", but both proofs establish
**lower** bounds — `≥ (16C_0)^{−1/3} n^{4/3}` per `i` in Lemma 4, summing to `Ω(n^{7/3})`.
`O` should be `Ω` in both. This is a typographical slip, not a gap in the argument; the proof body is
correct as written. Recorded because the issue asked for the model to be stated precisely.

### 5.2 The assumptions, stated explicitly

1. Cost is **total distance travelled by data**, in units of element·metre. It is not time, not
   energy, not DRAM traffic, not cache misses, and not bandwidth.
2. The computation is laid out in **`R^3` with finite information density**. The asymptotic in `n`
   therefore presumes the machine *grows* with the problem: a fixed physical machine has a bounded
   diameter, and the `n^{1/3}` distance factor is a constant for it.
3. The circuit is the **radix-2 NTT DAG specifically**, with that butterfly edge structure. Lemma 3
   is a statement about that graph and does not transfer to other transforms unchanged.
4. The bound is on **one transform of size `n`**, with an unstated constant depending on `C_0`.
5. [PC] §4.2 is deliberate about what this buys and what it does not: "Some literature uses a
   simplified two-level hierarchical memory model (corresponding to most real-world settings) to
   derive lower bounds of memory access cost. But we are aiming for a lower bound that holds for any
   physically realizable architecture." And the extension from the theorem to the attack cost is
   flagged by the authors themselves: "we also (with some boldness) model the root finding cost as
   scaling with the 4/3-power of the polynomial degree".

### 5.3 The practical claim and the theoretical claim rest on different models

This is the key judgement the issue asked for, and it is the paper's own structure that forces it.
§4.3's *practical* bottleneck argument is a **two-level bandwidth argument**: 25 multiplications per
8-byte element transferred over a ~16 GB/s PCIe link, therefore 50 GOPS suffices, therefore the
arithmetic unit idles. That is precisely the "idealized hierarchical memory model" §5.2 declines to
rely on. The `4/3` theorem does not predict the GPU utilisation figure, and the GPU utilisation
figure does not evidence the `4/3` theorem. **Two separate claims, each supported, neither
supporting the other.**

### 5.4 Does the `4/3` model apply to Zeebra's access patterns?

**No, at the sizes Zeebra operates at — and the reason is assumption 2.**

- Zeebra runs on **one fixed machine**: 64 cores, 300 GB RAM, **256 MB of L3**. Its physical
  diameter does not grow with `n`. The `n^{1/3}` factor is therefore a constant over the whole range
  of transform sizes any registered instance needs, and the model predicts `Θ(n)` movement cost with
  a machine-dependent constant — i.e. it degenerates to the pseudo-linear model it is meant to
  replace.
- The regime in which the model bites is the one [PC] actually hit: **90 TB swapped to disk**
  ([PC] Table 3), where the storage hierarchy genuinely extends physically. Zeebra reaches no such
  working set at any size in §2.4's table over KoalaBear: the largest radix-2 transform the field
  admits is `2^24`, whose coefficient array is `2^24 × 8 B = 134 MB` — **smaller than this box's
  L3**.
- Assumption 3 ties the bound to the radix-2 DAG. #161 replaces Zeebra's recursive split with an
  iterative in-place kernel; both are radix-2, so the bound's premise survives #161, but a
  mixed-radix kernel (which §2.4 shows is required for every open challenge) is outside the
  theorem's scope as proved.
- Separately, the model is a **lower bound**, so no measurement on this machine can confirm or refute
  it. It can only be tested for *relevance*, which is what §6 does.

The honest summary: the `4/3` result is a statement about asymptotically large physically-realized
computations, it is correctly proved under its stated facts, [PC] applies it to a 90 TB
disk-swapping run where the premise is plausible, and it has **no bearing on any transform Zeebra
can perform over KoalaBear**.

## 6. The access-bound question for Zeebra, measured

The issue requires this answered by measurement "regardless of the paper's model". It is.

### 6.1 Pre-#161 baseline, measured

Agent C is replacing `src/fft/evaluate.rs`'s recursive split with an iterative in-place kernel on
`perf/161-iterative-ntt`, so the curve below is **explicitly a pre-#161 baseline** and was taken from
an uncommitted throwaway binary rather than a committed benchmark, for exactly that reason. Single
core, `taskset -c 8`, under `tools/benchlock.sh`, KoalaBear in a `u64` (`size_of::<F>() = 8`).

The *arithmetic* comparand was measured in the same run and the same binary, as an independent
`acc = acc + a[i]*b[i]` loop over a 4 KB window resident in L1: **1.560–1.572 ns per
multiply-accumulate, i.e. 636–641 M mul/s**. That loop serialises the additions, so 641 M mul/s is a
*lower bound* on the field-multiplication throughput; for comparison `MILESTONE-SIMD-PARALLELISM.md`
§8.1 reports 1.809 ns for an isolated `mul` over the Mersenne-31 modulus at the same storage width.

A radix-2 transform of size `n` performs `(n/2)·log2 n` butterflies, each one multiply plus one add
and one subtract, so one butterfly is charged one field multiplication below.

| `log2 n` | input array | impl. peak at `7nB` | s / transform | ns / element | **ns / butterfly** | M butterfly/s | achieved / arithmetic rate |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 10 | 8 KB | 57 KB | 0.000105 | 102.9 | **20.59** | 48.6 | 7.6% |
| 12 | 33 KB | 229 KB | 0.000452 | 110.2 | **18.37** | 54.4 | 8.5% |
| 14 | 131 KB | 918 KB | 0.002128 | 129.9 | **18.55** | 53.9 | 8.4% |
| 16 | 524 KB | 3.7 MB | 0.009289 | 141.7 | **17.72** | 56.4 | 8.8% |
| 18 | 2.1 MB | 14.7 MB | 0.040281 | 153.7 | **17.07** | 58.6 | 9.1% |
| 20 | 8.4 MB | 58.7 MB | 0.173903 | 165.8 | **16.59** | 60.3 | 9.4% |
| 21 | 16.8 MB | 117 MB | 0.361491 | 172.4 | **16.42** | 60.9 | 9.5% |
| **22** | **33.6 MB** | **235 MB** | **0.749915** | **178.8** | **16.25** | **61.5** | **9.6%** |
| 23 | 67.1 MB | 470 MB | 1.612120 | 192.2 | **16.71** | 59.8 | 9.3% |
| **24** | **134 MB** | **940 MB** | **3.641236** | **217.0** | **18.09** | **55.3** | **8.7%** |

**The answer, for the stage as it stands: Zeebra's NTT runs at 8.7%–9.6% of its own
field-multiplication rate, and the shortfall is flat in working-set size.** `ns/butterfly` varies by
`±13%` over a 16 384-fold range of `n`, and it is *worst at the smallest size*, where the entire
working set is in L1. A stage that were access-bound would show `ns/butterfly` rising as the working
set crossed L2 and then L3; this one falls and then rises by 11% at the very last point, where the
implementation's `7nB` footprint (940 MB) finally exceeds the 256 MB L3.

So the 90%+ deficit against the arithmetic rate is **not** a cache effect. It is the recursive
formulation: `evaluate` calls `evens_and_odds` (two fresh `Vec`s), `UnivariatePolynomial::new` (a
copy), `domain.split()` (another `Vec`) and allocates a fresh output `Vec` at every one of the
`log2 n` levels — which is also the arithmetic behind `fast-univariate.md` §3.2's measured `7nB`
peak. **That is exactly what #161 removes**, and it is why no curve against this kernel should be
committed.

### 6.2 Why KoalaBear cannot answer the access-bound question on this box at all

`MILESTONE-SIMD-PARALLELISM.md` §8.2 warns that this machine's **256 MB L3** makes a "32 MB, out of
cache" working set a misreading — it is out of L2 and still in L3. The same trap is sharper here and
in a way the issue did not anticipate:

| field | `size_of::<F>()` | two-adic ceiling | coefficient array at the ceiling | past 256 MB L3? |
|---|---:|---:|---:|---|
| **KoalaBear** (`u64`) | 8 B | `2^24` | **134 MB** | **never** |
| KoalaBear (`u32`, `fields::KoalaBear`) | 4 B | `2^24` | 67 MB | never |
| Goldilocks | 8 B | `2^32` | 34 GB | from `2^25` (268 MB) |
| BN254 `Fr` | 32 B | `2^28` | 8.6 GB | from `2^23` (268 MB) |
| BLS12-381 `Fr` | 32 B | `2^32` | 137 GB | from `2^23` |

**Over KoalaBear, the coefficient array of a radix-2 NTT can never leave this machine's L3**, because
the field's two-adicity caps `n` at `2^24` and `2^24 · 8 B < 256 MB`. The only reason row `log2 n =
24` above shows anything is the recursive kernel's `7nB` multiplier, and an iterative in-place kernel
(#161) will remove even that. Any sweep that claims to cross the cache hierarchy over KoalaBear is
measuring the implementation's temporaries, not the transform's working set.

**Consequence for the experiment design: the access-bound question must be asked over Goldilocks and
BN254, not over KoalaBear.** Goldilocks keeps the arithmetic comparable to KoalaBear's (8 bytes,
one-word Montgomery) and reaches `2^25`–`2^28` within reasonable time; BN254 reaches 268 MB at
`2^23`, which `fast-univariate.md` §3.1 already shows is one doubling past the `2^21` it reaches in
one second. KoalaBear remains in the sweep as the *field of the registered challenge*, with its
ceiling stated as a result rather than as a limitation of the sweep.

### 6.3 Specification for the committed `examples/` binary

The issue asks for "an NTT size sweep reporting effective field operations per second against
transform size, with peak bytes, from a committed `examples/` binary". This is the specification,
**not** the code — #84's experimental half is blocked on #124 and the kernel is being rewritten under
#161, so committing the binary now would commit a table that #161 invalidates on merge.

**File** `examples/ntt_access.rs`. **Invocation**
`cargo run --release --example ntt_access [field…] [budget=S] [list]`, following
`examples/univariate_scaling.rs`'s argument convention exactly.

**Fields**, in this order: `KoalaBear` (`PrimeFieldElement64<2_130_706_433>`, the registered
challenge's field, swept to its `2^24` ceiling), `Goldilocks`, `Bn254Fr`. Mersenne-31 is excluded and
the exclusion printed: two-adicity 1, no power-of-two transform above size 2
(`fast-univariate.md` §1.1).

**Columns per row**, all with units in the header:

| column | definition |
|---|---|
| `log2 n`, `n` | transform size |
| `coeff bytes` | `n · size_of::<F>()` — **the working set that matters**, printed separately from peak |
| `peak bytes` | peak live heap bytes from a counting global allocator, as `univariate_scaling.rs` does; **not** process RSS |
| `peak / coeff` | the implementation's multiplier. Pre-#161 this is ≈7; post-#161 it should approach 1–2, and the column is how a reader sees that |
| `s / transform` | median of `reps` repetitions, `reps` chosen for ≥0.3 s total |
| `ns / butterfly` | `t · 1e9 / ((n/2)·log2 n)` — **the headline curve** |
| `eff. Mmul/s` | `(n/2)·log2 n / t`, one butterfly charged one multiplication |
| `arith Mmul/s` | measured in the same binary, same field, from an isolated-multiply loop in L1 |
| `achieved %` | `eff. Mmul/s / arith Mmul/s` — the access-bound verdict, per row |
| `cache level` | which of L1 / L2 / L3 / DRAM the **`coeff bytes`** figure falls in, from constants named in the source with this box's 256 MB L3 written down and cited to `MILESTONE-SIMD-PARALLELISM.md` §8.2 |

**Sweep bounds.** From `2^10` (below that the timing is noise) by doubling, stopping at the field's
two-adicity or when one measurement exceeds `budget` (default 1.0 s), whichever comes first — and
printing *which* of the two stopped it, as `univariate_scaling.rs`'s `Stop` enum does. Cap at `2^26`
unconditionally so a default run cannot starve a concurrent agent: at 217 ns/element that is ~15 s
per field, and the whole binary is under a minute.

**The arithmetic comparand must be in the same binary and the same run.** `benches/field_arithmetic.rs`
has arms for `p31` (the Mersenne-31 modulus in `u64`), `p31_u32`, `p64`, `p68`, `p254_bn254` and
`p255_bls12_381` — **there is no KoalaBear arm and no Goldilocks arm at the Goldilocks modulus**. So
the bench cannot supply the comparand for two of the three fields swept. Two things follow, and both
are recommendations rather than part of this document's scope:

- add `bench_field::<KoalaBear…>` and a Goldilocks arm to `benches/field_arithmetic.rs`, so the
  example's in-run figure has a criterion-measured check against it;
- have the example print both its own figure and the committed bench figure it should match, so a
  divergence is visible rather than silent — `MILESTONE-SIMD-PARALLELISM.md` §8.2's note that
  "that harness was not committed, so the two are not the same program" is the failure this avoids.

**What must not be asserted.** No wall-clock assertion, no pinned absolute `ns/butterfly`. The
correctness assertion is the round trip (`interpolate(evaluate(p)) == p`) at two sizes, which is
cheap and invariant to the kernel.

**Correctness part of #84, also specification only.** The issue asks for a Graeffe step on a
degree-16 polynomial over `PrimeFieldElement64` checked against directly squared roots. The test
belongs in `src/poly/univariate/` next to `roots.rs` once #124 lands, and its oracle is: build
`f = ∏(x − r_i)` from 16 known roots, compute `GT_2(f) = (−1)^d (f_e² − x f_o²)` ([P937] §5.3), and
assert it equals `∏(x − r_i²)` up to a unit. Two further checks that cost nothing and catch the
errors this is actually prone to: `GT_2(GT_2(f)) == GT_4(f)` ([PC] Lemma 2) and
`deg GT_ℓ(f) == deg f` ([PC] Lemma 1).

### 6.4 What progressive reduction is actually worth, measured

§3.6 says the sum of transform sizes over the whole iteration is "a small constant times the largest
one, not `k` times it". **That is true and the constant is not small.** The constant is
`ceil(log2((p − 1) / d)) + 2`, because the degree stays full until `beta_i = (p − 1) / 2^i` falls
below `d` and only halves after that — which is exactly the schedule §7.2 computes by hand, stated
as a formula. Measured, from the `sum n / max n` column of §4.4 (72.00 would be no reduction at all,
since 24 steps of three transforms each):

| degree over KoalaBear | `(p − 1) / d` | full-size steps | `sum n / max n` | saving against no reduction |
|---|---:|---:|---:|---:|
| `3^6` = 729 | 2 922 780 | 22 | 68.25 | 1.05x |
| `3^8` = 6 561 | 324 753 | 19 | 59.91 | 1.20x |
| `3^10` = 59 049 | 36 083 | 16 | 50.99 | 1.41x |
| `3^11` = 177 147 | 12 027 | 14 | 45.00 | 1.60x |
| `3^12` = 531 441 | 4 009 | 12 | 39.00 | 1.85x |
| **`3^13`** = 1 594 323 | **1 337** | **11** | **36.00** | **2.00x** |

**At the target degree the lever is worth a factor of two, and it improves as the degree rises.**
That is the opposite of how §3.6's wording reads — the reduction is *least* valuable at small
degrees, because a small degree means `beta_i` has further to fall before it bites. The asymptotic
limit is 3x (3 transforms, one full-size step, then a halving geometric series summing to one more),
reached as `d` approaches `p − 1`.

**Whether it bounded memory: yes for the transforms, no for the retained polynomials.** The largest
transform at `3^13` is `2^21` and no transform is larger, which is the whole claim about transform
sizes. But §4.4.4's 194.7 MB peak is dominated by the retained `G_(2^i)` — 18.0 M coefficients,
144 MB at 8 bytes, of which 11 are at the full degree because the schedule above keeps 11 steps
full-size. **That is now the whole of the peak rather than a share of it:** #161 took the transform
term to `4 n B` at one size, i.e. 67 MB at `2^21`, so the retained set went from roughly half the
peak to essentially all of it. §3.4 records [PC]'s way out ("there is no need to store all
intermediate polynomials… we use interpolation to recover it each time it is needed"), and that is
the trade this implementation does not take: it keeps them because [PC] Algorithm 2 line 8's descent
needs them, and recomputing instead would cost `O(k^2)` forward steps rather than `O(k)`. **Memory
bounded at a linear multiple of the degree, not at a constant multiple of one transform** — and
195 MB is three orders of magnitude inside this box's RAM, so the trade is not currently a
constraint. §3.9 costs out the batched `NTT_r` alternative that would remove it.

### 6.5 Goldilocks: where the method does not pay, measured

Also from `examples/graeffe_root.rs`, `goldilocks degrees=256,…,4096`, same conditions:

| degree | steps | transforms | forward | **subgroup** | descent | total | forward share |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 256 | 32 | 96 | 0.0011 s | 0.0243 s | 0.04 ms | 0.0254 s | 4.3% |
| 1 024 | 32 | 96 | 0.0040 s | 0.3244 s | 0.10 ms | 0.3286 s | 1.2% |
| 4 096 | 32 | 96 | 0.0183 s | **5.0725 s** | 0.38 ms | 5.0915 s | **0.36%** |

Pre-#161 the same rows read 0.0315 s, 0.3626 s and 5.2494 s total with a forward stage of 0.0064 s,
0.0274 s and 0.1080 s — so **#161 made the forward iteration 5.9x faster and the call 3% faster**,
because the forward iteration was never the cost here. Retained, marked superseded.

**The forward iteration is 0.36% of the call and the subgroup search is 99.6%**, growing
quadratically. **#161 sharpened this finding rather than softening it**: making the transforms
faster cannot help a stage that is not transforms.
The reason is structural and is the point: Goldilocks' odd part is `2^32 − 1`, so `beta_i >= 2^32 − 1`
for every `i <= 32` and **the progressive reduction never bites at any degree of interest** — the
final polynomial still has the input's degree, the order-`s` subgroup has `2^32 − 1` elements and
cannot be enumerated, and the search falls back to `roots` on a polynomial as large as the input.
The iteration is then pure overhead on top of the quadratic finder it was meant to replace.

**This is why [PC] writes a separate Algorithm 3 for Goldilocks**, and why §3.1's Lemma 2 and the
odd-order transform of §3.2 are load-bearing rather than decorative: driving `beta` through
`3 · 5 · 17 · 257` leaves `s = 65 537`, which is enumerable. `graeffe_l` (§10 row 4) is implemented
and validated, but is **not** wired into `graeffe_root`'s descent, because the backward phase for a
mixed order `R = 2^32 · 3 · 5 · 17 · 257` needs the gcd descent at odd `q_i` as well — [PC]
Algorithm 3 lines 10–14 — and that is a separate PR. Recorded as open in §11.

One more measured detail, because it cuts against §4.4.4's estimate: over Goldilocks the peak heap
at degree 4 096 is **2.56 MB measured against 1.31 MB estimated, a 1.95x under-prediction** —
`estimated_bytes` models the forward iteration and the subgroup search here is `roots`, whose own
peak is `12 n B` (`fast-univariate.md` §3.2). The estimate is calibrated for the route the method is
designed around and says so.

The contrast is the single most useful engineering fact in this document: **the Graeffe route is a
property of the field's `p − 1`, not of the degree.** KoalaBear's odd part of 127 is what makes the
registered challenge's field the good case, and §2.5's "smooth but shallow" verdict reads the wrong
way round — the shallow two-adicity is a ceiling on transform size, but the single small odd factor
is precisely what the root finder wants.

## 7. Required size against reachable size, and the go/no-go

### 7.1 The comparison the acceptance criteria require

Reachable, from `fast-univariate.md` §3.1 and §4.1, with the §6.1 figures beside them:

| | KoalaBear | Goldilocks | BN254 `Fr` | BLS12-381 `Fr` |
|---|---:|---:|---:|---:|
| `ntt` reached in 1 s per measurement (§3.1) | `2^23` | `2^23` | `2^21` | — |
| `intt` reached, post-#118 (§3.1 note) | `2^23` | `2^23` | `2^20` | — |
| two-adic ceiling (§4.1) | **`2^24`** | `2^32` | `2^28` | `2^32` |
| what binds at the ceiling (§4.1) | two-adicity | memory, at ≈`2^30` | two-adicity | memory, at ≈`2^30` |
| §6.1 measured wall time at `2^22` / `2^24` | 0.75 s / 3.64 s | — | — | — |

Against §2.4's required sizes:

| target | required `n` | reachable | ratio | verdict |
|---|---:|---:|---:|---|
| **the degree-`3^13` univariate itself** (`rf6-rp8`, the coordinator's figure) | `2^21` interp., `2^22` product, `2^21` per Graeffe step | `2^24` ceiling, `2^23` in 1 s | **under the ceiling by 4–8x** | **within a small factor — GO** |
| `rf6-rp6` **resultant** (CICO-2) | `2^26` | `2^24` ceiling | **4x over** | over the field's radix-2 ceiling |
| `rf6-rp8` **resultant** (CICO-2) | `2^29` | `2^24` ceiling; `2^31.0` mixed-radix | **32x over radix-2** | mixed radix mandatory |
| `rf6-rp10` **resultant** (CICO-2) | `2^32` | `2^31.0` mixed-radix max | **over even mixed-radix** | unreachable over KoalaBear |
| `poseidon256-cico-2025-rf6-rp11` (CICO-1, open) | `2^35` | `2^32` ceiling; 1.1 TB per array at 32 B | **8x over radix-2, 3.7x over RAM** | unreachable on this box |
| `poseidon256-cico-2025-rf6-rp16` (CICO-1, open) | `2^47` | `2^32` | `2^15` over | hopeless |
| `poseidon64-cico-2025-rf6-rp13` (CICO-1, open) | `2^51` | `2^32` | `2^19` over | hopeless |

### 7.2 The go/no-go

> **RETRACTED IN PART — see the retraction at the head of this document.** Reason 2 below is false
> (the disclosed `R_P = 8` attack interpolates `P_1` at degree `3^13`, not a resultant at `3^18`)
> and reason 3 applies only to the resultant route. Reason 1's *quotation* of [PC] is accurate but
> does not support the conclusion drawn from it. The **GO** half below stands unchanged.
> `elimination-beyond-grobner.md` §3.1 is the current authority.

**GO on the root finder as a component; NO-GO on any registered challenge.** The two have to be
stated separately because they answer differently, and conflating them is the specific error §9.4
warns about.

> **SUPERSEDED BY MEASUREMENT, §4.4 and §4.5 — and the estimate below was calibrated on the
> pre-#161 kernel.** Its transform count was right: **36.00** transform-size-equivalents of `2^21`
> against the **≈39** estimated. Its wall time was right *for the kernel it was built from*:
> **13.85 s measured pre-#161** against **≈14 s** estimated, to within 1%. But the rate it used is
> §6.1's 0.361 s per `2^21` transform, which #161 replaced.
>
> **What this paragraph should now read.** #161 makes a `2^21` transform ~4.24x faster
> (`fast-univariate.md` §3.3), so 39 transforms of `2^21` is **≈3.3 s**, not ≈14 s — and the
> measurement is **3.11 s**, still within 7% of the recalibrated estimate. `roots` is measured to
> degree 32 768 and extrapolates to **57.1 hours** at `3^13`, so the ratio is **≈66 000x** rather
> than ≈15 900x. Read §4.4 and §4.5 for both revisions and §6.4 for what the reduction was actually
> worth.

**GO** — the Graeffe root finder at the degree the issue's own figure names. A degree-`3^13`
polynomial over KoalaBear needs transforms of size `2^21`; the field admits `2^24` and this box
reached `2^22` in 0.75 s and `2^24` in 3.6 s with the *pre-#161* recursive kernel (§6.1).
Algorithm C with `r = 2^24`, `s = 127` costs `k = 24` order-2 steps; by §3.6's reduction rule, with
`(p−1)/δ = 1337`, the degree is full for `i ≤ 10` and halves thereafter, so the total is ≈13
full-size steps ≈ 39 transforms of size `2^21` ≈ **14 s single-threaded, pre-#161**. Against
`fast-univariate.md` §5's extrapolation of the *existing* `roots` to `d = 2^20` over KoalaBear —
**~31 hours** — that is a ~4 orders-of-magnitude reduction at a comparable degree, from a stage
that is already measured rather than hoped for. This is the clearest "within a small factor of the
measured ceiling" the issue's criterion could ask for.

**NO-GO** — the published attack on any registered instance. Three independent reasons, any one
sufficient:

1. **The 2026 KoalaBear challenges are CICO-2, which [PC] excludes from its own method** ([PC] §1
   and §4.2, quoted in §2.1). The paper's recommendation is the opposite direction: for CICO-2 "the
   best known attack would be the Gröbner basis computation together with the FGLM algorithm, or the
   mutant XL algorithm, where the main bottleneck is linear algebra". That is the pipeline this
   repository already has.
2. **The univariate object for CICO-2 is the resultant**, of degree `3^16`–`3^20`, needing `2^26` to
   `2^32` against KoalaBear's `2^24` radix-2 and `2^31.0` mixed-radix ceilings. `rf6-rp10` is
   unreachable over the field at all.
3. **The resultant construction is unreachable independent of the transform.**
   `resultant-elimination.md` §3 puts the construction at `≈ 16·3^{5·rounds}` field operations —
   `5.6×10^10` at four rounds and `10^18` at six — and measures four rounds as *not finishing in two
   hours*. The 2026 rows are **fourteen rounds**. Even granting the §4.1 fixes that document ranks
   (early-terminating interpolation, a structured determinant, an `O(n log² n)` interpolation), the
   gap is not a constant factor.

The three open 2025 CICO-1 rows *are* the right shape for the Graeffe method and are a cleaner
no-go: `2^35`, `2^47` and `2^51` required against a `2^32` radix-2 ceiling, and 1 TB for a single
coefficient array on the smallest of them against 300 GB of RAM.

**Per the issue's instruction, the gap is recorded and handed to E3/E4 as an external-memory and
hardware problem rather than an algorithmic one** — §8.

## 8. Handoff note to E3 (#88): conditions for proceeding in external memory

Scope discipline: #84 forbids designing the external-memory algorithm here, and this section does
not. It states the conditions, with their sources.

1. **The authors did it, and said what it cost.** [PC] §4.2: "When available memory is limited, users
   can configure the maximum RAM usage, and our implementation will automatically swap polynomial
   coefficients and NTT data to and from disk as needed. All other data, aside from polynomial
   coefficients and NTT values, require only a few gigabytes and should fit comfortably in RAM on
   most systems. In this scenario, overall speed will be limited by disk I/O, but still
   acceptable — in our case it is about **2 ∼ 3 times slower** than running entirely in RAM." The
   `P2_6_10` row of [PC] Table 3 is a 90 TB working set marked "data swapped to disk". **That is a
   measured external-memory slowdown factor for exactly this computation, from a primary source, and
   it is the single most useful number #88 can start from.** It also sharpens #88's own distinction:
   [PC] describes a *configured* budget with the algorithm deciding what to spill, not OS swap with
   the kernel deciding — the difference #88 exists to preserve.
2. **What has to be spillable, and what does not.** Only the coefficient arrays and NTT working
   buffers — [PC] §4.2, above. Algorithm C's other state is `ω_r`, `ω_s`, the length-`s` NTT output
   and a few scalars; for KoalaBear `s = 127`, so "a few gigabytes" is generous. **A single
   spill-aware array abstraction over `Vec<F>` would cover the whole algorithm.**
3. **The structure that makes it spillable.** A radix-2 NTT at size `n` decomposes into a
   four-step/six-step form: view the array as `n_1 × n_2`, transform the columns, twiddle, transform
   the rows. Each phase touches a contiguous block at a time, so the I/O schedule is a sequence of
   full passes over the array rather than random access, and the pass count is `O(log n / log(M/B))`.
   **The practical gate is therefore whether #161's kernel exposes a blocked phase boundary**, not
   whether an external-memory NTT exists. #161 should be asked for that boundary before it merges.
4. **The conditions, stated as a checklist for #88.**
   - A transform size whose coefficient array exceeds RAM. **On this box, over KoalaBear, this never
     happens** (§6.2): `2^24 · 8 B = 134 MB`. It happens over Goldilocks from `2^32` (34 GB array,
     within RAM) and only genuinely binds over BLS12-381 at `2^32` (137 GB array, 962 GB at `7nB` —
     `fast-univariate.md` §4.1 already identifies `2^30` as where memory binds there).
   - A kernel with an explicit blocked phase boundary (point 3).
   - A declared RAM budget with the algorithm, not the kernel, choosing evictions.
   - An I/O complexity stated in `(M, B)` and a measured bytes-to-disk figure, against which [PC]'s
     2–3x is the comparand to beat or match.
5. **What E3 should not inherit from this document.** The `4/3` lower bound of §5 is **not** an
   argument for external memory and must not be quoted as one. It is a lower bound on total data
   movement for an asymptotically large physical realization; it says nothing about whether a 90 TB
   array should live on NVMe, and §5.4 finds it inapplicable at Zeebra's sizes.

## 9. Scoping the full attack honestly

**A fast root finder is not the published attack.** A one-family reproduction of the Poseidon1
CICO-2 univariate attack shape — and `R_F = 6, R_P = 8` in particular — needs every component below,
not just the Graeffe step.

### 9.1 The components, and what Zeebra has today

| # | component | in Zeebra today? | file | gap |
|---|---|---|---|---|
| 1 | the reduced-round permutation, and the verifier's `Perm+` variant | **yes** | `src/grobner/research/poseidon.rs:381` | none |
| 2 | the registered challenge, with its identity digest and target | **yes** | `src/grobner/research/challenge.rs:1002` | none |
| 3 | the **round-skipping parametrization** (`A_1…A_k, B` of [JAZ] slide 16; [PC] §2.3's explicit `y_i`) | **yes**, #209 | `parametrize`, `CicoFamily`, `src/grobner/research/univariate_cico.rs` | none. Derived for the hybrid in §9.5.2 and asserted there; inverts the MDS via `linalg::Matrix::inverse` and takes rows `0..k` of `M^{-1}`, not the last, because the constrained inputs are the *first* `k` coordinates |
| 4 | symbolic evaluation of the permutation on an affine family — **bivariate** | **yes** | `cico_bivariate`, `src/grobner/research/resultant.rs:53` | `k = 2` only, and dense multivariate; a `cico_univariate` is the one-line analogue |
| 5 | construction of the univariate output polynomial of degree `δ` | **yes**, #209 | `cico_univariate_family`, `cico_univariate`, `src/grobner/research/univariate_cico.rs` | both routes present and asserted to agree: symbolic at `δ ≤ 4096`, evaluation-domain above it at `2^ceil(log2(δ+1))` recovered by `fft::interpolate`. `3^13` routes to `2^21`, inside the `2^24` two-adicity |
| 6 | interpolation over a power-of-two evaluation domain | **yes** | `src/fft/interpolate.rs` | sound to `2^23` KoalaBear (`fast-univariate.md` §3.1) |
| 7 | interpolation at **arbitrary** points | yes but **cubic** | `lagrange_interpolate` | `O(n³)`, measured; stops at `n = 1 024` (`fast-univariate.md` §4.3). Only needed by the resultant route |
| 8 | **NTT-based polynomial multiplication** | **yes**, #124 | `src/fft/multiply.rs` | none |
| 9 | the **Graeffe transform** `GT_2`, `GT_ℓ` | **yes** | `graeffe_2`, `graeffe_2_over_domain`, `graeffe_l`, `src/poly/univariate/graeffe.rs` | none. §6.3's three oracles are tests |
| 10 | Algorithm C's subgroup search (`mod x^s − 1`, then `NTT_s`) | **yes** | `graeffe_root`'s `subgroup_roots` | none. Resolved in favour of the direct `O(s·d)` evaluation over Bluestein: **0.10 ms of a 13.85 s call** at `3^13` (§4.4). Over a field whose odd part is large this is the binding stage instead — §6.5 |
| 11 | `k` square roots in `F_p` | **yes**, #175 | `src/fields/sqrt.rs` | none, and §3.9 shows the descent needs it only in one degenerate branch |
| 12 | candidate reconstruction and verification **through the permutation** | **yes** | `CicoInstance::is_solution`, which "rebuilds the state and runs `permutation_plus_linear`" (`poseidon.md` §2.1) | none — and this is the step [P937] §5.2 relies on to make the `O(r)` scan cheap |
| 13 | mixed-radix NTT | **no** | — | required by every row of §7.1's no-go table; out of scope for #84 |
| 14 | existing generic root finder, for comparison | yes, **quadratic** | `src/poly/univariate/roots.rs` | `O(log q · d²)`; the comparand the Graeffe path must beat, and §4.5 measures it to degree 32 768 |

**Thirteen of fourteen now exist.** 8 landed as #124, 9 and 10 as the root-finding PR, 11 as #175,
and **3 and 5 as #209**. The one that remains is **13** (mixed-radix), needed only by `rf6-rp10`,
whose method is undisclosed and which is out of scope. This supersedes two earlier readings of the
table: "the three that matter and do not are 8, 3, and 9", and "**Eleven of fourteen now exist** …
The three that remain are **3**, **5**'s evaluation-domain construction at `δ = 3^13`, and **13**."

Component completeness is not attack feasibility, and §9.5.3 is the reason: the route's cost is
`N ≈ 2^31` families times the per-family cost, and only the second factor is now buildable here.

### 9.2 Single-family cost, for `R_F = 6, R_P = 8` over KoalaBear

One family = one choice of the 12 fixed free inputs plus the affine parametrization of §9.1's
component 3. Estimates, each labelled by where its rate comes from:

| stage | size | cost | basis |
|---|---|---:|---|
| build the degree-`3^13` univariate by evaluation at `2^21` points | `2^21` permutation calls | **tens of seconds** | 14 rounds × ~16 S-boxes ≈ 250 field ops per call ⇒ `5×10^8` ops at ~640 M/s ≈ 0.8 s, plus MDS: `t² = 256` multiplications per round ⇒ `3.6×10^3` ops/call ⇒ `7.5×10^9` ops ≈ **12 s** |
| interpolate `2^21` evaluations | `2^21` | **~0.4 s**, and **~0.09 s post-#161** | §6.1, `intt ≈ ntt` post-#118 (`fast-univariate.md` §3.1 note); the post-#161 figure is §4.4.3's measured 4.53x on the same transform size |
| Graeffe iteration, Algorithm C | 72 transforms, 36.00 `2^21`-equivalents | **3.11 s, measured** (post-#161; 13.85 s pre-#161, superseded) | §4.4. The estimate both replace — "≈39 transforms of `2^21`, ~14 s" from §6.1's 0.361 s and §3.6's schedule — was right to 1% against the kernel it was calibrated on, and recalibrates to ≈3.3 s |
| `NTT_s` at `s = 127` + subgroup scan | 127 | **negligible** | `O(s²) = 16 129` multiplications |
| 24 square roots | — | **negligible** | 24 × `O(log p)` |
| candidate scan, `r = 2^24` permutation calls | `2^24` | **~100 s** | `2^24 × 3.6×10^3` ops at 640 M/s ≈ 94 s; [P937] §5.2's `O(r)` observation |
| verification through the permutation | 1 | **µs** | component 12 |
| **one family, total** | | **≈2 minutes single-threaded** | **estimated**; only the Graeffe row above is measured, and the candidate scan — which dominates — is a permutation-evaluation estimate that #161 does not touch |

Peak memory: at `7nB`, `2^21 × 8 × 7 = 117 MB` pre-#161; post-#161 and with §3.6's reduction, a few
tens of MB. **Memory is not the constraint at single-family scale**, consistent with
`fast-univariate.md` §5's finding for the whole layer.

The candidate scan dominates, which is a pleasant surprise and a real one: it is `O(r)` with
`r = 2^24` because KoalaBear's two-adicity is 24. Choosing a smaller `r` (and correspondingly larger
`s = (p−1)/r`) trades the scan against the `NTT_s`, which is [P937] §5.3's "important
consideration … the choice of parameters `r = 2^k` and `s` such that `r·s = p − 1`". With `r = 2^12`,
`s = 2^12 · 127 = 520 192`: 12 Graeffe steps instead of 24, an `NTT_s` of ~`2^19` (Bluestein, since
`s` is not a power of two), and a 4 096-call scan. **That is the parameter choice an implementation
must measure rather than assume**, and it is not stated for KoalaBear in any source read here.

### 9.3 Families needed — the number that makes §9.2 irrelevant

> **VERIFIED, AND THE NUMBER STANDS — but §9.2's per-family cost does not.** 2026/1254 has been read
> directly; **§9.5** is the resolution and supersedes this block. Outcome, in one line: the `≈2^31`
> below is **confirmed**, both of its inputs are endorsed by the paper, and the irreconcilable factor
> was never in this section — it was in §9.2's ~2 min, which bundles a ~100 s candidate scan the
> published algorithm does not perform once per family. The *separation* between per-family cost and
> family count is the right discipline and is retained. **`2^31` is now quotable as the family count
> for the univariate `k = 1` route**, with §9.5.4's two caveats: it is a model, not a measurement,
> and #210 is what measures it.
>
> The block this replaces read: "**SUPERSEDED PENDING VERIFICATION.** The `≈2^31` families derived
> below cannot be reconciled with 2026/1254 Table 1, which reports this instance solved in 7 hours on
> 96 GPUs. … the **number is not to be quoted**. See the retraction at the head of this document for
> the three candidate explanations." Two of those three candidates are refuted in §9.5.1.

This is the separation the issue insists on, and it is where the single-family figure stops meaning
anything.

**CICO-2 needs two conditions satisfied, and a one-parameter family gives one variable.** Fix 13 of
the 14 free inputs and parametrize the last by `x`; the first constrained output word is a
univariate polynomial `P_1(x)` of degree `3^13`, and §2.3's construction forces it to zero at its
roots. `P_1` "behave[s] like random polynomials in practice" ([PC] §2.3), so its expected number of
`F_p`-roots is ≈1. Each such root leaves the **second** constrained word unconstrained, zero with
probability ≈`1/p`. So

```
expected families for a CICO-2 witness by the univariate route  ≈  p  =  2.13 × 10^9  ≈  2^31
```

At §9.2's ~2 minutes per family that is **about 8 100 years single-threaded**, or ~130 years across
all 64 cores. **The one-family cost is irrelevant to the attack by a factor of `2^31`.**

**That factor is precisely why the resultant route exists.** A *two*-parameter family gives two
variables for two conditions: a zero-dimensional system whose expected number of `F_p`-points is
`O(1)`, so `O(1)` families suffice — `resultant-elimination.md` §2 found **three** base-field
witnesses on its single 2-round slice, which is that `O(1)` observed. The cost moves entirely into
the elimination: a resultant of degree `3^18` built at `≈16·3^{5·rounds}` field operations
(`resultant-elimination.md` §3), which §7.2 point 3 rules out.

So the two routes trade the same `2^31` in opposite directions, and **neither end of the trade is
affordable**:

| route | families needed | per-family cost | univariate degree | verdict |
|---|---:|---|---|---|
| univariate, `k = 1` parametrization | ≈`2^31` | ~2 min | `3^13`, `n = 2^21` — **reachable** | degree fine, family count fatal |
| bivariate + resultant, `k = 2` | `O(1)` | `≈16·3^70` field ops | `3^18`, `n = 2^29` — over the ceiling | family count fine, construction fatal |

The intermediate options — fixing fewer inputs to get a `k = 3`-variable family, or a hybrid that
guesses part of the second condition — are not analysed in any source read here and are **open**.

### 9.4 A Graeffe benchmark is not an attack

Stated in the terms the coordinator asked for, because the §9.2 table is exactly the kind of number
that gets misquoted:

- **A working `GT_2` validated against squared roots is a unit test.** It establishes correctness of
  one transform, nothing about a challenge.
- **A degree-`3^13` root-finding run completing in 14 s is a benchmark of one stage of one family.**
  It is a real and useful measurement — it would be ~4 orders of magnitude faster than
  `src/poly/univariate/roots.rs` at a comparable degree — and it is **not** evidence about
  `poseidon31-cico-rf6-rp8`, because §9.3 shows the univariate route needs `2^31` such runs and the
  resultant route needs a polynomial Zeebra's field cannot transform.
- **A successful Graeffe benchmark is not a successful attack.** No figure in this document may be
  quoted as progress on a registered challenge, and nothing here changes
  `MILESTONE-CRYPTANALYSIS-SCOREBOARD.md` §1's position: the three 2026 CICO targets are solved
  externally, the best available outcome there is a reproduction, and the three open 2025 rows are
  `2^35`–`2^51` in required transform size against a `2^32` ceiling.
- Per the scoreboard's own class discipline (§3), a Graeffe benchmark is
  `BenchmarkClass::Engineering { why }` — evidence about the implementation — and could not be
  anything else until it produces a witness verified through the permutation.

### 9.5 2026/1254 read directly — the five extractions, and the discrepancy resolved

For #208. The gate M24-0 was opened on: §9.3 derives ≈`2^31` families and 2026/1254 Table 1 reports
the same instance solved in 7 hours on 96 GPUs. §9.3's `SUPERSEDED PENDING VERIFICATION` block and
§11's `UNVERIFIED — not read here` entry both point here.

**Obtained.** `https://web.archive.org/web/20260919192452id_/https://eprint.iacr.org/2026/1254.pdf`,
18 pages, read with `pdftotext -layout`; §1's raw-content route worked first try and no 429 was hit.
The cross-check, 2026/1905 (Bak–Hostettler), came from the `20260918234320` snapshot of
`2026/1905.pdf`, 22 pages. Both are now **read here**, not at second hand.

#### 9.5.1 The five extractions

**(1) The `(1,[1])` parametrization — recovered, §2.2.** The notation is [11, Def 3.1]:
`((r_F, r_P), [δ_0 … δ_{d−1}])`, abbreviated `(r_F, [δ …])` when `r_P = 0`; `r_F` counts **skipped
full rounds**, not skipped S-boxes, and `[1]` says the state at the end of the prefix is *affine* in
the one search parameter. Its degree law, the paper's eq. (1), is
`deg_X P_i ≤ δ · α^{R_F+R_P−r_F−r_P}`.

The construction is given for `(2,[1])` — two full rounds, no initial linear layer, constrained
inputs in the last two coordinates — and it is the template. Let `λ^{(t−1)}, λ^{(t−2)}` be the last
two rows of `M^{-1}` and `y` the state after the second full round's S-box layer, *before* that
round's MDS. Substituting `z_i = y_i^{1/α}` (legitimate since `gcd(α, p−1) = 1`) turns the two input
constraints into **two affine equations in `z`**:

```
Σ_i λ_i^(t−1) z_i  =  Σ_i λ_i^(t−1) c_i^(1) + (C_1^in + c_{t−1}^(0))^α
Σ_i λ_i^(t−2) z_i  =  Σ_i λ_i^(t−2) c_i^(1) + (C_0^in + c_{t−2}^(0))^α
```

Pick `z*` solving both and a direction `v` solving the two *homogeneous* equations; then every point
of the line `z(X) = z* + vX` inverts through the prefix to an input satisfying both input
constraints. Back in the skipped state, `y_i(X) = (z*_i + v_i X)^α`, which is degree `α` in `X` —
**but choosing `supp(v) ∩ supp(z*) = ∅` collapses it to `y_i(X) = (z*_i)^α + v_i^α X^α`**, affine in
`Z = X^α`, and `Z ↦ X` is a bijection on `F_p`. The following MDS preserves affinity, so the prefix
output is affine: that is what `[1]` means, and it is worth a factor `α` in the final degree.

The `(1,[1])` case is stated rather than worked, §2.2 verbatim: *"With an additional initial linear
layer, the analogous classical construction used here gives a `(1, [1])` round skip, with output
polynomials of degree at most `α^{R_F+R_P−1}`. The initial linear layer is included in the prefix but
is not counted as a round."* §9.5.2 does the derivation for Zeebra's hybrid.

- **Degrees of freedom.** One search variable per family. `z*` ranges over a `(t−2)`-dimensional
  affine subspace and `v` over a `(t−2)`-dimensional linear subspace — at `t = 16`, 14 and 14. A
  *family* is a choice of `(z*, v)`; the supply of families is `≈p^28`, so supply is never the
  binding constraint.
- **Which constraints it forces.** The two **input** constraints, by construction, at every point of
  the line. **Neither output constraint.** Both must still be imposed on the output polynomials
  afterwards. This is the point §9.3 had right and it is worth stating plainly, because it is the
  reason the family count is what it is.
- **Family generation.** Made fully explicit at §3.2 (lines 430–465) for the five-parameter ZeroTest
  variant, and the mechanism carries down to one parameter: a base point plus direction vectors with
  **pairwise disjoint supports**, each direction's first entry normalized to one. The paper's
  concrete choice there — base support `{12,13}`, direction supports `{3j, 3j+1, 3j+2}` — is for
  **`M_{i,j} = (i − 16 − j)^{-1}`**, which is *identically* `Poseidon::cauchy_mds` at `t = 16`
  (`src/grobner/research/poseidon.rs`, `M[i][j] = (i − t − j)^{-1}`). Zeebra and the paper are
  working with the same matrix, so the support choice transfers without reinterpretation.

**(2) The expected `F_p`-root count of `P_1` — recovered, §2.2, and §9.3 was right.** Verbatim: *"The
random-polynomial heuristic predicts a probability of approximately `1−1/e` that a single output
polynomial has a base-field root; this is not the probability of satisfying both output
constraints."* `1 − 1/e` is Poisson(1)'s `P(≥1)`, so the paper is asserting **≈1 expected `F_p`-root
per family** — exactly §9.3's assumption, taken from [PC] §2.3's "behave like random polynomials in
practice". A counting argument gives the same answer independently of genericity: `π` is a
permutation, so as `X` runs over the `p` points of the line the constrained output word takes each
value about once, and `0` about once.

> **Candidate explanation 1 is refuted by the source.** `P_1` is *not* more split than a random
> polynomial, and the paper would have had to claim otherwise for the family count to fall this way.

**(3) "Common-root strategy" — recovered, §2.1 and §4.2, and §9.3 was right again.** The phrase names
a *family* of methods, and the paper is explicit about which member it used. §2.1: the classical
low-memory CICO-2 route is a **gcd** computation, which genuinely does couple the two constraints —
and 2026/1254 does not use it. Verbatim, §2.1: *"we follow the low-memory univariate strategy, but
**replace the GCD computation with Graeffe-based root finding**: we recover the roots of the
univariate polynomial corresponding to one constrained output coordinate, then evaluate the
permutation on the input induced by each root to check whether the second output constraint is
satisfied."* §4.2 repeats it for the challenge instance: *"Instead of computing a resultant with the
second constrained output polynomial, we apply Graeffe-based root finding to `P_1`. Each root induces
a candidate input, on which we evaluate the full permutation and check whether the second constrained
output coordinate has the desired value."*

> **Candidate explanation 3 is refuted by the source.** The strategy is **independent filtering of
> `P_1`'s roots against the second constraint**, one permutation evaluation per root. The `1/p` factor
> in §9.3 is the right factor. The word "common-root" was the trap: it is inherited from the gcd
> method the paper abandoned.

**(4) The total-work model's measured terms — `UNVERIFIED — not stated`. This is the named missing
input.** The model is stated, §4.2:

```
W_total  =  W_pre  +  Σ_{i=1..N} ( W_control,i + W_poly,i + W_root,i + W_check,i )
```

and **not one term of it is reported, nor is `N`**. §4.2 verbatim: *"Only aggregate timings are
available; the records do not support a breakdown by stage or a separate accounting of
preprocessing. Software versions for the original bounty runs are also unavailable."* `N` appears
only as the symbol in the sum and, qualitatively, as *"Several families may be needed before both
output constraints are satisfied"* — and as a remark on [11], *"Their concrete attack also constructs
several parametrizations and tries them in the output-solving stage."* Two **orderings** are stated
and they are all that is: `W_poly ≈ W_root` dominate (*"The dominant cost is the construction of the
univariate polynomial and the Graeffe root-finding stage"*), and `W_check` is negligible (*"this
final evaluation step is negligible compared with polynomial construction and root finding"*).
`W_control = 0` for this row — §4.2 says the CICO-2 instance *"was solved first, before the
degree-annihilation technique was developed. This attack used a classical parametrization"*.

**(5) Single run or extrapolation — recovered, Table 1, and it is a single run.** The caption:
*"Times marked 'est.' are extrapolated using (9) because the execution logs were lost; the other
times are previously reported values."* The CICO-2 row is **not** marked `est.`:

| instance | `R_F` | `R_P` | initial linear layer | round skip | GPUs | time (h) | status |
|---|---:|---:|---|---|---:|---:|---|
| **CICO-2** | 6 | 8 | yes | `(1,[1])` | 96 | **7** | **previously reported** |
| ZeroTest | 6 | 7 | no | `((3,2),[3])` | 4 | 10.45 | previously reported |
| ZeroTest | 6 | 8 | no | `((3,2),[3])` | 4 | 49.65 | previously reported |
| ZeroTest | 6 | 10 | no | `((3,2),[3])` | 28 | 64 | est. |
| ZeroTest | 6 | 11 | no | `((3,2),[3])` | 28 | 192 | est. |
| ZeroTest | 6 | 12 | no | `((3,2),[3])` | 28 | 575 | est. |

So the discrepancy carries **full weight** — the figure is a claimed measurement, not a model.
*Correction to #208 and to the milestone plan's §5.1: **three** rows are marked "est.", not four, and
they are all ZeroTest.* The figure is nonetheless an **aggregate**: no stage split, no `N`, no
software versions, logs lost. It is a wall clock, and extraction (4) is why it cannot be taken apart.

#### 9.5.2 The `(1,[1])` construction for Zeebra's hybrid `permutation_plus_linear`

§2.3's **reconstructed** marking was about this and is now discharged. `permutation_plus_linear`
(`src/grobner/research/poseidon.rs`, via `run(state, true)`) is neither Poseidon nor Poseidon2: the
initial linear layer is Poseidon2's, but the MDS is the same every round and the partial rounds take
**all-state** round constants. Written out, with `k = 2`, constrained inputs in coordinates `0, 1`
(which is what `CicoInstance::is_solution` checks — `state = constants[..k] ++ free`, so the paper's
"last two coordinates" becomes "first two" and rows `t−1, t−2` of `M^{-1}` become rows `0, 1`, exactly
the substitution §3.2 makes for its own ZeroTest instance):

```
x                        the permutation input;  x_0 = C_0^in,  x_1 = C_1^in  required
initial linear layer:    s = M · x                        <- no round constants here
round 0 (full):          u = s + c^(0);   y = u^{◦α};     then  M · y
```

Let `y` be the state after round 0's S-box layer and *before* round 0's MDS, and put
`z_i = y_i^{1/α} = u_i`. Then `z = M·x + c^(0)`, so `x = M^{-1}(z − c^(0))`, and with `λ^{(0)},
λ^{(1)}` the **first two rows of `M^{-1}`** the two input constraints become

```
Σ_i λ_i^(0) z_i  =  C_0^in  +  Σ_i λ_i^(0) c_i^(0)
Σ_i λ_i^(1) z_i  =  C_1^in  +  Σ_i λ_i^(1) c_i^(0)
```

**Two affine equations in `z`, and the right-hand sides carry no `α`-th power** — which is the one
structural difference from the paper's `(2,[1])`. There the second skipped round forces
`(C_j^in + c_j^(0))^α` onto the right, because the input constraint has to be pushed through a cubing
before it reaches `z`. Here the initial linear layer is linear, the single skipped round contributes
one constant vector, and nothing is cubed. The hybrid's all-state partial-round constants are
irrelevant: the prefix contains no partial round. The same-MDS-every-round property is likewise
irrelevant, because only `M^{-1}` for the *initial* layer enters. **That is why the hybrid inherits
Poseidon2's one-round skip rule, and §2.3's degree `α^{R_F+R_P−1} = 3^13` is unaffected.**

Family generation, concretely:

1. Choose disjoint index sets `T` (base support, `|T| = 2`) and `S` (direction support, `|S| = 3`).
   Following §3.2's choice: `T = {12, 13}`, `S = {0, 1, 2}`.
2. Solve the `2×2` system on `T` for `z*` supported on `T`. Solvable for *any* `T`: `M` is MDS, so
   is `M^{-1}`, so every `2×2` minor is nonsingular.
3. Solve the `2×3` homogeneous system on `S` for `v` supported on `S`, normalizing `v`'s first entry
   to one. A nonzero kernel vector exists because `3 > 2`, and every `2×2` minor being nonsingular
   forces it to have **full support on `S`** — so `supp(v) = S`, disjoint from `T` as required.
4. `y_i(Z) = (z*_i)^α + v_i^α Z`, affine. Lift a search point `Z` to the input by
   `x = M^{-1}(z(Z^{1/α}) − c^(0))`; equivalently work from `y` directly, `z_i = y_i(Z)^{1/α}`.
5. A new family is a new `(T, S)` or a new solution within the same supports.

**The oracle, and it is an assertion rather than a reading — and it is green.** `x_0 = C_0^in` and
`x_1 = C_1^in` must hold **identically in `Z`**, at many random `Z` and many random families, with
`x` recovered as above and fed through `permutation_plus_linear`. A construction that has the wrong
rows of `M^{-1}`, the wrong constant vector, or the paper's `α`-th power left on the right-hand side
fails at the first point.

Implemented in `src/grobner/research/univariate_cico.rs` for #209, and asserted by four tests over
the `rf2-rp0`, `rf2-rp2` and `rf4-rp0` reductions:

| test | what it settles |
|---|---|
| `the_family_holds_the_input_constraints_at_every_point` | `x_0, x_1` are the input constants at 64 random `Z` per row — **this is the test that discharges §2.3** |
| `the_lifted_input_reproduces_the_skipped_state` | the lifted input's first-round S-box outputs *are* `y(Z)`, so the prefix matches `run`'s own schedule and not an idealized one |
| `the_family_polynomial_agrees_with_the_permutation` | `P_i(Z)` equals the constrained output word, minus its target, on the lifted input |
| `the_family_polynomial_has_the_round_skipping_degree` | `deg P_i` **equals** `α^{R_F+R_P−1}` — attained, not merely bounded, so the skip is real |

So this subsection is **derived and verified**: derived from a source rather than guessed, which is
the distinction §2 of `additional-benchmarks.md` draws for Griffin's linear layer, and then checked
against the permutation. One corroboration arrived for free: the degree test attains the bound
exactly on all three rows, which would fail if the prefix were skipping the wrong amount of work.

#### 9.5.3 The discrepancy, resolved with arithmetic

Extractions (2) and (3) **confirm both inputs to §9.3's family count**, so the count itself survives:

```
families per witness  ≈  1 root per family  ×  1/p per root  →  N ≈ p ≈ 2^31
```

That leaves only one place for a factor of `2^31` to hide: the **per-family cost**. And §9.2's ~2
minutes is not the per-family cost of the algorithm 2026/1254 §4.2 describes. Its stage list is

| §9.2 stage | per family in 2026/1254's loop? |
|---|---|
| build the degree-`3^13` univariate at `2^21` points, ~12 s | **yes** — `W_poly` |
| interpolate `2^21` evaluations, ~0.09 s | **yes** — `W_poly` |
| Graeffe, Algorithm C, **3.11 s measured** | **yes** — `W_root` |
| `NTT_s` at `s = 127` + subgroup scan, negligible | yes, inside `W_root` |
| 24 square roots, negligible | yes, inside `W_root` |
| **candidate scan, `r = 2^24` permutation calls, ~100 s** | **no** |
| verification through the permutation, µs | yes — `W_check`, "negligible" in §4.2 too |

The `~100 s` row is the cost of enumerating the two-adic subgroup in Zeebra's **single-root descent**,
not a stage of the published per-family loop — which evaluates the permutation on the **≈1** recovered
root of `P_1`, and whose own `W_check` the paper calls negligible. It is 100 of the 120 seconds.
Corrected to the stages the published algorithm actually runs:

```
per family, single-threaded, Zeebra's own figures:   12 + 0.09 + 3.11  ≈  15.2 s   (not ~120 s)
total implied work at N = 2^31:                      2.15e9 × 15.2 s   ≈  1 036 core-years
published:                      7 h × 96 GPUs        =  672 GPU-hours  =  2.42e6 GPU-s
implied per-GPU throughput over one Zeebra core:     3.27e10 / 2.42e6  ≈  1.35e4
```

So the published figure requires each RTX 5090 to be worth `≈1.4 × 10^4` of this box's cores on this
workload. A defensible factor for `2^21` independent permutation evaluations plus power-of-two NTTs
on a 21 760-core GPU is `10^2`–`10^3`. The residual is therefore **≈13×** at `10^3`, **≈43×** at
`10^2.5`, and `≈135×` at `10^2`:

| reading | residual gap | orders of magnitude |
|---|---:|---:|
| §9.3 as written: ~8 100 core-years vs 7 h wall clock, no throughput model | `1.06e5` | **~5.0** |
| §9.3's work vs 672 GPU-hours, no throughput model | `1.06e5` | ~5.0 |
| corrected per-family cost, no throughput model | `1.35e4` | ~4.1 |
| corrected per-family cost, GPU worth `10^2` cores | `135` | ~2.1 |
| corrected per-family cost, GPU worth `10^2.5` cores | `43` | **~1.6** |
| corrected per-family cost, GPU worth `10^3` cores | `13` | **~1.1** |

**Verdict: within two orders of magnitude for any per-GPU factor above ≈140.** The "four orders of
magnitude after any plausible GPU factor" in §9.3 and in the milestone plan's §1 was the product of
two separable errors — comparing core-years against a wall clock without converting to a common work
unit, and charging the published loop for a stage it does not run — and neither was in the family
arithmetic. **Candidate explanation 2 (more usable freedom per family) is not needed to close the
gap and remains open**; a fourth candidate, Zeebra's per-family cost itself, turns out to carry most
of it.

**Independent anchor, 2026/1905 Table 4.** Bak–Hostettler attack the *same* CICO-2 challenge family
(Poseidon1 with the initial linear layer, `R_F = 6`, one full round skipped) by a bivariate Villard
resultant — deterministic, no family search at all — and measure:

| `R_P` | budget | time | source |
|---:|---|---|---|
| 6 | 128 CPU cores | 1 d 17 h | 2026/1905 |
| 7 | 128 CPU cores | 21 d 5 h | 2026/1905 |
| 8 | 96 GPUs | 7 h | 2026/1254, cited not re-measured |

`R_P = 7` is `21 d 5 h × 128 = 7.4` core-years measured, and the `6 → 7` step costs `12.4×`, so one
more partial round puts `R_P = 8` at **≈92 core-years** by their route. `672` GPU-hours at `10^2`–`10^3`
cores-equivalent is `7.7`–`77` core-years. **Two independent methods bracket the total work for this
instance at `10^1`–`10^2` core-years**, which is what makes the corrected ~1 036 core-years for the
family-search route the *right order of magnitude for a less efficient algorithm* rather than an
absurdity — and 2026/1905 §5.3 says as much about the comparison: *"our attack complexity grows in
`d^{2.66 R_F}` with the number of full rounds, whereas theirs grows in `d^{R_F}`."*

#### 9.5.4 Go / no-go, against §5.2 of the milestone plan

The criterion was: **go** if extractions (1)–(4) are recoverable and the family count is within two
orders of magnitude of the published cost once GPU parallelism is accounted for; **no-go** if the
parametrization or the family-generation procedure cannot be reconstructed without guessing.

| | verdict |
|---|---|
| (1) parametrization | **recovered**, §2.2, generalized at §3.2; hybrid derived in §9.5.2 |
| (2) root count of `P_1` | **recovered**, §2.2 — and it confirms §9.3 |
| (3) common-root strategy | **recovered**, §2.1 and §4.2 — and it confirms §9.3 |
| (4) total-work model's terms | **`UNVERIFIED — not stated`** — no term, and no `N` |
| (5) 7 h / 96 GPUs | **single run**, previously reported, not an extrapolation |
| family count vs published cost | within two orders for any per-GPU factor `> ≈140` |

**GO.** The no-go trigger is not met and is not close to met: both the parametrization and the
family-generation procedure are written out in the source, the hybrid case follows from them by
linear algebra rather than by guessing, and the one ambiguity that had to be resolved — which rows of
`M^{-1}`, and whether the right-hand side carries an `α`-th power — is decided by the constrained
input position, not chosen. Nothing here is a guessed attack.

Two things are **not** resolved, and they are the honest residue:

1. **`N` and the stage split are unavailable in principle, not merely unreported** — the execution
   logs are lost and the paper says so. The named missing input is therefore
   **`N` together with `W_poly`/`W_root` for the `R_F = 6, R_P = 8` CICO-2 run**. No future reading
   of 2026/1254 recovers it. The `≈13×`–`≈135×` residual in §9.5.3 cannot be closed from the
   literature and can only be closed by measurement, which is #210's whole purpose.
2. **The `1 036` core-years is a model, not a measurement.** Only the `3.11 s` Graeffe row inside it
   is measured; the `12 s` construction is an estimate. §9.4 applies to it unchanged: it is not a
   figure about a registered challenge, and `BenchmarkClass::Engineering { why }` is the only class
   it could carry.

What #210 therefore measures is unchanged by this reading, and better motivated by it: the observed
**distribution** of `F_p`-roots of `P_1` per family against the ≈1 the paper endorses, the observed
second-constraint rate against `1/p`, and the observed families-per-witness on a row small enough to
finish. Extractions (2) and (3) turn those from exploratory numbers into **falsifiable predictions
taken from the source** — which is the strongest form this document's open question could have been
left in.

### 9.6 The family economics, measured — `examples/graeffe_cico.rs`

For #210. §9.5.1 turned §9.3's two assumptions into predictions taken from 2026/1254; this section
checks them. Reproduce with

```
cargo run --release --example graeffe_cico -- --families 3000 --budget 25
```

A ladder of ten rows — the nine registered `t = 16, k = 2` reductions plus
`poseidon-t3-rf2-rp1-planted`, which is `k = 1` — each family built by `cico_univariate_family`,
root-counted, lifted, and verified through `CicoInstance::is_solution`. **17 838 families.** Every
row would carry `BenchmarkClass::Engineering { why }`; no record is written, because that needs
`ZEEBRA_AFFINITY`, `ZEEBRA_MACHINE` and the serialized benchmark lock.

#### 9.6.1 Assumption 1 — ≈1 base-field root per family. **Confirmed.**

| row | `δ` | families | mean roots | share with none | family cost |
|---|---:|---:|---:|---:|---:|
| `t3-rf2-rp1-planted` (`k = 1`) | 9 | 3 | 1.0000 | 0.3333 | 68.7 µs |
| `t16-rf2-rp0` | 3 | 3 000 | 1.0013 | 0.3187 | 118.9 µs |
| `t16-rf2-rp2` | 27 | 3 000 | 0.9960 | 0.3733 | 210.0 µs |
| `t16-rf4-rp0` | 27 | 3 000 | 1.0217 | 0.3503 | 222.7 µs |
| `t16-rf2-rp4` | 243 | 2 954 | 0.9939 | 0.3629 | 1.414 ms |
| `t16-rf4-rp2` | 243 | 2 892 | 1.0152 | 0.3709 | 1.525 ms |
| `t16-rf6-rp0` | 243 | 2 900 | 0.9762 | — | 1.547 ms |
| `t16-rf4-rp4` | 2 187 | 45 | 0.8222 | — | 64.95 ms |
| `t16-rf6-rp2` | 2 187 | 44 | 0.7500 | — | 65.77 ms |
| `t16-rf6-rp4` | 19 683 | 115 | census skipped | — | 218.8 ms |
| **pooled** | | **17 838** | **0.9997** | | |

**0.9997 against a predicted 1.0.** The *distribution*, not only the mean, tracks Poisson(1) —
`t16-rf4-rp0`, 3 000 families, observed against Poisson(1):

| roots | 0 | 1 | 2 | 3 | 4 | 5 | 6 |
|---|---:|---:|---:|---:|---:|---:|---:|
| observed | 0.3503 | 0.3820 | 0.1853 | 0.0633 | 0.0163 | 0.0023 | 0.0003 |
| Poisson(1) | 0.3679 | 0.3679 | 0.1839 | 0.0613 | 0.0153 | 0.0031 | 0.0005 |

The share of families with no base-field root sits at 0.35–0.37 against `1/e = 0.3679`, which is
2026/1254 §2.2's `1 − 1/e` existence probability reproduced directly.

Two honest qualifications. The `δ = 3` row departs — `{0, 1, 3}` roots at `0.3187 / 0.5213 / 0.1600`
and *no* two-root families — and that is **correct**, not anomalous: a cubic over `F_p` has 0, 1 or 3
roots, never exactly 2 without a repeated root. It is a low-degree artifact, and it is the reason
`δ = 3` is a good oracle row and a poor statistics row. Second, the `δ = 2 187` rows read 0.75–0.82,
but at 44–45 families the standard error of the mean is ≈0.15, so both are within ~1.5σ of 1.0;
they are small-sample noise and are reported rather than smoothed.

> **This settles candidate explanation 1 empirically, after §9.5.1 settled it textually.** `P_1` is
> root-count-generic. There is no factor hiding here.

#### 9.6.2 Assumption 2 — independent `1/p` filtering. **Independence confirmed; the rate is not measurable.**

`0` hits in `17 901` roots tested. That is uninformative about the *rate* and the example says so:
`1/p = 4.69e-10` predicts `8e-6` hits at this sample size, and 0 hits gives only a 95% upper bound of
`3/n ≈ 1.7e-4`, which fails to separate `1/p` from anything below it. **No run of this example on
this hardware can measure that rate**, and claiming otherwise would be the error §9.4 exists to stop.

What *is* measurable is **independence**, which is the half of the assumption that could actually be
wrong — §9.3 assumed it and milestone §6.3 asks for it by name. Binning the second constraint's
residual `out[1] − C_1^out` into 256 bins gives, on 255 degrees of freedom (mean 255, sd `√510 ≈ 22.6`):

| row | `χ²` | verdict |
|---|---:|---|
| `t16-rf2-rp0` | 234.7 | consistent with uniform |
| `t16-rf2-rp2` | 278.1 | consistent with uniform |
| `t16-rf4-rp0` | 201.9 | consistent with uniform |
| `t16-rf2-rp4` | 245.4 | consistent with uniform |
| `t16-rf4-rp2` | 234.1 | consistent with uniform |

Every row is inside ±3σ. **The `(1,[1])` parametrization does not correlate the two output
constraints**: conditioned on `P_0` vanishing, the second constrained word is uniform as far as this
test can see. Combined with §9.5.1's reading of §4.2 — Graeffe plus one permutation evaluation per
root, no gcd — the `1/p` factor is now confirmed from both directions.

> **This also closes candidate explanation 2**, the last of §9.3's three. "More usable freedom per
> family" would have to show up either as extra roots (§9.6.1: it does not) or as correlated
> constraints (here: it does not). All three candidates are now eliminated, and §9.5.3's correction
> to the *per-family cost* is the whole of the reconciliation.

#### 9.6.3 Assumption 3 — `≈p` families per witness. **Confirmed as a model, and not measurable on any registered reduction — which is the finding.**

This is where #210's framing has to be corrected. The issue and milestone §6.3 both ask for "the
observed count on a row small enough to finish", on the expectation that a reduced row reduces the
family count. **It does not.** The count is

```
families per witness  ≈  p / (roots per family)
```

and `p` is fixed by the field. Reducing `R_F` and `R_P` cuts `δ`, hence the per-family cost, and
leaves the family count untouched. The ladder demonstrates exactly that: **`δ` spans 6 561× from
row 2 to row 10 and the mean root count does not move off 1.0.** So `N ≈ 2^31` on
`poseidon31-cico-t16-rf2-rp0` just as on `poseidon31-cico-rf6-rp8`, and no `k = 2` row on this
ladder — or any reduction of it — can produce a witness. Zero witnesses were found and none was
expected.

Where it *can* be measured, it was. `poseidon-t3-rf2-rp1-planted` is `k = 1`: one output constraint
is all there is, so a base-field root of `P_0` **is** a witness and no `1/p` filter applies.
**1.00 families per witness, 3 witnesses verified through `CicoInstance::is_solution`** — the whole
pipeline, parametrization through verification, end to end. That calibrates the mechanism and
isolates the `1/p` factor at `k = 2` as the entire difference between `O(1)` families and `2^31`.

Also worth recording as a structural fact rather than a bug: the two `t = 2` planted rows are
**skipped**, because a `(1,[1])` family needs `2k + 1` disjoint support indices and `t = 2 < 3`. The
construction has a minimum state width, and `t = 2` is below it.

#### 9.6.4 Per-stage costs, and the one row that exercises the evaluation domain

`t16-rf6-rp4` is the only ladder row above `SYMBOLIC_CROSSOVER`; it takes the evaluation route at
`2^15` points with a `2^15`-size interpolation and a max Graeffe transform of `2^15`:

| stage | total over 115 families | mean per family | share |
|---|---:|---:|---:|
| parametrization | — | 39.4 µs | 0.02% |
| construction (`2^15` permutation evaluations) | — | 172.0 ms | **77%** |
| interpolation (`fft::interpolate`) | — | 1.07 ms | 0.5% |
| Graeffe root finding (`GraeffeStats`) | — | 50.5 ms | **23%** |
| lifting + verification | — | µs | <0.01% |

**This reproduces 2026/1254 §4.2's own cost ordering**: *"The dominant cost is the construction of
the univariate polynomial and the Graeffe root-finding stage"*, and *"this final evaluation step is
negligible compared with polynomial construction and root finding"*. Construction beats root finding
roughly 3.4 : 1 here, and the two together are 99.98% of the family. That is a second, independent
corroboration of §9.5.3's central move — the published loop's per-family cost is construction plus
Graeffe and nothing else, which is exactly why §9.2's ~100 s candidate-scan row did not belong in it.

The symbolic rows split differently: at `δ = 243`, construction is ~0.9–1.0 ms against ~0.44 ms of
Graeffe, and at `δ = 3`–`27` the Graeffe descent's fixed overhead (the `s = 127` subgroup scan and 24
squarings, which do not shrink with `δ`) actually *dominates* construction. That crossover is a
property of the implementation, not of the attack, and no figure here should be read as a per-family
cost for `δ = 3^13`: the ladder stops at `3^9`.

#### 9.6.5 What this does and does not establish

- It **does** confirm, by measurement, both inputs to §9.3's `2^31`: ≈1 root per family and
  uncorrelated output constraints. The family count is no longer an assumption.
- It **does** establish that the univariate `k = 2` route cannot produce a witness on any registered
  reduction, because the family count is invariant under round reduction. A reduced row buys a
  cheaper family, not a cheaper search.
- It **does not** measure the `1/p` rate, and cannot. §9.5.4's named missing input — 2026/1254's `N`
  and stage split — is therefore still the binding gap, and the `≈13×`–`≈135×` residual of §9.5.3
  stands unclosed.
- It **does not** touch `δ = 3^13`. The largest row here is `3^9`, four factors of three short, and
  the construction stage scales linearly in `δ` while the ladder's per-row budget does not.
- §9.4 applies to every figure above without exception.

## 10. Proposed PR decomposition

Each row is independently reviewable, has its own oracle, and does not depend on any cryptanalytic
claim. Rows 1–4 are unblocked by #124 only in the sense that they are *useless* without it; row 2
onward requires it merged.

| PR | content | depends on | oracle | status |
|---:|---|---|---|---|
| 1 | **this document** | — | the PDFs, read | **landed** |
| 2 | `examples/ntt_access.rs` to §6.3's specification, plus KoalaBear and Goldilocks arms in `benches/field_arithmetic.rs` | **#161 merged** | the `evaluate`/`interpolate` round trip; the in-run arithmetic figure against the criterion arm | open, blocked on #161 |
| 3 | `graeffe_2` — the order-2 transform, `(−1)^d(f_e² − x f_o²)` | **#124** | §6.3's three checks: squared roots at degree 16; `GT_2∘GT_2 == GT_4`; `deg` preserved | **landed**, `graeffe_2`, `graeffe_2_over_domain` |
| 4 | `graeffe_l` for odd prime `ℓ`, by [PC] §3.2's product recursion | 3 | `GT_ℓ` against `∏(x − r_i^ℓ)`; `GT_{ℓ₀}∘GT_{ℓ₁} == GT_{ℓ₀ℓ₁}` | **landed** as a transform for any order, prime or not; **not** wired into row 6's descent — see §6.5 |
| 5 | `sqrt` in `F_p` (Tonelli–Shanks) on `KnownOrder`, reusing `src/fields/two_adic.rs` | — | `x² == y` for the returned root; `None` for non-residues, cross-checked by the Euler criterion | **landed** separately as #175, `src/fields/sqrt.rs`; not reimplemented |
| 6 | `graeffe_root` — Algorithm C of §3.5, with §3.6's progressive reduction | 3, 5 | planted roots at degrees `2^8`…`2^16` over KoalaBear and Goldilocks, cross-checked against `src/poly/univariate/roots.rs` on every size the quadratic one reaches | **landed**, with [PC] Algorithm 2 line 8's descent in place of Algorithm C's `r`-way scan, which §3.5's correction block shows is unusable as transcribed — see §3.9 |
| 7 | `(r, s)` parameter selection, measured — §9.2's open question | 6 | a sweep over `k` reporting Graeffe steps against `NTT_s` size and scan length; no assertion | **answered, not swept**: §3.5's correction and §3.9 show the descent removes the scan, so `r = 2^two_adicity` and `s` the odd part is forced rather than chosen. No trade-off to sweep over KoalaBear |
| 8 | the round-skipping parametrization (§9.1 component 3) and `cico_univariate` | 4 (`cico_bivariate`'s pattern) | the parametrized family's constrained coordinates are the input constants at every point, asserted against `permutation_plus_linear` | **landed, #209** — `src/grobner/research/univariate_cico.rs`; the oracle is the first row of §9.5.2's table. Note the row's original wording said "last coordinate", which is the paper's input position and not Zeebra's: `CicoInstance` constrains the **first** `k` |
| 9 | an `examples/graeffe_cico.rs` ladder: one family end-to-end on *reduced* rows, reporting §9.2's per-stage costs and `BenchmarkClass::Engineering` | 6, 8 | every witness verified through `CicoInstance::is_solution` | **landed, #210** — §9.6. Ten rows, 17 838 families; the three witnesses are all on the `k = 1` row, and §9.6.3 is why there are none on the others. Record-writing deliberately left to a follow-up |
| 10 | extend `docs/research/graeffe-root-finding.md` with §9.2's figures as **measured** rather than estimated; re-take §6.1 as a post-#161 curve | 2, 9 | — | **partly landed**: §4.4, §4.5, §6.4 and §6.5 are the root-finding half, measured **both pre- and post-#161**. §6.1's own curve is still the pre-#161 one and awaits a re-take; §9.2's other rows still await row 8 |
| 11 | `graeffe_root` over a field whose odd part is large: [PC] Algorithm 3's odd-order forward steps and the gcd descent at odd `q_i`, wiring row 4 into row 6 | 4, 6 | planted roots over Goldilocks at a degree where §6.5's quadratic fallback does not finish | open — §6.5 is the measurement that motivates it |

**#161 has since merged**, so row 2 and the §6.1 half of row 10 are unblocked rather than blocked.
Row 1 was the first PR; rows 3, 4, 6 and the root-finding half of 10 are the second, measured
against both kernels.

## 11. Marked unverified, and open

- `UNVERIFIED — not read` the Springer conference version at `10.1007/978-3-032-35412-9_16` itself.
  Paywalled; Unpaywall reports no OA location. [PC] (ePrint 2025/1916) is its preprint by the same
  four authors with the same title, and is what is cited. Any figure that appears only in the
  Springer typesetting is not recorded here.
- `UNVERIFIED — not read` references `[7]` (Bak–Bariant–Boeuf–Hostettler–Jazeron, as a *paper*),
  `[8]`/`[9]`/`[10]` (Grenet–van der Hoeven–Lecerf; van der Hoeven–Monagan), `[24]`, `[32]`, `[34]`
  and `[35]` as cited by [PC] and [P937]. [JAZ]'s **slides** by the `[7]` authors were read and are
  cited as [JAZ]; the paper was not obtained. In particular **Figure 12 of [7]**, the fitting curve
  from which [PC] Table 3's comparand columns are *estimated*, was not read, so the "`2^13` faster"
  claim is recorded in §4.1 as reproducing from [PC]'s own table against an unread extrapolation.
- `UNVERIFIED — not read` the authors' CUDA implementation.
- **Discrepancy between sources**, recorded in §2.3: [PC] Table 1 gives `x ↦ x^5` for
  "M31 / KoalaBear"; [JAZ] slide 5 and `challenge.rs` give `α = 3` for KoalaBear and `α = 5` for
  Mersenne-31. Resolved in favour of the registry.
- **Discrepancy within [PC]**, recorded in §4.3: the 128-bit security estimate is "about `2^200`"
  in §1 and `2^198` in §4.2.
- **Typographical, recorded in §5.1**: [PC] Lemma 4 and Theorem 1 state `O` where their proofs
  establish `Ω`.
- **Unproven in its source**, recorded in §2.4: the CICO-2 resultant degree `d^{2(R_F−1)+R_P}` is
  called an *experimental result* in [JAZ] slides 19 and 22, with the coincidence with the ideal's
  degree left as an open question by its authors.
- **Reconstructed**, per §3.8: the skip count for Zeebra's hybrid `permutation_plus_linear` remains
  reconstructed and untested, since nothing in the root-finding PR touches the permutation. The
  expansion of Algorithm B line 16 and the Bluestein sizing schedule were both **reconstructions of
  steps the implementation does not need** — §3.8's verdict column says which and why.
- **Resolved, §3.5's correction block and §3.9**: Algorithm C lines 14–18 are not implementable
  outside the attack, and the `(r, s)` split for KoalaBear is therefore not a trade-off. Algorithm C's `r`-way scan
  is what made `r` a parameter worth sweeping, and the gcd descent removes the scan, so
  `r = 2^two_adicity` with `s` the odd part is forced. §10 row 7 is closed as answered rather than
  swept.
- **Open**: `graeffe_root` over a field whose odd part is large — §6.5 measures Goldilocks spending
  98% of the call in a subgroup search the reduction never shrinks, and §10 row 11 is the
  Algorithm-3-shaped fix. Also open: whether a `k = 3` family or a hybrid beats both ends of §9.3's
  trade; whether #161's kernel exposes the blocked phase boundary §8 point 3 needs; and whether the
  retained `G_{2^i}` of §6.4 can be dropped for the batched `NTT_r` scan §3.9 costs out, which trades
  384 MB and 62.7 ms for 134 MB and 3.6 s.
- **READ HERE, §9.5** — **2026/1254** (Sanso–Vitto, *Top Gun: Degree Annihilation Attacks on
  Poseidon*) and **2026/1905** (Bak–Hostettler, *A Better Bivariate Resultant Attack on
  Round-Reduced Poseidon*). Both obtained from the Wayback raw-content route and read from the PDF
  for #208; §9.5 records §2.2's `(1,[1])` construction, §2.1's and §4.2's definition of the
  common-root strategy, §4.2's cost model and Table 1, and 2026/1905 Table 4. **This document no
  longer quotes either at second hand**, and the earlier entry — "they were not available to this
  document … Any figure attributed to them here is at second hand from
  [`elimination-beyond-grobner.md`](elimination-beyond-grobner.md), which is the authority for them"
  — is struck. That sibling remains the authority for the parts of both papers §9.5 did not need:
  §3's degree-annihilation framework, the `((3,2),[3])` ZeroTest skip, and all of 2026/1905 except
  §5.3's Table 4.
  - Still `UNVERIFIED — not stated` **within** 2026/1254: every term of `W_total` and the family
    count `N`. §4.2 states the logs are lost and the timings are aggregate only, so this is
    unavailable in principle rather than unreported. See §9.5.1 extraction (4) and §9.5.4.
  - Not read in either paper: 2026/1254 §3.3 (the three-partial-round conditions) and Appendix-level
    detail of 2026/1905 §4 (Villard's algorithm). Neither bears on the univariate route.
- **RESOLVED, §9.5 — the gate is open.** The entry here read: "**Open, and it decides the gate**: the
  family count for the `R_P = 8` CICO-2 instance. §9.3's `≈2^31` against 2026/1254 Table 1's 7 hours
  on 96 GPUs. Resolving this needs 2026/1254 §4.2 read directly, with attention to the expected
  `F_p`-root count of `P_1`, how much freedom the `(1,[1])` parametrization supplies per family, and
  what 'common-root strategy' denotes operationally." All three were read. The root count is ≈1 and
  the strategy is independent `1/p` filtering — both **as §9.3 assumed** — so `≈2^31` stands; the
  reconcilable error was in §9.2's per-family cost, and the residual after correction is ~1.1 orders
  of magnitude at a `10^3` per-GPU factor. §9.5.4 records the **go**.
- **Open, and now the only thing in the way**: the residual `≈13×`–`≈135×` of §9.5.3, which depends
  on an assumed per-GPU throughput factor because 2026/1254's `N` and stage split are lost. Not
  closable from the literature, and **#210 did not close it either** — §9.6.2 shows the `1/p` rate is
  unmeasurable at any sample size this hardware can reach. What #210 did close is the *inputs*: ≈1
  root per family and uncorrelated constraints are now measured, not assumed, so `2^31` is a model
  with measured parameters rather than a model with assumed ones.
- **Measured, §9.6.3, and it corrects #210's own framing**: the family count is **invariant under
  round reduction**. `p / (roots per family)` has no `R_F` or `R_P` in it, and the ladder shows `δ`
  spanning 6 561× with the mean root count fixed at 1.0. So "the observed count on a row small
  enough to finish" does not exist at `k = 2`: no registered reduction can produce a witness, and a
  reduced row buys a cheaper family rather than a cheaper search.
- **Open**: nothing on this ladder reaches `δ = 3^13`. §9.6 stops at `3^9`, and §9.6.4's per-stage
  split is measured there, not at the disclosed target.
- **Closed by #209**: §9.5.2's `(1,[1])` construction for `permutation_plus_linear` is derived *and*
  verified. `src/grobner/research/univariate_cico.rs` asserts the constrained input coordinates at
  many random points on three reductions, that the lifted input reproduces the skipped state through
  `run`, that the polynomial agrees with the permutation, and that the degree **attains**
  `α^{R_F+R_P−1}`. This entry previously read "Derived but unverified … until that is green the
  construction is unconfirmed."
- §6.1's figures are from **one uncommitted throwaway binary on one machine against the pre-#161
  recursive kernel**, taken under `tools/benchlock.sh` with six other agents active. They are
  labelled a baseline for exactly that reason and PR 10 above re-takes them.
- §4.4, §4.5, §6.4 and §6.5's figures are from a **committed** binary, `examples/graeffe_root.rs`,
  one core (`taskset --cpu-list 8`) under `tools/benchlock.sh`. **Two revisions, both reported**:
  pre-#161 in §4.4.2 and post-#161 in §4.4.1, with §4.4.3 the difference. Single-shot rather than
  a median of interleaved runs: the ratios being reported are 10x and larger, where this machine's
  noise — which `README.md`'s crossover section needs 21 interleaved runs to see past — does not
  change a conclusion. A 1.1x claim would need the interleaved protocol and none is made. The one borderline
  figure is §4.4.3's 1.07x on the descent, which is **reported as "did not get faster", not as a
  7% gain.**
- **Nothing in §4.4–§6.5 is evidence about a registered challenge.** §9.4 states the discipline and
  it is unchanged by these measurements: per-family root-finding cost is measured, the family count
  a CICO-2 witness needs is the open question above, and `2^31` is not quoted.
