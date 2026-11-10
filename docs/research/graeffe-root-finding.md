# Graeffe root finding: the published algorithm, the degree it consumes, and whether Zeebra's NTT is access-bound

**Measured at:** publication bound `bc8778cc`…`bfec9d71` — the commits that published these figures,
recovered from git rather than recorded at the time ([§10](external-comparison-protocol.md#10-the-commit-and-what-a-publication-bound-is)).
[§6.3.1](#631-the-binary-landed--and-what-it-answers-which-is-half-the-question)'s post-#161 sweeps
are stamped base `5e785fd1` plus blob `3146be5b24a2`
(`git hash-object examples/ntt_access.rs`), per #505. The published sweep was taken at a one-minute
load of **5.55**, under the binary's own publishable gate of 8; §6.3.2 is why every run states its
load and why the arithmetic denominator is paired per row. `5e785fd1` is the tree the measured
binary was built from, which is not this branch's base; `git diff 5e785fd1 <base> -- src/fft/
src/poly/` is empty, so the transform and the polynomial code the figures describe are
byte-identical at both.

Reference for D3 (#84), a child of the #68 epic. This is the **reading and scoping half**; the
implementation half is blocked on #124 (polynomial multiplication through the transform).

The issue imposes one evidentiary rule, and this document honours it strictly: *no figure from a
paper is recorded here without having been read in the PDF.* Every paper figure below carries a
section or table reference to a PDF that was obtained and read. Figures that could not be verified
are marked `UNVERIFIED`.

*The 2026-11-05 retraction of §7.2's go/no-go for the registered CICO-2 targets was moved out with
the cryptanalysis research in #668; it is preserved at commit 9532a9a2.*

## 1. The papers, and how they were obtained

`eprint.iacr.org/*.pdf` is behind a Cloudflare interstitial that returns HTTP 403 from this
environment — confirmed again on 2026-11-05 with `curl`, a browser `User-Agent` and a `Referer`.
The working route is the Wayback Machine's **raw-content** form,
`https://web.archive.org/web/<ts>id_/https://eprint.iacr.org/<year>/<id>.pdf`; the `id_` suffix is
essential, since without it the rewritten viewer HTML is returned instead of the original bytes.
Wayback rate-limits aggressively and `curl --retry 12 --retry-delay 25 --retry-all-errors` cleared
every 429. This supersedes the "PDF not obtained" note the issue was opened with: **Wayback raw
content is the first thing to try for an ePrint PDF from this environment**, ahead of the HAL and
institutional-page routes that `docs/research/additional-benchmarks.md` §8 (moved out in #668) records for other papers.

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

*§2 (the CICO problem instance, its round-skip degree, and the degree and transform size per
registered instance, §2.1–§2.5)
was moved out with the cryptanalysis research in #668; it is preserved at commit 9532a9a2.*

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
`P2_6_8` $133 against $4 000. **Those prizes were claimed, and the programme behind them is
`expired`** — the 2025 bounty programme "runs till December 1st, 2025", read 2026-11-08
(`prize-ledger.md` §2, moved out in #668). The figures are a published cost-versus-reward ratio, quoted; none of them
is available.

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

**Superseded in part by [§6.3.1](#631-the-binary-landed-and-the-answer-access-binds-at-1632-mb-and-not-at-the-l3-boundary), which re-takes this curve post-#161 from the committed binary.**
Its conclusion survives; its `ns/butterfly` and `achieved` columns and its flatness observation do
not. Read it for the baseline and §6.3.1 for what the kernel costs now.

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

**Implemented, #591.** The binary exists at `examples/ntt_access.rs` and
[§6.3.1](#631-the-binary-landed-and-the-answer-access-binds-at-1632-mb-and-not-at-the-l3-boundary)
has its results.
This section is kept as the specification it was written as, because the three deviations from it
are worth being able to see. The arithmetic comparand reports **both** an isolated and an
accumulated multiply rate rather than only the isolated one §6.3 asked for, since neither is tight
enough to resolve the last few percent and the accumulated form is what §6.1 used. The binary
carries a **load gate** §6.3 did not specify. And the comparand is measured **once per row** rather
than once per field — the deviation that turned out to be load-bearing, for the reason in §6.3.2.

The issue asks for "an NTT size sweep reporting effective field operations per second against
transform size, with peak bytes, from a committed `examples/` binary". This was the specification,
**not** the code — #84's experimental half was blocked on #124 and the kernel was being rewritten
under #161, so committing the binary then would have committed a table that #161 invalidates on
merge.

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

### 6.3.1 The binary, landed, and the answer: access binds at 16–32 MB, and not at the L3 boundary

`examples/ntt_access.rs` is §6.3's specification, implemented and committed for #591, with the
KoalaBear and Goldilocks arms added to `benches/field_arithmetic.rs`. Neither field had one: `p31`
and `p31_u32` are the Mersenne-31 modulus and `p64` is `2^64 - 59`, a prime of two-adicity **2**, so
before this no committed arm could supply an NTT comparand — which is what §6.3 flagged.

Taken under `tools/benchlock.sh`, `taskset --cpu-list 12`, at a **one-minute load of 5.55** against
the binary's own publishable gate of 8. The arithmetic comparand is re-measured immediately before
each row rather than once per field, for the reason in §6.3.2; its own span over each sweep was
1.13x–1.19x, which is why that matters.

#### The three sweeps

`p/c` is peak live heap over coefficient bytes. `arith` is the isolated multiply rate in M mul/s
measured beside that row. `achieved` is the transform's effective rate over it.

**KoalaBear, `2^31 - 2^24 + 1`, 8 bytes.** Two-adicity 24, so the array never leaves the 256 MB L3.

| `log2 n` | coeff | `p/c` | ns/bf | arith | achieved |
|---:|---:|---:|---:|---:|---:|
| 10 | 8 KB | 1.00 | 2.69 | 353.0 | 105.3% |
| 13 | 64 KB | 1.00 | 2.66 | 356.3 | 105.4% |
| 16 | 512 KB | 1.00 | 2.86 | 351.1 | 99.7% |
| 19 | 4 MB | 1.00 | 2.90 | 382.4 | 90.1% |
| 21 | 16 MB | 1.00 | 3.07 | 349.1 | **93.2%** |
| 22 | 32 MB | 1.00 | 4.10 | 402.1 | **60.6%** |
| 23 | 64 MB | 1.00 | 4.47 | 354.6 | 63.0% |
| 24 | 128 MB | 1.00 | 4.75 | 337.0 | 62.5% |

**Goldilocks, `2^64 - 2^32 + 1`, 8 bytes.** Reaches `2^26`, 512 MB, past the L3.

| `log2 n` | coeff | `p/c` | ns/bf | arith | achieved |
|---:|---:|---:|---:|---:|---:|
| 10 | 8 KB | 1.00 | 2.62 | 400.4 | 95.4% |
| 16 | 512 KB | 1.00 | 3.14 | 382.7 | 83.3% |
| 19 | 4 MB | 1.00 | 3.18 | 379.9 | 82.8% |
| 21 | 16 MB | 1.00 | 3.40 | 399.4 | **73.7%** |
| 22 | 32 MB | 1.00 | 4.33 | 354.3 | **65.2%** |
| 24 | 128 MB | 1.00 | 5.01 | 366.3 | 54.5% |
| 25 | 256 MB | 1.00 | 5.22 | 363.4 | 52.7% |
| 26 | 512 MB | 1.00 | 6.07 | 355.9 | 46.3% |

**BN254 `Fr`, 32 bytes.** Reaches `2^26`, **2 GB**, four doublings past the L3.

| `log2 n` | coeff | `p/c` | ns/bf | arith | achieved |
|---:|---:|---:|---:|---:|---:|
| 10 | 32 KB | 1.00 | 20.34 | 40.9 | 120.2% |
| 14 | 512 KB | 1.00 | 26.63 | 39.2 | 95.8% |
| 18 | 8 MB | 1.00 | 28.56 | 41.1 | 85.3% |
| 20 | 32 MB | 1.00 | 32.29 | 42.4 | **73.0%** |
| 22 | 128 MB | 1.00 | 31.81 | 39.3 | 80.0% |
| 23 | 256 MB | 1.00 | 32.92 | 38.4 | 79.2% |
| 24 | 512 MB | 1.00 | 33.81 | 38.5 | 76.8% |
| 26 | 2 GB | 1.00 | 35.18 | 38.1 | 74.6% |

#### Four results, in order of how much they change

**1. The `7nB` footprint is gone, exactly.** `p/c` is **1.00 at every one of the 49 rows**. §6.1's
`7nB` was the recursive formulation's `evens_and_odds`, a `UnivariatePolynomial::new` copy,
`domain.split()` and a fresh output `Vec` at each of the `log2 n` levels; post-#161 the transform
allocates its output and nothing else. A counter, so exact and machine-independent.

**2. Up to a few MB the transform runs at its field's own arithmetic rate.** 90–105% on KoalaBear
to `2^19`, 83–95% on Goldilocks, 83–120% on BN254. §6.1's figure for the same quantity was
**8.7–9.6%**, so a radix-2 NTT over a 31- or 64-bit prime now costs **one field multiplication per
butterfly** to within the precision of the comparand. §6.1 concluded the pre-#161 shortfall was the
recursive formulation and not the cache; removing the formulation recovered the arithmetic rate,
which confirms that from the other side.

**3. The access bound does bind — and it binds at 16–32 MB of coefficients, not at the 256 MB L3.**
Both 8-byte fields step down hard between `2^21` (16 MB) and `2^22` (32 MB): KoalaBear 93.2% → 60.6%
and Goldilocks 73.7% → 65.2%, with `ns/butterfly` rising 3.07 → 4.10 and 3.40 → 4.33. On a box at
load 5.55, so this is **not** ambient eviction. And it is **not** the DRAM boundary either, which is
the finding that matters for anyone sizing a transform here: crossing 256 MB costs Goldilocks 16.3%
(5.22 → 6.07 ns/bf) and BN254 **2.7%** (32.92 → 33.81), both far less than the 16–32 MB step.

So 32 MB — the working set `MILESTONE-SIMD-PARALLELISM.md` §5.3 called "out of cache" and §8.2
corrected to "out of L2, still in L3" — is where this transform's cost actually changes. §8.2's
correction was right about the *cache* and the step is there anyway, which is a statement about the
access pattern rather than about capacity: a radix-2 transform revisits the whole array `log2 n`
times with a stride that doubles each pass, so what has to stay resident is not bounded by the
array's size alone.

**4. The degradation saturates, and it saturates lower for the field with more bytes per
operation.** KoalaBear reads 60.6%, 63.0%, 62.5% across 32, 64 and 128 MB — flat. BN254 reads
73.0%, 80.0%, 79.2%, 76.8%, 74.6% from 32 MB to **2 GB**, six doublings and four of them past the
L3, essentially flat. Only Goldilocks keeps falling, 65.2% to 46.3%.

The field comparison is the sharpest evidence in the section, because it holds the machine fixed and
varies only arithmetic intensity. BN254's element is 32 bytes and its multiply is **9x** slower than
KoalaBear's (40.3 against 354.3 M mul/s, measured in the same run), so it performs about four times
fewer multiplications per byte of traffic — and it is the field that degrades **least** and stops
degrading soonest. A transform bound by access would degrade *more* for the field carrying more
bytes per operation. That it degrades less is what says the residual 20–40% is a latency the
arithmetic can partly hide, rather than a bandwidth wall.

#### What this does and does not settle

- **Settled:** below ~16 MB of coefficients the transform is arithmetic-bound on all three fields,
  and 2025/950's premise does not describe it there. The `7nB` footprint is gone. The step's
  location (16–32 MB) and depth (35% of the arithmetic rate for an 8-byte field, 20% for a 32-byte
  one) are measured on a quiet box.
- **Not settled:** *why* 32 MB. Nothing here distinguishes an effective-capacity limit from a stride
  or associativity effect, which would need hardware counters rather than a size sweep — and that is
  a different instrument, not a longer run of this one. The `4/3`-power claim is asymptotic and three
  fields over six doublings past the step do not test an exponent; what they test is whether the
  premise holds at Zeebra's own sizes, and the answer is "not below 16 MB, partly above it, and
  saturating rather than growing".
- **Not measured:** anything about a mixed-radix or a cache-oblivious formulation, which is what the
  step suggests would pay. That is an optimization and #591 is a measurement; it should be its own
  issue if the 16–32 MB regime turns out to be where a caller lives.

#### What §6.1 keeps and what it loses

Its conclusion — the 90% deficit was the recursive formulation, not the cache — stands. Its absolute
`ns/butterfly` column (16.25–20.59) is superseded by 2.65–2.90 in the flat region, a **6.4x**
improvement at matched size, and its `achieved / arithmetic rate` column (8.7–9.6%) by 90–105%. Its
flatness observation — "`ns/butterfly` varies by ±13% over a 16 384-fold range of `n`, and it is
*worst at the smallest size*" — does **not** survive: post-#161 the curve is flat to `2^21` and then
steps, and it is worst at the largest size. §6.2's conclusion that KoalaBear cannot answer the
access question also stands, and is now visible in the table: its sweep ends at 128 MB with no row
outside the L3, and the `Across the L3 boundary` line it would otherwise print is replaced by the
refusal to draw one.

### 6.3.2 The denominator has to be paired per row, and that was found the hard way

The first version of the sweep measured the multiply rate **once per field**, before the first
transform, exactly as §6.3 reads. On a quiet box that is harmless. On this one it produced
`achieved` readings of **105–165%** on KoalaBear, because the denominator was measured during a slow
window and the numerators during a faster one: the same binary measured 371 M mul/s in one run and
133 M mul/s eleven minutes later.

So each row now re-measures the isolated rate immediately before its own transform, and the sweep
prints how far that denominator moved over the whole sweep — 1.13x to 1.19x in the published runs
above, and the binary says so, because a wide span invalidates reading the `ns/butterfly` column
*across* rows even though `achieved` survives it. This is the same interleaving discipline the rest
of the repository's A/B figures use, applied to a ratio rather than to two arms.

It is worth recording as a method note rather than a footnote: **the figure that survived a 2.8x
swing in this box's absolute speed was the paired ratio, and the figure that did not was the
absolute time.** Four KoalaBear sweeps taken at one-minute loads of 325, 611, 644 and 998 gave
`ns/butterfly` at `2^12` of 5.19, 2.64, 2.65 and 2.64 — and `achieved` of 107.6%, 101.1%, 106.7% and
102.1%. The ratio moved by 6 points across a 2x spread in the absolute figure, and the published
run at load 5.55 reads 100.4% on the same row.

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

> **Wired in by #593 — §6.6.** The odd-order steps and the gcd descent at odd `q_i` both land, and
> over Goldilocks the route becomes `Enumerated { points: 65537 }` where this section measured
> `GcdRootFinder`. One correction to the paragraph above, which §6.6 is mostly about: the steps pay
> **from about degree 1 024 and not below it**, so the 256-row in the table above stays on the gcd
> route and is right to. The crossover is a property of the degree as well as of `p − 1`.

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

### 6.6 #593: the odd-order steps, wired in — and the crossover is a degree

[PC] Algorithm 3's two missing halves both land: the odd-order forward steps, and the gcd descent at
odd `q_i` that inverts them. `graeffe_l` had been implemented and validated since §10 row 4 with no
caller in the descent, for the reason §6.5 gives — the backward phase needed `gcd(g, x^q − mu)`
rather than the order-2 shortcut of reducing modulo `x^2 − mu`.

**What changed, exactly.** Over Goldilocks `s = 2^32 − 1 = 3 · 5 · 17 · 257 · 65537`. Steps at
`3, 5, 17, 257` leave a residual subgroup of **65 537**, and the search enumerates it:

| | before #593 | after #593 |
|---|---|---|
| order-2 steps | 32 | 32 |
| odd-order steps | — | **4**, at `3, 5, 17, 257` |
| transforms | 96 | **100** |
| subgroup order faced | 4 294 967 295 | **65 537** |
| route at degree 1 024 | `GcdRootFinder { degree: 1024 }` | **`Enumerated { points: 65537 }`** |

Every figure in that table is a **count**, exact and machine-independent, which is why it is here
and §6.6.2's timings are not. The counts are asserted by
`test_the_odd_steps_make_the_goldilocks_subgroup_enumerable`.

#### 6.6.1 The steps pay from about degree 1 024, and are declined below it

§6.5 reads as though the odd steps are simply what Goldilocks needs. They are not unconditionally:
**the crossover is a property of the degree as well as of `p − 1`.** Enumerating the residual costs
`s_residual (d + 1)` and the gcd route costs `log q (d + 1)^2`, so with `s_residual = 65 537` and
`log q = 64` the first is cheaper only from

```text
65537 (d + 1) <= 64 (d + 1)^2        <=>        d + 1 >= 1024
```

Below that the four transforms would be paid and the search would still take the gcd route — which
is precisely the criticism §6.5 makes of the order-2 iteration over Goldilocks, and it would be
no better one phase later. So `plan_odd_steps` takes the steps **all or nothing**: if the factors
available do not get the residual below the crossover, it takes none, and a degree-256 Goldilocks
instance keeps exactly the route and the 96 transforms it had. `test_small_goldilocks_instances_keep_the_old_route`
asserts that side, including the transform count, so the decline cannot silently become a cost.

This also reads §6.5's own table correctly in hindsight: its 256-row is below the crossover, so that
row would not have moved and the method's floor there is the gcd route's.

Two smaller decisions, both recorded in the source rather than inferred:

* **A factor is worth a step only below `2^16`.** An order-`q` transform multiplies `q` scaled
  copies, so its cost grows with `q` while the subgroup it removes shrinks by the same factor.
  The bound keeps `3, 5, 17, 257` and excludes Goldilocks' own `65 537`, whose step would cost more
  than enumerating it — which is the residue Algorithm 3 is written to leave behind.
* **A transform the field cannot host is a cost, not a refusal.** `graeffe_l` needs a primitive
  `q`-th root and a domain for the degree-`q d` product; where it fails the phase stops at whatever
  order it reached and the search runs there, rather than failing a call the order-2 route alone
  would have answered. Found by `test_a_field_without_the_two_adicity_refuses`, which a first
  version broke by propagating the error.

#### 6.6.2 What is not measured, and why

**The timing curve beside §6.5's is not taken.** §10 row 11's fourth deliverable asks for the
Goldilocks curve reported against the fallback it replaces, and that is a wall-clock measurement
this machine could not produce honestly: over the hours this work ran, the one-minute load average
sat between **592 and 1 261**, from other agents' linkers, which `tools/benchlock.sh` does not
serialize because they are builds rather than measurements. §6.5's own figures were taken single-shot
on one pinned core under the lock, and a comparison against them from a box in this state would be
a comparison of load.

What is reported instead is the part that does not depend on the box: the counts above, and the
route. A reader wanting the curve should re-run

```sh
tools/benchlock.sh <tag> taskset --cpu-list 8 \
  cargo run --release --example graeffe_root -- goldilocks degrees=1024,2048,4096
```

on a quiet machine and report it beside §6.5's rows, which were taken that way. The expectation it
should test is **not** that the forward stage gets cheaper — it gets four transforms more expensive
— but that the subgroup stage stops being 99.6% of the call.


## 7. Required size against reachable size, and the go/no-go

*§7 (required against reachable transform size for the registered instances, and the go/no-go)
was moved out with the cryptanalysis research in #668; it is preserved at commit 9532a9a2.*

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

*§9.1–§9.6 (scoping the full attack: components, per-family cost, family counts, the 2026/1254
reading and the measured family economics) were moved out with the cryptanalysis research in #668;
they are preserved at commit 9532a9a2. §9.7 below is the general deflation root finder and stays.*

## 9.7 #351: all roots by deflation, measured against the gcd finder

§4.4 priced `graeffe_root` at **one** root, and the elimination route needs **every candidate**, so
nothing in this document before now was a like-for-like comparison with `roots`. #351 closes that,
and the gap is the reason the comparison was worth making rather than assuming.

### 9.7.1 The bridge, and what bounds it

`graeffe_all_roots` takes a root, divides it out by synthetic division in `O(d)`, and repeats until
the deflated polynomial has no base-field root left. Multiplicity falls out: a root of multiplicity
`m` survives `m − 1` deflations and is reported `m` times.

**Its cost is `(roots + 1)` searches, so it is a bet on the root count and not on the degree.** That
is the honest framing — against a polynomial with `O(d)` base-field roots it would lose to a single
gcd pass, and §9.7.3 is the measurement that decides which regime the real route is in.

### 9.7.2 Both finders on one polynomial per degree

`examples/graeffe_root -- deflate`, KoalaBear in a `u64`, one pinned core, on the lock. `agree` is
the two finders' root sets compared — a mismatch is a test failure, not a footnote.

| degree | deflation | roots found | roots/s | `roots` | **speedup** | agree |
|---:|---:|---:|---:|---:|---:|:---:|
| 729 | 0.0117 s | 4 | 340.5 | 0.0595 s | **5.1×** | yes |
| 6 561 | 0.1133 s | 5 | 44.1 | 2.8677 s | **25.3×** | yes |
| 32 768 | 0.3022 s | 4 | 13.2 | 48.6214 s | **161×** | yes |
| **59 049** | **0.5001 s** | 4 | 8.0 | **153.2146 s** | **306×** | yes |

The speedup **grows with the degree** because the two sides scale differently: deflation pays a fixed
number of Graeffe searches whose cost is near-linear in the degree, while `roots` pays one
quasi-quadratic pass. It is not a constant factor and should not be quoted as one.

### 9.7.3 The root count of a real resultant, measured

The regime question from §9.7.1, answered on **registered rows** rather than on planted inputs, via
`examples/resultant_cico --row` (moved out in #668):

| row | resultant degree | `F_p` roots | verified witnesses |
|---|---:|---:|---:|
| `poseidon31-cico-t16-rf2-rp0` | 81 | **3** | 3 |
| `poseidon31-cico-t16-rf2-rp2` | 729 | **1** | 1 |

**`O(1)`, not `O(d)`** — which is the regime deflation wins in, and it is consistent with the
Poisson(1) behaviour §9.6 measured for a different family. Two rows is two rows, and the six-round
rows are unmeasured; but a degree-729 resultant having **one** base-field root is a strong indication
that the candidate count is set by the problem's structure rather than by the eliminant's degree.

### 9.7.4 The `roots` curve, superseding the two-point fit

#351's other half. `roots` by doubling, eight points rather than the two in
`resultant-elimination.md` §6.3:

| degree | 256 | 512 | 1 024 | 2 048 | 4 096 | 8 192 | 16 384 | 32 768 | 65 536 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| seconds | 0.0048 | 0.0163 | 0.0651 | 0.2380 | 0.8519 | 3.1612 | 11.7957 | 44.7701 | 175.5648 |
| local exponent | — | 1.76 | 2.00 | 1.87 | 1.84 | 1.89 | 1.90 | 1.92 | 1.97 |

The local exponent settles at **1.90–1.97**, so the two-point **1.933** was right and is now
supported by eight points instead of two. It was flagged as the weakest number in the M25-D analysis
and it survives; what does not survive is the figure built on top of it.

### 9.7.5 What this does to `rf4-rp2`, and what it does not

*§9.7.5 (what the measurement does to the `rf4-rp2` registered row's cost)
was moved out with the cryptanalysis research in #668; it is preserved at commit 9532a9a2.*

---

## 10. Proposed PR decomposition

*§10 (the PR decomposition for the attack reproduction)
was moved out with the cryptanalysis research in #668; it is preserved at commit 9532a9a2.*

## 11. Marked unverified, and open

*§11 (open and unverified items for the attack reproduction)
was moved out with the cryptanalysis research in #668; it is preserved at commit 9532a9a2.*
