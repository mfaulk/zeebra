# Elimination beyond Gröbner bases: a feasibility assessment

**Measured at:** publication bound `f2135cce`…`03b419f7` — the commits that published these figures,
recovered from git rather than recorded at the time ([§10](external-comparison-protocol.md#10-the-commit-and-what-a-publication-bound-is)).
The bound is unchanged by the 2026-11-08 re-scoring (§0.1, §5.1, §7.1): **nothing was measured for
it.** Every Zeebra figure it quotes is cited to the document that took it —
[`resultant-elimination.md`](resultant-elimination.md),
[`graeffe-root-finding.md`](graeffe-root-finding.md),
[`fast-univariate.md`](fast-univariate.md) and
[`MILESTONE-PUBLISHED-ATTACK-REPRODUCTION.md`](../MILESTONE-PUBLISHED-ATTACK-REPRODUCTION.md) — each
carrying its own declaration.

Reference for #68. A decision record in the style of #58 — the question answered once with the
measurements attached — covering D1 (#82), D2 (#83), D3 (#84) and D4 (#85).

**#68's deliverable is an assessment, not an implementation, and nothing was implemented for it.**
Much has since been implemented *because* of it, under M23 and M24; §5.1 and §7.1 score the
assessment against that tree rather than claiming it as this epic's work.

### Revision history

This document was written three times as sources became readable, and two of its conclusions were
retracted. Both retractions are recorded here rather than edited away, because the shape of the
error is itself informative: each came from reasoning about the attack from complexity formulas
instead of from what the implementations actually do.

1. **First draft** had only Jazeron's slide deck; both ePrint PDFs returned HTTP 403. It declined the
   resultant route for all three registered targets on a memory figure of **824 TB**.
2. **Retraction 1.** That figure modelled `δ · D_I` as a resident working set. It is the *operation
   count*. The streaming evaluation–interpolation form uses `O(D_I)` memory — 1.55 GB, not 824 TB.
   Memory was never the wall.
3. **Retraction 2.** Having read 2025/950, the draft then argued from its remark that for more than
   one constrained zero "the best known attack would involve multivariate polynomial solving", and
   concluded the epic's challenge to Zeebra's architecture was unsupported. **2026/1905 supersedes
   that with measurements**: for CICO-2, Gröbner is the *least* competitive of three methods, by
   about 7 500x in time at the only instance all three reach. Gröbner is the best known method for
   CICO-k at **k ≥ 3**, not k = 2. §4.
4. **This version** rests on six sources, all read, including two that describe the actual solutions
   to two of the three registered targets, and one with public code.
5. **This re-scoring keeps §5 and §7 and adds the scores beside them** (2026-11-08). §5 and §7 were
   written `03b419f7`…`8b343139` and not revised since, and in the three days after, every one of
   §5's four items landed and D4 took its measurement. They are not edited away, in
   [`resultant-elimination.md`](resultant-elimination.md)'s style: what one reading supported and
   what the next one changed is the useful artifact, which is what the two retractions above are
   for. §0.1, §5.1, §7.1.

## 0. Recommendation

> **§0.1 supersedes this list.** Everything below was carried out; one item was reversed by the
> carrying out. Read §0.1 for the current recommendation and this list as the plan it was.

1. **The direction is real, published, and implemented.** Two of Zeebra's three registered 2026
   CICO-2 targets now have public technical disclosures, and one has public code. This is no longer a
   question about complexity estimates. §1, §2.
2. **First priority: reproduce the univariate route, not the resultant.** The `R_P = 8` target was
   solved *without* a resultant — round skip, interpolate one output coordinate, Graeffe root
   finding, then test candidates against the second constraint. Its working degree is `3^13`, which
   needs a `2^22` transform, **comfortably inside KoalaBear's `2^24` power-of-two ceiling**.
   NTT-based multiplication is the **only missing foundational polynomial-arithmetic primitive** for
   that route — but it is not the attack. Three attack-specific components also have to be written
   and validated: the round-skipping parametrization, the Graeffe transform itself, and candidate
   reconstruction and verification. Zeebra's root finder today is the gcd/factorization route, not
   Graeffe. §3.1, §5.
3. **Second priority: benchmark against Bak–Hostettler's public implementation** rather than build a
   resultant from scratch. It provides single-threaded evaluation–interpolation, Villard resultants
   *and* Gröbner comparisons, which is exactly the instrument D4 needs. §6.3.
4. **Gröbner's remaining territory is CICO-k with k ≥ 3**, where it is the best known method. Every
   registered target is k = 2, which is the one regime where it is outclassed. That is the honest
   answer to the epic's framing, and it is a reason to be careful about what the F4/FGLM path is
   claimed to be *for*. §4.
5. **Do not chase `R_P = 10`.** No public method exists; the programme allows reports to stay private
   until 2027-01-01. §2.3.

#68's go/no-go — "decline the direction if D4 shows the resultant path is not competitive" — is now
answerable in the other direction: §4's Table 3 shows the Gröbner path is the uncompetitive one on
CICO-2. What is still missing is any Zeebra measurement. §7.

### 0.1 The recommendation above, carried out — and one item reversed by carrying it out

Re-scored 2026-11-08. The list reads as a plan and is now a record.

| §0 item | state | what settles it |
|---|---|---|
| 1. the direction is real, published, implemented | **unchanged** | §1, §2 |
| 2. first priority is the univariate route, with NTT multiplication its only missing primitive | **done** | the primitive landed (#185); the three attack-specific components landed (#209, #210); one family measured end to end over 17 838 families with three verified witnesses — [`graeffe-root-finding.md`](graeffe-root-finding.md) §9.6. §5.1 scores each item |
| 3. second priority is to benchmark the public implementation **rather than build a resultant** | **reversed** | M24 built the Sylvester machinery and it moved the verified frontier from two rounds to six — [`MILESTONE-PUBLISHED-ATTACK-REPRODUCTION.md`](../MILESTONE-PUBLISHED-ATTACK-REPRODUCTION.md) §7.8. #85's closing comment records the reversal in those terms |
| 4. Gröbner's remaining territory is CICO-`k` at `k ≥ 3` | **unchanged, and no longer only somebody else's measurement** | §4 is 2026/1905's; [`resultant-elimination.md`](resultant-elimination.md) §2 is Zeebra's own on a registered slice, and agrees |
| 5. do not chase `R_P = 10` | **unchanged** | §2.3 |
| 6.4's `method_disclosed` field | **landed** | `challenge.rs` carries `DisclosedMethod`, with `poseidon31-cico-rf6-rp10` set to `Unknown`; README's challenge-registry section pins it |

**The current recommendation.** The elimination direction is **accepted**, it is implemented, and the
measured leverage is about the **formulation and not the engine**: three orders of magnitude separate
two ways of writing the same CICO slice, and F4 is on the expensive side of it
([`resultant-elimination.md`](resultant-elimination.md) §7). What remains is engineering with issues
already against it — #194 (half-GCD), #297 (a structured Sylvester determinant, the one axis left
with an asymptotic improvement in it), #371 (M26) — not a feasibility question. That is why #68
closes here rather than staying open as §7 directed; §7.1 is the scoring, the four caveats the
closure has to carry, and the three issues this epic's own residue became.

## 1. The method map

2026/1905 Table 1, *Best algebraic attacks for different CICO sizes (with no round-skips)*, verbatim.
`ω` is the matrix-multiplication exponent:

| CICO-k | method | complexity (Õ) | source |
|---|---|---|---|
| 1 | univariate solving | `d^(R_F+R_P)` | [BBLP22, ZSVD25] |
| 2 | guess & solve / GCD | `p · d^(R_F+R_P)` | [BBB+26, SV26] |
| 2 | bivariate resultants | `d^(3R_F+2R_P)` | [BBB+26] |
| 2 | " | `≥ d^(2(R_F+R_P))` | [GKK+26] |
| 2 | " | `d^((3-1/ω)R_F + (2-1/ω)R_P)` | 2026/1905, this work |
| **k ≥ 3** | **Gröbner bases** | `d^(ω(kR_F+R_P))` | [BBB+25] |

**Gröbner bases are the state of the art for `k ≥ 3` and for nothing below it.** All three of
Zeebra's registered targets are `k = 2`.

### 1.1 What is proven about `D_I`, and what is not — resolved

Every cost figure in this document depends on the ideal degree `D_I`. The first version of this
section recorded that two sources worded the claim differently, cited different results for it, and
that **neither primary source had been read**. Both have now been read, 2026-11-06, and so has the
theorem one of them cites. The discrepancy is resolved and **it was a citation error, not a
mathematical disagreement.**

| claim | strength | source, read |
|---|---|---|
| `D_I ≤ d^(k·R_F+R_P)` for Poseidon | **proven upper bound**, under stated genericity | eprint **2025/2040** (`[BBB+25]`, *The Algebraic CheapLunch*), Table 1 and §4.2 |
| `D_I = d^(c·R_F+R_P)` | asserted **equality** | 2026/150 §4.3, attributed to `[BSGL20, Theorem 10]` — **the attribution does not hold, see below** |
| `deg Res = D_I` for CICO-2 Poseidon | **experimental observation** | 2026/150 §4.3: "We also experimentally observed that…" |
| `deg Res = d^(2R_F+R_P)`, exactly | **measured here**, three rows, three independent checks | [`resultant-elimination.md`](resultant-elimination.md) §6.3 |

**The misattribution.** 2026/150 §4.3 states, verbatim: "It has been shown [BSGL20, Theorem 10] that
the systems for a CICO-c problem on Poseidon have a degree of the ideal equal to `D_I = d^(c·R_F+R_P)`."
Theorem 10 of eprint 2020/948 (Ben-Sasson, Goldberg, Levit, *STARK Friendly Hash — Survey and
Recommendation*) actually reads:

> **Theorem 10.** The degree of the univariate polynomial of the lexicographical Gröbner basis of
> `S_CICO0_Hades(a)` is `d^(k·R_F + P·R_P − 2k + 1)`

with, for Starkad/Poseidon (`d = 3`, `P = 1`), `D = 3^(k·R_F + R_P − 2k + 1)`. **The `− 2k + 1` is
dropped in 2026/150's rendering.** At `k = 2` that is a factor of `d^3`; 2020/948's own complexity
table for `k = 2` correspondingly reads `3^(2R_F+R_P−3)`, not `3^(2R_F+R_P)`.

**Which value is right for Zeebra's instances is settled by measurement, not by the citation.**
`resultant-elimination.md` §6.3 measured the resultant degree on three registered `t = 16` rows and
got `d^(2R_F+R_P)` exactly — 729 at `R_F=2, R_P=2`, where Theorem 10's formula would give
`3^3 = 27`. The measurement is checked three ways there (uniqueness of the interpolant below a
proven degree ceiling, agreement with a direct Sylvester determinant at points outside the
interpolation domain, and the root lifting to an accepted pair). So **the repository's figures rest on
a proven upper bound plus its own measurement that the bound is attained on these instances, and at
no point on 2026/150's citation.**

What that leaves open: **why Theorem 10's formula differs is not established here.** Its system is
written `S_CICO0_Hades(a)` and may be normalized differently — the subscript and the argument are
unexplained in the quoted statement — so this section records the numerical disagreement and
Zeebra's measurement rather than asserting that 2020/948 is wrong.

**The consequence for this document is favourable and narrower than the first version feared.** That
version warned that "every degree and every derived cost in this document [is] an upper bound on a
particular instance's, not a prediction of it". For the three rows §6.3 measured, the bound is
attained and the degrees *are* predictions. For the registered targets at larger `R_P`, they remain
upper bounds — which is still the conservative direction, so no conclusion flips.

**A bonus from 2025/2040, and it belongs to the Anemoi work.** Its Table 1 also gives
`D_I ≤ (d+2)^(k·R)` for Anemoi with `2k = t`. At `k = 1` that is `(d+2)^R` — which is exactly the
`(α+2)^N` quotient dimension `additional-benchmarks.md` §3.2 measured from the `six-worlds-anemoi`
logs and tagged `Claim::Observed` because "the designers' corresponding statement is a conjecture".
**There is now a proven upper bound for it**, so a Zeebra measurement agreeing with `(α+2)^N` can be
checked against a bound rather than only against someone else's measurement. Handed to #201.
2025/2040's Table 1 also marks the CheapLunch genericity assumptions as **not satisfied** for Griffin
and ArionHash, which is relevant to #202 and which §7 of `additional-benchmarks.md` did not know.

Within the Gröbner approach the bottleneck has already moved off F4: [ABM23] observed that Poseidon
CICO systems have a lower solving degree than random ones, so "the bottleneck shifts from the Gröbner
basis computation step to finding an univariate polynomial in the ideal" — and 2026/1905 confirms it
in practice, "the bottleneck for the Gröbner basis attack comes from the change-of-ordering step,
which is performed using the FGLM algorithm". That is Zeebra's FGLM, and it is the stage M23's
scalability work is aimed at.

## 2. What was actually published, per registered target

Zeebra registers three official 2026 CICO targets in `src/grobner/research/challenge.rs`: Poseidon,
KoalaBear, `alpha = 3`, `t = 16`, `k = 2`, `R_F = 6`, `R_P ∈ {6, 8, 10}`, with an initial linear layer
before the first round.

| target | EF verified | published method | reported cost | source |
|---|---|---|---|---|
| `R_P = 6` | 2026-04-10 | Villard-style bivariate resultant, one full round skipped | **1 d 17 h on 128 CPU cores** | 2026/1905 |
| `R_P = 8` | 2026-05-06 | round skip + interpolation + **Graeffe root finding, no resultant** | **7 h on 96 RTX 5090 GPUs** | 2026/1254 |
| `R_P = 10` | 2026-07-06 | none located | — | — |

**The publications establish successful attacks at these parameters; they do not necessarily identify
the submissions the EF verified on those dates.** The programme site does not name first submitters,
so the match is circumstantial and should be recorded as such — see §6.4 on what the scoreboard
should hold.

### 2.1 `R_P = 8` — the univariate route, and the most useful result for Zeebra

> **This section is no longer the sole authority for 2026/1254.** For #208,
> [`graeffe-root-finding.md`](graeffe-root-finding.md) §9.5 read the PDF directly and extracted §2.2's
> `(1,[1])` construction in full, §2.1's and §4.2's operational definition of the "common-root
> strategy" (**independent `1/p` filtering of `P_1`'s roots, not a gcd**), §4.2's cost model and what
> it does *not* report, and Table 1's run-versus-estimate status. It also derives the construction for
> Zeebra's hybrid `permutation_plus_linear`. This section remains the authority for §3's
> degree-annihilation framework and the `((3,2),[3])` ZeroTest skip, which §9.5 did not need.

Sanso–Vitto, *Top Gun: Degree Annihilation Attacks on Poseidon* (2026/1254). The paper's contribution
is degree annihilation, but §4.2 is explicit that the CICO-2 `R_P = 8` instance "was solved first,
before the degree-annihilation technique was developed. This attack used a classical parametrization,
followed by the common-root strategy". The strategy, from §4.2:

> For the CICO-2 instance with `R_F = 6` and `R_P = 8`, the challenge includes an initial linear
> layer before the first round. We use a `(1, [1])` round skip adapted to this layer and interpolate
> the univariate polynomial `P1` corresponding to the first constrained output coordinate.
> …
> Instead of computing a resultant with the second constrained output polynomial, we apply
> Graeffe-based root finding to `P1`. Each root induces a candidate input, on which we evaluate the
> full permutation and check whether the second constrained output coordinate has the desired value.
> This avoids the memory cost of resultant computations while exploiting the FFT-friendly structure
> of the KoalaBear field.

Their Table 1, verbatim — all over KoalaBear on RTX 5090 GPUs, "est." rows extrapolated because the
execution logs were lost:

| instance | `R_F` | `R_P` | initial linear layer | round skip | GPUs | time (h) |
|---|---|---|---|---|---|---|
| CICO-2 | 6 | 8 | yes | `(1,[1])` | 96 | **7** |
| ZeroTest | 6 | 7 | no | `((3,2),[3])` | 4 | 10.45 |
| ZeroTest | 6 | 8 | no | `((3,2),[3])` | 4 | 49.65 |
| ZeroTest | 6 | 10 | no | `((3,2),[3])` | 28 | 64 (est.) |
| ZeroTest | 6 | 11 | no | `((3,2),[3])` | 28 | 192 (est.) |
| ZeroTest | 6 | 12 | no | `((3,2),[3])` | 28 | 575 (est.) |

Degrees. The `((3,2),[3])` skip gives an output degree bound of `3^(R_P+2)`; the `(1,[1])` skip used
for the challenge, which has the extra initial linear layer, gives `3^(R_P+5)`. So the registered
targets' univariate degrees are **`3^11`, `3^13` and `3^15`** — and §3.1 is why those numbers matter
more than anything else in this document.

The asymptotic cost of the root-finding stage is `Õ(M(δ) log p)` for `M` the cost of multiplying
degree-`δ` polynomials, "followed by evaluation of the second polynomial on the recovered roots. In
our implementation, this final evaluation step is negligible compared with polynomial construction
and root finding."

### 2.2 `R_P = 6` — a specialized resultant really did work

Bak–Hostettler, *A Better Bivariate Resultant Attack on Round-Reduced Poseidon* (2026/1905). They
adapt **Villard's** bivariate resultant algorithm, exploiting that the Poseidon resultant's degree
`D_I` is far below the generic `δ²` — the same structural fact §1's table encodes — to cut the
evaluation-point count. They skip one full round first.

Their Table 4, verbatim; `r_F`/`r_P` are the numbers of *skipped* full/partial rounds:

| problem | `R_F (r_F)` | `R_P (r_P)` | budget | time | source |
|---|---|---|---|---|---|
| CICO-2 | 6 (1) | 6 (0) | 128 CPU cores | **1 d 17 h** | this work |
| CICO-2 | 6 (1) | 7 (0) | 128 CPU cores | 21 d 5 h | this work |
| CICO-2 | 6 (1) | 8 (0) | 96 GPUs | 7 h | [SV26] |
| CICO-2 | 6 | 10 | — | *no public information yet* | — |
| ZeroTest | 6 (2) | 7 (2) | 4 GPUs | 10 h 27 m | [SV26] |
| ZeroTest | 6 (2) | 8 (2) | 4 GPUs | 2 d 2 h | [SV26] |
| ZeroTest | 6 (2) | 8 (0) | 128 CPU cores | 3 d 5 h | this work |
| ZeroTest | 6 (2) | 9 (1) | 128 CPU cores | 3 d 13 h | this work |

Their own comparison of the two routes is the sentence to keep: "our attack complexity grows in
`d^(2.66 R_F)` with the number of full rounds, whereas theirs grows in `d^(R_F)`. One of the main
practical limits of our attack compared to [SV26] is the lesser GPU-friendliness of our algorithm."

So the resultant route is worse in `R_F` and harder to parallelize, and the gap on CICO-2 in Table 4
is partly compute budget (96 GPUs against 128 CPU cores) and partly that only one full round can be
skipped there.

**Public implementation:** `PoseidonCicoTwo`. Single-threaded evaluation–interpolation, Villard
resultants and Gröbner comparisons, plus a multithreaded version using NTL, PML and CUDA. §6.3.

### 2.3 `R_P = 10` — undisclosed

2026/1905 records it as "no public information yet", and notes the site "reports CICO-2 attacks on up
to 10 rounds and ZeroTest attacks on up to 12 rounds, though the details of the attacks are not
public yet". The programme requires a technical report within a month of a claim but does not require
publication before **2027-01-01**, so a private report may already exist. Nothing should be recorded
about its method.

## 3. What this means for Zeebra, quantitatively

### 3.1 The univariate route fits inside what Zeebra already has

This is the central finding. The `R_P = 8` attack's working degree is `3^13 = 1 594 323`, so a Graeffe
step or polynomial product needs at least `2 δ + 1 = 3 188 647` points:

| target | `δ = 3^(R_P+5)` | NTT points needed | power-of-two | fits KoalaBear's `2^24`? |
|---|---|---|---|---|
| `R_P = 6` | `3^11` = 177 147 | 354 295 | `2^19` | **yes** |
| `R_P = 8` | `3^13` = 1 594 323 | 3 188 647 | `2^22` | **yes** |
| `R_P = 10` | `3^15` = 14 348 907 | 28 697 815 | `2^25` | no — needs mixed-radix (`2^24 · 127`) |

**Two of the three registered targets are inside Zeebra's existing power-of-two NTT ceiling.** The
previous version of this document said a mixed-radix FFT was mandatory for any of them; that was true
of the *resultant* route's `D_I = d^(2R_F+R_P)`, and is false for the univariate route's
`d^(R_F+R_P-1)`. Mixed-radix is needed only at `R_P = 10`, which is the undisclosed one.

Estimating one family's algebraic cost from D2's measured KoalaBear transform rate (~210 ns per
element at these sizes), where Graeffe root finding is about `log2 p = 31` steps of roughly one
FFT-multiply each:

| target | transform | one NTT multiply | Graeffe root find, one family |
|---|---|---|---|
| `R_P = 6` | `2^19` | 0.33 s | **~10 s** |
| `R_P = 8` | `2^22` | 2.64 s | **~1.4 min** |
| `R_P = 10` | `2^25` | 21 s | ~11 min |

Single-threaded, on this workstation, with the one piece of missing machinery supplied.

**And interpolation is not a gap here.** 2026/1254 builds `P1` by interpolation, and the points can be
chosen as a power-of-two multiplicative subgroup — which is exactly what `fft::interpolate` inverts,
and what #118 made as cheap as the forward transform. No subproduct tree is required for this route.
That removes item 5 of the previous version's gap list from the critical path.

### 3.2 But the search multiplicity, not one polynomial, is the cost

The per-family numbers above are not attack times, and the sources are emphatic about why.
2026/1254's closing caution: "A degree reduction alone is insufficient to assess an attack: the cost
of finding controls and satisfying the output constraints must also be included." Random sampling
would need "on the order of `p²` permutation evaluations… about `2^62` for the KoalaBear prime"; the
algebraic attack instead searches parametrized families, and "several families may be needed before
both output constraints are satisfied".

The ZeroTest `R_P = 8` row is the calibration: degree bound `3^10 = 59 049`, where one family's
Graeffe stage is sub-second, yet it took **49.65 hours on four GPUs**. Essentially all of that is
family count and control recovery. Their total-work model is explicit about it —
`W_total = W_pre + Σ_i (W_control,i + W_poly,i + W_root,i + W_check,i)` over `N` families.

So a Zeebra reproduction should target **one family end to end**, measured, and report the per-family
cost honestly rather than extrapolating an attack time. That is a well-defined, checkable deliverable.

## 4. Where Gröbner actually stands, measured

2026/1905 §5.2 runs all three methods on the same instances: KoalaBear (`p = 2^31 - 2^24 + 1`),
`t = 4`, `d = 3`, `R_F = 2`, **single-threaded**, on a 16-core Xeon 5218 with 128 GB. Gröbner is
Magma's `Variety`; the resultant methods use PML. `T` is time, `M` memory in GB, `Th.` the
theoretical `log2` complexity. Verbatim:

| `R_P` | GB `T` | GB `M` | GB `Th.` | Eval–Inter `T` | `M` | `Th.` | Villard `T` | `M` | `Th.` |
|---|---|---|---|---|---|---|---|---|---|
| 4 | **1 d 3 h** | 4.6 | 35 | **13 s** | 0.006 | 30 | **11 s** | 0.1 | 27 |
| 5 | — | | 40 | 3 m 39 s | 0.01 | 34 | 1 m 14 s | 0.46 | 31 |
| 6 | — | | 44 | 43 m 14 s | 0.017 | 37 | 7 m 25 s | 2.4 | 34 |
| 7 | — | | 48 | 8 h 05 m | 0.046 | 41 | 51 m 03 s | 10.8 | 37 |
| 8 | — | | 53 | 2 d 7 h | 0.22 | 44 | 5 h 18 m | 50 | 39 |

Their observation: "the Gröbner basis is the least competitive attack both in terms of time and
memory complexity, the highest number of rounds we were able to break being `R_F = 2`, `R_P = 4`.
This is consistent with the fact that its time complexity grows with `D_I^ω` and memory complexity
with `D_I²`."

**At `R_P = 4`, the only row all three reach, Gröbner takes 1 d 3 h where evaluation–interpolation
takes 13 s — about 7 500x — and it cannot reach `R_P = 5` at all.** Between the two resultant
methods, "Villard algorithm outperforms the time complexity of evaluation–interpolation as long as
`R_P ≥ 4`, and the gap between the two grows quickly with the number of rounds. On the other hand,
evaluation–interpolation uses much less memory."

This retracts the previous version's §4.1. It had leaned on 2025/950's remark that beyond a single
zero "the best known attack would involve multivariate polynomial solving" to argue the epic
overstated the threat to Zeebra's architecture. Measurements beat a remark: for CICO-2 the Gröbner
path is the uncompetitive one, and §1's table places Gröbner's best-known territory at `k ≥ 3`.

**What that does and does not say about Zeebra.** It does not say F4 or FGLM are wrong — they remain
the best known method for `k ≥ 3`, they are what the crate is, and the measured bottleneck inside the
Gröbner approach is the change-of-ordering step that M23 targets. It does say that **the registered
2026 CICO-2 targets are not a fair arena for Zeebra's architecture**, and that presenting progress on
them as progress against the best known attack would be wrong. Picking `k ≥ 3` instances, or being
explicit that the comparison is method-internal, is the honest framing.

## 5. The gap list, revised again

What Zeebra has, from [`fast-univariate.md`](fast-univariate.md) (#83) and
[`batch-inversion.md`](batch-inversion.md) (#118), both measured here: a two-adic root of unity over
every field in the crate including the wide ones; `evaluate` reaching `2^23` over KoalaBear in one
second; `interpolate` at the same cost since #118; Poseidon with the official constants; and
`roots.rs`, whose algorithm matches the published gcd-based one but at `O(log q · δ²)`.

For the **univariate/Graeffe route** of §2.1, separated into the one missing primitive and the
attack-specific work, because conflating them is what made the previous version of this section
overstate Zeebra's readiness:

**The missing polynomial-arithmetic primitive — one item.**

1. **NTT-based multiplication and squaring.** The only *foundational* gap. Graeffe is
   `f0(x)² - x·f1(x)²` by FFT, pointwise, invFFT — every piece exists except the wrapper. Schoolbook
   today, measured exponent 2.00. It is also the largest missing piece of the univariate layer D2
   measured, and a prerequisite for every other route here, which is why it is first regardless of
   what follows it.

**The attack, which does not exist in any form — three items.**

2. **The Graeffe transform and Graeffe-based root finding.** `roots.rs` implements the
   gcd/factorization route (`x^q - x mod f`, then gcd), which is a *different algorithm*, not a
   slower version of this one. Small on top of (1), but it is new code with its own correctness
   obligations.
3. **A round-skipping parametrization** for Poseidon with an initial linear layer — the `(1,[1])`
   skip of 2026/1254 §2.2. New mathematics for the crate.
4. **Family construction, candidate reconstruction and verification.** Building each family's `P1`,
   lifting a root of `P1` back to a full input, and checking the second output constraint.
   `CicoInstance::is_solution` covers the last step; the rest does not exist.

**Only for `R_P = 10`:** a mixed-radix FFT (§3.1). KoalaBear admits `2^24 · 127`.

Not needed by this route at all: subproduct trees (§3.1), half-gcd, Newton division, modular
composition.

So the honest sequencing is: item 1, then a *bounded* reproduction at small round counts with items
2–4 written against it, recording interpolation, Graeffe and verification costs separately. The
per-family figures in §3.1 are first-order extrapolations from Zeebra's measured transform
throughput, not validated whole-family runtimes, and nothing in §3.1 is an attack time (§3.2).

For the **resultant route**, additionally: Sylvester/Villard machinery, fast multipoint
evaluation–interpolation, and `gcd.rs` is plain Euclid where the literature uses half-gcd. §6.3
argues against building these.

### 5.1 The gap list, scored against the tree — every item has landed

Re-scored 2026-11-08. §5 above was written at `03b419f7` and calls item 1 "the only *foundational*
gap… a prerequisite for every other route here, which is why it is first regardless of what follows
it." Everything in the list, including that item, is now implemented, measured and tested. Each line
is settled by code or by a committed figure, **not** by an issue being closed.

| §5 item | state | what settles it |
|---|---|---|
| 1. NTT-based multiplication and squaring | **landed** | `src/fft/multiply.rs` — `multiply_over_domain`, `try_multiply_via_fft`, and a `multiply` dispatcher over a crossover measured per element width (#185). Reachability and the measured exponent below, because neither is what §5 assumed |
| 2. the Graeffe transform and Graeffe-based root finding | **landed** | `src/poly/univariate/graeffe.rs` — `graeffe_2`, `graeffe_l`, `graeffe_root`, `graeffe_all_roots`, with `deflation_agrees_with_the_gcd_finder_on_random_polynomials` as the differential oracle. Still a *different algorithm* from `roots.rs`, as §5 required rather than hoped: `roots.rs` carries no reference to it, and `graeffe.rs` calls `roots` only to finish inside the small odd subgroup |
| 3. a round-skipping parametrization for the initial linear layer | **landed, #209** | `src/grobner/research/univariate_cico.rs` — `parametrize` and `CicoFamily`, the `(1,[1])` skip derived for Zeebra's hybrid `permutation_plus_linear` in [`graeffe-root-finding.md`](graeffe-root-finding.md) §9.5.2 |
| 4. family construction, candidate reconstruction and verification | **landed, #209 and #210** | the same file — `cico_univariate_family` and `CicoFamily::lift`, with both invariants asserted (`the_family_holds_the_input_constraints_at_every_point`, `the_family_polynomial_agrees_with_the_permutation`); `examples/graeffe_cico.rs` runs parametrization through verification and §9.6 measures it over **17 838 families** |
| "only for `R_P = 10`: a mixed-radix FFT" | **landed, and already stale when written** | `src/fft/prime_factor.rs`'s `transform_any` is the *sole* transform path for `evaluate` and `interpolate`: power-of-two → radix-2, coprime → Good–Thomas, prime power → Bluestein above a measured crossover (#125, #375). `2^24 · 127` over KoalaBear splits as `(2^24, 127)` |
| "not needed by this route at all: subproduct trees" | landed anyway, and load-bearing elsewhere | `src/poly/univariate/subproduct_tree.rs` (#162). [`resultant-elimination.md`](resultant-elimination.md) §6.1 credits #162's interpolation, not the subgroup route, with the resultant's four-round rows |

**Item 1 is closed for the route it was blocking, and two narrower things are true in its place.**

- **The transform is not reachable from the operator, and will not become so.** `&a * &b` dispatches
  to `multiply_dense` — schoolbook below the Karatsuba base case, Karatsuba above (#231). The reason
  is a type bound, not an omission: a domain needs `KnownOrder` and a source of randomness, neither
  of which `Mul`'s signature can carry, and the Gröbner core deliberately does not require
  `KnownOrder` of a coefficient type — `test_the_grobner_stack_needs_no_field_cardinality` fails to
  compile if it starts to. So everything built on the operator (`pow_mod`, `lcm`, `from_zeros`,
  `Polynomial::pow`, `compose`, `shift`) tops out at Karatsuba. This is **not** #375's pattern of a
  standalone entry point nothing dispatches to; it is a dispatcher that `Mul` is the wrong signature
  to host.
- **The dispatcher has no in-crate callers, and the consumer it was built for reaches past it.**
  `fft::multiply` is public API exercised by its tests and `examples/multiplication_dispatch.rs`.
  `multiply_over_domain` has exactly one real caller in `src/` — `graeffe.rs`, building one domain
  and reusing it across a subproduct-tree level. That is the right shape here, since the domain is
  the expensive part, and it is why the Graeffe route is not subject to `try_multiply_via_fft`'s
  `next_power_of_two`, which does inherit the two-adicity ceiling rather than the smooth-part one.

**The measured exponent, since §5's "Schoolbook today, measured exponent 2.00" is now three separate
numbers.** From [`fast-univariate.md`](fast-univariate.md)'s stage table and its re-take after #189:
the **transform** route measures **1.03 – 1.27** from `n = 256` up, reaching operand `2^22` in
1.60 s over KoalaBear in a `u64`; **Karatsuba** measures **1.584 – 1.613** by least squares over
`2^9`…`2^14` against `log2 3 = 1.585`; and the **2.00 is still in the tree as a deliberate quadratic
control** — `examples/univariate_scaling.rs`'s `mul` row calls `karatsuba_unstable(.., usize::MAX)`,
a base case the recursion never passes, precisely so that the baseline every crossover is quoted
against did not drift to 1.59 when #231 moved the operator. §5's 2.00 is therefore no longer a
description of what multiplication does.

`2^22` is the transform size §3.1's `R_P = 8` row needs, where §3.1 estimated 2.64 s for one NTT
multiply from a per-element rate. **The 1.60 s is not that quantity** — operand rather than transform
size, and KoalaBear in a `u64` rather than the 4-byte one — so it corroborates §3.1's order of
magnitude and does not replace its extrapolation. No exponent sweep of `fft::multiply`'s *dispatched*
path exists; §4.1.2 of `fast-univariate.md` measures the dispatcher as ratios and crossover brackets
instead.

**What is genuinely still open on this route, none of it foundational:**

1. The Bluestein dispatch is **wired but dormant.** It fires only for a domain carrying a prepared
   convolution domain, and `with_bluestein` has no non-test caller in `src/`. An unprepared domain
   takes the quadratic `dft` on its prime-power factors, giving up the 3.55x `prime_factor.rs`
   records for KoalaBear's 127.
2. `with_bluestein` cannot be used at `size = 2^24 · 127` over KoalaBear at all — the convolution
   length comes out `2^32` against a two-adicity of 24. The 127 axis reaches Bluestein only through a
   factor-sized `bluestein_convolution_domain(127, ..)` attached by hand. Unverified whether any
   caller wants that today; no code path asks for a `2^24 · 127` domain.
3. **The memory-access hypothesis was never tested.** 2025/950's 4/3-power FFT lower bound is half of
   #68's own framing of this regime — "reportedly bound by memory *access* rather than arithmetic" —
   and `examples/ntt_access.rs`, specified in [`graeffe-root-finding.md`](graeffe-root-finding.md)
   §6.3 and listed as row 2 of its §10 plan, does not exist. Filed as #591.

## 6. Per-child recommendation

### 6.1 D3 (#84) — promote to first

It is the route that solved `R_P = 8`, its one missing *primitive* is the NTT multiply (§5), two of
three registered targets sit inside Zeebra's existing transform ceiling, and its memory profile is
modest by construction — the whole point of the strategy is that it "avoids the memory cost of resultant
computations". Deliverable: **one family, end to end, measured** — build `P1` by interpolation over a
power-of-two subgroup, Graeffe root finding, evaluate candidates against the second constraint.
`ZSVD25` (2025/1916) is the machinery reference; 2026/1254 §4.2 is the recipe.

### 6.2 D1 (#82) — recast as a benchmark, not a build

Its structural question is answered, with the strength of the answer stated carefully in §1.1, and
both 2026/150 and 2026/1905 exploit `D_I ≪ δ²` as the thing that makes the attack work. Zeebra has no
Sylvester construction, no subresultants and no Poseidon2, and §4 shows the resultant route is
GPU-unfriendly and worse in `R_F`. Building it to find out is not warranted.

### 6.3 D4 (#85) — use the public implementation

`PoseidonCicoTwo` contains single-threaded evaluation–interpolation, Villard, *and* Gröbner
comparisons. That is the head-to-head instrument D4 was created to build, already written by the
authors of the attack, with the measurements in §4 to check a local run against. D4 becomes: run it
on a small instance, run Zeebra's F4/FGLM on the same instance, and report both — which also tests
Zeebra against Magma's `Variety` indirectly. Far cheaper and more credible than a from-scratch
resultant.

The earlier note that D4 must change instance still holds for any comparison against *published*
timings — 2026/150's figures are Poseidon2 and the crate has no Poseidon2 — but 2026/1905's
experiments are on **Poseidon1** (§5.3: "Both challenges are on Poseidon1"), so its Table 3 instances
at `t = 4`, `d = 3`, `R_F = 2` are directly reproducible by Zeebra.

### 6.4 The scoreboard should record method separately from verification

`challenge.rs` records each official target's external status and verification date. It should also
record **what method was publicly disclosed**, as a field distinct from the EF verification, because
the two are not known to coincide: the papers establish attacks at these parameters, while the site
does not name first submitters. A `method_disclosed` field with `R_P = 10` set to *unknown* — not
`resultant`, not `brute_force` — is the accurate state. The published results also belong in the
scoreboard as **method-specific reference rows** (§2's table), so a Zeebra measurement can be
compared against a named method rather than against "somebody solved this".

### 6.5 Deployed parameters

Unchanged and worth restating: both earlier extrapolations put these attacks worse than brute force
at real security levels, and 2025/950 estimates the 128-bit Poseidon-256 instance at `2^198`
SHA-256 permutations. The significance of this whole direction is against reduced-round bounty
instances and against Gröbner-derived security estimates, not against deployed parameters.

## 7. Acceptance criteria, scored

- [x] "D1 and D3 each state, for one concrete published instance, what the method computes and what
      it would cost in Zeebra." D1: §2.2 and §6.2. D3: §2.1 and §3.1, with per-family costs.
- [ ] "D4 produces a measured comparison on a problem solvable both ways." Now cheap (§6.3) but not
      done. **Nothing in this document is a Zeebra measurement of either attack.**
- [ ] "The epic closes with a written recommendation, including the option of declining." §0 is a
      recommendation, and no longer a declining one — but it is not a closure, because every number
      about the attacks is somebody else's.

**#68 stays open.** The single step that moves it furthest is §5 item 1, NTT-based multiplication:
it unlocks the Graeffe route, it is independently the largest missing piece of the univariate layer
D2 measured, and it is a prerequisite for every other item here.

### 7.1 Re-scored: all three criteria are met, and #68 closes

Re-scored 2026-11-08. §7 directs that #68 stay open on one reason — "every number about the attacks
is somebody else's" — and **that reason stopped being true the day after §7 was written**. The
instrument it nominated was not the one that settled it: §6.3 recommended running Bak–Hostettler's
`PoseidonCicoTwo` against Zeebra's F4, and that external head-to-head was never done. M23-E built
Zeebra's own resultant instead and measured it against Zeebra's own F4, which is a stronger answer to
the same question.

- [x] "D1 and D3 each state, for one concrete published instance, what the method computes and what
      it would cost in Zeebra." Unchanged: D1 in §2.2 and §6.2, D3 in §2.1 and §3.1.
- [x] "**D4 produces a measured comparison on a problem solvable both ways.**"
      [`resultant-elimination.md`](resultant-elimination.md) §2, on
      `poseidon31-cico-t16-rf2-rp0` at `slice(12 fixed, seed 1)` — two rounds, challenge digest
      `56ccc99d85e0…` on both sides: **F4/FGLM 30 142 ms against a resultant total of 52.2 ms,
      578x**, and the resultant returns all three base-field witnesses where F4's search returns the
      first one it finds. Both outcomes are `verified_witness`, both checked by running
      `permutation_plus_linear` through `CicoInstance::is_solution`; nothing in the resultant code
      decides that a candidate is a solution. Both sides are committed scoreboard run records, not
      only prose. §5 there revises the factor to 4 306x on a later resultant run.
- [x] "The epic closes with a written recommendation, including the option of declining." §0 is the
      recommendation and §0.1 its current state. The direction is **accepted**. What makes that not a
      decline is a Zeebra measurement rather than a complexity estimate, which is the thing §7 was
      holding out for.

**Four things the closure carries, or it overstates itself.**

1. **One row, two rounds.** `rf2-rp0` is the *only* instance both methods completed, and two rounds
   is as far as F4 reaches on these slices. The resultant reaches four
   ([`resultant-elimination.md`](resultant-elimination.md) §6.1) and six
   ([`MILESTONE-PUBLISHED-ATTACK-REPRODUCTION.md`](../MILESTONE-PUBLISHED-ATTACK-REPRODUCTION.md)
   §7.8 — witness `x = 941710918, y = 475196876`, verified through the permutation), but F4 is not
   there to be compared against: on every other registered row it is `stopped_at_limit`, and its
   runs there are on slice seed 0 rather than seed 1, so those pairings are not even the same
   instance. A result at two rounds does not extrapolate to ten, which is what #85 required be said.
2. **The two factors are not equally clean.** The **578x** is machine-matched — both sides on fedora,
   8 logical cores, affinity 0–7, concurrency 1 — but across commits (`7e333fb` against `744fdf9`).
   The **4 306x** in §5 there is **cross-machine**: the 30 142 ms F4 figure is the 8-core box and the
   later resultant figure is the 128-core workstation. The machine-matched number is the one to
   quote; the larger one is a resultant improvement measured elsewhere, not a widened comparison.
3. **The criterion is met by the resultant route, not by the one §0 ranked first.** The
   univariate/Graeffe route has no head-to-head against F4 and **cannot get one on any reduction** —
   [`graeffe-root-finding.md`](graeffe-root-finding.md) §9.6.3 is the finding, not the gap: families
   per witness is `≈ p / (roots per family)`, `p` is fixed by the field, and cutting `R_F` and `R_P`
   cuts the per-family cost while leaving the family count at `2^31`. `δ` spans 6 561x across the
   ladder and the mean root count does not move off 1.0 (0.9997 pooled over 17 838 families), so no
   `k = 2` row produces a witness and none was expected. The three witnesses that exist are on the
   `k = 1` planted row, where F4 itself stops at `max_matrix_columns`. That is an argument rather than
   an omission — but it is an asymmetry in the evidence, and §0's ranking of the routes rests on
   published figures where the resultant's rests on Zeebra's own.
4. **The result is about the formulation, not the engine.**
   [`resultant-elimination.md`](resultant-elimination.md) §7: three orders of magnitude separate two
   ways of writing the same CICO slice, and the expensive one is the one the literature uses by
   default because it bounds the degree. F4 pays 32 variables to hold the degree at 3; the resultant
   pays degree `3^rounds` to hold the variables at two. Neither #179's 17.96x nor #227's 92–95%
   scaling moved a frontier on its own — §13.1 of the M24 milestone records that explicitly. Nothing
   here says F4 or FGLM are wrong; §4 and §1's table still put Gröbner's best-known territory at
   `k ≥ 3`, and every registered target is `k = 2`.

**The epic's residue, filed rather than left as prose.** Three items of #68's own scope had no issue
and now do: **#591** the memory-access hypothesis (§5.1 item 3), **#593** `graeffe_root` over a field
with a large odd part, **#594** scoreboard records for §9.6's family economics. Already tracked
elsewhere: #194 (half-GCD), #297 (a structured Sylvester determinant — the one axis left with an
asymptotic improvement in it), #367 and #371 (M26, still *planned*).

## 8. Sources and verification status

#68 and #82 require that figures be read out of the document and that search-engine summaries are not
citable. All six are read, as of 2026-11-05. The ePrint PDFs 403 from this environment; copies were
supplied locally and extracted with `pdftotext`.

| source | status | cited here |
|---|---|---|
| **2026/1254** Sanso–Vitto, *Top Gun: Degree Annihilation Attacks on Poseidon* | read; §2.2, §4.2 and Table 1 re-read from the PDF for #208 in `graeffe-root-finding.md` §9.5 | §2.1, §3.1, §3.2, §6.1 |
| **2026/1905** Bak–Hostettler, *A Better Bivariate Resultant Attack on Round-Reduced Poseidon* | read | §1, §2.2, §2.3, §4, §6.2, §6.3 |
| **2025/1916** Zhao–Sanso–Vitto–Ding, *Graeffe-Based Attacks on Poseidon and NTT Lower Bounds* | read | named as the Graeffe machinery reference, §6.1 |
| **2025/950** Zhao–Ding, *Breaking Poseidon Challenges with Graeffe Transforms…* | read | the FFT 4/3-power memory-access lower bound; its CICO-1 scope and its remark on >1 zero, now superseded by §4 |
| **2026/150** Bak–Bariant–Jazeron et al., *Ethereum Poseidon bounties* | read | the 2025 round's resultant attacks and the streaming-memory argument |
| Jazeron, *Solving CICO-2 bounty instances of Poseidon*, 15 Mar 2025 | read — fetched directly | the 2025 round's instance table and results |
| [BSGL20] Thm 10 and [BBB+25] on `D_I` | **read**, 2026-11-06 — this row previously said "not read", which §1.1 has contradicted since `8b343139` | §1.1, which resolves the discrepancy as a citation error rather than recording it |
| `PoseidonCicoTwo` implementation | **not inspected**, and no longer load-bearing — existence and contents per 2026/1905 and the user's check | §2.2, §6.3 |

**One item remains unread, and it stopped mattering.** `PoseidonCicoTwo` was load-bearing only for
§6.3's recommendation to benchmark it rather than build a resultant, and §0.1 records that
recommendation as **reversed**: M24 built the resultant and measured it against Zeebra's own F4, so
D4 was settled without the external instrument. Reading it would now be a cross-check on a
comparison that already exists, not a prerequisite for one.

The `D_I` results, which were the genuinely load-bearing unread item — every cost figure here depends
on `D_I` — were read on 2026-11-06 and §1.1 is the resolution.
