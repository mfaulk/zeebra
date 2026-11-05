# Elimination beyond Gröbner bases: a feasibility assessment

Reference for #68. A decision record in the style of #58 — the question answered once with the
measurements attached — covering D1 (#82), D2 (#83), D3 (#84) and D4 (#85).

**#68's deliverable is an assessment, not an implementation, and nothing was implemented for it.**

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

## 0. Recommendation

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

### 1.1 What is proven about `D_I`, and what is not

Every cost figure in this document depends on the ideal degree `D_I`, so the strength of that claim
matters. The two papers word it differently, cite different results for it, and **neither primary
source has been read here**:

| claim | strength | as cited by |
|---|---|---|
| `D_I ≤ d^(k·R_F+R_P)` | a proven **upper bound** | 2026/1905, citing [BBB+25]: "a proof that the degree `D_I` … is **upper bounded by** `d^(kR_F+R_P)`" |
| `D_I = d^(c·R_F+R_P)` | stated as an **equality** | 2026/150 §4.3, citing [BSGL20, Theorem 10]: "have a degree of the ideal **equal to**" |
| `deg Res = D_I` for CICO-2 Poseidon | an **experimental observation** | 2026/150 §4.3: "We also experimentally observed that…" |

So the firm result is an upper bound; the equality is asserted in one source against a different
citation, and the resultant attaining it is an observation on the instances studied. §2 and §3 use
the equality, which is what the sources' own cost models use — but that makes every degree and every
derived cost in this document **an upper bound on a particular instance's**, not a prediction of it.
For a feasibility assessment that is the conservative direction, so no conclusion here flips if only
the bound holds. Any claim that a *specific* instance's resultant has exactly this degree would need
[BBB+25] and [BSGL20] read, and ideally a degree measured on a small instance.

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

## 8. Sources and verification status

#68 and #82 require that figures be read out of the document and that search-engine summaries are not
citable. All six are read, as of 2026-11-05. The ePrint PDFs 403 from this environment; copies were
supplied locally and extracted with `pdftotext`.

| source | status | cited here |
|---|---|---|
| **2026/1254** Sanso–Vitto, *Top Gun: Degree Annihilation Attacks on Poseidon* | read | §2.1, §3.1, §3.2, §6.1 |
| **2026/1905** Bak–Hostettler, *A Better Bivariate Resultant Attack on Round-Reduced Poseidon* | read | §1, §2.2, §2.3, §4, §6.2, §6.3 |
| **2025/1916** Zhao–Sanso–Vitto–Ding, *Graeffe-Based Attacks on Poseidon and NTT Lower Bounds* | read | named as the Graeffe machinery reference, §6.1 |
| **2025/950** Zhao–Ding, *Breaking Poseidon Challenges with Graeffe Transforms…* | read | the FFT 4/3-power memory-access lower bound; its CICO-1 scope and its remark on >1 zero, now superseded by §4 |
| **2026/150** Bak–Bariant–Jazeron et al., *Ethereum Poseidon bounties* | read | the 2025 round's resultant attacks and the streaming-memory argument |
| Jazeron, *Solving CICO-2 bounty instances of Poseidon*, 15 Mar 2025 | read — fetched directly | the 2025 round's instance table and results |
| [BSGL20] Thm 10 and [BBB+25] on `D_I` | **not read** — only as 2026/150 and 2026/1905 cite them, and they cite *different* results with *different* strengths | §1.1, which records the discrepancy rather than resolving it |
| `PoseidonCicoTwo` implementation | **not inspected** — existence and contents per 2026/1905 and the user's check | §2.2, §6.3 |

The two items not read are the results bounding `D_I` and the public implementation. Both are
load-bearing — `D_I` for every cost figure here, the implementation for §6.3's recommendation — and
should be read before anything stronger than §1.1's upper-bound reading is claimed.
