# Elimination beyond Gröbner bases: a feasibility assessment

Reference for #68. A decision record in the style of #58 — the question answered once with the
measurements attached — covering D1 (#82), D2 (#83), D3 (#84) and D4 (#85).

**#68's deliverable is an assessment, not an implementation, and nothing was implemented for it.**
What changed since the epic was written is that D2 landed, and that all three primary sources became
readable: the two ePrint PDFs are HTTP 403 from this environment, but copies were supplied, and
Jazeron's slide deck is not on ePrint at all. §8 records the status of each.

> **Correction.** The first draft of this document declined the resultant route for Zeebra's
> registered targets on a memory figure of 824 TB. **That figure was wrong.** It modelled `δ · D_I`
> as a resident working set; `δ · D_I` is the *operation count*, and both 2026/150 and 2024/886
> describe a streaming evaluation–interpolation form whose memory is `O(D_I)` — 1.55 GB, not 824 TB,
> for the same target. The conclusion changes with it: memory is not the constraint on any of the
> three registered targets. Time is, and it binds on two of the three rather than all three. §3.

## 0. Recommendation

1. **Do not decline the direction, and do not pursue it at the top.** Of the three registered 2026
   CICO-2 targets, `R_P = 6` needs about **2^47.5 field operations and 1.55 GB** streaming — days to
   weeks of wall clock. `R_P = 8` is 2 years and `R_P = 10` is 158 years, scaled from the published
   implementation's own measured rate. Declining those two is safe; declining `R_P = 6` is not. §3.2.
2. **The attack shape for Zeebra's registered targets composes both children**, rather than choosing
   between them: the resultant (D1) eliminates a CICO-2 system to one variable, and Graeffe-based
   root finding (D3) is the fast way to finish. 2025/950's own caveat is that its interpolation
   attack applies "only when a single zero is required in both the input and output", i.e. CICO-1 —
   and every registered target is CICO-2. So D3 is not a substitute for D1 here. §6.
3. **Build the univariate layer in this order**, which is also the order of decreasing certainty:
   NTT-based multiplication and squaring → **mixed-radix (non-power-of-two) FFT** → Newton division →
   half-gcd. The Graeffe route needs only the first two; the gcd-based root finder needs all four.
   §5.
4. **Zeebra's own architecture is less challenged than the epic assumed.** 2025/950 states that once
   more than a single zero is required, "the best known attack would involve multivariate polynomial
   solving, where the main bottleneck is linear algebra over finite fields" — which is what Zeebra
   is. That is a reason to finish the F4/FGLM path, not to abandon it. §4.1.
5. **D4 must use a Poseidon instance from Zeebra's own frozen ladder**, because every published
   CICO-2 figure is Poseidon2 and the crate has no Poseidon2. §6.3.

#68's own go/no-go — "decline the direction if D4 shows the resultant path is not competitive" — is
still not answerable. §7 scores each acceptance criterion.

## 1. What the published work actually does

Two distinct lines, on the **November 2024** Ethereum Foundation bounty programme. Neither is the
2026 programme whose targets Zeebra has registered; §3.2 says what carries over.

### 1.1 Resultants for CICO-2 — Bak, Bariant, Jazeron et al.

Sources: eprint **2026/150** (read) and Jazeron's deck *Solving CICO-2 bounty instances of Poseidon*,
15 March 2025 (read). The instances:

| instance | base primitive | CICO branches | field | t | d | `(R_F, R_P)` attacked |
|---|---|---|---|---|---|---|
| Poseidon2-31k | Poseidon2 | 2 | KoalaBear (31) | 16 | 3 | (4,1), (4,3), (6,4) |
| Poseidon2-31m | Poseidon2 | 2 | Mersenne (31) | 16 | 5 | (4,0), (4,1), (6,1) |
| Poseidon-256 | Poseidon | 1 | BLS12-381 (255) | 3 | 5 | (6,8), (6,9) |
| Poseidon2-64 | Poseidon2 | 1 | Goldilocks (64) | 8 | 7 | **none — "we did not manage to attack any"** |

Resultants are used for **CICO-2 only**; "for CICO-1, we used already known techniques".

**Their root-finding algorithm is the one Zeebra already has.** The deck states it as: compute
`X^q - X mod P` by double-and-add, take `G = gcd(P, Q)`, recover the roots of `G`, which "will have
degree one or two with high probability". That is `src/poly/univariate/roots.rs` line for line.
Theirs is `Õ(δ log q)` — "First step: `Õ(δ log(q))`. Second step, using the half-gcd algorithm:
`Õ(δ)`." Zeebra's is `O(log q · δ²)`, measured. **The difference is entirely in the subroutines.**

### 1.2 Graeffe transforms for CICO-1 — Zhao and Ding

Source: eprint **2025/950** (read), *Breaking Poseidon Challenges with Graeffe Transforms and
Complexity Analysis by FFT Lower Bounds*. They solved the previously unsolved 24-, 28- and 32-bit
**Poseidon-64** (Goldilocks, `t = 8`, `x^7`, Poseidon2 linear layer) challenges, at polynomial
degrees `7^12`, `7^13` and `7^15` after the Skip First Rounds Trick.

The algorithm is strikingly cheap in primitives. From §4.1: the Graeffe transform of
`f(x) = f0(x²) + x·f1(x²)` is computed as `f0(x)² - x·f1(x)²`, "by first applying the FFT to both
`f0(x)` and `f1(x)`, then doing pointwise operations, and finally applying the invFFT to obtain the
result. Thus, FFT and invFFT are the most time-consuming parts of our implementation."

**So the Graeffe route needs forward FFT, inverse FFT and pointwise multiplication, and nothing
else** — no half-gcd, no Newton division, no subproduct tree. Zeebra has `evaluate` and
`interpolate` over every field in the crate, and after #118 the inverse transform costs what the
forward one does. §5.

Their own comparison, verbatim (Table 3; **times are `log2` seconds**, `[7]` is the gcd-based
predecessor, estimated from its published fitting curve):

| degree | time | memory | time `[7]` | memory `[7]` |
|---|---|---|---|---|
| `7^12` | `2^8.56` s (6.3 min) | 0.32 TB | `2^21.81` s | 6.1 TB |
| `7^13` | `2^11.38` s (44 min) | 1.8 TB | `2^24.83` s | 41 TB |
| `7^15` | `2^18.35` s (93 h) † | 90 TB | `2^30.88` s | 1.9 PB |

† "Data swapped to disk."

## 2. The structural claim: mostly proven, partly observed

D1 was created to verify that Poseidon-style structure collapses the resultant's degree below the
generic product bound, and hoped for "a cheap and decisive negative result" if it does not. It does
not — and the claim is better established than the epic assumed. From 2026/150 §4.3:

> It has been shown [BSGL20, Theorem 10] that the systems for a CICO-c problem on Poseidon have a
> degree of the ideal equal to `D_I = d^(c·R_F + R_P)`. We also experimentally observed that, in the
> case of the CICO-2 problem on Poseidon, the bivariate resultant has (univariate) degree equal to
> the degree of the ideal, `D_I`. Skipping one round using the trick from the previous section gives
> a bivariate system of ideal degree `D_I = d^(2(R_F-1) + R_P)`.

So the **ideal degree is a theorem**, not an observation; what is experimental is that the
*resultant's* degree attains it. Against the generic bound `d^(2R_F + 2R_P)` the structure saves a
factor `d^(R_P)`, and the deck's reading is explicit: "Hints that partial rounds are not as strong as
full rounds to prevent algebraic attacks."

The arithmetic checks against their own table: for Poseidon2-31k (6,4), `δ = 3^10` and `D_I = 3^16`
give `log2(δ · D_I) = 41.2` against their stated complexity estimate of 43.

**Consequence for D1:** the question it was created to answer is answered, and the cheap negative it
hoped for is unavailable. Independent verification on a small instance is still worth doing as
confirmation, but it is no longer the deciding question.

## 3. What it costs, correctly separated into time and memory

### 3.1 The two are not the same quantity, and the first draft conflated them

The resultant approach's **time** is `Õ(δ · D_I)` (2026/150 §4.4). Its **memory** depends entirely on
which algorithm computes the resultant:

- **Dense bivariate resultant.** 2026/150: it "requires storing bivariate polynomials of total
  (multivariate) degree δ, making the memory scale quadratically with δ". 2024/886 §2.2 puts it more
  bluntly — the degree "may become extremely high, which introduces unaffordable memory consumption
  in practical attacks".
- **Streaming evaluation–interpolation.** 2024/886's answer to exactly that problem: "we propose to
  use Lagrange interpolation to compute `R(f, g, y)`, which also enables parallelization… an upper
  bound on the degree of `x` in `R(f, g, y)` can always be estimated in advance." Assign values to
  one variable, compute a scalar resultant at each, interpolate. The evaluation points are
  independent, so the resident set is the `O(D_I)` output plus `O(δ)` of working space — **and the
  work parallelizes**.

The published 10 TB figure below is the first form, in PML. It is a property of that implementation,
**not a lower bound of the method** — which the same paper demonstrates by falling back to a
different algorithm when memory ran out: "We only used the GCD approach for the third Mersenne
instance as the required memory complexity for the resultant approach was too high."

Their results, verbatim from 2026/150 Table 2 and the deck. Complexity estimates are `log2`; bold
marks where they beat the EF claim.

| instance | `R_F` | `R_P` | EF estimate | their estimate | practical time | memory |
|---|---|---|---|---|---|---|
| Poseidon2-31k CICO-2 | 4 | 1 | 32 | 19.6 | 0.11 s | 6 MB |
| | 4 | 3 | 41 | 30.6 | 1.55 s | 611 MB |
| | 6 | 4 | 45 | 43 | **2.6 h** | **10 TB** |
| Poseidon2-31m CICO-2 | 4 | 0 | 37 | 18.8 | 0.31 s | 41 MB |
| | 4 | 1 | 40 | 26.8 | 4.01 s | 1 GB |
| | 6 | 1 | 45 | 37.5 | 40 h | 5.4 GB |
| Poseidon-256 CICO-1 | 6 | 8 | 31 | 43.1 | 8 h (not the first solution) | 250 GB |
| | 6 | 9 | 36 | 45.6 | 8.5 d | 1.3 TB |

Hardware, verbatim: "AMD EPYC 9354 with 1To of RAM, 12To of NVMe swap memory and 120 threads", one
instance on "1000 cores of Intel Xeon 5218". Software: **NTL** for polynomial arithmetic, **PML** for
the interpolation–evaluation resultant. Their resultant algorithm is `Õ(δ³)`; they note Villard's
`Õ(δ^(2+ε))` exists but "is not implemented in the finite field polynomial libraries (NTL, Flint,
…)".

### 3.2 Zeebra's registered 2026 targets

`src/grobner/research/challenge.rs` registers three official 2026 CICO targets: **Poseidon** (not
Poseidon2), KoalaBear, `alpha = 3`, `t = 16`, `k = 2`, `R_F = 6`, `R_P ∈ {6, 8, 10}`. Applying
`D_I = d^(2R_F + R_P)` and `δ = d^(R_F + R_P)`, with wall clock scaled from the published
`(6,4)` run — 2.6 h at `2^41.2` operations on 120 threads:

| target | `δ` | `D_I` | operations | scaled time | streaming memory |
|---|---|---|---|---|---|
| `R_P = 6` | `3^12` = 531 441 | `3^18` = 387 420 489 | `2^47.5` | **~9 days** | **1.55 GB** |
| `R_P = 8` | `3^14` = 4 782 969 | `3^20` = 3 486 784 401 | `2^53.9` | ~2 years | 13.9 GB |
| `R_P = 10` | `3^16` = 43 046 721 | `3^22` = 31 381 059 609 | `2^60.2` | ~158 years | 126 GB |

**Memory is comfortable on all three** — this workstation has 300 GB. **Time binds, on two of the
three.** That is the corrected conclusion, and it is the opposite of the first draft's.

Three caveats, stated rather than buried. The degree formula is proven for **Poseidon** (BSGL20) and
the resultant-attains-it observation was made for Poseidon, so it does carry to the registered
targets — but the published *timings* are Poseidon2 and the linear layers differ. The scaling assumes
the published implementation's rate holds across a `2^6`–`2^19` range of operation counts, which is a
long extrapolation. And the 2026 programme is **finished with all three solved externally** (registry:
`R_P = 6` verified 2026-04-10, `R_P = 8` 2026-05-06, `R_P = 10` 2026-07-06), so all three are
feasible for somebody; the `R_P = 10` row above says it was not this method on one machine.

### 3.3 The transform ceiling: smoothness, not two-adicity

A product or Graeffe step at degree `D` needs a transform of at least `2D + 1` points whose size
divides `q - 1`. The relevant quantity is therefore the **smooth part** of `q - 1`, not the
two-adicity alone — and D2 recorded the two-adicity because Zeebra's FFT is power-of-two only ("the
simplest case, assumed here, is when the size is a power of 2", `src/fft/domain.rs`).

| target | `D_I` | points needed | power-of-two | KoalaBear, `q-1 = 2^24 · 127` |
|---|---|---|---|---|
| `R_P = 6` | `3^18` | 7.75e8 | `2^30` — above KoalaBear's `2^24` | **fits**: `2^24 · 127` = 2.13e9 |
| `R_P = 8` | `3^20` | 7.0e9 | `2^33` | does not fit |
| `R_P = 10` | `3^22` | 6.3e10 | `2^36` | does not fit |

So the one registered target that time allows is **also** the one the field can host a transform
for — but only with a **mixed-radix** FFT, which the crate does not have. With power-of-two
transforms alone, KoalaBear stops at `2^24` and none of the three is reachable. This is why
mixed-radix FFT is item 2 of §5 rather than a footnote.

Goldilocks is the instructive contrast: `q - 1 = 2^32 · 3 · 5 · 17 · 257 · 65537`, which is why
2025/950 chose it and why they say their code "can be easily adapted to other 64-bit moduli where
`p - 1` is sufficiently smooth".

## 4. Where Zeebra actually stands

From [`fast-univariate.md`](fast-univariate.md) (D2, #83) and
[`batch-inversion.md`](batch-inversion.md) (#118), both measured here:

- **The wide-field NTT blocker is cleared.** `root_of_unity` was `unimplemented!()` for
  `PrimeFieldElement256`; the two-adic construction landed. #68 named this as D2's first task and a
  blocker on D3's experimental half. Done.
- **The transforms are healthy.** `evaluate` reaches `2^23` over a 31-bit field in one second, and
  after #118 `interpolate` costs the same as `evaluate` to within 2–10%.
- **Root finding is the binding stage** at `O(log q · δ²)`: degree 4 096 in 1.72 s over KoalaBear,
  measured exponent 1.93.
- **Memory is not the constraint anywhere Zeebra can reach.** Every stage is linear in degree at a
  small constant; root finding peaks at `12 n B`.

On the published premise: #68 says the regime is "bound by memory *access* rather than arithmetic".
2025/950 establishes that as more than a report — Theorem 1 proves that FFT data movement costs at
least the 4/3 power of input size "regardless of how it is realized in our three-dimensional world",
from the physical facts that moving information costs distance and that information density is
finite. They then model root finding the same way, and conclude "the pseudo-linear arithmetic cost
will ultimately become negligible" with the crossover "well below `7^15`". Their implementation is
bandwidth-bound by design: "the performance is mainly determined by memory bandwidth rather than
compute throughput", after "almost no low-level optimization".

**Zeebra is not yet in that regime**, and that is the thing to be clear about. Its barrier is the
absence of sub-quadratic multiplication; its memory is comfortable precisely because its degrees are
small. The two statements describe different points on one curve.

### 4.1 The epic's framing of the threat to Zeebra needs softening

#68 opens by calling this "a direct challenge to Zeebra's architecture". 2025/950 §4.2 says the
opposite for anything beyond a single zero:

> It is crucial to remark that this estimation applies only when a single zero is required in both
> the input and output of the sponge permutation. Otherwise, the best known attack would involve
> multivariate polynomial solving, where the main bottleneck is linear algebra over finite fields
> and memory cost is less relevant. Therefore, it may be preferable to choose a large underlying
> field so that interpolation is the best known attack when parameterizing Poseidon hash functions.

Every registered target is CICO-2. So on Zeebra's own corpus the authors of the fastest published
interpolation attack name **multivariate polynomial solving with linear algebra as the bottleneck** —
F4 — as the best known approach. There is a genuine tension here, and it should be recorded rather
than resolved: Jazeron et al. beat Gröbner-derived estimates on CICO-2 using resultants, which is
either a counterexample to that remark or a reading of "multivariate solving" broad enough to include
elimination. Either way, the epic's premise that Zeebra's architecture is the wrong one is not
supported by the sources.

## 5. The gap list, in priority order

Zeebra's root-finding *algorithm* already matches the published gcd-based one (§1.1). What is missing
is the subroutine set under it, and under Graeffe:

1. **NTT-based multiplication and squaring.** Schoolbook today, measured exponent 2.00. Every
   prerequisite exists — two-adic roots of unity over every field, `FFTDomain`, `evaluate`,
   `interpolate`. Needed: pad, transform, multiply pointwise, invert. **This alone unlocks the
   Graeffe transform**, which is `f0² - x·f1²` by exactly those operations (§1.2).
2. **Mixed-radix FFT.** Power-of-two only today, which caps KoalaBear at `2^24` and puts every
   registered target out of reach regardless of time (§3.3). The field admits `2^24 · 127`. Bluestein
   or a radix-127 stage both reach it.
3. **Newton-iteration division.** `pow_mod_limbs` reduces once per squaring, so the gcd-based root
   finder inherits division directly; this takes it from `log q · δ²` to `log q · δ log δ`. **Not
   needed by the Graeffe route.**
4. **Half-gcd.** `gcd.rs` is plain Euclid, `O(δ²)`; the deck names half-gcd at `Õ(δ)` as the second
   step of the gcd-based root finder. D2 did not identify this. **Not needed by the Graeffe route.**
5. **A subproduct tree**, for multipoint evaluation and interpolation at arbitrary points — what the
   streaming evaluation–interpolation resultant of §3.1 runs on. D2 measured
   `lagrange_interpolate` at exponent 2.97, cubic. Nothing exists to build on.
6. **Modular composition** (Brent–Kung) only if something needs it; `Polynomial::compose` is the
   unreduced form.

Items 1–2 are the smallest useful increment and serve both routes. Items 3–4 are the gcd-based root
finder. Item 5 is specific to the resultant elimination.

## 6. Per-child recommendation

### 6.1 D1 (#82) — keep it, recast it

Its structural question is answered (§2), so the value moves to construction and reproduction. Two
prerequisites the issue does not mention:

- **Zeebra has no Poseidon2.** `src/grobner/research/poseidon.rs` implements Poseidon; `grep` finds
  no Poseidon2. Every published CICO-2 figure is Poseidon2, so without it there is nothing to
  reproduce against.
- **Zeebra has no resultant machinery at all** — no Sylvester construction, no subresultants.
  `Matrix::determinant` exists, enough for a naive bivariate resultant at tiny degree and no more.

Target the two smallest published rows — Poseidon2-31k (4,1) and (4,3), which cost the authors
0.11 s / 6 MB and 1.55 s / 611 MB, at resultant degrees `3^9` and `3^11`. D2's measured curve puts
those at **40 s** and **0.89 h** for Zeebra's *existing* root finder, before any of §5. A
reproduction is checkable in a way an estimate is not.

### 6.2 D3 (#84) — unblocked, cheapest, but not a substitute for D1

Its wide-field NTT blocker is gone, and §1.2 shows its prerequisite is the smallest of any item
here: FFT, invFFT, pointwise. 2025/950's measured gains over the gcd-based predecessor are large —
about `2^13` in wall time and `2^4.5` in memory — and its memory **streams**: "large system RAM is not
necessary… our implementation will automatically swap polynomial coefficients and FFT data to and
from disk as needed… about 2 ∼ 3 times slower than running entirely in RAM". That is what makes a
300 GB machine usable at TB-scale data volumes.

But it attacks **CICO-1**, and every registered target is CICO-2 (§4.1). So D3 is the *inner* root
finder for a CICO-2 attack, not the whole of one. Sequencing D3 before D1 is still right — it is
cheaper, it is independently useful, and D1 needs a fast univariate solver anyway.

### 6.3 D4 (#85) — the comparison has to change instance

No published figure can be the common instance: they are all Poseidon2 and Zeebra generates
Poseidon. D4's head-to-head must run on a **Poseidon** instance from Zeebra's own frozen ladder
(`challenge.rs`'s nine rows, `R_F ∈ {2,4,6}` against `R_P ∈ {0,2,4}`), with both sides implemented
here. That is a measurement of two Zeebra implementations — a weaker claim than the issue implies,
and the only honest one available.

Note the near-coincidence: the hardest row the published resultant attack solved is `(6,4)`, and the
ladder's hardest row is also `(6,4)` — but for Poseidon, so 2.6 h / 10 TB does not transfer to it.

### 6.4 Does any of this threaten deployed parameters?

No, on both papers' own extrapolations. The deck's, to parameters chosen for a real security level:

| instance | t | d | `R_F` | `R_P` | k | their CICO-k complexity | brute-force CICO-k |
|---|---|---|---|---|---|---|---|
| Poseidon2-31k | 16 | 3 | 8 | 20 | 2 | 105.1 | 62 |
| Poseidon2-31m | 16 | 5 | 8 | 12 | 2 | 110.8 | 62 |
| Poseidon2-64 | 8 | 7 | 8 | 22 | 1 | 97.6 | 64 |
| Poseidon-256 | 3 | 5 | 8 | 114 | 1 | 298.8 | 255 |

Worse than brute force on every row. And 2025/950 §4.2, for the 128-bit Poseidon-256 instance at
`R_F = 8`, `R_P = 56` — degree `5^63` after the Skip First Rounds Trick — estimates the attack as
hard as `2^198` SHA-256 permutations, concluding "the current parameter choice looks a little bit
conservative".

So the significance of this direction is against **reduced-round bounty instances** and against
**Gröbner-derived security estimates**, not against deployed parameters. That bounds how much it is
worth: it is a statement about estimation methodology.

## 7. What is not concluded, and what would close it

- [x] "D1 and D3 each state, for one concrete published instance, what the method computes and what
      it would cost in Zeebra." **Both done**: D1 in §1.1/§2/§6.1 on Poseidon2-31k, D3 in §1.2/§6.2
      on Poseidon-64 at degree `7^12`.
- [ ] "D4 produces a measured comparison on a problem solvable both ways." Needs a resultant
      implementation and §6.3's change of instance.
- [ ] "The epic closes with a written recommendation, including the option of declining." §0 is a
      recommendation but a partial one: it declines `R_P ∈ {8, 10}` on time, keeps `R_P = 6` open,
      re-scopes the children, and does not accept or decline the direction as a whole, because D4 is
      unmeasured and nothing here has been built.

**#68 should stay open.** The cheapest next step that moves it is §5 items 1–2 — NTT multiplication
and a mixed-radix FFT — which are prerequisites for every route, are independently valuable to the
crate, and would let D3 reproduce one published degree.

## 8. Sources and verification status

#68 and #82 require that figures be read out of the document, and that search-engine summaries are
not citable. Status as of 2026-11-05:

| source | status | cited here |
|---|---|---|
| Jazeron, *Solving CICO-2 bounty instances of Poseidon*, 15 Mar 2025 (`gjazeron.github.io`) | **read** — fetched directly, `pdftotext` | §1.1, §2, §3.1, §6.4 |
| eprint **2026/150**, Bak–Bariant–Jazeron et al., *Ethereum Poseidon bounties* | **read** — PDF supplied locally after HTTP 403; `pdftotext` | §1.1, §2, §3.1, §3.2 |
| eprint **2025/950**, Zhao–Ding, *Breaking Poseidon Challenges with Graeffe Transforms…* | **read** — PDF supplied locally after HTTP 403; `pdftotext` | §1.2, §3.3, §4, §4.1, §6.2, §6.4 |
| eprint **2024/886**, Yang et al., *A New Security Evaluation Method Based on Resultant…* | **read** — PDF supplied locally; `pdftotext` | §3.1 only. It concerns Rescue-Prime, Anemoi and Jarvis rather than Poseidon, so its instance figures do not bear on this assessment; its streaming evaluation–interpolation argument does |
| BSGL20, Theorem 10 (ideal degree of CICO-c) | **not read** — cited as 2026/150 cites it | §2, flagged as second-hand |

Both ePrint PDFs returned the same Cloudflare 403 that #68 recorded on 2026-11-04, re-tested on
2026-11-05; they were read from locally supplied copies. The one remaining second-hand citation is
BSGL20's Theorem 10, which is load-bearing for §3.2's degree column and should be read before any
cost estimate here is treated as settled.
