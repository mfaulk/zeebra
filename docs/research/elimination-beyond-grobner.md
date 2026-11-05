# Elimination beyond Gröbner bases: a feasibility assessment

Reference for #68. A decision record in the style of #58 — the question answered once with the
measurements attached — covering D1 (#82), D2 (#83), D3 (#84) and D4 (#85).

**#68's deliverable is an assessment, not an implementation, and nothing was implemented for it.**
What changed since the epic was written is that D2 landed, and that the primary source for D1's
central question turned out to be readable. Together those answer more of the epic than its child
issues assumed was open.

## 0. Recommendation

1. **Decline the registered 2026 CICO-2 targets by the resultant route.** The published method needs
   **824 TB** for the easiest of the three, by a memory model calibrated against the authors' own
   reported figure to within 2%. This workstation has 300 GB. §3.
2. **Recast D1** from "verify the structural claim" — already answered, §2 — to **"reproduce the two
   smallest published rows"**: Poseidon2-31k CICO-2 at `(R_F, R_P) = (4,1)` and `(4,3)`, which cost
   the authors 0.11 s / 6 MB and 1.55 s / 611 MB. Those are reachable here, and a reproduction is
   checkable in a way an estimate is not. §6.1.
3. **Build the univariate subroutine set first**, in this order: NTT-based multiplication, Newton
   division, **half-gcd**. It is the common prerequisite for D1 and D3, it is what separates Zeebra
   from the published work algorithmically, and it is independently valuable. §5.
4. **Prefer D3 to D1** for the leverage, if only one is done. §6.2.
5. **D4 must use a Poseidon instance from Zeebra's own frozen ladder**, because the published figures
   are all Poseidon2 and the crate has no Poseidon2. §6.3.

The epic's own go/no-go — "decline the direction if D4 shows the resultant path is not competitive"
— is not yet answerable, and §7 says exactly what would answer it.

## 1. What the published resultant attack does

**Source, read directly.** Guilhem Jazeron, *Solving CICO-2 bounty instances of Poseidon*,
15 March 2025, `https://gjazeron.github.io/assets/presentations/poseidon.pdf`. Fetched and extracted
with `pdftotext` on 2026-11-05, so the figures below are read out of the document, as #68 and #82
both require. §8 records the verification status of every other source, including the two ePrint
PDFs that are still HTTP 403.

The attack targets the **2025** Ethereum Foundation bounty round, and its CICO-2 instances are
**Poseidon2**:

| instance | base primitive | CICO branches | field | t | d | `(R_F, R_P)` attacked |
|---|---|---|---|---|---|---|
| Poseidon2-31k | Poseidon2 | 2 | KoalaBear (31) | 16 | 3 | (4,1), (4,3), (6,4) |
| Poseidon2-31m | Poseidon2 | 2 | Mersenne (31) | 16 | 5 | (4,0), (4,1), (6,1) |
| Poseidon-256 | Poseidon | 1 | BLS12-381 (256) | 3 | 5 | (6,8), (6,9) |
| Poseidon2-64 | Poseidon2 | 1 | Goldilocks (64) | 8 | 7 | **none — "we did not manage to attack any"** |

Resultants are used for **CICO-2 only**; "for CICO-1, we used already known techniques".

**The root-finding algorithm is the one Zeebra already has.** The deck states it as: compute
`X^q - X mod P` by double-and-add, take `G = gcd(P, Q)`, and recover the roots of `G`, which "will
have degree one or two with high probability". That is `src/poly/univariate/roots.rs` line for line.
Their complexity is `Õ(δ log q)` — "First step: `Õ(δ log(q))` operations. Second step, using the
half-gcd algorithm: `Õ(δ)`." Zeebra's is `O(log q · δ²)`, measured. The difference is **entirely in
the subroutines**, not in the algorithm. §5.

## 2. The structural claim: answered, not open

D1 was created to verify that Poseidon-style structure makes the resultant's degree far smaller than
the generic product bound — "a cheap and decisive negative result" if it does not appear. The deck
answers it, as an experimental finding of the authors:

> The degree of the two polynomials forming the system is `d^(R_F+R_P)`. We would expect the degree
> of the resultant to be `d^(2R_F+2R_P)`. However, we experimentally noticed that the degree of the
> resultant is `d^(2R_F+R_P)`. It also corresponds to the degree of the polynomial ideal: why is
> that?

So the structure saves exactly a factor **`d^(R_P)`**, and their reading of it is stated plainly:

> This fact saves a factor `d^R_P` in the computation. Hints that partial rounds are not as strong as
> full rounds to prevent algebraic attacks.

Two consequences for Zeebra. The claim is **real and quantified**, so D1 does not need to establish
it — the cheap negative result D1 hoped for is not available. And it is an *experimental* observation
in the source, with the authors asking why it holds, so verifying it independently on a small
instance remains worth doing — as a confirmation, not as the deciding question.

The formula also checks out against their own table: with the round-skipping trick the deck gives
`δ = d^(R_F-1+R_P)`, `d_res = d^(2(R_F-1)+R_P)` and total `Õ(d^(3(R_F-1)+2R_P))`. For
Poseidon2-31k (6,4) the un-skipped form gives `δ = 3^10`, `d_res = 3^16`, so
`log2(δ · d_res) = 41.2` against their stated estimate of 43.

## 3. What it cost them, and what that implies here

Their results, verbatim from the deck. Complexity estimates are `log2`; bold in the original marks
the instances where they beat the EF claim.

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

Hardware, verbatim: "AMD EPYC 9354 with 1TB of RAM, **12TB of NVMe swap memory** and 120 threads",
with one instance run on "1000 cores of Intel Xeon 5218". Software: **NTL** for polynomial
arithmetic and **PML** for the interpolation–evaluation resultant algorithm. Their own resultant
algorithm is `Õ(δ³)`; they note Villard's `Õ(δ^(2+ε))` exists but "is not implemented in the finite
field polynomial libraries (NTL, Flint, …)".

### 3.1 A memory model, calibrated

An evaluation–interpolation resultant holds on the order of `δ · d_res` field elements. At 4 bytes
for a 31-bit residue:

| instance | `δ` | `d_res` | model | they reported |
|---|---|---|---|---|
| Poseidon2-31k (4,1) | `3^5` = 243 | `3^9` = 19 683 | 19.1 MB | 6 MB |
| Poseidon2-31k (4,3) | `3^7` = 2 187 | `3^11` = 177 147 | 1.55 GB | 611 MB |
| Poseidon2-31k (6,4) | `3^10` = 59 049 | `3^16` = 43 046 721 | **10.2 TB** | **10 TB** |

The model over-estimates the two small rows by about 2.5x and lands **within 2%** on the large one —
which is the row where memory is the binding constraint and the full structure has to be resident.
It is trustworthy exactly where it matters.

### 3.2 Zeebra's registered 2026 targets, under that model

`src/grobner/research/challenge.rs` registers the three official 2026 CICO targets: **Poseidon**
(not Poseidon2), KoalaBear, `alpha = 3`, `t = 16`, `k = 2`, `R_F = 6`, `R_P ∈ {6, 8, 10}`.

| target | `δ` | `d_res` | memory model |
|---|---|---|---|
| `R_P = 6` | `3^12` = 531 441 | `3^18` = 387 420 489 | **824 TB** |
| `R_P = 8` | `3^14` = 4 782 969 | `3^20` = 3 486 784 401 | 66.7 PB |
| `R_P = 10` | `3^16` = 43 046 721 | `3^22` = 31 381 059 609 | 5.4 EB |

**This workstation has 300 GB.** The step from the hardest instance anyone solved by this method
(`3^16`, 10 TB) to the easiest target Zeebra has registered (`3^18`) is a factor of `3^4 = 81` in
the product, i.e. 810 TB — which the model confirms independently at 824 TB.

Two caveats, both stated rather than buried. The formula is the authors' observation for
**Poseidon2**, and Zeebra's registered targets are **Poseidon**, whose linear layer differs; the
degree growth is governed by the S-box and the MDS spreading it, so the form is expected to carry
over, but it is not verified here. And the 2026 programme is **finished with all three targets
solved externally** (registry: `R_P = 6` verified 2026-04-10, `R_P = 8` 2026-05-06, `R_P = 10`
2026-07-06) — so they were solved, and by this arithmetic not by this resultant method. §6.2.

### 3.3 The transform ceiling bites too

Independently of memory, a product of two degree-`d` polynomials needs a power-of-two transform of
at least `2d + 1` points, and D2 recorded each field's two-adicity as a hard ceiling on that:

| working degree | transform needed | KoalaBear, s = 24 | BabyBear, s = 27 |
|---|---|---|---|
| `3^9` = 19 683 | `2^16` | yes | yes |
| `3^11` = 177 147 | `2^19` | yes | yes |
| `3^16` = 43 046 721 | `2^27` | **no** | yes |
| `3^18` = 387 420 489 | `2^30` | **no** | **no** |
| `3^22` | `2^36` | **no** | **no** |

So at the 2026 targets' resultant degree, **no NTT-friendly 31-bit prime in the crate can host the
transform at all** — that needs CRT across several primes, Kronecker substitution, or a wider field.
D2 listed a CRT/Kronecker fallback as a gap for Mersenne-31's two-adicity of 1; it turns out to be
needed for KoalaBear as well, at exactly the degrees this direction cares about.

## 4. Where Zeebra actually stands

From [`fast-univariate.md`](fast-univariate.md) (D2, #83) and
[`batch-inversion.md`](batch-inversion.md) (#118), both measured on this workstation:

- **The wide-field NTT blocker is cleared.** `root_of_unity` was `unimplemented!()` for
  `PrimeFieldElement256`; the two-adic construction landed, so there is now a transform over BN254
  and BLS12-381. #68 named this as D2's first task and a blocker on D3's experimental half. Done.
- **The transforms are healthy.** `evaluate` reaches `2^23` over a 31-bit field in one second, and
  `interpolate` now costs the same as `evaluate` to within 2–10%.
- **Root finding is the binding stage**, at `O(log q · δ²)`: degree 4 096 in 1.72 s over KoalaBear,
  measured exponent 1.93.
- **Memory is not the constraint anywhere Zeebra can reach.** Every stage is linear in degree at a
  small constant — root finding peaks at `12 n B`, so 2.07 GB even at `3^16`.

Extrapolating the measured quadratic growth of root finding, with no new machinery:

| degree | Zeebra `roots`, extrapolated | `roots` peak memory |
|---|---|---|
| `3^9` = 19 683 | **40 s** | 0.94 MB |
| `3^11` = 177 147 | **0.89 h** | 8.5 MB |
| `3^16` = 43 046 721 | 52 770 h (6.0 years) | 2.07 GB |

**So the epic's premise needs restating.** #68 says this regime is "FFT/NTT-dominated, and reportedly
bound by memory *access* rather than arithmetic". The *reported* half is consistent with what little
of 2025/950 is legible from here — its abstract is said to call memory access an essential barrier
and to model FFT memory-access cost as growing with the 4/3 power of input size, though §8 records
why even that is provisional. The published resultant figures in §3, which *are* read directly, say
the same thing outright: 10 TB against 2.6 h is a memory problem. But that describes mature
implementations operating at the
degrees where bandwidth binds. Zeebra is **two subroutines short of reaching that regime at all**:
its barrier is that it has no sub-quadratic multiplication, and its memory is comfortable precisely
because its degrees are small. The two statements are not in conflict; they describe different
points on the same curve, and conflating them would set the wrong priorities.

## 5. The gap list, in priority order

Zeebra's root-finding *algorithm* already matches the published one (§1). What is missing is the
subroutine set underneath it, and each item has a measured cost it would remove:

1. **NTT-based multiplication.** Schoolbook today, measured exponent 2.00. Every prerequisite now
   exists — a two-adic root of unity over every field of interest, `FFTDomain`, `evaluate`,
   `interpolate`. Needed: pad to a power of two, transform both inputs, multiply pointwise, invert.
   Plus a CRT or Kronecker fallback, which §3.3 shows is needed for KoalaBear and not only for
   Mersenne-31.
2. **Newton-iteration division.** `pow_mod_limbs` reduces once per squaring, so root finding
   inherits division's cost directly; this takes it from `log q · δ²` to `log q · δ log δ`.
3. **Half-gcd.** `src/poly/univariate/gcd.rs` is plain Euclid, so `O(δ²)`. The deck names half-gcd
   as the second step of its root-finding complexity, at `Õ(δ)`. **D2 did not identify this**; it is
   new here, and it is the step that would otherwise become the bottleneck once (1) and (2) land.
4. **A subproduct tree**, for multipoint evaluation and interpolation at arbitrary points. D2
   measured `lagrange_interpolate` at exponent 2.97 — cubic — and it is what an
   evaluation–interpolation resultant runs on. Nothing exists to build on.
5. **Modular composition** (Brent–Kung) only if D3 needs it. `Polynomial::compose` is the unreduced
   form, unusable for `f(g) mod h`.

Items 1–3 are the univariate root-finding path and are shared by D1, D3 and the existing `factorize`.
Item 4 is specific to the resultant route.

## 6. Per-child recommendation

### 6.1 D1 (#82) — recast, and much smaller

Its central question is answered (§2), so the remaining value is a **reproduction**, which is
checkable in a way an estimate is not. The two smallest published rows are the targets:
Poseidon2-31k CICO-2 at `(4,1)` and `(4,3)`, costing the authors 0.11 s / 6 MB and 1.55 s / 611 MB,
with resultant degrees `3^9` and `3^11` — which §4 puts at 40 s and 0.89 h for Zeebra's *existing*
root finder, and far less once §5's items 1–3 land.

Two prerequisites the issue does not mention:

- **Zeebra has no Poseidon2.** `src/grobner/research/poseidon.rs` implements Poseidon; `grep` finds
  no Poseidon2 anywhere. Every published CICO-2 figure is Poseidon2, so without it there is nothing
  to reproduce against.
- **Zeebra has no resultant machinery at all** — no Sylvester construction, no subresultants; `grep`
  for `resultant`/`Sylvester` over `src/` finds nothing. `Matrix::determinant` exists, which is
  enough for a naive bivariate resultant at tiny degree and nothing more.

Do **not** aim D1 at the registered 2026 targets (§3.2).

### 6.2 D3 (#84) — the better-leveraged bet

2025/950 is reported to claim **2^13 improvement in wall time and 2^4.5 in memory** over existing
attacks, which is the resultant work in §3. If that holds, it is the difference between 10 TB and
roughly 450 GB on the instance that cost 10 TB — still above this box, but a different order of
problem. Both figures reached us only through a summarizing fetch of the abstract page (§8), so they
are a reason to look, not a baseline. And the 2026 programme's three targets were all solved externally while the resultant
method's own arithmetic puts them at 824 TB and up, which points at the Graeffe/FFT route rather
than the resultant one.

Its experimental half was blocked on D2's wide-field NTT. That block is gone. It shares §5's items
1–3 with D1 and needs no subproduct tree, which makes it the cheaper of the two to attempt.

**The 2025/950 PDF is still unread** (§8), so neither figure may be treated as a baseline. Reading
it is the first task of D3, not an assumption D3 may start from.

### 6.3 D4 (#85) — the comparison has to change instance

D4 needs "an instance both paths can consume". No published resultant figure can be one: they are
all Poseidon2, and Zeebra generates Poseidon. So D4's head-to-head must run on a **Poseidon**
instance from Zeebra's own frozen ladder (`challenge.rs`'s nine rows at `R_F ∈ {2,4,6}` against
`R_P ∈ {0,2,4}`), with both sides implemented here and neither taken from a paper. That makes it a
measurement of two Zeebra implementations, which is a weaker claim than the issue implies but the
only honest one available.

Note the near-coincidence: the hardest instance the published resultant attack solved is
`(R_F, R_P) = (6,4)`, and Zeebra's frozen ladder's hardest row is also `(6,4)` — but for Poseidon,
not Poseidon2, so the 2.6 h / 10 TB figure does not transfer to it.

### 6.4 Does this direction threaten anything deployed?

The deck's own extrapolation to parameters chosen for a real security level says no:

| instance | t | d | `R_F` | `R_P` | k | their CICO-k complexity | brute-force CICO-k |
|---|---|---|---|---|---|---|---|
| Poseidon2-31k | 16 | 3 | 8 | 20 | 2 | 105.1 | 62 |
| Poseidon2-31m | 16 | 5 | 8 | 12 | 2 | 110.8 | 62 |
| Poseidon2-64 | 8 | 7 | 8 | 22 | 1 | 97.6 | 64 |
| Poseidon-256 | 3 | 5 | 8 | 114 | 1 | 298.8 | 255 |

On every row the resultant attack is **worse than brute force**. Its significance is against
*reduced-round bounty instances* and against *Gröbner-derived security estimates*, not against
deployed parameters. That bounds how much this direction is worth to Zeebra: it is a statement about
estimation methodology, which is interesting, rather than a break.

## 7. What is not concluded, and what would close it

#68's acceptance criteria, honestly scored:

- [x] "D1 and D3 each state, for one concrete published instance, what the method computes and what
      it would cost in Zeebra." **D1: done here** — §1 for what it computes, §3.1/§4 for the cost, on
      Poseidon2-31k (6,4) and the two smaller rows. **D3: not done** — the 2025/950 PDF is
      unreadable from here, so what the Graeffe method computes is not recorded from a primary
      source.
- [ ] "D4 produces a measured comparison on a problem solvable both ways." Needs a resultant
      implementation and §6.3's change of instance.
- [ ] "The epic closes with a written recommendation, including the option of declining." §0 is a
      recommendation, but it is partial: it declines the registered targets by the resultant route
      and re-scopes the children, and does not decline or accept the direction as a whole, because
      D3 and D4 are unmeasured.

**So #68 should stay open.** What would close it: read the 2025/950 PDF by some route the 403 does
not block, then do §5 items 1–3, then D3 on one small instance. The resultant half can be declined
now on the arithmetic in §3.

## 8. Sources and verification status

#68 and #82 both require that any figure be read out of the document before it is recorded, and that
search-engine summaries are not citable. Status as of 2026-11-05:

| source | status | what is cited here |
|---|---|---|
| `gjazeron.github.io/assets/presentations/poseidon.pdf` | **read** — fetched, extracted with `pdftotext` | everything in §1, §2, §3, §6.4 |
| eprint 2025/950 (Graeffe / FFT lower bounds) | PDF **HTTP 403**. Abstract page reachable, but only through a summarizing fetch — **not a verbatim read** | nothing as a baseline. Reported from that summary, and flagged as provisional wherever used: a 2^13 wall-time and 2^4.5 memory improvement over existing attacks, FFT memory-access cost growing as the 4/3 power of input size, and memory access as "an essential barrier" |
| eprint 2026/150 (resultant attacks on small-scale Poseidon/Poseidon2) | PDF **HTTP 403**, not read | nothing |
| eprint 2024/886 (resultant-based security evaluation) | abstract reached only through a summarizing fetch, i.e. **not a verbatim read** | nothing. It concerns Rescue-Prime, Anemoi and Jarvis rather than Poseidon, so it does not bear on this assessment |

The two 403s are the same Cloudflare block #68 recorded on 2026-11-04, re-tested on 2026-11-05 with
the same result. The deck was reachable because it is not hosted on ePrint; it covers the same work
as 2026/150 by the same author, which is why the resultant half of this assessment is well sourced
and the Graeffe half is not.
