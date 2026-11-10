# Elimination beyond Gröbner bases: a feasibility assessment

**Measured at:** publication bound `f2135cce`…`03b419f7` — the commits that published these figures,
recovered from git rather than recorded at the time ([§10](external-comparison-protocol.md#10-the-commit-and-what-a-publication-bound-is)).
The bound is unchanged by the 2026-11-08 re-scoring (§0.1, §5.1, §7.1): **nothing was measured for
it.** Every Zeebra figure it quotes is cited to the document that took it —
[`resultant-elimination.md`](resultant-elimination.md),
[`graeffe-root-finding.md`](graeffe-root-finding.md),
[`fast-univariate.md`](fast-univariate.md) and
`MILESTONE-PUBLISHED-ATTACK-REPRODUCTION.md` (moved out in #668) — each
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

*§0 (the recommendation for the registered CICO-2 targets, and its re-scoring in §0.1)
was moved out with the cryptanalysis research in #668; it is preserved at commit 9532a9a2.*

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
`(α+2)^N` quotient dimension `additional-benchmarks.md` §3.2 (moved out in #668) measured from the `six-worlds-anemoi`
logs and tagged `Claim::Observed` because "the designers' corresponding statement is a conjecture".
**There is now a proven upper bound for it**, so a Zeebra measurement agreeing with `(α+2)^N` can be
checked against a bound rather than only against someone else's measurement. Handed to #201.
2025/2040's Table 1 also marks the CheapLunch genericity assumptions as **not satisfied** for Griffin
and ArionHash, which is relevant to #202 and which §7 of `additional-benchmarks.md` (moved out in #668) did not know.

Within the Gröbner approach the bottleneck has already moved off F4: [ABM23] observed that Poseidon
CICO systems have a lower solving degree than random ones, so "the bottleneck shifts from the Gröbner
basis computation step to finding an univariate polynomial in the ideal" — and 2026/1905 confirms it
in practice, "the bottleneck for the Gröbner basis attack comes from the change-of-ordering step,
which is performed using the FGLM algorithm". That is Zeebra's FGLM, and it is the stage M23's
scalability work is aimed at.

## 2. What was actually published, per registered target

*§2 (the published solutions per registered target, §2.1–§2.3)
was moved out with the cryptanalysis research in #668; it is preserved at commit 9532a9a2.*

## 3. What this means for Zeebra, quantitatively

*§3 (per-target degree, transform-size and per-family cost estimates for the registered targets)
was moved out with the cryptanalysis research in #668; it is preserved at commit 9532a9a2.*

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

*§5–§7 (the gap list, the per-child recommendations and the acceptance scoring for the
registered-target work) were moved out with the cryptanalysis research in #668; they are preserved
at commit 9532a9a2.*

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
