# M33-G1: where the one-worker gap to grobx lives on wide primes (#970)

**Status:** complete, 2026-11-21. **Plan:** [`MILESTONE-COMPETITIVE-BENCHMARKING.md`](../MILESTONE-COMPETITIVE-BENCHMARKING.md)
§§3.1, 4.1, 6 (HG1–HG3), 9.5, 13.
**Measured at:** study builds `a13983d6` (tag `measured/970-g1-build`; `src/` differs from F0
`31e334bd` only by code compiled under `research-sigf4-split`, so the timed `sig` build is F0's
engine), `hwcount.py` at `b518248e` (tag `measured/970-g1-hwcount`), grobx 0.155.1 `8005a2a1`
(driver SHA-256 `fdd6aeec…`, [`pins.json`](../../research/m33-baseline/pins.json)). One
`tools/bench-job` dev-mode session, job `4004a790e353`, 2026-11-21: n = 9 per arm and row, arms
interleaved and rotated, fresh process per attempt, CPU 8 of reserved CCDs 1–2, load 1.3–4.0.
Conventional-F4 counters (`work.json`) were taken untimed on CPU 40. **Host:** Threadripper PRO
5995WX. **Records:** [`research/m33-grobx-attribution/`](../../research/m33-grobx-attribution/README.md);
every figure below is in its generated [`tables.md`](../../research/m33-grobx-attribution/tables.md).

## Outcome

| | Result |
|---|---|
| **Where the gap is** | **Not in elimination.** On Eco-12 Zeebra's elimination clock equals grobx's (1.01× [0.98, 1.03]); on Katsura-11 it is faster (0.89×). The gap is **symbolic preprocessing** (41% of Eco-12's gap, 50% of Katsura-11's), **bookkeeping** (25%, Eco-12 only), **interreduction** (16% / 37%), the **digest** (8% / 25%) and in-call glue (9% / 9%). MQ11 is the exception: half its gap is elimination, from rows grobx rules zero by **randomized** tests |
| **Per-product cost** | Zeebra is **cheaper per product** on every row: 2.18 / 2.14 / 2.01 ns against grobx's 2.77 / 2.92 / 2.80 ns per charge (0.72–0.79×). grobx takes a `u128` remainder per product at p ≥ 2⁶³ |
| **HG1** | Count **holds**: 90% / 42% / 52% of Zeebra's elimination products go into rows that reduce to zero or yield an element the reduced basis drops. The **exact** route to removing them is not found (Q6), and grobx spends the same elimination time on Eco-12 anyway. Not a G2 candidate |
| **HG2** | **Falsified as stated** (the unfused layout). #964's lead holds on Eco-12 (symbolic 0.621×) and Katsura-11 is still slower (1.069×) after one explanation attempt. A different mechanism, the one grobx uses, is candidate 1 |
| **HG3** | **Holds.** 7.6% / 14.7% / 8.3% of wall is outside the four stages: the digest 3.4% / 9.5% / 5.5%, basis materialization 2.5% / 2.2% / 1.5% |
| **Candidates for #971** | **One Gate A record**: a persistent monomial table for symbolic preprocessing (predicted Eco-12 −10.1%). The second-ranked, interreduction in the engine's own representation, predicts 13% on Katsura-11 but only 5.2% on Eco-12, under the 8% gate; owner decision |
| **Go/no-go** | No candidate or additive pair brings Eco-12 below 1.0. Both together predict 2,106 ms ÷ 1,597 = **1.32**. Only if every stage but elimination, the digest and the glue included, matched grobx would Eco-12 reach about 1.00. **T-G is reported as missed**; Track G aims at the largest achievable reduction |
| **Correctness** | All 162 attempts' `m33-basis-v1` digests agree per row (1 distinct digest each) |
| **Session** | Void under the per-cell clock rule (78/162), and 35/162 grouped per arm. Foreign load peaked at 1.7%. The flags are the frequency sampler's, not the CPU's: `hwcount`'s cycle counts give 4.09–4.25 GHz for arms the sampler read at 1.43 GHz (§1) |

## 1. Session

Six arms per row at one worker: `sig` (the timed build), `split` (`research-sigf4-split`: unfused
symbolic, component clocks and the element ledger), `grobx155` (its stock report carries per-round
clocks and budget charges), `sig-hw` and `split-hw` (the two builds under
[`hwcount.py`](../../research/m33-grobx-attribution/hwcount.py)), and `sig-w4` (the timed build asked
for four workers on its one CPU). 162 attempts, all ok, one digest per row.

bench-job's §11.2 verdict is **void**: 78 of 162 attempts are flagged by the 3% clock rule alone,
and 35 of 162 when the median is taken per arm. The thresholds are unchanged. Every Katsura-11 cell
is flagged because the sampled `scaling_cur_freq` reads one of four values (1.43, 2.67, 3.99,
4.54 GHz), and the hardware-counted arms on Katsura-11 sampled 1.43 GHz on every attempt. Their
counted cycles over in-process time are 4.16 and 4.09 GHz. The same mechanism voided #966's
sessions. As there, every table uses all ok attempts, pending the owner's decision on #965. The
paired ratios (§§5, 7) are within-row and do not depend on the reading.

## 2. Where the wall goes (Q1, HG3)

Medians in ms, `sig` against `grobx155`. grobx's report is mapped onto Zeebra's stages:
bookkeeping = select + update + record, symbolic = symbolic + encode, elimination = reduce +
backsub + decode, interreduction = its final `inter` matrix. "Digest" is Zeebra's `basis_m33`
against grobx building its basis text, both inside the process wall. Ratio = Zeebra ÷ grobx,
independent bootstrap. Share = part's Δ ÷ wall Δ.

| Part | Eco-12 Z | grobx | Δ | share | ratio | Katsura-11 Z | grobx | Δ | share | ratio |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| **process wall** | 2,484 | 1,597 | 887 | | 1.56 [1.53, 1.57] | 835 | 559 | 276 | | 1.49 [1.47, 1.52] |
| exec, parse, exit | 23 | 31 | −8 | −1% | 0.73 | 18 | 33 | −14 | −5% | 0.56 |
| digest / basis text | 84 | 11 | 73 | 8% | 7.55 | 79 | 11 | 68 | 25% | 7.23 |
| in call, outside stages | 83 | 3 | 81 | 9% | 33.6 | 26 | 1 | 25 | 9% | 28.3 |
| bookkeeping | 230 | 5 | 225 | **25%** | 45.3 [44.9, 46.8] | 15 | 6 | 10 | 3% | 2.61 |
| symbolic | 454 | 89 | 366 | **41%** | 5.13 [4.99, 5.22] | 158 | 20 | 138 | **50%** | 7.93 [7.74, 8.10] |
| elimination | 1,329 | 1,314 | 15 | 2% | **1.01 [0.98, 1.03]** | 428 | 481 | −54 | −19% | **0.89 [0.88, 0.91]** |
| interreduction | 274 | 136 | 138 | 16% | 2.01 [1.90, 2.14] | 110 | 7 | 102 | **37%** | 15.3 [15.3, 15.5] |

**MQ11 / Goldilocks** (wall 4,883 against 2,919, Δ 1,963): elimination 3,502 against 2,510 (51% of
the gap, 1.40×), symbolic 447 against 46 (20%, 9.7×), interreduction 512 against 216 (15%), digest
267 against 36 (12%), in-call glue 5%, bookkeeping 1%.

The session's ratios (1.56, 1.49, 1.67) sit inside #966's record intervals (1.578 [1.290, 1.659],
1.522 [1.284, 1.594], 1.731 [1.584, 1.966]).

**HG3 (outside the four stages, under the aligned region).** 188 / 123 / 405 ms, which is 7.6% /
14.7% / 8.3% of wall. That is above the 5% of HG3, so HG3 holds. It splits as follows:

- the digest: 84 / 79 / 267 ms, of which grobx's own text build is 11 / 11 / 36;
- materialization of the signature basis as polynomials: 62 / 19 / 76 ms;
- exec, argument and input parsing, and exit: 23 / 18 / 41 ms, less than grobx's;
- other engine glue: about 21 / 7 / 20 ms;
- the engine drop and input normalization: under 0.2 ms.

## 3. Work counters (Q1)

Deterministic; one attempt per row shown, all nine agree. Full table in `tables.md` §3.

| | Eco-12 Z | grobx | Katsura-11 Z | grobx | MQ11 Z | grobx |
|---|---:|---:|---:|---:|---:|---:|
| Route | signature | sig 2 rounds → plain (combinations) | signature | signature | signature | signature |
| Pairs created | 1,775,561 | — | 156,250 | — | 293,761 | 293,761 considered |
| Rows reduced | 2,898 | 1,381 | 706 | 693 | 1,307 | 782 |
| Reductions to zero | 1,013 | 384 | 145 | 124 | 540 | 26 |
| Rows ruled zero by randomized tests | — | 165 | — | 242 | — | **562** |
| Elements added | 1,885 | 941 | 561 | 543 | 767 | 756 |
| Reduced basis | 743 | 743 | 537 | 537 | 767 | 767 |
| Max matrix | 8,353 × 9,375 | 26,563 × 27,439 | 3,549 × 4,545 | 4,343 × 5,332 | 2,130 × 3,836 | 2,130 × 3,836 |
| Elimination products / charges (M) | 610.8 | 473.9 | 200.1 | 165.1 | 1,744.9 | 894.5 |
| … on zero rows | 335.6 (55%) | | 82.6 (41%) | | 898.6 (52%) | |
| … on redundant elements | 216.2 (35%) | | 0.4 | | 0 | |
| … on kept elements | 59.0 (10%) | | 117.1 (59%) | | 846.2 (48%) | |
| Interreduction columns / nonzeros (M) | 9,773 / 0.98 | 6,379 / 0.74 | 1,561 / 0.39 | 1,569 / 0.39 | 2,815 / 1.27 | 2,815 / 1.27 |
| Interreduction charges (M) | — | 52.4 | — | 1.4 | — | 76.1 |

Conventional F4 (`--discovery`) does 5,924 M / 4,556 M / 20,377 M products on these rows. Of those,
93.0% / 93.1% / 92.9% are on zero rows (6,331 / 3,936 / 6,293 zero rows), unchanged from M29. The
signature route has already removed 90% / 96% / 91% of that work.

**MQ11 is the same computation in both solvers up to the zero test.** It has the same pair
population (293,761), the same largest matrix (2,130 × 3,836) and the same 767-element basis.
Zeebra reduces its 540 zero rows in full. grobx's signature run (`reduce=tests`) rules 562 rows
zero by randomized tests (#714's "signature zero tests") and fully reduces only 26. Zeebra's
products on kept elements (846 M) match grobx's charges less its interreduction (818 M).

## 4. Per-product cost (Q1)

Zeebra's elimination clock ÷ products, against grobx's round reduce + backsub ÷ charges. #713 found
grobx's charges within 2% of executed products.

| Row | Zeebra ns/product | grobx ns/charge | Zeebra ÷ grobx | work: Zeebra ÷ grobx |
|---|---:|---:|---:|---:|
| Eco-12 | 2.18 [2.15, 2.20] | 2.77 [2.75, 2.82] | **0.79 [0.76, 0.80]** | 1.29 |
| Katsura-11 | 2.14 [2.12, 2.17] | 2.92 [2.88, 2.95] | **0.73 [0.72, 0.75]** | 1.21 |
| MQ11 | 2.01 [2.00, 2.01] | 2.80 [2.79, 2.84] | **0.72 [0.71, 0.72]** | 1.95 |

**Work count, not throughput, explains elimination**, and only on MQ11. There, 1.95× the work at
0.72× the cost leaves elimination 1.40× slower, and the extra work is exactly the 540 zero rows
grobx tests randomly. On Eco-12, 1.29× the work at 0.79× the cost comes out level. On Katsura-11,
1.21× the work at 0.73× comes out 11% faster.

The kernels are the same family. Both use a dense accumulator and a Shoup product with a
precomputed factor. Above 2⁶³, grobx's `Gf64` row update instead takes a `u128` remainder per
product (read from its source for attribution only; no code is copied). The elimination kernel is
not where Track G's gap is.

## 5. Symbolic preprocessing and HG2 (Q2)

**#964's quiet A/B is reproduced on the Track G rows** (`split` ÷ `sig`, paired, n = 9):

| Row | symbolic | process wall |
|---|---:|---:|
| Eco-12 / 2⁶⁴−353 | **0.621 [0.602, 0.635]** | 0.952 [0.935, 0.971] |
| Katsura-11 / 2⁶⁴−353 | **1.069 [1.049, 1.095]** | 1.034 [1.031, 1.047] |
| MQ11 / Goldilocks | 1.086 [1.049, 1.109] | 1.022 [1.011, 1.029] |

#964 read Eco-12 at 0.612 and Katsura-11 / Goldilocks at 1.143. The Eco-12 wall gain, 4.8%, is
below HG2's 8% in any case.

**Where the symbolic time goes** (split build, medians):

| Row | symbolic | interning | multiply | reducer search | column sort | terms (M) | interning ns/term |
|---|---:|---:|---:|---:|---:|---:|---:|
| Eco-12 | 281 | 172 (61%) | 59 | 22 | 19 | 14.57 | **11.8** |
| Katsura-11 | 170 | 140 (82%) | 19 | 4 | 5 | 5.55 | **25.2** |
| MQ11 | 484 | 408 (84%) | 58 | 5 | 9 | 16.08 | **25.4** |

**Hardware counters** (user mode, whole process; the builds differ only in the symbolic loop and the
split build's clocks, so the paired difference is that stage's):

| Row | IPC sig → split | split − sig: instructions | cycles | L1d misses | DRAM fills |
|---|---|---:|---:|---:|---:|
| Eco-12 | 3.02 → 3.25 | +0.44 G | **−0.62 G** | +30.3 M | +1.7 M |
| Katsura-11 | 2.96 → 2.91 | +0.17 G | **+0.11 G** | +11.7 M | +0.5 M |
| MQ11 | 3.59 → 3.55 | +0.51 G | **+0.33 G** | +35.7 M | +2.8 M |

**Explanation attempt (one, bounded).** Unfusing adds instructions and L1d misses on every row: the
scratch buffer is written and then reread. On Eco-12 it still saves 0.62 G cycles, because a batch
of products is probed back to back and the probes' latencies overlap (IPC +0.23). On Katsura-11 and
MQ11 there is no such saving.

Those rows' lookups cost about twice Eco-12's per term (25 against 12 ns), although their tables are
smaller (4,545 and 3,836 columns at most, against 9,375). So their lookups are not limited by cache
capacity, which overlap could hide. Each lookup is costlier in itself.

The hypothesis left standing is long probe sequences: an FxHash-style hash over 11 small exponents,
and a full 44–48-byte key compare per probe. A probe-length counter would test it, and this session
did not have one. HG2's falsifier ("Katsura-11 still slower after one bounded explanation attempt")
is therefore met, and **HG2 as stated is falsified**.

**A layout that wins on both rows is plausible, but it is not the unfused loop.** grobx's symbolic
stage is 5.1× / 7.9× / 9.7× cheaper, at about 4.4 ns per matrix entry on Eco-12. It reaches that by:

- keeping one monomial table for the whole run;
- making a product's hash the sum of its factors' hashes, so a product is never rehashed;
- storing each monomial's current matrix column in its table entry.

Its design notes cite Monagan & Pearce 2015 §2.1 for the persistent table and the additive hash, and
attribute both ideas to Faugère and Magma. That is candidate 1 (§9).

Zeebra instead builds a fresh `MonomialMap` per batch, rehashes every product's exponent vector, and
re-interns every term. Removing the per-lookup work, rather than overlapping it, does not depend on
which row's probes are long.

## 6. Interreduction (Q4)

#877's tail-only interreduction **already runs on the signature route**: `sigf4::engine::interreduce`
uses `MatrixInterreductionMethod::TailsOnly` (#879). It cannot move these rows further. The stage
is still ≥ 10% of wall on all three rows (11.0% / 13.1% / 10.5%), so it was re-read:

- **Katsura-11:** Zeebra 110 ms against grobx 7 ms (15.3×), on matrices of the same size: 1,561 and
  1,569 columns, 0.39 M nonzeros each. grobx charges 1.4 M products. The arithmetic is at most a few
  ms, so roughly 100 ms is construction and conversion. That is the minimal selection (9 ms), plus
  rebuilding a matrix from polynomials and back.
- **Eco-12:** 274 against 136 ms. Zeebra's matrix is wider (9,773 against 6,379 columns), and its
  minimal selection runs over 1,885 elements (27.5 ms), 1,142 of them redundant.
- **MQ11:** 512 against 216 ms, at equal matrix dimensions.

Materialization (signature basis to `MultivariatePolynomial`, 62 / 19 / 76 ms) feeds this stage, and
interreduction then re-interns every term. Candidate 2 removes that round trip.

## 7. Design 2 at one CPU (Q5, #894)

#894 found conventional F4's concurrent forward kernel about 10% cheaper than the serial one at one
CPU on Katsura-11. **The signature route does not use either kernel.** Its elimination is
`sigf4::engine::Workspace::reduce`. The route's analogue is design 2, which first reduces every
target against the reducer block in a pass of its own. `sig-w4` ÷ `sig` on one CPU:

| Row | elimination | wall |
|---|---:|---:|
| Eco-12 | 1.226 [1.215, 1.241] | 1.116 [1.109, 1.128] |
| Katsura-11 | 1.010 [0.989, 1.023] | 0.995 [0.988, 1.020] |
| MQ11 | 1.037 [1.029, 1.047] | 1.028 [1.020, 1.030] |

There is no serial win: it is level on Katsura-11 and slower elsewhere. #894's effect is specific to
the conventional kernel and does not transfer.

## 8. Exact zero avoidance (Q6, #955)

The ceiling is the zero rows' products at Zeebra's own per-product cost: 336 M × 2.18 ns ≈ 732 ms on
Eco-12 (29% of wall), 177 ms on Katsura-11 (21%) and 1,806 ms on MQ11 (37%). A costed exact design
must pay for the following.

1. **A per-row exact audit is the reduction itself.** #714 measured grobx's native residual audit
   at 1.30× *slower* than deterministic plain reduction. That design nets ≤ 0 by construction.
2. **The signature route consumes its zero rows.** Each one inserts a syzygy signature, and those
   signatures reject 689,359 / 32,474 / 108,247 later pairs (`rejected_zero_row`). A wrong
   randomized zero test does not only miss a pivot: it plants a false syzygy that silently prunes
   pairs. That is detectable only by certification, at 2–67× the solve per #955, or by a Hilbert
   function check.
3. **A per-degree Hilbert-function check is exact and cheap only where the series is known a
   priori**, as for a regular sequence such as dense square MQ. Once a degree's batch is done, its
   new leading monomials can be counted against H(d). That certifies the degree, so every
   randomized "zero" in it was zero, at the cost of a count.
   - On **MQ11** it could recover most of grobx's advantage. grobx's elimination is 2,510 ms against
     Zeebra's 3,502, so the predicted gain is ≤ ~1.0 s (≤ 20% of MQ11's wall), less the test's cost.
   - On **Eco-12** no series is known in advance. A second-prime Hilbert computation is Monte Carlo,
     not exact.

**No exact design is costed positive on Eco-12, so none is proposed for G2.** The MQ11 route,
Hilbert-certified randomized zero tests on regular inputs, is #955's research question 1. It is
recorded there as a costed lead, not as an M33 candidate.

The 35% of Eco-12 products on redundant elements cannot be removed exactly either. Those elements
carry signatures the route needs, and discarding dominated signature elements is refuted (§4.3:
3.1% of Eco-12).

## 9. Ranked candidates (additive per-row estimates from the medians above)

| # | Mechanism | Evidence | Eco-12 | Katsura-11 | MQ11 | File scope | Lines | Risk to controls |
|---|---|---|---:|---:|---:|---|---:|---|
| **1** | **Persistent monomial table for symbolic preprocessing**: one id per monomial for the run, a hash additive under multiplication, the batch column stored in the entry, terms of basis elements kept as ids | symbolic 5.1–9.7× grobx's; interning 61–84% of it, 12–25 ns per term | **−250 ms (−10.1%)** | −87 (−10.4%) | −224 (−4.6%) | `src/grobner/sigf4/engine.rs` (symbolic, row building), new `sigf4/table.rs` | 400–600 | the table only grows: memory on Noon-8 and Cyclic-7; exact, digests unaffected |
| 2 | **Interreduction in the engine's column space**: interreduce from the engine's sorted rows, skipping materialization and re-interning | Katsura-11 interreduction 15× grobx's at equal matrix size; materialize 19–76 ms | −128 (−5.2%) | −110 (−13.2%) | −269 (−5.5%) | `sigf4/engine.rs` (`interreduce`, materialization) | 300–500 | must keep the division fallback and the budgets (#962) |
| 3 | Cheaper criteria checks (base divisors and a pair bit-triangle, Roune & Stillman 2012) | Eco-12 bookkeeping 45× grobx's, 1.78 M pairs from 1,885 elements | −150 (−6%) | ~0 | ~0 | `sigf4/engine.rs`, `signature.rs` | 300 | Eco-12 only; touches every criterion |
| 4 | Hilbert-certified randomized zero tests | MQ11's 562 test-ruled rows (§8) | 0 (no series) | — | ≤ −1,000 (≤ −20%) | `sigf4/engine.rs` | 600+ | #955 owns it; regular inputs only |
| — | Unfused multiply-then-intern (#939/#964) | §5 | −4.8% | +3.4% | +2.2% | | | fails HG2 |
| — | Faster digest | 84 ms against grobx's 11 ms text | −2.9% | −8.2% | −4.7% | harness (`examples/support/basis_digest.rs`) | | timed-region change, plan §11.3; not a library candidate |

How the estimates are derived:

- **Candidate 1:** symbolic falls to ≤ 2.0× grobx's stage on Eco-12 (454 → 204 ms) and Katsura-11
  (158 → 71). MQ11 is held to half its stage. Elimination setup also builds rows from handles, and
  any saving there is not counted.
- **Candidate 2:** interreduction falls to 1.3× grobx's, plus half of materialization.

The two are additive: they touch different stages. Together they predict Eco-12 at 2,484 − 378 =
2,106 ms in this session's units, which is about 1.32× grobx.

## 10. Gate A record proposed for #971

**G2-1: persistent monomial table in the signature engine's symbolic preprocessing.**

- **Current bottleneck (measured):** symbolic is 454 ms of Eco-12's 2,484 ms (grobx: 89 ms, 5.13×
  [4.99, 5.22]). Interning is 61% of the stage at 11.8 ns per term on Eco-12, and 82% at 25.2 ns per
  term on Katsura-11. Records: job `4004a790e353`.
- **Hypothesis (falsifiable):** most of the stage is per-batch rehashing and re-interning of
  products. One table with additive hashes and an in-entry column removes it: Eco-12 symbolic paired
  ratio ≤ 0.45, with elimination and interreduction within 1.03.
- **Predicted gain:** Eco-12 1-w wall −250 ms, **−10.1%** (≥ 8%). Katsura-11 −10.4%, MQ11 −4.6%. Ceiling with the stage at grobx's level: Eco-12 −366 ms (−14.7%).
- **Falsified if:** at Gate B the Eco-12 paired wall upper bound is > 0.95, or the symbolic ratio is
  > 0.45, or Katsura-11's wall upper bound is > 1.00.
- **File scope:** `src/grobner/sigf4/engine.rs`, a new `src/grobner/sigf4/table.rs`;
  `src/poly/multivariate/monomial_hash.rs` is read-only.
- **Line estimate:** 400–600.
- **Not in §4.3.** Packed exponents, reducer-search indexes and the stitch walk are different
  mechanisms. The reducer search is 22 ms here.
- **Provenance:** the mechanism is Monagan & Pearce (2015) §2.1 and Faugère's F4 implementation
  practice, re-derived from the papers. grobx was read for attribution only.

Candidate 2 does not reach 8% on Eco-12 (−5.2%), so no Gate A record is posted for it. Whether a
Gate A may name Katsura-11 (−13.2%) as its target row is an owner decision on #965.

## 11. What this does not show

- The 1.43 GHz clock readings are a sampler artifact by the counted cycles. The rule's treatment of
  them is the owner's decision on #965.
- The probe-length hypothesis for Katsura-11's interning cost (§5) is unmeasured.
- The interreduction attribution beyond the minimal selection is by subtraction.
- **Sessions:** 1 of the 4-session cap, plus untimed counter runs.
- **Instrumentation:** 80 net lines under `src/` and `examples/`, all under `research-sigf4-split`;
  the timed `sig` build compiles none of it. The research scripts add about 700 lines, outside the
  cap as #966 read it.
