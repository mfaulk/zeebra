# XL and block Wiedemann: a differently-posed problem, priced from construction

**Measured at:** not measured here — no solver runs and no matrix is built. Every XL figure is an
exact combinatorial count from `examples/xl_dimensions.rs`, reproducing bit-for-bit; the F4
comparands are measurements transcribed from `research/scoreboard/runs/` and cited in
[`mq-comparison-methodology.md`](mq-comparison-methodology.md) §7; the external figures are
published attacks' own reported numbers.

Reference for **#76 (B3)**, a child of epic #66. The comparison it is measured under is #77's,
written in `mq-comparison-methodology.md`; the epic required that to exist first and it now does.

## 1. This does not reopen #58, and the distinction is the whole point

#58 is a decision record: **Wiedemann is won't-do for F4's echelonization.** That reasoning stands
and is not revisited. F4's output *is* the transformed matrix, its matrices are deliberately
rank-deficient, and the operator is destroyed by the computation — so the black-box model does not
apply.

XL is a different algorithm with a different output, which is exactly why it is worth pricing
separately:

| | F4 echelonization | XL + block Wiedemann |
| --- | --- | --- |
| output | row-space basis in echelon form; polynomials read off by leading monomial | a vector in the kernel / a solution to a linear system |
| matrix role | transformed **in place**; the rank defect is the answer | a **fixed** black-box operator, applied repeatedly |
| rank | deliberately rank-deficient | the nullspace is the object of interest |

**So block Wiedemann is not a drop-in replacement for F4's elimination.** It is the linear-algebra
engine for a differently-posed problem. Conflating the two is the likely failure mode and is what
this section exists to prevent.

## 2. What is priced, and why no solver is needed

#76's go/no-go says the answer is reachable without one:

> **No-go** if XL's matrix is larger than F4's for every degree at which it could succeed — a result
> obtainable from **construction alone**, without a solver.

XL multiplies each equation by every monomial of degree at most `D - 2` and treats the products as
linear in the monomials of degree at most `D`. At a chosen `D` that fixes the shape exactly:

- **rows** = `m` x |monomials of degree <= `D - 2`|
- **columns** = |monomials of degree <= `D`| — the linearized unknowns
- **nonzeros** = rows x |monomials of degree <= 2|, a dense quadratic's coefficient count

All integers. No floating point, no timing, no lock.

**The operating degree is not a free parameter.** XL pins the monomials down only once the equations
it has generated leave essentially no residue classes, and the semiregular model is what predicts
that — already in the crate as `SemiregularSeries::quadratics`, the series
`(1 - z^2)^m / (1 - z)^n`, whose **degree of regularity** is "the first degree at which a
semiregular sequence is predicted to have no residue classes left". That is a *prediction*, labelled
as one wherever it appears below; [`hilbert-functions.md`](hilbert-functions.md) §3 records where the
model fails and in which direction.

### 2.1 The construction is checked against the published record-holder

The instrument asserts two things before printing anything, because every figure is linear in them.

**The term count, against a real file.** `fukuoka-mq.md` §4 records the type III `n = 10` import as
"parses, **66 coefficients** x 20 polynomials". Monomials of degree at most two in ten variables is
66. Were that wrong, every row would be wrong by one factor and nothing would look odd.

**The column count, against the record-holder's own matrix.** eprint 2026/2641 is the XL + block
Wiedemann implementation that holds the Fukuoka **type III `n = 38`** record, and it reports its
matrix as **`N = 45 379 620` columns**. This harness predicts the operating degree from the
semiregular model with no knowledge of that paper, then counts columns combinatorially, and lands on
**45 379 620**. Both halves are therefore checked at once: the degree the model picks for `n = 38`
is the degree the implementation used, and the count is right.

That agreement is the reason the rest of this document can be believed without a solver.

## 3. XL's matrix against F4's measured peak

Determined systems, `m = 2n` quadratics in `n` variables, as type III publishes. Both sides priced
in the same unit — a live sparse entry at 16 bytes, the quantity `max_live_bytes` spends.

| n | m | D (predicted) | XL rows | XL columns | XL nonzeros | XL sparse bytes | F4 measured peak entries | XL / F4 |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 10 | 20 | 4 | 1 320 | 1 001 | 87 120 | 1.3 MiB | 168 020 | **0.52x** |
| 15 | 30 | 4 | 4 080 | 3 876 | 554 880 | 8.5 MiB | 2 143 983 | **0.26x** |
| 20 | 40 | 5 | 70 840 | 53 130 | 16 364 040 | 249.7 MiB | 12 212 087 | **1.34x** |
| 24 | 48 | 6 | 982 800 | 593 775 | 319 410 000 | **4.76 GiB** | 14 329 816 | **22.29x** |
| 38 | 76 | 7 | 73 157 448 | **45 379 620** | 57 062 809 440 | **850.30 GiB** | — | — |

The `n = 24` F4 figure is the type VI `m = 16` run rather than a type III one, since that is the
rung Zeebra has at that width; `n = 38` has no Zeebra figure at all.

**The cost climbs about an order of magnitude per degree**, which is why the operating degree carries
the whole result. At `n = 24`:

| D | predicted `H(D)` | XL nonzeros | XL sparse bytes | usable? |
| ---: | ---: | ---: | ---: | --- |
| 2 | 252 | 15 600 | 244 KiB | no — residue classes remain |
| 3 | 1 448 | 390 000 | 6.0 MiB | no |
| 4 | 4 278 | 5 070 000 | 77.4 MiB | no |
| 5 | 552 | 45 630 000 | 696.3 MiB | no |
| **6** | **−46 276** | **319 410 000** | **4.76 GiB** | **yes** |

`H(D)` is the *untruncated* expansion, so the sign of the first non-positive term is visible rather
than clamped — that term is what the degree of regularity is defined by. A prediction wrong by one
degree moves the XL column by an order of magnitude, in either direction.

## 4. The go/no-go, answered — and neither branch fires cleanly

> **Go** if the measured XL matrix at the required degree fits a workstation memory budget and F4's
> peak on the same instance is worse. **No-go** if XL's matrix is larger than F4's for every degree
> at which it could succeed.

**The no-go condition is not met.** XL's matrix is *smaller* than F4's measured peak at `n = 10`
(0.52x) and `n = 15` (0.26x). So the flat refusal the go/no-go anticipated is not available.

**And the go condition buys nothing where it fires.** At `n = 10` and `n = 15` F4 already *solves*
the instance — 114 ms and 7.8 s, verified witnesses, `D = 1` — so a smaller matrix is a smaller
matrix for a problem that is not hard. XL's advantage exists exactly where there is nothing to win.

**The crossover is between `n = 15` and `n = 20`**, and from there XL loses: 1.34x at `n = 20`,
22.29x at `n = 24`, and 850 GiB at `n = 38` — which exceeds this machine's 503 GB of RAM outright
and is why the published implementation uses block Wiedemann at all. A dense elimination of that
matrix is not a thing anyone could do; an `O(n)`-memory black-box iteration over it is.

### 4.1 The one reading that is genuinely favourable, stated carefully

At `n = 24` — the first *real* challenge, and the rung where **F4 refused** — XL's matrix is
**4.76 GiB**, which is comfortably inside the §9 authorization ceiling of ~64 GB peak RSS and a
rounding error against 503 GB of RAM. F4 on that instance stopped at the 20 000 000-entry cap
needing 20 010 753 at degree 6.

So on the one rung where F4 does not finish, **XL's matrix is affordable and F4's live set was
not.** That is the strongest thing this document can say for the direction, and it needs three
caveats to stay honest:

1. **An affordable matrix is not a solve.** This prices *storage* at the operating degree. Block
   Wiedemann then needs roughly `O(n)` sparse matrix-vector products over it plus a
   Berlekamp–Massey step, and the operation count is not measured here and is not bounded by
   anything above. A 4.76 GiB operator applied tens of thousands of times is a different question
   from a 4.76 GiB allocation.
2. **The degree is predicted, not observed.** `D = 6` comes from the semiregular model. The model
   underestimates on structured systems — `hilbert-driven.md` §3 reports it 27x wrong on Poseidon —
   and type III is random, which is where it is most likely to be sound, but "most likely" is not
   "measured".
3. **F4's cap is a configured budget, not a hardware limit.** F4 refused at 20 000 000 entries
   because that is what `max_live_nonzeros` is set to, and #453 established that raising it does not
   advance the degree — the demand at degree 5 exceeded 40 000 000 too. So the comparison is between
   XL's *known fixed* requirement and F4's *unbounded* one, which favours XL in kind and not only in
   size.

## 5. The recommendation

**Not a route to the published record on this machine, and worth keeping for one narrow reason.**

Against the record: `n = 38` needs 850 GiB of sparse entries, 550x beyond Zeebra's largest matrix to
date. The published type III result took 23.34 days with `VmPeak` 49.45 GB on 2x EPYC 7742, and the
type II `n = 38` result over `F256` is presented as an **estimate rather than a completed solve**.
Nothing about that is reachable here, and M27-D's gate must not treat it as though it were.

What survives is narrower: **XL is the only candidate whose cost at the rung where F4 refuses is
both known and affordable.** That is worth revisiting if and when the `n = 24` rung becomes the
target, and it is not worth building now, because:

- the prerequisite is a **Berlekamp–Massey implementation**, which does not exist
  (`fglm/shape.rs` records it as missing), plus a block-Wiedemann driver and a solution-recovery
  step;
- the sparse matvec it needs is the shape `MultiplicationOperator::apply` already has, so the
  linear-algebra half is less work than the rest; and
- #77's metric is time and peak bytes **to a verified solution**, and an XL route produces a kernel
  vector that still has to be turned into a point and substituted into the published system.

### 5.1 Berlekamp–Massey is a shared prerequisite, and that changes its priority

#58's second half names Berlekamp–Massey as missing and lists block Wiedemann plus Faugère–Mou
machinery as the prerequisite for the general FGLM case; #368 (M26-B) wants a certified
Krylov/Wiedemann order conversion whose stage 2 is "scalar Wiedemann, Berlekamp–Massey, and
shape-position reconstruction". **One implementation serves #58's FGLM case, #368's conversion and
this issue's XL route.** It should be costed once against all three rather than three times against
each, and this document records that as the reason its priority is higher than #76 alone would
justify.

## 6. What this does not establish

- **No XL solve was attempted**, and no claim is made that one would succeed at any rung. §3 is
  storage at a predicted degree.
- **No operation count.** The matvec count, the Berlekamp–Massey cost and the recovery step are all
  unpriced. The memory profile is the reason XL appears in these records; the operation count is the
  reason it takes 23 days when it works.
- **No comparison with the published figures.** 23.34 d on 2x EPYC 7742 and 811 805 s on 2x EPYC
  7763 are published facts about those instances, not comparands — `mq-comparison-methodology.md` §6
  and the absolute rule it cites.
- **Nothing about GF(2^8).** Type II is the `F256` family and `Gf256Mq` exists, but the type II
  rungs are not importable (`SUPPORTED_DIMENSIONS` stops at 24 and type II starts at `n = 35`), so
  this document prices GF(31) only. The field changes the entry size not at all — a sparse entry is
  16 bytes at either width, per #218 — and changes the arithmetic cost, which is unpriced here.

## 7. Reproducing

```sh
cargo run --release --example xl_dimensions            # the default rungs: n = 10, 15, 20, 24
cargo run --release --example xl_dimensions -- 38      # the published record's instance
```

No lock, no build flags and no machine state matter: the figures are integer counts. The two
self-checks of §2.1 run before anything is printed, so a run that prints at all has reproduced the
published `n = 38` column count and the published `n = 10` coefficient count.
