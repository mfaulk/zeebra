# M24 — Published Attack Reproduction and Cryptanalytic Frontier Extension

**Measured at:** publication bound `95a1558d`…`900af4e7` — the commits that published these figures,
recovered from git rather than recorded at the time ([§10](research/external-comparison-protocol.md#10-the-commit-and-what-a-publication-bound-is)).

**Status:** complete. **Minimum and Strong met, Stretch not met** — §13.1 scores each against the
criterion written before the work started. Every figure in this document is reproducible from §16;
§10.1 records which of its own predictions held and which did not.
**Prerequisite:** M23, merged; #162 stage 1, #124, #161, #175, #188 and #191 merged
**Research issues:** #80 (C3, published attack reproduction), #84 (D3, Graeffe), #82 (D1), #85 (D4),
#179, #180 (resultant stages), #65, #73 (benchmark corpus and schema), #189, #185 (instrument fixes)

M23 changed the unit of progress from an optimization to a problem. M24 changes what is allowed to
count as progress on a problem: **a result is either a reproduction of something published, or a
witness for a registered instance nothing public has a witness for.** Everything else is
infrastructure.

The reason is the one M23 found and did not plan for. §5b.4 of
[`MILESTONE-CRYPTANALYSIS-SCOREBOARD.md`](MILESTONE-CRYPTANALYSIS-SCOREBOARD.md) measured a 578x
difference between two ways of writing the *same* registered CICO slice, and the post-M23
interpolation fix turned that into a frontier extension — two rounds to four — without touching F4
at all. Nothing in M17–M22's optimization work moved a frontier. One change of formulation moved it
twice. So the next milestone is not a kernel milestone.

---

## 1. What this milestone is actually blocked on

Not compute, and not kernels. Reading.

> **Zeebra can execute the published `R_P = 8` attack's hardest stage and cannot explain the
> published attack's cost.** `examples/graeffe_root.rs` finds roots of a degree-`3^13` polynomial
> over KoalaBear in **3.11 s** — the exact degree the disclosed CICO-2 `R_F = 6, R_P = 8` solution
> works at. `docs/research/graeffe-root-finding.md` §9.3 then derives **≈`2^31` families** for a
> witness, which at §9.2's ~2 minutes a family is ~8 100 core-years. Sanso–Vitto Table 1 reports
> that instance solved in **7 hours on 96 GPUs**.

Those two cannot both be right, and the gap is about four orders of magnitude after any plausible
GPU factor. The document says so itself and marks §9.2–§9.3 *superseded pending verification*. Three
candidate explanations are on the record and none has been checked:

1. `P_1` is not root-count-generic the way §9.3 assumes.
2. The `(1,[1])` parametrization supplies more usable freedom per family than one variable.
3. "Common-root strategy" — the paper's own phrase — does more than independent `1/p` filtering.

**A reproduction cannot be built on top of an unresolved factor of `2^31`.** Writing
`cico_univariate`, running one family, and reporting a per-family cost would produce a correct
measurement of something whose relationship to the published attack is unknown. That is the failure
mode M23-C was designed to prevent on the Gröbner side and it applies here unchanged.

So M24 opens with a reading gate, not an implementation.

### 1.1 The second thing it is blocked on, and this one is cheap

The resultant route's cost is **one stage**: 99.0% of the four-round row is 16 384 order-162
Sylvester determinants, on **one core of 128** (#180). Two independent reductions of that single
stage are specified, measured-against and unimplemented — #179 cuts the number of determinants,
#180 cuts the wall-clock cost of the remainder — and they multiply. Nothing about either is
algorithmically deep. That is the cheapest route to a harder verified witness this repository has.

---

## 2. The external position, re-stated for M24

Unchanged from M23 §1 on the bounty side: the three 2026 Poseidon-31 CICO targets are solved
externally and the program is closed, so **the best available outcome on them is a reproduction**.
What M24 adds is the per-target method, read out of the papers rather than inferred
(`docs/research/elimination-beyond-grobner.md` §2):

| registered target | verified | published method | reported cost | source |
|---|---|---|---|---|
| `poseidon31-cico-rf6-rp6` | 2026-04-10 | Villard-style bivariate resultant, one full round skipped | 1 d 17 h on 128 CPU cores | 2026/1905 |
| `poseidon31-cico-rf6-rp8` | 2026-05-06 | `(1,[1])` round skip + interpolation + Graeffe root finding, **no resultant** | 7 h on 96 RTX 5090 GPUs | 2026/1254 |
| `poseidon31-cico-rf6-rp10` | 2026-07-06 | none located | — | — |

**The publications establish successful attacks at these parameters; they do not establish that they
are the submissions the EF verified on those dates.** The programme names no first submitters. M24
inherits that caveat verbatim and must not launder it.

And the finding that bounds every Gröbner claim in this milestone, from 2026/1905 §5.2 on a
`t = 4, R_F = 2` ladder, single-threaded, all three methods on the same instances:

| `R_P` | Gröbner (Magma `Variety`) | evaluation–interpolation | Villard resultant |
|---:|---|---|---|
| 4 | **1 d 3 h**, 4.6 GB | **13 s**, 0.006 GB | **11 s**, 0.1 GB |
| 5 | did not reach | 3 m 39 s | 1 m 14 s |
| 8 | did not reach | 2 d 7 h | 5 h 18 m |

7 500x at the only row all three reach, and Gröbner cannot reach the next one. **The registered 2026
CICO-2 targets are not a fair arena for Zeebra's architecture**, which is exactly why M24-C adds an
arena that is (§6).

---

## 3. The three questions M24 answers

M23's two questions stay and a third is added, because M23's own report could not answer it.

1. **What public problem can Zeebra solve, and is that solve a reproduction or a first?**
2. **For a problem it cannot solve, where exactly does the computation stop, and which stage got
   cheaper?**
3. **For a problem someone else solved, does Zeebra's cost model explain their result?** A
   reproduction that runs is worth less than a reproduction that predicts, and §1 is a case where
   the prediction is off by `2^31` and nobody noticed until two documents were put side by side.

---

## 4. Sub-milestones

| phase | workstream | deliverable | gate |
|---|---|---|---|
| M24-0 | source-grounded attack specification | 2026/1254 §4.2 read directly; the family-count discrepancy resolved or the direction redirected | **gates M24-A only** |
| M24-A | univariate CICO attack reproduction | the `(1,[1])` parametrization, `cico_univariate`, one family end to end on reduced rows, per-stage costs | M24-0 |
| M24-B | resultant frontier extension | #179 and #180 measured apart and together; the six-round `rf2-rp4` attempt under an explicit budget | none |
| M24-C | external Anemoi calibration | the permutation, `FCICO`/`PCICO` models, a registered ladder, and the published rows reproduced or attributed | none |
| M24-D | resource scaling and instruments | an F4 budget ladder on two problems; #189, #185 and `tools/benchlock.sh` | none |
| M24-I | verification and report | scoreboard, history, comparison against published work, the negative results, the next frontier | all |

M24-B, M24-C and M24-D are independent of M24-0 and of each other and can run in parallel. **Only
M24-A is gated**, and it is gated on reading rather than on code.

### 4.1 The issues, and the dependency order

Everything carries the `M24` label.

| phase | issue | depends on |
|---|---|---|
| M24-0 | **#208** read 2026/1254 §4.2 and resolve the `2^31` family-count discrepancy | — |
| M24-A | **#209** the `(1,[1])` parametrization and `cico_univariate` | #208 |
| M24-A | **#210** `examples/graeffe_cico.rs` — one family end to end, and the family economics | #209 |
| M24-B | **#179** predict the sample count from `3^{2R_F+R_P}` | — |
| M24-B | **#180** parallelize the Sylvester determinants, and record the concurrency | — |
| M24-B | **#211** the six-round attempt on `rf2-rp4` under an explicit budget | #179, #180 |
| M24-C | **#212** the Anemoi permutation and its derived round constants | — |
| M24-C | **#213** `FCICO`/`PCICO`, the `AnemoiCico` registry variant, a reference-point record | #212 |
| M24-C | **#214** run the ladder: quotient dimension first, stage split second, wall times last | #213 |
| M24-D | **#215** an F4 live-entry budget ladder on two problems, with a stop rule | #216 |
| M24-D | **#216** commit `tools/benchlock.sh` | — |
| M24-D | **#189** the `fftmul` stage verifies against schoolbook and never finishes past `2^20` | — |
| M24-D | **#185** dispatch schoolbook → Karatsuba → NTT | — |
| M24-I | **#217** scoreboard, cost-model table, negative results, report | all |

Parent epics and the research children they close against: #80 (C3) by #208–#210, #84 (D3) by
#209–#210, #82 (D1) and #85 (D4) by #179, #180 and #211, #65 and #73 by #212–#214.

Four chains run concurrently: `#208 → #209 → #210`, `{#179, #180} → #211`,
`#212 → #213 → #214`, and `{#216 → #215, #189, #185}`. Only the first is gated on reading.

---

## 5. M24-0 — the gate

### 5.1 What to read, and what to extract

Source: **2026/1254**, Sanso–Vitto, *Top Gun: Degree Annihilation Attacks on Poseidon*, §4.2 and
whatever §2–§3 §4.2 depends on. `docs/research/graeffe-root-finding.md` §1 records the retrieval
route that works from this environment — the Wayback Machine's raw-content form,
`https://web.archive.org/web/<ts>id_/https://eprint.iacr.org/2026/1254.pdf`, where the `id_` suffix
is essential — because `eprint.iacr.org/*.pdf` returns 403 here.

Five extractions, each of which is a number or a construction and not an impression:

1. **The `(1,[1])` parametrization, written out.** The degrees of freedom it carries, the output
   constraints it forces by construction, and the family-generation procedure. `(1,[1])` names a
   skip of one full round with one skipped S-box; the construction for Zeebra's hybrid
   `permutation_plus_linear` has to be derived from it, and §5.3 says why that derivation is itself
   a deliverable.
2. **The expected `F_p`-root count of `P_1`.** §9.3 assumes ≈1 from "behave like random
   polynomials". If the parametrization forces `P_1` to split more than a random polynomial does,
   the family count falls by that factor.
3. **What "common-root strategy" denotes operationally.** If it couples the two constraints rather
   than filtering candidates against the second independently, the `1/p` factor in §9.3 is wrong
   and the whole discrepancy may be this one term.
4. **The total-work model's measured terms.** `W_total = W_pre + Σ_i (W_control,i + W_poly,i +
   W_root,i + W_check,i)`. Which of these the paper reports, and the `N` it reports them over.
5. **Whether the 7 h / 96 GPU figure is a single run or an extrapolation.** Table 1 marks three
   rows "est." because execution logs were lost. The CICO-2 row's status decides how much weight
   the discrepancy carries.

   > **Corrected, 2026-11-06, by the reading this section asked for.** This said *four* rows, which
   > was written from `elimination-beyond-grobner.md` at second hand. It is **three**, and all three
   > are ZeroTest — so the CICO-2 row is a reported run and the discrepancy carried full weight
   > rather than less. See §5.4.

### 5.2 The go/no-go, stated before reading

**Go** if (1) through (4) are recoverable from the text, and the resulting family count is within
two orders of magnitude of the published cost once GPU parallelism is accounted for. M24-A proceeds.

**No-go** if the parametrization or the family-generation procedure cannot be reconstructed without
guessing. Then:

- Record exactly what is missing, in `docs/research/` and in the issue, at the level of detail §2 of
  `additional-benchmarks.md` used for Griffin's `(δ, µ)` ambiguity — a named ambiguity with the
  readings that were tried.
- Redirect M24-A's effort to the **public Bak–Hostettler implementation**, `PoseidonCicoTwo`, which
  `elimination-beyond-grobner.md` §6.3 already recommends for D4 (#85): it contains single-threaded
  evaluation–interpolation, Villard resultants *and* Gröbner comparisons, with §2's measurements to
  check a local run against. A reproduction of someone else's *code* against their own published
  numbers is a weaker result than a reproduction of their attack and a much stronger one than a
  guessed attack benchmarked as a reproduction.

**Do not build a guessed attack and then benchmark it as a published reproduction.** This is the one
prohibition in M24 with no exception clause.

### 5.3 The hybrid-permutation derivation, which is a deliverable either way

`permutation_plus_linear` is not Poseidon and not Poseidon2. `graeffe-root-finding.md` §2.3 records
it as a hybrid with Poseidon2's initial linear layer, Poseidon's same-MDS-every-round, and
all-state round constants in the partial rounds, and marks the skip count **reconstructed** —
"the paper states the rule for Poseidon and for Poseidon2, not for this hybrid, and no source read
here states the hybrid case".

Two independent readings of two different papers agree that the degree is `3^{R_F+R_P−1}` and give
`3^11`, `3^13`, `3^15` on the three registered targets. The *degree* is therefore safe. The
*construction* — which `y_i` are set to what, in terms of the last row of `M_E^{-1}` — is not, and
M24-A's first test is the one that settles it: **the parametrized family's constrained coordinate
must be identically zero when evaluated through `permutation_plus_linear`**, at many random points.
A construction that is wrong for the hybrid fails that test at the first point.

## 5.4 What the gate returned: **go**, and `2^31` was never the error

2026/1254 was read directly (#208, PR #228). The verdict is **go** against §5.2's criterion, and the
reconciliation is the milestone's first answer to §3's third question.

| extraction | verdict |
|---|---|
| (1) the `(1,[1])` parametrization, written out | recovered — §2.2, generalized at §3.2 |
| (2) expected `F_p`-root count of `P_1` | recovered — and it **confirms** §9.3's ≈1 |
| (3) what "common-root strategy" denotes | recovered — and it **confirms** §9.3's `1/p` |
| (4) the total-work model's measured terms | `UNVERIFIED — not stated`, and unavailable *in principle*: §4.2 records the execution logs as lost |
| (5) a run or an extrapolation | a reported **run** |

**Both of §9.3's inputs survive, so `≈2^31` families stands.** The paper endorses the
random-polynomial heuristic for `P_1` and defines its strategy as Graeffe root finding plus one
permutation evaluation per recovered root — independent filtering, not a coupling. Two of the three
candidate explanations are refuted on the record; the third is not needed.

The factor was in **§9.2's per-family cost**, and in the comparison itself:

```
corrected per family      12 + 0.09 + 3.11  ≈ 15.2 s      (not ~120 s)
work at N = 2^31                            ≈ 1 036 core-years
published                 7 h × 96 GPUs     =   672 GPU-hours
implied per-GPU factor over one core        ≈ 1.35e4
```

§9.2's ~2 minutes charged every family a ~100 s `r = 2^24` subgroup scan that belongs to Zeebra's
*single-root descent* and not to a loop filtering ≈1 root — a stage the published attack does not
run, and whose `W_check` the paper itself calls negligible. Residual after that: **≈13x** at a `10^3`
per-GPU factor, 43x at `10^2.5`, 135x at `10^2`. So the gap is inside two orders of magnitude for
any per-GPU factor above ≈140.

> **The error was two separable mistakes, and neither was the family count: comparing core-years
> against a wall clock, and charging the published loop for a stage it does not perform.**

Independently anchored: 2026/1905 Table 4 gives `R_P = 6` at 1 d 17 h and `R_P = 7` at 21 d 5 h on
128 cores — a 12.4x step per partial round, putting `R_P = 8` at ≈92 core-years by the *resultant*
route. Two unrelated methods bracket the instance at `10^1`–`10^2` core-years against this route's
`10^3`.

**What this does not license.** The univariate route at the official `R_P = 8` is ~10^3 core-years
and therefore out of reach, exactly as `graeffe-root-finding.md` §9.4 requires to be said. M24-A's
deliverable is unchanged — one family end to end on reduced rows, class `Engineering { why }` — and
is now backed by a cost model that has been reconciled against a published result rather than left
disagreeing with one. The `10^2`–`10^3` per-GPU throughput factor is an estimate, not a measurement,
and the verdict's margin depends on it.

---

## 6. M24-A — one family, end to end

### 6.1 What exists and what does not

`graeffe-root-finding.md` §9.1 is the component table and **eleven of fourteen components exist**.
Three remain, and only two are in scope:

| # | component | status | scope |
|---:|---|---|---|
| 3 | the round-skipping parametrization | **absent** — needs `M_E^{-1}`'s last row and the affine construction | **M24-A** |
| 5 | construction of the degree-`δ` univariate in the *evaluation* domain | absent at `δ = 3^13`; present symbolically at `k = 1` via `cico_bivariate`'s pattern | **M24-A** |
| 13 | mixed-radix NTT | absent | **out of scope** — needed only by `rf6-rp10`, whose method is undisclosed |

Everything else landed: NTT multiplication (#124), `graeffe_2`/`graeffe_l`/`graeffe_root` (#188,
corrected by #191), `sqrt` (#175), `fft::interpolate`, and `CicoInstance::is_solution` as the
verifier.

### 6.2 The deliverable, and what it is not

**One family, end to end, on reduced rows, with every stage timed separately.** Concretely:

1. `cico_univariate(instance, fixed) -> UnivariatePolynomial<F>` — the `k = 1` analogue of
   `cico_bivariate` (`src/grobner/research/resultant.rs:76`), built on the §5.3 parametrization.
   Symbolic at small `δ`; evaluation-domain at large `δ`, which is component 5.
2. `examples/graeffe_cico.rs` — a ladder over the registered reductions, each row reporting
   parametrization, polynomial construction, interpolation, Graeffe root finding, candidate lifting
   and verification as separate costs, plus **the number of base-field roots found and the number of
   candidates that pass the second constraint**.
3. Every witness checked by `CicoInstance::is_solution`, which runs `permutation_plus_linear`.

Three things it is explicitly not, carried over from `graeffe-root-finding.md` §9.4 because that
section exists precisely to stop these being misquoted:

- A working `GT_2` validated against squared roots is a **unit test**.
- A degree-`3^13` root-finding run in 3.11 s is a **benchmark of one stage of one family**.
- A successful Graeffe benchmark is **not a successful attack**, and the record's class is
  `BenchmarkClass::Engineering { why }` until it produces a witness verified through the
  permutation.

### 6.3 The measurement that decides whether this route is worth continuing

Not the per-family time. The **observed root count and filter rate**, against §5.2's extraction (2)
and (3):

| quantity | §9.3's assumption | what M24-A measures |
|---|---|---|
| base-field roots of `P_1` per family | ≈1, from "behaves like a random polynomial" | the observed distribution over many families on a reduced row |
| probability a root satisfies the second constraint | ≈`1/p`, independent | the observed rate, and whether the parametrization correlates them |
| families per witness | ≈`p` ≈ `2^31` | the observed count on a row small enough to finish |

A reduced row where a witness is actually reachable turns `2^31` from an estimate into a measured
ratio that can be extrapolated with a stated model. **That, not a wall-clock figure, is M24-A's
contribution to question 3.**

### 6.4 What was measured, and the row this section asked for does not exist

17 838 families over ten rows (#210, PR #235). Both assumptions hold, the third candidate
explanation dies, and **the table above asks for something impossible** — which is the result.

**Assumption 1 holds, distributionally and not just on average.** Pooled mean root count **0.9997**
against a predicted 1.0, and the whole distribution tracks Poisson(1): on `t16-rf4-rp0` over 3 000
families the no-root share is 0.3503 against `1/e = 0.3679`, which is 2026/1254 §2.2's `1 − 1/e`
reproduced directly rather than assumed.

**Assumption 2's independence holds; its rate is not measurable here.** `χ²` on the second
constraint's residual over 256 bins at 255 dof (sd ≈ 22.6) gives 202, 234, 234, 245, 278 across
rows — every one inside ±3σ, so conditioned on `P_0` vanishing the second constrained word is
uniform as far as the test can see, and the parametrization does not couple the constraints. The
*rate* is a different claim and is refused: 0 hits in 17 901 roots where `1/p` predicts `8e-6`, a
95% upper bound of `3/n ≈ 1.7e-4` that does not separate `1/p` from anything below it. **No run on
this hardware can measure that rate**, and the example says so in those words.

So all three of §9.3's candidate explanations are eliminated — extra freedom per family would have
had to show up either as extra roots or as correlated constraints, and neither appears — and
§5.4's per-family cost correction is the *whole* of the reconciliation.

> **The correction to this section.** §6.3's third row asks for "the observed count on a row small
> enough to finish". **There is no such row at `k = 2`, at any round count.** The family count is
> `p / (roots per family)`, which contains neither `R_F` nor `R_P`, and the ladder shows it
> directly: `δ` spans **6 561x** across these rows and the mean root count never leaves 1.0. So
> `N ≈ 2^31` on `t16-rf2-rp0` exactly as on the disclosed `rf6-rp8`.
>
> **Reducing rounds buys a cheaper family, not a cheaper search.** Zero witnesses on the nine
> `k = 2` rows, and none was available to be found.

Measured where it *can* be: `poseidon-t3-rf2-rp1-planted` is `k = 1`, so one output constraint is
all there is and a root of `P_0` **is** a witness — **1.00 families per witness, 3 witnesses verified
through `CicoInstance::is_solution`**, parametrization through verification end to end. That
calibrates the mechanism and isolates the `1/p` factor at `k = 2` as the entire difference between
`O(1)` families and `2^31`. It is also why the `k = 3` family and the hybrid that
`graeffe-root-finding.md` §9.3 leaves open are the only directions that could change the trade.

**One corroboration that came free.** `t16-rf6-rp4`, the only row above the symbolic crossover,
takes the evaluation route at `2^15`: construction 172.0 ms per family (**77%**), Graeffe 50.5 ms
(**23%**), interpolation 1.07 ms, lifting and verification µs. That reproduces 2026/1254 §4.2's own
stated ordering — construction and root finding dominant, the final evaluation negligible — and so
independently corroborates §5.4's central move, that the published per-family loop is those two
stages and nothing else, which is why §9.2's ~100 s candidate-scan row never belonged in it.

`δ = 3^13` is **not** reached; the largest row is `3^9`, four factors of three short. Nothing in
§6.4 is a per-family cost for `rf6-rp8`.

---

## 7. M24-B — the resultant frontier, from four rounds to six

### 7.1 Where the cost is, measured

`poseidon31-cico-t16-rf2-rp2`, four rounds, KoalaBear, seed 1, single core, under the benchmark lock
(#180, and `resultant-elimination.md` §6):

| stage | time | share |
|---|---:|---:|
| **16 384 order-162 Sylvester determinants** | **51 450 ms** | **99.0%** |
| inverse NTT interpolation | 2.1 ms | 0.004% |
| root finding | 59.5 ms | 0.11% |
| candidate lifting | 1.1 ms | 0.002% |
| verification | 0.0 ms | — |

Peak RSS 15.4 MB. One stage, one core of 128, and two orthogonal reductions of it specified.

### 7.2 #179 — predict the sample count

The route samples enough points to pin a polynomial of the Bézout degree `2d²`. The observed degree
is `3^{2R_F+R_P}`, which `resultant-elimination.md` §6.3 confirms on three registered slices
including one that discriminates it from both the Bézout bound and the other form the source gives:

| row | `R_F` | `R_P` | Bézout `2d²` | predicted `3^{2R_F+R_P}` | **observed** |
|---|---:|---:|---:|---:|---:|
| `rf2-rp0` | 2 | 0 | 163 | 81 | **81** |
| `rf2-rp2` | 2 | 2 | 13 123 | 729 | **729** |
| `rf4-rp0` | 4 | 0 | 13 123 | 6 561 | **6 561** |

The formula is **experimental and unproven in its source** — [JAZ] slide 22's own authors leave the
reason open. So: predict, sample `3^{2R_F+R_P} + 1` points, interpolate, and **verify against a
direct Sylvester determinant at several points outside the interpolation domain**. The off-domain
check already exists from the subgroup work. If it fails, that is a falsification of a published
formula and a result worth recording.

Pairing note from #179 that must not be got wrong: the predicted count is **730**, not a power of
two, so it pairs with arbitrary-point Lagrange and **not** with an NTT domain, which would round up
to 1 024 and give 14.1x instead of 22.4x. §6.4 of `resultant-elimination.md` proves the
interpolation can never dominate this route again, so there is nothing to trade away.

### 7.3 #180 — parallelize the determinants

Each of the samples is an independent determinant evaluation at one field element. Nothing is shared
and nothing is sequentially dependent. The in-repo idiom is `std::thread::scope`
(`src/grobner/differential/sweep.rs:242`); there is no rayon dependency and none is wanted.

Three constraints, and the third is the one that makes this different from #166:

- **Deterministic sample ordering.** The interpolation consumes `(x_i, det_i)` pairs; a concurrent
  evaluation must reassemble them in index order, not completion order.
- **Disjoint pinned core sets**, not N threads contending for the eight cores
  `tools/scoreboard.sh` pins by default.
- **Concurrency recorded in `Environment`.** #166 parallelized a sweep whose product was an
  agreement verdict, so concurrency could not affect the result and it was kept off the scoreboard.
  Here the product **is** the timing. `Environment` currently carries `commit`, `machine`, `cpu`,
  `build` and `policy` (`src/grobner/research/scoreboard.rs:516`) and no concurrency field;
  `Environment::comparable` and the JSON round-trip both have to learn about it, and every existing
  record has to keep parsing.

### 7.4 The six-round attempt, costed before it is authorized

Three registered rows are six rounds. The predicted sample count separates them by two orders of
magnitude and that is why only one of them is a bounded experiment:

| registered row | `R_F` | `R_P` | `d = 3^6` | predicted degree `3^{2R_F+R_P}` | samples | determinant order |
|---|---:|---:|---:|---:|---:|---:|
| **`poseidon31-cico-t16-rf2-rp4`** | 2 | 4 | 729 | `3^8` = 6 561 | **6 562** | 1 458 |
| `poseidon31-cico-t16-rf4-rp2` | 4 | 2 | 729 | `3^10` = 59 049 | 59 050 | 1 458 |
| `poseidon31-cico-t16-rf6-rp0` | 6 | 0 | 729 | `3^12` = 531 441 | 531 442 | 1 458 |
| *generic bound, any six-round row* | | | 729 | `2d²` | 1 062 882 | 1 458 |

`rf2-rp4` needs `2d²/3^8 = 2·3^4 = 162` times fewer samples than the generic bound — exactly 162x,
not approximately. **It is the only six-round row to attempt.**

Per-determinant cost, extrapolated from the measured 2.868 ms at order 162 (37 634.3 ms over
13 123 samples on the reference route) by the dense-LU `(2d)³` law: `(1458/162)³ = 729`, so
**≈2.09 s** per order-1458 determinant.

| stage | estimate | basis | confidence |
|---|---|---|---|
| symbolic bivariate build | **~36 min**, single-threaded | §7.5 | **extrapolated; the milestone's largest unknown** |
| 6 562 determinants, 1 core | 13 721 s = **3.81 h** | 6 562 × 2.09 s | extrapolated from a measured per-determinant cost |
| 6 562 determinants, 8 cores | **~29 min** | ideal scaling of the above | upper-bounded by #180's measured curve |
| off-domain check, 8 fresh points | ~17 s | 8 × 2.09 s | same basis |
| interpolation at 6 562 points | **~0.4 s** | `O(n²)`, from 1.51 s at 13 123 | measured law |
| root finding at degree 6 561 | **~4 s** | 3 933 ms measured on `rf4-rp0` | measured |
| lift and verify | ms | measured | measured |
| **total, 8 pinned cores** | **~1–1.5 h**, build and determinants roughly equal | | |

Peak memory is not a concern: a 1458² dense matrix of 8-byte elements is **17.0 MB**, so 136 MB
across eight threads, plus ~68 MB for sixteen symbolic state words of ~266 000 terms.

> **Wrong by 838x, measured 2026-11-06 (#211, `resultant-elimination.md` §6.8).** The build's peak
> is **57.0 GB**, not ~68 MB, and it is the only sentence in this document that was wrong by more
> than three orders of magnitude. The determinant half of the paragraph stands: 17.0 MB a matrix,
> and 544 MB across 32 workers.
>
> The mechanism was read rather than inferred. `SparseMultiPoly`'s multiply pushes every pairwise
> term-product into one `Vec` and collects like terms afterwards, so cubing a degree-243 word as
> `p*p` then `(p²)*p` makes the second multiply 118 827 × 29 768 = **3.54 × 10⁹** products —
> **56.6 GB** at sixteen bytes an entry, for a product that is 4.3 MB. Predicted 56.6 GB, measured
> 57.0 GB. The RSS trace is a **sawtooth with one peak per state word**, not a climb, so it is a
> transient four orders of magnitude larger than its own result rather than a leak — which is why
> 503 GB of RAM absorbed it. #243 is the collecting multiply that would bound it by the output.
>
> **What this does not change: the time, and therefore the gate.** The build completed in
> **48.37 min** against §7.5's ~36 min estimate — **1.34x**, inside the band that estimate deserved
> — and the row is a go on that basis. §7.5 named the build's *time* as the milestone's largest
> unknown and was right to; it did not list the build's *memory* as a risk at all, and that is the
> omission worth remembering.

**Authorize 6 562 samples on `rf2-rp4` with a four-hour wall-clock backstop. Authorize nothing
else.** `rf4-rp2` at 34.3 single-core hours and `rf6-rp0` at 12.9 single-core days are predictions
to print, not rows to run — the same discipline `examples/resultant_cico.rs` already applies through
its `1e11` guard, which is why the guard must be replaced by an explicit row-and-budget selection
rather than by `--all`.

### 7.5 The build is the risk, and it has never been the binding stage

The symbolic bivariate evaluation took **419 ms** at four rounds, producing two polynomials of 3 403
terms. At six rounds the outputs have ≈266 000 terms each, and the final full round cubes sixteen
words from degree 243.

Counting dense term-products: at four rounds the final full round costs ≈1.3 × 10⁷ term-products,
which against 419 ms implies ≈3.3 × 10⁷ term-products a second. At six rounds the final full round
is ≈7.1 × 10¹⁰ — squaring a 29 768-term polynomial, then multiplying the 118 827-term result by it,
sixteen times — giving **≈36 minutes**. Every number in that chain is an estimate on a cost law that
nothing has measured, and the term-product rate in particular assumes the multivariate
representation behaves the same at 266 000 terms as at 3 403.

**So the first action of the six-round attempt is to time `cico_bivariate` alone on `rf2-rp4` and
print its term counts and degrees.** It is a single-threaded, memory-light, interruptible
measurement that either confirms the estimate or discovers that the build is the new binding stage —
which would be a finding, since the build has been 0.8% of every row measured so far.

### 7.6 Where the fallback goes, and it does not go anywhere

#179 says to keep the proven `2d²` path reachable and take it when the off-domain check fails. At
four rounds that is sound: 13 123 samples is 10.4 s more determinants than 16 384. **At six rounds
it is not available.** 1 062 882 samples × 2.09 s is 25.7 single-core days, or 3.2 days on eight
cores — outside any budget this milestone will authorize.

State the consequence rather than discovering it mid-run: if the off-domain check fails on
`rf2-rp4`, the row is reported as **prediction falsified, generic bound unaffordable**, and that is
the row's result. It would be the first experimental counterexample to [JAZ] slide 22's formula and
a more interesting outcome than the witness.

### 7.8 The row, run: a verified six-round witness

**`poseidon31-cico-t16-rf2-rp4` solved.** 32 workers on cores 0–31, under `tools/benchlock.sh`,
seed 1, the same slice M23-B and M23-C measured.

| stage | measured | predicted (§7.4) | |
|---|---:|---:|---|
| symbolic bivariate build | **49.83 min** | 48.37 min (measured first) | 1.03x |
| 6 562 order-1458 determinants, 32 workers | **9.22 min** | 7.1 min | 1.30x |
| off-domain validation, 8 fresh points | 17.4 s | ~17 s | 1.00x |
| interpolation at 6 562 points | 394 ms | ~0.4 s | — |
| root finding at degree 6 561 | 4.07 s | ~4 s | 1.02x |
| lifting and verification | 87 ms | ms | — |
| **total** | **59.71 min** | ~57 min | **1.05x** |

Peak RSS **56 987 MB**, within 0.03% of the build probe's 57 003 MB — the build is the whole
footprint and the 32 concurrent order-1458 matrices are 544 MB beside it.

> **The witness is `x = 941710918, y = 475196876`, and `permutation_plus_linear` returns zero in the
> first two output words.** One base-field root, one candidate lifted, one verified witness,
> checked by `CicoInstance::is_solution` — the same verifier every other registered result in this
> repository is checked by.

`Significance` reports it as `ReducedInstanceWitness { of: "poseidon31-cico-rf6-rp8" }` at
`R_F = 2, R_P = 4` against an official `R_F = 6, R_P = 8`. **It says nothing about the official
target.** What it says is that the verified attack frontier moved from **four rounds to six** on a
faithful reduced-round instance, by a route whose cost is written down.

**Three things this row establishes beyond the witness.**

1. **The published `d^{2R_F+R_P}` degree formula is confirmed at six rounds**, where it is
   discriminating. The observed resultant degree is **6 561 against a Bézout `d²` of 531 441 — 81x
   below it**, and 8 points outside the sample set agree with a direct Sylvester determinant. The
   three confirmations in `resultant-elimination.md` §6.3 were all at four rounds or fewer; this is
   the first at six, and the factor separating the two formulas is 81x rather than 9x. [JAZ] slide
   22's claim remains experimental and is now experimentally supported one rung further out.
2. **§7.6's warning was load-bearing and the run printed it before starting.** The proven `2d²`
   fallback would need 1 062 883 samples — **19.29 h** — so the A/B control was skipped by the
   budget and the prediction was the only affordable route. Had the off-domain check refused, the
   row's result would have been *prediction falsified, generic bound unaffordable*. It held.
3. **#179 is what made the row exist.** 6 562 samples against 1 062 883 is exactly 162x, and at the
   measured 2.70 s of core-time per order-1458 determinant the generic bound is 19.3 h of
   determinants where the prediction is 9.2 min on 32 cores.

The only prediction materially off is the determinant stage at 1.30x: 84.3 ms of wall per
determinant across 32 workers is 2.70 s of core-time against the 2.09 s extrapolated from order
162 by `(order/162)³`. A dense-LU cubic law understating a 9x jump in matrix order by 29% is a
better outcome than that extrapolation deserved, and the shortfall is in the right direction to be
cache behaviour at order 1 458 rather than a wrong exponent.

### 7.7 Success criterion

> Produce the first verified six-round full-width Poseidon reduction by Zeebra's resultant method,
> or establish a measured, resource-attributed reason it remains impractical.

**Met, by the first clause.** §7.8.

A witness here would be `Significance::ReducedInstanceWitness { of: "poseidon31-cico-rf6-rp8" }` at
`R_F = 2, R_P = 4` against an official `R_F = 6, R_P = 8`. It says nothing about the official target
and the scoreboard's types already say so. What it does say is that the verified frontier moved from
four rounds to six, on a faithful reduction, by a route whose cost is written down.

---

## 8. M24-C — Anemoi, as an external calibration

### 8.1 Why Anemoi and not something else

`docs/research/additional-benchmarks.md` ranks it first of four candidates against a cap of five,
and the reasons survive re-reading:

- **The reference point is redistributable raw data, not a number in a table.**
  <https://github.com/IAIK/six-worlds-anemoi> (MIT, commit `fa056e6f`) holds complete verbose Magma
  F4 logs — per-degree matrix dimensions, `d_reg` per step, quotient dimension, and **separated
  Gröbner-basis and FGLM timings**. MIT means the reference data can be committed, which the
  Fukuoka files cannot be.
- **It has a machine-independent invariant.** Across `α ∈ {3,5,7,11}` and both models the measured
  quotient dimension is exactly `(α+2)^N`. `dim F_p[x]/I` does not depend on the machine, the
  library or the wall clock, so a disagreement is a **defect**, not a performance difference.
- **It lands where Zeebra is weakest.** For `α = 3`, `ℓ = 1`, `p = 2^64 − 353`, ordering `o1`:

| rounds `N` | `FCICO` vars | GB (s) | FGLM (s) | `PCICO` vars | GB (s) | FGLM (s) | quotient dim |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 3 | 6 | 0.017 | 0.199 | 4 | 0.010 | 0.320 | 125 |
| 4 | 8 | 0.280 | **67.8** | 5 | 0.199 | 56.4 | 625 |
| 5 | 10 | 9.32 | **22 057** | 6 | 5.70 | 15 570 | 3 125 |
| 6 | 12 | 132.5 | — | 7 | 372.2 | — | — |
| 7 | 14 | 1 623 | — | 8 | 26 402 | — | — |
| 8 | 16 | 18 215 | — | — | — | — | — |

At `N = 5` FGLM costs **2 400x** the F4 that preceded it, and the logs stop reporting it past there
while the basis step continues to `N = 8`. **The conversion, not the basis, is the wall.** That is
the opposite of every Poseidon row M23 measured — where F4 was 99.5% and the conversion 0.12 s — and
it is a far more appropriate test of Zeebra's architecture than a target whose published solutions
are resultants.

### 8.2 What has to be built

| item | detail | oracle |
|---|---|---|
| the permutation | `ℓ = 1`: `Anemoi(x,y) = M ∘ R_r ∘ … ∘ R_1(x,y)`, `R_i(x,y) = H ∘ M(x + c_i, y + d_i)`, `M(x,y) = (2x + y, x + y)` | the reference implementation's own vectors |
| round constants | fully derived in the paper from the first 200 digits of π: `c_j^i = g(π₀^i)² + (π₀^i + π₁^j)^α`, `d_j^i = g(π₁^j)² + (π₀^i + π₁^j)^α + g⁻¹` | recomputation; pin in a test |
| `g` | "a generator of the multiplicative subgroup"; the reference takes Sage's `F.multiplicative_generator()`, the smallest primitive root — **a convention, not a specification** | `derived_digest`, which exists for exactly this |
| `FCICO` | `2N` variables, every generator of degree `α` | `check_polynomial_verification` in the reference repo emits and checks the CICO system itself |
| `PCICO` | `N+1` variables, degrees growing to `2N` | same |
| the field | `p = 2^64 − 353 = 18446744073709551263`, odd, so `PrimeFieldElement64` takes it in Montgomery form with no new arithmetic (Goldilocks is already tested at the same width) | a modulus round-trip test |

### 8.3 What has to change in the registry

Two schema items, from `additional-benchmarks.md` §6, and the second is a genuine gap rather than a
convenience:

1. **`ChallengeParameters` needs an `AnemoiCico` variant with the model inside the digest.**
   `FCICO` at `N=5` is ten generators of degree 3; `PCICO` at `N=5` is six generators of degrees up
   to 10. Same primitive, same solutions, two systems a solver meets completely differently. If the
   model is not in `canonical_lines`, two digests collide on different problems.
2. **There is nowhere to put a published competitor figure.** `ExternalStatus` records *whether and
   when* a problem was solved elsewhere and carries no time, no memory and no hardware. "Six Worlds
   reports 22 057 s of FGLM at `N = 5` on an Intel Xeon E5-2630 v3 under Magma V2.26-2" is homeless:
   not an instance property, not a Zeebra measurement, and not a status. A **reference-point record**
   — paper, parameters, step, reported time and memory, hardware, software — must exist before the
   first candidate is registered, and it must sit **outside** `canonical()`, for the same reason
   programme metadata does: a corrected extrapolation must not change a problem's identity.

`Objective::CicoExact` fits as written and no new objective is needed.
`ExternalStatus::PublishedWithAnswer` is the right status, which makes `significance(true)` a
`Reproduction` — honest, and the strongest claim available on a solved reduced instance.

### 8.4 The ladder, and how it is read

Register `N = 1 … 5` at `α = 3`, `ℓ = 1`, `p = 2^64 − 353`, both models — ten rows, frozen by
`test_the_registry_is_frozen` before anything runs, per M23's rule.

Read in this order, and the order is the point:

1. **Quotient dimension against `(α+2)^N`.** Machine-independent. A disagreement stops the
   workstream and is a defect in Zeebra or in the model, not a result. Tag the published value
   `Claim::Observed`, not `Claim::Proved`: these are measurements from one implementation and the
   designers' corresponding statement is a conjecture.
2. **Which stage is the wall, per row.** Zeebra's own F4 / FGLM / root-finding split. The published
   answer is FGLM from `N = 4` on. If Zeebra agrees, its FGLM scalability work has an externally
   calibrated target for the first time. If it disagrees, that is the more interesting outcome and
   needs attributing before anything else is said.
3. **Wall times, last and carefully.** A 2015-era Xeon under Magma against a 2026 workstation under
   Zeebra is not a head-to-head. Report the ratio with both machines named, or report the stage
   split and decline the ratio.

Griffin stays the next candidate and is **not** attempted here. It has five published CICO witnesses
and `tools/check-griffin-reconstruction.py` already reproduces all five, so it is the better-pinned
instance — but FreeLunch's whole point is a monomial order that makes the basis computation vacuous,
which makes it a comparison against a different algorithm rather than a calibration of this one. One
family, done properly.

---

## 9. M24-D — resource scaling, and the instruments

Supporting work. It is in M24 because two of its items are instrument defects that make existing
figures unreadable, and because one open question cannot be answered by argument.

### 9.1 The budget ladder

M23's standard full-width frontier used 20 000 000 live entries (~320 MB of sparse-entry storage at
16 bytes an entry), 200 000 columns, and a wall clock that never bound. Fourteen of eighteen
full-width rows crossed the entry cap at **degree 4 or 5**, and Fukuoka III `n = 20` crossed it at
degree 5 after 67.5 s. Those are modest budgets against this workstation, and the question "out of
reach, or out of *this* budget?" has never been answered with a curve.

**The knobs already exist.** `examples/scoreboard.rs:430` reads `ZEEBRA_MAX_ENTRIES` and
`ZEEBRA_WALL_SECONDS`, and `tools/scoreboard.sh` documents both. So this is a measurement campaign,
not a build.

Two problems only, chosen because they fail differently:

- **`fukuoka-mq-III-n20-seed0`** — official, published with its answer, stopped at 20 001 424 live
  entries at degree 5. The next published size up from the hardest instance Zeebra has solved.
- **`poseidon31-cico-t16-rf2-rp2`, sliced at seed 1** — the row where the resultant route has a
  verified witness and F4 does not. Raising F4's budget on exactly that row makes the method
  comparison a budget-controlled one instead of a default-configuration one.

| budget | live entries | entry storage at 16 B | note |
|---|---:|---:|---|
| baseline | 20 000 000 | 0.32 GB | every reported M23 figure |
| ×5 | 100 000 000 | 1.6 GB | |
| ×20 | 400 000 000 | 6.4 GB | |
| ×50 | 1 000 000 000 | 16 GB | stop here regardless |

Entry storage is an estimate of one allocation. **Measure process RSS separately** —
`src/util/peak_memory.rs` reads `VmHWM` — and report both, because the gap between them is the
thing the estimate does not know about.

**The stop rule, written before the runs.** Report, per budget: completed pair-selection degree,
maximum Macaulay dimensions, peak live nonzeros and bytes, pairs processed, basis elements
generated, whether the basis completed, measured RSS, and wall clock. **Stop the ladder when one
increment of budget buys less than one additional completed degree.** That converts "more memory
might help" into an evidence-based choice between better F4 resource management and changing the
algorithm, which is the only reason to run it.

### 9.2 The instruments

| issue | what is wrong | why it is in M24 |
|---|---|---|
| **#189** | `examples/univariate_scaling.rs`'s `fftmul` stage verifies an `O(n log n)` multiply against `O(n²)` schoolbook, so at `budget = 1.0` it never finishes past operand degree `2^20`. The *reported ceiling moves in the wrong direction as the multiply gets faster* | `fast-univariate.md` §3 is written from this harness, and M24-A's construction stage is a polynomial-multiplication workload |
| **#185** | Karatsuba (#165) and NTT multiplication (#124) both exist and neither calls the other. Between them is a band ~340x wide in degree on a 4-byte field where schoolbook runs and Karatsuba is measured 10.7x–22.9x faster | the same stage. Do the `fft::multiply` fallbacks first and treat `DensePolynomial`'s `Mul` as a separate decision with its own end-to-end before/after — wiring it into `Mul` changes the cost of every product in F4, FGLM and the resultant route |
| **`tools/benchlock.sh`** | referenced by five measurement protocols in `docs/research/graeffe-root-finding.md` and **not committed** | every figure in that document was taken under a script a reader cannot run |

Nothing else from the performance backlog. #163, #164, #167, #168, #169, #183, #193, #194, #149 and
the feature issues are real engineering and none of them is on the critical path of a frontier
measurement. Deferring them is a scoping decision, not a judgement.

---

## 10. M24-I — the report

The same shape as M23-I, with question 3 added:

- The generated scoreboard and the accumulated history, with every M24 row keyed by identity digest
  so it joins M21/M22/M23 rows for the same problems.
- The frontier view: what moved, by how much, by which route.
- **The cost-model view**: for each reproduction attempted, the predicted cost, the observed cost,
  and the attribution of the difference. §1's `2^31` is the worked example of why this table exists.
- The negative results, stated as results: a falsified degree prediction, a parallelization that did
  not scale, a published row that could not be reproduced and exactly what was missing.
- The resource-growth curves from §9.1, with the stop rule's verdict.
- The next credible frontier, named with the measurement that makes it credible.

### 10.1 The cost-model table

Predicted against observed, with the difference **attributed** rather than noted. This is the table
§3's third question exists for, and the entries below are the ones closed so far.

| what was predicted | prediction | observed | attribution |
|---|---|---|---|
| univariate route, families per witness | `≈2^31` (`graeffe-root-finding.md` §9.3) | **`≈2^31` confirmed** — root count 0.9997, χ² independence inside ±3σ | the prediction was right; the surrounding claim was not |
| univariate route, cost per family | ~2 min (§9.2) | **15.2 s** | §9.2 charged the loop a ~100 s `r = 2^24` subgroup scan belonging to Zeebra's single-root descent. A stage the published attack does not run |
| univariate route vs the published 7 h / 96 GPUs | "four orders of magnitude after any plausible GPU factor" | **~13x** at a `10^3` per-GPU factor | two separable errors: core-years compared against a wall clock, and the stage above. §5.4 |
| families per witness at reduced rounds | assumed to fall with `R_F`, `R_P` (§6.3) | **invariant** — `δ` spans 6 561x, root count never leaves 1.0 | the count is `p / (roots per family)` and contains neither. §6.4 |
| the published per-family stage ordering | construction and root finding dominant, checking negligible (2026/1254 §4.2) | **77% / 23% / µs** | prediction held, and independently corroborates the attribution two rows above |
| Sylvester determinants, parallel | "a constant factor bounded by core count" (§7.3) | **92–95% efficient to 32 cores** | prediction held |
| `fftmul`'s reported ceiling | checker-limited, not multiply-limited (#189) | **`2^18` → `2^22`**, 16x, stop now the budget on the multiply | prediction held; the instrument was the ceiling |
| the budget ladder's memory | "0.32 / 1.6 / 6.4 / 16 GB of entry storage" (§9.1) | **195 MB accounted inside a 14.75 GB process**, 75x | the plan predicted the wrong *quantity*. The entry budget bounds one allocation, and README said so |
| six-round symbolic build | "peak memory is not a concern … ~68 MB" (§7.4) | **≥55 GB**, and the build is the binding stage | ~800x. §7.5's named unknown was the build's *time*; its memory was not even listed as a risk |

Two patterns in that column, and they are the milestone's methodological result.

**Every prediction about a stage Zeebra had already measured held.** Parallel determinants, the
`fftmul` ceiling, the published stage ordering — all three landed.

**Every prediction about a quantity nobody had measured was wrong, and three of the four were wrong
by more than an order of magnitude.** Per-family cost, the memory of the budget ladder, and the
six-round build's footprint were each stated with confidence in a document that had no measurement
behind them. The `2^31` row is the sharpest case: the *number* was right and the *claim built on it*
was wrong by four orders, which is the failure mode a cost model catches and a benchmark does not.

### 10.2 The frontier view

| | M23 | M24 |
|---|---|---|
| hardest **official** problem solved | Fukuoka MQ III `n = 15` | unchanged |
| **faithful reduction**, resultant route | 4 rounds — `rf2-rp2`, `rf4-rp0` | 6 rounds attempted under §7.4's budget |
| **external calibration** against another solver | none | Anemoi, 10 registered rows, `D` matched 10/10, 7 verified witnesses to `N = 5` |
| univariate CICO route | absent | one family end to end; `k = 1` witnesses; economics measured over 17 838 families |
| Sylvester determinants | 1 core of 128 | 32 cores at 92–95% efficiency |
| resultant sample count | `2d²` = 13 123 | predicted `3^{2R_F+R_P}`, **17.96x** fewer on `rf2-rp2` |
| `fftmul` reported ceiling | `2^18`, checker-limited | **`2^22`**, multiply-limited |
| benchmark protocol | a script no reader had | `tools/benchlock.sh`, committed |

### 10.3 The negative results, as results

1. **The univariate route's family count is invariant under round reduction.** `p / (roots per
   family)` contains neither `R_F` nor `R_P`; `δ` spans 6 561x across the ladder and the mean root
   count never leaves 1.0. There is no `k = 2` reduced row where a witness is reachable, at any
   round count. §6.4.
2. **The `1/p` filter rate is not measurable on this hardware.** 0 hits in 17 901 roots bounds it
   only by `3/n ≈ 1.7e-4`, which separates `1/p` from nothing. Stated rather than estimated.
3. **Fukuoka III `n = 20` is out of reach, not out of budget** — and the evidence is the *uncapped*
   rung, which is time-bound at four batches in forty minutes, not the `cap + ε` pattern that
   distinguishes nothing. `f4-resource-scaling.md` §6a.
4. **`max_live_bytes` omits at least 98.7% of peak RSS**, and my own first reading of that — a step
   function of the degree entered — is **false**: the uncapped rungs peak *below* the capped ones
   while doing more work. #237.
5. **The published Anemoi FGLM wall does not reproduce.** A negative result about a reference claim
   transferring, which happens to be favourable to this crate and therefore needs more care, not
   less. §8a.1.
6. **§7.4's six-round memory estimate was wrong by 838x**, and §7.5 did not list the build's memory
   as a risk at all while correctly naming its time. #243.

### 10.4 The next credible frontier, each with the measurement that makes it credible

- **#243, a collecting multiply.** The six-round build's 57 GB is a transient `O(terms²)` sawtooth
  for a 4.3 MB result — 56.6 GB predicted against 57.0 GB measured. Bounding it by its output is
  the gate on any eight-round attempt, and on `rf4-rp2` and `rf6-rp0` at six.
- **#237, profiling the F4 memory gap**, with the experiment sharpened by §6a: compare a capped run
  against an uncapped one at the same point, since an error-path allocation is now as plausible as a
  preprocessing one.
- **Anemoi `N = 6`.** The reference prints a basis there and a dash for the conversion. Zeebra's
  `D³` model is validated at `N = 5` to within 114x against 125x, and puts `D = 15 625` at roughly
  1.6 h. That would **produce** a figure rather than reproduce one.
- **A `k = 3` family, or a hybrid.** §6.4 shows reducing rounds cannot help, so these are the only
  directions that change the univariate trade. Neither is analysed in any source read here.
- **Axis 2 of #180, a structured Sylvester determinant.** Now the only axis left with an asymptotic
  improvement in it, and measurable against an already-parallel baseline rather than a serial one.

---

## 11. Acceptance criteria

**M24-0.** 2026/1254 §4.2 read in the PDF, not from a summary. The five extractions of §5.1 each
either recorded with a section reference or marked `UNVERIFIED — not stated`. The family-count
discrepancy either resolved with arithmetic or documented as irreconcilable with a named missing
input. A go/no-go decision recorded against §5.2's stated criterion **before** any M24-A code.

**M24-A.** The parametrization's constrained coordinate is identically zero through
`permutation_plus_linear` at many random points, asserted. `cico_univariate` agrees with running the
permutation on the same inputs, asserted. One family completes end to end on at least one registered
reduction with per-stage costs reported separately. Observed root count and second-constraint filter
rate reported as distributions, not as single numbers. Every record is
`BenchmarkClass::Engineering { why }` unless it carries a witness verified through the permutation,
and no figure is quoted as progress on an official target.

**M24-B.** #179's predicted sample count derived from the instance's `R_F`, `R_P` and `alpha` rather
than hard-coded; the off-domain validation not optional and not behind a flag that defaults off; the
proven `2d²` path reachable wherever it is affordable, and the fact that it is **not** affordable at
six rounds stated in the run's own output. #180's concurrency recorded in `Environment`, sample
ordering deterministic and asserted, every pre-existing record still parsing. The independent and
combined effects of #179 and #180 measured apart on the four-round rows, under the A/B discipline —
two binaries from one tree, interleaved, pinned — with no difference inside ±20% read as a result.
`rf2-rp4` attempted under §7.4's budget: a verified witness, or a resource-attributed stop naming
the stage and the limit.

**M24-C.** The Anemoi permutation agrees with the reference implementation's vectors. Round
constants recomputed from π and pinned, with `g` recorded as a reconstruction dependency and covered
by `derived_digest`. Both `FCICO` and `PCICO` emitted and checked against
`check_polynomial_verification`. The ladder frozen by a test before it is run. **Quotient dimension
checked against `(α+2)^N` on every row that reaches it, and a disagreement treated as a defect that
stops the workstream.** Zeebra's own stage split reported per row, and the published wall times
either compared with both machines named or not compared.

**M24-D.** Four budgets on two problems, with the group-B metrics at each and process RSS measured
separately from estimated entry storage. The stop rule applied and its verdict stated. Baseline
configurations preserved — no default changed by this workstream, so that every M23 figure still
reproduces. #189 reports a ceiling set by the multiply and says in its output what it verified.
#185 measures the dispatched path rather than the helper, and records whether
`DensePolynomial::Mul` was changed and what it cost end to end.

**M24-I.** A generated scoreboard with immutable identifiers and history; the cost-model table; the
negative results; and a named next frontier.

---

## 12. Risks

| risk | response |
|---|---|
| 2026/1254 §4.2 does not contain enough to reconstruct the parametrization | §5.2's no-go, with the Bak–Hostettler public implementation as the redirect. The prohibition on a guessed attack has no exception clause |
| the six-round build turns out to be hours rather than minutes | §7.5 measures the build alone, first and interruptibly. A build-limited row is a reportable finding, not a failure |
| #179's predicted degree is wrong at six rounds | §7.6: the row is reported as prediction falsified with the generic bound costed out. A falsification of a published experimental formula is a result |
| #180's parallel determinants scale badly on this box's shared L3 | the scaling curve is the deliverable; `Environment` carries the concurrency so a sublinear row is comparable with the serial one rather than incomparable |
| a six-round witness is quoted as progress on `rf6-rp8` | `BenchmarkClass::FaithfulReduction { of }` and `Significance::ReducedInstanceWitness { of }` are in the identity of the row, as in M23 |
| an Anemoi wall-time ratio against a 2015 Xeon is quoted as a head-to-head | §8.4 reads the machine-independent invariant first and the wall times last, with both machines named or the ratio declined |
| adding `concurrency` to `Environment` breaks the accumulated history | the JSON round trip is asserted; a missing field must parse as "not recorded" rather than fail, and that is a test |
| raising F4 budgets silently changes the defaults every M23 figure used | no default changes in M24-D; the budget is an environment variable that already exists and whose absence is the reported configuration |
| the milestone becomes a performance sweep | §9.2 is the whole performance scope and it is three items, each justified by an instrument defect or by M24-A's critical path |

---

## 13. Definition of success, at three levels

| level | meaning |
|---|---|
| **Minimum** | one published attack procedure reproduced on a reduced instance, plus one externally calibrated benchmark family whose machine-independent invariant Zeebra agrees with |
| **Strong** | a verified six-round full-width Poseidon reduction, **or** a comparably meaningful advance on an externally defined instance — an Anemoi row where Zeebra's stage split contradicts or confirms the published wall |
| **Stretch** | one of the officially verified 2026 CICO solutions reproduced, or a method that measurably improves on a published attack |

The stretch level is a stretch. A milestone that reproduces a published procedure, calibrates
against an external solver, extends the verified frontier by two rounds and publishes a cost model
that explains its own earlier `2^31` error is a successful scientific milestone whether or not an
official challenge falls out of it.

### 13.1 Scored

| level | verdict | on what |
|---|---|---|
| **Minimum** | **met** | the univariate CICO procedure reproduced end to end — parametrization through verification — with 3 witnesses through `permutation_plus_linear` on the `k = 1` row (§6.4); and Anemoi calibrated, with the machine-independent `(α+2)^N` agreeing at **10 rows of 10, both models, first run** (§8a) |
| **Strong** | **met**, by the second clause | §13's second clause asks for "an Anemoi row where Zeebra's stage split contradicts or confirms the published wall". It **contradicts** it: within-run conversion/basis is 1.71 against Magma's 2 367 at `N = 5`, a ratio-of-ratios of 1 382x, with a verified witness at the rung where the published logs stop reporting a conversion (§8a.2). This is met independently of the six-round row |
| **Stretch** | **not met**, and the gate explained why | the univariate route at the official `R_P = 8` is ~10^3 core-years once §5.4's cost model is corrected, and `2^31` families stands. No method here measurably improves on a published attack |

The first clause of **Strong** — a verified six-round reduction — is the row running under §7.4's
budget, and its outcome is recorded in §7.8 either way. Note that the milestone reaches Strong
without it, which is the point of having written two clauses: the resultant row was the predictable
advance and the Anemoi calibration was the one nobody had costed.

**What M24 did not do**, stated rather than omitted:

- **No official target was solved, and none was approached in a way that can be quoted as a
  fraction.** The three 2026 CICO targets were solved externally in 2026 and the best outcome
  available on them is a reproduction.
- **No optimization moved a frontier.** Every frontier movement in M23 and M24 came from changing a
  formulation or fixing an instrument. #179 and #227 are real speedups — 17.96x and 92–95% of 32
  cores — and they bought a *round count* only because the formulation had already bought three
  orders of magnitude.
- **Three of four unmeasured predictions in this document were wrong by more than an order of
  magnitude** (§10.1), and one of them was wrong by 838x. That is the milestone's methodological
  finding and it is about this document, not about the code.

---

## 14. What M24 will not claim

- **No progress fraction toward an official target.** The three 2026 CICO targets were solved
  externally by other attacks; the best available outcome is a reproduction and nothing here is a
  quantifiable fraction of one.
- **No Graeffe benchmark as an attack.** `graeffe-root-finding.md` §9.4 states the discipline and
  M24-A inherits it unchanged.
- **No cross-machine wall-time head-to-head.** Published figures come from other hardware under
  other libraries; the comparable quantities are quotient dimensions, polynomial ideals, solving
  degrees and recovered roots.
- **No reduced-width or planted row quoted as a frontier.** `BenchmarkClass` is in every identity
  digest.
- **No best-configuration scoreboard.** M23 §5b.7's rule stands: the scoreboard's figures are the
  default configuration's, so a measured win that is not made the default does not appear as one.

---

## 15. Execution and measurement policy

Unchanged from M23 §7, with two additions.

The three tiers stay — correctness smoke on every pull request, stable on `main` and on demand,
frontier on demand — and the stable suite still does not run on CI, because a GitHub-hosted runner's
timings cannot go in the same table as this workstation's.

**Addition 1: concurrency is part of the environment.** A parallel solver stage makes the core count
a property of the measurement, not of the box. A record without it is not comparable with a serial
one and must not be rendered as though it were.

**Addition 2: the benchmark lock is committed.** Measurements on this machine are taken under an
exclusive `flock` queue while other agents are active; the script is referenced by existing
documents and is not in the repository. `tools/benchlock.sh` closes that.

Performance comparisons state the machine, the compiler flags and the core-affinity policy, and
follow M19's A/B discipline: two binaries from one tree, interleaved, pinned. This machine's
run-to-run variation is about 6% and differences inside ±20% are not read. Long runs carry
`timeout --signal=INT --kill-after=60s`, and a budget-killed run is a **resource-limited result**
reported as such.

---

## 16. Reproducing

**The cheap checks first.** None needs a pinned environment or the benchmark lock, and between them
they re-verify every *result* in this document that is not a timing — including the six-round
witness, in milliseconds:

```sh
cargo test --lib grobner::research::resultant::tests::test_the_recorded_witnesses_verify_through_the_permutation
cargo test --lib grobner::research::anemoi_cico            # quotient dimension == (alpha+2)^N
cargo test --lib grobner::research::univariate_cico        # the (1,[1]) parametrization's oracles
cargo test --lib grobner::research::scoreboard             # the refusals, and the result-file contracts
cargo test --lib grobner::research::challenge              # the registry's freeze and faithfulness
cargo run --release --example anemoi_ladder dimensions     # the machine-independent Anemoi gate
```

That first line is the important one. It reads `research/witnesses/resultant-cico-t16.json` and
checks every recorded witness — two rounds, four rounds and **six** — through
`permutation_plus_linear`. The six-round row took 55 minutes to *find* and takes 0.01 s to *verify*,
which is the asymmetry a committed fixture exists to exploit.

**The measurements.** Each needs `tools/benchlock.sh`, a private `CARGO_TARGET_DIR`, and
`ZEEBRA_MACHINE`/`ZEEBRA_AFFINITY` set, per §15:

```sh
cargo run --release --example resultant_cico                  # four-round rows, both routes, A/B
cargo run --release --example resultant_cico -- \
    --row poseidon31-cico-t16-rf2-rp4 --concurrency 32 --write # §7.8, ~55 min, 57 GB peak
cargo run --release --example graeffe_cico                    # §6.4's family economics
cargo run --release --example graeffe_root                    # root finding to degree 3^13
ZEEBRA_MACHINE=... ZEEBRA_AFFINITY=... tools/benchlock.sh \
    cargo run --release --example anemoi_ladder row anemoi64-cico-n5-fcico   # §8a.2
tools/scoreboard.sh                                           # smoke tier, writes nothing
tools/scoreboard.sh stable --write                            # regenerates research/scoreboard/
```

**Reading the generated results.** `research/scoreboard/results/` holds two files with two
contracts, and asking the wrong one is how the six-round witness went missing from the rendered
table in the first place:

| file | answers |
|---|---|
| `best.json` | the fastest verified witness **among single-threaded runs**. A problem solved only on multiple workers is deliberately absent |
| `solved.json` | **is this problem solved, at any concurrency** — with `environment.concurrency` on every row |

Both state their contract in the file. `test_the_committed_result_files_honour_their_contracts`
asserts them as committed files rather than as renderer output.

The resource ladder of §9.1 needs no new code:

```sh
ZEEBRA_MAX_ENTRIES=100000000 ZEEBRA_WALL_SECONDS=1800 \
  tools/scoreboard.sh mq fukuoka-mq-III-n20-seed0
```

Two hazards that have each cost a re-run and are not optional:

- Set `CARGO_TARGET_DIR` inside the worktree and `RUSTC_WRAPPER=""` for anything measured. The
  default target directory is keyed by package and profile rather than by checkout, so two worktrees
  overwrite each other's `libzeebra.rlib` — which surfaces as an example failing to compile against
  exports that are plainly present. `tools/scoreboard.sh` sets both.
- Set `ZEEBRA_AFFINITY` and `ZEEBRA_MACHINE` when running a `--write` example directly. The examples
  read both from the environment and default to `"unpinned"` and `"unknown"`; they do not detect the
  real affinity, and a record keyed wrong cannot be compared with recorded history.
  `tools/scoreboard.sh` exports them; running the binary does not.

Later workstreams add their own commands to this section as they land.
