# M22 — Degree-Aware F4 and Cryptanalytic Matrix-Growth Control

**Status:** complete
**Prerequisite:** M21, merged
**Research issues:** #74 (Hilbert-driven and mutant F4), #81 (solving-degree measurement)

M22 asked whether better scheduling and algebraic information can reduce the Macaulay matrix growth
that stops Zeebra on cryptanalytic systems, without changing the field arithmetic or the elimination
engines. The answer is **mostly no, in an informative way, with one clear win that came from a
direction the plan did not single out** — and with two of M21's conclusions corrected, plus two of
M22's own after review (§6).

Everything below is reproducible from this repository; §11 lists the commands. The Fukuoka instance
files are not redistributed and are fetched by `tools/fetch-mq-challenge.sh`.

**No correctness contract was weakened.** Every strategy this milestone added returns the identical
reduced Gröbner basis, which is asserted over the correctness corpus under every monomial order and
every criterion combination, and — new in M22-I — differentially against Singular on random systems
over six characteristics. Nothing discards a critical pair on heuristic grounds.

## 1. The nine questions

### 1.1 What fraction of F4's work is redundant on the selected MQ systems?

**33% to 60% of pair rows add no rank, and the figure is flat.**

| instance | dependent pair rows | reducer share of all rows |
|---|---:|---:|
| katsura-5 | 40.0% | 83.2% |
| Fukuoka III `n=10` | 54.2% | 40.1% |
| Fukuoka III `n=15` | 55.0% | 43.4% |
| Fukuoka VI `n=10`, published | 58.9% | **98.7%** |
| Poseidon `t=3`, as generated | 57.5% | 96.2% |
| Poseidon `t=2 R_F=4` | 53.6% | 75.9% |
| Poseidon `t=2 R_F=2` | 33.3% | 68.4% |

It does not separate the instances that finish from the ones that do not, and it does not grow with
size within a family. **And the denominator is the wrong one to optimize**: reducer scaffolding is
40% of rows on the overdetermined MQ instances and 68%–99% everywhere else, so halving the dependent
pair rows halves a minority of a minority. That is the single most important number M22-0 produced
and it bounded every workstream after it.

The measure is **rank attribution, not zero-row counting**. Reducer rows have distinct leading
monomials by construction, so they are independent and none ever reduces to zero; every zero row is
a dependent pair row, and a pair contributes two rows, so the zero count is a count of useless pairs
in neither direction. What is exact is `rank − reducer_rows`, and `rank − |input leading monomials|`
is exactly the number of new basis elements. Both identities are asserted on real batches.

### 1.2 Which pair-selection strategy produces the smallest matrices?

For *ordering within a degree*: **`PairSchedule::SmallMultiplierMonomial`**, which is
Sakata–Takagi's ordering as published — it compares multiplier *monomials*, and on the three
largest instances it is the best schedule measured on every structural counter at once: −7.1%,
−7.6% and −9.5% peak live entries, up to −14.5% row operations. It is the only schedule that
narrows the matrix on either Fukuoka instance. Its control,
`LargeMultiplierMonomial`, is the worst schedule on peak entries on five of seven instances, so
the effect is monotone in the comparator rather than incidental — a 1.54x–1.75x spread between the
two directions on the large instances.

The gains are real and **sub-threshold**: 7%–14.5% on exact counters, with runtime inside the ±20%
band this milestone declines to read. That is a different finding from "no effect" and from "make
it default".

`SmallMultiplierDegree` — comparing the multiplier's *degree* instead, which is a coarser and
genuinely different relation — **is** a null result: it cuts row operations 4%–15% and makes the
matrix larger on four of seven instances, with a 1.09x–1.13x direction spread that a machine with
6% run-to-run variation cannot distinguish from nothing.

**An earlier version of this report had these two the wrong way round**, because M22-A first
implemented only the degree comparator and reported its null result as a finding about the
published strategy. The correction is §2 of
[`docs/research/pair-scheduling.md`](research/pair-scheduling.md), and both comparators are now
selectable so either claim can be reproduced.

For *batch size*, which the plan asked to measure separately and which turned out to be the lever:

| instance | cap | pairs reduced | peak entries | ms |
|---|---|---:|---:|---:|
| Fukuoka III `n=10` | uncapped | 743 | 168 020 | 118.6 |
| | **64** | **334** | **60 809** | **32.7** |
| Fukuoka III `n=15` | uncapped | 3 596 | 2 142 707 | 8 262 |
| | **64** | **1 693** | **1 099 753** | **3 829** |

A cap of 64 cuts peak live entries **24%–64% on every instance** and is **3.6x and 2.2x faster** on
the two Fukuoka type III instances. The mechanism is not splitting work but avoiding it: a smaller
batch returns its candidates sooner, and those candidates let Gebauer–Möller eliminate pairs the
uncapped run had already committed to. The basis element count is unchanged, so nothing is traded.

The smallest matrices of anything measured come from the Hilbert-driven cap at slack 0 — 43 381 peak
entries on Fukuoka III `n=10`, a **74%** reduction — at the cost of being the slowest capped
configuration.

### 1.3 How accurate are semiregular Hilbert predictions?

**Exact at every degree on random and genuine overdetermined homogeneous MQ, and wrong on every
structured system.** 100% agreement on 10-quadratics-in-5, 12-in-6, 14-in-7, square 6-in-6, both
Fukuoka type III top-form systems, and — unexpectedly — katsura-5. 23% on the deliberate
counterexamples and on the Poseidon top forms, 15%–77% on the inhomogeneous systems.

The **sign** is what decides whether a wrong prediction is wasteful or unsound. Negative error
overestimates the ideal, so a cap built on it is too large: wasteful, never incomplete. Positive
error is the dangerous direction, and it is the direction the inhomogeneous systems fail in. The
sharpest case, on the published Fukuoka type III `n=10`:

> **the model says degree 4 has nothing left, and F4 finds 85 of its 168 basis elements there.**

A rule that truncated at the model's degree of regularity would return an incomplete basis on the
genuine challenge instance and look like a 3x speedup doing it. That is the plan's §2.4 correctness
boundary, on real data, and it is why nothing in this milestone discards a pair.

In the one figure a cap depends on — predicted new leading monomials against observed — the model is
103/168 on Fukuoka III `n=10` (a 39% underestimate) and **4/107 and 4/186** on the two Poseidon
systems (27x and 46x).

### 1.4 Does Hilbert-guided selection reduce work after including certification?

**On the instance where it helps, yes and the check is free; and it still only matches a cap chosen
without a model.**

| configuration | solve ms | cert ms | **total ms** |
|---|---:|---:|---:|
| uncapped | 118.6 | 0.4 | 118.9 |
| fixed cap 64 | 32.7 | 0.4 | **33.1** |
| hilbert limited+16 | 30.5 | 0.3 | **30.8** |

Fukuoka III `n=10`. 30.8 ms against 33.1 ms is inside this machine's run-to-run variation, so the
Hilbert-derived cap matches rather than beats the fixed one — and M22-B had predicted exactly that,
since the derived quota at the decisive degree is 65 against a hand-picked 64. Its real contribution
is that it needs no tuning.

Certification cost tracks the **basis** quadratically, not the system, so §8.5's worry is answered in
both directions:

| instance | basis | solve ms | certification ms | ratio |
|---|---:|---:|---:|---:|
| Fukuoka III `n=10` | 10 | 118.6 | **0.4** | **0.003x** |
| katsura-6 | 18 | 3.8 | 22.5 | 5.9x |
| Poseidon `t=2 R_F=2 R_P=2` | 70 | 142.2 | 4 824.7 | 34x |
| Poseidon `t=2 R_F=4` | 102 | 373.7 | **25 140.4** | **67x** |

**The check is free exactly where the saving is, and 67x the computation exactly where there is no
saving to erase.** The algorithm's completeness does not rest on it — it rests on no pair being
discarded — so `certify` stays off by default and reports its cost rather than folding it in.

And the aggressive form of the idea is rejected outright: `HilbertSelection::Deferred` is **214x
slower** on Poseidon `t=2 R_F=2 R_P=2` at 21x the matrix width, and on `t=2 R_F=4` it **crosses the
column budget on an instance the baseline finishes in 374 ms**. Correct throughout — a refused budget
is not a wrong answer — and unusable.

### 1.5 Are mutant relations common enough to exploit?

They are common, they are already exploited, and the count is the wrong measure.

| instance | mutant elements | batches with one / batches | regressions | **after a mutant** |
|---|---:|---:|---:|---:|
| katsura-5 | 0 | 0 / 5 | 0 | 0 |
| Fukuoka III `n=10` | 65 | 1 / 6 | 1 | 1 |
| Fukuoka III `n=15` | 335 | 2 / 7 | 1 | 1 |
| Fukuoka VI `n=10`, either form | 0 | 0 / 7–8 | 0 | 0 |
| Poseidon `t=3`, as generated | **164** | 12 / 20 | **0** | **0** |
| Poseidon `t=2 R_F=4` | 80 | 17 / 22 | 2 | 2 |

**Every degree regression in the corpus followed a batch that produced a mutant** — the two columns
are equal on all ten rows — so the mechanism is real and perfectly attributed. **And there are only
zero, one or two regressions per computation**, against 5 to 22 batches. The decisive row is
Poseidon `t = 3`: 164 mutants over 12 of its 20 batches, and zero regressions.

No mutant mode was added, and the reason is structural as well as empirical:
`PairQueue::select_batch` takes the lowest pending degree, so a mutant's pairs already precede the
remainder of the current degree. The one adjacent lever — interrupting the current batch — *is* batch
capping, already measured at 3.6x. MF4's auxiliary basis and degree-decreasing phases are a different
algorithm, out of scope, and in the same family as the manoeuvre §1.4 measured at 214x slower.

### 1.6 Do improvements generalize from MQ to Poseidon?

**No, and the direction is consistent.** Nothing that helps one helps the other:

| lever | Fukuoka type III | Poseidon |
|---|---|---|
| batch cap of 64 | **3.6x and 2.2x faster** | a small loss; pair counts barely move, so there is nothing to avoid |
| Hilbert prediction | exact on the top forms | **27x and 46x wrong**, in the capping direction |
| Hilbert cap | matches the best fixed cap | 6.5x–13.6x slower at slack 0 |
| deferral | 1.28x faster than the same slack's cap | **214x slower**, and one instance from solvable to infeasible |
| **variable order** | no measurable effect | **1.6x–1.7x, and 2.1x less peak memory** |

The last row is the generalization that goes the other way, and it is the milestone's clearest
positive result. It was not one of the plan's named levers.

### 1.7 How far can the controlled Poseidon frontier be extended?

Nine variables — and **the frontier is not where M21 placed it.** `N − E = t − 2k`, so M21's two
nine-variable benchmarks were not the same kind of system and the comparison was confounded. Adding
the controlled row:

| nine-variable instance | eqs | highest degree | peak MB | time |
|---|---:|---:|---:|---|
| `t=3 R_F=2 R_P=1`, as generated | 8 | 11 | 155.3 | column budget crossed after 18.2 s |
| `t=3 R_F=2 R_P=1`, one free input pinned | 9 | 5 | 0.2 | **complete, 13.5 ms** |
| `t=2 R_F=4 R_P=0` | 9 | 5 | 3.8 | complete, 356 ms |

Pinned, the `t = 3` system is **the easiest of the three**. What M21 measured as a state-width
frontier is the **underdetermined direction**: one free coordinate takes the computation from degree
5 to degree 11 and from 0.2 MB to 155 MB. The dimension is read from `classify_ideal` of the
computed basis, not inferred from the counts, and the pinned value is a planted one, so a solution
is known to exist there — the same transformation at an off-plant value was also run, found a
*different* preimage, and verified it through the permutation.

So the frontier was not extended in variable count. What was established is what it is a frontier
*of*.

### 1.8 Which stage remains the dominant limit?

**Matrix width, and under it the symbolic closure.** Reducer scaffolding is 68%–99% of rows on every
cryptanalytic instance, and both failing runs failed on the *column* budget rather than the entry
budget. Every strategy M22 measured acts on the pair block, which is the minority of the rows — which
is why the measured effects are bounded and why the one unbounded effect (variable order) acts on the
monomial order instead.

### 1.9 Is the next priority further F4 development, hybrid MQ, or resultant-based elimination?

**Not further general-purpose F4 scheduling.** M22 measured four scheduling levers and the best of
them matches a one-line batch cap. The plan anticipated this reading: *"If Hilbert-driven F4 offers
little improvement on Poseidon but resultants show a strong structural advantage, M23 should take
precedence."* It offers little improvement on Poseidon.

The ordering M22's measurements support:

1. **Structural reformulation (M23)**, including variable order as a first-class choice. §1.6's last
   row is the evidence: a transformation of the *problem statement* beat every transformation of the
   *algorithm*, on the systems the project exists for. Resultants and round elimination belong here,
   and the Poseidon initiative names resultant-based approaches as promising for its CICO problems.
2. **Symbolic-closure work.** §1.8 says where the rows are, and no M22 workstream touched it. A
   closure that is 99% of the matrix is not addressed by choosing which pairs enter it.
3. **Hybrid MQ (M24)** after that. The batch-cap result is specifically an overdetermined-MQ result,
   and Crossbred-style partial elimination is in the same family.

## 2. What was built

| workstream | PR | deliverable |
|---|---|---|
| M22-0 | #106 | per-degree instrumentation and rank attribution; controlled Poseidon baseline |
| M22-A | #107 | `PairSchedule`, and batch sizing measured apart from it |
| M22-B | #108 | `grobner::hilbert` — exact Hilbert functions and the semiregular prediction |
| M22-E | #111 | `research::reorder` and `research::linear`, both invertible; the controlled ladder |
| M22-C | #113 | `HilbertSelection`, and certification with explicit provenance |
| M22-D | #114 | mutant and degree-regression instrumentation; no mode |
| M22-I | this | the ablation, the Singular sweep over every strategy, this report |

Nothing became a default. Four strategies are selectable and documented as measured-and-not-adopted
— `PairSchedule::SmallMultiplierDegree` and `SmallMultiplierMonomial`, `HilbertSelection::Deferred`,
and `ReducerSelection::LargestLeadingMonomial` from M16 — which is the disposition this project uses
for a result that should stay reproducible whether it was negative or merely sub-threshold.

## 3. The ablation

§11.1's matrix, with the two departures the earlier workstreams forced:

- **There is no mutant configuration.** M22-D added no mutant mode, so D and Combined would be
  byte-identical to A and C. The ablation prints `D = A` rather than leaving a silent gap, and the
  figures confirm it: D and A agree to within run-to-run variation on every instance.
- **A fixed batch cap is included**, and so is its combination with A. M22-A and M22-C established
  that it, not the uncapped baseline, is the reference a Hilbert-driven cap has to beat; §11.1
  permits configurations "needed to isolate interaction effects", and without it the strongest
  result in the milestone is attributed to the wrong cause.

`total ms` is solve **plus certification**, which is §11.1's "complete end-to-end computation time"
and the only column a production decision may use.

### The decisive instance

Fukuoka type III `n=10` seed 0 — 20 quadratics in 10 variables over GF(31), the main overdetermined
MQ benchmark:

| configuration | pairs | batches | cols | peak MB | solve ms | cert ms | **total ms** |
|---|---:|---:|---:|---:|---:|---:|---:|
| Baseline | 743 | 6 | 859 | 2.7 | 105.9 | 0.3 | 106.2 |
| A  small-mult monomial | 743 | 6 | 851 | 2.5 | 97.5 | 0.3 | 97.9 |
| A' small-mult degree | 743 | 6 | 859 | 2.7 | 102.8 | 0.3 | 103.1 |
| B  hilbert observe | 743 | 6 | 859 | 2.7 | 108.5 | 0.3 | 108.8 |
| C  A + hilbert+16 | **279** | 15 | **368** | **0.5** | 24.5 | 0.3 | 24.8 |
| Cap  fixed cap 64 | 334 | 8 | 652 | 1.0 | 29.3 | 0.3 | 29.6 |
| **A+Cap** | 323 | 8 | 467 | 0.7 | **23.6** | 0.3 | **23.9** |
| D  = A | 743 | 6 | 851 | 2.5 | 97.8 | 0.3 | 98.1 |

**The headline is 4.44x end to end, certification included** — 106.2 ms to 23.9 ms — and it comes
from the batch cap, with the pair schedule contributing on top of it. Peak matrix bytes fall **74%**
at A+Cap and **81%** at C, either of which clears §11.5's 20% threshold several times over.

**The ordering matters in combination, and that is new.** Under the degree comparator the capped
configurations were 652 columns (Cap) and 598 (C); under the published monomial comparator they are
**467** and **368**. A alone is 851 columns against the baseline's 859 — under 1%, as M22-A
measured — so almost all of that is interaction: the cap decides *how many* pairs a batch takes and
the schedule decides *which*, and taking the right 64 is worth a third of the matrix width. The
first version of this report measured the degree comparator here and therefore missed it.

**C and Cap no longer tie, and C wins on size by more than before.** The Hilbert-derived cap
reduces the fewest pairs (279 against 334), the narrowest matrices (368 columns against 652) and the
least memory (0.5 MB against 1.0) — **81%** below the baseline — and comes within 4% of a cap picked
by hand on total time. M22-C's finding stands as stated: the model's contribution is that it needs no
tuning, not that it is faster.

### Everything else

| instance | Baseline total ms | best total ms | best configuration | peak MB, baseline → best |
|---|---:|---:|---|---|
| katsura-5 | 2.6 | 2.4 | within noise | 0.0 → 0.0 |
| katsura-6 | 25.0 | 25.0 | within noise | 0.1 → 0.1 |
| katsura-7 | 1 072.6 | 1 007.9 | C | 0.4 → 0.4 (A widens to 0.7) |
| cyclic-5 | 5.6 | 5.3 | within noise | 0.0 → 0.0 |
| cyclic-6 | 112.6 | 105.9 | Cap | 0.1 → 0.1 |
| planted-6 | 0.2 | 0.1 | within noise | 0.0 → 0.0 |
| nonradical | 0.0 | 0.0 | all identical, no matrix built | — |
| positive-dimensional | 0.0 | 0.0 | all identical | — |
| **Fukuoka III `n=10`** | **106.2** | **23.9** | **A+Cap** | **2.7 → 0.7** (C: **0.5**) |
| Fukuoka VI `n=10`, specialized | 13 628.2 | 13 290.0 | within noise | 4.0 → 4.0 |
| Poseidon `t=3`, pinned | 211.2 | 201.4 | within noise | 0.2 → 0.2 |
| Poseidon `t=2 R_F=2 R_P=2` | 5 059.6 | 5 059.6 | **the baseline** | 1.7 → 0.9 (C) |
| Poseidon `t=2 R_F=4` | 25 944.8 | 25 296.6 | A | 3.8 → 1.3 (C) |

**One instance of thirteen shows a real improvement in time, and it is the overdetermined MQ one.**
Everywhere else the spread across all eight configurations is under 7%, which on this machine is
noise — and on two instances the baseline is nominally the fastest, which is what a noise band looks
like from the inside. The classical instances are unmoved, the degenerate ones are identical —
`nonradical` builds no matrix at all, since `<x², y², z² − z>` has pairwise coprime leading
monomials and the product criterion discards every pair — and `positive-dimensional` terminates
under every configuration, which is the property §11.2 lists it for.

Three things the table makes visible that the per-workstream measurements did not:

**On Poseidon and the specialized MQ instance, certification is the computation.** `t=2 R_F=4`
spends 375 ms solving and **25 570 ms** certifying; `t=2 R_F=2 R_P=2` spends 136 ms against 4 923
ms; Fukuoka VI specialized, 457 ms against 13 172 ms. So every configuration's total agrees to
within a few per cent whatever the solve did — including C, which cuts peak memory by 66% on
`t=2 R_F=4` and is 44% *slower* to solve. A production default drawn from the `total ms` column on
these instances would be drawing it from the certification cost. That is why `certify` is off by
default, and why §1.4's table reports the ratio rather than only the total.

**Memory and time have different optima, consistently.** C has the smallest peak on
Fukuoka III `n=10` (0.5 MB), `t=2 R_F=2 R_P=2` (0.9) and `t=2 R_F=4` (1.3), and is the *slowest*
solve on cyclic-6, katsura-7, both Poseidon instances and Fukuoka VI. It is a memory strategy that
costs time, which is a usable thing to be and not the thing the plan hypothesized.

**The two multiplier comparators are not interchangeable, and the difference is not a constant.**
They are identical on katsura and cyclic (the multiplier degrees separate the pairs the same way the
monomials do), and they diverge on exactly the structured instances M22 is about: 851 against 859
columns on Fukuoka III `n=10`, 2.5 MB against 2.7, and 1 333 against 1 330 columns but 3.4 MB
against 3.8 on Poseidon `t=2 R_F=4`. Keeping both selectable is what makes that visible.

## 4. Correctness

§11.4 asks, for every tractable result: Buchberger's criterion; every original generator reduces to
zero; the result generates nothing outside the input ideal; the basis is reduced; and exact
comparison against a reference. The ablation does all five on every row of every instance, and does
them as **assertions** rather than columns — a differing basis is a defect, and a column reporting
one would bury it:

| check | how |
|---|---|
| Buchberger's criterion | `certify_f4_output`, every S-polynomial of the basis reduced modulo it |
| generators reduce to zero | `certify_f4_output`, every nonzero input generator |
| nothing outside the input ideal | structural, plus equality with the baseline's basis — which *is* the unique reduced Gröbner basis of the input ideal under this order |
| the basis is reduced | `certify_f4_output`: monic, minimal under divisibility, each element its own normal form modulo the rest |
| exact comparison | the same equality assertion |

**Certification's one blind spot is carried by the API rather than left to the reader.** The three
runtime checks establish `I ⊆ <G>` and that `G` is a reduced Gröbner basis of `<G>`. They say
nothing about `<G> ⊆ I` and they cannot: every generator of `I` reduces to zero in any ideal
containing `I`. The sharpest case is `I = <x²>` against `G = {x}` — `x²` reduces to zero modulo
`x`, a one-element basis has no S-polynomial, `x` is monic and reduced, and `<x²> ≠ <x>`.

So reverse containment is a **precondition on where the basis came from**, and the report records
it. `certify_f4_output` is the entry point that asserts F4 produced the basis from these
generators — sound because every F4 matrix row is a monomial multiple of a current basis element,
and its only call site in the crate is F4's own return path. `certify_submitted_basis` is the entry
point for everything else, and its `is_complete()` is **false even when all three checks pass**,
with `first_failure()` naming the containment that was not established. Two tests pin this down: one
runs the `<x²>` case and requires `checks_passed() && !is_complete()`, and one runs the same basis
under both provenances to show that the provenance is the entire difference. The structural
invariant is additionally checked against an independent Buchberger basis.

### Against Singular

M22-I threads `F4Options` through the differential harness, so the external oracle checks the
*strategies* and not only the default. `SweepOptions::f4` is the F4 analogue of the `fglm` field M18
added for the same reason.

**This did not work in the first version of M22-I, and the review caught it.** The sweep took the
configuration, used it to compute the basis whose border monomials the oracle was asked about, and
then called a comparison that recomputed the basis under `F4Options::default()`. Every
configuration agreed with Singular because the configuration was never what Singular saw. The claim
was unsubstantiated rather than wrong, which is worse in a validation harness.

The fix is a second pair of entry points — `verify_case_with` and `verify_recorded_with` — that take
the caller's `F4Options` and compute the source basis with them; `verify_case` and `verify_recorded`
remain as the default-configuration fixture path. Two tests hold it in place:

| test | what would break it |
|---|---|
| `test_the_configured_f4_options_reach_the_source_basis` | runs a configuration F4 **cannot finish** under (`max_batches: Some(1)`) and requires `Check::SourceBasis` — if the parameter were dropped again, the default would succeed and the test would fail |
| `test_a_perturbed_tail_is_rejected_although_the_leading_monomials_agree` | perturbs one *constant* term of one oracle basis element, asserts the leading monomial is unchanged, and requires rejection under **every** configuration — so the comparison is tail-sensitive and not leading-monomial-sensitive |

```text
cargo test --release --lib -- --ignored --exact \
    grobner::differential::tests::test_m22_strategies_agree_with_singular
```

Eight configurations — baseline, `SmallMultiplierDegree`, `SmallMultiplierMonomial`, `Observe`,
`CertifiedLimited { slack: 4 }`, `Deferred { slack: 4 }`, `certify`, and three together — each on
**24** random systems, which is exactly the `4 x 6` cross product of supported variable counts and
characteristics that the sweep walks in a fixed order. The earlier version ran eight systems, which
reached GF(2) and GF(3) only and asserted nothing about which fields it had reached; the field and
variable-count coverage is now **asserted from the agreed cases** rather than inferred from the
index arithmetic. **All eight pass, with no disagreement and no oracle failure**, in 13.6 s.

The fixtures give the same check with no Singular installed, since a fixture *is* a recorded
Singular answer. `cargo test --lib agrees_with_the_recorded_oracle` runs all eight configurations
over all 240 committed ideals, and it runs in CI — as **one test per configuration**, because
`cargo nextest` runs each test in its own process and eight tests of eleven seconds cost eleven
seconds of wall clock where one test of ninety costs ninety. A further test asserts that every
configuration in the list has an offline test of its own, so adding a ninth cannot reach the live
sweep and quietly miss CI.

Each workstream separately asserts its strategy returns the baseline's basis on a fixed corpus, and
the baseline was already differentially tested; composing those is a valid argument but it is an
argument, and this checks the strategies against the oracle directly.


## 5. The default decision

**No default changed.** §11.5's bar is that an optimization be correct, measurably better on a
relevant workload, worth its memory and complexity, free of unacceptable regressions, and not
dependent on unverified assumptions about an arbitrary input. Against it:

| candidate | correct | better | no regressions | verdict |
|---|---|---|---|---|
| `PairSchedule::SmallMultiplierMonomial` | yes | **7%–14.5% alone**, under the 20% bar; **−28% matrix width in combination with a cap** | — | **not alone** |
| `PairSchedule::SmallMultiplierDegree` | yes | row operations only; matrix larger | — | **no** |
| `HilbertSelection::CertifiedLimited` | yes | matches a fixed cap | slack is instance-dependent | **no** |
| `HilbertSelection::Deferred` | yes | no | **catastrophic** | **no** |
| a fixed batch cap | yes | **3.6x and 2.2x on MQ** | a loss on square Poseidon systems | **not as a fixed number** |
| `certify` by default | yes | n/a | 67x on Poseidon | **no** |

The batch cap is the interesting row and the one that is *not* simply rejected. It clears both of
§11.5's thresholds on the overdetermined MQ instances — 24%–64% less peak memory, 3.6x and 2.2x
faster — and loses on the square Poseidon systems, where the pair count does not move under capping
so the extra matrices are pure overhead. **The honest default is therefore neither a fixed cap nor
none**, and choosing between them from the input is a planner question rather than an `F4Options`
question: `grobner::planning` already selects a solving route from `analyze`'s structural reading,
and "overdetermined enough that capping pays" is the same kind of judgement. That is left for M23
rather than guessed at here.

The schedule's row says "not alone" rather than "no" because of the ablation's interaction result:
by itself `SmallMultiplierMonomial` is a 1% change in matrix width on the decisive instance, and
*with* a cap of 64 it is 467 columns against 652 — a 28% cut that neither change produces on its
own. So the candidate M23 should weigh is **the pair (cap, schedule)**, not either in isolation, and
that is one more reason the cap question belongs to the planner rather than to a constant.

## 6. What M22 corrects

### Two of M22's own claims, after review

Both were caught in review of the PR stack, and both were claims about *evidence* rather than
errors in the Gröbner machinery:

1. **"`SmallMultiplier` is Sakata–Takagi's refinement, and it is a null result."** The implemented
   comparator ordered pairs by the multiplier's total *degree*; the published one compares
   multiplier *monomials*, which is a different and strictly finer relation. The degree comparator's
   null result is real and says nothing about the published strategy — which, implemented exactly,
   is the best schedule measured on every structural counter on the three largest instances and cuts
   the capped configuration's matrix width by 28% on the decisive one. §1.2, and
   [`research/pair-scheduling.md`](research/pair-scheduling.md) §2.
2. **"All seven strategies were compared directly against Singular."** They were not. The sweep
   threaded `F4Options` as far as the oracle query and then compared a basis recomputed under
   `F4Options::default()`, so each configuration agreed with Singular without Singular having seen
   it. §4 has the fix, the two regression tests that would now fail, and the corrected result — and
   the coverage claim was also overstated, at two of six fields rather than six.

### Two statements from M21 and one from the README

1. **"Nine variables solve at `t = 2` and fail at `t = 3`"** is confounded: the two instances have
   different algebraic dimension. §1.7.
2. **"because the MDS layer couples three words rather than two"** — the README's explanation for
   the above — is wrong. Pinned, the `t = 3` system is the fastest of the three.
3. M22-0's own first framing of the mutant question counted *elements*; M22-D showed the batch and
   regression counts are the measure, and that element count does not predict opportunity. §1.5.

One instrumentation bug was found and fixed inside M22-C during its own measurement run:
`pairs_withheld` counted all pending pairs rather than those at the degree being selected, which
overstated it severalfold. The published tables are from the corrected build.

## 7. Limitations, stated

- **Timings are single runs on a shared machine** with other work on it. Differences under about 20%
  should not be read; the structural counters — pairs, batches, columns, peak entries, row
  operations — are exact, and every conclusion above rests on those where it can.
- **Two instances is not a curve.** The variable-order result is two Poseidon systems at one state
  width; the batch-cap result is two Fukuoka type III instances. Both are consistent and neither is
  a scaling law.
- **No full-round Poseidon claim.** The 2026 initiative's CICO instance is `t = 16, R_F = 6, R_P = 8`
  — 104 S-box variables plus fourteen free inputs — and the largest instance here has nine
  variables. `CicoInstance::reduced_from` carries what each instance was reduced from so this cannot
  be lost.
- **The bounty's relaxed CICO verifier is still not modelled**: its condition is on the low bits of a
  canonical integer representative, which is not a polynomial identity over the field.
- **The semiregular model was validated on top forms**, which is a different ideal from the
  inhomogeneous system it is derived from. Every table that uses it says so.
- **`F4Options::max_live_bytes` is a budget on matrix entries, not on the process.** It does not
  cover the dense buffer, the monomial-to-column map, or allocator overhead, and no figure here is a
  measured RSS except where labelled as one.
- **The Hilbert recursion is bounded by a node budget.** A failure makes the cap inert and is
  counted; it is not a silent fallback.

## 8. Resource policy

Every table states its configuration. The budgets used throughout: `max_matrix_columns = 60_000`,
`max_live_bytes = 400 MB` (slack: the effective live cap is the `min` of the two budgets, so `max_live_nonzeros` bound first at 20 000 000 entries — **320 MB** over these fields' 16-byte entry; #322, #469), `max_batches = 20_000`, which are the ones M21 measured with plus a batch
ceiling that a small cap makes necessary — the same work split into many more matrices has to fail
reproducibly rather than be killed by whoever is watching.

A reported crossing distinguishes the matrix row limit, the column limit, the live-entry limit, the
live-byte limit, and the batch limit, each as its own `F4Error` variant naming the limit it crossed.
F4 has no cooperative time check, so a hard wall-clock bound needs an external supervisor and none of
the figures above rely on one. Memory estimates are estimates and are never reported as measured RSS.

## 9. Test matrix

**Mathematical correctness.** Existing bases unchanged under default options; every pair schedule,
every Hilbert mode, and `certify` return the identical basis over the correctness corpus under all
three monomial orders and all three criterion combinations; chain and Gebauer–Möller invariants hold
under reordered batches *and* under deferral, which is why deferral moves pairs without recording
them as handled; Hilbert predictions are never treated as proved redundancy, and no mode discards a
pair; certification rejects every single-element truncation of a correct basis and a non-monic
basis, and its one blind spot — a reduced Gröbner basis of a strictly larger ideal — is pinned by its
own test; nonradical and positive-dimensional ideals are in the ablation corpus; differential tests
against Singular pass under every M22 strategy.

**Performance and reproducibility.** Per-degree metrics are available and tested, and reconcile
exactly with the whole-run counters; profiling is off by default and a profiled run returns the same
basis; Fukuoka and Poseidon inputs are pinned by SHA-256 and by `reduced_from`; every benchmark
states its configuration; the controlled Poseidon comparison accounts for dimension; certification
overhead is reported separately; failure-stage diagnostics survive a crossed budget; reproduction
commands are in §11.

**Engineering.** Stable Rust; `cargo test` green in debug and release; `cargo clippy --all-targets
--all-features` clean; `cargo fmt` clean; no new criterion is enabled by default and no unsound one
exists; existing public solver contracts unchanged; memory limits enforced; benchmarks run one
instance per process where they are large; no new network dependency in ordinary CI — the MQ data is
fetched by a script and every test that needs it is `#[ignore]`d.

## 10. Where this leaves the research backlog

- **#74 is not complete.** The Hilbert-driven half is answered — diagnostic machinery built, model
  validated, cap measured and rejected as a default. The **mutant** half is answered only for the
  immediate-priority form; MF4's auxiliary basis and degree-decreasing phases are untried, and §1.4
  gives a reason to expect them to be difficult rather than a reason not to try.
- **#81 is advanced, not closed.** Solving degrees are now measured per instance and separated from
  the degree of regularity, and the semiregular model's accuracy is quantified. What is missing is
  the curve against round count that the issue asks for: three Poseidon points is not one.
- **#79** (comparing polynomial formulations) is where §1.6's last row points, and M22-E's
  `VariableOrder` and `AffineElimination` are the machinery for it.
- **#82 and #85** (multivariate resultants; Gröbner versus resultants) are what §1.9 recommends
  taking next.

## 11. Reproducing

```sh
tools/fetch-mq-challenge.sh                           # Fukuoka toy examples, not redistributed

cargo run --release --example f4_degrees               # §1.1, §1.5, §1.7, §1.8
cargo run --release --example f4_schedule              # §1.2
cargo run --release --example hilbert_study            # §1.3
cargo run --release --example hilbert_driven -- mq3-n10  # §1.4
cargo run --release --example cryptanalysis_ladder     # §1.6, §1.7
cargo run --release --example m22_ablation             # §3

cargo test --lib                                       # §9
cargo test --release --lib -- --ignored --exact \
    grobner::differential::tests::test_m22_strategies_agree_with_singular
```

Per-workstream detail, with the full tables:

- [`docs/research/degree-profiles.md`](research/degree-profiles.md) — M22-0
- [`docs/research/pair-scheduling.md`](research/pair-scheduling.md) — M22-A
- [`docs/research/hilbert-functions.md`](research/hilbert-functions.md) — M22-B
- [`docs/research/hilbert-driven.md`](research/hilbert-driven.md) — M22-C
- [`docs/research/mutants.md`](research/mutants.md) — M22-D
- [`docs/research/structure-experiments.md`](research/structure-experiments.md) — M22-E

## 12. References

Sakata, K., Takagi, T. (2026). *An Efficient Variant of F4 Algorithm for Solving MQ Problem.* IACR
TCHES 2026(3), 1284–1309. <https://doi.org/10.46586/tches.v2026.i3.1284-1309> — the primary
reference for HDF4, `SelectPairLimited`, the refined pair ordering, and mutant-F4.

Sakata, K., Takagi, T. *An Efficient Algorithm for Solving the MQ Problem Based on Non-Homogeneous
Hilbert-Driven Strategies.* <https://eprint.iacr.org/2023/1650>

Bigatti, A. M. (1997). *Computation of Hilbert–Poincaré series.* J. Pure Appl. Algebra 119, 237–253.
Bayer, D., Stillman, M. (1992). *Computation of Hilbert functions.* J. Symbolic Computation 14,
31–50. — the recursion `grobner::hilbert` implements.

Fukuoka MQ Challenge: <https://www.mqchallenge.org/>. Poseidon Cryptanalysis Initiative:
<https://www.poseidon-initiative.info/>, with reference implementation and verifiers at
<https://github.com/khovratovich/poseidon-tools>.
