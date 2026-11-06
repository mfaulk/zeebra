# Elimination that is not a Gröbner basis: a resultant on the registered CICO slices

Reference for M23-E (#141), which consumes #82 and #85. **§1–§5 are M23-E, with the figures it
took; §6 supersedes §4 and amends §2 and §5, and says so inline. Nothing is overwritten.**

```sh
cargo run --release --example resultant_cico          # ~2 min: the four-round rows now complete
cargo test --lib grobner::research::resultant
cargo test --release --lib grobner::research::resultant -- --ignored   # the four-round row, ~1 min
```

The spike the plan asks for, on the instances that make the comparison mean something: these are the
**registered** `t = 16` reductions M23-B measured, sliced at the same precommitted seed, so the
resultant's cost sits beside an F4 figure for exactly the same problem.

## 1. The structure, and why F4 is not told about it

Fix twelve of the fourteen free inputs and two unknowns remain. Every S-box output is then a
*polynomial in those two*: the permutation is a straight-line program, so there is nothing to solve
for, only to evaluate. The whole 46-equation system collapses to **two polynomials in two
variables**, and the CICO condition is their common root.

The S-box-per-variable formulation exists to stop the degree compounding — `y − L^3 = 0` is degree 3
whatever the round count — and pays 32 extra variables for it. At `t = 16` those variables are what
make the matrices unaffordable: M23-B measured fourteen of eighteen rows dying on live entries at
degree 4–5. Evaluating them away trades the variables back for degree `3^rounds`, and the question
is where that trade stops paying.

## 2. Measured

One resultant eliminates the second unknown; its roots are candidates for the first; each candidate
is extended and then checked **by running the permutation**. Nothing here decides that a candidate
is a solution — a resultant root is a necessary condition, not a sufficient one.

**These are the M23-E figures, taken with Lagrange interpolation at consecutive points.** §6
supersedes them: the interpolation is now an inverse NTT on a power-of-two subgroup, the four-round
rows complete, and the two-round row's total drops. They are kept because §3 and §5 are written
against them.

| row | rounds | bivariate degree | terms | build | resultant degree | Bézout | eliminate | roots | verify | **total** | F4 on the same slice |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `t16 R_F=2 R_P=0` | 2 | 9 | 55 | 2.8 ms | **81** | 81 | 30.8 ms | 18.1 ms | 0.5 ms | **52.2 ms** | **30 142 ms** |
| `t16 R_F=2 R_P=2` | 4 | 81 | 3 403 | 431 ms | — | 6 561 | see §4 | — | — | — | stopped at the entry cap |

**578x on the row both routes can do**, and the resultant returns *all three* base-field witnesses
where F4's search returns the first one it finds. Both were checked through the permutation.

The bivariate degree is exactly `3^rounds` on every row — the straight-line bound, with no
cancellation — and the resultant's degree on the 2-round row is exactly the Bézout bound `9 × 9`.
So nothing about Poseidon's structure reduces the degree here; what the resultant exploits is the
*variable count*, not a degree collapse. That is worth stating plainly because the plan asked
whether a structural degree reduction appears, and the answer is **no**.

> **Superseded by §6.3, and the sentence above is wrong.** The "no" was drawn from one row whose
> `R_P = 0`, which is exactly the case where the Bézout bound `d^{2R_F+2R_P}` and the published
> experimental degree `d^{2R_F+R_P}` coincide — so that row could not have seen a collapse whether
> or not one exists. §6.3 measures the four-round row with `R_P = 2` at degree **729 against a
> Bézout bound of 6 561**, confirming the published formula.

## 3. Why this is not a general answer

The resultant route costs about `16 · 3^{5·rounds}` field operations before any polynomial
arithmetic: `2d²` interpolation samples of an order-`2d` Sylvester determinant, with `d = 3^rounds`.
That is 1.0 × 10⁶ at two rounds, 2.3 × 10⁸ at three, 5.6 × 10¹⁰ at four, and 10¹⁸ at six — and the
*evaluation* itself has to cube a polynomial with `d²/2` terms, which is 266 000 terms at six
rounds.

So the reach of **this implementation** is two rounds, and §4 is the four-round attempt. The example
predicts rather than attempts anything past `10^10` predicted operations, printing the arithmetic
that rules each row out. F4's reach on the same slices was also two rounds — so what the spike
establishes is not a frontier extension but a **cost difference of 578x at the frontier both
routes share**, plus an arithmetic ceiling for the alternative that F4 does not have in writing.

Two constants are visibly loose and would be the first things to fix in an implementation
milestone, not in a spike:

- **The sample count.** The degree bound `n·deg_x(f) + m·deg_x(g)` is `2d²`, and the observed degree
  is `d²` — exactly 2x loose on the row that finished. An early-terminating interpolation would
  halve the work and need no bound at all.
- **The determinant.** This takes an order-`2d` determinant per sample through the generic dense
  path. A Sylvester matrix is structured, and a subresultant or Euclidean algorithm is
  asymptotically better; the module docs record why the spike did not use one — the specialization
  trap it would have to handle is exactly what the determinant construction avoids.
- **The interpolation**, which §4.1 measures at `O(n³)` and which turns out to dominate both of the
  above. Ranked there rather than here, because it took attempting a row that does not finish to
  see it.

## 4. The four-round row, attempted

> **Superseded by §6.** This section records the state of the four-round row under *cubic* Lagrange
> interpolation: it did not finish. With #162's quadratic interpolation it finishes in about 40 s,
> and with the subgroup route of §6 in about 49 s. The figures below are kept because they are the
> measurement that chose what to fix.

`--all` attempts what the guard declines. On `t16 R_F=2 R_P=2` — four rounds, so degree 81 — the
symbolic evaluation takes **431 ms** and produces two polynomials of 3 403 terms each, exactly the
straight-line degree. The resultant then needs 13 123 samples of an order-162 Sylvester determinant,
and **it had not finished after two hours** when this was written. §4.1 is why.

### 4.1 Where the time actually goes, measured

The first draft of this section blamed the determinants. That was wrong, and the measurement is
easy: `lagrange_interpolate` is **cubic** in the number of points.

| points | time | factor for 2x the points |
|---:|---:|---:|
| 250 | 28.6 ms | — |
| 500 | 219.4 ms | 7.7x |
| 1 000 | 1 632 ms | 7.4x |
| 2 000 | 12 880 ms | 7.9x |

`7.4x`–`7.9x` per doubling is `2³`: the implementation builds each of the `n` Lagrange basis
polynomials by multiplying `n − 1` linear factors into a growing polynomial and then dividing, which
is `O(n²)` apiece and `O(n³)` in total. Extrapolating 12.9 s at 2 000 points to the 13 123 the
four-round row needs gives **about an hour for the interpolation alone** — against roughly
`3 × 10^10` field multiplications, or a few minutes, for all 13 123 determinants together.

So the ranked list of what to fix is not what §3 guessed. **The ranking below is the pre-#162 one
and is superseded**: it is kept because it is the measurement that chose what to fix, and each entry
carries what later measurement did to it. The current ranking is §6.6's.

1. **The interpolation.** `O(n³)` where Newton's divided differences are `O(n²)` and a product-tree
   or NTT evaluation is `O(n log² n)`. KoalaBear has the two-adic roots of unity for the NTT route —
   #147 landed them — and 13 123 points pad to 16 384.
   **Fixed, in part: #162 stage 1 made `lagrange_interpolate` `O(n²)`, and the 13 123-point
   interpolation above now takes 1.37 s measured rather than the extrapolated hour. The table in
   this section is the pre-#162 measurement and is kept as such; see
   [`fast-univariate.md`](fast-univariate.md) §4.3.2 for the same point counts after.**
   **Fixed again: the NTT subgroup route of §6 recovers 16 384 points in 2.1 ms. §6.4 argued that
   ended the direction; §6.6 measures it back in contention once the determinants are parallel —
   at 32 workers the reference route is 55% Lagrange solve.**
2. **The sample count**, 2x loose: the degree bound is `2d²` and the observed degree is `d²`.
   **Now the largest remaining *algorithmic* win, and larger than 2x — §6.3 measures a resultant
   whose degree is 9x below the bound, not 2x. Not implemented.**
3. **The determinant**, which is a few minutes of the hour and therefore last. **Now first, and
   done in part.** With the interpolation at milliseconds it was 99% of the four-round row (§6.4);
   #180 spread the independent determinants over workers and measured **29–31x at 32 of this box's
   128 cores**, at 92–95% parallel efficiency, taking the four-round row from 49.7 s to 2.16 s with
   byte-identical coefficients. §6.6. What remains unexploited is the Sylvester *structure* — the
   path is still a generic dense LU per sample — which is an asymptotic improvement rather than a
   constant factor and composes with the parallelism.

That reordering is the useful output of attempting a row that does not finish. `bivariate_resultant`
is a reference implementation and the module says so; what the spike establishes is which of its
three costs is worth an implementation milestone, and it is not the one that looked obvious.

Together those are a factor of several before any algorithmic change, which is why the conclusion is
"scope an implementation" rather than "the resultant route stops at two rounds". What can be said
without an implementation milestone is: **two rounds in 52 ms, four rounds not in two hours, and
six rounds never** — `3.3 × 10¹⁵` field operations for the resultant alone, before cubing a polynomial
with 265 720 terms.

## 5. What this decided

The M23-E answers, with what §6 revised. **The original answers are kept verbatim**: the two
columns are the record of what one measurement supported and what the next one changed.

| question | M23-E answer | revised by §6 |
|---|---|---|
| Does structure-aware elimination beat general F4 here? | **Yes, by 578x** on the one row both can do, and it returns every witness rather than the first. | unchanged, and the factor is larger: the two-round total is now 7.0 ms, so **4 306x**. |
| Is the univariate polynomial manageable? | Yes at two rounds — degree 81, 17 ms to find its roots over KoalaBear. | Yes at four — degree 729 in 60 ms, degree 6 561 in 4.2 s. |
| Does Poseidon's structure reduce the degree below Bézout? | **No.** The bivariate degree is exactly `3^rounds` and the resultant's is exactly `d²`. | **Sometimes yes.** Four rounds with `R_P = 2` gives **729 against 6 561**; with `R_P = 0` it gives 6 561 exactly. The bivariate degree is still exactly `3^rounds`. §6.3. |
| Does it scale? | No. The cost is `16 · 3^{5·rounds}`: two rounds in 52 ms, four rounds not in two hours with this implementation, six rounds `3.3 × 10^15` operations. | Four rounds in **40 s** by the reference route, 49 s by the subgroup one, and **2.16 s on 32 cores** (§6.6). The exponent is unchanged, so six rounds is `3.3 × 10^15` serially and `10^14` on 32 cores: the reach moved one step up the ladder and the constant moved 30x, neither of which is an order of growth. |
| Which cost should an implementation attack first? | **The interpolation**, measured at `O(n³)` — not the determinant, which is a few minutes of the hour. §4.1. | Revised twice. §6.4: the interpolation is **3.9%** of the four-round row and, *serially*, provably cannot dominate again — so the sample count, then the determinant. §6.6 then measured the determinant: **the determinant, and it was 29–31x of parallelism at 92–95% efficiency**, 49.7 s to 2.16 s. That also undoes §6.4's "provably": with the determinants parallel the recovery is 55% of the reference route at 32 workers, so the ranking is now **the sample count, then the Sylvester structure, with the interpolation back in contention at high worker counts**. |
| Did it extend the frontier? | **No** — both routes reach two rounds. What it changed is the cost there, by 578x. | **Yes** — verified CICO witnesses at **four rounds** on two registered reductions, where F4 stops at two. Credit goes to #162's quadratic `lagrange_interpolate` and the formulation of §1, **not** to the subgroup route, which §6.5 measures as slower. §6.1. |
| Should a resultant implementation be scoped? | Yes, and narrowly: early-terminating interpolation plus a structured determinant, aimed at the slice shape, not at a general solver. | Narrower still. The interpolation half is finished and was the wrong half; the **parallel** determinant is done and measured (§6.6). What remains is a **predicted** sample count from §6.3's degree formula, guarded by an off-domain check, and a **structured** determinant exploiting the Sylvester form — the one piece that is asymptotic rather than a constant. |

## 6. The four-round row completing, and a subgroup interpolation that does not help

Reference for #82, #85 and #180. Four results, in order of what they are worth:

1. **The four-round rows complete with verified witnesses**, where M23-E reached two rounds. §6.1.
   The enabling change is #162's quadratic `lagrange_interpolate`, not anything in this milestone.
2. **The published `d^{2R_F+R_P}` resultant degree is confirmed** on three registered slices, one
   of which discriminates it from both the Bézout bound and the other form the source gives. §6.3.
3. **The determinants parallelize at 92–95% efficiency** out to 32 of this box's 128 cores, taking
   the four-round row from 49.7 s to 2.16 s with byte-identical coefficients — and in doing so
   **falsify §6.4's claim** that no interpolation improvement could help this route again. §6.6.
4. **The NTT-subgroup interpolation is slower than the reference** single-threaded, by 1.23x–1.40x.
   §6.5. A negative result at the time; §6.6 measures the sign flipping at eight workers and the
   subgroup route winning by 1.7–1.8x at 32, which is why both routes were worth retaining.

`bivariate_resultant_ntt` is `bivariate_resultant` with the samples moved: the *same* Sylvester
determinant of the *same* two polynomials, eliminating the *same* variable, evaluated on a
power-of-two multiplicative subgroup rather than at `0, 1, 2, ...`, and recovered with
`fft::interpolate` instead of `lagrange_interpolate`. Nothing about the resultant's definition, the
CICO objective, the instance parameters or the verification condition changes; the abscissae do.
`bivariate_resultant_reference` is the retained reference with its two stages timed apart, which is
what makes §6.5 a comparison rather than two readings.

All figures below from one run of the command below on the `perf/resultant-subgroup-interpolation`
branch (#186) — the code as merged, which later commits on that branch change only in this
document — seed 1, on the development
workstation (128 logical cores, 500 GB; `-C target-cpu=x86-64-v3` from `.cargo/config.toml`,
`profile.release` with fat LTO and one codegen unit). **Single-threaded, unpinned, and taken under
the exclusive benchmark lock, `tools/benchlock.sh`** while five other agents were idle on it:

```sh
tools/benchlock.sh agentR cargo run --release --example resultant_cico
```

### 6.1 Measured, stage-separated

Subgroup route, which is the one the pipeline below consumes:

| row | rounds | build | samples | matrix order | determinants | interpolate | off-domain check | roots | lift | verify | **total** | peak RSS |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `t16 R_F=2 R_P=0` | 2 | 2.9 ms | 256 | 18 | 2.9 ms | **0.0 ms** | 0.1 ms | 0.9 ms | 0.2 ms | 0.0 ms | **7.0 ms** | 2.6 MB |
| `t16 R_F=2 R_P=2` | 4 | 419.3 ms | 16 384 | 162 | 48 054.4 ms | **1.9 ms** | 22.5 ms | 52.7 ms | 1.0 ms | 0.0 ms | **48 551.8 ms** | 14.2 MB |
| `t16 R_F=4 R_P=0` | 4 | 397.7 ms | 16 384 | 162 | 49 175.7 ms | **2.1 ms** | 23.1 ms | 3 933.3 ms | 2.0 ms | 0.0 ms | **53 534.0 ms** | 15.2 MB |

Peak RSS is the process figure from `/proc/self/status`'s `VmHWM`, measured. The estimate for the
interpolation's own live arrays — sample vector, domain, inverse domain, coefficients, at
`4 n · size_of::<F>()` — is **0.5 MB** at 16 384 points, and the gap to 14–15 MB is the bivariate
polynomials and the process itself, not the transform.

| row | resultant degree | Bézout | base-field roots | **verified witnesses** |
|---|---:|---:|---:|---:|
| `t16 R_F=2 R_P=0` | 81 | 81 | 3 | **3** |
| `t16 R_F=2 R_P=2` | **729** | 6 561 | 1 | **1** |
| `t16 R_F=4 R_P=0` | 6 561 | 6 561 | 2 | **2** |

**The four-round rows complete, and they return verified witnesses.** Every witness is checked by
`CicoInstance::is_solution`, which runs `permutation_plus_linear` — the same verifier every other
registered result in this repository is checked by. Nothing in the resultant code decides a
candidate is a solution. §2's two-hour non-result on `R_F=2 R_P=2` is superseded by the 48.6 s row
above, and by the 39.7 s §6.5 reaches on the reference route.

The witness coordinates are committed at
[`research/witnesses/resultant-cico-t16.json`](../../research/witnesses/resultant-cico-t16.json)
and re-verified through the permutation by
`grobner::research::resultant::tests::test_the_recorded_witnesses_verify_through_the_permutation`,
which takes milliseconds. The four-round run itself is reproduced by the `#[ignore]`d
`test_the_four_round_row_completes_on_the_subgroup_route`.

**This extends the verified-witness frontier on the registered reductions from two rounds to four.**
F4 stops at two (M23-B: fourteen of eighteen rows die at degree 4–5) and so did the resultant. It
is a frontier on *faithful reduced-round instances*, not on an official public problem: the
official targets are `R_F = 6` with `R_P ∈ {6, 8, 10}`, which §6.4 still prices at `3.3 × 10^15`
field operations and above. A larger reachable round count is not a fraction of those.

**Credit for the frontier move belongs to #162 and to the formulation, not to the subgroup
interpolation.** §4.1 blamed the cubic `lagrange_interpolate`, and #162 stage 1 made it quadratic:
13 123 points now interpolate in 1.5 s measured here. That alone is enough to make the four-round
row finish, and §6.5 measures the reference route doing so in 39.2 s of elimination. What the
subgroup route contributes is the interpolation at 1.9 ms instead of 1.5 s — and it pays for that
with 3 261 extra determinants, which costs more than it saves. The honest reading is that the elimination formulation of §1 and
#162's quadratic interpolation did this, and the NTT route is a **measured negative result** whose
value is §6.4's structural argument for why no interpolation improvement can matter here.

### 6.2 The domain, and the degree bound

The resultant's degree is at most `n·deg_x(f) + m·deg_x(g)` with `m = deg_y(f)`, `n = deg_y(g)`.
At four rounds every one of those is 81, so the bound is **13 122** and 13 123 samples determine the
answer. `interpolation_route` takes the smallest power-of-two subgroup with more than 13 122
elements — `2^14 = 16 384` — provided the field's two-adicity admits it. KoalaBear's is 24, so it
does; Mersenne-31's is 1, so there the route falls back to `bivariate_resultant_reference` rather
than building a domain that does not exist. `test_a_field_without_a_large_enough_subgroup_dispatches_to_lagrange`
pins that, and `test_the_domain_covers_the_degree_bound` pins the choice of 2^14.

§3 noted the sample count is 2x loose — the bound is `2d²` and the observed degree is `d²` — and
§4.1 ranked tightening it second. **It is deliberately not taken here.** The proven bound is what a
correct resultant must cover; the tighter count rests on the experimental formula of §6.3, which the
source leaves unproven. §6.4 records how to take it safely, and why it is now the largest remaining
win.

Padding to a power of two is not free, and that turns out to be the whole story of this milestone:
16 384 samples where 13 123 suffice is **3 261 extra order-162 determinants**, about 10 s. §6.5
measures what they buy.

### 6.3 The published `d^{2R_F+R_P}` resultant degree, confirmed

This is the result that answers #82, and it is a confirmation of a published claim rather than a
new one. [`graeffe-root-finding.md`](graeffe-root-finding.md) §2.4 records [JAZ] slide 22: the
expected resultant degree is `d^{2R_F+2R_P}` — the Bézout bound — "however, we experimentally
noticed that the degree of the resultant is `d^{2R_F+R_P}`", a saving of `d^{R_P}`. The source
leaves it **unproven**, its own authors asking why it also matches the ideal's degree, and this
repository recorded it as unproven and noted that the 2-round slice of §2 was *too small to
separate the two formulas*.

It is no longer too small. With `d = 3`:

| row | `R_F` | `R_P` | Bézout `d^{2R_F+2R_P}` | slide 19's `d^{2(R_F−1)+R_P}` | slide 22's `d^{2R_F+R_P}` | **measured** |
|---|---:|---:|---:|---:|---:|---:|
| `t16 R_F=2 R_P=0` | 2 | 0 | 81 | 9 | **81** | **81** |
| `t16 R_F=2 R_P=2` | 2 | 2 | 6 561 | 81 | **729** | **729** |
| `t16 R_F=4 R_P=0` | 4 | 0 | 6 561 | 729 | **6 561** | **6 561** |

**Three rows, three agreements with slide 22, and three disagreements with slide 19.** The source
gives both forms — slide 19 states `d^{2(R_F−1)+R_P}` and slide 22 states `d^{2R_F+R_P}` — and this
discriminates between them. The two `R_P = 0` rows are degenerate, since the Bézout bound and the
experimental degree coincide there; `R_F=2 R_P=2` is the row that separates them, and its factor of
nine is exactly the predicted `d^{R_P} = 3²`.

The measurement is checked three ways, which is what makes it a confirmation rather than an
observation:

1. The recovered polynomial is the **unique** one of degree below 16 384 agreeing with the
   determinant on the whole domain, and the true resultant's degree is at most the proven 13 122,
   so the recovered polynomial *is* the resultant and 729 is its actual degree.
2. It agrees with a direct Sylvester determinant at 8 random points **outside** the interpolation
   domain — a different code path, and points the interpolation never saw.
3. Its root lifts to a pair that `permutation_plus_linear` accepts.

**Why the degree collapses is still open**, as it is in the source. The plausible mechanism visible
in this construction is that partial rounds cube only word 0, so the degree-27 piece entering the
last full round is the same polynomial in every word up to a scalar; that makes the leading forms
of `f` and `g` proportional and drops the resultant's degree. **That is a hypothesis, not a
measurement**, and checking it is follow-up work.

The collapse is not cosmetic. It shows up in the shared tail both elimination routes pay: root
finding on the degree-729 polynomial is **59.5 ms** against **4 156.5 ms** on the degree-6 561 one,
a 70x difference. And it makes the sample count *predictable* rather than merely loose — §6.4.

### 6.4 Where the time goes now, and why the interpolation can never matter again

The ranking inverted twice. §3 guessed the determinant; §4.1 measured the cubic interpolation and
ranked it first; with the interpolation at 1.9 ms the determinant is **98.9%** of the four-round
subgroup row and **96.1%** of the reference one. One order-162 determinant is 2.9 ms through the
generic dense LU path, and there are 16 384 or 13 123 of them.

**That is not a one-row accident, and it is the structural claim worth keeping from this
milestone.** For a degree-`d` bivariate pair, the sample count goes as `2d²` and each sample is an
order-`2d` determinant at `(2d)³/3` operations, so the determinant work goes as `d^5`. Lagrange
interpolation at `n = 2d²` points is `O(n²) = O(d^4)` after #162. So:

> The determinant stage grows one whole power of `d` faster than the interpolation stage. Once the
> interpolation is quadratic, **no further interpolation improvement can change the end-to-end cost
> of this route at any round count.** An `O(n log n)` recovery removes a term that is already
> asymptotically negligible.

> **Superseded by §6.6, and this is the interesting correction.** The argument above holds for a
> **serial** route and silently assumes one. Spread the determinants over `p` workers and they cost
> `d^5/p` against the recovery's `d^4`, so the recovery returns to contention once `p` reaches the
> order of `d` — measured, at `d = 81` and `p = 32`, as the reference route spending 55% of its
> elimination inside `lagrange_interpolate`. The claim as stated above is wrong; the narrower one
> that survives is in §6.6.

That looked like it closed off the direction, which would have been more useful than a speedup. The
ranked list as of this section — see §6.6 for the current one — was:

1. **The sample count** — the largest remaining win, and larger than §3's 2x. §6.3's confirmation of
   `d^{2R_F+R_P}` makes the needed count **predictable a priori**, not merely adaptively
   discoverable: 730 points instead of 16 384 on `R_F=2 R_P=2` (22.4x) and 6 562 instead of 16 384
   on `R_F=4 R_P=0` (2.5x). Because the formula is experimental, the guard is the off-domain check
   this milestone already built — predict, sample, verify against a direct determinant at fresh
   points, and fall back to the proven `2d²` bound if the check fails. Not implemented here.
2. **The determinant** — 99% of the row today. A Sylvester matrix is structured and the generic
   dense LU path exploits none of it; the 16 384 determinants are also embarrassingly parallel, and
   this run used one core of 128. Either is a large constant factor and neither is algorithmically
   deep. **The parallel half is done and measured in §6.6: 29–31x at 32 cores. The structured half
   is not.**
3. **The interpolation** — done, twice, and provably not where the cost is. **The "provably" is
   retracted: see the note above and §6.6.**

The exponent is unchanged, which bounds every claim above. The route still costs about
`16 · 3^{5·rounds}` field operations: `3.3 × 10^15` at six rounds and `1.9 × 10^20` at eight, before
the bivariate evaluation has to cube a polynomial with 265 720 terms. **Four rounds in 52 s, six
rounds not with any constant factor this list can supply.** What moved is the reach by one step of
the ladder, not the growth.

### 6.5 The A/B: the subgroup route loses, at every size measured — single-threaded

> **Scoped by §6.6.** Everything in this section is at one worker, and the sign of the result
> depends on that: §6.6 measures the subgroup route winning by 1.7–1.8x at 32 workers, because its
> extra determinants parallelize and the reference route's Lagrange solve does not.

Every row runs **both** routes on the same two polynomials in the same process and asserts the two
answers are equal, so the comparison is free of build, machine and contention differences:

| row | subgroup determinants | subgroup interpolate | **subgroup** | reference determinants | reference `lagrange_interpolate` | **reference** | subgroup / reference |
|---|---:|---:|---:|---:|---:|---:|---:|
| `t16 R_F=2 R_P=0` | 256 → 2.9 ms | 0.0 ms | **2.9 ms** | 163 → 1.8 ms | 0.3 ms | **2.1 ms** | **1.40x** |
| `t16 R_F=2 R_P=2` | 16 384 → 48 054.4 ms | 1.9 ms | **48 056.3 ms** | 13 123 → 37 634.3 ms | 1 529.4 ms | **39 163.6 ms** | **1.23x** |
| `t16 R_F=4 R_P=0` | 16 384 → 49 175.7 ms | 2.1 ms | **49 177.8 ms** | 13 123 → 37 959.3 ms | 1 512.8 ms | **39 472.1 ms** | **1.25x** |

**The subgroup route is 1.23x–1.40x slower than the reference, on every row.** This is the
milestone's main measured result and it is a negative one. The arithmetic is plain in the table: on
the four-round row the subgroup route removes 1.53 s of interpolation and adds 3 261 determinants —
10.4 s — for a net loss of about 8.9 s. The per-sample determinant cost is the same on both routes
(2.93 ms against 2.87 ms), so the difference is entirely the power-of-two padding.

Taking the better route at every stage, the four-round row is therefore **about 39.7 s**
(419.3 build + 39 163.6 reference elimination + 22.5 + 52.7 + 1.0 + 0.0), not the 48.6 s the
subgroup column totals.

**Repeated.** A second run of the same binary under the same lock gave 1.40x, **1.19x** and
**1.19x**, against 1.40x, 1.23x and 1.25x above — so the sign and the rough size of the loss
reproduce, and the ~5% drift between runs is this workstation's noise with five other agents
active. Both runs agree exactly on every sample count, every resultant degree and every witness.

Two notes on comparability:

- §2's 30.8 ms for the two-round elimination is *not* comparable with either column: it was taken at
  a different commit against the cubic interpolator, and is left in §2 unaltered for that reason.
- `lagrange_interpolate` at 13 123 points measures 1.51–1.53 s here against the 1.37 s #162 recorded
  for the same point count. The difference is the element type — these rows use the 64-bit-backed
  `PrimeFieldElement64<KOALABEAR_PRIME>` and #162's sweep used the 32-bit-backed `KoalaBear` — and
  is reported rather than reconciled.

### 6.6 The determinants in parallel, and the recovery stage mattering again

Reference for #180. §6.4 ranked the determinant second and called it "a large constant factor,
neither algorithmically deep". That is now measured, and it also **falsifies §6.4's own asymptotic
claim about the interpolation** — which is the more interesting half.

`ResultantOptions::concurrency` spreads the independent determinants over worker threads. It
defaults to 1, so every figure above reproduces unchanged. The samples are written into their own
index rather than collected as they finish, so the recovered polynomial is a function of the
abscissa sequence alone: the resultant's coefficients and the witness set are **byte-identical at
1, 8 and 32 workers**, asserted by the run itself and pinned by
`test_the_registered_slice_gives_the_same_witnesses_at_every_concurrency` and
`test_the_resultant_does_not_depend_on_the_concurrency`.

Measured with

```sh
ZEEBRA_MACHINE="$(hostname)" ZEEBRA_AFFINITY=0-31 \
  flock /tmp/zeebra-bench.lock \
  taskset -c 0-31 \
  cargo run --release --example resultant_cico -- --concurrency 1,8,32
```

on the development workstation (128 logical cores, 256 MB L3, 500 GB; `-C target-cpu=x86-64-v3`
from `.cargo/config.toml`, `profile.release` with fat LTO and one codegen unit), seed 1, under an
exclusive benchmark lock, with the worker set **pinned to a 32-core subset** rather than left to
contend with the eight-core set the rest of the scoreboard uses. Two independent runs of the same
binary:

| row | workers | subgroup determinants | speedup | efficiency | reference determinants | speedup | efficiency |
|---|---:|---:|---:|---:|---:|---:|---:|
| `t16 R_F=2 R_P=2` | 1 | 49 261 ms | — | — | 39 632 ms | — | — |
| | 8 | 6 428 ms | 7.66x | 96% | 5 143 ms | 7.71x | 96% |
| | 32 | 1 674 ms | 29.4x | 92% | 1 301 ms | 30.5x | 95% |
| `t16 R_F=4 R_P=0` | 1 | 49 821 ms | — | — | 41 091 ms | — | — |
| | 8 | 6 482 ms | 7.69x | 96% | 5 189 ms | 7.92x | 99% |
| | 32 | 1 632 ms | 30.5x | 95% | 1 351 ms | 30.4x | 95% |

End to end on the subgroup route, including the shared 0.4 s bivariate build and the single-threaded
tail: `R_F=2 R_P=2` goes from **49.7 s to 2.16 s** and `R_F=4 R_P=0` from **54.5 s to 6.12 s**. The
second row's larger residual is its own degree-6 561 root finding — 4.0 s of it, untouched here and
tracked separately.

**Repeated.** The first run gave 7.40x/29.2x and 7.91x/30.6x against the 7.66x/29.4x and
7.69x/30.5x tabulated; the two agree on every sample count, every resultant degree and every
witness.

#### What the 5–8% shortfall at 32 workers is, by evidence

Not the core count: 32 workers on a 32-core pinned set returned 29.4–30.5x, and the box has 128.
The limit is the **all-core clock**, and the discriminating measurement is core-time per
determinant — wall clock times workers, divided by 16 384:

| workers | `R_F=2 R_P=2` | `R_F=4 R_P=0` |
|---:|---:|---:|
| 1 | 3.007 ms | 3.041 ms |
| 8 | 3.139 ms | 3.165 ms |
| 32 | 3.270 ms | 3.188 ms |

Per-determinant cost steps up 4% as soon as eight cores are busy and then moves 1–4% more out to
32. **A memory-bandwidth limit would widen monotonically with the number of concurrent streams, and
this does not** — it saturates at the point where the clock does. Two independent bounds agree:

- **Working set.** One determinant holds an order-162 matrix of eight-byte elements, 210 KB, and
  `crout_lu_pivoting` returns `L`, `U` and `P` beside it: about 840 KB live per worker. At 32
  workers that is 27 MB against this box's 256 MB L3, and measured peak RSS tracks it — 16.2 MB at
  one worker, 24.5 MB at eight, 54.9 MB at 32. Bandwidth has no way to bind here.
  `MILESTONE-SIMD-PARALLELISM.md` §8.2 is about misreading a working set on exactly this L3, and the
  point of quoting the figure is that it is small, not that it is fast.
- **The matrix build.** Building the Sylvester matrix is 26 244 element writes and 326 polynomial
  evaluations against the LU's roughly `162³/3 ≈ 1.4 × 10⁶` multiply-and-subtract steps — under 2%
  by operation count, and *per worker*, so it is not a serial bottleneck at any width.

#### Where the granularity argument stops

The two-round row is the counter-example that bounds the claim. Its 256 determinants are order 18,
about 8.6 µs each, and it gets 2.2–2.5x at eight workers and **gets slower** at 32 — 1.2–1.3 ms
against 2.2 ms serial. Dividing out the work gives about 35 µs of spawn and join per thread, which
is four times a whole determinant. `MILESTONE-SIMD-PARALLELISM.md` §6.4's aggregating-granularity
rule is what this is: the four-round rows clear it by a factor of 350, the two-round row does not
clear it at all, and the default of 1 worker is what keeps the small row honest.

#### §6.4's asymptotic claim does not survive concurrency

§6.4 argued that because determinant work grows as `d^5` and quadratic Lagrange interpolation as
`d^4`, no further interpolation improvement could ever change this route's cost. That argument
assumed **both stages serial**. Spread the determinants over `p` workers and they cost `d^5/p`
while the Lagrange solve stays `d^4`, so the recovery is back in contention as soon as `p` reaches
the order of `d` — and at `d = 81`, `p = 32` is already close enough to see it:

| row | workers | subgroup elimination | reference elimination | of which `lagrange_interpolate` | subgroup / reference |
|---|---:|---:|---:|---:|---:|
| `t16 R_F=2 R_P=2` | 1 | 49 262 ms | 41 272 ms | 1 640 ms (4%) | **1.19x** |
| | 8 | 6 429 ms | 6 773 ms | 1 630 ms (24%) | **0.95x** |
| | 32 | 1 675 ms | 2 884 ms | 1 583 ms (55%) | **0.58x** |
| `t16 R_F=4 R_P=0` | 1 | 49 822 ms | 42 736 ms | 1 645 ms (4%) | **1.17x** |
| | 8 | 6 482 ms | 6 832 ms | 1 643 ms (24%) | **0.95x** |
| | 32 | 1 633 ms | 2 957 ms | 1 606 ms (54%) | **0.55x** |

**§6.5's negative result inverts.** The subgroup route loses by 1.17–1.19x single-threaded and wins
by 1.7–1.8x at 32 workers, and the arithmetic is plain: its extra 3 261 determinants parallelize and
the reference route's 1.6 s Lagrange solve does not. At 32 workers the reference route is *more than
half* serial interpolation.

So the two routes are not redundant after all, and retaining the one §6.5 measured as a loss turns
out to have been the right call for a reason §6.5 could not see. The honest form of §6.4's claim is
narrower: **a serial route cannot be helped by a faster interpolation; a parallel one can, and the
NTT recovery is the one that keeps up.** Nothing here changes the exponent — the route still costs
about `16 · 3^{5·rounds}` operations and six rounds is still `3.3 × 10^15`, which 32 cores move to
`10^14` and not to reach.

#### The scoreboard, and what is not recorded here

The figures above are **not** on the cryptanalysis scoreboard as a speedup, and the machinery now
refuses to make them one. `Environment::concurrency` is recorded on every run and defaults to 1 for
every record written before it existed; `Comparison::of` returns
`ScoreboardError::DifferentConcurrency` rather than a ratio when two runs disagree on it; and
`Scoreboard::best` — the headline the rendered table quotes — considers uncontended runs only, so a
30x core count cannot displace the single-core figure it is not comparable with.
`Scoreboard::best_at` reaches the parallel rows deliberately. This differs from #166, which
parallelized a differential sweep whose product was an agreement verdict and therefore needed none
of this.

### 6.8 The six-round build, measured — and it is memory, not time

The six-round attempt (#211) is costed in `MILESTONE-PUBLISHED-ATTACK-REPRODUCTION.md` §7.4, which
flags the symbolic build as the one stage whose cost law nothing had checked: it has been under 1%
of every row measured here, and at six rounds the outputs grow from ~3 400 terms to ~266 000. §7.5
of that plan therefore asks for `cico_bivariate` to be timed **alone** on
`poseidon31-cico-t16-rf2-rp4` before any determinants are authorized. It was, single-threaded on
one pinned core under `tools/benchlock.sh`:

| | §7.4's estimate | **measured** | |
|---|---:|---:|---|
| elapsed | ~36 min | **48.37 min** | 1.34x — the same order, so the time estimate holds |
| peak RSS | ~68 MB | **57.0 GB** | **838x** |

The outputs are two bivariate polynomials of degree 729 with **266 815 terms** each, which is
exactly `(729+1)(729+2)/2`: the dense bivariate triangle, with no cancellation anywhere in six
rounds. So the term-count extrapolation was right and the memory estimate was not.

**The mechanism, read rather than guessed.** `SparseMultiPoly`'s multiply materialises every
pairwise term-product in one `Vec` and collects like terms afterwards, so its transient is
`O(|a|·|b|)` entries however few distinct monomials the product has. `cico_bivariate` cubes sixteen
degree-243 words as `p * p` then `(p²) * p`:

| step | term-products | at 16 bytes an entry |
|---|---:|---:|
| `p * p` | 29 768² = 8.86 × 10⁸ | 14.2 GB |
| `(p²) * p` | 118 827 × 29 768 = 3.54 × 10⁹ | **56.6 GB** |
| the product's actual size | 266 815 terms | 4.3 MB |

56.6 GB predicted against 57.0 GB measured, and the RSS trace is a **sawtooth** with one peak per
state word rather than a monotonic climb — each word's transient is freed before the next
allocates. It is a transient four orders of magnitude larger than the result it builds, not a leak.

Two consequences:

1. **The build is now a binding stage, and binds on memory first.** 48.4 minutes is about half of
   §7.4's whole ~1–1.5 h estimate for the row, where the build has been 0.8% of every row before
   it. A collecting or chunked multiply would bound the live set by the output size instead of the
   product count — tracked in #243, with the caveat that a map insert per product may cost more
   time than `push` plus one sort, so it is a memory win that has to be measured for time.
2. **§7.4's "peak memory is not a concern" is wrong by 838x**, in the direction that matters: 57 GB
   is 11% of this workstation's RAM for one single-threaded build, and two concurrent six-round
   builds would be noticed by every other process on the box.

Measured with `--row poseidon31-cico-t16-rf2-rp4 --build-only`, which runs before the budget check
on purpose: the budget is on the determinants and the build runs none of them, so the build of a
row whose determinants are unaffordable is still a bounded, interruptible measurement. Peak RSS
from `VmHWM`, polled externally and cross-checked against `util::peak_resident_bytes`, which reads
the same field. Reported as an upper bound on the elapsed: this agent's own `cargo build` and
`cargo test` ran on eight unrelated cores during part of the window, which the lock does not
serialize and which inflates a memory-bandwidth-bound figure rather than deflating it.

**No determinants were run on this row.** At six rounds the proven `2d²` fallback is 1 062 882
order-1 458 determinants — 25.7 single-core days — so a falsified prediction there would be
reported as *prediction falsified, generic bound unaffordable* rather than retried, and
`examples/resultant_cico` now prints that consequence before it starts a row instead of discovering
it mid-run.

## 7. The deeper consequence

It is about the **formulation**, not the algorithm. Three orders of magnitude separate two ways of
writing the same CICO slice, and the expensive one is the one the whole cryptanalysis literature
uses by default because it bounds the degree. When the free-variable count is small, bounding the
degree is the wrong trade — and the scoreboard is what made that visible, because both routes are
measured against the same registered problem.

§6 does not change that and is a smaller point by comparison: it moves one stage of the cheap
formulation from cubic to quasi-linear, which buys a round count. The formulation is what bought
the three orders of magnitude.
