# Elimination that is not a Gröbner basis: a resultant on the registered CICO slices

Reference for M23-E (#141), which consumes #82 and #85, continued by M24-B (#179, #211). **§1–§5
are M23-E, with the figures it took; §6 supersedes §4 and amends §2 and §5; §6.7 supersedes §6.4's
ranked list. Each says so inline. Nothing is overwritten.**

```sh
cargo run --release --example resultant_cico          # the rows the budget admits
cargo run --release --example resultant_cico -- --concurrency 1,8,32          # §6.6's scaling
cargo run --release --example resultant_cico -- --row poseidon31-cico-t16-rf2-rp4 --build-only
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

### 6.7 The predicted sample count, measured — and §6.4's ranked list closed out

§6.3 confirmed [JAZ] slide 22's experimental degree `d^{2R_F+R_P}` on three registered rows and
§6.4 ranked acting on it first. #179 does, and this is what it measures. **§6.4's ranked list is
superseded by the one at the end of this section**; it is kept where it is, because it chose the
order the work was done in and was right about it.

#### Three sample counts, and which denominator a factor is quoted against

| count | where it comes from | `rf2-rp2` | `rf4-rp0` |
|---|---|---:|---:|
| NTT domain | the proven bound padded to a power of two — §6.2 | 16 384 | 16 384 |
| proven `2d²` | `n·deg_x(f) + m·deg_x(g)` + 1, the reference route — §6.5 | 13 123 | 13 123 |
| **predicted** | `3^{2R_F+R_P}` + 1, from the row's own `alpha`, `R_F` and `R_P` | **730** | **6 562** |

So the sample-count reduction is **22.44x** and **2.50x** against what the route did by default
before #179, and **17.98x** and **2.00x** against the proven reference route. The second pair is
the one the measurements below use, because the reference is what runs beside the prediction in the
same process at the same concurrency. Both pairs are exact — they are ratios of integer sample
counts, not timings.

#### The four cells

`poseidon31-cico-t16-rf2-rp2` and `-rf4-rp0`, KoalaBear, seed 1. One binary from one tree, so the
only difference between cells is a flag; each invocation measures the predicted and the proven
counts in one process on the same two polynomials at one concurrency, which isolates #179, and the
two concurrencies give #227's effect at both counts. `taskset --cpu-list 40-47` in **every** cell
so affinity is not a variable, under `tools/benchlock.sh`, interleaved `1, 8, 1, 8`. Determinant
stage only, mean of two passes:

| row | | proven 13 123 | predicted 730 / 6 562 | **#179** |
|---|---|---:|---:|---:|
| `rf2-rp2` | 1 worker | 39 764 ms | **2 214 ms** | **17.96x** |
| | 8 workers | 5 239 ms | **333 ms** | **15.7x** |
| | **#227** | **7.59x** (95%) | **6.65x** (83%) | **119x both** |
| `rf4-rp0` | 1 worker | 39 175 ms | **19 714 ms** | **1.99x** |
| | 8 workers | 5 087 ms | **2 547 ms** | **2.00x** |
| | **#227** | **7.70x** (96%) | **7.74x** (97%) | **15.4x both** |

**The two reductions multiply, and #179 delivers its sample-count ratio exactly.** 17.96x against
17.98x fewer determinants on `rf2-rp2` and 1.99x against 2.00x on `rf4-rp0`: the per-determinant
cost is unchanged by the sample count, 3 033 µs against 3 030 µs on the one row and 3 004 against
2 985 on the other, which is what it should be and is worth checking rather than assuming.

Row wall clock, build through verification: `rf2-rp2` **0.88 s** at 8 workers (2.74 s at 1), and
`rf4-rp0` **7.58 s** at 8 workers (24.66 s at 1). Both still return the witnesses §6 recorded, the
same coordinates through `permutation_plus_linear`, and on both rows **the prediction held** — eight
points outside the sample set agreed with a direct Sylvester determinant, for 22–25 ms.

**One cell is not resolved and is not claimed.** `rf2-rp2`'s predicted count at 8 workers measured
379.0 ms and 286.7 ms on the two passes, a 32% spread, which is outside the ±20% this workstation's
noise makes readable. The honest form is that 730 determinants over 8 workers is 91 apiece and the
fixed costs — thread setup, and the sequential layout of the abscissae — are then a visible share,
so parallel efficiency falls off at that size: **6.0–7.7x, 75–96%**. `rf4-rp0` at 6 562 samples has
no such problem at 97%, and neither does either row at the proven count. The 119x combined figure
inherits that uncertainty; 15.4x on `rf4-rp0` does not.

#### #179 closes §6.6's reopening of the interpolation question

§6.6 found that a *parallel* route can be helped by a faster recovery, since the determinants
shrink with the core count and the interpolation does not: at the proven count on 8 workers the
Lagrange solve is **23.5%** of `rf2-rp2`'s elimination. With the predicted count it is **1.7%**.

The reason is the exponents, and it is general rather than a fact about this row: determinant work
is **linear** in the sample count and the Lagrange recovery is **quadratic** in it, so cutting
samples 18x cuts the determinants 18x and the recovery 323x. Fewer samples therefore makes the
recovery a *smaller* share — the opposite direction to adding cores. It shows up in the totals: the
elimination-stage speedup from #179 is **18.5x** against the determinant stage's 17.96x, because
the proven path also pays 1.6 s of interpolation that the predicted path reduces to 5.1 ms.

730 is also not a power of two, so an NTT domain would round it to 1 024 and hand back a third of
the saving to buy the stage that just became negligible twice over. **The right pairing is the
predicted count with arbitrary-point Lagrange**, and §6.6's finding stands for the proven count
without reaching this one.

#### The ranked list, superseding §6.4's

1. **The determinant's per-sample cost.** Still the row, and now the only axis left with an
   asymptotic improvement in it: 3.0 ms at order 162 through a generic dense LU, against a
   Sylvester matrix that is block-banded with each block a shifted copy of one coefficient vector,
   and matrices that differ across samples only in the evaluation point. Measured against an
   already-parallel baseline, which is why #227 came first.
2. **The symbolic build, on memory rather than time** — §6.8. It has been under 1% of every row
   measured and is not that at six rounds.
3. **The sample count** — done, predicted from the row's parameters and validated per row.
4. **Concurrency** — done, 95–97% efficient to 8 workers at the counts where a worker gets enough
   determinants to amortize its setup.
5. **The interpolation** — done twice, and now negligible on both axes at once.

The exponent is unchanged, which bounds all of it: the route still costs about `16 · 3^{5·rounds}`
field operations before the build. What has moved is the constant, by about 119x on the row where
both reductions apply.

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

### 6.9 The determinant cost law, calibrated at five orders

Everything above extrapolated the determinant cost from **one** point — 2.868 ms at order 162,
§6.5 — by a cubic law nothing had checked above that order. #289 asked for the law to be measured.
`examples/determinant_sweep` does it: random bivariate pairs of named degree, three independent
draws per order, the same `sample_determinants` loop every resultant route uses, under
`tools/benchlock.sh` on one pinned core.

Random pairs rather than a registered row **on purpose**. A row's matrix order is tied to its round
count, so a sweep over rows would vary the order and the row's internal structure together and
could not separate them; and the orders worth knowing about — 4 374 — belong to no row that is
affordable to run. The pairs are degree 1 in the surviving variable and `order / 2` in the
eliminated one, so the matrix order is the only thing that changes. Building the matrix is then
`O(order)` polynomial evaluations and `O(order²)` writes against the LU's `O(order³)`, under 2% by
operation count at order 162 and falling, which is what makes this a measurement of the determinant
kernel rather than of the setup around it.

| order | matrix | live set/worker | determinants × draws | wall = core-time per determinant | spread |
|---:|---:|---:|---:|---:|---:|
| 18 | 3 kB | 10 kB | 20 000 × 3 | **7.88 µs** | 7.0% |
| 162 | 210 kB | 840 kB | 500 × 3 | **3.624 ms** | 2.8% |
| 486 | 1.9 MB | 7.6 MB | 100 × 3 | **94.494 ms** | 4.6% |
| 1 458 | 17.0 MB | 68.0 MB | 8 × 3 | **2.404 s** | 1.3% |
| 4 374 | 153.1 MB | 612.2 MB | 3 × 3 | **68.182 s** | 5.2% |

All five at one worker, so wall clock and core-time coincide. The live set is four times the matrix:
`crout_lu_pivoting` returns `L`, `U` and `P` beside a clone of `A`. The spread is
`(max − min) / median` over the draws, and the reported figure is the **median** — a draw that
collided with another agent's work on a shared L3 is slow and never fast, so the contamination is
one-sided and a mean would carry it.

#### A single power law does not describe it; above L2 it is cubic

| from → to | order ratio | cost ratio | local exponent |
|---|---:|---:|---:|
| 18 → 162 | 9.00x | 459.8x | **2.790** |
| 162 → 486 | 3.00x | 26.1x | **2.968** |
| 486 → 1 458 | 3.00x | 25.4x | **2.946** |
| 1 458 → 4 374 | 3.00x | 28.4x | **3.045** |

Ordinary least squares on `(ln order, ln core-time)` — `fit_power_law`, which is unit-tested against
exact cubic data and against curved data — over all five orders:

**single law, every order: `1.5710e-9 · order^2.9071`, exponent ±0.0318, worst residual +14.9%**

| order | measured | fitted | residual |
|---:|---:|---:|---:|
| 18 | 7.88 µs | 7.01 µs | −11.12% |
| 162 | 3.624 ms | 4.164 ms | **+14.91%** |
| 486 | 94.494 ms | 101.527 ms | +7.44% |
| 1 458 | 2.404 s | 2.475 s | +2.96% |
| 4 374 | 68.182 s | 60.352 s | **−11.48%** |

**Reject it.** The residual signs run −, +, +, +, − : the fit sits above the middle of the range and
below both ends, which is curvature and not noise — the draws' own spread is 1.3–7.0%, five to ten
times smaller than the 14.9% miss. Splitting at the order whose matrix stops fitting this machine's
512 kB L2 (`lscpu -C`: 32 kB L1d and 512 kB L2 a core, 32 MB L3 × 8 instances = 256 MB) gives:

**above L2 — orders 486, 1 458, 4 374: `8.3216e-10 · order^2.9953`, exponent ±0.0285, worst residual 3.7%**

| order | measured | fitted | residual |
|---:|---:|---:|---:|
| 486 | 94.494 ms | 92.801 ms | −1.79% |
| 1 458 | 2.404 s | 2.493 s | +3.68% |
| 4 374 | 68.182 s | 66.960 s | −1.79% |

**below L2 — orders 18 and 162: `2.4783e-9 · order^2.7902`**, exact through two points, so no
residual and no standard error: two points fit a line, and the exponent is reported with that
caveat rather than with a fabricated uncertainty.

So the law is **piecewise, and the upper piece is cubic to within the measurement**: 2.9953 ± 0.0285
brackets 3.0, and 3.7% is inside the run-to-run spread at the top of the range. The lower piece is
genuinely sub-cubic at 2.79 — fixed per-determinant cost (the coefficient-row evaluations, the
`(m+n)²` matrix build, the allocation of four `(m+n)²` arrays, the `Matrix::new` copy) that an
order-18 determinant's 2 000 multiply-subtract steps cannot amortize and an order-162 determinant's
1.4 million already can.

#### The cache hierarchy is not the mechanism, which was the surprise

#289 was opened on the reading that the law is **super**-cubic above order 162 — 3.116 — with a
cache transition at the top as the mechanism, and order 4 374 was swept precisely because its
153 MB matrix is the point that separates L3 from main memory. It is not what the data say:

- order 4 374's local exponent is **3.045**, no different from 486 → 1 458's 2.946 and
  1 458 → 4 374 being the pair that crosses out of L3 entirely. There is no cliff there to model.
- the reason is arithmetic rather than lucky: Crout LU does `O(n³)` work on `O(n²)` data, so its
  compute-to-traffic ratio *grows* with the order. At 4 374 that is 2.8 × 10¹⁰ multiply-subtracts
  against 153 MB of matrix — about 180 operations per byte touched. A kernel at that ratio is
  compute-bound at every level of the hierarchy, and the inner loop walks rows contiguously.
- the 3.116 that looked super-cubic came of dividing a **32-worker** core-time at order 1 458
  (2.70 s, from the six-round run records) by a **single-worker** one at order 162 (2.868 ms, §6.5).
  Those are two different widths and two different sessions. The width is what the excess was —
  see the next heading. Measured at one width throughout, the same interval gives 2.96.

The remaining candidate mechanisms are ruled out or bounded rather than left open. Field arithmetic:
the only non-multiply-add in the kernel is one inverse per pivot, `order` of them against
`order³/3` multiply-subtracts — 0.7% at order 162 and 0.02% at 4 374, so it cannot bend the curve
and it would bend it the other way. Implementation: the matrix build is `O(order²)` against
`O(order³)`, which again shrinks with the order. What is left is the fixed overhead at the bottom,
and that is what the sub-cubic lower piece is.

#### Core-time per determinant rises with the worker count, by more than §6.6 recorded

The same sweep at three widths, orders 162, 486 and 1 458, `--repeats 3`–`5`:

| order | 1 worker | 8 workers | 32 workers | 32 workers, 4 determinants a worker |
|---:|---:|---:|---:|---:|
| 162 | 3.624 ms | 4.037 ms (1.11x) | 5.236 ms (1.44x) | — |
| 486 | 94.494 ms | 106.982 ms (1.13x) | 135.865 ms (1.44x) | — |
| 1 458 | 2.404 s | 2.821 s (1.17x) | 3.643 s (1.52x) | **3.148 s (1.31x)** |

Two things in that table. First, at order 1 458 and 32 workers the default sweep gives each worker a
single determinant, so each one first-touches its own 68 MB live set and pays the page faults
alone; raising the count to four a worker amortizes them and the penalty falls from 1.52x to
**1.31x**. The 1.31x is the figure to use, and the 1.52x is what a *row* would see only in its last,
ragged block.

Second, and less comfortably: **§6.6 measured this penalty as 4–9% out to 32 workers and it
reproduces here as 31–44%.** §6.6's own argument — that the limit is the all-core clock rather than
memory bandwidth — is if anything strengthened by the larger number, and the shape still supports
it: the penalty is the same 1.44x at order 162 and at order 486, whose matrices differ by 9x, which
a bandwidth limit would not do. But the size of it disagrees with what is on record and this
milestone did not resolve why. Treated as a finding, not repaired — #319.

#### The figures on record are ~1.2x faster than the same measurements today

Worth stating plainly, because every ratio in §6 is quoted against one of them:

| measurement | on record | re-measured in M25 | ratio |
|---|---:|---:|---:|
| order-162 determinant, 1 worker, 13 123-sample reference route on `rf2-rp2` | 37 634.3 ms / 13 123 = **2.868 ms** (§6.5) | 45 131.0 ms / 13 123 = **3.439 ms** | 1.199x |
| order-162 determinant, 1 worker, synthetic pair | — | **3.624 ms** | 1.264x vs §6.5 |
| order-18 determinant, 1 worker | 8.45–8.6 µs | **7.88 µs** | 0.92x |
| order-1 458 determinant, 32 workers, core-time | **2.70 s** (six-round records) | 3.148 s | 1.166x |

The first row is the same measurement, on the same registered row, through the same code path, under
the same lock — only months and a commit range apart. Three of the four point the same way by about
1.2x and the smallest order points the other way. **This is unexplained**, and until it is, a factor
computed between a figure from §6.5 and a figure taken now carries a ~20% systematic that is not a
property of either implementation. Filed as #318 rather than guessed at here. Two unrelated
single-core processes were resident during part of the M25 sweep — `tools/benchlock.sh` serializes
benchmarks and not builds — which inflates a measurement rather than deflating it, and so cannot
explain a figure on record being *faster*.

#### What `RowCost::of` now does, and why it is not the fitted law

The budget guard's purpose is to **refuse** runs, so the asymmetry matters: over-predicting costs an
operator a flag, and under-predicting authorizes a multi-day run nobody costed.
`determinant_core_ms` therefore takes

```text
core_ms(order, workers) = max( 3.624 · (order/162)³ , 3.624 · (order/162)^2.9953 )
                        × (1 + 0.065 · log2(workers))
```

Three deliberate choices in that line:

1. **The larger of the two laws, not the fit.** The measured exponent 2.9953 is *below* 3, so
   anchored at order 162 the fitted law predicts **less** work than the cubic at every order above
   it. Adopting the fit alone would have made the guard weaker than it was before it was calibrated.
   The `max` keeps the conservative figure and picks a future re-fit up automatically if one comes
   out above 3.
2. **The anchor is 3.624 ms, not 2.868 ms.** A guard anchored to the fastest figure ever recorded on
   a machine that no longer delivers it is a guard that does not bind. The current, reproducible
   figure is the one to refuse runs with, and the 1.2x gap is documented above rather than averaged
   away.
3. **A measured width penalty.** 6.5% a doubling, linear in `log2(workers)` through the measured
   1.00 / 1.17 / 1.31 at 1 / 8 / 32 workers, and **extrapolated at the same slope beyond 32** rather
   than held flat: nothing wider has been measured, and flattening it would make the guard
   optimistic exactly where it has no evidence.

At order 1 458 the model gives 2.642 s a determinant against 2.404 s measured — 10% conservative,
which is the intended direction. Above order 4 374 it is an extrapolation and the example says so on
the line it prints.

#### The rows restated

Sample counts are **exact**: `alpha^(2 R_F + R_P) + 1` from each row's own parameters. The
per-determinant cost at order 1 458 is **measured**; at order 13 122 it is **extrapolated** from the
above-L2 law, three times past the largest order measured. Determinant time only — the symbolic
build (§6.8: 48.4 min and 57 GB at six rounds), the recovery and the solve are not in these numbers.

| row | rounds | samples | order | 1 worker | 32 workers | basis |
|---|---:|---:|---:|---:|---:|---|
| `rf2-rp4` | 6 | 6 562 | 1 458 | 4.82 h | **12.0 min** | measured |
| `rf4-rp2` | 6 | 59 050 | 1 458 | 43.33 h | **1.79 h** | measured |
| `rf6-rp0` | 6 | 531 442 | 1 458 | 16.25 d | **16.15 h** | measured |
| `rf4-rp4` | 8 | 531 442 | 13 122 | 11 846 d | **490.5 d** | extrapolated |
| `rf6-rp2` | 8 | 4 782 969 | 13 122 | 106 617 d | **4 415 d** | extrapolated |

From the measured core-times alone, without the model's conservatism: `rf4-rp2` is
59 050 × 2.404 s = **39.4 single-core hours**, and at 32 workers 59 050 × 3.148 s / 32 =
**1.61 h**; `rf6-rp0` is 531 442 × 2.404 s = **354.9 single-core hours** and **14.5 h** at 32
workers. The reconnaissance figures of 44.3 single-core hours and 1.38 h for `rf4-rp2`, and 398
single-core hours and 12.5 h for `rf6-rp0`, are arithmetically correct for the 2.70 s core-time they
assumed; the difference is entirely that input, which M25 measures as 2.404 s at one worker and
3.148 s at 32.

**The eight-round rows are out of reach by three orders of magnitude and no exponent in the
plausible range changes that.** At 490 days on 32 workers, `rf4-rp4` would need the per-determinant
cost to fall by 500x, not the sample count to be sized better. That is the useful negative result of
the calibration: the question for eight rounds is not the cost model but whether an order-13 122
determinant is the right object at all.

#### A note on #289's own arithmetic

The issue tabulates order 13 122 as "cubic 1 524 s vs 2 294 s (1.50x)" against a stated 3.116 fit.
The cubic column is right — 2.868 ms × 81³ = 1 524 s — but 2.868 ms × 81^3.116 = **2 541 s**, not
2 294 s. 2 294 s corresponds to an exponent of 3.093. So the issue's super-cubic column is
inconsistent with the exponent it states by about 10%. Recorded here because the figure it is
inconsistent with is also the figure this section does not reproduce: measured, one order-13 122
determinant is 1 833–1 926 s at one worker — *below* the issue's super-cubic column, because the
exponent is 3.00 and not 3.09–3.12, and *above* its cubic column, because the anchor is 3.624 ms and
not 2.868 ms.

### 6.10 The off-domain validation, on the parallel path

`agrees_off_domain` was a serial `while` loop of Sylvester determinants while the interpolation's
samples went over the worker pool, so the guard's cost did not fall with the worker count at all:
22–25 ms on a four-round row, **17.4 s at six rounds — about 3% of the row** — and the eight-round
projection scales that by `(13 122/1 458)³ = 729`, which is three and a half hours of serial work
hung off a parallel run.

The fix is that the points do not depend on the thing being checked. `off_domain_abscissae(points,
checks)` is pure in its arguments and the fixed seed — not in the candidate, not in the concurrency
— so the draws can happen *before* any determinant is evaluated, and the checks then go through the
same indexed `sample_determinants` loop as the samples, partitioned over the same workers.

| 8 off-domain checks at order 1 458 | workers | wall clock |
|---|---:|---:|
| serial, as before | 1 | **19.97 s** (8 × 2.496 s measured) |
| on the parallel path | 8 | **2.82 s** |

Substituted into the six-round `rf2-rp4` record — 551.37 s of sampling, 0.41 s of interpolation,
17.749 s of validation at 32 workers — the validation's share of the elimination goes from
**3.12% to 0.51%**. Eight checks cannot use more than eight workers however many are asked for, so
32 workers buys nothing further here; the residual is one determinant, which is the floor for a
guard that must evaluate at least one point it did not interpolate through.

Two properties the rewrite had to keep, and now keeps by construction rather than by accident:

- **the verdict is order-independent.** All `checks` determinants are evaluated before any is
  compared, so a falsifying case cannot depend on which worker reached it first. The old loop
  returned on the first disagreement, which was fine serially and would not have been fine spread.
  Evaluating all eight costs eight determinants on the one path — falsification — that is about to
  pay for a whole proven-bound fallback anyway.
- **the draws are distinct, not merely outside the sample set.** Over KoalaBear a repeat among eight
  draws has probability about `8²/2³²`, so this changes no run on record; but the probability bound
  below is an argument about `checks` *independent* points, and a silently repeated point would
  weaken the bound without changing the count that is reported.

`with_off_domain_checks(0)` still panics, the count still defaults to 8, and `validation` is still
its own reported stage — which is why the checks are a second call to `sample_determinants` rather
than being fused into the samples' batch as #285 suggested. Fusing them would have made the guard's
cost unmeasurable, and §6.11 needs that field to be disjoint from the others. The price is `checks`
thread spawns, about 35 µs, against determinants of seconds.

#### What the check establishes, and what it does not

**It is a probabilistic consistency check, not a proof of a polynomial identity**, and the two
routes through this module differ exactly there:

- the **proven**-bound routes need no argument of this kind. A polynomial of degree at most
  `n·deg_x(f) + m·deg_x(g)` agreeing with the determinant at `bound + 1` points *is* the resultant,
  by uniqueness of interpolation — §6.3's first bullet, and it is a certificate.
- the **predicted** route interpolates through `alpha^(2R_F+R_P) + 1` points, far fewer than the
  bound, so uniqueness says nothing. If the prediction is wrong, the recovered `C` and the true
  resultant `R` differ, `C − R` is a nonzero polynomial of degree at most the proven bound `D`, and
  a point drawn uniformly is a root of it with probability at most `D/p`. Eight independent
  agreements therefore bound the failure probability by `(D/p)^8`: at four rounds
  `(13 122/2 130 706 433)^8 ≈ 2 × 10⁻⁴²`, at six rounds `(1 062 882/2 130 706 433)^8 ≈ 4 × 10⁻²⁷`.

Overwhelming, and still evidence rather than a certificate. One caveat is worth stating because the
reproducibility requirement creates it: the seed is **fixed**, so the bound is over the choice of
seed and not over a fresh draw each run. Re-running the same row reuses the same eight points and
accumulates no new evidence. For a measurement that is the right trade — a figure that cannot be
reproduced is not a figure — but it does mean the guard is strong against a *generic* failure of
slide 22's formula and not against an input built to pass these eight points.

### 6.11 The off-domain validation was counted twice, and the six-round totals carry it

`examples/resultant_cico` charged the validation to `Stage::Elimination`, through
`Pass::elimination`, and again to `Stage::Verification` as `pass.off_domain.1`. `RunRecord::elapsed`
is the sum of the stages, so **the recorded row total was inflated by the cost of the check.** It is
visible in the six-round record without any recomputation: elimination 569.53 s = 551.37 sampling +
0.41 interpolation + 17.75 validation, and the verification stage is 17.749 s — the same 17.4 s in
two places.

Validation now belongs to the elimination and to nothing else. The reasoning, since it is a judgement
and not a mechanical fix: `Stage::Verification` is defined as the independent check of a
*candidate*, which here means a recovered input pair run through `permutation_plus_linear`, whereas
the off-domain check is what decides **which polynomial the elimination returns at all** — and on a
falsified row `stages.validation` already contains the refused attempt's own sampling and
interpolation, which is unambiguously elimination work. Its *count* stays on the verification stage
as description; its duration moves, and a new `validation_us` detail on the elimination stage keeps
it visible rather than buried in a sum.

Two things keep it fixed rather than fixed once. `ResultantStages::elapsed` is now the single
definition of what one elimination cost, so a caller filing a stage cost and a caller printing a
total cannot drift apart; and `record` **asserts** that the recorded stage durations sum to the total
the row printed, which fails the run rather than filing an inflated record. A unit test pins both
halves of the invariant against an outer timer: the three stage fields sum to no more than the
route's measured elapsed — which a double count violates — and to no less than half of it, which a
dropped stage violates.

**The records already written are not edited.** A historical measurement is not rewritten because a
later implementation accounts for it better; what it says about the machine on the day is what it
says. So the six-round run records, and `MILESTONE-PUBLISHED-ATTACK-REPRODUCTION.md` §7.8's total of
59.71 min, continue to carry **17.75 s of double-counted validation** — 0.5% of that row, and the
inflation is in `elapsed_nanos` and the verification stage, not in `sampling` or `interpolation`,
which were never wrong. Any row recorded from this commit onwards does not carry it, and a total
compared across the boundary should subtract the verification stage from the older one.

## 7. The deeper consequence

It is about the **formulation**, not the algorithm. Three orders of magnitude separate two ways of
writing the same CICO slice, and the expensive one is the one the whole cryptanalysis literature
uses by default because it bounds the degree. When the free-variable count is small, bounding the
degree is the wrong trade — and the scoreboard is what made that visible, because both routes are
measured against the same registered problem.

§6 does not change that and is a smaller point by comparison: it moves one stage of the cheap
formulation from cubic to quasi-linear, which buys a round count. The formulation is what bought
the three orders of magnitude.
