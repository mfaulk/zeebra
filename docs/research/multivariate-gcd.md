# The multivariate GCD routes, measured: each is the fastest somewhere, and the default is the one that always answers

**Measured at:** §§0–4 at `261b9540` plus the change that adds `examples/gcd_routes.rs`; §5 from a
tree based on `4de99385` plus the change that adds `GcdRoute::Brown` and the third arm. Both are
commits on `main` and so stay resolvable ([#505](https://github.com/mfaulk/zeebra/issues/505)).
`4de99385` is not this document's own base — `git diff 4de99385 <base> --
src/poly/multivariate/multivariate_gcd.rs src/poly/univariate/gcd.rs
src/poly/univariate/lagrange_interpolation.rs` is empty, so every line §5 times is byte-identical at
both; what moved in between is a counter added to the normal-form path (`0d7825d4`), which no arm
here enables. Every arm is an entry point selected by `GcdRoute`, so there is no before-side tree to
name and nothing merged in between can have moved one arm relative to another. §5's two runs are
stamped with their one-minute loads, 9.51 and 2 100.79, because §5.3 is about what that does and
does not change.

Measurement record for #407 and #434. #128 landed the primitive PRS and published **no timings at
all**; Collins' subresultant PRS then became the default on correctness evidence plus an asserted
*operation count*, with the wall clock explicitly deferred. So before #407 there was no duration
figure for either route, and before #434 Brown's modular route did not exist.
[§5](#5-browns-modular-route-measured-it-owns-the-tail-both-sequences-lose) is the three-route
comparison; §§0–4 are #407's two-route one and are unchanged except where §5 supersedes them.

Machine: AMD Ryzen Threadripper PRO 5995WX, 128 hardware threads, 503 GB RAM. One core
(`taskset --cpu-list 12`), release profile with the repository's defaults, `RUSTFLAGS` unset,
`RUSTC_WRAPPER=""`, a per-worktree `CARGO_TARGET_DIR`, under
[`tools/benchlock.sh`](../../tools/benchlock.sh). ISA floor `x86-64-v3 or better (AVX2)`, printed in
the run's own header. Each figure is the fastest of up to 5 interleaved repetitions; the `reps`
column in the raw output says how many a shape actually got, and rows that got one are single-shot.

**Durations here are shared-machine durations.** Other agents build and measure concurrently on this
box; `benchlock` excludes other measurements and does nothing about shared L3 or memory bandwidth.

## 0. The result, which is not the one the operation count predicts

The asserted operation count — 18 recursive content GCDs against 6 on a degree-five-against-two
pair — says the subresultant route does less work. **The wall clock says it is usually slower.**

| field | shapes the subresultant route wins by >10% | shapes the primitive route wins by >10% |
|---|---:|---:|
| KoalaBear | 2 | **15** |
| Goldilocks | 3 | **14** |
| BN254 `Fr` | 2 | **16** |

Twenty shapes per field — seven each at two and three variables, six at four — crossing the shared
factor's term count, each cofactor's term count and the largest per-variable exponent. The
subresultant route's typical loss is **10% to 50%**.

**And the default should stay anyway.** The two routes are not slower-and-faster; they are
different-tailed, and the tail is what decides it.

**The same shape repeats one level up, with Brown's route** ([§5](#5-browns-modular-route-measured-it-owns-the-tail-both-sequences-lose)):
it is the fastest of the three on every shape that defeats a sequence — by 4.3x to **67x** against
the better of them — and it loses the median on two fields of three, by up to 5.2x on the smallest
shapes. Three routes, each fastest somewhere. The default is the best route that **always answers**,
which Brown's does not: it refuses over an extension field and over a field with too few points.

## 1. The primitive route's tail is unbounded; the subresultant route's is not

| | shape | primitive | subresultant | |
|---|---|---:|---:|---|
| **the primitive route's worst** | KoalaBear, 4 vars, 2-term factor x 6-term cofactor, 10 terms | **1.2561 s** | 0.0020 s | **628x** |
| the subresultant route's worst | KoalaBear, 4 vars, 4 x 4, 16 terms | 0.0011 s | **0.0262 s** | 24x |
| a typical row | Goldilocks, 3 vars, 3 x 3, 9 terms | 0.00015 s | 0.00015 s | ~1.0x |

The 628x row got **one repetition**, so it is a single pass rather than a minimum of five — which is
the honest caveat on the largest number here, and it is an order of magnitude clear of anything the
spread could explain.

Worse, there is a shape where the primitive route appears not to terminate on any useful timescale.
The first attempt at this sweep was killed by its own 2 400 s timeout **mid-table**, having
completed KoalaBear's two- and three-variable shapes and six of the seven four-variable ones. The
rows it did print sum to under two seconds. So the seventh four-variable shape — a 5-term factor
against 5-term cofactors at exponent 4 — consumed essentially the whole remaining **~40 minutes**
without finishing, and two of the three fields were never reached.

That shape is now excluded in advance rather than reactively, and the exclusion is printed, because
the cost cannot be bounded after the fact: a single pass of either route is a synchronous call.
**The attribution to the primitive route is inferred, not measured** — the harness runs the
correctness pass primitive-first, and the neighbouring shape has the primitive route 628x slower, so
it is the overwhelmingly likely culprit, but the run died before it could say which arm it was in.

## 2. Why the tails differ, which the theory already said

- **Primitive PRS** removes the content from every pseudo-remainder. A content is itself a recursive
  GCD in a smaller ring, so the cost is a *recursion over recursions*, and nothing bounds how much
  work a step's content costs in terms of the original inputs. Coefficients cannot grow — that is
  the bound it buys — but the recursion is where the time goes, and it is the recursion that
  explodes.
- **Subresultant PRS** replaces that with one exact division by `g * h^delta`. The sequence's
  entries *are* subresultants, determinants of submatrices of the inputs' Sylvester matrix, so
  Hadamard's inequality bounds them in terms of the inputs alone. There is no recursion to explode;
  the cost is the growth, and the growth is bounded in advance.

So the measured picture is the theoretical one with the emphasis moved: the subresultant route pays
a steady 10–50% to buy a bounded worst case, and the primitive route takes a better median in
exchange for a tail that reaches 628x and, on at least one shape, does not land.

## 3. What this changes

**The default does not move.** `GcdRoute::SubresultantPrs` stays, and the justification in the
source changes from "correctness evidence, not a measurement" to a measurement — of the tail rather
than the median. A library default should be the route that cannot fall off a cliff on an input the
caller did not know was special, which is the usual argument for a bounded worst case over a better
average, and it is now supported by numbers rather than by the operation count.

**`PrimitivePrs` stops being only a reference implementation.** It is 10–50% faster on most shapes,
which makes it a legitimate choice for a caller who knows its inputs, and `gcd_by` already exposes
it. That is worth stating in the README, where it was previously described only as the route the
other is tested against.

## 4. What this does not establish

* ~~**Brown's modular algorithm.**~~ **Done, #434** —
  [§5](#5-browns-modular-route-measured-it-owns-the-tail-both-sequences-lose). It is the route that
  changes the asymptotics and the measurement bears that out in the tail rather than the median.
  §§0–3 below are the two-route comparison and stay as they were taken.
* **A shape-aware default.** The two routes' costs differ by up to 628x in one direction and 24x in
  the other on *neighbouring* shapes, which is the signature of a choice that wants to be made per
  input rather than once. Nothing here measures a predictor — term count, arity and exponent are
  the three axes swept and none of them separates the 628x row from its neighbours on its own.
* **Where the primitive route's blow-up comes from.** Attributed to the content recursion by the
  theory and by the shape of the measurement, not by a profile.
* **Any instance from the solver.** These are planted-factor random inputs. What F4 and FGLM
  actually hand `gcd` is unmeasured, and that is the input distribution a default should really be
  chosen against.

## 5. Brown's modular route, measured: it owns the tail both sequences lose

#434 added the third route. It does no Euclidean step at all — it fixes the other variables at field
elements, solves the univariate problems with `poly::gcd` and interpolates the answer back — so
neither coefficient growth nor a content recursion arises. §4 named it "the route that changes the
asymptotics", and the measurement says where that cashes out: **not in the median, and decisively in
the tail.**

Same harness, same machine, same twenty shapes per field, with a third timed arm. All three routes
are asserted equal at every shape before the clock starts.

### 5.1 Where each sequence is worst, and what Brown's costs there

| field | worst shape | primitive | subresultant | **Brown** | Brown against the worse of the two |
|---|---|---:|---:|---:|---|
| KoalaBear | 4 vars, shared 2, cofactor 6 | **1.3704 s** | 0.0020 s | **0.000459 s** | **2 988x** |
| KoalaBear | 3 vars, shared 5, cofactor 5, exp 4 | 0.0025 s | **0.0348 s** | **0.000518 s** | **67x** |
| Goldilocks | 3 vars, shared 5, cofactor 5, exp 4 | **0.0073 s** | 0.0030 s | **0.000555 s** | **13x** |
| BN254 `Fr` | 3 vars, shared 5, cofactor 5, exp 4 | **0.0510 s** | 0.0328 s | **0.003096 s** | **16x** |

Read the rows as "the shape that defeats a sequence, and what the third route does there". On the
KoalaBear shape where the primitive route takes 1.37 **seconds**, Brown's takes 459 microseconds. On
the shape where the *default* takes 34.8 milliseconds, Brown's takes 518 microseconds — **67x**.
Against the better of the two sequences on each field's worst shape, Brown's is 4.3x, 5.4x and 10.6x
faster on KoalaBear, Goldilocks and BN254.

**Brown's is the fastest of the three on every shape that defeats a sequence, on every field.** That
is the finding, and it is the one §4 predicted from the theory: a route that forms no multivariate
coefficient has no coefficient growth to pay for, and one that interpolates instead of recursing has
no content recursion to explode.

BN254 is the sharpest case and the most expected one: its element is 32 bytes, so coefficient growth
costs the most there, and it is where the subresultant route's own worst shape costs 33 milliseconds
against Brown's 3.1.

### 5.2 And it loses on small inputs, which is the honest half

| field | Brown's best against the default | Brown's worst against the default | wins / loses / 20 |
|---|---|---|---|
| KoalaBear | **0.01x** (67x faster) | **4.58x** slower, 4 vars, shared 2, cofactor 2, exp 2 | 7 / 11 |
| Goldilocks | **0.18x** (5.6x faster) | **2.52x** slower, 4 vars, shared 6, cofactor 2 | 10 / 7 |
| BN254 `Fr` | **0.09x** (11x faster) | **5.17x** slower, 4 vars, shared 2, cofactor 6 | 5 / 12 |

Brown's cost is one univariate GCD per evaluation point per level of recursion plus one
interpolation, and on a shape the sequences finish in ten microseconds that fixed structure is the
whole cost. So the same shape as §0: **the route with the better tail loses the median**, now one
level up. Three routes, and each is the fastest on some shapes and the slowest on others.

### 5.3 The ratios are load-independent, and this sweep is where that was checked

§0 warns that these are shared-machine durations. This revision can say how much that matters,
because the whole sweep was taken twice — at a one-minute load of **9.51** and again at **2 100.79**,
a 221x range — and the `subresultant / brown` ratio was compared row by row on the 40 shapes both
runs covered:

| | agreement |
|---|---|
| 40 paired shape ratios across a 221x load range | **every one within 0.06**, most within 0.02 |
| the three tail rows above | within 2% at the two loads |

So the ratio columns here are figures and the absolute-seconds columns are a snapshot — the same
split `graeffe-root-finding.md` §6.3.2 found for the NTT sweep, confirmed independently on a workload
with completely different memory behaviour. `examples/gcd_routes.rs` now prints the one-minute load
at the head of every run and says which columns survive it. That is also why no load gate was added
here, unlike `examples/ntt_access.rs`: this workload's figures do not need one, and the evidence for
that claim is the table above rather than an assumption.

### 5.4 So the default stays, and the reason is sharper than before

§3 kept `SubresultantPrs` as the default because its tail is bounded and the primitive route's is
not. Brown's tail is better still — and **it cannot be the default**, because it is the one route
that can refuse:

- **Prime fields only.** Fixing a variable at an element of GF(2^8) and lifting back would answer a
  question about the prime subfield. `GcdError::ExtensionField`.
- **More elements than the degree it interpolates over.** GF(2) and GF(3) do not have them for most
  inputs. `GcdError::TooFewPoints` — and that is what the exhaustive GF(3) brute-force test asserts.
  It runs Brown's on every enumerated pair and requires the *refusal*, which is how a route that
  cannot apply over that field is still exercised by the one test that enumerates its inputs rather
  than choosing them.

A width that does not refuse: a 254-bit prime field has ample evaluation points even though its
order does not fit a `u128`. The first implementation indexed points with `KnownOrder::element_at`,
which takes a `u128`, and so refused **every** BN254 shape — the field where coefficient growth costs
the most and where Brown's advantage is largest. The points are now the images of `0, 1, 2, …` under
repeated addition of one, distinct in any prime field below its characteristic, and
`test_brown_answers_over_a_field_too_wide_to_enumerate` is the regression test.

A default has to answer for every field in the crate, so the default is still the best route that
always answers. What changes is the recommendation beside it: **over a prime field, on inputs big
enough to matter, `try_gcd_by(&other, GcdRoute::Brown)` has the best measured worst case of the
three** — 4.3x to 67x faster than the better sequence on the shapes that defeat them — and it is the
route to ask for when the inputs are not known to be small.

### 5.5 What #434 does not establish

* **A dispatching default.** The obvious next move is a default that tries Brown's where the field
  admits it and falls back otherwise. That is attractive and is **not** done here, for the reason §4
  already gave: Brown's loses up to 5.2x on the smallest shapes, and what F4 and FGLM actually hand
  `gcd` is still unmeasured. Changing the default on this evidence would be tuning the tail of a
  distribution nobody has looked at. It is now a three-way version of the same open question.
* **The interpolation's own bound.** `brown` falls through to the subresultant route when the
  interpolated candidate fails to divide both inputs, which is what a degree bound that was not tight
  produces. `brown_outcomes` counts the two outcomes and
  `test_the_interpolation_answers_rather_than_the_fallback` requires the interpolation to be what
  answers, so the figures above are Brown's own and not the fallback's. How often the fallback fires
  on a *wider* input distribution is unmeasured.
* **Sparse interpolation.** This is dense Brown's: it spends `d + 1` points per interpolated variable
  whether or not the answer has that many terms. Zippel's sparse variant is the standard improvement
  and is a different algorithm, not a tuning of this one.
* **The univariate GCD underneath.** Every evaluation bottoms out in `poly::gcd`, classical Euclid at
  `O(d^2)`; `fast-univariate.md` §4.5 records that half-GCD is deliberately not written. Brown's
  advantage here is measured against a quadratic base case and would widen if that base case
  improved.

## 6. Reproducing

```sh
export CARGO_TARGET_DIR=/path/outside/the/worktree RUSTC_WRAPPER=""
unset RUSTFLAGS
cargo build --release --example gcd_routes
tools/vec_census.sh "$CARGO_TARGET_DIR/release/examples/gcd_routes"

tools/benchlock.sh <tag> taskset --cpu-list 12 \
  cargo run --release --example gcd_routes
cargo run --release --example gcd_routes -- bn254   # one field
```

The binary asserts **all three** routes equal at every shape before timing it, prints the ISA floor,
the one-minute load and the repetition count per row, and reports which shapes it omitted and why
and which shapes Brown's route refused.

`benches/multivariate_gcd.rs` is the regression surface for the same question: four shapes, one per
regime, under criterion, with the Brown arm **probed outside the timed region** and simply not
registered where it refuses — criterion has no way to express "this arm does not apply", and an arm
that fell back silently would report another route's time under Brown's name.

```sh
cargo bench --bench multivariate_gcd
cargo bench --bench multivariate_gcd -- brown/koalabear/3vars   # one arm
```
