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
Section 8 adds #658's call-site audit and deterministic census against runtime source `778e1dc9`.

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

## 1. Historical outliers and a sweep that exceeded its budget

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

## 2. The structural trade-off, with finite-field qualifications

Primitive PRS extracts a recursive content after every completed pseudo-remainder.
This removes a common polynomial factor; it does **not** prevent the remaining
coefficient polynomials from growing in support or degree. Subresultant PRS
replaces those per-step content extractions with exact scaling. It still extracts
contents at entry and exit, so neither recursion nor expensive input shapes have
disappeared.

Scaled subresultant entries have coefficients represented by Sylvester minors.
Hadamard's inequality gives magnitude bounds over the integers. Here each field
coefficient has fixed width: the relevant analog is the degree/support bound from
determinant expansion, specified and checked in [§7](#7-intermediate-size-profiles-652).
Raw pseudo-remainders before exact division are a separate size quantity.

The historical timings show different tails on this planted-factor distribution.
They do not establish a universal runtime guarantee for either route, nor do they
by themselves identify which recursion or polynomial-size mechanism dominates.

## 3. What this changes

**The default does not move.** `GcdRoute::SubresultantPrs` stays, and the historical justification is the measured tail rather than the median. This is a
choice on the measured distribution, not a universal bound on runtime or support growth.

**`PrimitivePrs` stops being only a reference implementation.** It is 10–50% faster on most shapes,
which makes it a legitimate choice for a caller who knows its inputs, and `gcd_by` already exposes
it. That is worth stating in the README, where it was previously described only as the route the
other is tested against.

## 4. What this does not establish

* ~~**Brown's modular algorithm.**~~ **Done, #434** —
  [§5](#5-browns-modular-route-measured-it-owns-the-tail-both-sequences-lose). It is the route that
  adds an image/interpolation route whose measured advantage is in the tail rather than the median.
  The historical timings in §§0–3 remain at their original source pins; explanatory prose is
  qualified by §7 rather than treating timings as complexity proofs.
* **A shape-aware default.** The two routes' costs differ by up to 628x in one direction and 24x in
  the other on *neighbouring* shapes, which is the signature of a choice that wants to be made per
  input rather than once. Nothing here measures a predictor — term count, arity and exponent are
  the three axes swept and none of them separates the 628x row from its neighbours on its own.
* **Where the primitive route's blow-up comes from.** The historical attribution was an inference,
  not a causal profile. [§7](#7-intermediate-size-profiles-652) adds support/degree and call-count
  observations, preserving the limits on what these establish about time.
* **Any instance from the solver.** These are planted-factor random inputs. Section 8's later
  audit and census find no multivariate GCD calls in the current solver, so this distribution
  cannot justify a solver-specific multivariate dispatcher.

## 5. Brown's modular route, measured: it owns the tail both sequences lose

#434 added the third route. Its main path fixes other variables at field elements,
solves image GCDs recursively and interpolates the candidate. Content extraction is
still recursive. It materializes coefficient polynomials in images/interpolants,
and uses subresultant PRS for candidate cleanup and fallback. The historical
measurement found its advantage in the tail rather than the median; these timings
do not establish an asymptotic improvement for this implementation.

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

### 5.3 A historical cross-load observation

§0 warns that these are shared-machine durations. This revision can say how much that matters,
because the whole sweep was taken twice — at a one-minute load of **9.51** and again at **2 100.79**,
a 221x range — and the `subresultant / brown` ratio was compared row by row on the 40 shapes both
runs covered:

| | agreement |
|---|---|
| 40 paired shape ratios across a 221x load range | **every one within 0.06**, most within 0.02 |
| the three tail rows above | within 2% at the two loads |

This is an observation about those two historical runs, not a guarantee that ratios
survive contention. New measurements need matched controls, interleaving and repeat
ranges; the bounded §7 campaign has an explicit ambient-load gate. The ordinary
legacy sweep still reports load without a gate and should be interpreted accordingly.

### 5.4 So the default stays, and the reason is sharper than before

§3 kept `SubresultantPrs` as the default because its measured tail on these inputs was smaller than the primitive route's. Brown's tail is better still — and **it cannot be the default**, because it is the one route
that can refuse:

- **Prime fields only in this implementation.** Points are generated as0,1,2,… by repeated
  addition of one, which enumerates only the prime subfield of an extension. Extension-field
  point enumeration is not implemented, so the route returns `GcdError::ExtensionField`.
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
  already gave: Brown's loses up to 5.2x on the smallest shapes. **#658 is resolved by §8's
  narrower null result:** current F4/FGLM/point-recovery routes make no multivariate GCD calls.
  There is no solver input population on which to train or score this dispatcher. Whether a
  predictor helps external multivariate GCD callers remains unmeasured.
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

## 7. Intermediate-size profiles (#652)

The instrument is opt-in under the existing `research-work` feature. Its
[API and boundary definitions](../guide/polynomials.md#intermediate-size-diagnostics)
distinguish normalized/scaled PRS entries, completed raw pseudo-remainders,
Brown's accepted scaled images and complete interpolants. Maxima cover all
recursive calls in the scope. They are not simultaneous live memory, coefficient
bit lengths, or allocator/RSS measurements. Brown's PRS columns include cleanup
and fallback; they are never relabelled image sizes.

For a local PRS call with main-variable degrees m,n and largest input
coefficient total degree C, a subresultant coefficient is a Sylvester-minor
determinant of order at most m+n.
Each product in the determinant has degree at most B=(m+n)C; addition and finite-field
cancellation cannot increase degree. Each materialized scaled/primitive next entry and the
initial operands are checked against that local bound. The term count of a
coefficient in v remaining variables is therefore at most binomial(B+v,v), and
an entry of main-variable degree d has at most (d+1)binomial(B+v,v) terms. These are
loose support envelopes, not predictions. Bounds are recomputed per recursive
call and overflow is reported explicitly. They do not bound raw pseudo-remainders
before exact scaling or transient products.

The determinant interpretation is the primary result used here; compare
[Brown, *Euclid's Algorithm and Computation of Polynomial GCD's*, §3](https://www.cecm.sfu.ca/~mmonagan/teaching/TopicsinCA19/Brown1971.pdf).
Its integer Hadamard magnitude argument is not transplanted to finite-field bit
length. Brown also notes that primitive PRS entries divide the corresponding
subresultants. Thus this degree envelope applies to primitive entries too: the
trade-off is **not** bounded subresultant degree versus unbounded primitive degree.
Normalization removes content but does not imply constant coefficient degree or
support. The `subresultant_*` profile fields name this theorem, not an exclusive route.
The implementation checks the envelope for both PRS routes; Brown still
performs recursive contents and its cleanup/fallback PRS is included.

### Declared campaign

The runner reuses `grobx-work-study.py`'s fresh-process/RSS guard and the machine
benchmark lock. Each child has a 10-second / 512 MiB RSS ceiling. The aggregate
campaign ceiling is 600 seconds, checked before each child; at most one bounded
child plus artifact writing can extend beyond it. Every stop, refusal or failure
is retained. A timeout is an outcome, not a duration estimate or a claimed speedup.
Build and test both binaries before locking and commit the instrument first.

Five interleaved fresh-process repetitions cover each combination of:

- KoalaBear, Goldilocks and BN254;
- (arity, historical shape index) (2,0), (3,3), (3,6), (4,3), (4,4);
- primitive, subresultant and Brown;
- feature-absent stock, feature-present/capture-off and capture-on.

This is 675 planned attempts. In addition, the previously omitted four-variable
shape index6 gets one diagnostic attempt per field/route/arm (27 attempts), under
the same child caps. No repeated timing claim is made for that diagnostic.
The generator replays preceding shapes from each field's historical fixed seed,
so the 628x and 24x shapes are represented by identical mathematical generator
rules, with full contemporary input digests retained. Historical timings remain
at their original pins and are not pooled with this campaign.

Every completed call checks that its result divides both inputs and contains the
planted factor. The runner compares the **complete normalized GCD**, bound to
its input digest, across all completed routes and observer modes. Divisibility
alone is not a greatestness proof; these equality checks preserve the existing
independent-algorithm agreement, backed by the library's exhaustive GCD tests.
Profile support scans run separately from the unobserved timing passes, and the
stock/off/on controls expose compilation/no-op and collection overhead. A profile
pass's own duration is not substituted for an unobserved route's time.

Reproduction commands and retained data are in
[`research/gcd-size/README.md`](../../research/gcd-size/README.md).
### Native outcomes and reproducible tables

**Measured at:** `e74e70589e77b5a7dc952ece892674886b3b7955` (runner); compiled Rust/config is
`3a9bae54`, unchanged at the runner commit. The [source/config fingerprints and
recovery patch](../../research/gcd-size/evidence/provenance.json) reconstruct the
frozen source from base `a33a192e`; compiler and binary hashes are retained.

The [complete cohort](../../research/gcd-size/cohort.json.gz) retains all **702**
planned attempts: **699 completed**, **3 wall stops**, zero refusals and zero
validation/infrastructure failures. Every one of the 675 regular attempts
completed. The three diagnostic stops are KoalaBear arity 4 / shape 6 primitive PRS,
once each under stock/off/on, at the declared ten-second child ceiling. No timing
or intermediate maximum is invented for those interrupted computations. The
remaining 24 diagnostic attempts completed; they remain single feasibility
samples, not repeated timing evidence.

Machine: Threadripper PRO 5995WX, one worker pinned to CPU 2, Rust 1.99.1 / LLVM 23.1.1,
release/fat LTO/one codegen unit, x86-64-v3 with the local mold linker. The
[lock log](../../research/gcd-size/evidence/benchlock.log) records START 23:06:21 and
END 23:08:12 on 2026-11-12 America/New_York, status=0 / end=exited, with no builds or
tests from this study during the window. Attempt-start load was 1.70–2.93, below
the declared load gate of 4. Each process wall/RSS includes generation, full GCD checks and
JSON encoding; function time excludes those and profile JSON construction. The
controller's existing two-millisecond polling and process spawn create a floor
for small process-wall samples. Do not rank tiny operations from that floor or
divide function time by process wall to infer a stage share.

All completed full normalized GCDs agree across routes and stock/off/on modes for
the same input digest. All five fixed-input profile repetitions are identical.
Every checked normalized/scaled entry satisfies its local determinant degree
envelope; no bound overflows occurred. Brown actually uses fallback on some
fixtures: the diagnostic KoalaBear arity 4 / shape 6 profile records eight fallbacks,
so its PRS work is retained rather than hidden under an interpolation label.

[The generated full table](../../research/gcd-size/table.md) places function
median/range, process wall/range and RSS/range beside the phase-size columns for
all three fields and all regular cases. [summary.csv](../../research/gcd-size/summary.csv)
and [summary.json](../../research/gcd-size/summary.json) retain all arms, repeat
ranges, diagnostics and outcomes. Regeneration revalidates complete GCDs and
profile stability. The following KoalaBear rows focus on the historical outliers;
time/RSS are medians from stock, while sizes come from separate capture-on calls.
T/D means independent maxima of polynomial term count / coefficient total degree,
not necessarily the same entry or simultaneous storage.

| arity/shape | route | function ms | process wall ms | RSS MiB | PRS T/D | raw T/D | image T/D | interpolant T/D | contents | max local B |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|

| 4/4 | primitive | 1592.308559 | 1597.024787 | 87.18 | 2330/139 | 6051/401 | — | — | 2289 | 1914 |
| 4/4 | subresultant | 4.167038 | 5.935336 | 6.80 | 162/22 | 162/27 | — | — | 429 | 143 |
| 4/4 | brown | 0.468607 | 3.822005 | 3.11 | 1/0 | — | 2/1 | 2/1 | 210 | 0 |
| 4/3 | primitive | 1.220300 | 3.832234 | 3.11 | 38/8 | 241/31 | — | — | 615 | 144 |
| 4/3 | subresultant | 29.923675 | 32.600723 | 33.07 | 367/57 | 517/66 | — | — | 721 | 180 |
| 4/3 | brown | 0.567143 | 3.724701 | 3.18 | 3/2 | 1/0 | 4/4 | 4/4 | 275 | 2 |
| 3/6 | primitive | 2.138047 | 3.790064 | 3.21 | 83/19 | 273/50 | — | — | 505 | 300 |
| 3/6 | subresultant | 9.220665 | 12.358855 | 9.11 | 377/38 | 481/46 | — | — | 468 | 456 |
| 3/6 | brown | 0.364661 | 3.469037 | 3.19 | 1/0 | 0/0 | 5/3 | 5/4 | 170 | 0 |

The degree envelope is deliberately loose: on arity 4 / shape 4, the largest observed
primitive coefficient degree 139 is below its largest local B=1914; subresultant
coefficient degree 22 is below B=143. On arity 4 / shape 3 the corresponding pairs are
8 / B=144 and57 / B=180. All *individual* checks used each call's own bound, not these
independently aggregated maxima. These bounds quantify the theorem but do not
predict practical support or memory.

### Observer overhead and corrected attribution

Across the fifteen regular route/case cells per field, the extrema of within-cell
function-median quotients are:

| field | capture-off / stock | capture-on / capture-off |
|---|---:|---:|
| KoalaBear | 0.959–1.134 | 0.971–1.044 |
| Goldilocks | 0.950–1.154 | 0.895–1.122 |
| BN254 | 0.906–1.054 | 0.914–1.101 |

These are matched observation controls, not optimization gains. Some ranges
include negative apparent overhead; scheduling, layout and microsecond-scale
noise preclude assigning those differences to a useful technique. Full per-cell
ranges remain in the generated table/summary. Use stock for unobserved durations,
and capture-on for size/call evidence; this campaign does not claim that profiling
is free or choose a faster default from noisy small rows.

**The historical recursion-only explanation is rejected as stated.** The
KoalaBear arity 4 / shape 4 generator geometry is the historical 628x outlier, with
contemporary input SHA-256
`c7adfed5c2119ade6d146559428dc9ac8f21a94b497ab5006c04e0d21a84d245`.
Historical timings remain at the §§0–5 pins; the new duration is not a reassertion
of 628x. Normalized primitive entries reach 2,330 terms / degree 139, while completed
raw remainders reach 6,051 terms / degree 401. They demonstrably do **not** stay small.
The primitive run also makes 2,289 content calls and 36,723 GCD entry calls, versus
429 and2182 for subresultant PRS. Growth and repeated recursive work coexist;
these maxima include content subproblems and do not assign exclusive CPU shares
to either mechanism. A growth-only explanation would be equally unsupported.

The historical 24x subresultant outlier (arity 4 / shape 3, input SHA-256
`05d22eaae3d31618f6180eb9e3549bf9b1308e1ac8a19193b4d3842ffb6b74e3`)
shows the other side: scaled entries 367 terms / degree 57 versus primitive 38/8, and
raw 517/66 versus 241/31. Global content counts can even be higher for the
subresultant route on that shape, 721 versus 615, despite replacing per-step
content extraction at any one PRS level. Nested coefficient growth matters to
the whole computation. The arity 3 / shape 6 rows similarly expose the larger
subresultant intermediates instead of assuming their cost from theory.

**Decision:** retain these bounded, opt-in diagnostics and correct the earlier
explanation; leave the default GCD route unchanged. The experiment establishes
actual size growth and structural recursion counts on these planted-factor
fixtures, with typed stops retained. It does not establish causal wall-time
shares, behavior on arbitrary inputs, a shape predictor, or the solver's own GCD
input distribution; §8 supplies #658's separate solver call audit. No solver
speedup or universal runtime guarantee follows from the degree bounds.

## 8. Solver input census and default decision (#658)

**Audited and exercised runtime source:** `778e1dc9`; this change modifies tests and documentation,
with no runtime changes. The [retained census](../../research/gcd-solver/census.txt) binds its
observation lines to that commit, the new test harness SHA-256 and the frozen cryptanalytic input
SHA-256. These are deterministic call counts and verified outcomes, not elapsed-time measurements.

**Decision: retain `GcdRoute::SubresultantPrs` and reject a solver-driven multivariate dispatcher
for the current call graph.** The solver supplies no inputs to this API. This is an empty input
population, not evidence that no shape predictor can exist on general multivariate inputs.

### Call-site audit

The similarly named operations belong to distinct polynomial types:

| Boundary | Current implementation | Multivariate GCD consumer? |
|---|---|---|
| F4, Buchberger, normal forms and FGLM operator construction | polynomial division, row reduction and monomial operations | No |
| Solver candidate recovery | `src/grobner/solve.rs::candidate_values` converts constraints with `as_univariate`, calls `roots`, then filters candidates against other constraints | No |
| Root finding and equal-degree splitting | `src/poly/univariate/{roots,factorize}.rs` calls the free `gcd` on `UnivariatePolynomial<F>` | No |
| Certified Wiedemann reconstruction | `src/grobner/fglm/wiedemann.rs` calls the free `xgcd` on `UnivariatePolynomial<F>` | No |
| Planned solving | `src/grobner/planning/policy.rs` delegates to F4, FGLM and `solve_from_lex_basis` | No |
| Resultant route | `src/grobner/resultant.rs` builds Sylvester determinants and interpolates a univariate polynomial | No |
| Multivariate content, primitive part, squarefree part and squarefree decomposition | `src/poly/multivariate/multivariate_gcd.rs` calls its own `gcd_by` / `try_gcd_by` | Yes, for direct API callers; no incoming solver calls |

The multivariate `gcd`, `gcd_by` and `try_gcd_by` entry points and their content/squarefree wrappers
have no incoming runtime call from outside `multivariate_gcd.rs` in this revision. Integer GCD
methods in integer factorization are also distinct. The audit checks the indirect wrappers,
not just occurrences of the token `gcd` in `src/grobner`.

### Dynamic census

The existing `research-work` observer enters before zero/constant early returns in `gcd_by`, and
before Brown's field/degree refusal in `try_gcd_by`; non-Brown `try_gcd_by` delegates to `gcd_by`.
It counts every recursive entry. Therefore zero total `gcd_calls` proves zero outermost calls,
without needing a second shape-scanning observer. Every negative case asserts the **entire**
`GcdProfile` equals its default value. Three positive controls prove that the scope is active
and that all routes return the expected common factor.

| Workload | Field | Attempts / boundary | Multivariate GCD calls |
|---|---|---|---:|
| Cyclic-3, Katsura-3, Eco-3, Noon-3, Reimer-3, planted-3 | GF(32003) | 12 completed solves: six systems × direct lex F4 and grevlex F4/FGLM | 0 each |
| `x+y-3`, `x*y-2` | GF(13) | Three completed planner policies: conservative, fallback-enabled, classify-then-direct-lex | 0 each |
| The same bivariate pair | GF(13) | Completed resultant: degree 2, vanishes at 1 and 2 | 0 |
| Frozen `anemoi17-cico-n5-fcico.system`, ten variables | GF(65537) | One completed F4 batch, then explicit `TooManyBatches { limit: 1 }` | 0 |
| `(x+y)(y+1)`, `(x+y)(y+2)` | GF(13) | Primitive / subresultant / Brown positive controls, GCD `x+y` | 22 / 20 / 21 including recursion |

All solve RNGs use seed 0. The planted-3 generator receives `[3,5,7]`; the other systems are
exactly `benchmark_systems::{cyclic,katsura,eco,noon,reimer}::<3, Zp32003>()` at the audited commit
(Katsura-3 here means three variables, conventionally Katsura-2). Both routes return
`NoBaseFieldPoint` for Cyclic-3 and Reimer-3; the other eight corpus attempts return points checked
by substitution into every original equation. Each planner point is checked the same way.
The fallback-enabled planner completes on its first attempt; this census does not force its
failure/fallback branch. The static call audit covers that branch's existing delegated solvers.

The Anemoi fixture's SHA-256 is
`d39cf955ea1a683e468a5433236a2fd20b816cf405d41b3e46141044adb1679f`.
Its test retains default F4 settings except `max_batches=Some(1)` and asserts exactly one batch
completed. This is an actual cryptanalytic **prefix refusal**, not a completed basis or solve,
and says nothing about this input's later recovery cost. No large cryptanalytic campaign is needed
to establish absence of a call edge in the audited solver source.

Scopes are thread-local and synchronous. These cases use the current serial defaults; the
observer would need explicit worker aggregation if a future implementation called multivariate
GCD on worker threads. They do not count the separate univariate GCD, and make no claim that the
solver performs no GCD work of any kind.

### Predictor, wrong-choice cost and recommendation

The outermost multivariate input list is empty: arity, operand term counts and per-variable degrees
have **no observations**, rather than observed zero-valued shapes. A predictor's accuracy and
error rate are undefined on this population. The multivariate dispatcher has no call site at
which it could improve this solver, and the cost of any multivariate Brown probe/fallback in these
solves is exactly zero because no such probe runs. No speedup follows from changing the default.

For a direct multivariate API caller the trade-offs remain those of §§5 and 7. Brown's field
eligibility check can refuse extension fields or too few points before recursive work, but an
accepted shape can still pay interpolation plus PRS cleanup/fallback. Field eligibility alone
does not predict that cost. The existing `FiniteField`-only `gcd` cannot select Brown's
`KnownOrder`-bounded entry point without changing its contract. Retain the infallible subresultant
default; callers with an appropriate prime field can explicitly request Brown and handle
`GcdError`. External callers need their **own** input census before a dispatch/default proposal.
The present result neither ranks fixed defaults for that unobserved population nor proves a
universal predictor impossible. Univariate GCD optimization remains the separate #194 question.

### Reproduction and checks

The [census README](../../research/gcd-solver/README.md) gives the exact commands and output
regeneration procedure. Existing CI already runs `cargo test --features research-work --test
gcd_profile`, so all new guards run without an additional workflow. No production behavior is
changed: the new tests capture existing behavior, and a failing-before-implementation cycle is
inapplicable to this negative feasibility result. No new file-level source documentation is
needed; each new test has one sentence describing its assertion.
