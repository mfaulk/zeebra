# Structured Sylvester computation: five axes, and the one with an exponent in it

M25-D deliverable 3. `docs/research/resultant-elimination.md` §6.7 ranks "the determinant's
per-sample cost" first among what is left and calls it "the only axis left with an asymptotic
improvement in it". This document separates that into five distinct things, prices each against the
**measured** determinant cost law of #312, and recommends building exactly one of them.

**Build axis 4, the Euclidean/subresultant route. Do not build axes 1, 2, 3 or 5.** The prototype
that axis 4's analysis authorised exists and is tested, on branch
`research/m25-euclidean-resultant` — held out of this change for the process reason in §5.4, not
for a defect.

**And the headline is not the one the determinant stage suggests.** Axis 4 is a **measured 1 692×**
improvement to the determinant stage (§5.5) and only a **~3× improvement to the row**, because
once the determinants go, root finding at degree `5.3 × 10^5` and a 57 GB symbolic build are what
is left. §7 is that accounting and it is the most useful part of this document. The verdict in §8 is still *build* —
1 692× on the largest stage for ~200 lines is not a close call — but the claim "this raises the
reachable round count" **does not survive the accounting**, and saying so is the point.

## 0. The criterion, stated before the numbers

An axis is a **build** only if all three hold:

1. **It beats the measured baseline** — not a theoretical one, and not by a factor inside this
   workstation's noise.
2. **It is scored honestly as mathematical progress or as implementation performance.** Making an
   already-reachable row faster is the second kind; raising the maximum reachable round count is the
   first. The M25 research gate requires saying which, and §7 is where this document pays that bill.
3. **It does not require a new major subsystem.** If it does, file a future issue rather than
   absorbing it into M25.

And one gate specific to this document, because the winning axis was **previously rejected in this
repository**: a rejected approach may be reconsidered only when new evidence changes the decision,
and that evidence must be named. §5.1 names it.

## 1. The measured baseline

The determinant is `Matrix::determinant` (`src/linalg/matrix/mod.rs:359-387`) → `crout_lu_pivoting`
(`src/linalg/crout.rs:135`): Crout LU with partial pivoting, triple-nested scalar loops, one inverse
per pivot, `O(n³)` at about `n³/3` multiply-subtracts, **purely serial per determinant**.
Parallelism exists only *across* samples (`src/grobner/research/resultant.rs:376-403`, static blocks
over `std::thread::scope`).

### 1.1 The cost law is cubic, and there is no cache cliff to exploit

From #312 (`examples/determinant_sweep.rs`, orders 18 / 162 / 486 / 1 458 / 4 374, random bivariate
pairs, three draws each, per-point residuals):

| quantity | value | kind |
|---|---|---|
| exponent above the L2 footprint | **2.9953 ± 0.0285**, worst residual **3.7%** | **fitted** |
| exponent below L2 | 2.79 — fixed per-determinant overhead the small orders cannot amortise | **fitted** |
| order 1 458 core-time per determinant, 1 / 8 / 32 workers | **2.404 s / 2.821 s / 3.148 s** | **measured** |
| order 162 per determinant, reference route / synthetic sweep | **3.439 ms / 3.624 ms** | **measured** |

Two consequences, and both matter for this document more than the exponent itself.

**There is no cache anomaly.** The fit is cubic to within the measurement *including at order
4 374*, whose 153 MB matrix exceeds a CCX's L3 entirely. So the cache-transition story that
motivated #289 does not survive its own measurement, and **the baseline is clean**: there is no
implementation slack for a "structured" method to recover by accident. Anything recommended here has
to beat an honest `n³`, not a cache-bound mess.

**#289's 3.116 exponent was an artefact, and it is the cleanest available example of this
workstream's own methodological hazard.** It came of dividing a **32-worker** core-time at order
1 458 by a **single-worker** one at order 162. The excess was the *width*, not the order — and that
spurious super-cubic exponent then propagated into an eight-round projection. Two figures at
different concurrencies, divided. This document therefore quotes **no per-determinant figure without
its worker count**, and `determinant_core_ms` now deliberately takes the *larger* of the fitted and
cubic laws, because 2.9953 is below 3 and a model that under-predicts authorises a run nobody costed.

The 2.868 ms order-162 anchor that earlier documents used **no longer reproduces**; the same
13 123-determinant reference route measures 3.439 ms today. Figures below use the new ones.

Note also what the three worker counts say: 2.404 → 3.148 s is a **31% core-time penalty for running
32-wide**, which is memory-bandwidth contention on a 17 MB working set. Axis 4 shrinks that working
set to ~6 kB, so it should recover that penalty as well as the exponent — §5.2.

### 1.2 The two laws the route obeys

Both **derived**, both checked against a measurement. For `d = 3` and `R = R_F + R_P` rounds, with
`y` eliminated:

```
Sylvester order        N  =  2 · 3^R          (18 at R=2, 162 at R=4, 1458 at R=6 — all measured)
per-polynomial degree  n  =  3^R              so N = 2n
sample count           S  =  3^{2R_F+R_P} + 1 (#179, predicted per row and validated per row)
resultant degree       D  =  S − 1            ([JAZ] slide 22, confirmed on three rows in §6.3)
```

so the determinant work is `S · N³/3 = (8/3) · 3^{5R_F + 4R_P}` multiply-subtracts.

**Check.** `poseidon31-cico-t16-rf2-rp4`: `S = 6 562` determinants at the **measured** 3.148 s
32-worker core-time is 645 s of wall on 32 cores = **10.8 min**. Measured row: **9.22 min**. Within
17% on the one six-round row that has run, which is what licenses using the law on the two that have
not.

### 1.3 The prize, concretely

Six-round rows all have Sylvester order 1 458 and share the same degree-729 symbolic build.
Per-determinant cost **measured** at 32 workers; row totals **extrapolated** by sample count.

| row | `R_F` | `R_P` | `S` | determinant wall, 32 cores | status |
|---|---:|---:|---:|---:|---|
| `rf2-rp4` | 2 | 4 | 6 562 | 10.8 min (**measured 9.22 min**) | done |
| `rf4-rp2` | 4 | 2 | 59 050 | **≈1.61 h** | not run |
| `rf6-rp0` | 6 | 0 | 531 442 | **≈14.5 h** | not run |

One rung further, `rf7-rp0` at `R = 7`: `N = 4 374`, `S = 3^14 + 1 = 4 782 970`, per-determinant
`3.148 s · 27 = 85.0 s` at 32 workers (**extrapolated** by the cubic law), total **≈147 days on 32
cores**.

So the prize has two parts, different in kind:

- **`rf4-rp2` and `rf6-rp0`** — 1.6 h and 14.5 h of determinants. Uncomfortable, not impossible.
  A factor here is **implementation performance**.
- **`R = 7`** — 147 days, and the step from `R = 6` is `3^5 = 243`. Only an exponent change reaches
  it, which would be **mathematical progress**. A 10× constant leaves 14.7 days.

§7 revisits both after the rest of the route is costed, and the answer changes.

## 2. Axis 1 — constant-factor SIMD and threading

**What it is.** Make the `O(n³)` determinant faster: vectorise Crout's inner loop; block it for
cache.

**What it would deliver, and why §1.1 shrinks it.** Threading *across* samples is done. Within one
determinant: the inner loop is a scalar axpy over a 31-bit prime field, and AVX2 on `x86-64-v3`
offers 8 lanes of 32-bit with Montgomery or Barrett reduction eating some — realistically **3–5×**,
a **hypothesis** from reading `crout.rs`. The *blocking* half of the idea is now largely dead:
#312 measured the kernel as cubic with **no cache anomaly even at 153 MB**, so there is no cache
term to recover. What is left of axis 1 is vectorisation alone.

And vectorisation inside one determinant competes for the cores the across-samples sweep already
occupies at 92–95% efficiency, which makes it **close to zero-sum**: SIMD lanes within a
determinant and independent determinants on other cores draw on the same memory bandwidth, which
§1.1's 31% wide-running penalty already shows is binding.

**Verdict: do not build, and specifically not before axis 4.** Two reasons, the second decisive:

1. Implementation performance only: a 10× does not reach `R = 7` (§1.3).
2. **Axis 4 deletes the work axis 1 optimises.** The Euclidean route never forms the matrix, so the
   LU work ceases to exist in the hot path. The axes are not additive; axis 1 is *conditional on
   axis 4 not happening*.

## 3. Axis 2 — reusing structural information across evaluations

**What it is.** The `S` Sylvester matrices differ *only* in the evaluation point. §6.7's ranked list
names exactly this. What can be computed once and reused `S` times?

**Enumerated, and the axis is empty.**

- **The symbolic Sylvester construction** — already shared, already under 1% of every row's *time*.
  Its problem is memory, not reuse (§7).
- **Evaluating the matrix entries** — a Sylvester matrix has only `2(n+1)` distinct entries, two
  shifted coefficient vectors, each a polynomial of degree ≤ `n`. Horner on all of them is `≈ 2n²`
  multiplications per sample against the determinant's `N³/3`: **0.2%** at `R = 6` (**derived**:
  `1.06 × 10^6` against `1.03 × 10^9`). Fast multipoint evaluation would be optimising 0.2%.
- **Incremental LU as the sample moves** — **no.** LU with partial pivoting is not a continuous
  function of the entries (the pivot sequence changes discretely), and `Syl(a_{k+1}) − Syl(a_k)` has
  rank up to `2(n+1)`, not low rank. There is no update formula.
- **Baby-step/giant-step over samples** — **no.** The determinant is neither multiplicative nor
  additive in the sample point.

**Verdict: nothing to build.** Worth stating plainly because §6.7 bundled axes 2, 3 and 4 into one
line. The asymptotic improvement it correctly identified is real, but it lives on axes 3, 4 and 5.
The only "reuse" that pays is the opposite of reuse: not building the matrix at all.

## 4. Axis 3 — Sylvester and displacement structure

**What it is.** A Sylvester matrix is Toeplitz-like with **displacement rank 2**. Superfast
structured solvers — Bitmead–Anderson, Morf, the Levinson and Schur recursions, Kailath–Sayed's
displacement framework — run in `O(n²)` classically, `O(n log² n)` with fast multiplication.

**The complexity is right; the axis is dominated, for a specific reason.** The leading principal
minors of a Sylvester matrix are, up to signs and powers of leading coefficients, the
**subresultants** of the pair, and the Schur/Levinson recursion a displacement-structured
determinant algorithm runs *is* the subresultant remainder sequence in matrix notation.

> Axis 3 and axis 4 are the **same algorithm in two presentations**, at the same `O(n²)`.

The presentations are not equally expensive. The displacement form additionally needs generator
pairs maintained through the recursion and breakdown handling when a leading minor vanishes — the
same degeneracy axis 4 settles with a degree comparison (§5.3). **Verdict: do not build. Identical
complexity to axis 4, strictly more implementation.** This is a section rather than a footnote
because it saves a month.

## 5. Axis 4 — the Euclidean / subresultant route

### 5.1 It was rejected here; here is the named new evidence

`src/grobner/research/resultant.rs` module docs, under *"Why the determinant and not a Euclidean
algorithm"*:

> A subresultant or Euclidean approach would be asymptotically better and would need exactly the
> case analysis this avoids: specializing `f` at a point where its leading coefficient in `y`
> vanishes drops its degree, and the specialized resultant is then **not** the specialization of the
> resultant. That is the classic trap, and **at the sizes M23-E measures — a Sylvester matrix of
> order at most a few dozen over a 31-bit prime — it buys nothing worth the risk.**

That is **correct, and explicitly scoped to its sizes.** The scope has changed, measurably:

| | M23-E, when the decision was made | now |
|---|---|---|
| Sylvester order | **18** (`R = 2`) | **1 458** (`R = 6`); 4 374 at `R = 7` |
| operation-count gap `(16/3)·3^R` (**derived**, §5.2) | **48×** | **3 888×**; 11 664× at `R = 7` |
| **measured** ratio at that order (§5.5) | — (not worth measuring) | **1 692×** |
| stage cost on the target row | milliseconds, on a row that finished in seconds | **14.5 h on 32 cores**, on a row that has not been run |
| share of the row | not the bottleneck | **67%** of `rf6-rp0` (§7) |

So: the gap grew 81×, and the stage went from milliseconds to the largest item in a row that has not
been attempted. "Buys nothing worth the risk" was a statement about absolute cost at order 18.
And §5.3 closes the trap that motivated the rejection, which the 2023 decision did not have.

### 5.2 The complexity, derived

Classical Euclidean resultant of two degree-`n` polynomials: drive the remainder sequence with
`Res(f, g) = (−1)^{nm} lc(g)^{n − deg r} Res(g, r)`. For a generic pair the degree drops by one per
step, so the cost is `Σ_{i=1}^{n} i ≈ n²/2` multiply-adds plus `n` inversions.

| | per sample | at `R = 6` (`n = 729`, `N = 1 458`) |
|---|---|---:|
| dense LU | `N³/3 = (8/3)·3^{3R}` | `1.033 × 10^9` |
| classical Euclid | `n²/2 = (1/2)·3^{2R}` | `2.657 × 10^5` |
| **operation-count ratio** | **`(16/3) · 3^R`** | **3 888×** |

The ratio **grows 3× per round**: the determinant work drops from `3^{5R_F+4R_P}` to
`3^{4R_F+3R_P}`, a saving of `3^R`. These are exact ratios of operation counts at a fixed order, so
they do **not** depend on #312's fitted law.

Memory moves too, in the direction §1.1 showed matters: the per-sample working set goes from an `N²`
matrix (**17 MB** at `R = 6`) to two coefficient vectors (**~6 kB**), a factor of ~2 800. That should
also recover the **31% core-time penalty** measured for running 32-wide — a **hypothesis**, worth one
measurement after integration.

### 5.3 The specialization trap, closed in `O(1)` per sample

The trap is real as stated: `Res(f(a,·), g(a,·))` is the resultant of the *specialized* pair, whose
`y`-degrees may have dropped, while the route needs `det Syl_{n,m}(f, g)(a)` at the **formal**
degrees taken from the bivariate coefficient-vector lengths — which is exactly how
`sylvester_determinant` (`resultant.rs:823`) sizes its matrix.

The correction is classical and `O(1)`. Expanding `det Syl_{n,m}` along its first column when
`deg f = n' < n` leaves one nonzero entry, `lc(g)`, in row `m`:

```
deg f = n' < n, deg g = m        →  det Syl_{n,m} = (−1)^{m(n−n')} · lc(g)^{n−n'} · Res(f,g)
deg f = n,      deg g = m' < m   →  det Syl_{n,m} = lc(f)^{m−m'} · Res(f,g)
both below their formal degrees  →  det Syl_{n,m} = 0        (the first column vanishes)
```

Two degree comparisons and one exponentiation per sample. **The asymptotic win is available without
the trap being left to the caller**, and that is the substantive addition to the 2023 decision beyond
the change of scale.

**It may never fire, and checking is cheap.** It fires only when `lc_y(f)` or `lc_y(g)` — polynomials
in the surviving variable — have a root at a sample point. If either is a nonzero *constant*, no
sample can trigger it. For `cico_bivariate`'s Poseidon outputs that is a property of the construction,
inspectable in milliseconds. **That check gates any integration**, and it is not done here:
`src/grobner/research/resultant.rs` is owned by another agent this milestone.

### 5.4 The prototype, and why it is not in this change

An operation-count gap of 3 888× at the stage that stops the ladder cleared §0's bar for a prototype,
so one was written — small, isolated, and differential against the thing it would replace.
`resultant(f, g)` (classical Euclidean, `O(d²)`) and `resultant_at_formal_degrees(f, g, n, m)`
(§5.3's correction, which is what an elimination route calls), with four tests:

| test | what it pins |
|---|---|
| `euclidean_resultant_matches_the_sylvester_determinant` | agreement with an explicitly built Sylvester determinant over `Matrix::determinant`, random full-degree pairs, every degree pair `1..7` |
| `formal_degree_correction_handles_vanishing_leading_coefficients` | §5.3's three cases over **every** combination of formal degree `1..6` and deficit `0..formal` — the trap tested at every way it can fire |
| `resultant_vanishes_on_a_shared_root` | zero exactly on a common factor |
| `constant_and_zero_arguments` | `Res(f, c) = c^{deg f}`, and the zero polynomial |

**It was held out of that change, and the reason was a process gate rather than a problem with the
code.** M25-D's rule was that a prototype must be justified *in the document* before it exists. The
*analysis* did precede the code — §5.1's scope change and §5.2's operation count are what authorised
it — but this document was written afterwards, so the letter of the gate was not met. Three things
made holding it free:

1. It was not integrated into anything, so nothing was lost by waiting.
2. The integration needed a check that workstream could not run: whether `lc_y(f)` and `lc_y(g)` are
   constant on `cico_bivariate`'s outputs (§5.3), in a file another agent owned that milestone.
3. §9's issue — integrate behind a flag, dense determinant as differential reference, gated on that
   check — was the natural place to review the module and its integration together.

§5.5's measurements were taken against that branch, through a harness that adds nothing to `src/`.

**That issue is #350, and it is now done — §5.6.** The holding commit was
`5ebb516 feat(poly): resultant by the Euclidean algorithm, and the five Sylvester axes priced`,
reverted by `b3bd7f0 revert(poly): hold the Euclidean resultant for its own issue`, so the code
reached `main` only as history. #350 restored it to the location that commit chose,
`src/poly/univariate/resultant.rs`, rather than reimplementing it elsewhere.

### 5.5 Measured, at the orders that matter

Three kinds of number appear below and they are not interchangeable:

- **operation count** — exact arithmetic about the *algorithms*, independent of machine and
  implementation. `16n/3`.
- **measured ratio** — a fact about *this machine, this implementation, this build*. Neither
  predicts the other.
- **bound** — a quantity constrained from a measurement taken elsewhere, not measured here.

Measured on one pinned core (`taskset --cpu-list 52`) under `tools/benchlock.sh`, three draws at the
two largest orders and twenty at the others, **with agreement against `Matrix::determinant` asserted
at every size**. Built with `-C target-cpu=x86-64-v3`, `lto = "fat"`, `codegen-units = 1`, verified
present with `cargo build -v | grep target-cpu`; `RUSTFLAGS` never set.

| `n` | Sylvester order | `Matrix::determinant` | `resultant` | **measured ratio** | operation count `16n/3` | agree |
|---:|---:|---:|---:|---:|---:|---|
| 18 | 36 | 47.9 µs | 4.2 µs | **11×** | 96 | ✓ |
| 81 | 162 | 3.62 ms | 31.7 µs | **114×** | 432 | ✓ |
| 243 | 486 | 91.7 ms | 177 µs | **519×** | 1 296 | ✓ |
| **729** | **1 458** | **2.272 s** | **1.343 ms** | **1 692×** | 3 888 | ✓ |

**The harness cross-checks against #312.** Its order-1 458 single-worker core-time is a **measured**
2.404 s; this harness, a different binary on a different core, measures **2.272 s** — 5.5% apart. So
the baseline column is not an artefact of a throwaway crate.

**1 692× measured at the order the six-round rows use**, against an operation count of 3 888×. The
factor of 2.3 is **not** the per-step inversion: charging Euclid's `n` inversions at the plateau
`docs/research/batch-inversion.md` measured over Mersenne-31 — one inversion costs 35× three
multiplications, so ~105 multiplications pre-#160 — accounts for only 29% of the gap. That is a
**bound** carried from another document's measurement, not something measured here.

What the gap actually is, **measured**, is per-operation efficiency:

```
Matrix::determinant   2.272 s  / (1458³/3 = 1.03e9)  =  2.20 ns per multiply-subtract
resultant             1.343 ms / (729²/2  = 2.66e5)  =  5.05 ns per multiply-add
```

**LU's inner loop is 2.3× more efficient per field operation than the remainder sequence's**, which
is credible rather than mysterious: LU's is a long fixed-stride axpy, while a division step is an
axpy over a *shrinking* vector with a fresh scalar multiplier and an inversion each time. Euclid's
per-operation cost is still falling with `n` (`n = 81 / 243 / 729` gives 9.7 / 6.0 / 5.05 ns), so the
ratio is still amortising upward: it grew **3.26×** from `n = 243` to `n = 729` against the
operation count's 3×, which **extrapolates** to roughly **5 500×** at `n = 2 187` (`R = 7`).

#### 5.5.1 The build flag, which this measurement nearly lost

The benchmark lives in a throwaway crate **outside** the worktree, deliberately, so that nothing had
to be added to `src/` for a measurement. `.cargo/config.toml` in this repository says in its own
comment that it "is not inherited by crates that depend on `zeebra`" — and that is exactly what
happened: the **first** run silently lost `-C target-cpu=x86-64-v3`, `lto = "fat"` and
`codegen-units = 1`. `RUSTFLAGS` was never set; the flag was lost by *where* the build ran.

Both runs are kept, because the comparison is the useful part:

| build | order-1 458 LU | order-1 458 Euclid | ratio |
|---|---:|---:|---:|
| no `target-cpu`, no LTO | 6.360 s | 3.295 ms | **1 930×** |
| `x86-64-v3`, fat LTO, cgu 1 | **2.272 s** | **1.343 ms** | **1 692×** |
| speedup from the flags | 2.80× | 2.45× | — |

So the flags are worth **2.8× to LU and 2.45× to Euclid**, and the ratio fell 12% — LU gains more
from AVX2 than a division step does, as predicted. **The v3 row is the figure to quote.** This
repository has lost two sets of figures to `RUSTFLAGS`; this is a third route to the same failure,
and the cross-check against #312 in the table above is what caught it.

#### 5.5.2 Does this change §8? No.

At 1 692× rather than 3 888×, `rf6-rp0`'s determinants go from 14.5 h to **~31 s** on 32 cores
instead of ~10 s, and §7.1's row totals move by well under a percent because they are dominated by
root finding either way. What the measurement changes is what should be quoted: **1 692× measured**,
not 3 888× derived — the operation count overstates the real gap by 2.3× and has no business in a
recommendation now that there is a measurement.

### 5.6 Landed in `src/`, re-measured, and the asymptotic claim confirmed

#350 restored the held module to `src/poly/univariate/resultant.rs` and added the allocation-free
form a sample loop needs, `resultant_from_coefficients`, whose formal degrees are the coefficient
slice lengths. `src/grobner/research/resultant.rs` selects between the kernels through
`DeterminantKernel::{Dense, Euclidean}` on `ResultantOptions`, **defaulting to dense** so every
figure taken before this existed still reproduces.

**The figures below are from the shipped code**, not the throwaway harness: both kernels in one
binary, one pinned core, on the lock, minutes apart, inside the worktree so
`-C target-cpu=x86-64-v3` is inherited rather than hoped for (§5.5.1).

| order | dense | Euclidean | ratio |
|---:|---:|---:|---:|
| 162 | 3.609 ms | 26.40 µs | 137× |
| 486 | 94.790 ms | 146.07 µs | 649× |
| **1 458** | **2.322 s** | **1.109 ms** | **2 094×** |
| fitted exponent | **2.9431 ± 0.0183** | **1.8452** (above L2) | — |

**The asymptotic claim is now measured rather than derived.** §5.2 argued `O(n³)` against `O(n²)`
from operation counts; the fitted exponents are **2.94 and 1.85**, a gap of 1.09 powers of the order.
That is also why the ratio climbs with the order — 137× to 2 094× over a 9× order range — and why
M23-E's judgement was right at order 18 and wrong at order 1 458. A constant-factor framing of this
axis was never the right one.

**On 1 692× versus ~2 100×.** Across three matched runs the order-1 458 ratio was **2 006×, 2 094×
and 2 151×**, so ~2.1 × 10³ rather than §5.5's 1 692×. The difference decomposes, and neither half is
a correction to §5.5:

- The **dense** side measured 2.322, 2.413 and 2.553 s against §5.5's 2.272 s. The spread is
  run-to-run — order 1 458 is 8 determinants a draw — and the whole range sits inside #318's recorded
  ~1.2× drift. Nothing here says the recorded figure was wrong.
- The **Euclidean** side measured 1.109–1.203 ms against the prototype's 1.343 ms, about 17% faster,
  and the mechanism is known: the prototype took `&a % &b` on `UnivariatePolynomial` once per
  remainder step, where the shipped path works in place on coefficient slices. The sequence is as
  long as the degree, so one allocation per step is the step.

**So §5.5 stays the quotable cross-harness figure and this is the quotable same-binary one.** Per
#350's own framing and §7, none of this raises the reachable round count: after axis 4 the six-round
route is 78% root finding, and the row gains ~3× against the stage's ~2 000×.

#### 5.6.0 The parallel hypothesis, falsified

§5.2 and #350 predicted that axis 4 would **recover** #319's width penalty as well as the exponent,
because the per-sample working set falls from a 17 MB matrix to two ~6 kB coefficient vectors. The
authorized `rf4-rp2` row (#367) measured the opposite:

| quantity | Euclidean | dense |
|---|---:|---:|
| core-time per determinant, 1 worker | **1.109 ms** | 2.322 s |
| core-time per determinant, 32 workers | **3.563 ms** | — |
| **width penalty at 32 workers** | **3.21x** | **1.32x** modelled, 31-44% measured (#319) |

So the kernel with the small working set contends **worse** than the one with the large one, and the
bandwidth story §5.2 told cannot be what dominates. The budget guard had been given the dense
penalty on the stated grounds that this was conservative; it was optimistic, and under-predicted the
determinant stage by **2.43x**. Corrected to a measured two-point penalty.

The candidate mechanism is **allocator contention** rather than bandwidth — `remainder` allocates a
fresh vector per step, and the sequence is as long as the degree, so one order-1 458 determinant
makes on the order of a thousand allocations and 32 threads do it at once. **Unmeasured**, and #412
is the measurement; it also names the fix, which is two reusable buffers swapped per step.

Nothing here argues against axis 4: it is 2 094x per determinant at this order and it is what made
the `rf4-rp2` row affordable. What it argues against is quoting its parallel behaviour from a
working-set argument.

#### 5.6.1 The specialization trap, closed twice and cross-checked

§5.3's correction was derived a second time, independently, while implementing #350 — and the two
derivations agree exactly: `(−1)^(m·deficit) · lc(g)^deficit` when `f` drops, `lc(f)^deficit` with
**no** sign when `g` drops, zero when both do. Agreement between two derivations is worth more than
either alone, and it is pinned by a test rather than by this paragraph:
`the_two_forms_agree_over_a_coefficient_sweep` runs every combination of formal degrees up to 2 over
a coefficient set containing zero — 15 625 pairs, so every way the trap can fire — against **both**
an explicitly built Sylvester determinant and the polynomial-typed form.

Two further guards, because a fast kernel checked against itself is not checked:

- `agrees_off_domain` validates against the **dense** kernel whatever the route used, so every
  predicted run is a differential test of the remainder sequence rather than only the unit tests.
- `DeterminantBatch` records its `kernel`. The two differ by three orders of magnitude at the same
  order, so a batch that does not name its kernel is a number nothing can be compared with.

## 6. Axis 5 — polynomial-matrix determinant algorithms

**What it is.** Skip the evaluation sweep: compute `det Syl(f, g)` directly over `F_p[x]`.
Labahn–Neiger–Zhou and Villard's algorithm give `Õ(N^ω D)` for an `N × N` matrix of entry degree
`≤ D`. This is the published state of the art — FreeLunch's `polyDet` uses PML for it
(`docs/research/griffin-freelunch.md` §4.1), and eprint 2026/1281 (*Resultants Meet Resultant*,
which broke full-round Griffin) finishes with Villard's algorithm.

**The crossover, derived.** Here `N = 2·3^R` and `D = 3^R`, so with `ω = 2.81`:

```
axis 5:  N^ω · D   =  2^ω · 3^{(ω+1)R}  ≈  7 · 3^{3.81 R}
axis 4:  S · n²/2  =  3^{4R}/2                              (at R_P = 0)

axis 4 / axis 5  =  3^{0.19 R} / 14  >  1   ⟺   R > 12.7
```

**Axis 5 overtakes axis 4 at about 13 rounds** on operation counts — six rungs past anything
reachable.

**Correcting for §5.5's measurement moves that, and it should be said.** Euclid runs at 5.05 ns per operation
against LU's 2.20 ns, so axis 4's real cost is ~2.3× its count. Carrying that factor:
`2.3·3^{0.19R}/14 > 1 ⟺ R > 8.7`. So the honest crossover is **about 9 rounds**, not 13 — still
three rungs past `R = 7`, which costs 147 days of determinants today, and still before the `Õ`
polylogarithms and the constants a polynomial-matrix multiplication carries (both of which push it
back out). Worse for
axis 5: refining axis 4 with half-GCD gives `O(M(n) log n)` per sample, which at Zeebra's Karatsuba
`M(n) = n^1.585` is `3^{3.585R}·R` — **better than axis 5's `3^{3.81R}` at every `R`**. Axis 4's
refined form dominates axis 5 unconditionally at this problem's `N`-to-`D` ratio, which the Sylvester
construction pins at `N = 2D`.

**Implementation cost: an entirely new major subsystem.** Polynomial matrices, polynomial-matrix
multiplication, order bases, and Villard's or LNZ's algorithm — PML is a library, not a function.
`docs/research/elimination-beyond-grobner.md` §5 already lists "Sylvester/Villard machinery" as
absent and §6.3 argues against building it.

**Verdict: do not build; file as a future issue with the crossover as its trigger** (§9), per §0
gate 3.

### 6.1 Half-GCD is not a new finding here

`docs/research/fast-univariate.md` §4.5 measured half-GCD as **slower** than plain Euclid at Zeebra's
current multiplication, and `src/poly/univariate/gcd.rs:9-12` records the same. Nothing here
contradicts that. Sequencing: **classical Euclid now** (1 692× measured, already written); half-GCD only if
determinants ever bind again, where that document's own model puts it at a further ~1.6× at
`n = 729`. §8 does not depend on it.

## 7. The accounting that changes the claim

Determinants are often quoted as **~99%** of the route. That figure is explicitly a **four-round**
one — `resultant-elimination.md` line 139 says so in as many words, "it was 99% of the four-round
row (§6.4)" — where the resultant had degree 729 or 6 561 and root finding cost 59.5 ms or 4 156.5 ms
against determinant stages of seconds.

**It does not survive to six rounds**, and the reason is structural: the resultant degree `D = S − 1`
grows as fast as the sample count, so root finding grows *quadratically in `S`* while the determinant
stage grows only linearly. Carrying the 99% forward to a six-round row — which is easy to do, since
it is the number in circulation — is what would make axis 4 look like a 4 000× row improvement
instead of a 3× one.

Three tail stages, each anchored on a measurement and extrapolated:

| stage | anchor | law | kind |
|---|---|---|---|
| symbolic build | **48.4 min, 57.0 GB** at `R = 6` (§6.8) | identical for all six-round rows — they share degree 729 | **measured** |
| interpolation | **5.1 ms** at `S = 730`, predicted-count Lagrange (§6.7) | `O(S²)` | **measured** anchor, `O(S²)` **derived** |
| root finding | **59.5 ms** at degree 729, **4 156.5 ms** at 6 561 (§6.3) | exponent **1.933** on two points | anchors **measured**, exponent **fitted on two points** |

The root-finding exponent is fitted on **two points** and must be read as such; it is consistent with
`roots()` being `gcd(f, x^q − x)` via `pow_mod` — `O(log q)` polynomial multiplications at Karatsuba
`M(d) = d^{1.585}` — which is quasi-quadratic, not cubic.

### 7.1 Row budgets, six rounds

All determinant and tail figures **extrapolated** from the anchors above; the build is **measured**.

| stage | `rf4-rp2` (`D = 59 049`) | `rf6-rp0` (`D = 531 441`) |
|---|---:|---:|
| symbolic build | 0.81 h | 0.81 h |
| determinants, LU, 32 cores | **1.61 h** | **14.5 h** |
| interpolation | 0.01 h | 0.75 h |
| root finding | 0.08 h | **5.63 h** |
| **total today** | **2.51 h** | **21.7 h** |
| determinants, **axis 4** at the measured 1 692×, 32 cores | ~3 s | ~31 s |
| **total after axis 4** | **0.90 h** | **7.2 h** |
| **row improvement** | **2.8×** | **3.0×** |

So: **axis 4 is 1 692× measured on the stage and 3× on the row**, and after it `rf6-rp0` is
**root-finding-bound** — 5.63 h of a 7.2 h row, 78%.

### 7.2 Seven rounds

| stage | `rf7-rp0` (`S = 4 782 970`, `D = 4 782 969`) |
|---|---|
| symbolic build | **~1 TB transient — blocked** (§7.3) |
| determinants, LU, 32 cores | ~147 days |
| determinants, **axis 4**, 32 cores | **~37 min** |
| interpolation, `O(S²)` | ~2.5 days |
| root finding, exponent 1.933 | **~16.4 days** |

Axis 4 removes a 147-day wall and leaves **~19 days of serial tail plus a memory-blocked build**.
That is an 8.7× row improvement if the build were solved — large, and **not** sufficient.

> **This is where the claim has to be downgraded.** Axis 4 alone does **not** raise the reachable
> round count. It is **one of four** things `R = 7` needs: axis 4, an output-bounded symbolic
> multiply (#243), a sub-quadratic root finder at degree `5 × 10^6`, and a sub-quadratic
> interpolation at `S = 5 × 10^6`. Three of the four are *serial quadratic stages with known fast
> algorithms Zeebra has not wired in*, which is a much better position than needing new mathematics —
> but it is not the position "axis 4 buys a round" would describe.

### 7.3 The build, and a structural note from a second subsystem

The 57 GB is a *transient*, not a result. `SparseMultiPoly`'s multiply materialises every pairwise
term-product in one `Vec` before collecting like terms, so cubing sixteen degree-243 words costs
`118 827 × 29 768 = 3.54 × 10^9` entries — **56.6 GB predicted against 57.0 GB measured** — to build
a 266 815-term result occupying 4.3 MB. Four orders of magnitude of transient. Tracked in **#243**.

One rung further: at `R = 7` the build cubes degree-729 words (266 815 terms each), so the `p*p` step
alone is `266 815² = 7.1 × 10^{10}` entries ≈ **1.14 TB** — **extrapolated**, from a mechanism that
predicted the `R = 6` figure to 0.7%.

**The same failure appears in a second subsystem, which is evidence rather than restatement.**
F4MEM's #237 attribution found that **88.4% of a 14 GB F4 peak** on `fukuoka-mq-III-n20-seed0` is
symbolic preprocessing's pending monomial queue (162 M `Monomial<20>` at high-water), while the
matrix entries the budget actually counts are **1.3%** and the pair heap — the prior top suspect — is
**4.5 MB**. Both that and the 57 GB here are *unbounded intermediate containers in a symbolic stage,
dominating a peak attributed to the numeric stage.* In both subsystems, once the obvious numeric
thing is fixed, the resource goes to symbolic bookkeeping. That is an argument for #243 being the
right next issue, from two independent directions.

### 7.4 Root finding may already be solvable with what exists

`roots()` (`src/poly/univariate/roots.rs`) is `gcd(f, x^q − x)` by `pow_mod` plus equal-degree
splitting — `O(log q)` multiplications at Karatsuba. Two cheaper directions, neither requiring new
mathematics:

- **An NTT multiply** would make each of `pow_mod`'s `O(log q)` multiplications quasi-linear instead
  of `d^{1.585}`. `docs/research/fast-univariate.md` tracks this; it is the same missing primitive
  the Graeffe route names.
- **`graeffe_root`** is measured at **3.11 s for one root at degree `3^13 = 1 594 323`**
  (`graeffe-root-finding.md` §4.4, post-#161) — three times the degree of `rf6-rp0`'s resultant, in
  seconds. **But it returns one root where the route needs all candidates**, so it is not a drop-in
  and the comparison is not like for like. Whether deflate-and-repeat over `graeffe_root` beats
  `roots()` at degree `5 × 10^5` is **an open measurement, and a cheap one.**

**Not claimed:** that root finding is solved. Claimed: the tail axis 4 exposes is a *wiring* problem
with two candidate answers already in the crate, not a research problem — and measuring which is the
natural successor to this document.

## 8. Verdict

| axis | complexity | implementation cost | delivers | verdict |
|---|---|---|---|---|
| 1 — SIMD / threading constants | `O(n³)`, 3–5× (blocking half dead: #312 found no cache anomaly) | high; `src/linalg/` contention | implementation performance, near zero-sum against the sweep | **do not build**; axis 4 deletes the work |
| 2 — reuse across evaluations | no improvement available | — | nothing | **nothing to build** |
| 3 — displacement / Sylvester structure | `O(n²)` | high; generators + breakdown handling | same as axis 4 | **do not build**; identical complexity, strictly more work |
| 4 — **subresultant / Euclidean** | **`O(n²)`; `3^R` saved** | **low; ~200 lines, written and tested, on its own branch** | **1 692× measured on the stage, 3× on the row** | **BUILD** |
| 5 — polynomial-matrix determinant | `Õ(N^ω D)` | **new major subsystem** | overtakes axis 4 past `R ≈ 8.7` once Euclid's measured per-operation penalty is charged | **do not build; file with a trigger** |

**Build axis 4**, scored against §0:

1. **Beats the measured baseline**: **1 692× measured** at order 1 458 against a baseline #312
   measured as cleanly cubic with no slack to recover, growing 3.5× per 3× in `n`. The operation
   count predicts 3 888×; the factor of 2.3 is Euclid's **measured** 5.05 ns per operation
   against LU's 2.20 ns (§5.5), and the harness cross-checks against #312's independent order-1 458
   figure to 5.5%.
2. **Honestly scored**: at six rounds it is **implementation performance** — a 3× row improvement
   (§7.1), not a new reachable size. At seven rounds it removes the largest of **four** walls and is
   **necessary but not sufficient** (§7.2). The claim "it raises the reachable round count" is
   **withdrawn**; the accounting does not support it.
3. **No new subsystem**: two functions and four tests, which exist on
   `research/m25-euclidean-resultant` (§5.4).
4. **The rejection is reconsidered on named evidence**: order 18 → 1 458, gap 48× → 3 888×, the stage
   from milliseconds to 67% of a row that cannot be run — and the trap that motivated the rejection
   closed in `O(1)` per sample (§5.3), which the 2023 decision did not have.

Three numbers decided it: **1 692× measured** at the order the six-round rows use (against an
operation-count gap of **48×** at the order the 2023 rejection was scoped to); **14.5 h → ~31 s** for
`rf6-rp0`'s determinants on 32 cores
against a **5.63 h** root-finding tail that then dominates; and **`R > 8.7`** for axis 5's crossover
once Euclid's measured per-operation penalty is charged, which still rules out the subsystem by
three rungs.

## 9. Issues this suggests

**File, High.** *"Land the Euclidean resultant and integrate it into the bivariate elimination
route"* — take `research/m25-euclidean-resultant`'s module (§5.4), then consume
`resultant_at_formal_degrees` in `src/grobner/research/resultant.rs`'s sample loop behind a flag, so
the dense determinant stays as the differential reference, **gated on §5.3's leading-coefficient
check**. Deliverable: `rf4-rp2` and `rf6-rp0` run. It is the only item in M25-D the arithmetic says
build, and it unblocks the two rows the milestone wants.

**File, High.** *"Price root finding at degree 5·10^5: `roots()` against deflate-and-repeat
`graeffe_root`"* — §7.4. After axis 4 this is **78% of `rf6-rp0`**, it is a measurement rather than a
build, and both candidates already exist in the crate.

**Already filed, and now top of the ranked list: #243.** §7.3 raises its priority — after axis 4 it
is the binding constraint at six rounds and a 1 TB wall at seven, and #237's independent finding in
F4 points the same way.

**File as a future milestone, Low.** *"Polynomial-matrix determinant: Villard / Labahn–Neiger–Zhou
over `F_p[x]`"* — axis 5, with the crossover at `R ≈ 8.7` (§6) recorded as the trigger, in the style of
#58's deferred Wiedemann/Krylov entry. The evidence that would change it is a target whose
`N`-to-`D` ratio is not pinned at `N = 2D`.

**Argue against filing:** anything on axes 1, 2 or 3. Axis 1's work is deleted by axis 4 and its
blocking half is refuted by #312; axis 2 has no content; axis 3 is axis 4 with more machinery.

## 10. Marked unverified, and open

- **The 1 692× is a *measured ratio*, not a property of the algorithms.** It is a fact about one
  core of this workstation, this implementation and this build. The machine-independent statement is
  the operation count `16n/3` = 3 888× at `n = 729`, and it **overstates the measured gap by 2.3×**
  (§5.5). Anything that quotes one of those two as if it were the other is wrong; the recommendation
  in §8 rests on the measured one.
- **The per-step inversion is a *bound*, not a measurement taken here.** §5.5 charges it from
  `docs/research/batch-inversion.md`'s measured Mersenne-31 plateau (one inversion ≈ 105
  multiplications pre-#160) and finds it accounts for 29% of the 2.3× gap. No inversion was timed in
  this work.
- **The first run of this benchmark silently lost `-C target-cpu=x86-64-v3`** (§5.5.1), because
  `.cargo/config.toml` is not inherited by a crate that merely depends on `zeebra` and the harness
  deliberately lives outside the worktree. `RUSTFLAGS` was never set — the flag was lost by *where*
  the build ran. All quoted figures are from the corrected build, and the cross-check against #312's
  independent order-1 458 figure (2.272 s against 2.404 s, 5.5%) is what makes that claim checkable.
- **Whether the specialization trap fires at all on the registered rows is unchecked** (§5.3). It
  needs `lc_y` of `cico_bivariate`'s outputs, in a file another agent owns this milestone.
- **The root-finding exponent 1.933 is fitted on two points** (§7). Every root-finding figure in §7.1
  and §7.2 inherits that, including the 5.63 h that §8 leans on. It is the weakest number in this
  document and the one most worth re-measuring — which is why §9 files it as its own issue.
- **The interpolation `O(S²)` law is derived, not fitted**, from one measured anchor at `S = 730`
  extrapolated across three orders of magnitude in `S`.
- **The `R = 7` build transient of ~1 TB is extrapolated** across one rung, from a mechanism that
  predicted `R = 6` to 0.7%.
- **Axis 1's 3–5× and axis 4's better parallel efficiency are both hypotheses**, from reading the
  code and from the 2 800× working-set drop respectively. Nothing in §8 depends on either value.
- **`ω = 2.81` is used for axis 5** because `resultant-elimination.md` and the FreeLunch paper both
  use it. Zeebra's dense linear algebra is `ω = 3`, which makes axis 5 *worse* than §6 computes.
- **Axis 5's crossover moved from `R ≈ 13` to `R ≈ 8.7`** once §5.5's measured 2.3× per-operation
  penalty for Euclid is charged (§6). That is the one place the measurement tightened a margin
  rather than leaving it alone, and it is still three rungs past `R = 7`. If a target ever lands at
  `R ≈ 9` with the build and tail stages solved, axis 5's deferral should be revisited — that is the
  named trigger in §9.
- **#312's fitted exponent is 2.9953 ± 0.0285, below 3.** Projections here use the cubic law, matching
  `determinant_core_ms`'s deliberate choice of the larger of the two, so the determinant figures are
  if anything slight over-estimates — which flatters axis 4 by at most a few percent.
