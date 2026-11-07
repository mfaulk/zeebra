# The first competitive baseline: where Zeebra leads, lags, and cannot be compared

Decision gate for #263, and the deliverable that decides which of H12–H17 (#268–#273) is worth
engineering effort. Every figure elsewhere in `docs/` is stated against Zeebra's own past; this is
the first statement of where Zeebra stands against other software on the same machine.

**Read §1 and §9 if you read nothing else.** §1 is the one place a reader can be misled, and §9 is
what this decided.

---

## 0. Conventions, before any number

- **Noise band: a difference under about 20% should not be read.** The convention
  `docs/research/pair-scheduling.md` established, and it is the band this machine's run-to-run
  variation actually occupies. Conclusions below rest on order-of-magnitude gaps and on exact
  structural counters, never on a 1.1x.
- **No cross-machine and no cross-concurrency ratio appears anywhere.** Where two figures came from
  different worker counts the fact is stated and no ratio is formed.
- Every measured row was taken under `tools/benchlock.sh`, whose overlapping `START..END` windows
  are the machine-checkable proof that two figures were *not* taken under the protocol.
- A **limit stop is a lower bound** and never a measurement; an **unsupported input has no time at
  all**. The five outcomes and what each licenses are §3 of
  `docs/research/external-comparison-protocol.md`, and
  `CompetitiveBoard::speedups` is the only place a ratio is computed.
- Zeebra runs in-process and gets **no process-startup charge**, where msolve's and Julia's wall
  times include theirs. That favours Zeebra, and it is now **measured rather than estimated**:

  > **Singular's process-startup floor on this machine is 36.0 ms.** Five sweep rows cluster at
  > 36.01, 36.04, 36.05, 36.07 and 36.08 ms across instances whose quotient dimensions differ by a
  > factor of 2 000 (9 to 16 384). A figure that constant across that range is not a computation.

  **The rule this gives, and it is used throughout §4a: where a comparand's wall time is within
  about 2x of its own startup floor, the row is not an engine comparison in either direction.**
  Such rows are recorded — they are what it costs to *ask* that engine, which is a real quantity —
  but no speedup is drawn from them. Four apparent Zeebra wins of 2.2x, 3.4x, 8.4x and **450x**
  turn out to be Singular starting up, and the 450x is the clearest warning in the whole report
  about reading a ratio without its denominator's floor.

### Pinned versions

| engine | version | how obtained |
|---|---|---|
| Zeebra | this tree, `cargo` release profile | in-process |
| msolve | 0.11.0 | source build, `/home/…/zeebra-ext` |
| Groebner.jl | 0.10.11 on Julia 1.11.7 | provisioned |
| Sagebrush | `86d9f1c7` | provisioned |
| Singular | 4.4.1, build 44105 | distribution |

---

## 1. The headline: Zeebra loses to msolve on order conversion, and the reason is the algorithm

The cleanest comparable measurement M25 produced. One machine, byte-identical generators (msolve is
fed the system from the same `instance.system::<N>()` the Zeebra rows use), both under `benchlock`,
**msolve on one core and Zeebra on eight**.

| row | msolve | Zeebra | wall ratio | msolve RSS | Zeebra RSS |
|---|---:|---:|---:|---:|---:|
| Anemoi `n5-fcico` | **1.81 s** | **63.71 s** | **35x** | 32 MB | 330 MB |
| Anemoi `n5-pcico` | **1.85 s** | **39.0 s** | **21x** | 34 MB | 216 MB |
| Anemoi `n6-pcico` | **353.88 s** | — | — | 635 MB | ~4.5 GB |

**Zeebra is roughly one and a half orders of magnitude behind msolve on this family.** A tighter
bound is not defensible from six rows.

**The conversion stage alone is ~30x** — 47.53 s against msolve's ~1.6 s of FGLM at `n5-fcico`.

### What may and may not be said about per-core cost

Zeebra's conversion is **single-threaded** (~1 CPU-second per wall second, observed), so for *that
stage* the wall and per-core ratios nearly coincide. A per-core figure of **~280x is defensible for
the conversion stage and for nothing else.** Quoting it for the whole solve would overstate the
result, because the basis stage is parallel and was given eight cores.

### Three caveats that travel with the row

1. **Everything is at `p = 65537`.** msolve refuses `p = 2^64 − 353` outright
   (`characteristic must be 0 or < 2^31`), so the comparison was taken at a 17-bit control prime.
   **Whether the deficit holds at 64-bit characteristic is unmeasured.** Zeebra's own conversion
   being characteristic-flat to 12% across a 47-bit prime range is *weak evidence* that it would,
   and that is an inference, not a measurement.
2. **Verified at `N = 4`, `N = 5`, and `N = 6` `PCICO` (msolve only).** Nothing extrapolates to
   `N = 7` or to `α ≠ 3`.
3. **Eight cores against one.** No per-core ratio is quoted for the end-to-end rows, for exactly
   that reason.

### A correction this report must not inherit

`anemoi.md` §8a.1 recorded an apparent **507x Zeebra advantage** over published Magma. #283 found
that the published 2 400x Anemoi conversion/basis ratio is mostly **Magma's generic finite-field
arithmetic at `p ≥ 2^32`**, not a property of the problem — the same ratio is 124.6 at
`p = 65537`. **That 507x is not a competitive lead and does not appear in this report as one.**
§8a.1 is marked superseded-in-part in #302.

---

## 2. The finding underneath the ratio: three engines, three different conversion algorithms

| engine | dominant conversion stage | share |
|---|---|---:|
| Zeebra | **lex walk / dependence test** | 82.8% (`FCICO`, `N = 5`) |
| Magma V2.26-2 | `Get rep mat` + **Keller-Gehrig spin** | 96.6% (`FCICO`, `N = 6`) |
| msolve 0.11.0 | **scalar sequence (Wiedemann)** | 349.52 s of 353.88 s (`PCICO`, `N = 6`) |

Zeebra does border reduction plus an `O(D³)` incremental-span dependence test; msolve runs a
Wiedemann scalar sequence; Magma spins a representation matrix.

> **A conversion ratio between any two of these three is not a measurement of FGLM.** They are not
> on the same cost curve.

This is worth more to the report than the ratio is, and it has two consequences:

- It is the sharpest case in the milestone for why §7.4 of the plan labels a stage attribution a
  **hypothesis** when the stages are not comparable. The 30x is a real, reproducible fact about two
  programs; it is *not* evidence that Zeebra's FGLM is 30x off the achievable, because the
  achievable here is a different algorithm.
- **It bears directly on #58**, which defers Wiedemann/Krylov methods. Wiedemann is precisely what
  msolve uses for the stage where Zeebra's measured deficit is largest. §9 revisits that.

---

## 3. Where Zeebra cannot be compared at all — reported as prominently as the wins and losses

These are **results**, not gaps in the work. Each is a statement about the state of the available
tools, and each would be invisible if the row were simply omitted.

### 3.1 The solution tasks have no comparand, at any field size

`Task::OneFiniteFieldSolution` and `Task::AllFiniteFieldSolutions` are **unsupported by all four
comparands**, now unanimous and each verified from source rather than inferred:

| engine | why |
|---|---|
| msolve | the operation is **absent from its source** (`main.c:96-97`); it returns a rational parametrization, not explicit finite-field points |
| Groebner.jl | ships no finite-field solver to drive |
| Sagebrush | ships no finite-field solver to drive |
| Singular | no route with conventions this project has verified; declared `Unsupported::Task` rather than guessed at |

**Those two columns are empty for every engine at every field size.** No tuning changes it. This is
the cleanest illustration of why `Unsupported` must be a separate outcome: folded into "failed", or
left as a missing row, the empty column would read as though Zeebra's solver had never been
compared because nobody got round to it — when in fact there is nothing to compare it against.

### 3.2 Two field ceilings, not one — and above the second, msolve does not terminate

| task | msolve bound | source |
|---|---|---|
| `ReducedGrobnerBasis` | `p < 2^31` | `iofiles.c:564` |
| **`UnivariateEliminant`** | **`p < 1515531529`** | `linalg-fglm.c:38` |

`corpus::REFERENCE_CHARACTERISTIC` is `2^31 − 1 = 2147483647`, which is **above the eliminant
ceiling**. So **msolve is a basis comparand on the corpus reference field and not an eliminant
one.**

And the failure above that ceiling is worse than a refusal. msolve's sparse-FGLM refuses
`p >= 1518500213` (`fglm_core.c:1385`), the `NULL` is laundered into the genericity signal
(`msolve.c:1740-1752`), and that reaches a `goto restart` loop with **no exit**:
`add_linear_form_to_input_system` has no failure path (`msolve.c:649`) and
`undo_variable_order_change` permanently returns 0 once a linear form exists (`msolve.c:482-484`).
Measured on katsura-5 over `GF(2^31 − 1)`: **25 353 retries and 1.37 M lines of output in 8 s,
never exiting.**

**Why this is a measurement-integrity problem and not a footnote.** A sweep that asked msolve for
an eliminant at the reference prime would hang a worker until the wall limit killed it, and the row
would read **`StoppedByLimit`** — which is *timing-adjacent* and wrong. The truth is
`Unsupported::Characteristic`. The sweep harness therefore **refuses to ask**
(`MSOLVE_ELIMINANT_CEILING` in `examples/competitive_sweep.rs`), which is the only way to guarantee
the row is never produced. The adapter declares the documented-safe `1515531529` rather than
msolve's own guard, because the 2 968 684-wide window between them runs with no accumulation
guarantee.

### 3.3 The corroboration bands — and the limit is usually corroboration, not representability

The capability boundary, derived from four engine ceilings rather than stated per family.
`corpus::corroboration` is the function and `corpus::ceilings` the constants, so a corrected
ceiling corrects every statement that depends on it.

| band | engines that reach it | corroboration |
|---|---|---|
| `p < 2^31` | msolve, Singular, Groebner.jl, Sagebrush | **four-way** |
| `2^31 ≤ p < 2^62` | Groebner.jl, Sagebrush | **two-way**, neither checkable against a third |
| `2^62 ≤ p < 2^64` | Groebner.jl only | **none** |
| 254/255-bit (BN254, BLS12-381 scalar) | none | none |

The ceilings: msolve `2^31` (`iofiles.c:564`), Singular `2^31`, Sagebrush `2^62` (its own gate,
`lib.rs:1552`), Groebner.jl `typemax(UInt64)` — measured computing correctly at `2^31 − 1`,
`2^32 − 5`, Goldilocks, `2^64 − 353` and `2^64 − 59`.

**Row 2 is the uncomfortable one, and for a sharper reason than "only two".** The differential
harness's whole argument for Singular as an oracle is that its `std` is Buchberger/slimgb lineage
and therefore *algorithmically* independent. **Two engines that agree prove less than two engines
that agree for different reasons** — and with exactly two, a disagreement says one of them is wrong
without saying which.

**Row 3 is where Anemoi's field sits**, at `2^64 − 353`. One engine reaches it, so a timing is
publishable and its invariants are checkable against that one engine — but nothing can
triangulate. Goldilocks is in the same band.

**Row 4 means Zeebra's widest fields are validated by its own cross-field agreement and by
`ark-ff` on the arithmetic, not by any Gröbner comparand.**

> **The distinction rows 3 and 4 draw is the one to take away, because the two have different
> fixes.** Row 4 is a *representability* limit and needs a **new** tool. Row 3 is a
> *corroboration* limit and needs a **second** tool at the same field — Sagebrush is the obvious
> candidate and its `2^62` gate is exactly what excludes it from Anemoi's prime.
>
> An earlier draft of this report collapsed both into "no comparand can represent this", which was
> wrong for row 3 and wrong in the expensive direction: it would have told a reader to wait for a
> new engine when what is needed is a second one at a field two engines nearly share.

### 3.4 Characteristic two is not yet comparable

No corpus rung is in `GF(2^k)` for `k > 1`, because two engines' default `GF(2^8)` need not be the
same ring: different defining polynomials give isomorphic but not identical representations, and a
basis compared element by element across them disagrees for no mathematical reason.
`SingularSolver::supports` returns `Unsupported::ExtensionField` rather than guessing. Until the
convention is established per engine, **there is no measured gap in characteristic two** — which
matters for #272, see §9.

---

## 4. Where Zeebra agrees: the correctness result that licenses every timing

All **seven** corpus ladder rungs — `katsura-4/5/6/7`, `cyclic-4/5/6` — agree **exactly** with
Zeebra's own F4 on **leading monomials and basis cardinality**, with each rung's digest asserted
against `corpus::ladder()`. **No disagreements.**

Two properties of that check are worth stating because they are what make it evidence:

- **Zeebra's F4 was the oracle, not Singular.** So none of the `dp`/`Dp` ordering traps or
  `simplify` conventions are in the loop.
- The comparison is on **invariants, not text**: the initial ideal and the cardinality, which are
  properties of the ideal and the order, so a different print order or sign convention cannot
  produce a false disagreement.

Quotient dimensions were additionally checked against **published** values rather than against a
previous run of this code — Katsura-n has `2^(n-1)` solutions and cyclic-5 has 70 — because an
engine agreeing with itself proves nothing.

### Two text-interface hazards, one closed and one still open

Both are the same shape, and it is the shape this milestone has been chasing: **a malformed render
that produces a well-formed answer to a different ideal.**

| hazard | status |
|---|---|
| `x1` is a **prefix** of `x10`, so a greedy tokenizer reads `x1*x10` as something else | **Closed for Zeebra and msolve.** Zeebra pinned at the 14-variable rung; msolve verified safe by construction (`store_exponent` splits on `*` and matches with full `strcmp`, never `strncmp`) and by measurement over 53 distinct degree-2 monomials in `x1..x14`. **Groebner.jl and the Sagebrush driver are still unverified.** |
| A generator naming an **undeclared** variable has that factor **silently dropped** — `iofiles.c:57-62` has no `else` branch, so `x*z-1` with only `x,y` declared reads as `x-1`, exit 0, `#invalid equations 0` | **Not reachable from this corpus**, which renders its own variable list — and now asserted rather than assumed (`test_every_identifier_in_every_rung_is_a_declared_variable`). The msolve adapter checks every identifier in `supports()`. |

The msolve prefix check works because distinct degree-2 monomials are pairwise non-dividing, so the
Gröbner basis *is* the generating set — which is why a set round-trip is a sound test there.

---

## 4a. Measured cross-library rows on the corpus — including a basis-stage loss

Zeebra against Singular 4.4.1, one machine, `taskset -c 0-7`, one worker, under `benchlock`, 60 s
wall limit, every row from `corpus::instance` so the generators are digest-identical. Singular's
startup floor is subtracted from no figure; the `startup share` column is what says whether a row
means anything about the engines (§0).

| row | task | Zeebra | Singular | wall ratio | startup share | verdict |
|---|---|---:|---:|---:|---:|---|
| **mq-random-10** | **basis** | **29 963 ms** | **7 291 ms** | **0.24x** | 0% | **Zeebra 4.11x slower** |
| **mq-random-10** | **conversion** | **30 605 ms** | **8 580 ms** | **0.28x** | 0% | **Zeebra 3.57x slower** |
| mq-planted-10 | conversion | 19.6 ms | 163.7 ms | 8.37x | 22% | Zeebra faster, startup-sensitive |
| poseidon-t2-rf4-rp0 | basis | 291 ms | 209 ms | 0.72x | 17% | Zeebra 1.39x slower |
| poseidon-t2-rf4-rp0 | conversion | 316 ms | 215 ms | 0.68x | 17% | Zeebra 1.47x slower |
| poseidon-t2-rf2-rp2 | basis | 118 ms | 87 ms | 0.74x | 41% | 1.35x, **startup-dominated** |
| mq-random-6 | basis | 25.3 ms | 56.4 ms | 2.23x | 64% | **not an engine comparison** |
| cyclic-6 | conversion | 15.3 ms | 51.3 ms | 3.35x | 70% | **not an engine comparison** |
| mq-planted-6 | basis | 0.08 ms | 36.0 ms | 450x | 100% | **not an engine comparison** |
| mq-random-14 | both | entry cap | 60 s wall | — | — | **different limits; no ratio** |

All quotient dimensions agreed on every completed row — 9, 25, 57, 64, 81, 156, 354, 1024, 16 384 —
which is the invariant check that licenses the timings at all (§5 of the protocol).

### The new result: a basis-stage loss on random MQ

**§6 previously recorded the basis stage as "not yet measured" cross-library. It is measured now,
and Zeebra loses: 4.11x to Singular on `mq-random-10`.** Singular's wall is 200x its startup floor
there, so startup is irrelevant and the ratio is clean.

This matters more than its size suggests, for two reasons:

- **Random MQ is the corpus family closest in shape to a cryptanalytic system** — dense, square,
  quadratic, no exploitable structure. A deficit here is a deficit on the problems Zeebra exists
  for, where the Anemoi loss in §1 was on a conversion-dominated row.
- **Zeebra loses on the basis and on the conversion by similar factors** (4.11x and 3.57x), and the
  conversion row is only 2% slower than the basis row in absolute terms — so on this instance the
  conversion is nearly free and the whole gap is in F4. That is a *different* gap from §1's, where
  the conversion was 75% of the solve.

So there are now **two** measured cross-library deficits with different locations, and §6's gap map
is revised accordingly.

### The capability finding: a stale FGLM default, revealed by the wider corpus

`mq-planted-14` has a **16 384-dimensional** quotient. `FglmOptions::default()` caps
`max_quotient_dimension` at **4 096**, and its documented rationale is that 4 096 is "26x the
largest quotient dimension in the benchmark corpus, which is cyclic-6's 156". The corpus has since
grown a rung 105x over that cap, so **the default is now mis-set relative to the corpus it
guards.**

Singular converts the same instance in 45.8 s using 10.4 GB, so the problem is solvable and
Zeebra's refusal is a self-imposed bound rather than an inability. The refusal itself is **correct
behaviour** — a refused budget is not a wrong answer — and raising the cap to 32 768 lets the rung
through (`test_raising_the_budget_lets_the_same_rung_through`, `#[ignore]`d for cost).

Two separate actions fall out, and only the first is a defect:

1. **The row was being recorded as `Failed`.** A declared budget is a **limit stop**, and putting
   it in the bucket reserved for an engine that broke is the exact confusion this contract exists
   to prevent — it also makes the row eligible for a ratio, which a limit stop never is. Fixed;
   every `FglmError` resource variant now maps to `StoppedByLimit`, `PositiveDimensional` to
   `Unsupported`, and only the genuine errors to `Failed`.
2. **The default should be revisited** against the corpus it now has to cover. That is a decision
   for whoever owns `FglmOptions`, not a defect — the figure was correct for the corpus it was
   chosen against.

## 5. Zeebra's own stage split, and the correction #269 was built on

`examples/f4_profile recommended`, milliseconds, from `MILESTONE-F4-OPTIMIZATION.md` §8.5.

| system | order | total | symbolic | construction | elimination | extraction | interreduction |
|---|---|---|---|---|---|---|---|
| cyclic-5 | lex | 3.14 | 0.65 | **1.48** | 0.37 | 0.09 | 0.35 |
| katsura-5 | lex | 0.88 | 0.12 | **0.35** | 0.09 | 0.06 | 0.17 |
| katsura-6 | lex | 19.53 | 4.42 | **9.33** | 1.28 | 0.99 | 2.33 |
| katsura-6 | grlex | 4.40 | 0.30 | 1.11 | 0.77 | 0.11 | **1.98** |
| katsura-6 | grevlex | 3.77 | 0.31 | 1.14 | 0.80 | 0.08 | **1.33** |
| katsura-7 | grlex | 46.72 | 2.58 | 6.21 | 8.00 | 0.63 | **28.71** |
| katsura-7 | grevlex | 32.13 | 1.64 | 5.53 | 7.12 | 0.40 | **16.90** |

> ### #269's premise is false, and it is the premise the issue's title states
>
> #269 is titled "F4 elimination kernels — **the 65–88% stage**". That figure was true **at M16-0**
> and has not been true since. Elimination is now **7%–22%** of every instance in the table:
> 6.6% on katsura-6 lex, 22.2% on katsura-7 grevlex.
>
> It was corrected on the issue, including that the `la_ff_small_prime.c` it cites **does not
> exist**.

**The Amdahl ceiling this puts on #269.** Even an *infinitely fast* elimination kernel buys:

| instance | elimination share | ceiling if elimination became free |
|---|---:|---:|
| katsura-6 lex | 6.6% | **1.07x** |
| katsura-7 grlex | 17.1% | **1.21x** |
| katsura-7 grevlex | 22.2% | **1.29x** |

Every one of those is at or barely above the 20% noise band. **No kernel work on elimination can
produce a readable end-to-end result on these instances.**

### Where the cost actually is

| stage | share | instance | ceiling if it became free |
|---|---:|---|---:|
| **Interreduction** | **61.5%** | katsura-7 grlex (28.71 of 46.72 ms) | **2.59x** |
| Interreduction | 52.6% | katsura-7 grevlex (16.90 of 32.13) | 2.11x |
| **Matrix construction** | **47.8%** | katsura-6 lex (9.33 of 19.53) | **1.92x** |
| Matrix construction | 47.1% | cyclic-5 lex (1.48 of 3.14) | 1.89x |

Both are consequences of succeeding elsewhere — the pair criteria replaced 59 large matrices with
107 small ones, and construction's per-matrix cost (the monomial-to-column `HashMap`, the sort)
does not shrink with the matrix. Their best ceilings are **2.59x** and **1.92x**, which are worth
chasing where elimination's 1.07x is not.

---

## 6. The per-stage gap map, ranked by absolute time lost

The report's central table. "Measured against" names what the gap was measured against, because a
gap with no comparand is a hypothesis.

| rank | stage | absolute time lost | measured against | is the comparand on the same cost curve? |
|---:|---|---:|---|---|
| **1** | **Order conversion / FGLM** | **~46 s** on one row (47.53 s against ~1.6 s) | msolve 0.11.0, same machine, `p = 65537` | **No** — lex walk against Wiedemann. §2. |
| **2** | **Basis (F4), cross-library** | **~22.7 s** on one row (29.96 s against 7.29 s) | **Singular 4.4.1, same machine, `p = 2^31 − 1`** | **Partly** — both compute a reduced grevlex basis, but Singular's `std` is Buchberger/slimgb lineage, not F4. §4a. |
| **3** | Interreduction | 28.71 ms of 46.72 (katsura-7 grlex) | Zeebra's own past only | n/a — internal |
| **4** | Matrix construction | 9.33 ms of 19.53 (katsura-6 lex) | Zeebra's own past only | n/a — internal |
| **5** | Elimination | 8.00 ms of 46.72 | Zeebra's own past only | n/a — internal |

**The honest shape of this table is that ranks 1 and 2 dwarf everything below them by three orders
of magnitude, and neither has a comparand on the same cost curve.** Ranks 3–5 are internal profile
shares with no external comparand at all.

Rank 2 is new since the first draft, and it moves the conclusion: there are now **two** measured
cross-library deficits, in **different stages**, on **different families**. §1's is conversion on a
structured CICO row; §4a's is the basis on dense random MQ, where the conversion is nearly free.
A single explanation is unlikely to cover both, and §9 says so.

---

## 6a. The Amdahl screen, applied to every candidate

An issue proposing to speed a stage can be bounded before any implementation question arises:
if the stage became **free**, the end-to-end gain is `total / (total − stage)`. Where that ceiling
sits at or inside the 20% noise band, **no implementation of any quality can produce a readable
result**, and the issue is settled on arithmetic rather than on opinion.

Applied to all five H-series items that target a stage, from §5's profile. The screen is only
credible if it runs on the favoured candidate too, so #268 is in the table.

| issue | target stage | best share | **ceiling** | verdict |
|---|---|---:|---:|---|
| **#268** H12 | interreduction | 61.5% | **2.59x** | **clears the band by 13x** |
| **#268** H12 | matrix construction | 47.8% | **1.92x** | **clears by 4.6x** |
| #269 H13 | elimination | 22.2% | 1.28x | **barely clears, 1.07x typical** |
| #271 H15 | extraction (F4 half) | 5.1% | **1.053x** | **fails; 1.01x typical** |
| #272 H16 | linear algebra in char 2 | — | **not computable** | **no char-2 profile exists** |
| #273 H17 | — | — | **not applicable** | bounded by route spread, not stage share |

Three things this screen produces that a discussion of implementations would not:

- **#271 is settled, not merely unpromising.** An infinitely fast extraction stage is
  unmeasurable on every instance in the profile. Its *univariate-factoring* half is a different
  claim the screen does not reach, and §9 keeps the two apart.
- **#272 is the one place the screen cannot run**, and that is the finding. Extrapolating from the
  prime-field split would be the same error #269 is being deprioritized for. One `GF(2)` profile
  decides it, and needs no comparand.
- **#273 is bounded by the wrong quantity if a stage share is used at all.** Selection does not
  make a stage faster; it picks a route. The measured route spread is **70x** — planted-8's lex
  basis takes F4 0.04 ms directly against a 2.8 ms conversion
  (`MILESTONE-FGLM-SCALABILITY.md` §8.5) — against the best stage ceiling anywhere of 2.59x.

**A ceiling bounds the conceivable, not the achievable.** That asymmetry is why it is decisive
against #269 and #271, where even the free case is unmeasurable, and only permissive for #268,
where the achievable depends on a per-term factor nobody has measured. #268's acceptance test is
therefore a before/after on a corpus rung, not a forecast from this table.

## 7. The six-axis ranking

Per the plan's §7.4, candidates are ranked on **six axes, not raw ratios**: absolute cost, measured
gap, expected benefit, implementation difficulty, effect on maximum solvable size, and
applicability to cryptanalytic systems. A raw ratio is excluded deliberately — §2 is the reason.

Scores are `+` favourable, `0` neutral, `−` unfavourable, `?` unmeasured.

| candidate | absolute cost | measured gap | expected benefit | difficulty | max solvable size | cryptanalytic applicability |
|---|---|---|---|---|---|---|
| **Krylov/Wiedemann conversion** (#58, currently deferred) | **+ ~46 s/row** | **+ 30x, measured** | **+ 2.59x–30x** | **− high** | **+** large: conversion is the wall | **+** CICO rows are conversion-dominated |
| **#268 H12** compact representations | + 28.71 ms (interreduction) | ? none external | + up to 2.59x | 0 moderate | + fewer bytes per entry | + MQ and CICO both |
| **#273 H17** adaptive strategy selection | 0 varies | ? none external | 0 route-dependent | **+ low** — extends existing planner | 0 | + picks the route per instance |
| **#271 H15** modular composition / factoring | 0 extraction is 0.4–1 ms | ? none external | − extraction is already small | − high | 0 | 0 |
| **#269 H13** elimination kernels | **− 8 ms, 7–22%** | **− premise false** | **− ceiling 1.07x–1.29x** | − high | 0 | 0 |
| **#270 H14** per-field-width arithmetic | ? | **− premise undermined** | **− see below** | − high | 0 | 0 |
| **#272 H16** bit-packed `GF(2)`/`GF(2^e)` | ? | **? no char-2 rung exists** | ? | − high | ? | + if char 2 matters |

### The evidence against #270, which is new and decisive

#270's premise is that **per-field-width specialization is where msolve's advantage lies.** Two
facts from the msolve source study say the gap it reasons from does not exist at the fields being
compared:

1. **msolve's delayed reduction is active only below `2^18`.** At Zeebra's benchmark prime msolve
   runs a **per-MAC correction** — so whatever its narrow per-bitwidth kernels gain is **invisible
   on the instances being compared.**
2. **All three of msolve's kernels use `int64_t`.** So the narrow kernels buy **bytes and SIMD
   lanes, not accumulator headroom** — which is a different and much smaller claim than the one
   #270 is scoped around.

---

## 8. Acceptance against #263's own criteria

| criterion | status |
|---|---|
| ≥3 external tools | **Partially met, with reasons.** msolve measured (§1); **Singular measured on 19 corpus rungs across both tasks (§4a)**. Groebner.jl and Sagebrush are now adapted and wired into the sweep, but their four-engine run is **queued behind a 90-minute reproduction on `benchlock`** — the serialization protocol working, not failing. |
| ≥6 families | **Corpus has six** (`katsura`, `cyclic`, `mq-random`, `mq-planted`, `poseidon`, `anemoi`); cross-library **agreement** on seven rungs of two of them against Zeebra's F4 (§4) **plus quotient-dimension agreement on every completed Singular row across all six** (§4a); cross-library **timing** on `anemoi` (§1) and on `mq-random`, `mq-planted` and `poseidon` (§4a). |
| every row verified or classified unverified, method named | **Met.** §4 names the method (invariant agreement against Zeebra's F4, dimensions against published values). §1's rows are verified at `N = 4, 5, 6`. |
| failure stages and limits recorded for incomplete runs | **Met** by construction: `StoppedByLimit` carries the limit and `Unsupported` the missing capability, and neither is timing evidence. |
| no cross-machine or cross-concurrency ratio | **Met.** §1 states 8-core against 1-core and quotes **no** per-core ratio for the end-to-end rows; the per-core figure is restricted to the single-threaded conversion stage. |
| recommendation for each H12–H17, issue updated | §9, and the issues updated. |

**What is missing and why.** The **four-engine** sweep. The basis-stage number §8 previously listed
as missing has been taken against Singular (§4a) and produced the report's second measured deficit;
what remains is msolve, Groebner.jl and Sagebrush on the same rungs, which is a lock-queue wait
rather than an engineering gap. The harness runs all four.

---

## 9. What this decided

| question | answer |
|---|---|
| Where does Zeebra lag by more than the noise band? | **Two places, measured.** Order conversion, ~30x against msolve on Anemoi `N = 5` at `p = 65537` (§1). And the **basis stage, 4.11x against Singular** on `mq-random-10` at `p = 2^31 − 1` (§4a) — new, and on the family closest in shape to a cryptanalytic system. |
| Is that gap in elimination, symbolic preprocessing, conversion, or extraction? | **It depends on the family, which is itself the finding.** On Anemoi it is conversion — 82.8% of Zeebra's conversion is the lex walk and dependence test. On `mq-random-10` the conversion is nearly free (30.6 s against a 30.0 s basis) and **the whole gap is in F4**. One explanation is unlikely to cover both. |
| Is it a tuning gap or an algorithm gap? | **Algorithm.** Zeebra walks and tests dependence in `O(D³)`; msolve runs a Wiedemann scalar sequence; Magma spins a representation matrix. **A conversion ratio between any two of the three is not a measurement of FGLM.** |
| Does Zeebra's measured 65–88% elimination share hold? | **No, and it no longer holds for Zeebra either.** It is **7%–22%** (§5). The figure in #269's title is from M16-0 and was superseded by M16's own success. |
| Does the per-field-width hypothesis survive? | **No.** msolve's delayed reduction is active only below `2^18`, so it is inactive at the compared fields, and all three of its kernels use `int64_t` — narrow kernels buy lanes, not headroom. |
| Which instances does Zeebra solve that no comparand does, and is that capability or performance? | **Capability, in four distinct ways** (§3.3): the solution tasks (no comparand at any size); `2^31`–`2^62` (two engines, neither checkable against a third); `2^62`–`2^64`, where Anemoi and Goldilocks sit (**one** engine — publishable but uncorroborated); and 254/255-bit (none at all). None is a speedup and none is reported as one. **Only the last is a representability limit; the middle two are corroboration limits, and they have a different fix.** |
| Do the external anchors agree in rank order? | **Not assessed.** #199's Magma page and Sagebrush's `bench/magma-scoreboard/` are cross-machine, and §0 forbids a cross-machine ratio. Deliberately left open rather than answered weakly. |
| Does Zeebra have a capability limit a comparand does not? | **Yes, one, and it is self-imposed.** `FglmOptions`'s default caps the quotient dimension at 4 096, chosen when the corpus's largest was 156; the corpus now has a 16 384-dimensional rung that Singular converts in 45.8 s and 10.4 GB. The refusal is correct behaviour and the default is simply stale (§4a). |
| **Should H12–H17 proceed as scoped?** | **No. The measurement points at a lever the H-series does not contain — and now at a second one it partly does.** |

### The conclusion that matters

**H12–H17 were scoped before the measurement, and the measurement says the largest lever is not
among them.** The largest measured cross-library gap is in order conversion, and the candidate that
addresses it is **#58** — Wiedemann/Krylov — which is currently *deferred*. Meanwhile the two
H-series items with the strongest a-priori stories, #269 and #270, both rest on premises this
report falsifies.

**The second measured gap partly rehabilitates the H-series, and #268 specifically.** The 4.11x
basis loss on `mq-random-10` is in F4 itself, and #268's two target stages — interreduction and
matrix construction — are F4 stages with ceilings of 2.59x and 1.92x. That is the right order of
magnitude to explain a 4.11x if both contribute, which is the first external evidence any H-series
item has had. It is **not** confirmation: the stage split for `mq-random-10` has not been profiled,
and §6a's ceilings come from katsura and cyclic. **Profiling `mq-random-10`'s stage split is now the
single highest-value cheap measurement available**, because it would either point #268 at a
measured external gap or rule it out.

### Recommendations, per issue

| issue | recommendation | reason |
|---|---|---|
| **#58** (Krylov/Wiedemann) | **Reopen the FGLM half for measurement**, as "the measured conversion gap is worth a Krylov route" and **not** as "sparse-FGLM would be 30x faster". Highest-value candidate in the set. | It is the algorithm msolve uses for the stage where Zeebra's only measured cross-library deficit lies (~46 s on one row, ~30x). #58 deferred it on a named trigger rather than a judgement that the idea was bad, and a measured gap against a maintained implementation is the trigger. **But see §9a: the 30x does not transfer to a prediction, and `MILESTONE-FGLM-SCALABILITY.md` §8.5's three measurements still stand.** |
| **#268 H12** compact representations | **Raise to the top of the H-series**, and profile `mq-random-10` first. | Addresses interreduction (61%) and matrix construction (48%) — the two largest *internal* stages, ceilings 2.59x and 1.92x. §4a's 4.11x basis loss is the first **external** gap any H-series item could plausibly explain, and 2.59x × 1.92x spans it — but the stage split of the losing instance is unprofiled, so that is a hypothesis and the profile is what tests it. |
| **#273 H17** adaptive strategy | **Keep, at low cost.** | Extends the existing planner. §6a: its benefit is bounded by **route spread, 70x measured** on planted-8, not by any stage share — against a best stage ceiling of 2.59x. `fglm::shape` already ships a tested detector that is deliberately unwired, so this is connecting two existing pieces. |
| **#271 H15** modular composition | **Defer** — the F4 half is **settled**. | Extraction's ceiling is **1.013x–1.053x** (§6a): an infinitely fast stage is unmeasurable on every profiled instance. The univariate-factoring half is a separate claim the screen does not reach, and the large univariate win was already taken — `graeffe-root-finding.md` has one root at degree `3^13` in 3.1 s against an extrapolated 57 hours. |
| **#269 H13** elimination kernels | **Deprioritize, and correct the title.** | The 65–88% premise is false; the stage is 7–22%, giving an Amdahl ceiling of 1.07x–1.29x, at or inside the noise band. The cited `la_ff_small_prime.c` does not exist. |
| **#270 H14** per-field-width arithmetic | **Deprioritize; close unless re-scoped.** | msolve's delayed reduction is inactive at the compared fields and all its kernels are `int64_t`. The advantage #270 is scoped to chase is not present in the comparand at these field sizes. |
| **#272 H16** bit-packed `GF(2)`/`GF(2^e)` | **Hold, and take the `GF(2)` profile first.** | Not refuted — **unmeasurable**: §6a's screen needs a profile and there is no char-2 one. `GF(2)` is a prime field and could be profiled today; only the `GF(2^e)` half is blocked on the defining-polynomial convention (§3.4). One profile converts this from held to decided. |

## 9a. The limit on the #58 recommendation

The claim most likely to be misread, so it is stated separately rather than left in a table cell.

**Reopen #58 as "the measured conversion gap is worth a Krylov route". Not as "sparse-FGLM would
be 30x faster."** The second does not follow: §2's three engines use three different algorithms, so
the ~30x is a measurement of *Zeebra's conversion against msolve's* on one family at one prime, and
the comparand's cost curve is not one a Zeebra Krylov route would inherit.

`MILESTONE-FGLM-SCALABILITY.md` §8.5's three measurements are why #58 said no the first time, and
**nothing here refutes any of them**:

1. Where conversion is the only route, the cost is not the dependence algorithm — **96% of
   katsura-7's conversion is border reduction**, which sparse FGLM does not touch.
2. Where the dense blocks dominate, the ideal is **not in shape position** — planted-10's blocks
   are 54x its operators, and its last variable has a degree-4 minimal polynomial in a
   1024-dimensional quotient.
3. On those systems one should not be converting at all — planted-8's lex basis takes F4 **0.04 ms**
   directly against a 2.8 ms conversion.

What #263 adds is one new fact about **a family §8.5 did not measure**: on Anemoi CICO there is now
a maintained implementation ~30x faster at this stage on the same machine, and its route is
Wiedemann. That is why it does not contradict §8.5.

**The cheap question a reopened scope should answer first.** §8.5 measured 96% border reduction on
katsura-7, where a Krylov route would buy nothing; §1's split says **82.8% of the Anemoi `N = 5`
conversion is the lex walk and dependence test** — the opposite split, and what makes the family
different. Confirming that on a second Anemoi rung is one row, and it decides whether the rest of
the work has a target.

§8.5's answer 4 also still holds: a Wiedemann variant choosing a random linear form could reuse the
existing `O(N D)` verification **unchanged**, so it could be exposed as certified rather than
conjectural. That is the one unambiguously reusable result of the M18 spike and it lowers the cost
of #58 more than anything else in it.

**#58's won't-do for F4 is untouched** and rests on reasoning nothing here disturbs.

### Four follow-ups this report generates

- **Profile `mq-random-10`'s stage split.** The highest-value cheap measurement in the report:
  Zeebra loses 4.11x there and §6a's stage ceilings are all from katsura and cyclic, so nobody
  knows whether #268's targets are where that particular loss lives.

- **Verify the `x1`/`x10` prefix handling in Groebner.jl and the Sagebrush driver**, as #311 did for
  msolve. Both are unverified, and the failure is invisible from the engine's side.
- **Settle the `GF(2^k)` defining-polynomial convention per engine**, which is what blocks both a
  char-2 corpus rung and any decision on #272.
- **Find a second engine above `2^62`.** That band currently has one, so every figure Zeebra takes
  at Goldilocks or at Anemoi's `2^64 − 353` is uncorroborated by construction. This is the cheapest
  available improvement to the *trustworthiness* of the widest rows, as distinct from their speed,
  and it is a different task from finding an engine for the 254/255-bit fields.

### A note on Sagebrush's maturity, which is separate from its ceiling

Sagebrush **disagreed with nothing** — term-for-term on every family tried, including at a 62-bit
prime. But it is five weeks old, nothing is versioned, it has six F4 tests, and no oracle run in
its own repository exercises the elimination. So it is reportable **with its SHA** and **never as a
speedup denominator**. That is a maturity judgement, not a correctness one, and it is independent
of the `2^62` ceiling that keeps it out of Anemoi's band.

---

## 10. Reproducing

```sh
# The corpus, its digests, and the equivalence evidence for each family
cargo test --lib external::corpus

# What the sweep would run
cargo run --release --example competitive_sweep -- --list

# One measured row: one process, so its peak RSS is attributable to it
ZEEBRA_MACHINE=workstation ZEEBRA_AFFINITY=0-7 \
  tools/benchlock.sh runner taskset -c 0-7 \
  cargo run --release --example competitive_sweep -- \
    --row katsura-6 --task reduced-grobner-basis --measure --wall 600 --write

# Render the board from its accumulated history
cargo run --release --example competitive -- --write
```

`--measure` without `--row` is refused: a peak-RSS figure is only attributable in a process that
runs one row, and a harness that silently dropped the figure would make a sweep look like a
measurement.
