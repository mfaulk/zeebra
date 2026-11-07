# The 348x against Groebner.jl, decomposed: three factors, and only one of them is §6's

Measurement record for #447, following #265's source study
(`docs/research/groebner-jl-implementation.md`) and #349's stage split
(`docs/research/competitive-baseline.md` §6b). **#265 is not reopened and nothing here re-reads
Groebner.jl for ideas**; what is new is a *comparand* for the counters §6's hypotheses were ranked
against, and the counters say the ranking was aimed at the wrong column.

Pinned: Zeebra at `25e10fe`, Groebner.jl **0.10.11** on **Julia 1.11.7** with AbstractAlgebra
0.50.5, from `tools/external/provision.sh`'s prefix. Groebner.jl `path:line` citations are relative
to the package root `julia-depot/packages/Groebner/Aqs1M`.

**Licensing, restated because this note quotes its mechanisms.** Groebner.jl is GPL-2.0, is
self-declaredly adapted from GPL-2.0-or-later msolve, and embeds GPL-3.0-or-later code
(`groebner-jl-implementation.md` §1, §1.1). **Algorithmic reference only; no line of it may enter
this MIT crate.** It is run as a separate process and nothing is copied
(`docs/research/external-provenance-policy.md` §7).

**Machine caveat, once, applying to every duration below.** Two other agents were building
concurrently throughout. Every timing was taken under `tools/benchlock.sh` pinned to cores 0-7,
which excludes other *measurements* and does nothing about shared L3 and memory bandwidth. So the
durations here are **shared-machine durations** and are not clean. They are used for ratios between
figures taken minutes apart on the same box, which is the use that survives contention; none of
them is a record and none should be promoted to one. The **counts** are not affected at all — #349
established they are deterministic across runs, and this note re-confirms it.

---

## 0. The answer to item 1, which decides the rest

> **Same work. Not a different algorithm.** On `mq-random-10` grevlex at the same identity digest
> `72d0ad315fc25409…`, Zeebra and Groebner.jl reach **10 matrix batches**, **1 777 against 1 787
> selected critical pairs** (0.6% apart), **247 basis elements**, **quotient dimension 354**. The
> only count that differs materially is reducer rows — Zeebra 84 645 against 47 464, a factor of
> **1.78** — and Groebner.jl's own trace says only 41.5% of its own reducer rows were ever used.
>
> So the issue's first candidate shape — "Zeebra is doing asymptotically more work, and no
> data-structure change closes this" — is **dead**. Zeebra does the same work, 1.78x more reducer
> rows, and takes 344x longer.

And the headline this produces, which is a reversal of the issue's own premise:

> The 348x is **fully accounted for**, as a product of three independently measured factors:
>
> | factor | size | what it is | reachable through §6? |
> |---|---:|---|---|
> | A | **4.89x** | Groebner.jl's default *randomized* linear algebra, which Zeebra declines by policy (§6.6) | **No — by design.** §6.6 is right and its magnitude was understated ~20x |
> | B | **5.03x** | Zeebra's final interreduction done by **iterated division** where Groebner.jl does **one Macaulay matrix** | **No — §6 contains no such hypothesis.** This is the finding |
> | C | **14.0x** | a near-uniform per-operation constant across *every* remaining stage (11.6x–25.5x) | **Yes — this is what §6.2 and §6.3 are actually aimed at** |
>
> Where each comes from, so the product is checkable: **A** is 424.615 ms deterministic against
> 86.842 ms randomized, same process, warm (§5). **B** is 29 912.76 ms against the 5 945.7 ms that
> remains if interreduction were done Groebner.jl's way at *Zeebra's own* per-operation constant —
> 1.74 ms × 97.1 ≈ 169 ms in place of 24 136.08 ms (§4). **C** is that 5 945.7 ms against the 424.615
> ms deterministic comparand, and §3's per-stage ratios confirm it independently at 11.6x–25.5x.
>
> 4.89 × 5.03 × 14.0 = **344x**, against a measured 344x. The issue's "most of a two-orders-of-magnitude
> gap unexplained" was unexplained because the comparison was against the *randomized* figure and
> because interreduction was being screened as a stage when the thing wrong with it is an algorithm.

§6's stated priority order — §6.1 first, aimed at 48% of katsura-6 **lex** construction — targets
**3.43%** of the instance that loses, a ceiling of **1.04x**. The order is wrong for the comparison,
exactly as the issue suspected, and §7 of the study should be read as superseded by §5 below.

---

## 1. How each side was counted

Nothing new was built on the Zeebra side. `examples/f4_profile -- mq` is #349's instrument,
unchanged: it builds `mq-random-10` through `grobner::external::instance` at
`REFERENCE_CHARACTERISTIC` under grevlex, **asserts the identity digest**, and profiles under
`F4Options::default()` with `measure_stages` on.

Two small additions make the two sides comparable rather than merely adjacent:

* `examples/f4_profile -- mq-instance` prints that instance's `Instance::canonical` — the bytes the
  digest is taken over — and the digest itself. No measurement.
* `tools/external/groebner-jl-counts.jl` reads that text, rebuilds the ideal in AbstractAlgebra with
  the **same ring, same `internal_ordering`, same `ordering=` and same `tasks=`** as
  `src/grobner/external/groebner_jl.rs`'s generated script, including the two-element proxy warm-up,
  and echoes every generator back before computing anything. It then reports Groebner.jl's own
  counters.

Two Groebner.jl facilities do the reporting, and neither needed a patched build:

1. **`groebner_learn` records the counts.** `f4_learn!` (`src/f4/learn_apply.jl:156-199`) is
   `f4!` (`src/f4/f4.jl:415-452`) with a recorder attached — same `f4_update!`, same
   `f4_select_critical_pairs!`, same `f4_symbolic_preprocessing!`, same termination, plus
   `push!(trace.critical_pair_sequence, (degree_i, npairs_i))` at `:174`. Its `Trace` carries
   `matrix_infos` as `(nup, nlow, ncols)` per iteration and `Base.show` prints an "F4 statistics"
   block (`src/f4/trace.jl:24`, `:225-258`). **`matrix_infos` has one entry more than the loop has
   iterations**, the last being the final-interreduction matrix — which is how `:487` recovers the
   iteration count by subtracting one.
2. **`Groebner._TIMER` gives a per-stage split, and ships disabled.**
   `TimerOutputs.disable_timer!(_TIMER)` at `src/Groebner.jl:82`, with `@timeit _TIMER` on
   `f4!`, `f4_reduction!`, `f4_symbolic_preprocessing!`, `f4_select_critical_pairs!`, `f4_update!`
   and `f4_autoreduce!`. `enable_timer!` is a runtime flag, so the stages can be read without
   recompiling anything. **This is more stage information than any adapter in this repository
   currently collects, and it is a direct answer to one of #428's tasks** — see §6.

What `groebner_learn` cannot witness is the *randomized* linear algebra: the learn backend is
deterministic (`backend_learn_apply.jl`). That does not affect any count — the pairset, the
criteria, symbolic preprocessing and the matrix shapes are all upstream of the kernel — and it is
why factor A had to be measured separately, by passing `linalg=:deterministic` to `groebner`.

---

## 2. The counts, side by side

| quantity | Zeebra | Groebner.jl | ratio |
|---|---:|---:|---:|
| matrix batches / F4 iterations | **10** | **10** | 1.00 |
| critical pairs reaching a matrix | **1 777** | 1 775 low-rows, 1 787 selected | 1.00 |
| matrices built, including the final interreduction | 10 + 1 | **11** | 1.00 |
| reducer (upper) rows, summed | **84 645** | **47 464** (41.5% ever used) | **1.78** |
| total matrix rows | 86 422 | 49 239 | 1.75 |
| basis elements | **247** | **247** | 1.00 |
| quotient dimension | **354** | **354** | 1.00 |
| pair-degree progression | *not reported by the instrument* | 2,3,4,5,6,6,6,7,7,8 | — |

Zeebra's figures: `examples/f4_profile -- mq`, `batches` / `pairs` / `basis` and the `reducers`
diagnostic. Groebner.jl's: the trace block and `@matrix`/`@pairbatch` lines.

**On the two pair counts.** 1 787 is what `f4_select_critical_pairs!` took off the pairset; 1 775 of
those became matrix lower rows. Zeebra's `pairs_reduced` is "pairs that reached a matrix" and is
1 777. The two engines use different pruning implementations — Zeebra's `PairCriteria`, which
discarded 31 893 pairs here with the chain criterion contributing 0.000%, against Gebauer–Möller at
`src/f4/basis.jl` — and they arrive at the **same pair set to within 0.6%**. That is a stronger
agreement than either side's documentation claims.

**On the 1.78x in reducer rows.** This is the one place Zeebra demonstrably does more work, and it
is a constant and not an exponent. Groebner.jl's own trace reports 41.46% of its upper rows
"useful", so the waste is not one-sided; Zeebra has no comparable counter, and adding one is the
measurement that would turn 1.78x into an attributed difference. Recorded as **not settled**. Note
also that 1.78x is a sub-factor *inside* factor C, not a fourth factor: it is already paid for
inside the stage times of §3.

**The matrix shapes, for scale.** Groebner.jl's eleven matrices, `(nup, nlow, ncols)`:

```
(9,5,40) (68,14,178) (385,72,620) (1166,230,1530) (3241,444,3662) (4847,169,5261)
(4786,57,5161) (10248,733,10612) (9419,48,9773) (13045,3,13399)      ← the loop
(250,0,604)                                                          ← f4_autoreduce!
```

The last line is §4's whole argument in one tuple: **the final interreduction of this ideal is a
250 × 604 sparse echelon.** Zeebra spends 24.1 seconds on it.

---

## 3. The per-stage split, both engines, same box, same lock

Zeebra, `F4Options::default()` with `measure_stages`, `taskset -c 0-7`, one worker — a confirming
re-measure of #349 taken in the same session as the Groebner.jl figures below, so the pairing is as
matched as this machine allows:

| total/ms | symbolic | construction | elimination | extraction | **interreduction** | other |
|---:|---:|---:|---:|---:|---:|---:|
| 29 912.76 | 403.16 | 1 025.21 | 4 159.19 | 108.04 | **24 136.08** | 81.07 |
| share | **1.35%** | **3.43%** | **13.90%** | **0.36%** | **80.69%** | **0.27%** |

Identical in shape to #349's three runs (80.4%, 13.9%, 3.5%, 1.4%). Counts identical. The stage
shares on the losing instance are therefore now measured four times and have not moved.

Groebner.jl, `_TIMER` enabled, same lock and affinity, `-t1`, defaults (so *randomized* linear
algebra). The run's wall was 89.16 ms against 86.84 ms with the timer off, so timer overhead is
~2.7% and the shares are what to read:

| section | ncalls | time | % of `f4!` |
|---|---:|---:|---:|
| `f4!` | 1 | **79.0 ms** | 100% |
| ├─ `f4_reduction!` | 10 | 54.5 ms | 61.7% |
| ├─ `f4_symbolic_preprocessing!` | 10 | 15.8 ms | 17.9% |
| ├─ `f4_select_critical_pairs!` | 10 | 4.16 ms | 4.7% |
| ├─ `f4_update!` (Gebauer–Möller) | 11 | 2.80 ms | 3.2% |
| └─ **`f4_autoreduce!`** | 1 | **1.74 ms** | **2.0%** |
| `io_`/`ir_convert_*` (AbstractAlgebra ↔ internal) | 4 | 9.33 ms | *outside `f4!`* |

`f4_reduction!` (`src/f4/f4.jl:46`) is the column map, the row sort, `linalg_main!` and
`matrix_convert_rows_to_basis_elements!` — so it is Zeebra's construction + elimination +
extraction in one section. That gives four paired stages:

| stage | Zeebra | Groebner.jl | ratio |
|---|---:|---:|---:|
| symbolic preprocessing | 403.16 ms | 15.8 ms | **25.5x** |
| construction + elimination + extraction | 5 292.44 ms | 54.5 ms | **97.1x** |
| pair selection + basis bookkeeping | 81.07 ms | 6.96 ms | **11.6x** |
| **final interreduction** | **24 136.08 ms** | **1.74 ms** | **13 871x** |
| F4 total | 29 912.76 ms | 79.0 ms | 379x |

**That is the shape of the whole finding.** Three stages sit between 11.6x and 97.1x. One sits at
nearly fourteen thousand. A spread of 8x among the first three is an implementation constant; a
1 400x outlier among them is not an implementation of the same thing at all.

And with factor A removed — `linalg=:deterministic`, the correctness regime Zeebra actually
commits to — `f4_reduction!` rises to roughly 392 ms and that row becomes **13.5x**, putting all
three non-interreduction stages in an **11.6x–25.5x** band. A constant uniform to within 2.2x
across stages that share nothing but the monomial and polynomial representations is a statement
about those representations.

### 3.1 Two asymmetries in the totals, neither of which moves anything

* Groebner.jl's 9.33 ms of AbstractAlgebra↔internal conversion is inside the `@solve_ns` the
  competitive board records and **outside** `f4!`. Zeebra pays no equivalent, its inputs being
  native. Stripping it makes the engine-to-engine ratio ~386x rather than 344x, so **the board's
  348x is the conservative reading** and nothing here needs the larger number.
* Both stage instruments inflate their own totals — `measure_stages` reads a clock four times a
  batch (#349 measured 3.8%–11.5%), `_TIMER` ~2.7% here. Both inflate in the same direction and
  neither moves a share.

---

## 4. What Groebner.jl does instead of Zeebra's interreduction (item 3)

It is not a faster interreduction. **It is linear algebra where Zeebra does division.**

**Groebner.jl.** `f4_autoreduce!` (`src/f4/f4.jl:106-170`): `matrix_reinitialize!` to
`basis.n_nonredundant` rows; each non-redundant basis element becomes an **upper row** of one
Macaulay matrix at multiplier 1 (`:120-133`); `f4_symbolic_preprocessing!` supplies whatever
reducers those rows need (`:135`); every column is marked `UNKNOWN_PIVOT_COLUMN` so that *all* of
them are eliminated against rather than treated as already-reduced (`:137-139`);
`linalg_autoreduce!`; `matrix_convert_rows_to_basis_elements!`; then the leading-monomial
divisibility sweep that drops subsumed elements (`:151-169`). One matrix, the same hashtable, the
same sparse kernels as every other batch. Measured here: **250 × 604, 1.74 ms, 2.0% of `f4!`.**

**Zeebra.** `reduce_grobner_basis_until` (`src/grobner/buchberger.rs:287-352`):
`minimize_grobner_basis`, sort ascending by leading monomial, then **for each of the 247 elements in
turn, `p.normal_form(&others, order)`** at `:336`, writing each remainder back in place.
`normal_form` (`src/poly/multivariate/sparse_multivariate_polynomial_arithmetic.rs:330-376`) pops
the working polynomial's leading term, **linearly scans all 246 reducers calling `checked_div`**
(`:348-352`), and `subtract_shifted` merges the chosen divisor's tail back into the working vector
(`:362-369`). 247 sequential divisions, each with its own intermediate growth.

The ascending-order-and-write-back optimization in that function is real and is documented at
`:294-314` as the difference between 2.5 s and a millisecond on katsura-6 under lex. It is not
enough here: 24 136 ms over 247 elements is **97.7 ms per element**, against a final basis whose
entire monomial support is 604 monomials. At roughly a nanosecond per `checked_div` that is of order
10⁸ divisor tests for one element — several hundred thousand terms passing through a working
polynomial whose answer has a few hundred. **That is intermediate expression swell**, which is
precisely the cost F4's matrix formulation exists to avoid, and which Zeebra avoids everywhere in
F4's main loop and then pays once, at the end, for four fifths of the run.

**Labelled as inference, with the measurement that would settle it.** The per-element arithmetic
above is a plausibility argument, not a measurement: nothing counts terms processed or
`checked_div` calls inside `normal_form`. A `SymbolicCounts`-style pair of counters on
`reduce_grobner_basis_until` — terms popped and divisor tests, summed — settles it for the cost of
two `usize` fields, and would distinguish swell (terms popped ≫ terms in the answer) from scan cost
(terms popped ≈ answer, divisor tests dominating). **Not taken here.** Either way the replacement is
the same, which is why this note does not block on it.

**Zeebra already owns every part of the replacement.** `src/grobner/f4/macaulay.rs` builds Macaulay
matrices, `src/grobner/f4/symbolic.rs` finds reducers, `src/linalg` eliminates them, and
`minimize_grobner_basis` already produces the row set. What is missing is the assembly, and the
correctness argument is the one `:306-314` already writes out — the reduced basis is determined by
its leading monomials, so the route to it cannot change the answer.

**One honest caveat about the ceiling.** #349's 5.10x and this note's 5.03x are ceilings on
*interreduction*, and a matrix pass is not free. The 1.74 ms Groebner.jl spends is a figure for an
engine 11.6x–97x faster than Zeebra per operation, so Zeebra should expect to pay of order 170 ms
and keep about 5.0x of the 5.18x available. That is the first stage-level estimate in this
repository where the comparand's own cost for the same stage is known, rather than a stage share
divided into one.

---

## 5. §6's seven hypotheses, re-screened against grevlex on the instance that loses (item 2)

The screen is `docs/research/competitive-baseline.md` §6a's: if the stage became **free**, the
end-to-end gain is `total / (total − stage)`, and a ceiling inside the 20% noise band settles the
item on arithmetic. §6 ranked its items against **lex and grlex shares on katsura and cyclic**.
Below is the same list against **grevlex shares on `mq-random-10`**, which is the column every
competitive row is measured in.

| § | hypothesis | §6's stated target | **target share here** | **ceiling** | verdict after the change of column |
|---|---|---|---:|---:|---|
| 6.1 | persistent interning table replacing the per-matrix monomial→column `HashMap` | 48% of katsura-6 **lex** construction | construction **3.43%** | **1.04x** | **Demoted from first to last.** Fails the screen |
| 6.2 | cache the total degree in `Monomial<N>` | 61% of katsura-7 grlex interreduction | *not a stage* | *screen cannot bound it* | **Survives, for a different reason than stated** — see below |
| 6.3 | pack a monomial into one `u64` | same | *not a stage* | *screen cannot bound it* | **Survives, and needs rescoping to two words** |
| 6.4 | do **not** port the divmask | symbolic 5.5% on katsura-7 grlex | symbolic **1.35%** | **1.014x** | **Won't-do, more firmly** |
| 6.5 | learn/apply traces for same-shape families | 70% of katsura-6 lex (symbolic + construction) | ≤ **5.05%** | **≤1.05x** | **Dies as a performance hypothesis on this column** |
| 6.6 | do **not** port randomized linear algebra | "at most 22% of elimination" | elimination **13.90%** for Zeebra; **4.89x** for Groebner.jl | 1.16x / — | **Verdict stands, magnitude was wrong by ~20x** |
| 6.7 | delayed reduction in the elimination accumulator | elimination 7–22% | elimination **13.90%** | **1.16x** | **Won't-do, and refuted on evidence too** |

Five of seven are bounded at or below **1.16x** on the instance the deficit was measured on. Item by
item, where the change of column changes the reasoning and not only the number:

**§6.1 is the study's own first priority and it fails here.** Its target is matrix construction,
which is 47.8% of katsura-6 lex and **3.43%** of `mq-random-10` grevlex. This is the same verdict
#349 reached for #268 and for the same reason; what is new is that it lands on the item §7 ranked
first. Worth keeping: the mechanism is real, and `labels` doing double duty as the column index with
no second dictionary (`hashtable.jl:36-62`, `matrix.jl:341`) remains the single most transferable
fact in §3. It is simply not where this instance's time is.

**§6.2 and §6.3 survive precisely because the stage screen cannot touch them.** They are not stage
hypotheses: a cached degree and a packed layout change the per-operation cost of *every* stage at
once, and factor C — 11.6x–25.5x, uniform to within 2.2x across stages that share nothing but the
representations — is exactly the shape a representation constant makes. The measured contrast:

* Groebner.jl ran this instance on `PackedTuple2{UInt64, UInt8}` (measured, `@monomtype`): two
  64-bit words, 8-bit exponent fields, **total degree in the top byte of the first word**, so a
  degrevlex comparison is one unsigned word compare (`packed_vector.jl:58`, `:78-89`, `:290-308`;
  §2.4 of the study).
* Zeebra's `Monomial<10>` is `[u32; 10]` — **40 bytes against 16**
  (`src/poly/multivariate/monomial.rs:15-18`) — with no stored degree: `degree()` sums the array on
  every call (`:53`), and `grevlex` calls it **twice per comparison**
  (`src/poly/multivariate/monomial_order.rs:89-90`).
* And underneath both: `SparseMultiPoly` is a `HashMap<Monomial<N>, F>`
  (`src/poly/multivariate/sparse_multivariate_polynomial.rs:29-35`), so a term lookup hashes 40
  bytes where Groebner.jl adds two integers — its hash is a random dot product chosen *because it
  is linear*, so symbolic preprocessing never re-hashes a monomial, it adds
  (`hashtable.jl:478-480`, `f4.jl:273-275`).

**Two corrections to §6.3's scope.** It is written for "`N ≤ 7` with 8-bit exponents … Zeebra's
whole benchmark corpus at the sizes that matter". `mq-random-10` has **ten** variables, so one word
does not hold it and the comparand uses two; the hypothesis has to be rescoped to a
`PackedTuple2`-shaped two-word layout, which is more work than §6.3 estimated and still inside the
same idea. And the overflow escape hatch §6.3 names as a prerequisite is a real prerequisite:
Groebner.jl can afford narrow fields only because `MonomialDegreeOverflow` plus
`hint = :large_exponents` retries the whole computation wider (§2.2), where Zeebra panics on a
checked add.

**§6.5's cheap transfer test is still worth running, but not for speed on this column.** What
`f4_apply!` skips (§4.2: pair generation, Gebauer–Möller, pair selection, the reducer search, the
zero rows, and the column sort from the second apply on) maps here onto symbolic 1.35% + other 0.27%
+ part of construction's 3.43% — at most 5.05%, a ceiling of 1.05x. Its value is amortization across
a *family*, which this instance cannot exhibit; the honest statement is that the hypothesis is
untested rather than refuted, and that its stated 70% was a lex number.

**§6.6's verdict is right and its arithmetic was wrong.** §6.6 bounded randomized linear algebra at
"at most 22% of elimination" and concluded the trade was bad. The correctness argument is
independent and primary and is unaffected: `src/interface.jl:107-109` still says "no precise bound
on the probability is known". But the *size* of what is being declined is now measured, and it is
large:

| `groebner` call, same process, warm | wall |
|---|---:|
| randomized (default), calls 1 / 2 / 3 | 88.745 / 87.706 / **86.842 ms** |
| `linalg=:deterministic`, calls 1 / 2 | 529.820 / **424.615 ms** |

**4.89x.** The share screen was applied to the wrong engine's profile: elimination is 13.90% of
*Zeebra's* run and about 89% of *Groebner.jl's deterministic* run, and the factor a kernel change
buys is a fact about the engine whose kernel it is. Two consequences, and they pull in opposite
directions, which is why both are stated:

* Nothing changes today. At Zeebra's current speed, randomized linear algebra could buy at most
  1.16x, so declining it costs nothing measurable.
* It is a **permanent floor on the comparison**. The best end-to-end figure Zeebra can reach on this
  row while keeping a deterministic checked answer is Groebner.jl's own deterministic 424.6 ms — a
  70x improvement over 29 912.76 ms — and it would still read **4.89x behind** the published 83 ms.
  Any roadmap that treats 348x as the thing to close is committing to a number that is not
  available. Also worth recording: deterministic Groebner.jl at 424.6 ms is still 16.5x faster than
  Singular's 7 001 ms on this row, so 424.6 ms is a *deterministic* target and not a concession.

**§6.7 is refuted twice over.** The share makes it a 1.16x ceiling. And it is not even what the
comparand does: Groebner.jl ran this instance on `SpecializedArithmeticZp{UInt64, UInt32, true}`,
**not** `DelayedArithmeticZp` (measured, `@arithmetic`), because `p = 2^31 − 1` falls outside every
window delayed arithmetic is selected for (`Zp.jl:363-381` — `2^16 ≤ p < 2^28`, `2^8 ≤ p < 2^12`,
`p < 2^4`). At Zeebra's `REFERENCE_CHARACTERISTIC` the hypothesis has no comparand behaviour to
imitate. §6.7's own refutation clause anticipated this from the other direction, for 64-bit primes
in a `u128` accumulator; it is also true at 31 bits.

---

## 6. The JIT caveat, settled (and what it means for #428)

The issue requires that until the JIT question is settled, only direction and order of magnitude be
quoted. It is now settled, in Groebner.jl's disfavour.

Three successive `groebner` calls on this instance **in one process, after the adapter's proxy
warm-up**: 88.745, 87.706, **86.842 ms**. Monotone, total spread **2.2%**. So on this instance the
residual compilation inside the inner timer is **at most 2.2%**, and its sign *inflates*
Groebner.jl's reported time rather than flattering it — the adapter's module documentation predicted
exactly this and predicted the mechanism (`src/grobner/external/groebner_jl.rs:33-35`: "a code path
the proxy does not reach … compiles inside the timed call, so the figure over-states Groebner.jl's
time and never under-states it").

The deterministic pair is the direct demonstration of that mechanism: 529.820 ms then 424.615 ms, a
**24.8% first-call penalty** for a backend the two-element proxy never reaches. The randomized
default pays a much smaller version of the same thing, which is the 2.2%.

**Consequences.**

* `competitive-baseline.md` §4b's caveat can be narrowed from "ratios should not be quoted" to
  "ratios are accurate to about 2%, erring against Groebner.jl". Two significant figures are now
  defensible on an instance of this size. The caveat still bars the **floor**: at 0.734 ms the 2.2%
  is a different proportion of a much smaller number, and the adapter's own ~0.17 ms absolute
  estimate is a reason not to quote this comparand below a few milliseconds at all.
* The board's 83 ms and this note's 86.842 ms are 4.6% apart, which is the shared-machine
  difference, and both are the same quantity.

**For #428.** Groebner.jl's `wall` is already engine-internal, so the floor-free statistic #428 asks
for adds nothing for this comparand — which is the reconciliation the issue asked for: it is the one
engine for which the classical families were always decisive, and §4b's `katsura-7` 15.9x and
`cyclic-6` 6.2x already are that statistic. What this note adds to #428's third task ("check each
adapter for what stage information it can actually obtain") is a positive answer nobody had:
**Groebner.jl can report a full per-stage split at runtime**, via
`TimerOutputs.enable_timer!(Groebner._TIMER)`, with no patched build and no recompilation — six
named sections, `ncalls` included. §3's table is what that looks like. A `stage` column for
Groebner.jl is buildable today; the only cost is the ~2.7% the timer adds to the run it instruments,
which is why it should be a separate invocation rather than the measured one.

---

## 7. Revised priority order (item 4)

Not §6's order, and the first item is not in §6 at all.

1. **Final interreduction as one Macaulay matrix, not 247 divisions.** Ceiling **5.03x** on the
   losing instance — the largest in this repository and the only one whose comparand's cost for the
   same stage is known (1.74 ms, a 250 × 604 matrix). Mechanism at `src/f4/f4.jl:106-170`; Zeebra's
   current mechanism at `src/grobner/buchberger.rs:287-352`; every component already exists in
   `src/grobner/f4/`. This is #304's stage, promoted again and for a different reason: #304 was a
   *memory* finding about holding the basis three times, and #349 promoted it on an 80.4% share.
   Neither said the stage was computing the right thing the wrong way.
2. **§6.2 then §6.3, as one monomial-representation change at two words**, aimed at factor C
   (11.6x–25.5x) and not at any stage. §6.2's own instruction stands and should be obeyed: a
   microbenchmark of `MonomialOrder::cmp` before touching the type, because `Monomial` is
   serialized and a new field is a format change. The `HashMap<Monomial<N>, F>` term store
   (`sparse_multivariate_polynomial.rs:29-35`) belongs in the same screen and may well dominate the
   layout question; nothing has measured the two apart.
3. **§6.1 last, not first.** 1.04x here. Revisit only if §6.2/§6.3 succeed enough to make
   construction's 3.43% a large share, which is the same conditional §6.4 already carries.
4. **Won't-do, now on the losing column**: §6.4 (1.014x), §6.7 (1.16x, and the comparand does not
   do it either), §6.6 (correctness, with its magnitude corrected to 4.89x), §6.5 as a performance
   hypothesis (≤1.05x; its family-amortization claim remains untested).

**And the explicit statement the issue asked for: the gap is *not* reachable through §6 — but not
because it is unexplained.** Of the measured 344x, §6 can address factor C and only factor C. Factor
A (4.89x) is a design commitment Zeebra should keep. Factor B (5.03x) is an algorithm substitution
that §6 never proposed, because §6 was looking for stages to speed up and this stage needs
replacing. What is reachable, taking items 1 and 2 above and keeping the deterministic kernel, is
roughly **424 ms against 29 913 ms — a 70x improvement, landing 4.89x behind the published figure
and ahead of every other deterministic engine measured on this row.** That is a target; it is not a
forecast, because a ceiling bounds the conceivable and not the achievable (§6a), and factor C has no
measured decomposition yet at all.

---

## 8. Negative results and loose ends, kept

* **"Zeebra is doing asymptotically more work" is false**, and it was the issue's leading candidate.
  Recorded as the most expensive hypothesis this measurement killed.
* **The 1.78x in reducer rows is unattributed.** Zeebra builds 84 645 upper rows where Groebner.jl
  builds 47 464; Groebner.jl says 41.5% of its own are useful and Zeebra has no such counter. A
  "reducer rows ever used" counter is the measurement.
* **Intermediate swell in `normal_form` is inferred, not measured** (§4). Two counters settle it.
* **The pair-degree progression is not comparable from the current instruments.** Groebner.jl
  reports 2,3,4,5,6,6,6,7,7,8; `f4_profile` reports no per-batch degree sequence. `examples/f4_degrees`
  does report per-degree rows but has no `mq` mode. The batch *count* agrees, which is what item 1
  needed.
* **Every duration here is a shared-machine duration** (header). The counts are not, and the
  conclusions rest on counts plus ratios taken minutes apart on one box.
* **`groebner_learn` took 1 065.7 ms** against the deterministic `groebner`'s 424.6 ms, so trace
  recording roughly 2.5x's the run. Noted only so that nobody reads `@learn_ns` as a competitive
  figure; no count depends on it.

---

## 9. Reproducing

```sh
. tools/external/env.sh          # REQUIRED FIRST, or julia is not on PATH

# Zeebra's side: the digest-pinned instance, and its stage split
cargo run --release --example f4_profile -- mq-instance > /tmp/mq.canonical
tools/benchlock.sh <tag> taskset -c 0-7 \
    cargo run --release --example f4_profile -- mq

# Groebner.jl's side: the same ideal, its own counters, its own stage split
tools/benchlock.sh <tag> taskset -c 0-7 \
    julia -t1 tools/external/groebner-jl-counts.jl /tmp/mq.canonical
```

The Julia script echoes `@digest` and every `@gen` before computing anything. **If the digest it
prints is not `72d0ad315fc25409…`, the two sides are not on the same ideal and nothing below the
echo means anything** — which is the same discipline `Instance::digest` enforces on the board.
