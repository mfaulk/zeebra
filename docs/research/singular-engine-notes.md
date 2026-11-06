# Reading Singular's engine: six things it does that Zeebra does not

A source-reading record, in the style of `signature-based.md` §4.0 — read the primary source before
contemplating an implementation. **No new code and no measurements here.** Every claim about
Singular cites a file and line; every claim about Zeebra was checked against the tree rather than
recalled, and the three candidates that turned out to be *already done* are recorded in §8, because
a mining exercise that only reports hits is not a reading, it is a sales pitch.

Source: `github.com/Singular/Singular` at `3f188e4e` (2026-11-05), the `kernel/GBEngine`,
`libpolys/polys` and `Singular/LIB` trees.

Singular is already this project's Gröbner oracle (`src/grobner/differential/singular.rs`), so it is
the one external engine whose behaviour Zeebra is already committed to agreeing with. That makes its
*internals* the natural place to look for what the agreement is costing.

Ranked by expected value, which is not the same as by size. **§0 revises that ranking against the
ceilings this repository has already measured, and it demotes most of it.** Read §0 first.

---

## 0. What these are worth, against the instruments that already exist

Written after §1–§8, by doing to this note what `signature-based.md` §4.0 did to its own first
version: reading the ceiling off existing measurements instead of asserting that a mechanism from a
mature engine must be worth having. One figure below is new (§0.3); every other is already in the
tree.

### 0.1 The budget: elimination is the computation

`docs/MILESTONE-F4-OPTIMIZATION.md` §6.2, the `f4_profile` table:

| stage | share of total |
|---|---|
| elimination | **65%–88%** on every instance above a millisecond |
| construction | ~13% |
| symbolic preprocessing | **2%–15%**, and smallest where the reducer share is largest (2.1% on katsura-7 grevlex) |

**Not one of the six findings touches elimination.** So the whole of §1–§6 competes for the 12%–35%
that is not linear algebra, and the honest ceiling on all of them combined, on the solve path, is a
fraction of that. The large numbers below are all *off* the solve path.

### 0.2 Item by item

| § | finding | what it attacks | measured ceiling | verdict |
|---|---|---|---|---|
| 5 | criteria + fork in certification | certification, which is **34x–67x the solve** on Poseidon (4.8 s and 25.1 s, `hilbert-driven.md` §5) | 69%–89% fewer pairs × ~8–16x cores | **Do this.** The only item attacking a measured multi-second cost. |
| 3 | `clearS` | redundant basis elements | **2 of 43 in grevlex; 200 of 206 in lex** (§0.3, new) | Worthless in grevlex, large in lex. Zeebra computes in grevlex. |
| 1 | exact Hilbert series | the semiregular prediction's 39% and **27x** errors | removes the slack parameter; but costs ~a full extra GB | **Probably a net loss as stated** — see §0.4. |
| 4 | term-count selection axis | matrix size | best schedule ever measured here: **7%–14.5%** structural, runtime in noise, under the 20% threshold | Cheap to try, low prior. |
| 6 | whole-state `kTest` | defect-detection latency | no runtime effect at all | Worth having, not a speedup. **Done** — #252. |
| 2 | short exponent vectors | divisor lookup | **≈0** — "*eliminating divisor lookup entirely would save about 1% of the symbolic stage's share of 1.4%*" | Already rejected twice. §2.3. |

### 0.3 New measurement: redundant basis elements, by order

How many polynomials F4 carries that the final minimization discards — `system.len() +
statistics.elements_added − basis.len()`, under `F4Options::recommended()` over `Zp2147483647`. A
proxy for what `clearS` would remove, and an upper bound on the count (not on the duration they were
carried for, which is what actually costs).

| system | lex | grlex | grevlex |
|---|---|---|---|
| cyclic-4 | 5 / 11 (45.5%) | 3 / 10 | 3 / 10 |
| cyclic-5 | 40 / 51 (78.4%) | 28 / 58 | 26 / 46 (56.5%) |
| katsura-4 | 12 / 16 (75.0%) | 3 / 11 | 2 / 9 |
| katsura-5 | 41 / 46 (89.1%) | 4 / 20 | **2 / 15** |
| katsura-6 | **200 / 206 (97.1%)** | 5 / 37 | **2 / 24** |
| katsura-7 | *crosses the entry budget* | 6 / 70 | **2 / 43 (4.7%)** |

**Under a graded order the katsura family carries exactly two redundant elements, at any size.**
Under lex, katsura-6 carries 206 polynomials to keep 6. `clearS` is therefore not an optimization
Zeebra is missing; it is an optimization for a regime Zeebra does not compute in. (cyclic-5 is the
exception at 56.5% in grevlex, and is the one instance where the idea could be tested at all.)

### 0.4 The pattern, which is the actual finding

§1 and §3 are the same discovery twice: **both are levers on the expensive-monomial-order path, and
Singular takes that path where Zeebra does not.** `stdhilb` pays a cheap `dp` Gröbner basis to
accelerate an expensive `lp` one, and the §6.2 table shows that ratio is real here too — katsura-6 is
27 ms in grevlex against 2 963 ms in lex, katsura-5 is 1.87 against 15.64. Zeebra never pays it: it
computes in grevlex and converts with FGLM. So the series that would drive the hard computation
would have to be bought with a homogenized grevlex computation of **about the cost of the one it is
meant to accelerate**, and `pair-scheduling.md` §5 has already made the sharper version of this
argument — "*a batch cap gets a large part of the same saving with no prediction and no
certification*", 55% of the pairs on Fukuoka III `n=10`.

Both items become worth having the moment Zeebra wants a Gröbner basis in a hard order *directly* —
which is the positive-dimensional case FGLM structurally cannot serve, and which §7's Gröbner-walk
note is the other half of. That is a capability question, not a performance one, and it is not
currently on the roadmap.

The one unambiguous recommendation is §5, and it is unambiguous because certification is the only
place in the measured profile where a 25-second cost sits next to a mechanism of known size.

---

## 1. An exact Hilbert series from a cheap order, instead of a prediction

**What Singular does.** `Singular/LIB/standard.lib`'s `stdhilb` is a four-step recipe:

1. `hilbRing(i,w)` builds a ring with one extra homogenizing variable and a single `dp`/`wp(w)`
   block, and homogenizes the input into it.
2. `Id[1] = std(Id[1])` — a Gröbner basis in that **cheap degree order** — then
   `hi = hilb(Id[1],1,W)` takes the Hilbert series of the result.
3. It switches to a ring that differs only in carrying the **target (hard) ordering**, and calls
   `i = std(i, hi)`: a Hilbert-driven Gröbner basis *with that series supplied*.
4. `subst(i, @, 1)` dehomogenizes and the result is interreduced back in the original ring.

The driving itself is `kernel/GBEngine/khstd.cc:28`, `khCheck`. It keeps a countdown `eledeg` of how
many further basis elements the current degree is still owed, obtained by subtracting the series of
the current leading ideal from the target series. When the countdown reaches zero it **deletes the
remaining pairs below that degree** from `L`; when the two series agree outright it empties `L`
entirely and the computation is over.

**Why that is a different claim from Zeebra's.** The Hilbert series of a homogeneous ideal does not
depend on the monomial order — both the leading ideal's series and the ideal's are the same series.
So a series computed in `dp` is a **theorem** about the `lp` computation, and deleting pairs on it is
sound. Zeebra's `HilbertSelection` (`src/grobner/f4/hilbert_driven.rs`) drives on
`SemiregularSeries` instead, which is a **prediction**, and the module says so at length — which is
exactly why its two modes (`CertifiedLimited`, `Deferred`) are built never to discard a pair. The
design is right for the input it has.

**This is the item that addresses a measured failure.** `docs/research/hilbert-driven.md` §1 records
that the semiregular prediction is "wrong — in the unsafe direction — on the inhomogeneous systems
this milestone is about". Singular's answer to precisely that case is: stop predicting, homogenize,
and *compute* the series where it is cheap. Zeebra has both halves already —
`HilbertSeries::of_basis` (`src/grobner/hilbert.rs:205`) is the exact series of a leading ideal, and
F4 over grevlex is the cheap computation — and has no path that joins them.

**What it would cost, honestly.** Homogenizing means one more variable, and `Monomial<const N>`
makes that a type-level change: stable Rust will not write `Monomial<{N+1}>`. The way out is for the
caller to work at the larger width throughout, or to reserve a slot, and either way the plumbing is
the bulk of the work rather than the algorithm.

**And the economics do not work for the pipeline Zeebra has — see §0.4.** `stdhilb` is cheap because
the driving computation is in `dp` and the driven one in `lp`; Zeebra's expensive computation *is*
the grevlex one, so the series would cost about what it saves. The measurement that would settle it
is small and specific: time a grevlex Gröbner basis of a homogenized instance against the
inhomogeneous original. If homogenizing is materially cheaper the recipe is live; if it is not, this
is a won't-do for the reason `pair-scheduling.md` §5 gives.

## 2. Short exponent vectors — **already measured and rejected here; see §2.3**

**What Singular does.** `libpolys/polys/monomials/p_polys.cc:4968`, `p_GetShortExpVector`, squeezes
an exponent vector into a single machine word: with `n = 64 / #vars` bits per variable, exponent `e`
sets `min(e, n)` of its `n` bits. The point is the implication recorded in the comment above it —

```text
if (ev1 & ~ev2) then exp1 does not divide exp2
```

— a one-word necessary condition for divisibility. `p_LmShortDivisibleBy`
(`libpolys/polys/monomials/p_polys.h:1931`) tests it first and only then does the real comparison.
Two details make it fast rather than merely clever:

- The vector is **cached beside the data, in a parallel array of words**: `strat->sevT`, `sevS`.
  `kFindDivisibleByInT` (`kernel/GBEngine/kstd2.cc:317`) is then a scan whose per-candidate cost is
  `!(sevT[j] & not_sev)` — one word load and one `AND` — over contiguous memory.
- The *complement* is what gets stored for the divisor side, so the inner loop has an `AND` and no
  `NOT`.

And it is checked rather than trusted: under `PDEBUG` the same function asserts the cached word
equals a fresh `p_GetShortExpVector`, and that a `FALSE` from the mask implies `FALSE` from the
exact test.

**What Zeebra does.** `MonicBasis::find_divisor_with` (`src/grobner/f4/symbolic.rs:475`) is a linear
scan calling `Monomial::checked_div` — an N-element loop with an early return — on every basis
element. `SymbolicCounts::divisor_scan_steps` exists specifically to measure this
(`src/grobner/f4/symbolic.rs:147`: *"Divisor lookup is a linear scan"* is named there as a
hypothesis with a counter attached). `normal_form`'s inner loop
(`src/poly/multivariate/sparse_multivariate_polynomial_arithmetic.rs:162`) has the same shape.
Nothing in `src/poly/multivariate/` computes a support mask.

**Why it fits here particularly well.** `find_divisor_with`'s own documentation already reserves the
seam — *"an index or a filter goes behind this signature"* — and states the agreement obligation: a
faster lookup must return the **same** divisor, not merely *a* divisor, because a different divisor
is a different multiplier, hence a different row. A mask filter satisfies that by construction: it
can only reject non-divisors, so `FirstApplicable` returns the identical index and the matrix is
bit-identical. That is the rare optimization that needs no new correctness argument, only the
existing differential test. Singular's debug-mode cross-check of cache against recomputation is the
assertion to copy along with it.

### 2.3 Which is why it is already dead

`docs/MILESTONE-F4-OPTIMIZATION.md` §7.2.2 built a divisor-lookup index, measured it, and rejected
it — and the last paragraph of that section is explicit: "*A support bitmask over the variables was
measured alongside and also rejected: for these bases the mask rarely rejects, so it adds a word
operation ahead of a `checked_div` that already exits on the first variable it fails.*" The index
itself reduced examinations on every instance and was **slower** on every instance, because the scan
it replaced is sequential and the prefetcher covers it.

Two things survive the correction, and neither rescues the idea:

- Singular's vector is **strictly stronger than the one Zeebra tried.** A support bitmask is one bit
  per variable; `p_GetShortExpVector` spends `64/N` bits per variable and sets `min(e, n)` of them,
  so it rejects on exponent *magnitude* and not only on support. At `N ≤ 10` that is six or more
  bits per variable. The measured "rarely rejects" is a fact about the one-bit variant.
- The ceiling makes that irrelevant. §7.2.2 also states it: "*Eliminating divisor lookup entirely
  would save about 1% of the symbolic stage's share of 1.4%.*" A better filter cannot beat deleting
  the whole stage.

Recorded as a **won't-do, for the second time**, which is the useful outcome: the agreement-preserving
argument in §2.2 is sound and would have been worth having if the stage mattered, and it does not.

## 3. Shrink the basis during the run

**What Singular does.** `clearS` (`kernel/GBEngine/kInline.h:1235`): when a new element `p` enters,
every `S[at]` whose leading monomial is divisible by `LM(p)` is **deleted from `S`** on the spot —
using the mask test from §2 to find them cheaply. `clearSbatch` (`kernel/GBEngine/kutil.cc`) runs it
across the whole basis after each insertion, and `strat->noClearS` exists because there are settings
(syzygies, modules) where it is not allowed.

**What Zeebra does.** Nothing of the kind. In F4's main loop
(`src/grobner/f4/mod.rs:406`) every candidate is pushed onto `basis`, `monic` and `leads`, and
none of the three ever shrinks. A redundant element — one whose leading monomial is a multiple of
another's — therefore keeps costing a scan step in every subsequent divisor query, keeps generating
pairs in `push_pairs_from_leads`, and is only dropped at the very end by `minimize_grobner_basis`.

The pruning is standard (it is the removal half of Gebauer–Möller's `Update`), and the shape that
fits Zeebra is a `redundant: bool` on the lead rather than a removal: pair indices refer to basis
positions, so marking keeps `BasisIndex` stable while removing the element from divisor lookup and
pair generation.

**Measured in §0.3, and it is not worth building for the grevlex pipeline:** the katsura family
carries exactly two redundant elements under a graded order at every size, against 200 of 206 under
lex. cyclic-5 at 56.5% in grevlex is the only instance in the corpus where the idea could even be
tested.

## 4. Two selection axes Zeebra has not tried: term count

Zeebra's `PairSchedule` (`src/grobner/pairs.rs:221`) has five variants and every one of them ranks
by **multiplier size** — degree or monomial, small-first with a large-first control. Its
`ReducerSelection` has `FirstApplicable` and `LargestLeadingMonomial`, which is the same axis again
(largest divisor = smallest multiplier). Singular ranks by something orthogonal: **how many terms
the polynomials have.**

- **Reducer choice.** Singular keeps the reduction set `T` *sorted* by the chosen criterion so that
  the first divisor found in the scan is the preferred one, and `initBuchMoraPos`
  (`kernel/GBEngine/kutil.cc:9588`) carries a comment recording which criterion won a bake-off:
  "*from my experiments for Singular-2-0 I conclude that `posInT_EcartpLength` is the best of
  `posInT15`, `posInT_EcartFDegpLength`, `posInT_FDegLength`, `posInT_pLength`*". That function
  (`kutil.cc:5146`) orders by ecart, then by **`pLength` — the term count**. In global orders the
  ecart is zero, so what remains is: among the divisors, prefer the one with the fewest terms. In
  F4's symbolic preprocessing the reducer chosen *is* the row added, so the sparsest reducer is
  directly the sparsest row.
- **Pair ranking.** `slimgb`'s `pair_weighted_length` (`kernel/GBEngine/tgb.cc:1325`) scores a pair
  by the expected length of its S-polynomial: over a prime field the coefficient-size factors drop
  out and it reduces to `lengths[i] + lengths[j] - 2`.

Both are cheap in Zeebra — `BasisElement::terms` is a `Vec`, so `len()` is free — and both drop into
the existing shape: a `FewestTerms` reducer policy, and a `ShortPair`/`LongPair` schedule pair with
the latter as the control, picked up automatically by `PairSchedule::ALL` and the ablation examples.
Under a `CertifiedLimited` cap, which decides *which* pairs of a degree enter the batch, a
length-based rank is a principled choice where the multiplier-size schedules are silent.

Worth flagging what Singular's comment really licenses: it is a 2000-era measurement on
classical systems under Buchberger, not F4, and `docs/research/pair-scheduling.md` has already found
that schedule changes on these systems mostly measure noise. The claim here is that the *axis* is
untried, not that it wins.

**Measured, in #253, and the two halves came out differently.** The pair ranking is a null result:
`short-pair` raises peak live entries on all seven instances and `long-pair` is inverted against it
on two, which is the noise signature. The reducer policy is not: `FewestTerms` takes peak live
entries down 27.4% and 31.7% on katsura-5 and katsura-6 grevlex with a control 1.09x–3.82x away —
and *up* 25%–30% on the same systems under grlex, so it stays selectable rather than becoming the
default. Both tables are in `docs/research/pair-scheduling.md` §2 and §6.

## 5. Certification: apply the criteria, and fork

`kernel/GBEngine/kverify.cc:24`, `kVerify1`, is a standalone Buchberger-criterion check of a
submitted basis — and it calls `initBuchMoraCrit` first, so the **product, chain and Gebauer–Möller
criteria prune the pairs it has to verify.** `kVerify2` (line 141) is the same check with the pair
list split across `fork`ed processes, because the checks share no state.

Zeebra's `certify.rs` is the stricter instrument of the two — it also checks `F ⊆ <G>` and
reducedness, and it reasons explicitly about provenance, which Singular does not — but it checks
**all** pairs: its own cost note says "`|G|²/2` normal forms … on a 105-element basis some 5 500
divisions", and §8.5's rule is that "a saving the check erases is not a saving". Zeebra's own
`pair_criteria` table (`docs/research/signature-based.md` §2) measures Gebauer–Möller discarding
69–89% of pairs on this corpus.

Applying the criteria during certification is the same theorem applied to a different set of
polynomials, and the split matters. The product criterion and Gebauer–Möller's lcm-divisibility
criteria are functions of the leading monomials alone, so they transfer unchanged. The **chain**
criterion does not: `PairQueue::discards` (`src/grobner/pairs.rs:1007`, with the argument at
`:1005`) justifies a discard by "*a pair processed strictly earlier*", and in a verification pass
nothing has been processed — every pair is merely present. That is the classical static-basis
Gröbner test and the minimal-counterexample argument for it has to be written out rather than
inherited. `examples/pair_criteria.rs` already has a `product`-only configuration, so the share
that transfers for free is measurable before any of this is built.

Forking is the second, independent factor, on a check that is
embarrassingly parallel; `README.md` already records 92–95% efficiency to 32 cores on the resultant
route, so the machinery and the habit are both there.

## 6. One whole-state checker, not scattered assertions

> **Implemented, #252.** `MonicBasis::check` and `PairQueue::check`, both `cfg(debug_assertions)`,
> called once per batch from F4's main loop. Eleven tests, each corrupting one field and asserting
> the checker names it, plus a control per checker so they cannot pass against a checker that
> rejects everything. Cost at suite scale: 41.08 s to 41.41 s on the debug library suite, inside
> noise. One invariant this section proposed turned out to be **false** and is documented as such
> rather than asserted — see the end of the section.

Singular carries `kTest`, `kTest_TS`, `kTest_T`, `kTest_L`, `kTest_S` (`kernel/GBEngine/kutil.h:636`
ff., bodies at `kutil.cc:789` and `:1004`), compiled to `TRUE` without `KDEBUG`, and calls them once
per main-loop iteration. What they check is the discipline worth copying: **every cached or derived
field is recomputed and compared to what is stored.** `T[i].max_exp` is recomputed by
`p_GetMaxExpP` and compared (`"T[%d].max out of sync"`); the short exponent vectors are asserted
equal to a fresh `p_GetShortExpVector`; `kbTest` (`libpolys/polys/kbuckets.cc:109`) recomputes each
bucket's `pLength` and also checks the structural bound `pLogLength(length[i]) <= i`; `S_2_R` and
`i_r` cross-indices are checked to point back at each other. Failures go through `dReportError`,
which names the field and the index.

Zeebra has four `debug_assert`s across all of `src/grobner/f4/` and `src/grobner/pairs.rs` and no
whole-state checker. Its safety net is instead proptest plus the Singular differential sweep — which
is a real net, but it catches a **wrong answer**, where `kTest` catches the corruption at the
iteration that caused it. The invariants to check are already written down as prose in the places
that establish them: `symbolic.rs:337` and `:402` on the recorded leading monomials agreeing with
the terms, the reducer cache's coherence, the pending/deferred sets being disjoint. A
`#[cfg(debug_assertions)]` `check()` on `MonicBasis` and `PairQueue`, called once per batch, is the
same idea in Rust's idiom and would have to recompute rather than trust.

## 7. Three smaller ones, recorded without a recommendation

- **Geobuckets.** `libpolys/polys/kbuckets.h:179`: a polynomial under reduction is held as levels,
  bucket `i` of length at most `4^i`, leading monomial separate in bucket 0, so repeated
  subtractions merge into small levels and carry up amortized instead of re-walking one long list.
  The header also records that a base of 2 was tried and is "less efficient, both, in theory and in
  practice". Zeebra's `normal_form` already keeps its working polynomial as an ascending sorted
  `Vec` with O(1) leading-term `pop` — most of the benefit — but `subtract_shifted` merges into that
  one vector, which is the operation geobuckets exist to replace. It only matters where the working
  polynomial gets long, i.e. lex and elimination orders.
- **Gröbner walk.** `kernel/groebner_walk/` is a whole module for order conversion that, unlike
  FGLM, does not need zero-dimensionality. Zeebra's conversion is FGLM only
  (`src/grobner/fglm/conversion.rs`) and the word "walk" does not appear anywhere in `docs/` in this
  sense. It is usually slower than FGLM where FGLM applies, so this is a note about a structural
  gap, not a proposal.
- **Factorizing Buchberger.** `kernel/GBEngine/kstdfac.cc`: when a new basis element factors, clone
  the entire strategy state once per factor and continue independent computations, yielding a list
  of ideals whose varieties cover `V(I)`. Full use needs multivariate factorization, which Zeebra
  does not have and which Singular gets from `factory`. The special case within reach is splitting
  on an element that is univariate — `src/poly/univariate/factorize.rs` can already factor those.

## 8. Candidates that were already done, and one that was wrong

Recorded because they are the useful half of a mining exercise.

- **Exponent-overflow safety.** Singular carries an entire machinery for it — exponent bounds, a
  `tailRing`, `completeReduce_retry` when a reduction would exceed the bound. Zeebra panics instead,
  in every build, on a checked add, with a regression test naming the release-only defect that
  motivated it (`src/poly/multivariate/monomial_arithmetic.rs:14–23`).
- **Small-prime arithmetic.** Singular's `npMultM` (`libpolys/coeffs/modulop.h:71`) multiplies by
  discrete log/exp table lookups and inverts in one lookup. That is for `p` small enough to
  tabulate; Zeebra's fields are 31-, 32-, 64- and 256-bit with Montgomery multiplication
  (`src/fields/prime_field_32.rs:122`) and Montgomery's trick for batch inversion. Nothing to take.
- **Interreduction cost.** Singular's reduction order and Zeebra's `reduce_grobner_basis` arrive at
  the same optimization — reduce in ascending order of leading monomial, writing back in place —
  and `src/grobner/buchberger.rs:239–259` records it as the difference between 2.5 s and a
  millisecond on katsura-6 under lex, with the proof that the result is unchanged. The comment in
  `f4/mod.rs` about interreduction dominating predates that fix.

The thing I expected to find and did not: a reason to revisit F5. Singular ships a real
signature-based engine (`sba` in `kstd2.cc`, with `posInLSig`, rewritten-criterion variants, and its
own `Tst/SBA` suite), which makes it a fine oracle for anyone implementing one — but a working
implementation is not an argument about headroom. `docs/research/signature-based.md` measured that
headroom at ~2x on this corpus and, as of its 2026-11-06 revision, rests the won't-do on three
independent legs. Nothing read here touches any of them.

---

## 9. What §6 got wrong, found by implementing it

§6 listed "no duplicate leads" among the invariants a whole-state checker should assert. It is
**false**, and so is the stronger property that no leading monomial divides another's. Asserting
either fires on `certify`'s own fixtures, where element 0's lead `x_0^2` is divisible by element 4's
lead `x_0` — an input generator divided by a basis element F4 discovered *later*.

That is the same fact §0.3 measured from the other direction, and it is worth stating as an
invariant of the engine rather than an accident: **F4's basis is not minimal at any point before the
final interreduction**, because nothing removes an element once a later one subsumes it. §3 is the
mechanism that would, and §0.3 is the measurement saying it is not worth adding for a grevlex
pipeline. The checker documents the non-invariant in place, so the next reader does not re-derive it
by watching a correct computation fail an assertion.
