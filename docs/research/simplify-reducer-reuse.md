# Faugère's `Simplify` (reduced-row reuse across F4 batches): deferred

**Measured at:** not measured here — every figure is quoted from a cited source: #835's work ledger
([`m29-grobx-attribution.md`](m29-grobx-attribution.md), measured at `7e18d089`, counter binary
built from `2fe11b8d`, evidence in [`research/m29-c1/`](../../research/m29-c1/README.md)), the
M29 cost model ([`m29-baseline-cost-model.md`](m29-baseline-cost-model.md), `7251e775` and
`6a78e91a`/`6efb70a5` for §6b), M16's reducer measurements
([`MILESTONE-F4-OPTIMIZATION.md`](../MILESTONE-F4-OPTIMIZATION.md) §7.1.5 and §7.2.3, publication
bound `914f1ef8`…`ca0b3dad`), #1031's reuse census
([`reduced-multiple-reuse-census.md`](reduced-multiple-reuse-census.md), measured at `f6cafd44`)
for §6.1 and §7, and the two papers' own tables. Nothing was built, run or reserved.
Arithmetic on those figures is labelled as derived.

This is #809, the follow-up that [`specialized-gb-engines.md`](specialized-gb-engines.md) §4.1 filed
from OpenF4. It is a literature and design note only. The prototype the issue describes is
**deferred** (§6), because the gate #809's own comment set — "pursue only if #835's work ledger
shows substantial repeated reducer computation" — is not met: shipping F4 does **no** computation on
reducer rows, so there is no repeated reducer work for `Simplify` to save. It would have to add
that work first.

OpenF4 is GPL-3.0-or-later. It is described here as a reference and nothing from it may enter the
crate ([`external-provenance-policy.md`](external-provenance-policy.md)).

---

## 1. Sources

| Source | Copy read | Notes |
|---|---|---|
| J.-C. Faugère, *A new efficient algorithm for computing Gröbner bases (F4)*, J. Pure Appl. Algebra 139(1–3):61–88, 1999. DOI 10.1016/S0022-4049(99)00005-5 | The author's own copy (`www-polsys.lip6.fr/~jcf/Papers/F99a.pdf`, 29 pp.). The live host timed out, so the copy came from the Internet Archive's capture of that URL | `Simplify` is in **§2.4**, "Buchberger criteria. Improved F4 algorithms" (author's copy pp. 8–11), not §2.2 as #809's body says. §2.2 is the linear-algebra notation. The worked example is §2.6 (p. 14) |
| A. Joux, V. Vitse, *A variant of the F4 algorithm*, CT-RSA 2011, DOI 10.1007/978-3-642-19074-2_23. IACR ePrint 2010/158 | `scripts/fetch-eprint 2010/158` (14 pp., CC BY) | `TabSimplify` is described on pp. 3–4. Alg. 3 is `Simplify` and Alg. 5 is `Postprocessing` (pp. 5–6). The Katsura-12 matrix-size remark is on p. 13 |
| OpenF4, `nauotit/openf4` | `gh api repos/nauotit/openf4/tarball/7155c6ec4e5f776e0e12202716dc7da58469e77b` (the pin in `specialized-gb-engines.md` §0, committed 2018-04-06) | Paths below are relative to the repository's `openf4/` directory |

## 2. What `Simplify` is

### 2.1 Faugère 1999, §2.4

The first F4 keeps only the rows of each reduced matrix whose head terms are new, F̃⁺. Rows whose
head terms already appeared in the matrix are thrown away. The improved algorithm keeps those rows
too, so it keeps every reduced matrix F̃ⱼ (p. 9). Symbolic preprocessing then stops adding a
product `t·f` literally. Each row, whether a pair half or a reducer, is
`mult(Simplify(t, f, 𝓕))` (p. 10), where 𝓕 is the list of every earlier matrix.

`Simplify(t, f, 𝓕)` scans the divisors `u` of `t`. If some earlier matrix Fⱼ contained the row `u·f`,
it takes the row `p` of Fⱼ's echelon form whose head term is `HT(u·f)`. It then recurses on
`(t/u, p)`, or returns `(1, p)` when `u = t`. If no divisor `u` has such a row, it returns `(t, f)`
unchanged. (The pseudo-code writes `p ∈ F̃ⱼ⁺`. But `HT(u·f)` is a head term of Fⱼ itself, and F̃ⱼ⁺
excludes exactly those head terms. So the row meant is in F̃ⱼ, the "useless rows" kept above.)

Remark 2.6 (p. 11) reports that in 95% of cases the result is a product `(xᵢ, p)` with one
variable, "frequently" `(xₙ, p)`. Faugère compares it to FGLM's normal forms by matrix
multiplication. That is the empirical basis for OpenF4's per-variable chain (§3).

### 2.2 The invariant, and why the basis does not change

**Lemma 2.3** (p. 10). If `Simplify(t, f, 𝓕) = (t′, f′)`, then
1. `HT(t′·f′) = HT(t·f)`, and
2. `t·f = λ·t′·f′ + r` for some nonzero `λ ∈ R` and some `r` in the R-module spanned by
   F̃⁺ ∪ 𝓕, with `HT(r) < HT(t·f)`.

**Theorem 2.4** (p. 11). Suppose every earlier F̃ₖ⁺ is in G, the two rows of a pair are the
simplified products, and `spol(f₁, f₂)` has a `t`-representation over the matrix with `t` below the
lcm. Then the original `spol(g₁, g₂)` also has a `t′`-representation with `t′ < lcm`. The difference
between the simplified and the literal S-polynomial is `r + r′`, which lies in the ideal and sits
strictly below the lcm. Theorem 2.3 (the t-representation criterion, from Becker–Weispfenning) then
makes G a Gröbner basis.

For Zeebra, the operational form is: **a replacement row must lie in the ideal, have exactly the
head term of the product it replaces, and differ from that product only by ideal elements whose
head terms lie strictly below it.** Any row that some earlier batch computed *from* `u·f`, by
subtracting lower-headed rows of the same matrix, qualifies. Two consequences:

- **The output reduced basis is unchanged.** `Simplify` changes the polynomials each batch reduces,
  so it changes the candidates, the later pairs and the trajectory. The reduced Gröbner basis of an
  ideal under a fixed order is unique, though, and Zeebra always returns the interreduced basis.
  Exact `basis_sha256` equality with shipping F4 is therefore the correctness assertion a prototype
  has to pass on every instance. A different element count before interreduction is not a failure.
  This is the same argument `ReductionStrategy::Structured` already relies on
  (`src/grobner/f4/options.rs:45-49`).
- **Forgetting is always safe.** `(t, f)` is a valid answer, so a retained-row store can evict
  anything at any time and the result is still correct. `ReducerCache::clear` relies on the same
  property (`src/grobner/f4/symbolic.rs:254-262`). This is what makes a memory bound on the store
  possible (§4.2).

### 2.3 Joux–Vitse 2010/2011: `TabSimplify`

Joux and Vitse replace the scan over "all the former matrices" with a per-basis-element array
`TabSimplify[ind]` of pairs `(m, g)`, meaning that "the product `m·f` can be simplified into the more
reduced polynomial `g`" (pp. 3–4).

- **Alg. 3 `Simplify(t, ind)`** walks that list from last to first. On `m = t` it returns `g`. On
  `m | t` it appends `(t, (t/m)·g)` to the list and returns `(t/m)·g`. So every product built is
  also memoized.
- **Alg. 5 `Postprocessing`** (lines 10–24) takes each row `f` of the reduced row echelon form whose
  head term is **not** new. For each `g` in G_min with `LM(g) | LM(f)`, it overwrites the entry for
  `LM(f)/LM(g)` in `TabSimplify[index(g)]` with `f`, or appends one.
- The matrix is taken to **reduced** row echelon form (Alg. 1 line 25). The stored rows are
  therefore fully reduced against every pivot of their matrix, including the other reducers.

The paper's subject is F4Remake, a trace-replay method for many systems of the same shape. F4Remake
reuses `Simplify` unchanged. Its one quantitative remark about `Simplify` is that their F4's matrices
were smaller than Magma's: 15,393 × 19,368 against 20,162 × 24,137 at step 12 of Katsura-12, with the
same new polynomials found. They attribute this to a "much more efficient" `Simplify` (p. 13). That
is a **symbolic** effect, a smaller closure, as well as an elimination effect. #835's ranking does
not credit it (§5.2).

## 3. OpenF4's implementation (reference only)

- **The chain.** Every `TaggedPolynomial` holds `int* _simplyrules`, one slot per variable
  (`include/tagged-polynomial.h:252-253`). Slot `i` is the index, in the global
  `_taggedPolynomialArray`, of the polynomial standing for `xᵢ·(this)`.
- **`Ideal::simplify(u, numList)`** (`src/ideal.inl:232-279`) walks `u`'s exponent vector from the
  last variable to the first, one power at a time, and follows slot `i` at each step.
  - A non-empty node becomes the new best ancestor, and the code records which part of `u` is still
    to be multiplied (`varlistTmp`).
  - A missing link (`< 0`) gets a new **empty placeholder** `TaggedPolynomial` appended to the
    array and linked in (`:264-272`).
  - At the end, an empty target node is materialized as best-ancestor × remaining monomial
    (`:274-278`; `setTaggedPolynomial`, `src/tagged-polynomial.inl:249-262`).
  - This is Remark 2.6's "usually one variable" made structural. Each lookup costs O(deg u) link
    follows and needs no hashing.
- **Every product goes through it.** That covers both pair halves (`appendMatrixF4`, `:510`, `:531`)
  and every preprocessing reducer (`:776`).
- **Write-back.** `postprocessing` (`:807-827`) loops over the first `nbPiv` matrix rows, the
  rows whose leading monomial was already a pivot. It writes reduced row `i` over the stored
  polynomial of **every** `_matPols` entry with that leading monomial (`:813-824`). The next lookup
  of any of those products, or of a product extending them, starts from the reduced row.
- **What makes the rows reduced.** `Matrix::echelonize` (`src/matrix.inl:641-934`, serial build)
  takes the whole matrix to reduced form.
  - It back-substitutes inside the left (pivot) block: the "Triangular part" loops at `:660-680`
    subtract reducer rows from other reducer rows.
  - After the lower-right block is echelonized, it clears the upper-right block against the new
    pivots (`:810-934`).
  - **Reducer-against-reducer work is therefore the price OpenF4 pays every batch** to have reduced
    rows to store.
- **No eviction.** `_taggedPolynomialArray` only grows during a computation. `_matMons` and
  `_matPols` are reset per batch, but the array is not (`src/ideal.inl:997`, `:1140-1145`,
  `:1175-1176`). Memory is one linked-list polynomial per product ever used, plus one placeholder
  per chain link, each with an `nbVariable`-int rule array.

Earlier studies found no full `Simplify` table in msolve or Groebner.jl. Sagebrush uses a
fewest-terms divisor choice, which is not a reuse table
([`sagebrush-implementation.md`](sagebrush-implementation.md) §2).

## 4. Interaction with Zeebra's F4

### 4.1 Shipping F4 never reduces a reducer row, so there is nothing to retain

- **Rows are products by construction.** A preprocessed row is `(multiplier, basis_index, kind)`
  (`src/grobner/f4/symbolic.rs:745-770`). Its terms are generated on demand by `shifted_terms`, one
  integer addition per variable per term (`:716-730`). There is no row kind for "a stored polynomial
  times a monomial". `Simplify` needs a third row source, and `Preprocessed`, the reducer-block
  invariant and matrix construction all read this two-kind shape.
- **The reducer block is never touched.** `ReductionStrategy::Structured` (`options.rs:37-50`,
  shipping since M16) places reducer rows first as a unit upper-triangular pivot block and reduces
  pair rows against it. The block "needs no discovering and no reducing against itself"
  (`src/grobner/f4/structured.rs:7-18`). #835 measured the consequence:
  `reducer_target_operations = 0` in the forward stage on every target. All 31.8 M (Eco-12) and
  26.3 M (MQ11) forward applications target pair rows (`m29-grobx-attribution.md` §2;
  `research/m29-c1/discovery-*.json.gz`, `work.forward`).
- **Only candidates are reduced.** `reduce_batch_rows` (`options.rs:851-865`) fully reduces
  *candidates*, the rows with new leading monomials (F̃⁺), against the batch pivots. "Unused
  inherited rows can retain echelon tails." Those candidates already join the basis.

So a Zeebra batch produces no reduced row with an *old* head term. Those are exactly the rows
`Simplify` stores (F̃ \ F̃⁺ in Faugère's notation, the `nbPiv` rows in OpenF4's). Adopting `Simplify`
therefore means **adding** reduction of the reducer block, in some form, to get rows worth keeping.

That within-batch operation has already been built and measured. `BlockPlan::InterreducedBlock`
(`structured.rs:66-72`) interreduces the reducer block so that "a pair row needs one subtraction per
reducer column instead of a chain of them". M16 §7.1.5 **rejected** it:

- On replayed batches it cost more row operations than the plain block on 17 of 23 instances, up to
  2.18× on katsura-4 grlex.
- It cost more peak nonzeros wherever the two differed.
- End to end it was slower almost everywhere: katsura-7 grlex 853.0 ms against 615.2 ms; katsura-6
  grlex 39.0 ms against 25.5 ms. "The denser basis elements it produces undo it."

`Simplify` changes that calculation in exactly one way: the cost is paid once per product and then
amortized over every later batch that needs the same product or extends it. Whether amortization
recovers a loss that InterreducedBlock showed inside one batch depends on recurrence (§5.1). It is
the question a prototype would have to answer, and nothing measured so far answers it.

### 4.2 `ReducerCache`, and why rows cannot be cached as rows

`ReducerCache` (`symbolic.rs:134-161`) exists and serves nothing. `CacheMode::Count`
(`:107-131`) records `(basis_index, multiplier)` repetition. M16 §7.2.3 then built and measured a
store of a multiple's **shifted terms**:

- The repetition rate was 29–95% (for example katsura-6 lex 95%, katsura-7 grevlex 64%).
- Serving from the store was still slower at every rate. Rebuilding a multiple costs one addition
  per variable per term, against a hash and a pointer chase to fetch it. On katsura-7 grevlex
  symbolic preprocessing went from 9.9 ms to 14.9 ms.

`Simplify` is not that cache, and that result does not reject it. What a `Simplify` hit saves is
**elimination work**, the products of reducing against a less-reduced row. A cache hit saves only
monomial additions. The same type comment marks the constraint any implementation inherits: a built
sparse row's column indices are relative to one batch's column set, so a retained row has to be kept
as `(monomial, coefficient)` terms and re-interned into each later batch's columns
(`symbolic.rs:141-144`). That re-interning is construction work the shipping path does not do for a
product. It is paid on every hit.

### 4.3 `ReducerSelection`

`ReducerSelection` (`options.rs:534-572`) chooses *which* divisor covers a monomial. Shipping uses
`FirstApplicable`, inherited from `baseline()` (`options.rs:914-934`, `:978-1001`).

- The M16 finding behind `LargestLeadingMonomial`'s rejection (`options.rs:539-549`) bears on
  `Simplify`. A reducer always leads with the covered monomial, so the choice only changes the
  row's **tail**, and a tail that is still reducible spawns more closure rows. On katsura-7 grevlex
  that took the largest matrix from 6810 × 6862 to 16750 × 16812.
- `Simplify`'s retained row has a tail reduced against every pivot of the batch that produced it.
  That is the opposite pressure. It is the plausible mechanism behind Joux–Vitse's smaller matrices.
- The two compose: selection picks `(i, u)`, then `Simplify` substitutes the retained form of
  `u·gᵢ` or of its longest stored ancestor.
- `FewestTerms` is a weak proxy for the same goal and needs no store. Sagebrush's choice is that
  proxy (§3).
- `PairMultiples::Distinct` (#831, `options.rs:53-61`) deduplicates on the exact
  `(basis_index, multiplier)` key. That key is still correct under `Simplify`, because two
  different keys map to two different stored chains.

### 4.4 Live-entry budgets, and where retained rows would be charged

- `max_live_nonzeros` and `max_live_bytes` (`options.rs:622-710`; 32 M entries and 512 MB in
  `recommended()`) bound **one batch's matrix** payload and nothing else. They do not bound the
  basis or any cross-batch state; the field doc lists the omissions and measures the gap at 75×.
- A retained-row store is cross-batch state. It would be a new unbudgeted resident set unless it
  got a budget of its own. Because eviction is always safe (§2.2), that budget can be strict: a
  byte cap with whole-store `clear()` or LRU, which never refuses a computation.
- Retained rows re-enter later batches as ordinary rows. Their entries are counted by the existing
  live budgets there, like any other row's.

**Size, derived from cited figures.** OpenF4 keeps one stored polynomial for every distinct product
ever used. On #835's serial runs:

| Target | Reducer rows built, all batches | Initial entries, all batches | Peak basis terms | Peak RSS (serial, whole process) |
|---|---:|---:|---:|---:|
| Eco-12 / 2⁶⁴−353 | 149,040 | 26,993,014 | 463,062 | 204 MB |
| MQ11 / Goldilocks | 49,833 | 36,569,205 | 1,225,359 | 398 MB |

Source: `research/m29-c1/discovery-{eco12-wide64,mq11-goldilocks}.json.gz`, binary from
`2fe11b8d` (`statistics.*`, `peak_rss_bytes`).

- The distinct-product count is **not** in these records: they ran with `reducer_cache: Off`, so
  `reducer_rows_reused` reads 0 by construction, not by measurement.
- The upper bound is every initial entry retained once at 16 bytes per entry
  (`statistics.bytes_per_entry`): **≈ 432 MB on Eco-12 and ≈ 585 MB on MQ11 (derived)**. That is
  2.1× and 1.5× each target's whole serial process peak. Reduced rows can also be denser than built
  ones; InterreducedBlock's fill-in is the measured precedent.
- At M16's 43–95% repetition the distinct set is much smaller. It is unmeasured on these targets,
  and measuring it is the first step of §6.2.

## 5. What #835's ledger implies

### 5.1 The gate as written is not met

#809's gate asks whether the ledger shows "substantial repeated reducer computation". It shows none,
because reducers receive no computation at all (§4.1). What the ledger does show:

- **88–89% of reduced pairs give zero, and those rows carry 93% of all coefficient work.** That is
  5.51 of 5.92 G products on Eco-12 and 18.92 of 20.38 G on MQ11 (§1–§2). `Simplify` does not
  change which pairs are reduced, so it cannot remove a zero row. It can only make each one cheaper
  to reduce.
- **Forward work against inherited pivots is 81.4% (Eco-12) and 75.4% (MQ11) of forward products.**
  Those are reducer rows built from basis elements of earlier batches: 4.54 of 5.58 G and 14.57 of
  19.33 G (`work.inherited_products`). This is the pool `Simplify` acts on.
  - Applying a reduced reducer row can shorten the pair row's chain, so it removes applications as
    well as products per application. #835 §2's sentence says only "the cost *per* application",
    which is narrower than the mechanism allows; InterreducedBlock is the measured case of chains
    shortening.
  - The zero row still has to be reduced across its whole width, which bounds the gain.

### 5.2 Ceilings already on record, and what they leave out

| Source | Eco-12 | MQ11 | Assumption |
|---|---:|---:|---|
| M29 cost model §5, C2-2 (`7251e775`) | −18.4% | −25.8% | **ceiling**: all inherited-pivot products removed at no cost |
| Derived from #835 §2 and §5 (post-#851 16-worker base) | −21.3% | −33.7% | the same ceiling on the later base: inherited share × forward ÷ process wall (0.814 × 808 / 3,088 and 0.754 × 2,558 / 5,716), assuming forward wall scales with products |
| #835 §5, rank 3 | ≤ −8% | ≤ −10% | half the inherited work removed, at today's efficiency |

What none of these rows charges or credits:

- **Charged nowhere: the cost of producing reduced reducer rows.** This is reducer-block reduction,
  the work InterreducedBlock measured as a net loss inside one batch (§4.1). It falls on the
  forward stage that the gain comes from, and it brings fill-in. The rank-3 estimate is therefore
  an upper bound on the net, not a midpoint.
- **Charged nowhere: re-interning retained rows.** It is construction work on every hit (§4.2).
- **Credited nowhere: a smaller symbolic closure.** Joux–Vitse's Katsura-12 matrices were 20–24%
  smaller per side than Magma's (§2.3). Symbolic is 990 ms of Eco-12's and 1,316 ms of MQ11's
  16-worker wall (#835 §5). This is the one upside the ranking omits. It is unmeasured on Zeebra,
  it could go either way, and it is cheap to measure (§6.2 step 1).

`Simplify` was ranked third in #835 with "low expected value", below parallel symbolic, and #836
closed with no C2 selected. Nothing here raises it above that. The missing costs push it down, and
the one missing credit is unmeasured.

## 6. Verdict: **defer**

**Deferred, not rejected.** The reasons are:

1. The gate is not met (§5.1). There is no repeated reducer computation to reuse, only repeated
   reducer *products*. `Simplify` would first have to add reducer reduction, which M16 measured as
   a net loss within a batch.
2. The work is dominated by zero rows, which `Simplify` cannot remove (§5.1). The mechanism that
   removes them is signatures. That is M31's subject (#900; `MILESTONE-COMPETITIVE-SIGNATURE-F4.md`).
3. M31 is changing the files a prototype would touch, `src/grobner/f4/symbolic*.rs` and the
   batch driver (`MILESTONE-COMPETITIVE-SIGNATURE-F4.md` §12, "File contention"). M31's gates are
   ratios against shipping F4-16. A trajectory-changing F4 option landing during M31 would move
   M31's denominator.
4. Memory: OpenF4's never-evicting store is of the order of the whole process peak on the wide
   targets (§4.4). Zeebra would need a new budget for it.

### 6.1 Evidence that would reopen it

*Revised by #1069.* The gate is the **counterfactual product census**. Recurrence alone does not
reopen this note. #1031's census (§7) found conditions (b)–(d) below formally met on current routes,
and (d) on 86 of 114 (row, engine) pairs, while a store of tail-reduced multiples cost more
elimination products than it saved on every pinned row but one. The conditions are necessary-looking
but not predictive, so they are now preconditions, and the census decides.

**Gate.** Reopen only when both of these hold:

1. **Precondition: recurrence.** At least one of conditions (a)–(d) holds, on shipping or on a
   successor default route.
2. **Decision: the counterfactual saves work.** On at least **two** of §6.2 step 5's wide targets
   (Eco-12, MQ11, MQ10, Katsura-11), on the same route, the census's *hits tail-reduced* arm saves
   **≥ 10% of elimination products net of upkeep**. Net means the arm 3 − arm 1 difference less
   the products spent tail-reducing the hit multiples
   ([`reduced-multiple-reuse-census.md`](reduced-multiple-reuse-census.md) §1). It is measured with
   `examples/reuse_census.rs` under `--features research-reuse`. The census's avoidable count is an
   upper bound on what a real store saves, so a figure below the bar cannot be rescued by a better
   store. A figure above it only admits §6.2, where wall time decides.

On #1031's figures (`f6cafd44`) the decision half holds on no target. The best pinned figure is
Eco-12 on the signature engine, which saves 5.2% gross and −56% net. The best dense-cohort figure is
1.4% net.

**Re-run the census only when an engine change alters its cost structure.** Recurrence moving is not
enough. Two changes qualify:

- **Reducer-block reduction becomes free.** For example, a full-RREF default or an elimination that
  reduces its reducer block anyway. Rows would then be tail-reduced without upkeep, and the upkeep
  column the census charges would no longer apply.
- **A pair-at-a-time organization.** An M4GB- or M5GB-style backend (#1030, #1032) applies stored
  rows to single reductions rather than to a batch's shared pivots. The census's batch replay does
  not predict that organization's products.

**Preconditions.** These are the original §6.1 conditions. The census labels them (a)–(d), and its
§4 gives the operational thresholds for "collapse" and "large reducer fractions".

- **(a) Reducer rows start receiving work.** A ledger, on shipping or a successor default route, shows
  `reducer_target_operations` that is a material share of forward products. Examples: a reducer
  interreduction route, a full-RREF default, or a sig-F4 elimination that reduces its reducer block.
  Rows would then be reduced anyway, and storing them costs only memory.
- **(b) The zero-row share collapses and inherited-pivot work dominates what remains.** Signature F4
  (M31) or #716-style pair pruning removes most zero reductions. A ledger on that route then shows
  inherited-pivot products ≥ 50% of process work, together with a `CacheMode::Count` repetition rate
  ≥ 50% on the same targets. A signature engine adds a constraint this note does not analyze: a
  retained row would also have to carry a signature compatible with `u·sig(f)`.
- **(c) The closure is the bottleneck.** A measured workload where reducer tails, rather than pair
  count, drive matrix size. Signs would be large reducer fractions per batch, as on MQ11 where late
  batches are > 90% reducer rows (`work.batches[].reducer_rows`), together with a symbolic stage
  ≥ 30% of wall.
- **(d) A dedicated measurement** (§6.2 step 1) shows a per-variable chain hit rate ≥ 50% on the
  pinned wide targets.

### 6.2 Prototype protocol, when reopened

0. **Isolation.** A research feature, outside any file a running milestone is modifying. Cross-batch
   state is passed explicitly, as `ReducerCache` is. The store is keyed `(basis_index, multiplier)`
   with Faugère / OpenF4 per-variable parent links. Rows are stored as terms, not columns. A byte
   budget with safe eviction is charged in its own statistic. **Null arm:** a store capped at zero
   bytes must reproduce shipping F4's trajectory and `basis_sha256` bit for bit.
1. **Gates, before any elimination change.** None of them changes anything computed. (a) and (b)
   use existing counters. (c) replays each batch under `--features research-reuse`.
   - (a) `CacheMode::Count` repetition on the pinned targets.
   - (b) An offline replay over a `--discovery` record that marks each reducer product whose
     `(i, m / xⱼ)` ancestor was built in an earlier batch. That is the `Simplify` hit rate Remark 2.6
     describes.
   - Stop if (a) or (b) is < 30% on the wide targets.
   - (c) The counterfactual product census of §6.1's gate. Stop unless the hits-tail-reduced arm
     saves ≥ 10% of elimination products net of upkeep on at least two wide targets. Gates (a) and
     (b) measure recurrence, which #1031 found high whatever the outcome. This gate is the one that
     decides.
2. **Arms.**
   - Shipping, which is `Structured` with an untouched reducer block.
   - Shipping with `Simplify` lookup and rows retained only where they are already reduced. On
     today's code that is the null arm.
   - Reducer block reduced (InterreducedBlock-style), with retention.
   - Reducer block reduced only for products the replay in step 1(b) predicts will recur.
3. **Per-batch counters.**
   - Rows, split pair / reducer / simplified.
   - Columns.
   - Initial and final nonzeros.
   - Reducer rows per batch.
   - Forward applications and products, split inherited / discovered.
   - `reducer_target_operations`, the new cost.
   - Store entries, bytes, hits and evictions.
   - Zero rows.
4. **Whole-run figures.**
   - Per-stage wall (symbolic, construction, forward, finishing, interreduction).
   - F4 call and process wall at 1 and 16 workers.
   - Peak RSS.
   - **Exact `basis_sha256` equality** with shipping, plus `certify` on the correctness corpus.
5. **Corpus.**
   - The M29/M31 pinned targets: Eco-12 / 2⁶⁴−353, MQ11 / Goldilocks, MQ10 / 32003 and 2³¹−1, and
     Katsura-11.
   - M16's classical instances where repetition was measured at 43–95% (§4.2).
   - Small controls (cyclic-5, katsura-6/7) for the regression bar.
6. **Timing discipline.**
   - Follow `docs/guide/benchmarking.md`: `benchlock`, interleaved arms in rotated order,
     n ≥ 5 at 16 workers.
   - Paired ratios against shipping F4-16 from the same build.
   - The commit is stamped beside every figure (`external-comparison-protocol.md` §10).
7. **Proposed adoption bar.** Set before measuring, and revisable only before then.
   - ≥ 10% process wall at 16 workers on at least two wide targets.
   - No control worse than 3%.
   - Peak RSS ≤ 1.25× shipping.
   - Bases identical everywhere.
   - Otherwise reject, and record the counters that explain why.

## 7. Addendum (#1031): the census on current routes — defer retained

[`reduced-multiple-reuse-census.md`](reduced-multiple-reuse-census.md) ran §6.2 step 1's free gates and
added the counterfactual they lack. Every batch was replayed with its reducer multiples as built,
all tail-reduced, and only the earlier-built ones tail-reduced. This ran on the conventional F4
defaults and the signature engine, over the M29 pinned rows and #1030's dense quadratic cohort.

- **Conditions.** (a) is met nowhere. (b) and (c) are met only on the signature engine for MQ10, and
  (b) also for Katsura-11. (d) is met on 86 of 114 (row, engine) pairs, as M16's recurrence predicted.
- **But a store of tail-reduced multiples is a loss.** It removes the fill-in chains, but its rows
  are longer, and the longer rows win. On every pinned row but one the hit-reduced arm costs 3–132%
  *more* elimination products before upkeep. The exception is Eco-12 on the signature engine: 5.2%
  saved gross, but −56% once upkeep is charged. On the dense cohort it saves at most 2.4%, and 1.4% net.
- **So §6.1's conditions are not predictive.** (d) passes where the counterfactual is negative.
  Before any §6.2 step 2 arm, the gate should be the counterfactual product census
  (`--features research-reuse`, `examples/reuse_census.rs`), not recurrence. §6.1 now says so
  (#1069).
