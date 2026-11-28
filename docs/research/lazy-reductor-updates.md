# Lazy, signature-safe updates for a tail-reduced reductor store (#1197)

**Status:** done. **Recommendation: if a store is built, update lazily, keep a few batches, and
do not adopt M5GB's signature flags.** A lazy store does 17–35% of an eager store's updates, and
24–35% of invalidated entries are reused, so the stop rule (fewer than about 3% reused) is not met.
But lazy maintenance does not rescue the store. On these shapes, 96–100% of the tail-reduction work
on store hits falls on entries that were already stale, which is the upkeep #1031 charged, so
#1031's net-negative verdict stands. §5 states the signature-safety condition in the engine's
terms. It needs no flag, because Zeebra's column cascade clears a stale or blocked term wherever
the target admits a pivot for it.

**Measured at:** `ff333703`, `examples/reuse_census.rs --census` built with `--features
research-reuse` in release, thin LTO and 16 codegen units (sha256 prefix `e337e31dd088`), one
worker, macOS arm64 (14 cores), unpinned, 2026-11-27. The figures are counts, which are
deterministic, so the profile and the machine do not change them. The wall and RSS figures in §2
only show that each run fits on a laptop. Evidence:
[`research/1197-lazy-store/`](../../research/1197-lazy-store/) (`runs.jsonl.gz`, `tables.md`,
`summarize.py`, `run.sh`).

Parent: #1031's census ([`reduced-multiple-reuse-census.md`](reduced-multiple-reuse-census.md)).
Store owners: #1198 and #1032. Source: Hauke, Lamster, Lüftenegger and Rechberger (M5GB,
arXiv:2208.00844, the same text as ePrint 2022/987), read in full from its arXiv LaTeX source: §3,
Algorithm 3 and Lemma 1, and §2.2's account of Makarim and Stevens' lazy M4GB variant. The M4GB
paper itself was not read here. Everything is re-derived, with no code from either.

---

## 1. What was counted

The #1031 census replays each batch with the reducer multiples tail-reduced. This note adds a
ledger (`StoreLedger` in `src/grobner/reuse_census.rs`) for a hypothetical never-evicting store of
those tail-reduced multiples, keyed `(element, multiplier)` as `CacheMode::Count` keys them. Both
engines' census hooks pass the batch's column monomials and every basis lead.

- **Stored entry.** Every reducer multiple after the census's tail reduction. Its *irreducible
  tail* is the tail terms at columns with no pivot (no reducer, and no target leading there). In a
  conventional F4 matrix both halves of an S-pair are targets, so their lcm column is reducible
  with no reducer. Those terms are counted apart (`unreduced_terms`). Under the signature bound,
  tail terms whose pivot has a larger signature stay in the row. These are *blocked* (M5GB's
  finite signature flag).
- **Invalidation.** A lead that joined the basis after the entry was built divides one of its
  irreducible tail terms. The entry goes from valid to stale. That starts an *episode*, which ends
  either in a *stale hit*, when the key is built again (one lazy update), or at the end of the run.
- **Eager.** An eager store updates every stale entry. *Eager (lower)* counts episodes, because each
  costs an eager store at least one update. *Eager (rounds)* counts the (entry, round) pairs in
  which a new lead hits the tail as last built, which is M4GB's original proactive policy at batch
  granularity. Per-element eagerness would cost more, so both columns are generous to eager.
- **Lazy.** Stale hits. A valid hit costs a lazy store nothing. The products the census spends
  tail-reducing a stale hit in its batch bound the update's work from above, because an
  incremental update only has to reduce the newly reducible terms.
- **Checks.** Every exact hit is valid or stale. Episodes equal stale hits plus episodes still open
  at the end. No stored irreducible term was already divisible by an earlier lead (`born_stale` =
  0, which checks that every reducible column had a pivot). Residual mismatches are 0, and the
  signature engine's replay matches its live product count. Every census basis digest equals the
  other engine's on the same row. All of these hold on every run (`tables.md`, "Checks").

Rows: #1031's dense quadratic generator (`dmq-…`, each monomial of degree ≤ 2 kept with
probability ½, planted). The shapes are the issue's (14, 25) and (16, 29), the held-out shapes of
#1030 §9, and n = 18 at the same m/n ≈ 1.8, (18, 32). (14, 25) was run on two seeds and two fields
to show the ledger counts depend on shape. They differ by at most 0.3% across seed and field, the
same independence M4GB's counters showed in #1030 §9. The product counts move more, up to 8% at
GF(32003) (`tables.md`).

## 2. Eager against lazy update work

GF(31), seed 1. *Reused* is stale hits over episodes. *Lazy / eager* is lazy over eager (rounds)
and lazy over eager (lower). *+ flagged* adds valid hits on an entry with a blocked term (§5.3).

| Row | Engine | Batches | New leads | Stored | Exact hits | Valid hits | Episodes = eager (lower) | Eager (rounds) | Lazy | Lazy / eager | Lazy + flagged | Reused |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| (14, 25) | f4 | 8 | 913 | 3 492 | 1 459 | 518 | 2 670 | 2 679 | 941 | 0.35 | 941 | 35.2% |
| (14, 25) | sigf4 | 5 | 893 | 5 021 | 1 179 | 222 | 3 805 | 4 690 | 957 | 0.20–0.25 | 1 162 | 25.2% |
| (16, 29) | f4 | 8 | 1 831 | 7 135 | 2 241 | 809 | 5 851 | 5 861 | 1 432 | 0.24 | 1 432 | 24.5% |
| (16, 29) | sigf4 | 5 | 1 806 | 9 702 | 2 111 | 272 | 6 417 | 7 743 | 1 839 | 0.24–0.29 | 2 096 | 28.7% |
| (18, 32) | f4 | 9 | 4 039 | 18 019 | 7 153 | 3 048 | 13 166 | 20 461 | 4 105 | 0.20–0.31 | 4 105 | 31.2% |
| (18, 32) | sigf4 | 6 | 4 011 | 23 151 | 5 772 | 732 | 21 343 | 28 809 | 5 040 | 0.17–0.24 | 5 748 | 23.6% |

Per new lead, and the work in products:

| Row | Engine | Episodes per new lead | Stale share of exact hits | Stale hits 0 / 2 / 3–4 rounds after invalidation | Stale-hit tail products | Share of all hit tail products | Share of elimination products |
|---|---|---:|---:|---|---:|---:|---:|
| (14, 25) | f4 | 2.92 | 64.5% | 941 / 0 / 0 | 33.0 M | 96.3% | 0.97% |
| (14, 25) | sigf4 | 4.26 | 81.2% | 957 / 0 / 0 | 10.9 M | 100% | 0.85% |
| (16, 29) | f4 | 3.20 | 63.9% | 1 432 / 0 / 0 | 126.9 M | 97.8% | 0.54% |
| (16, 29) | sigf4 | 3.55 | 87.1% | 1 839 / 0 / 0 | 10.0 M | 100% | 0.10% |
| (18, 32) | f4 | 3.26 | 57.4% | 3 230 / 209 / 666 | 537.4 M | 96.9% | 0.38% |
| (18, 32) | sigf4 | 5.32 | 87.3% | 5 040 / 0 / 0 | 448.2 M | 100% | 0.33% |

Census run cost, to show the rows fit a laptop (an untimed replay, not a timing claim):

| Row | f4 wall | f4 peak RSS | sigf4 wall | sigf4 peak RSS |
|---|---:|---:|---:|---:|
| (14, 25) | 24 s | 175 MiB | 10 s | 90 MiB |
| (16, 29) | 182 s | 544 MiB | 85 s | 304 MiB |
| (18, 32) | 1 036 s | 1 586 MiB | 1 054 s | 1 446 MiB |

What the tables say:

- **Lazy does a sixth to a third of eager's updates, on every row and both engines.** Eager does
  2.8–5.7× lazy's updates. Most invalidated entries (65–76% of episodes) are never built again, so
  an eager store spends most of its updates on rows nobody reads. That is M4GB's argument for the
  lazy variant, and it holds in Zeebra's batches. Eager (rounds) exceeds eager (lower) because an
  entry can be hit in several rounds before it is reused or dropped. That gap is 0.3% under
  conventional F4 at n ≤ 16 and 55% at n = 18, and 21–35% under the signature engine.
- **Not a stop record.** 24–35% of episodes end in a reuse, an order of magnitude above the issue's
  "a few percent". Lazy does not degenerate to "never update".
- **Reuse is almost always one batch later.** At n ≤ 16 on both engines, and at n = 18 on the
  signature engine, every exact hit was built in the previous batch (#1031's `reuse_distance` =
  [hits, 0, 0, 0, 0]), and every stale hit was reused in the first batch after its invalidation.
  So an entry is built in batch b, made stale by batch b's new leads, and either rebuilt in batch
  b + 1 or never again. The exception is conventional F4 at (18, 32): 875 of its 7 153 hits (12%)
  come 3–4 batches back. They land in the run's last two batches (7 and 8), which come after the
  last new leads and rebuild keys built 3–4 batches before. All 875 are stale.
- **Most hits are stale: 57–65% (conventional) and 81–87% (signature).** The new leads from batch b
  land squarely in the tails of batch b's multiples. That is expected on dense rows, whose tails
  cover most of the staircase's boundary.
- **The upkeep #1031 charged is the lazy upkeep.** 96–100% of the tail-reduction products spent on
  hits were spent on stale ones, and a valid hit's built row needed almost no tail reduction.
  #1031's "upkeep (hits)" column charged every hit's tail reduction, so on these shapes it already
  prices a lazy store, and a lazy policy recovers at most the remaining 0–4%. #1031's rows (the
  same generator at n ≤ 14) were not re-run here. On the shapes that were, nothing moves #1031's
  verdict (net negative on every dense row but conventional F4 at m/n = 3).

## 3. Reading against M4GB's counters

M4GB's store peaks at 11 213 entries at (14, 25) and 19 197 at (16, 29) (#1030 §9). Zeebra's
census store holds 2 033 and 4 894 distinct keys on the conventional engine at the same shapes
(`distinct_keys`), and 3 842 and 7 591 on the signature engine. At (18, 32) it holds 10 866 and
17 379. M4GB keeps a multiple for every reducible monomial it ever reduces, and Zeebra's matrices
hold multiples only for the columns of one batch. The
counts are not comparable as a store size. M4GB's log has no hit counter, so its reuse fraction
remains unknown, and these figures are Zeebra's computation only, which is #1030's transfer limit.

## 4. Recommendation to the store owners (#1198, #1032)

1. **Update lazily.** The counts favour it 2.8–5.7× over eager, with no case for eager on any row.
2. **Keep the previous batch, plus a few on the conventional engine.** One batch back holds 100% of
   the hits on five of the six rows and 88% at (18, 32) under conventional F4, where the rest come
   3–4 batches back. A one-batch store is #1075's adjacent buffer shape. #1031's LRU, capped at
   2× the largest tail-reduced block, keeps all 7 153 of those hits at (18, 32) (`lru` in
   `runs.jsonl.gz`).
3. **Use the generation test of §5.2, not a full rescan.** A stored entry carries the basis length
   at build, and an entry is updated when the basis has grown since. The generation test flags
   92–94% of hits under conventional F4 at n ≤ 16, 69–82% at (18, 32), and all of them under the
   signature engine. Against that, 57–65% and 81–87% of hits are actually stale (`tables.md`,
   "Generation test"). That is cheap and only mildly conservative.
4. **Do not expect lazy updating to change #1031's verdict.** The upkeep a lazy store pays is what
   #1031 charged. If #1198 or #1032 builds a store, its benefit must come from elsewhere (#1198's
   dense tails over irreducible monomials, for instance), not from deferring updates.

## 5. The signature-safety condition in the engine's terms

### 5.1 M5GB's condition

M5GB processes one row at a time in increasing signature `s`. It reduces with stored reductors
`m` that satisfy two conditions (Algorithm 3, Lemma 1). First, `Sig(m) < s`. Second, `m` is
*Sig-tail-irreducible up to `s`*: no tail term of `m` is the lead of a multiple `v·g` with
`Sig(v·g) < s`. The second condition has two ways to fail. **(1)** An element added after `m`'s
generation regularly tail-reduces it. This is the generation test. **(2)** A tail-reductor that
already existed but was inadmissible when `m` was built (`Sig(v·g) ≥` the signature then) becomes
admissible because `s` has grown. This is the signature flag: `Flag(m)` is the least signature of a
tail-reductor of `m`, and `m` is updated when `Flag(m) < s`. M5GB tail-reduces `m` with reductors
of signature below `s`, the *served* row's signature, so the stored `m'` can carry a signature
above the multiple's own, which stays below `s`.

The condition exists because M4GB-style reduction visits each term once (M5GB Lemma 1). A reductor
with a reducible tail term would leave that term in the result unreduced.

### 5.2 In Zeebra

The engine (`src/grobner/sigf4/engine.rs`) uses Schreyer shifted signatures (`<lt-pot`) and one
batch per signature degree. Each column's reducer is the least-ratio element whose lead divides it
(`reducer`, `least_ratio`), which is the multiple of least signature with that lead. A target of
signature τ applies a pivot only if the pivot's signature is strictly below τ (`ReducerBlock::admits`).
A target whose lead's reducer has signature exactly τ is singular (`classify`, EF Lemma 5.1). A zero
row records τ as a syzygy signature. Targets are selected through the Koszul and zero-row syzygy
criteria (`reject_by_syzygy`) and the canonical rewriter, the element of greatest ratio
(`rewriter`).

A stored entry is `R' = u·g − Σ c_j r_j`, built in batch b, where every `r_j` is a batch-b reducer
with `sig(r_j) < sig(u·g)` (the census's rule, `rr[j] < rr[k]`). Hence **`sig(R') = u·sig(g)`
and `lead(R') = u·lead(g)`**: tail reduction by strictly smaller signatures changes neither.

**Condition.** In a later batch, `R'` may stand in for the reducer at column `m` of target τ when
all three of the following hold.

- **(A) `u·sig(g) < τ`.** This is the engine's own `admits` test on the multiple, unchanged. Every
  operation `T − c·R'` is then a combination of rows of signature below τ, which is a regular
  reduction (Lairez Algorithm 8 line 98 permits exactly these).
- **(B) The engine's own reducer at `m` in this batch is `(g, u)`, i.e. an exact hit.** `classify`
  decides singularity against the signature of the block's reducer at the target's lead column. A
  stored row of another signature at that column could turn a singular row (to be discarded) into a
  new element, or the reverse. The least-ratio choice is also what keeps reducer signatures
  minimal, so a superseded key admits fewer targets. #1031 measured that no lead-only match on the
  signature engine is admissible wherever the current reducer is, so (B) loses no reuse.
- **(C) Symbolic preprocessing closes over `R'`'s terms, not over `u·g`'s.** A stale term (one a new
  lead divides) or a blocked term then gets its own column and reducer, and the column cascade
  clears it in the target wherever (A) admits that reducer. Without (C), a stale term can survive
  in a target, and if the higher columns cancel it becomes the target's lead. The new element is
  then top-reducible, which `check_new_element` rejects ("a new element must be regular
  top-irreducible and not singular").

**What (A)–(C) leave out, and why.**

- *Tail-irreducibility is not a safety condition here.* With (C), every term a stale `R'` brings
  into a target has a column carrying its least-signature reducer. The target's result is then
  regular top-irreducible with respect to every multiple of signature below τ, so its lead is the
  one τ determines. That is the engine's own argument (EF Lemma 4.10, cited at `eliminate`). Only
  the result's tail can differ from the plain multiple's, and interreduction removes that.
  Staleness costs secondary products and columns but never correctness. This is the one place
  Zeebra differs from M4GB and M5GB, whose reduction routine has no closure and so needs
  tail-irreducibility to be correct. In Zeebra, the lazy update is an optimization, never an obligation.
- *The syzygy criterion is unaffected.* It acts on targets at selection, and `symbolic` picks
  reducers through `reducer` alone, never consulting the syzygy store. `R'` carries `u·g`'s
  signature, so a syzygy signature recorded after `R'` was built changes nothing a plain multiple
  would not.
- *The rewrite criterion is unaffected.* It chooses which pair half becomes a target (`rewriter`),
  and the stored rows are reducers.
- *Generations.* M5GB's case (1) is the §1 invalidation, exactly. The cheap test is M4GB's:
  record `|G|` at build and treat an entry as possibly stale when `|G|` has grown (§4 item 3).

### 5.3 M5GB's signature flag in Zeebra

Under the signature-preserving rule, blocked terms stay in `R'`. They occur in **98.5–99.6% of the
signature engine's stored entries** (731 241 terms at (14, 25), 3.16 M at (16, 29), 15.2 M at
(18, 32)). Batches are taken from a queue keyed by signature degree, lowest first, and `<lt-pot`
under grevlex compares degree first. So a target in a batch of higher degree has a larger signature
than every row of an earlier batch, including the blocking pivot. M5GB's flag test would therefore
fire on essentially every reused entry. The *+ flagged* column counts that: 1 162, 2 096 and 5 748
updates, 99–100% of all exact hits.

Zeebra does not need them, by (C): a blocked term's reducer is in the batch, and the target clears
it where (A) admits it. An M5GB-style update would instead tail-reduce `R'` with reductors of
signature up to the smallest target that uses it. That raises `R'`'s signature to the largest
reductor applied, and `admits` and `classify` would then have to use the raised signature. That
breaks (B), because the column's reducer signature would no longer be the engine's. **Recommended
rule: tail-reduce stored rows only by strictly smaller signatures, keep the multiple's signature,
and carry no flag.**

This argument is written for review before any code, as the issue asks. It was checked against the
engine's code paths named above, not by a prototype.

## 6. Limits

- One store model: never evicting, keyed exactly, tail-reduced against the batch it was built in
  (#1031's optimistic arm). The eager (rounds) count tests the tail as last built. After an eager
  update the tail changes, so that column can be off in either direction. Eager (lower) and lazy
  are exact for the model.
- Half-density supports only, one seed per shape at n ≥ 16, one field at n ≥ 16. n = 18 was run
  at (18, 32), m/n ≈ 1.8 like the other two shapes, not at #1198's (18, 36).
- Counts, not time. An eager or lazy store's wall cost was not measured, and the issue asked for no
  prototype.
