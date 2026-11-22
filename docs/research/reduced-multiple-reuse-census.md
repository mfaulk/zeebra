# Reduced-multiple reuse census on the current routes (#1031)

**Measured at:** `f6cafd44` (tag `measured/1031-reuse-census`), census binary `--features
research-reuse` (sha256 prefix `9bcbcb6bafebe6cc`) and timed binary `--features research-sigf4`
(`98e6ca5b3e66361e`), both `examples/reuse_census.rs`, one worker, 2026-11-22. Evidence:
[`research/1031-reuse-census/`](../../research/1031-reuse-census/README.md) (`runs.jsonl.gz`,
`tables.md`, `overhead.txt`).

This is #1031, the census #1030 and #1032 wait on. It measures whether Zeebra's own computation
repeats work that a store of tail-reduced reducer multiples (Faugère's `Simplify`, M4GB's store,
M5GB's signature-safe reductors) would remove, on the routes and workloads #809 did not ledger, and
marks each of [`simplify-reducer-reuse.md`](simplify-reducer-reuse.md) §6.1's four reopen
conditions. Nothing in the algorithm changed; every census run's basis digest equals its timed run's,
and the two engines' digests agree on every row.

**Verdict.** The hypothesis is **disproved** on both engines: on no dense overdetermined row does a
store avoid more than 2.4% of elimination products, and once the work to tail-reduce what it stores
is charged it saves at most 1.4% (conventional F4, m/n = 3) and is negative everywhere else.
Conditions (b), (c) and (d) are formally met on some rows, (a) on none (§4). **#1032 is not
supported; #809's defer is retained.** §6 records the follow-up filed because conditions are met.

---

## 1. What was measured

Each batch's elimination is replayed three times over the same pivots
(`src/grobner/reuse_census.rs`):

1. **as built**, which must reproduce the engine's own product count. It does, batch for batch, on
   all 114 (row, engine) pairs: the signature engine's `coefficient_products` exactly, and the
   conventional work ledger's forward products once its one-per-application charge for the pivot
   lead is converted out;
2. **all tail-reduced**: every reducer multiple first reduced against the batch's other reducers
   (under the signature bound only by reducers of smaller signature, which keeps its signature, so
   every target's admissible pivots are unchanged);
3. **hits tail-reduced**: only the multiples whose `(element, multiplier)` was built in an earlier
   batch, which is what a never-evicting store of tail-reduced multiples could serve.

No replay may move a target's leading term (conventional F4, whose forward pass stops at the first
unpivoted column) or its residual (signature F4, which clears every admissible pivot column); 0
mismatches. The arm 3 − arm 1 difference is the **avoidable** share. It is an upper bound on what a
real store saves: a stored row was reduced against its own batch's pivots, not the current one's.
The products spent tail-reducing the hit multiples in the batch are the **upkeep**. A batch whose
tail reduction passed 16× its as-built reducer products was abandoned, and its "bound" column
credits all of its reducer products as avoidable. That happened in 40 batches, 20 of them on the
two MQ10 rows under signature F4.

The per-key ledger gives `CacheMode::Count`'s repetition rate (asserted equal to
`reducer_rows_reused` in a test), the one-variable chain hit `(i, m/x_j)` of §6.2 step 1(b),
leading-monomial matches with a different key (and, under signatures, whether the earlier reducer's
signature is admissible wherever the current one is), reuse distances, and store sizes.

Products are multiply-accumulates past a pivot's lead. *Elimination products* are the replayed
reduction plus, on the conventional engine, the backward stage from its work ledger. Signature F4's
column-space interreduction is outside them on both engines.

### 1.1 Rows

- **Pinned:** Eco-12 / 2⁶⁴−353, Katsura-11 / 2³¹−1, MQ10 / 32003 and 2³¹−1, MQ11 / Goldilocks, as in
  `research/m29-c1/`.
- **#1030's development cohort:** dense quadratic, `m` equations in `n` variables, each monomial of
  degree ≤ 2 present with probability ½ under a support seed. Coefficients are uniform and nonzero,
  with a planted point. m/n ∈ {1.5, 1.8, 2, 3} as (12, 18), (13, 23), (14, 28), (14, 42), over
  GF(31), GF(32003), GF(2³¹−1) and GF(2⁶⁴−59), with three supports per cell: 48 rows. One
  unplanted control per ratio at GF(32003) adds 4 more.
- **Deviation:** the m/n = 3 rows run 55–271 ms, under #1030's 0.3 s floor. The example's largest
  variable count is 14, and the census is a count, not a timing.

## 2. Census table

From `research/1031-reuse-census/tables.md` (per row there). These are the shares of elimination
products. *Rep.* is `CacheMode::Count`'s repetition, *Chain* the exact-or-one-variable-ancestor hit
rate, and *Sym.* the symbolic share of the one-worker wall. *Heavy* is the share of products in
batches whose rows are ≥ 90% reducer multiples. Dense cells give the min–max over their 12 rows.

| Row | Engine | Zero-row | Inherited | Rep. | Chain | Sym. | Heavy | (a) | (b) | (c) | (d) |
|---|---|---:|---:|---:|---:|---:|---:|---|---|---|---|
| Eco-12 | f4 | 93.0% | 76.6% | 84.0% | 98.8% | 7.0% | 25.5% | no | no | no | **yes** |
| Eco-12 | sigf4 | 54.9% | 85.5% | 82.8% | 95.1% | 10.7% | 78.8% | no | no | no | **yes** |
| Katsura-11 | f4 | 93.1% | 63.3% | 79.2% | 97.7% | 4.8% | 38.5% | no | no | no | **yes** |
| Katsura-11 | sigf4 | 41.3% | 89.8% | 68.1% | 91.2% | 13.5% | 99.6% | no | **yes** | no | **yes** |
| MQ10 (both fields) | f4 | 91.0% | 49.4% | 73.2% | 98.9% | 6.9–7.2% | 10.0% | no | no | no | **yes** |
| MQ10 (both fields) | sigf4 | 45.5% | 97.1% | 72.9% | 99.0% | 32.8–33.0% | 99.7% | no | **yes** | **yes** | **yes** |
| MQ11 | f4 | 92.9% | 71.5% | 85.5% | 96.3% | 2.8% | 9.9% | no | no | no | **yes** |
| MQ11 | sigf4 | 51.5% | 89.3% | 60.6% | 81.3% | 4.5% | 22.6% | no | no | no | **yes** |
| dense m/n 1.5 | f4 | 76.2–76.3% | 36.0–36.3% | 35.3–35.4% | 66.3–67.1% | 1.4–3.0% | 0% | no | no | no | 12/12 |
| dense m/n 1.5 | sigf4 | 64.0–64.1% | 84.1% | 25.7–49.5% | 53.8–76.0% | 2.5–3.2% | 0% | no | no | no | 12/12 |
| dense m/n 1.8 | f4 | 52.2–52.3% | 32.8–33.1% | 44.0–44.1% | 60.0–61.2% | 3.8–4.9% | 0% | no | no | no | 12/12 |
| dense m/n 1.8 | sigf4 | 81.4–81.5% | 89.0–89.1% | 22.4–68.2% | 51.2–88.5% | 2.1–3.9% | ≤ 0.1% | no | no | no | 12/12 |
| dense m/n 2 | f4 | 58.1–58.3% | 28.8–29.0% | 36.3–36.4% | 57.1–58.3% | 2.5–3.3% | 0% | no | no | no | 12/12 |
| dense m/n 2 | sigf4 | 81.8–81.9% | 92.8% | 18.8–61.9% | 49.5–83.2% | 1.8–3.6% | 0% | no | no | no | 6/12 |
| dense m/n 3 | f4 | 35.8–36.6% | 28.9–29.6% | 27.1–27.6% | 27.1–31.2% | 6.2–7.7% | 0% | no | no | no | 0/12 |
| dense m/n 3 | sigf4 | 88.0–88.5% | 93.7–93.8% | 16.4–88.3% | 43.3–94.7% | 3.3–11.3% | ≤ 0.3% | no | no | no | 5/12 |

The unplanted controls fall inside their planted cells on every column except signature F4 at
m/n = 1.5, where they run 41.0% zero-row, 73.8% inherited and 80.7% chain. That does not change
any mark.

Two readings matter beyond the marks:

- **On dense overdetermined MQ the signature engine does not collapse the zero-row share. It
  raises it:** 81–89% of its products land on rows that end zero at m/n ≥ 1.8, against 36–58% for
  conventional F4. The extra equations give the signature engine targets whose syzygies only appear
  as zero rows. On the pinned rows it is the other way: 41–55% against 91–93%.
- **The best Zeebra route at one worker on that cohort is conventional F4**: 490–622 ms against
  925–1178 ms at m/n = 1.8, 818–1055 against 1414–1734 at 2, and 55–68 against 204–271 at 3. These
  walls are from the census campaign's timed runs, 12 concurrent (`runs.jsonl.gz`). They are not a
  timing claim, only which engine to census as "best".

## 3. Avoidable products, upkeep and store size

| Row | Engine | Hits, done | Hits, bound | All, done | Upkeep (hits) | Net (hits) | Store / peak RSS |
|---|---|---:|---:|---:|---:|---:|---:|
| Eco-12 | f4 | −65.0% | −64.6% | 6.0% | 52.8% | −117.3% | 4.63× |
| Eco-12 | sigf4 | 5.2% | 5.3% | 34.5% | 61.3% | −56.0% | 2.60× |
| Katsura-11 | f4 | −70.6% | −70.3% | −81.6% | 27.8% | −98.1% | 4.92× |
| Katsura-11 | sigf4 | −12.5% | −11.6% | −16.9% | 119.6% | −131.1% | 1.70× |
| MQ10 / 32003 | f4 | −132.1% | −131.6% | −78.5% | 30.9% | −162.5% | 4.85× |
| MQ10 / 32003 | sigf4 | −66.0% | −45.3% | 31.1% | 492.0% | −537.3% | 3.22× |
| MQ11 | f4 | −59.4% | −59.2% | −71.4% | 22.7% | −81.9% | 1.31× |
| MQ11 | sigf4 | −2.9% | −2.9% | −7.6% | 38.3% | −41.1% | 1.12× |
| dense m/n 1.5 | f4 | −10.9…−10.6% | same | −25.7…−25.2% | 1.1% | −12.0…−11.7% | 0.69–0.74× |
| dense m/n 1.5 | sigf4 | −1.3…−1.2% | same | −8.4…−8.3% | ≤ 0.6% | −1.9…−1.8% | 1.32–1.83× |
| dense m/n 1.8 | f4 | −4.5…−4.3% | same | −19.0…−18.3% | ≈ 4.2% | −8.6…−8.5% | 0.58–0.61× |
| dense m/n 1.8 | sigf4 | −3.2% | same | −7.7…−7.6% | ≤ 1.2% | −4.4…−3.3% | 1.20–1.76× |
| dense m/n 2 | f4 | −2.8…−2.5% | same | −16.7…−15.9% | 0.6% | −3.4…−3.1% | 0.59–0.69× |
| dense m/n 2 | sigf4 | −2.3…−2.2% | same | 2.0–2.2% | ≤ 0.5% | −2.7…−2.4% | 1.14–1.83× |
| dense m/n 3 | f4 | 2.1–2.4% | same | 1.0–1.8% | 1.0% | 1.1–1.4% | 0.13–0.16× |
| dense m/n 3 | sigf4 | −1.0…−0.8% | −0.8…−0.6% | 6.5–6.8% | ≤ 5.7% | −6.6…−0.9% | 0.66–1.22× |

MQ10 at 2³¹−1 matches MQ10 / 32003 except store / RSS (5.17× and 2.60×).

- **Tail-reduced multiples cost more to apply than they save.** A tail-reduced row has no entries in
  other reducers' leading columns, so it removes the chains of fill-in (the *secondary* products,
  up to 79% of elimination on MQ10 / sigf4). But it carries their tails, so each application is
  longer. On every pinned row and every dense cell but one the longer rows win. This is the batch-
  internal fill-in M16 §7.1.5 measured for `InterreducedBlock`, now measured across batches with
  reuse credited for free.
- **The one positive cell is conventional F4 at m/n = 3, at 2.1–2.4% gross and 1.1–1.4% net.** It
  sits under the 25% hypothesis by an order of magnitude. Those rows are also the 55–68 ms ones.
- **All-reduced is not a store.** Its larger figures (Eco-12 / sigf4 34.5%, MQ10 / sigf4 31.1% done
  and 51.8% bound) tail-reduce first-built multiples too, at an upkeep of 61% and 492% of
  elimination. Only the hit column is a store's saving.
- **Memory.** A never-evicting store of tail-reduced multiples peaks at 0.13–0.74× peak RSS
  (conventional) and 0.66–1.83× (signature) on the dense cohort, so it would fit #1031's 2× bound
  there, and at 1.12–5.17× on the pinned rows. LRU stores capped at 2× and 4× the largest
  tail-reduced reducer block seen so far never evicted. They kept 97–100% of hits and their peaks
  equal the never-evicting store's. So the cumulative store stays within about two batches' blocks,
  and eviction would not change the verdict.
- **Signature compatibility.** An exact hit has the same signature by construction. Leading-monomial
  matches with a different key are 0–3.5% of reducers. On the signature engine none of them carries
  an earlier signature no larger than the current one: when the least-ratio reducer for a monomial
  changes, the earlier reducer's signature is the larger one, so a stored row matching only the
  leading monomial is never admissible wherever the current one is (`lead_only`,
  `lead_only_admissible` in `runs.jsonl.gz`). The store's reach is the exact hits.

## 4. The four reopen conditions

Thresholds are §6.1's. "Collapse" is fixed as fewer than half the products on zero rows, and
"large reducer fractions" as ≥ 50% of products in batches whose rows are ≥ 90% reducers. Both were
set before reading the data, in `summarize.py`'s docstring.

- **(a) Reducer rows receive material work: not met anywhere.** `reducer_target_operations` is 0 in
  the conventional ledger's forward and backward stages on all 57 rows. The signature engine reduces
  targets only (`sigf4/engine.rs`, `eliminate`), so its reducer rows receive none by construction.
- **(b) Zero-row share collapses, inherited ≥ 50%, repetition ≥ 50%: met on 3 of 114 pairs.** These
  are signature F4 on Katsura-11 (41.3%, 89.8%, 68.1%) and MQ10 at both fields (45.5%, 97.1%,
  72.9%). Not on Eco-12 / sigf4 or MQ11 / sigf4, whose zero-row shares are 54.9% and 51.5%. Not on
  any dense row: the signature engine's zero-row share is 64–89%, and conventional F4's inherited
  share is ≤ 36%.
- **(c) Closure-bound, symbolic ≥ 30% of wall: met on 2 of 114.** Signature F4 on MQ10, at 32.8–33.0%
  symbolic with 99.7% of products in reducer-heavy batches. The dense cohort's symbolic share is
  1.4–11.3% and none of its batches is reducer-heavy.
- **(d) Per-variable chain hit rate ≥ 50%: met on 86 of 114.** That is every pinned row on both
  engines, and the dense cohort except conventional F4 at m/n = 3 and about half of signature F4's
  rows at m/n ≥ 2. Recurrence is real, as M16 found.

**Hypothesis** (#1031): at least one condition holds on dense m/n ≥ 1.8 under the best route, *and*
a tail-reduced store avoids more than 25% of elimination products. The first half holds on 23 of 48
(row, engine) pairs, all through (d). The second holds on none. The maximum is 2.4% (conventional
F4, m/n = 3), and on the signature engine the store is a loss on every dense row. **Disproved on both
engines.**

## 5. Decision

- **#1032 is not supported.** #1032's criterion asks the hypothesis to hold on at least one engine,
  and it holds on neither.
- **#809's defer is retained.** The note gains an addendum pointing here. Its §6.1 conditions are
  necessary-looking but not predictive: (d) is met almost everywhere, and the counterfactual product
  count is negative wherever it is. The free gates of §6.2 step 1 would have passed. The
  counterfactual this census adds is the gate that decides.
- **For #1030.** If an M4GB or M5GB reference wins on dense overdetermined MQ, the win is not from
  removing work Zeebra's batched engines repeat. In Zeebra's organization, tail-reduced multiples
  are net-negative per product. #1030's own transfer limit applies: a pair-at-a-time engine
  organizes reduction differently, and this census does not predict its wall time.
- **For #1016.** The repetition rate is not a useful early observation, because it is high whatever
  the outcome. The secondary-product share (fill-in chains) is the quantity a reuse scheme acts on,
  and it is visible in the first batches.

## 6. Overhead and follow-up

- **Overhead when off** (`overhead.txt`, n = 5, interleaved, medians). The census binary without
  `--census` against the `research-sigf4` binary gives ratios 0.975 and 1.009 (dense n14/m28/p64,
  conventional and signature F4), and 1.013 and 0.995 (MQ10 / 32003). That is within 5%, and within
  this machine's noise. The conventional hook is a batch observer in the example, so the shipping
  path carries no new code. The signature engine's is one `Option` test per batch under
  `research-reuse`. A census run replays each batch three times and is untimed.
- **Follow-up.** Conditions (b)–(d) are formally met, so #1069 was filed (Low) rather than closing
  the question silently. It covers revising #809 §6.1 to gate on the counterfactual product
  census, not on recurrence. Nothing was implemented.

## 7. Limits

- One worker. The symbolic share at 16 workers is larger, which could move (c). Mostly not, though:
  (c) also needs reducer-heavy batches, which the dense cohort does not have.
- The tail-reduced arm reduces against the current batch's pivots, which is optimistic for a store.
  A store that also simplified the pair rows, as `Simplify` does, is not modelled. Nor is
  re-interning stored terms, a cost a real store pays.
- The conventional backward stage (4.0–5.8% of elimination on the pinned rows) is kept as built in
  every arm.
- Supports at 50% density only. #1030's full-density cohort is not run here.
