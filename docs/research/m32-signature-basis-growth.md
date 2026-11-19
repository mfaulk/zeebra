# M32-S3: signature-basis growth and bookkeeping (#936)

**Status:** complete, 2026-11-19. **Gate G fails** (§6): every sound option projects ≤ 3.1% of
Eco-12's 16-worker wall, and Cyclic-7 cannot reach conventional F4 even with bookkeeping at zero.
**Measured at:** `3d46b15f`, tag `measured/936-sig-basis-growth` (the `research-sigf4-usage` instrument; binary sha256 prefix
`6c8c489798fbb6d6`), one worker pinned to CPU 2, under `tools/benchlock.sh` tag `936-usage`
(2026-11-19T09:10, load 10.4 from builds elsewhere). Raw output:
[`research/m32-outgrowth/`](../../research/m32-outgrowth/). **Counts** are algebraic and do not
depend on workers or load. **Timings** are single runs of an instrumented binary and are
estimates; the 16-worker stage figures are quoted from the M31 final cohort at `8715c8ed`
([`tables.md`](../../research/m31-final/tables.md); plan §2.2).
**Plan:** [`MILESTONE-ADAPTIVE-F4.md`](../MILESTONE-ADAPTIVE-F4.md) §4.1 (H5), §7.4, §8.2 (Gate G).
**Prior work:** [`signature-f4-rfc.md`](signature-f4-rfc.md), M31 §15.8.

## 0. Summary

- **The outgrowth is the minimal signature basis, and none of it can be discarded.** The engine
  rewrites by the greatest sig-lead ratio, so it computes the unique minimal signature Gröbner
  basis for the Schreyer order, which every signature basis contains (EF Lemma 4.13, Corollary
  7.20). The basis sizes 1,885 / 3,083 / 585 belong to the module order, not to the
  implementation. On every row the essential elements (no other lead divides theirs) are
  exactly the reduced basis: 743 / 209 / 247.
- **The dominated elements are heavily used.** On Eco-12, the 1,142 dominated elements are the
  source of 38.9% of reducer rows and 53.8% of targets. 1,069 of them are the canonical rewriter of
  some signature. One element out of 1,885 was never consulted. On Cyclic-7 the dominated elements
  are the source of 82% of reducer rows.
- **The bookkeeping cost is the eager Koszul store, not the elements as such.** On Eco-12 the engine
  makes 1,775,561 Koszul inserts (one per pair). Replaying the store calls on their own takes
  125 ms, and 50 ms without the Koszul inserts (§3). Of those inserts, 1,273,263 are provably
  no-ops. Skipping them is exact but saves only 17 ms, because the expensive inserts are the
  ones that are kept.
- **Sound options and what they would save on Eco-12 at 16 workers:** query-first Koszul
  insertion (exact) about 19 ms, incremental essential tracking instead of the final
  minimal-basis selection about 35 ms. Together that is 54 ms, **3.1%** of 1,744 ms, below the 5%
  bar. Roune–Stillman's lazy Koszul queue is sound and bounded at 6.8%, but only if 95,207 lost
  eliminations cost nothing. That is unproven for this engine, and about 0.1% of them reaching
  reduction would erase the gain (§5.1).
- **Cyclic-7 cannot be made dispatch-eligible this way.** Forced through the engine at 16
  workers it takes 0.669 s against conventional F4's 0.145 s. With bookkeeping and interreduction
  both at zero it would still take 0.279 s, 1.92× conventional.
- **Side finding (MQ10, not part of the gate):** the last essential element is added in batch 57
  of 65. The seven batches after it (degrees 8–10) add seven dominated elements and take 35% of
  the engine's stage time at one worker (161 of 457 ms). The 2-target degree-10 batch alone spends
  54 ms in symbolic preprocessing. Stopping early once the polynomial basis is complete (F5B/F5+,
  EF §10.2; RS Appendix B.4) is the only published way to skip work done on dominated elements.
  Filed as #946 (§7).

## 1. Sources

| Key | Source | Read |
|---|---|---|
| **EF** | Eder, Faugère, *A survey on signature-based Gröbner basis computations*, arXiv 1404.1774 | §4.1–4.2, §5, §7 (Def 7.1–7.4, Lemma 7.5, 7.11, 7.19, Cor 7.20), §10.2, §13 |
| **RS** | Roune, Stillman, *Practical Gröbner basis computation*, ISSAC 2012, arXiv 1206.6940 | §3.2–3.5, Theorem 6, Appendix B.1–B.4 |
| **Lz** | Lairez, *Axioms for a theory of signature bases*, arXiv 2210.13788 | Thm 62 / Algorithm 8, as the engine cites it (`sigf4/mod.rs`) |

## 2. The instrument

`--features research-sigf4-usage` (`src/grobner/sigf4/usage.rs`, hooks in `engine.rs` and
`examples/sig_f4_study.rs`) records the following:

- for each element: reducer rows built from it, target rows built from it, kept pairs in which
  it is the smaller half (only its signature and lead are read), and the times the rewrite
  criterion returned it;
- the batch from which another element's lead divides its lead (equal leads: the earlier element
  wins), and the matrix rows built from it after that batch;
- every syzygy-store call in order, replayed after the run (§3).

No engine decision reads the log. Every row's basis digest matches the uninstrumented engine's
(Eco-12 `3bf17412…`, Cyclic-7 `afd9a87c…`, MQ10/32003 `ccee8a56…`, MQ10/2³¹−1 `deb2802f…`).
The hooks inflate bookkeeping: 368 ms on Eco-12 at one worker, against 231 ms uninstrumented in
M31. For that reason no stage time from this binary is used directly. §5 uses the replays, which
time only the store, and the M31 stage clocks.

## 3. Counts: who is consulted

| | Eco-12 / 2⁶⁴−353 | Cyclic-7 / Goldilocks | MQ10 (both fields) |
|---|---:|---:|---:|
| signature-basis elements | 1,885 | 3,083 | 585 |
| essential (= reduced basis; = minimal-basis selection) | 743 | 209 | 247 |
| dominated / of which dominated at birth | 1,142 / 854 | 2,874 / 2,651 | 338 / 335 |
| never consulted in any role | 1 | 0 | 0 |
| dominated, terms read after domination | 1,087 | 2,720 | 337 |
| reducer rows: total / from dominated | 76,936 / 29,932 (38.9%) | 24,907 / 20,482 (82.2%) | 78,178 / 15,903 (20.3%) |
| target rows: total / from dominated | 2,886 / 1,554 (53.8%) | 3,204 / 2,917 (91.0%) | 770 / 417 (54.2%) |
| dominated elements that won a rewriter query | 1,069 | 2,874 | 336 |
| term entries: total / dominated / never read after domination | 1.051 M / 68.0% / 4.9% | 0.600 M / 95.0% / 6.7% | 0.175 M / 61.4% / 0.2% |
| rewriter calls; same-index entries scanned per call | 13,051; 218 | 15,777; 527 | 3,170; 75 |
| pairs created = Koszul inserts | 1,775,561 | 4,749,349 | 170,725 |
| store queries; answered by a Koszul entry | 1,440,934; 597,883 | 4,708,010; 3,170,652 | 120,039; 81,993 |
| of those, equal to a generated Koszul signature | 423,925 | 1,583,806 | 46,663 |
| neither equal nor covered by a zero-row syzygy ("lost" under a lazy queue) | 95,207 | 365,779 | 23,907 |
| Koszul inserts that are provable no-ops (query-first) | 1,273,263 | 4,478,326 | 100,885 |
| peak pending signatures | 94,921 | 105,516 | 11,061 |

Store replay at one worker (best of three, ms; the second figure in each Eco-12 cell is the run
at `637773db`, the same store code):

| | Eco-12 | Cyclic-7 | MQ10/32003 |
|---|---:|---:|---:|
| as recorded (eager Koszul) | 125.0 (119.3) | 168.4 | 6.9 |
| query-first, provable no-op inserts skipped (store contents identical, every answer checked) | 108.4 | 151.1 | 6.3 |
| without any Koszul insert (zero-row syzygies and queries only) | 49.5 (42.9) | 90.0 | 2.9 |
| minimal-basis selection on the whole signature basis (part of the interreduction stage) | 35.7 (31.1) | 19.4 | 4.6 |

## 4. Which elements could be discarded, stored compactly or kept lazily

**Discarding: unsound, and not available even in principle.** `rewriter` returns the element of
greatest sig-lead ratio. That is EF's ⊴rat (Def 7.13), and with it RB computes a *minimal*
signature Gröbner basis (EF Lemma 7.19, Cor 7.20). By EF Lemma 4.13 the minimal basis is unique and
contained, up to sig-lead pairs, in every signature Gröbner basis. Remove an element `g` and the
remaining set is not a signature Gröbner basis in signature `s(g)`. Lz Thm 62 and EF Thm 4.9 both
require one up to the current signature for every later batch. The counts confirm this: Eco-12's
dominated elements supply 39% of reducer rows, and every dominated Cyclic-7 element is somebody's
canonical rewriter.

Pairs whose generator is dominated (EF §10.2's "F5-critical" pairs) cannot be dropped either. A
rewrite can discard the corresponding GB-critical pair, and then the F5-critical pair is the one
that carries the correctness argument (EF §10.2, F5+). The only published way to skip work on
dominated elements is to **stop early** once the polynomial basis is complete. RS Appendix B.4
does this with a side Buchberger computation, F5B and F5+ with a chain-criterion degree bound
(EF §10.2). RS report a 30× gain on yang1, a 17× loss on katsura11, and nothing on hcyclic8. On
Eco-12 the last essential element arrives in the final batch (§3), so early stopping has nothing to
skip there.

**Compact storage of terms: memory only, and only in hindsight.** A dominated element's terms
are needed again whenever it becomes a reducer or a target, and only 4.9% of Eco-12's term
entries (51,803 × 56 bytes ≈ 2.9 MB) are never read after domination. That set is known only
once the run has finished. Freeing terms early would need a predicate that proves no future
read, and none is published. Not pursued.

**Query-first Koszul insertion: exact.** For a pair of signature `T` with Koszul signature `K`,
`T | K` holds (RS §3.3 uses it: "T | s(S(i,j)) | s(K(i,j))"). Both maxima compare the same two
sig-lead ratios, so they pick the same element `α`. `T = (lcm/lm(α))·s(α)`, and `lcm/lm(α)`
divides the other lead, which is the factor `K` applies to `s(α)`. If a
stored syzygy covers `T` it also covers `K`, so `SyzygyStore::insert(K)` is a no-op and can be
skipped. Checking `T` before inserting `K` changes an answer only when `K` covers `T`. Given
`T | K`, that requires `K = T`, which means coprime leads, and the product criterion has already
rejected those pairs. The replay checks every query answer against the recorded order, and
none changes. No obligation remains.

**Incremental essential tracking: exact.** The minimal basis is the set of essential elements,
one per distinct essential lead. `insert` already visits every older element with both leads in
hand, so one divisibility test per pair maintains the essential set. The final
`minimal_basis_for_interreduction` then becomes a filter. The output is unchanged because the
minimal basis's leads are determined and interreduction yields the unique reduced basis.

**Lazy Koszul queue (RS §3.3): sound, but its gain is not established.** It is sound because the
criteria only eliminate. EF Thm 4.9 and Lz Thm 62 need every regular S-pair that is not
eliminated to be s-reduced, and they never need a pair to be eliminated. A pair that a weaker
criterion lets through reduces to zero or to a singular row. It adds no element (EF Lemma 7.19),
the basis stays the unique minimal one (EF Lemma 4.13), and the output stays the unique reduced
basis. Its *cost* is open. A lazy queue keeps an elimination only when `T` equals a Koszul
signature, so 95,207 Eco-12 queries lose their syzygy hit. RS Theorem 6 says SB reduces no
S-pair at such signatures, but that is a theorem about SB's own loop. It is not proved here for
batched F4-RB with this rewriter, and §5.1 shows that the projection depends on it entirely.

## 5. Cost model

### 5.1 Eco-12 / 2⁶⁴−353 (M31: 16-worker entry wall 1,744 ms; bookkeeping 231 ms at 1 w, 259 ms at 16 w)

Bookkeeping and the minimal-basis selection are serial, so a one-worker saving carries over to 16
workers. M31's bookkeeping grows 1.12× from 1 to 16 workers (plan §2.2), so the projection scales
by 1.12 as well. These are estimates, not measurements of a prototype.

| Option | Soundness | 1-w saving (replay) | 16-w projection | of 1,744 ms |
|---|---|---:|---:|---:|
| A. query-first Koszul insertion | exact | 16.6 ms | 19 ms | 1.1% |
| B. incremental essential tracking (replaces 35.7 ms selection; costs ~1.78 M extra divisibility tests, ≈ 5 ms at an assumed 3 ns each; the 1.12 scaling flatters it, as interreduction does not grow with workers) | exact | ≈ 31 ms | ≈ 35 ms | 2.0% |
| **A + B (no open obligation)** | exact | ≈ 48 ms | **≈ 54 ms** | **3.1%** |
| C. lazy Koszul queue (subsumes A) | sound | ≤ 75.5 ms | ≤ 85 ms | ≤ 4.9% |
| **B + C (upper bound)** | sound; cost open | ≤ 106 ms | **≤ 119 ms** | **≤ 6.8%** |

Option C's bound assumes that none of the 95,207 lost eliminations costs anything. In the engine
each of them becomes a pending signature, which brings a sort, a store query and a rewriter scan
of about 218 entries. Any of them that the rewrite criterion does not reject becomes a reduced
target. Eco-12's mean symbolic plus elimination cost per target is (449 + 1,323) ms / 2,898 ≈
0.61 ms at one worker, so if 0.13% of the lost signatures (about 125) reach reduction, C's whole
75 ms is spent. Whether they do is RS Theorem 6's question, open for this engine (§4).

The interreduction's remaining 228 ms (264 ms at 16 w less the selection) is the tails-only
matrix on the 743 essential elements. It does not depend on the outgrowth. Peak RSS, from the
term counts: dominated elements hold about 40 MB of Eco-12's 172 MiB, and that memory cannot be
freed (§4). Of it, 2.9 MB is never read again, and that can be known only in hindsight.

H5 is falsified: the exact options cut Eco-12 bookkeeping by 7% (A, 16.6 of 231 ms), and B
removes selection time, not bookkeeping. The ≥ 30% cut needs C's unproven bound (≤ 33%).

### 5.2 Cyclic-7 / Goldilocks (engine forced; M31 at 16 w: wall 0.669 s, bookkeeping 0.369 s, interreduction 0.021 s; conventional F4 0.145 s)

Even zero bookkeeping and zero interreduction leave 0.669 − 0.369 − 0.021 = 0.279 s, which is
**1.92×** conventional F4. Symbolic (0.133 s) and elimination (0.077 s) at 16 workers already
come to 1.45× conventional's whole wall on their own. A + B and C together remove at most
(168.4 − 90.0) + 19.4 ≈ 98 ms at one worker. The dispatch rule's `DegreeSpread` route to
conventional F4 stays correct.

### 5.3 MQ10 (not in Gate G)

Bookkeeping is 20 ms of the 380 ms entry wall at 16 workers. No option here moves MQ10 by more
than about 9 ms (C's 4.0 ms plus B's 4.6 ms). The tail of §0's side finding is a different mechanism (§7).

## 6. Gate G reading (plan §8.2, read once)

| Criterion | Reading |
|---|---|
| Soundness argument with no load-bearing open obligation | **met** for A and B (exact) and for C's correctness. C's *saving* rests on an open obligation, RS Theorem 6 for this engine (§4, §5.1). |
| Projected Eco-12 wall saving ≥ 5%, or Cyclic-7 engine ≤ 1.00× conventional at 16 w | **missed**. Obligation-free projection 3.1%. C's 6.8% is an upper bound that holds only if 95,207 lost eliminations cost nothing. Cyclic-7 floor 1.92× (§5). |
| No conflict with #940 | met (A, B and C all touch `insert` and `run` in `engine.rs`, so any prototype would wait for #940) |

**Gate G fails.** Per the plan, #936 closes as completed with this negative result, and H5 is
falsified.

## 7. Follow-ups

- **MQ10 tail after the last essential element.** Seven batches add seven dominated elements and
  cost 35% of the one-worker stage time. Early termination (F5B/F5+ degree bound, EF §10.2; RS
  B.4) is the relevant literature, and its detection cost decides whether it pays. Filed as an
  `opportunity` issue, #946. It touches `engine.rs`, so it waits for #940.
- The `research-sigf4-usage` instrument stays in place for whoever picks that up.
