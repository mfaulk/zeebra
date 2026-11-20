# M32-S1a: parallel signature-aware symbolic preprocessing — design, correctness and ceiling (#933)

**Status:** design selected and argued (§2, §3) before any implementation, 2026-11-19. Replay
ceiling (§4): Eco-12 symbolic 2.95× at 16 workers, projected wall 0.79× the M31 reference.
**Gate P passes** (§6). #940 built this design. **Gate S failed** on both its reads; T1 and T2 passed both times. The
re-read, after the owner's fix pass, still missed Noon-7 at 16 workers
([`research/m32-gate-s`](../../research/m32-gate-s/README.md)). Attribution split by cause is incomplete (§5): it needs #939's frequency
record.
**Measured at:** `8694d172` — the M32 F0 baseline `7b25a1ee` plus this branch's replay instrument
(no change to the engine's algebra or its serial closure; tagged `measured/933-symbolic-replay`).
Built from `git archive` into a private target directory, release, fat LTO, `x86-64-v3`; SHA-256 in
[`research/m32-symbolic-replay/binaries.sha256`](../../research/m32-symbolic-replay/binaries.sha256).
Exploratory: n = 5 fresh processes per cell, one benchlock session (CPUs 8–23, CCDs 1–2 reserved).
**Plan:** [`MILESTONE-ADAPTIVE-F4.md`](../MILESTONE-ADAPTIVE-F4.md) §4.1 H1–H3, §7.2, §8.2 Gate
P, §9.2, §11 (Track A). M31 evidence: [`m31-sigf4-serial.md`](m31-sigf4-serial.md) §3
(change 3: the symbolic leg stayed 1.0×), [`m31-sigf4-parallel.md`](m31-sigf4-parallel.md),
[`research/m31-final/tables.md`](../../research/m31-final/tables.md).

## 1. What the stage does today

`Engine::symbolic` (`src/grobner/sigf4/engine.rs`) builds one batch's matrix:

1. **Seeds.** Each target `mult · source` has every term shifted by `mult` and interned in a
   per-batch `MonomialMap` (`seen`); a monomial met for the first time is appended to `work` and
   its id is its position there. Each row keeps the id of every term (its *handles*).
2. **Closure.** `work` is a FIFO worklist. For each column `m` in id order, `reducer(m)` returns
   the **least-ratio** basis element whose lead divides `m` (ties to the newest), from a
   per-monomial cache `reducers: m ↦ (best, scanned)` that persists across batches and rescans only
   elements added since `scanned`. If there is one, its tail is shifted by `m / lead` and interned,
   and the row `(sig · mult, mult, element)` is appended.
3. **Column sort.** Columns sorted descending by the monomial order; handles renumbered to
   positions.

Everything runs on the caller's thread. The basis is not touched between the batch's first seed
and its last reducer row: elements are appended only in `insert`, after elimination, and an
element's `sig`, `lead` and `terms` never change once inserted.

## 2. The design (deliverable 3)

**One design: a level-synchronous closure with a parallel scan and an ordered serial merge.** It
is #861's pattern, re-implemented for the signature engine; `symbolic_intern.rs` is **not used**.

Per batch, the closure runs as breadth-first *levels*: level 0 is the targets; level `L + 1` is
the columns first interned while level `L` was processed. Each level is one *step*:

- **Scan (parallel).** The level's items are cut into contiguous slices, claimed dynamically by
  the team (the caller included). For each item a worker, reading only state frozen for the step:
  - **reducer lookup against the fixed basis**: reads the cache entry for `m` and finishes the
    least-ratio scan over the elements added since, recording `(m, best, total)` locally;
  - **multiplication**: `mult = m / lead`, `sig · mult`, and the tail shifted by `mult`;
  - **interning, read side**: every shifted term is looked up in `seen` as it stood before the
    step; a hit is a handle, a miss is deduplicated in a slice-local table and gets a local id in
    first-occurrence order.
- **Merge (serial, caller, slices in order).** Each slice's new monomials are interned in `seen`
  and appended to `work` in local first-occurrence order (`entry().or_insert`, so a monomial new
  to two slices keeps the earlier slice's handle); local ids are translated; rows and handles are
  appended in item order; the slice's cache records are inserted into `reducers`.
- **Narrow levels** (below a frontier threshold) run the scan on the caller alone with no team
  wake-up, as #861 does, so a closure that never widens never starts a team.
- **Column sort (parallel).** A parallel sort of the distinct columns by the monomial order, then
  the handle renumbering per row on the team. Both are order-free (§3, Lemma 5).

One team per batch, parked at a barrier between steps; the caller mutates `seen`, `work` and
`reducers` only while the team is parked, so the scan needs no locks on them and no `unsafe`.

**Why not reuse `symbolic_intern.rs`.** Its step is welded to conventional F4's types:
`MonicBasis::find_divisor_with(selection)` (not signature-aware: no ratio, no signature on the row),
`MonomialSet` of pair lcms (the covered check has no signature analogue), `CriticalPair` seeds and
`PreprocessedRow`. Generalizing it over a reducer oracle is a conventional-F4 change that §11 rule 1
puts in its own PR with its own conventional A/B, for no gain to conventional F4; and its sharded
merge, the part that would be worth sharing, is a `research-work` instrument, not shipping code.
The engine already keeps handles from the closure (#914), so the pieces this design needs — slice
scan, local table, ordered merge — are about the size of the adapter a reuse would need. If #940
finds the merge is the limit (§4), generalizing #861's sharded merge is the follow-up, in a
separate PR.

**What stays serial, by design:** the merge (one `seen` insert per new column, one cache insert
per scanned column, the row append), and the level barriers. §4 measures how much that is.

**Not in the design:** a divisibility index for the reducer search (H3). §5.2 records whether the
search dominates; the correctness argument below does not depend on the scan order (Lemma 1), so
an index could be added inside #940 without reopening it.

## 3. Correctness argument (deliverable 4; plan §9.2)

Fix a batch. Write `B = (e_0, …, e_{n−1})` for the basis when the batch's symbolic stage starts,
`C` for the reducer cache then, and `T = (t_0, …, t_{k−1})` for the targets in the order `batch`
passes them. The claim is stronger than §9.2 asks: the parallel closure's output — `work` (hence
the column set), the rows `(signature, multiplier, source)` **in order**, every handle, the
reducer-row count, and the cache afterwards — is **identical** to the serial closure's, for every
worker count and every schedule. No canonicalization is needed, so the per-batch oracle is plain
equality.

**Lemma 1 (the reducer is a function of `m` and `B`).** Let `≺` compare elements by
`ratio_cmp` — the module-term ratio `s(e) / lm(e)` compared by cross-multiplication
`s(a)·lm(b)` against `s(b)·lm(a)`, then the signature index. A monomial order extends uniquely to a
total order on Laurent monomials compatible with multiplication, so `≺` is a total preorder, and
two elements tie only with equal ratio and index. The serial scan visits ids in increasing order and
replaces `best` whenever the candidate is not greater, so its result is
`R_B(m) = max{ i : lm(e_i) | m, e_i minimal under ≺ among those }`, or none — a definition that
mentions no scan order. The cached scan resumes the same loop at `scanned` from the stored `best`,
which is the same fold split in two; `e_0 … e_{scanned−1}` are the elements it saw (the basis is
append-only and elements immutable, §1), so the cached result is `R_B(m)` too.

**Lemma 2 (a batch looks up each monomial at most once, and nothing else writes its entry).** `m`
enters `work` only when `seen` misses it, so each column is processed once per batch; only that
lookup writes `reducers[m]`. Hence the value read for `m` in the batch is `C[m]` whatever other
entries were inserted before it, and deferring every insert to the merge (or to batch end, or to
hash shards in parallel) changes no lookup. The cache after the batch is `C` updated with
`m ↦ (R_B(m), n)` for every column whose entry was missing or stale — the same set in both.

**Lemma 3 (FIFO order is level order).** In the serial closure, the columns created while
processing level `L` (the seeds being level 0) are appended after all of level `L` and processed
after it, in creation order; so `work` is the concatenation of levels, and within a level ids
follow the first occurrence in the concatenation, *in item order*, of the monomials each item
produces (the seed's shifted terms; a reducer row's shifted tail).

**Lemma 4 (the merge assigns the serial ids).** Slices are contiguous ranges of the level, merged
in order, each slice's new monomials in local first-occurrence order. A monomial absent from `seen`
before the step therefore gets its id at its first occurrence in item order: an earlier slice
inserts it first, and a later slice's candidate finds it (`or_insert`). A monomial present before
the step is a hit in the scan with the handle the serial closure would read. So every handle, and
the next level, equal the serial ones (Lemma 3). The scan of an item reads only the frozen `seen`,
the frozen cache entry (Lemma 2) and `B` (Lemma 1), so what a slice produces is a function of its
range, not of which thread ran it or when: dynamic slice claiming moves work between threads, never
the result.

**Lemma 5 (the column sort is order-free).** The columns are distinct and the monomial order is
total, so the descending permutation is unique; any correct sort, parallel or not, gives it, and
the renumbering is a pure map per handle.

**Theorem.** By induction over levels with Lemmas 1–4, the parallel closure produces the serial
`work`, rows and handles; by Lemma 5 the same columns and renumbered handles. Elimination reads
only these, the basis and the targets, so the batch's elimination outcome — and everything after
it — is the serial engine's. The bound checks (`max_matrix_rows`, `max_matrix_columns`) read the
same final counts.

### 3.1 Obligations

Discharged by the argument (none is load-bearing and open):

| # | Obligation | Status |
|---|---|---|
| O1 | Reducer choice independent of scan order and cache state | Lemma 1 |
| O2 | Concurrent cache update changes no lookup | Lemma 2: the cache is read-only during a scan; inserts happen in the merge with the team parked |
| O3 | Concurrent interning changes no handle | Lemma 4: `seen` is read-only during a scan; inserts happen in the merge, slices in order |
| O4 | Basis fixed during the stage | §1: `insert` runs only after elimination; elements immutable |
| O5 | Column set, rows, multipliers, signatures, sources and their order equal the serial closure's | Theorem (equality, not a multiset) |
| O6 | Schedule independence (thread placement, slice claiming) | Lemma 4, last sentence |
| O7 | No `unsafe` | the design shares `&` during a scan and `&mut` only with the team parked |

Remaining for #940 to **implement and test** (each specified here, none changes the argument):

| # | Obligation | How #940 discharges it |
|---|---|---|
| T1 | Per-batch oracle: the parallel stage's output equals the serial closure's on every batch | equality test over the corpus at workers 1–16, as §4's replay already asserts on Eco-12 and MQ10 |
| T2 | Deterministic adverse schedules | seeded slice-claim permutations and forced yields between scan and merge at every worker count 1–16 (the cascade's `adversary` hook, `SigF4Options`) |
| T3 | Bound-check precedence | an early stop at a level boundary may raise only `TooManyRows` (rows only grow, and the serial check reads rows first); `TooManyColumns` is checked at the end, as now |
| T4 | Wall-budget cancellation at safe points | at level boundaries; a stop returns `TimeBudgetExceeded` with the batch's degree, and an unstopped run is unaffected |
| T5 | Scratch and the shared tables charged to `max_live_bytes` | slice scratch and the per-batch `seen`/`work` counted; typed `TooManyLiveBytes` |
| T6 | A field that cannot cross threads | `F::run_concurrent` falls back to the serial closure, which is today's code |

## 4. Ceiling from replayed batches (deliverable 5)

**Instrument.** `sigf4::symbolic_replay` (feature `research-sigf4-replay`; with its engine hook and `sig_f4_study` flags, 595 net non-test lines, under the 600-line cap) runs
§2's design on every batch beside the engine's serial closure, on the same targets and basis and a
clone of the reducer cache as the batch found it, at 1/4/8/16 workers, three runs each (the
median-time run kept), plus a serial census pass. Every run is **asserted equal** to the serial
closure — columns, rows in order, handles and the cache afterwards — so the replay is also the
per-batch oracle of §3.1 T1 on real batches. Its sort is serial (the design's is parallel; the
"parallel sort" column divides the measured sort by the worker count). Team start-up is on the
clock; the cache clone is not. A level narrower than 512 items (#861's `MIN_FRONTIER`) is scanned
by the caller alone.

```sh
sig_f4_study --field wide64 --name eco-12 --engine sigf4 --workers 16 --claim --symbolic-replay
research/m32-symbolic-replay/replay.sh <binary> <out.jsonl> 5      # the session below
python3 research/m32-symbolic-replay/summarize.py research/m32-symbolic-replay/replay.jsonl.gz
```

The engine ran at 16 workers with the parallel cascade (the M31 reference's configuration) and,
as a control, at one worker (design 1). `S_w` = the engine's own closure ÷ the prototype at `w`
workers, per process, summed over batches; median over 5 processes, range in brackets.

| Row | Engine w | Engine closure ms | S1 | S4 | S8 | S16 [range] | S16, parallel sort |
|---|---:|---:|---:|---:|---:|---:|---:|
| Eco-12 / 2⁶⁴−353 | 16 | 540.2 | 1.05 | 2.14 | 2.70 | **2.95** [2.91, 3.06] | 3.32 |
| | 1 | 472.6 | 0.96 | 1.91 | 2.37 | 2.58 [2.55, 2.68] | 2.92 |
| MQ10 / 32003 | 16 | 236.5 | 1.07 | 1.84 | 2.10 | 1.99 [1.93, 2.00] | 2.32 |
| | 1 | 222.0 | 1.01 | 1.72 | 1.97 | 1.84 [1.78, 1.90] | 2.15 |

Prototype phases, engine at 16 workers (medians, ms):

| Row | w | Total | Scan | Merge | Sort |
|---|---:|---:|---:|---:|---:|
| Eco-12 | 1 | 512.8 | 475.8 | 16.9 | 21.0 |
| | 16 | 183.1 | 120.9 | 29.5 | 22.2 |
| MQ10 | 1 | 221.7 | 189.9 | 14.6 | 16.4 |
| | 16 | 119.5 | 55.9 | 23.7 | 18.3 |

Reading:

- **Eco-12 has the width.** 29 batches, 181 levels, 79,834 rows over 100,702 columns; 63 levels are
  ≥ 512 items wide and hold 89% of all items. The scan scales 3.9× at 16 workers.
- **MQ10 does not.** 65 batches, 332 levels; the wide levels hold 74% of items, and from 8 to 16
  workers the merge's growth outweighs the scan's gain (S8 2.10, S16 1.99).
- **The serial remainder is the merge and the sort.** The merge grows with the worker count
  (Eco-12 16.9 → 29.5 ms): more slices means more monomials new to several slices, each re-probed
  in the merge. The sort is ~21 ms whatever the worker count. Together they are 28% of the 16-worker
  prototype on Eco-12, which is where #940's remaining headroom is (parallel sort; #861's sharded
  merge if needed).
- **Warm-run bias.** The prototype runs straight after the engine's closure on the same batch, so
  its caches are warmer; S1 = 1.05 in the 16-worker context is that bias (≈ 5%). Divided out
  (`S16 / S1`), Eco-12 is still 2.81×. These are ceilings, as the plan says: #940 measures the real
  thing through `f4_signature`.

## 5. Attribution and per-row cost (deliverables 1–2)

**The growth with workers is not symbolic work (H2's premise).** The closure is a deterministic
function of the batch (§3), and every replay process saw the same 29 Eco-12 batches with the same
100,702 columns and 79,834 rows, and the same basis digest, at 1 and 16 engine workers. Yet the
engine's own closure took 472.6 ms beside design 1 and 540.2 ms beside the 16-worker cascade
(+14%; unrecorded runs in the same processes: 446–485 against 539–542 ms), reproducing M31's
466 → 552 ms. The prototype at one worker, run on the same batches immediately afterwards, grew only
~4.5% (≈ 492 → 514 ms). What differs is what ran just before the closure: the parallel elimination.
That is consistent with the post-burst clock (this host holds all-core boost, ~12% below single-core,
for 200–500 ms after a multicore burst) and with caches evicted by the team; it does not separate the
two, nor allocator effects.

**Open (needs #939):** the split of the +68 ms between CPU frequency, cache and allocator. That
requires the frequency record and the component split #939 is producing; this note does not claim
it. A scheduling-only change (parking or not waking the team) is therefore not proposed here.

**H3 is falsified: reducer search is not the cost.** The census pass times the least-ratio lookup
(cache read and scan of the elements added since) separately: **2.3–2.6%** of the Eco-12 closure and
**5.6–6.0%** of MQ10's, far under H3's 30%. The lookups scanned 22.1 M basis elements on Eco-12
(13,621 cache misses, 65,457 stale entries, 21,624 current), mostly rejected by the 8-byte mask. The
closure's cost is shifting and interning terms — one hash probe of `seen` per shifted term — which is
exactly what the design parallelizes. No divisibility index belongs in #940.

**Per-row cost against conventional F4 (deliverable 2): partly open.** The signature closure costs
6.8 µs per row on Eco-12 and 3.0 µs on MQ10 (engine closure ÷ rows, 16-worker context). The
comparison with conventional F4's serial closure on the same inputs needs conventional symbolic stage
clocks at `7b25a1ee`, which #939's baseline cohort records; until then the only figure is M30's
92.6 ms serial on MQ10 / 32003 against this engine's 198–222 ms, at different commits. Since the
reducer search is a few percent, whatever gap remains is in interning volume (rows × terms), not in
the signature-aware choice.

## 6. Gate P

| Criterion | Evidence | Result |
|---|---|---|
| Correctness argument with no load-bearing open obligation | §3: O1–O7 discharged; T1–T6 are tests and safe points for #940, none changes the argument; the replay asserted equality on every Eco-12 and MQ10 batch at 1/4/8/16 workers (5 processes × 2 contexts × 13 runs) | **met** |
| Projected Eco-12 symbolic ≥ 2.0× at 16 w, from replayed batches | S16 = 2.95 [2.91, 3.06] in the reference's context; 2.81 with the warm-run bias divided out; 2.58 in design 1's context | **met** |
| Projected Eco-12 wall ≤ 0.88× M31 reference | 1,752 − 552 + 552 / 2.95 = 1,387 ms → **0.792**; with S16 = 2.58: 1,414 ms → 0.807 | **met** |

Additive Amdahl from the M31 reference's medians, as plan §6.3 does; `8715c8ed..7b25a1ee` changed no
measured path (`src/grobner/`, `src/poly/`), so the reference and this baseline run the same code.
MQ10 at 16 workers projects to S16 ≈ 2.0 (symbolic 232 → ~116 ms, wall ~264 ms), short of the 2.2×
plan §6.3 needs for T3 by S1 alone: **MQ10 still needs routing (#927).**

**Gate P passes; #940 is unblocked.**
