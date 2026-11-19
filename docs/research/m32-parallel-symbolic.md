# M32-S1a: parallel signature-aware symbolic preprocessing — design, correctness and ceiling (#933)

**Status:** design selected and argued (§2, §3) before any implementation; replay ceiling §4;
attribution §5. Gate P reading §6.
**Measured at:** `7b25a1ee` (the M32 F0 baseline) plus the replay instrument on this branch,
built from `git archive` into private target directories; exploratory n = 5, labelled as such.
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

PENDING (filled from the replay).

## 5. Attribution and per-row cost (deliverables 1–2)

PENDING.

## 6. Gate P

PENDING.
