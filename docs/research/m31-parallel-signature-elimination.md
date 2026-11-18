# M31-S1: signature-safe parallel elimination of the cross-target cascade (#902)

**Status:** complete, 2026-11-18. Recommends one exact schedule; Gate A items 1–2 pass, item 3
waits on #901's re-derived §6.3 table and on #903 (§11).
**Measured at:** `0e75b3b6` (replay records in [`research/m31-cascade/`](../../research/m31-cascade/);
coefficient-product counts only, no wall time taken). The only timings in this document are
quoted from #857 §3.2 at `2d589a80` / `7d85eee5` via plan §2.4.
**Plan:** [`MILESTONE-COMPETITIVE-SIGNATURE-F4.md`](../MILESTONE-COMPETITIVE-SIGNATURE-F4.md)
§4, §7.2, §8.1, §9.2. **Prior work:** [`signature-f4-rfc.md`](signature-f4-rfc.md) §3.2, §6.1;
[`m30-sigf4-prototype.md`](m30-sigf4-prototype.md) §5.

## 0. Summary

- **The cascade can be parallelised exactly.** Any schedule in which each target applies only
  admissible reducer rows and other targets' *final* results, and stops only once it knows every
  earlier target's lead, computes design 1's rows bit for bit (Theorem 1, §3: normal forms modulo
  an echelon pivot set are unique). Termination and freedom from deadlock follow because every
  wait is on a strictly smaller signature. No new result about signature bases is needed, and no
  displacement.
- **Least-signature-wins displacement (RFC §6.1 item 2) terminates but is not proved correct.** It
  reduces by unfinished rows and can see a different lead at **shadowed** columns, where two
  admissible rows share a lead — 33,935 such applications on Eco-12 (§4.3, §6). It leaves four open
  obligations, two load-bearing (§10), and its extra products are bounded only by 32% of design 1's
  on Eco-12 (§7). It is not selectable under Gate A item 1.
- **Recommended: "prereduce + claim".** Design 2's parallel pre-reduction against the reducer
  block, then a cascade pass in which a target, at its first surviving entry, waits for every
  earlier target to announce its lead or finish as a zero row, and otherwise waits only on the final
  rows it applies. Exact; coordination is one write-once owner slot per column, a per-row
  completion flag and a monotone announcement counter — no compare-and-swap.
- **Eco-12 replay (29 batches, 2,898 targets):** dependency width up to 87 targets, depth up to 31;
  critical-path share 0.149 of design 1's products for the recommended schedule. Elimination
  ceiling **3.26× / 5.88× / 6.70×** at 4 / 8 / 16 workers (greedy-achievable 4.63× at 16), products
  **1.216×**. Katsura-11: **3.98× / 7.85× / 14.72×**, products 1.000×.
- **Caveat that matters for Gate B:** the same model gives design 2 as built 2.39× at 16 workers on
  Eco-12, where #857 measured 1.39×. Scaled by that 0.58 efficiency the recommended schedule is
  about 3.9×.
- **Gate A:** item 1 passes, item 2 passes (6.70× ≥ 3.5×, 1.216× ≤ 1.25×). Item 3 is **pending**
  #901's re-derived §6.3 table: on plan §6.3's historical stage clocks the elimination ceiling alone
  projects 0.93× shipping F4-16, so the gate passes only if #903 cuts at least 0.54 s of Eco-12's
  1.70 s of interreduction, bookkeeping and symbolic time (0.73 s at the calibrated figure).

## 1. Sources

Read from the PDFs; `pdftotext -layout` used only to search. Keys follow the RFC's §1.

| Key | Source | Read |
|---|---|---|
| **EF** | Eder, Faugère, *A survey on signature-based Gröbner basis computations*, arXiv 1404.1774 | §4.1–4.2, §13, §14, §15 in full |
| **Lz** | Lairez, *Axioms for a theory of signature bases*, arXiv 2210.13788 | Defs 4, 14, 28; Cor 32–33; Props 30, 56; §5.3–5.7 with Algorithm 8 and Thm 62 |
| **RS** | Roune, Stillman, *Practical Gröbner basis computation*, arXiv 1206.6940 | §2.2, §5, Appendices A–B |
| **F45** | Albrecht, Perry, *F4/5*, arXiv 1006.4933 | §2–4 |
| **FL** | Faugère, Lachartre, *Parallel Gaussian elimination for Gröbner bases computations in finite fields*, PASCO 2010 (author-hosted copy; HAL hal-01293798 has no file) | §2–4.5 |
| **GBLA** | Boyer, Eder, Faugère, Lachartre, Martani, *GBLA*, arXiv 1602.06097 | §1, §3.1, §4.1–4.4, §5.1, §6.1–6.2 |
| **F5** | Faugère, ISSAC 2002 | not re-read: no copy reachable this session; cited only through the RFC's reading (RFC §1, §3.3) |

What the literature settles, and what it does not:

- **The row rule.** A row is reduced only by rows of strictly smaller signature, with rows sorted
  by signature and no swaps (EF Algorithm 4 l.10–11, p. 38: "s-reductions on the polynomial side
  correspond to fixing an order on the rows in M_d"; F45 pp. 8–9: "we cannot swap rows, nor can we
  reduce lower rows … by higher rows"; Lz Algorithm 8 l.97–98). Symbolic preprocessing takes, per
  monomial, the reducer of least signature; if it is not below the row's, the term stays (EF
  Algorithm 5 l.10, Property 13.3(b,c)). Batch results are used unmultiplied (Lz §5.7, p. 30).
- **Order independence is not published for a batch.** EF Lemma 4.10 and RS Lemma 2 (two regular
  top-reduced elements of one signature share a lead) assume a signature Gröbner basis up to that
  signature; Lz Corollary 33 assumes a rewrite basis below it. Inside a batch neither holds.
  Theorem 1 (§3) replaces them with a linear-algebra statement that needs no such hypothesis.
- **Lz Theorem 62 tolerates non-reduced insertions**: an inserted `g` that is not →-reduced keeps
  its signature in the queue (`Σ(g,h) = {sig g}`, pp. 30–31), and the reduction is to "a →-normal
  form", any one (Def 4). This is why a weaker equality is *plausible* for displacement (§4.3).
- **No parallel schedule for the within-matrix signature cascade is published.** EF §15(c), p. 50:
  "restrictions to s-reductions lead to restrictions swapping rows during the Gaussian Elimination.
  Getting more flexible and possibly able to use (at least some of) the ideas from [FL] is still an
  open problem." FL keeps the echelon form of `D` sequential (§4.5); GBLA parallelises it with a
  waiting list and a sequential prefix (§5.1) and treats F5 matrices as full-rank ones, never
  mentioning signatures (§4.3, §6.1). Lz §5.3 cites parallelism only as a reason to process
  *signatures* out of order (Thm 57), between batches. A 2026 preprint (arXiv 2601.06765, §11.5)
  sketches signature-safe block elimination without addressing the order among new rows; it is not
  relied on.
- **No published bound or measurement of the cascade's critical path** was found; §6 is, as far as
  this search reaches, the first.

grobx and msolve sources were not read (plan §11).

## 2. Formal model of a batch

Design 1 (`src/grobner/sigf4/engine.rs`, `Engine::batch` → `symbolic` → `eliminate`) processes
one signature degree at a time. A batch is:

- **Columns** `0 … n−1`: the monomials of the batch matrix in decreasing monomial order. Column
  `c` is to the *left* of `c′` when `c < c′`. Every row is stored monic, lead first; a pivot row's
  tail lies strictly to the right of its lead.
- **Targets** `T₁, …, T_m`: the surviving pending signatures, one row each (`mult · source`),
  with pairwise distinct signatures sorted so that `s(T₁) < … < s(T_m)` (`Engine::batch` merges
  equal signatures and keeps one). `row_k` is target `k`'s row before elimination.
- **Reducer block** `R`: for each column `c` that some basis element's lead divides, symbolic
  preprocessing adds the multiple `r_c` of the **least-signature** such element (`Engine::reducer`
  picks the least sig-lead ratio, which is the least signature at a fixed column monomial). So if
  `s(r_c)` is not below a target's signature, *no* basis multiple at `c` is admissible for it.
  Reducer rows are never modified during the batch.
- **Admissibility.** A row of signature `σ` may be reduced only by a row of strictly smaller
  signature (BFS §2.1; EF §3; Lz Algorithm 8; RFC §3.2). Signatures are labels fixed at
  construction: a row's signature after elimination is its signature before (EF Remark 4.4(a),
  EF §13; RFC §3.2), so admissibility of a pivot never depends on *when* it is applied.
- **Design 1's pivot map** for target `k`, a partial map from columns to rows:

  ```
  P_k(c) = r_c                      if c ∈ dom R and s(r_c) < s(T_k)
         = ρ_j                      else, if some j < k has a nonzero result ρ_j with lead c
                                    that is not singular (no r_c with s(r_c) = s(T_j))
         = undefined                otherwise
  ```

  `ρ_k = NF(row_k ; P_k)`, the left-to-right reduction of `row_k` by the rows `P_k` offers
  (`Workspace::reduce`). Zero `ρ_k` adds the syzygy signature `s(T_k)`; a lead at a column whose
  reducer has signature exactly `s(T_k)` is singular and discarded (EF Lemma 5.1); otherwise
  `(s(T_k), ρ_k)` is a new basis element and `ρ_k` becomes the batch pivot at its lead. This is
  Lz Algorithm 8 with `AG^{<σ}` realised as the reducer block and `N` as the earlier results.
- **The cascade** is the set of applications `P_k(c) = ρ_j`: a target using an earlier target's
  result. Design 2 parallelises everything else (each target against `R` alone, the "phase A")
  and leaves the cascade serial (#857 §5).

At most one target leads at any column, singular rows included: if `j < k` both led at `c`, `k`
would have been reduced at `c` by `ρ_j` (or by an admissible `r_c`). The instrument asserts this
on every recorded batch.

## 3. Correctness of exact schedules

**Lemma 1 (echelon pivots).** The rows in the image of `P_k` have pairwise distinct leads, each
at the column it is assigned to, with tails strictly to the right. Hence a nonzero element of
their span has its leftmost entry in `dom P_k`. *Proof:* one row per column by definition;
ordering the rows by lead column gives a matrix in row-echelon form, and the leftmost nonzero
entry of a combination is the lead of the leftmost row with a nonzero coefficient.

**Lemma 2 (normal forms are unique).** For any row `v` there is exactly one `w ∈ v + span(P_k)`
with `supp(w) ∩ dom P_k = ∅`, and any sequence of applications of `P_k` rows that ends when no
entry lies in `dom P_k` reaches it. *Proof:* existence by the left-to-right reduction, which
terminates because each application clears the leftmost entry in `dom P_k` and adds entries only to
its right. Two such `w, w′` differ by an element of `span(P_k)` that avoids `dom P_k`, which is
zero by Lemma 1. ∎

**Theorem 1 (schedule independence, exact rows).** Run the targets under any interleaving,
concurrent or not, in which target `k`

1. applies only rows of `P_k` — reducer rows `r_c` with `s(r_c) < s(T_k)`, or another target's
   **final** result `ρ_j` at its lead — and
2. stops only when no entry of its row lies in `dom P_k`, which requires knowing every earlier
   target's lead (or that the target is zero) at each column where its row has an entry and the
   reducer block offers nothing admissible.

Then every target's result equals design 1's `ρ_k` exactly. Consequently the zero rows (hence the
zero-row syzygy signatures), the singular discards, the new elements `(s(T_k), ρ_k)` and their
order, and every quantity derived from them after the batch — pairs, rejections, the syzygy and
rewrite stores, the final reduced basis — equal design 1's.

*Proof.* Induction on `k`. `P_k` depends only on `R` (fixed) and on `ρ_1 … ρ_{k−1}`, which equal
design 1's by hypothesis; condition 2 is the information needed to evaluate `dom P_k`; Lemma 2
makes the end state independent of the order of applications. ∎

**Admissibility at the moment of application.** Every row condition 1 allows has signature
`< s(T_k)` by construction, and labels do not move (§2), so each application is signature-safe
whenever it happens, including when the pivot is a result produced earlier in the same batch: `ρ_j`
is itself a valid row of signature `s(T_j)` because it was built only from rows below `s(T_j)`
(by the same argument one level down). This discharges plan §9.2's first bullet for exact
schedules.

**Termination and freedom from deadlock.** A target performs at most `n` steps (one per column,
left to right). Every wait in condition 1 or 2 is on a target of strictly smaller signature, so
the wait-for relation is contained in the signature order and is acyclic; `T₁` never waits, and
by induction every target completes. A potential function: `Φ = Σ_k (columns target k has not yet
passed)`, which every step decreases by at least one and no wait increases; `Φ ≤ m·n`. No
displacement, no restart, no extra row operation.

Design 2 is the special case "phase A, then the cascade serially" of Theorem 1: phase A applies
admissible reducer rows only (condition 1), and the serial pass reduces with `P_k` until condition
2 holds (`Workspace::reduce` visits every remaining entry). It therefore yields design 1's rows
exactly — which #857 observed only through the final digest, and which Theorem 1 explains.

What Theorem 1 does **not** need: EF Lemma 4.10 (lead uniqueness per signature, whose hypothesis
— a signature Gröbner basis up to `σ` — does not hold inside a batch) or any new result about
Lz Algorithm 8. It reduces the concurrent algorithm to the sequential one row for row.

## 4. Least-signature-wins displacement (RFC §6.1 item 2)

The RFC's scheme: each column carries an owner word `(signature rank, row)`. A target reaching a
column where the reducer block offers nothing admissible reads the owner; if the owner's rank is
lower it reduces by the owner's row, if the column is free it claims it by compare-and-swap, and if
the owner's rank is higher it **displaces** the owner, which must then reduce by the newcomer and
resume.

### 4.1 Can a lower-signature row displace a pivot, and can the displaced row resume?

Yes to both, as individual operations. Displacing `P` by `T` with `s(T) < s(P)` performs no row
operation on `T`; `P` then reduces by `T`, which is admissible because `s(T) < s(P)`. Resuming is
continuing `P`'s left-to-right reduction from the contested column: everything to its left is
already final for `P` (§2: pivot tails reach only rightward), and `T`'s tail adds entries only to
the right of the contested column.

### 4.2 Termination

`P`'s lead moves strictly right on each displacement (it is cleared at the contested column), or
`P` becomes zero. A column's owner rank only decreases. So
`Ψ = Σ_rows (n − lead column) + Σ_columns (owner rank)` (a row with no lead contributes 0) strictly
decreases on every displacement, and every other step is a left-to-right step bounded as in §3.
Displacements per batch are at most `m·n`, and per column at most `m − 1`. This much is a proof,
not an obligation.

### 4.3 Equivalence to a valid sequential order: what is and is not shown

The RFC infers that at quiescence each column's owner is the least-signature row leading there,
"which is what the sequential order produces", and invokes EF Lemma 4.10 for the leads. Three gaps
separate that from a proof:

1. **Snapshots.** Under displacement a target may reduce by an owner's row *before the owner has
   finished* (the owner is still clearing its tail, or is later displaced). Such a row is
   `ρ_j + (combination of rows below s(T_j))`: every application is still signature-safe, but it
   is not an element of Lz Algorithm 8 line 98's reducer set `AG^{<σ} ∪ N♮`, where `N` holds the
   batch's *finished* results. Lz's Theorem 62 proof does tolerate inserting an element that is not
   fully reduced (the signature then stays in the queue: `Σ(g,h) = {sig g}`, Lz pp. 30–31), but it
   is stated for →-reduction steps by `AG^{<σ} ∪ N♮`, not for subtraction of arbitrary
   lower-signature combinations. Whether the proof extends is not checked here (obligation O1).
2. **Lead equality needs a hypothesis that fails inside a batch.** EF Lemma 4.10 and RS Lemma 2
   assume a signature Gröbner basis up to `σ`; Lz Corollary 33 assumes a rewrite basis below `σ`.
   Neither holds for the rows of an unfinished batch (EF Property 5.8(a): "valid once all S-pairs of
   signature T are handled"). The linear-algebra substitute is: two fully reduced rows in
   `row_k + W_k` (with `W_k` the span of everything below `s(T_k)` in the batch) have the same lead
   if the admissible rows' leads are the leading-column set of `W_k`. That fails exactly when two
   admissible rows share a lead column: a target `T_j` leads at `c` because `r_c` is not admissible
   for it (`s(r_c) > s(T_j)`), and a later `T_k` with `s(T_k) > s(r_c)` has both. Design 1 then
   reduces by `r_c`; a displacement run may reduce by a snapshot of `T_j`, and `ρ_j − r_c` can
   expose a lead design 1 never sees. The instrument counts these **shadowed** applications (§6).
3. **Re-wake.** A target that passed column `c` with an entry left there, before an earlier target
   claimed `c`, is no longer fully reduced. Design 1 never has this state. The scheme needs a
   protocol to wake such rows (or a final validation sweep), and its termination: each column's
   owner changes at most `m − 1` times, so re-wakes per row are bounded by `(m − 1)·n`, but the
   products they cost are not bounded by anything better than the row's whole suffix.

So the displacement scheme terminates, and every operation it performs is permitted, but neither
"same new elements as design 1" nor "a different but valid set" is proved; the latter rests on O1.


## 5. Schedules and the replay instrument

### 5.1 What is recorded

`src/grobner/sigf4/replay.rs`, behind the `research-sigf4-replay` feature (which implies
`research-sigf4`). `engine.rs` gains four `#[cfg]`-gated call sites in `eliminate` and nothing else.
For every target, in signature order, the instrument records the column-ordered sequence of steps
`Workspace::reduce` takes: an application of a reducer-block row, an application of an earlier
target's result, or a surviving entry, each with its coefficient products (pivot row length − 1,
the engine's own count), plus the products the target spent before the signature-ordered pass
(design 2's phase A; zero in design 1). At batch end the traces are reduced to a `BatchRecord`
and discarded.

`sig_f4_study --replay --workers W` (with `--features research-sigf4-replay`) runs design 1 without
recording, design 1 recorded, and design 2 recorded at `W` workers, in one process. It **refuses**
unless the recorded run's 19 algebraic quantities (batches, pairs created and singular, rejections
by each of five mechanisms, targets, reducer rows, reductions to zero, singular rows, elements
added, signature and reduced basis sizes, syzygy signatures, total products, products on zero and
on singular rows) and basis digest equal the unrecorded run's, and design 2's digest equals
design 1's. `replay::tests::test_recording_changes_no_algebraic_quantity` asserts the same, plus
`Σ work = coefficient_products` and the zero-row count, on katsura-6 / Goldilocks, katsura-5 /
GF(32003) and cyclic-5 / Goldilocks at 1 and 4 workers.

### 5.2 The model

Time is coefficient products. Each target is one sequential task whose steps happen in column
order; a step may wait. Infinite workers give each schedule's critical path `CP`; for `p` workers,
per batch (batches are separated by the serial post-batch bookkeeping, a barrier):

- **ceiling** `= W₁ / Σ_batches max(CP_b, W_b / p)` — no list schedule beats it;
- **greedy** `= W₁ / Σ_batches (W_b / p + (1 − 1/p)·CP_b)` — Graham's bound, which any greedy
  scheduler that switches a blocked worker to another ready target achieves;

where `W₁` is design 1's total products and `W_b` the arm's products in batch `b`. Both ignore
synchronization, memory traffic and scheduling overhead, so both are upper bounds on the real
stage speedup; the ceiling is what plan §8.1 reads.

The waiting rules, for target `k` at a step at column `c`:

| Step | `dag` | `frontier` (exact) | `claim` (exact) |
|---|---|---|---|
| reducer row | none | none | none |
| earlier result `ρ_j` | until `ρ_j` is final | until `ρ_j` is final | until `ρ_j` is final |
| surviving entry | none | until every `j < k` has passed `c` or announced its lead | until every `j < k` has announced its lead or ended zero |

A target "passes" `c` when its last step at or before `c` completes, and every column once its lead
is announced (when its first surviving entry is resolved). `dag` is not a valid schedule on its
own — a target cannot know an entry survives without hearing from earlier targets — but it bounds
every schedule that applies only final rows, displacement included, and its excess over
`frontier` is all a non-exact scheme could gain. The instrument checks
`max target ≤ CP_dag ≤ CP_frontier ≤ CP_claim ≤ W` on every batch in its tests.

Arms: **exact** replays design 1's traces (the rows Theorem 1 says any exact schedule computes, with
the same products). **prereduce** replays design 2's: each target starts its cascade pass after its
own phase A, so `W_b` includes phase A's extra products; `serial-cascade` is design 2 as built
(`max(max phase A, A/p) + cascade`).

### 5.3 Dependency statistics

Per batch: targets, zero targets, distinct target-on-target edges, targets with any such edge, the
longest chain of edges (**depth**, in targets) and the most targets at one depth (**width**), the
costliest single target, and the counts of shadowed applications and would-be displacements (§7).

## 6. Results

One `sig_f4_study --replay --workers 2` run per row at `0e75b3b6`. Every run passed the invariance
check (§5.1). Design 1's and design 2's products reproduce #857's (Eco-12 0.611 G and 0.743 G).
Eco-12 at Goldilocks and Katsura-11 at 2⁶⁴−353 gave records identical to the rows shown, field
for field, so the field does not enter (both are kept in `research/m31-cascade/`). Tables from
`research/m31-cascade/summarize.py`.

### 6.1 Dependency structure (design 1)

| Row | Batches | Targets (zero) | d1 products | d2 ÷ d1 | Max width | Max depth | Dependent targets | CP share dag / frontier / claim | Shadowed | Would displace (suffix ÷ d1) |
|---|---:|---:|---:|---:|---:|---:|---:|---|---:|---:|
| **Eco-12** / 2⁶⁴−353 | 29 | 2,898 (1,013) | 0.611 G | 1.216 | 87 | 31 | 2,447 | 0.114 / 0.281 / 0.391 | 33,935 | 915 (0.320) |
| **Katsura-11** / Goldilocks | 18 | 706 (145) | 0.200 G | 1.000 | 41 | 44 | 681 | 0.220 / 0.284 / 0.304 | 33 | 297 (0.290) |
| Cyclic-7 / Goldilocks | 436 | 3,211 (128) | 0.019 G | 1.020 | 18 | 77 | 1,320 | 0.203 / 0.228 / 0.275 | 7,276 | 1,581 (0.451) |
| noon-7 / Goldilocks | 17 | 643 (120) | 384 k | 1.000 | 107 | 3 | 102 | 0.179 / 0.202 / 0.210 | 0 | 13 (0.004) |
| katsura-4 / Goldilocks | 5 | 11 (2) | 1.2 k | 1.000 | 2 | 2 | 5 | 0.638 / 0.638 / 0.638 | 0 | 2 (0.182) |

*Width* and *depth* are of the target-on-target use graph, per batch (maximum over batches).
*CP share* is `Σ_b CP_b ÷ W₁`: the infinite-worker floor as a fraction of design 1's elimination.
Every target-on-target use is at a distinct (user, used) pair, because a target applies another
only at that one's lead column: Eco-12 has 189,173 such uses against 3.73 M reducer-row
applications and 1.05 M surviving entries.

The cascade is not a chain. On Eco-12, 2,447 of 2,898 targets use an earlier target, but the
longest chain is 31 targets and the widest level 87. In the nine batches that hold 96.7% of the
products, the costliest single target is at most 8.9% of its batch (all-batch total: 1.8% of `W₁`),
so no single target bounds the stage. What the exact schedules wait on is **information**, not
rows: under `claim` a target waits at its lead for every earlier target's lead, so a lead
announced late delays every later target. The exact arm is poor (`claim` puts 0.391 of the
products on the critical path) while `dag`, which waits only for the rows actually applied, puts
0.114 there. Moving the reducer-block work in front of the cascade (next paragraph) cuts `claim`'s
share to 0.149, which is consistent with — though the records do not split it — that work
delaying the leads.

Pre-reduction removes exactly that: phase A clears every reducer-block column in parallel with no
waiting, so the cascade pass starts close to each target's lead. Design 2's critical-path shares on
Eco-12 are 0.052 (`dag`), 0.108 (`frontier`) and **0.149 (`claim`)**, for 1.216× the products
(phase A 0.855 W₁, the cascade pass 0.361 W₁: re-reducing columns that earlier targets' tails
reintroduce). On Katsura-11 phase A costs nothing extra (1.000×) and the shares are
0.034 / 0.041 / 0.042.

### 6.2 Elimination-stage ceilings against design 1

`ceiling = W₁ / Σ max(CP_b, W_b/p)`; *greedy* is Graham's achievable bound (§5.2). The products
column is the arm's work over design 1's.

| Row | Arm / schedule | Exact | Products ÷ d1 | 4 | 8 | 16 | 16 greedy |
|---|---|---|---:|---:|---:|---:|---:|
| **Eco-12** | exact / dag (displacement bound) | no | 1.000 + displ. | 3.83 | 6.56 | 8.64 | 5.90 |
| | exact / frontier | yes | 1.000 | 3.37 | 3.55 | 3.56 | 3.07 |
| | exact / claim | yes | 1.000 | 2.54 | 2.55 | 2.56 | 2.33 |
| | prereduce / dag | no | 1.216 | 3.27 | 6.45 | 11.59 | 8.00 |
| | prereduce / frontier | yes | 1.216 | 3.27 | 6.30 | 8.94 | 5.65 |
| | **prereduce / claim** | **yes** | **1.216** | **3.26** | **5.88** | **6.70** | **4.63** |
| | prereduce / serial-cascade (design 2) | yes | 1.216 | 1.73 | 2.13 | 2.39 | 2.33 |
| **Katsura-11** | exact / dag | no | 1.000 + displ. | 3.68 | 4.55 | 4.55 | 3.72 |
| | exact / frontier | yes | 1.000 | 3.36 | 3.53 | 3.53 | 3.05 |
| | exact / claim | yes | 1.000 | 3.17 | 3.29 | 3.29 | 2.88 |
| | prereduce / dag | no | 1.000 | 3.98 | 7.85 | 15.07 | 10.59 |
| | prereduce / frontier | yes | 1.000 | 3.98 | 7.85 | 14.91 | 9.94 |
| | **prereduce / claim** | **yes** | **1.000** | **3.98** | **7.85** | **14.72** | **9.79** |
| | prereduce / serial-cascade (design 2) | yes | 1.000 | 3.05 | 4.62 | 6.21 | 5.60 |
| Cyclic-7 | prereduce / claim | yes | 1.020 | 3.66 | 6.17 | 8.13 | 5.83 |
| noon-7 | prereduce / claim | yes | 1.000 | 3.73 | 5.24 | 6.00 | 4.57 |

Every schedule and arm for every row is in the records.

### 6.3 Calibration against the one measured point

The model's design 2 (`serial-cascade`) on Eco-12 at 16 workers is 2.39× (greedy 2.33×). #857
measured design 2's elimination at 1.22 s against design 1's 1.70 s, **1.39×** (plan §2.4; one run
each, `2d589a80` / `7d85eee5`, before M30's Workstream P). The products model therefore overstates
design 2's realised stage speedup by 1.71×: synchronization, the parallel pass's memory traffic and
per-step overhead are not products. If the recommended schedule realised the same 0.58 of its
ceiling it would be **≈ 3.9×** on Eco-12 at 16 workers. That is one point, on a different schedule,
at old commits; #901's fresh stage clocks supersede it, and S2's Gate B (≥ 2.5× measured) is the
real test.

## 7. Pricing displacement

On the `dag` timeline (every target as early as the rows it applies allow), a least-signature-wins
claim would be contested wherever a target reaches a column before the earlier target that will
own it has announced its lead there.

| Cost | Eco-12 | Katsura-11 |
|---|---:|---:|
| Contested uses (would-be displacements) | 915 of 189,173 | 297 of 27,512 |
| Products the displaced rows had already spent past the column (upper bound on redone work) | 0.320 W₁ | 0.290 W₁ |
| Shadowed applications (O2's hazard) | 33,935 | 33 |
| Owner-word reads (every visit to a column the reducer block does not cover) | 1.24 M | 0.42 M |
| Owner-word CAS: one per claim, one per displacement | ≤ 2,800 | ≤ 860 |

- **Extra row operations.** Between 0 and 0.32 W₁ on Eco-12: the bound is reached if a displaced
  row must redo its whole suffix, approached if displacement happens late. Products would then lie
  in [1.00, 1.32]× design 1 — not certifiably within plan §8.1's 1.25×. The real figure depends on
  the run's timing; this replay cannot pin it.
- **Synchronization.** Owner-word reads are 1.24 M on Eco-12 against 3.73 M reducer-row
  applications, at ~156 products per application: well under 1% of the inner-loop memory
traffic. CAS
  traffic is negligible. Synchronization is not where displacement's cost lies.
- **Memory.** Displaced rows resume, so no extra rows are held, but every snapshot a reader applies
  must stay valid while the owner keeps writing: a double-buffered or copy-on-publish row per
  target, roughly doubling the cascade's live row storage.
- **The ceiling it buys.** `dag` exceeds the exact schedules' ceilings only on the exact arm
  (8.64× vs 3.56× at 16 workers on Eco-12). After phase A, `dag`'s 11.59× is 1.30× the exact
  `frontier` and 1.73× `claim`, before displacement's own extra products are charged. The
  recommended exact schedule already clears Gate A item 2.

## 8. Alternatives considered

Each alternative is placed against Theorem 1; "exact" means it meets both of its conditions.

- **Signature-rank wavefronts / deterministic two-phase claims** — the `claim` schedule (§5). A
  target reduces freely until its first surviving entry, then waits until every earlier target has
  announced its lead (or ended zero), after which every column's owner is known and the rest of
  the row needs only the final rows it applies. Exact. The coordination is one monotone counter
  ("leads announced up to rank `k`") plus a per-row completion flag: no compare-and-swap on columns,
  no displacement. Its ceiling is the `claim` row of §6.
- **Per-column frontier** — the `frontier` schedule. Exact and strictly more permissive than
  `claim` (it waits on an earlier zero row only until that row has passed the column in question),
  but every surviving entry needs a prefix-maximum over earlier targets' published frontiers, a
  structure whose cost would sit on the critical path. Its ceiling is the upper bound for exact
  schedules.
- **Speculative reduction with validation** — the `prereduce` arm: reduce against the reducer block
  without waiting (design 2's phase A), then finish each target against earlier results under the
  `frontier` or `claim` rule. Exact by Theorem 1 (phase A applies only admissible reducer rows). It
  pays phase A's redundant products (§6) for a shorter cascade.
- **Least-signature-wins displacement** — §4; bounded by the `dag` schedule plus displacement
  costs (§7); not proved (O1–O3).
- **Column-block (Faugère–Lachartre) partitioning.** FL and GBLA split the matrix into a known-pivot
  block `A|B` and the rest `C|D`, parallelise `B ← A⁻¹B` and `D ← D − CB` by column blocks, and
  keep the echelon form of `D` sequential (FL §4.5: "since Gauss is sequential, it must be computed
  as soon as possible"; GBLA §5.1 eliminates the first `2 × threads` rows of `D` sequentially and
  parks out-of-order pivots in a waiting list). The signature rule does not break the block split,
  but it changes the pivot choice (FL §3.1 and GBLA §3.1 choose pivots by sparsity or arbitrarily;
  a signature matrix must take the least-signature reducer, EF Algorithm 5 / Property 13.3) and it
  fixes `D`'s row order. Phase A *is* the `A|B`/`C` step; the remaining question is `D`, which is
  exactly the cascade. A right-looking elimination of `D` in signature order (at each column the
  least-signature live row becomes pivot and reduces the rows above it in signature) is
  signature-safe and gives the same leads as design 1 when no column is shadowed, but different
  rows; it does strictly different products, which this replay cannot price from design 1's traces.
  **Open, not measured**: it would need its own replay, and the plan's caps do not stretch to a
  second instrument.
- **F4/5 and the published F4-signature descriptions** sort rows and forbid swaps (F45 pp. 6, 8–9;
  EF §13, Algorithm 4); none parallelises the cascade, and EF §15(c) lists making signature
  elimination "more flexible and possibly able to use (at least some of) the ideas from" FL as an
  open problem. No published parallel schedule for the within-matrix signature cascade was found
  (§1).

## 9. Required equality, and the syzygy and rewrite stores (plan §9.2)

**Decision: exact row equality with design 1, per batch.** Plan §9.2 offers three levels: exact
rows; the batch's new `(lead, signature)` elements and zero-row syzygy signatures; or only the final
reduced basis. Exact rows are required, for three reasons:

1. **It costs nothing in the ceilings that matter.** The exact schedules (`frontier`, `claim`) are
   provably exact (Theorem 1) and perform design 1's products to the unit (§6). The extra
   parallelism a weaker equality could buy is the gap between `dag` and the exact schedules, which
   §6 measures.
2. **The weaker levels are not proved.** "Same new elements" for displacement rests on O1–O3
   (§4.3). "Only the final reduced basis" would need, in addition, that a different set of new
   elements does not unsoundly enlarge the syzygy store: a zero row at `σ` is recorded as a
   syzygy signature (RFC T6) and thereafter rejects every pair `σ` divides, so a schedule that
   produced a zero row design 1 does not would discard pairs on a claim nobody has checked.
   Certification (plan §9.1) would turn a lost element into a refused output rather than a wrong
   one, but it would surface on a gating instance, not in a unit test.
3. **It makes #904's §9.2 tests sharp.** With exact equality S2 can compare every batch's result
   rows, zero-row signatures and new elements against design 1 under deterministic adverse
   scheduling — a per-batch oracle, not a final hash.

**Soundness of the syzygy and rewrite stores.** Under exact equality each batch hands
`Engine::insert` the same `(signature, row)` sequence in the same order as design 1, and the
zero-row syzygies the same signatures. The stores are then identical after every batch.
Concurrency stays inside one batch's elimination: batches remain sequential, and the post-batch
bookkeeping (`insert`, Koszul syzygies, new pairs, the rewriter cache) stays serial in signature
order. Plan §9.2's fourth bullet is therefore satisfied by serialization, as it allows.

## 10. Open proof obligations

**For the exact schedules (`claim`, `frontier`, and either after phase A):** none is load-bearing.
Theorem 1 reduces them to design 1 row for row; termination and deadlock freedom are proved in §3;
admissibility of every application is by construction. What remains is implementation evidence,
which belongs to #904's §9.2 tests, not to the argument:

- **E1 (publication).** A result `ρ_j` must be visible to other workers only once final, and a lead
  announcement only after the lead is resolved (release/acquire on the per-row flag and the
  announcement counter). A standard memory-model obligation of the code, not of the algorithm.
- **E2 (singular rows).** A singular target still announces its lead (so later targets can resolve
  their columns) but never becomes a pivot; Theorem 1's `P_k` already excludes it. The test must
  include batches with singular rows.
- **E3 (budget and cancellation).** Wall-budget cancellation at batch and pivot safe points must
  abandon the batch as a whole; a partially eliminated batch must not reach `insert`.

**For least-signature-wins displacement:** load-bearing and open.

- **O1.** Lz Theorem 62 with reduction by lower-signature *snapshots* (not finished results, not
  →-steps by `AG^{<σ} ∪ N♮`). Needed for the scheme's correctness at all.
- **O2.** Lead equality with design 1 at shadowed columns (§4.3 item 2), or a proof that the
  different elements and zero rows it can produce are valid and do not unsoundly enlarge the
  syzygy store (§9).
- **O3.** A re-wake protocol and its completeness: no row ends with an entry at a column owned by a
  lower-signature row that arrived after it passed.
- **O4.** A bound on extra products better than "every displaced row's suffix" (§7).

O1 bears on the admissibility of reducers and O3 on termination of the protocol as implemented, so
under plan §8.1 item 1 displacement **cannot be selected**.

## 11. Gate A (plan §8.1), read mechanically

For the selected schedule, **prereduce + claim**:

| # | Criterion | Value | Read |
|---|---|---|---|
| 1 | Argument covers the schedule; no load-bearing open obligation | Theorem 1 (exact rows), §3 termination and deadlock freedom; remaining items E1–E3 are implementation tests (§10) | **pass** |
| 2 | Eco-12 elimination ceiling ≥ 3.5× design 1 at 16 workers, displacement and redundant work included; products ≤ 1.25× | 6.70× (greedy 4.63×); products 1.216× (phase A's redundant work included; no displacement) | **pass** |
| 3 | Combined with S3, projected Eco-12 ≤ 0.70× shipping F4-16 on #901's re-derived §6.3 table | not yet computable: #901's table is not published (PR #908 holds only the held-out pins) and #903 has neither measured savings nor stage ceilings | **pending** |

Item 3, conditionally, on plan §6.3's historical inputs (design 1 3,625.5 ms, F4-16 2,338.6 ms,
elimination 1,698 ms; interreduction + bookkeeping + symbolic 1,695 ms), which #901 replaces:

| Elimination at 16 workers | Elimination after | Projection with no S3 saving | S3 saving needed for ≤ 0.70× |
|---|---:|---:|---:|
| ceiling 6.70× | 253 ms | 0.93× | ≥ 544 ms (32% of the three stages) |
| greedy 4.63× | 367 ms | 0.98× | ≥ 657 ms (39%) |
| calibrated ≈ 3.9× (§6.3) | 434 ms | 1.01× | ≥ 725 ms (43%) |

The rule to apply once #901 posts: with `D₁` design 1's median wall, `E` its elimination stage,
`F` the paired F4-16 median and `S` #903's measured (or ceiling) saving,
`(D₁ − E·(1 − 1/6.70) − S) / F ≤ 0.70`. Gate A passes if and only if that holds; the plan reads the
ceiling, and the greedy and calibrated rows show how much margin the ceiling carries.

## 12. Recommendation

**Build "prereduce + claim" in #904, if Gate A item 3 passes.**

1. Phase A as design 2 has it: every target reduced against the reducer block in parallel, each
   pivot use checked against the target's signature.
2. Cascade pass, targets dispatched in signature order to a work-stealing pool. A target reduces
   left to right. At a column with no admissible reducer it reads the column's owner slot: if set,
   it waits for that owner's completion flag and applies the owner's final row; if unset, it waits
   until the announcement counter reaches its own rank, after which the slot is authoritative.
   When its own lead is resolved it writes its owner slot (write-once: by Theorem 1 at most one
   target leads at a column, singular rows included) and then bumps the announcement counter in
   rank order; a zero row bumps it when it finishes.
3. Results are handed to the existing serial post-batch code in signature order, so the syzygy,
   rewrite and pair stores are updated exactly as in design 1.

Why this one: it is exact with no open obligation; its coordination is one ordered counter, a
write-once slot per column and a flag per row; it clears Gate A item 2 at 6.70× with the products
already paid by design 2; and its ceiling is within 1.33× of the exact optimum (`frontier`,
8.94×), which needs a per-column frontier structure on the critical path to realise. `frontier` is
the natural refinement if S2 measures `claim` short of Gate B; displacement is not recommended
(§4, §7, §10).

**#904's tests**, beyond plan §9: per batch, the cascade's result rows, zero-row signatures,
singular discards and new elements equal design 1's (Theorem 1 makes this the oracle, not just the
final digest), under forced interleavings and seeded random yields at every worker count 1–16.

**If Gate A item 3 fails**, this is a no-go for #904 under plan §8.1, and the evidence here stands
as M31's answer to H1 (supported on the stage: an exact schedule reaches ≥ 3.5× ceiling) and H2
(the displacement inference is unproven; an exact alternative makes it unnecessary).
