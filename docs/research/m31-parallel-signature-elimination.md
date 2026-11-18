# M31-S1: signature-safe parallel elimination of the cross-target cascade (#902)

**Status:** DRAFT.
**Measured at:** MEASURED_AT
**Plan:** [`MILESTONE-COMPETITIVE-SIGNATURE-F4.md`](../MILESTONE-COMPETITIVE-SIGNATURE-F4.md)
§4, §7.2, §8.1, §9.2. **Prior work:** [`signature-f4-rfc.md`](signature-f4-rfc.md) §3.2, §6.1;
[`m30-sigf4-prototype.md`](m30-sigf4-prototype.md) §5.

## 0. Summary

SUMMARY

## 1. Sources

SOURCES

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
                                    and s(r_c) ≠ s(T_j)  (ρ_j not singular)
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

INSTRUMENT

## 6. Results

RESULTS

## 7. Pricing displacement

PRICING

## 8. Alternatives considered

ALTERNATIVES

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

OBLIGATIONS

## 11. Gate A (plan §8.1), read mechanically

GATE

## 12. Recommendation

RECOMMENDATION
