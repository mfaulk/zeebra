# M30-S2: signature-compatible F4 — invariants, architecture and implementation RFC (#856)

**Status:** RFC, 2026-11-17. Documents only: no code under `src/` was written or changed.
**Measured at:** not measured here. Every figure is quoted from a source that carries its own commit:
the [C1 attribution](m29-grobx-attribution.md) (`7e18d089`), [#223's note](signature-based.md),
the [M30 plan](../MILESTONE-SIGNATURE-SYMBOLIC-F4.md) (planning base `adfa6a60`), and §12.1's Gate A1
figures, from #716's report (PR #867, head `d2e7e5c0`; grobx pinned at `1854835d`). Code
references are to `main` at `4f5784c5`.
**Plan:** [`MILESTONE-SIGNATURE-SYMBOLIC-F4.md`](../MILESTONE-SIGNATURE-SYMBOLIC-F4.md) §6.2.
**Gate dependency:** the go/no-go (§12) reads #716's Gate A1 (plan §6.1). A1 was posted on
2026-11-17 ([verdict](https://github.com/mfaulk/zeebra/issues/716#issuecomment-6955121982), PR #867).
**Decision: GO, narrowed to Eco-12 primary** (§12).

## 0. Summary

1. **A signature-compatible F4 can be built soundly on Zeebra's components.** The correctness
   argument (§4) needs only a module order compatible with the monomial order, regular
   reductions (a row is reduced only by rows of strictly smaller signature), and processing the
   rows of a batch in increasing signature order. It needs neither a regular sequence nor
   homogeneous input. Lairez proves a batched, F4-style variant correct and terminating
   (Theorem 62, Algorithm 8), and that is the theorem this design rests on.
2. **The criteria are not a filter on unsigned pairs** (§3.4). They take a signature on every
   basis element and every row, a syzygy-signature store, and a rewrite order. This is #223 §5.1's
   finding, and the RFC keeps it.
3. **Parallel forward elimination survives, with one change** (§6.1). Independent target rows can
   still be reduced in parallel, provided each use of a pivot is checked against the target's
   signature. Contested pivot columns must also go to the smaller signature, not to the first
   writer. The survey calls parallel signature elimination an open problem (Eder–Faugère §15(c)),
   so this is a design claim for #857 to measure, not an established result.
4. **Recommended:** the **isolated** architecture (§8, §9). It is a separate engine behind its own
   entry point that reuses fields, monomials, polynomials, divisor masks, sparse-row kernels,
   budgets and final interreduction. The algorithmic variant is **F4-RB with Schreyer
   (`<lt-pot`) shifted signatures, the sig-lead-ratio rewrite order, batches by least signature
   degree, Koszul and zero-row syzygies, and no handover in design 1** (§9).
5. **#223's findings stand** (§11). The ≤2× row bound is now read as a bound on *rows*, not on
   *coefficient products*, which is what #835 changed.
6. **Go, narrowed** (§12). On the RFC's own evidence there is no theoretical or architectural
   blocker. The decision rule was fixed before A1 reported. A1 then passed on Eco-12 only, in
   the exact pairing: 6.33× less work, 0.171 of the wall, RSS 1.03×. The rule therefore gives
   **GO, with Eco-12 primary and `katsura-11` as the second family**.

## 1. Sources read, and how

Read in full from the PDF or document, with equations and algorithms checked in the PDF and the
`pdftotext` extraction used only for searching:

| Key | Source | Read |
|---|---|---|
| **F5** | Faugère, *A new efficient algorithm for computing Gröbner bases without reduction to zero (F5)*, ISSAC 2002, Ver 1.2 (copy supplied by the owner) | all 9 pp. |
| **EF** | Eder, Faugère, *A survey on signature-based Gröbner basis computations*, arXiv 1404.1774 (J. Symbolic Comput. 2017) | all 53 pp. |
| **Lz** | Lairez, *Axioms for a theory of signature bases*, arXiv 2210.13788 (v3) | full |
| **RS** | Roune, Stillman, *Practical Gröbner basis computation*, ISSAC 2012, arXiv 1206.6940 | full |
| **AP** | Arri, Perry, *The F5 criterion revised*, J. Symbolic Comput. 2011, arXiv 1012.3664 (v6) | full |
| **F45** | Albrecht, Perry, *F4/5*, arXiv 1006.4933 | full |
| **BFS** | Bardet, Faugère, Salvy, *On the complexity of the F5 Gröbner basis algorithm* (Matrix-F5), arXiv 1312.1655 | full |
| **DZD** | Ding, Zhang, Deaton, *How Much Can F5 Really Do?*, IACR eprint 2021/051 | full |
| **St** | Stegers, *Faugère's F5 algorithm revisited*, IACR eprint 2006/404 | pp. 1–54 in full; the Magma listings (pp. 55–81) only searched |
| **GX** | grobx `MANUAL.md` at `1854835d` (documentation only; no grobx code was read, per [§4 of the plan](../MILESTONE-SIGNATURE-SYMBOLIC-F4.md) and [`external-provenance-policy.md`](external-provenance-policy.md)) | all 2,931 lines |
| — | [`signature-based.md`](signature-based.md), #223 with comments, [C1](m29-grobx-attribution.md), #716 | full |

Where F5's own paper covers a claim it is cited directly (F5 §, Definition, Theorem, Corollary,
algorithm or figure). The survey is cited where F5 is silent, chiefly on non-`<pot` orders, F4-style
reduction and termination outside the no-zero-reduction case.

A note on citations. EF states the compatibility requirement and the rule for Matrix-F5 row
operations in prose, with no Definition number, so they are cited by section and page. F45's
Algorithms 8 and 10 contradict its own prose and Lemma 4.3 about sort direction. This RFC follows
the prose and the lemma, which agree with BFS §2.1 and EF §3.

## 2. Vocabulary (plan §2.2, unchanged)

The plan's §2.2 quantities are used exactly as defined there: **pairs rejected** (by mechanism),
**reductions to zero**, **zero rows**, **pair rows adding no rank**, and **coefficient products on
zero-ending rows**. In addition, this RFC uses:

- **signature** `s(α)`: the leading term of a module element `α ∈ R^m` under a module monomial
  order (EF Def 2.1(b)). An implementation stores `(s(α), ᾱ)` and never `α` itself (EF Property
  5.8(b); RS §2.4). Coefficients of signatures are not needed (EF §2, after Def 2.1).
- **regular reduction**: reducing `α` by `bβ` only when `s(bβ) < s(α)` strictly. **Singular**
  means `s(bβ) ≃ s(α)` (EF Def 4.1 and the text after Remark 4.2). Signature algorithms perform
  only regular reductions (EF Algorithm 1 line 6, Algorithm 2 line 8; AP Def 4; Lz Def 14).

## 3. Theory

### 3.1 Module orders and signature representation

A module monomial order on `R^m` must be **compatible** with the monomial order: `a ≤ b ⇔ ae_i ≤
be_i` (EF §2; RS §2.1; Lz axiom S2). An incompatible order can give an infinite signature basis
(AP Appendix, Example 27). The candidates are:

| Order | Definition | Incremental? | Guarantee for regular input | Practical record |
|---|---|---|---|---|
| `<pot` | index first, then term (EF Def 2.2) | yes, by index (EF Property 7.7(b)) | no reduction to zero for any regular sequence (EF Cor 7.16) | huge syzygy sets: `|H|` 3,667,986 on HRandom(14,2,2) against 3,494 under `<lt-pot` (EF Tables 4/9) |
| `<d-pot` | degree of `\overline{ae_i}`, then `<pot` (EF Def 2.2) | no; by degree (F4/5 uses it, EF Property 13.1(a)) | none for a **homogeneous** regular sequence (EF Cor 7.17) | between the two |
| `<lt-pot` = **Schreyer** | `lt(\overline{ae_i})`, then `<pot` (EF Def 2.2, "also known as Schreyer's order") | no | **none**: zero reductions possible on regular input (EF V&S 8.4(b); Table 2: katsura-12 640 against 0) | fewest s-reductions and operations overall (EF §14.3(a),(d)); "often the best" (RS §5); grobx's order (GX "A batched F4 over signatures") |

**Representation.** Lz Remark 25 uses **shifted** signatures `lm(g_i) ⊗ e_i`. With a
term-over-position comparison these reproduce Schreyer order (Lz Example 26). A shifted signature
is a monomial of the ring plus an index. Comparing two signatures is then one monomial comparison
followed by an index tie-break, and the syzygy criterion's divisibility test (`S | T`) is monomial
divisibility at equal index. Both are operations Zeebra already has for monomials.

### 3.2 Signature-safe reduction, and what a row's signature means after elimination

- **Rule.** A row of signature `σ` may be reduced only by a row of strictly smaller signature
  (BFS §2.1, the "valid" row operation `Row(s) ← Row(s) + λ Row(s′)` with `s′ < s`; EF §3, p. 8:
  rows sorted by signature, and "the row we reduce with must be below the row to be reduced";
  F45 p. 8; St §3.7). There are no row swaps.
- **The signature is invariant.** "For regular s-reduction, we perform only those s-reduction
  steps that do not change the signature at all" (EF Remark 4.4(a)). In F4 terms, "the signatures
  corresponding to rows in `M_d` do not change throughout the whole process" (EF V&S 13.2(a)).
  So after elimination a row still means `\overline{aα}` plus a combination of rows of smaller
  signature, and its label is the label it was built with. **This answers the plan's question
  directly: a row's signature after elimination is its signature before.** Zeebra's existing
  per-row provenance (`PreprocessedRow`, `symbolic.rs:719-741`) has the same "original multiple"
  meaning, so it becomes exact rather than a caveat.
- **Lead terms are determined.** If the basis is a signature Gröbner basis up to `σ`, two
  regular top-reduced elements of signature `σ` have the same leading term (EF Lemma 4.10; RS
  Lemma 2). So the outcome does not depend on the order in which *permitted* reductions are
  applied, which is the property §6.1 relies on.
- **Singular reductions are detected, not performed.** An element that is singular
  top-reducible s-reduces to zero and is discarded (EF Lemma 5.1, Algorithm 1 line 9).
- **Full vs top reduction.** Full regular s-reductions mostly beat top-only (EF §14.3(b)), and
  give sparser rows (BFS §4). Tail reduction does not affect correctness (Lz §2: "only a matter of
  performance").

### 3.3 Correctness theorems the design uses

| # | Statement | Source | Hypotheses |
|---|---|---|---|
| T1 | A signature Gröbner basis's polynomial parts form a Gröbner basis of `I` | EF Lemma 4.6; AP Prop 13; Lz Lemma 18 | none beyond the setup |
| T2 | If every regular S-pair of signature `< T` s-reduces to zero, `G` is a signature GB up to `T` (signature Buchberger criterion) | EF Thm 4.9 | compatible order |
| T3 | RB with pairs in increasing signature order (`≼_s`) and **any** rewrite order computes a rewrite basis (hence a signature GB) and a GB of the syzygy module's initial terms, and terminates | EF Thm 7.6 (proofs: EF ref. [31] Thm 7, Thm 20) | compatible order; `≼_s` (EF Property 7.7(c)) |
| T4 | **Batched (F4-style) RB is correct and terminates**: take any subset `S` of the signature queue, reduce each reductant modulo `AG^{<σ} ∪ N` in increasing signature order, where `N` holds this batch's earlier results (unmultiplied), and insert `N` into `G` only after the batch | Lz Thm 62, Algorithm 8, §5.7 | compatible order; Lz's axioms, which hold in the polynomial ring (Lz §6.1) |
| T5 | The matrix arrangement "does not change what is computed" relative to the naive per-pair reductions | Lz §5.7 | as T4 |
| T6 | A reduction to zero at `σ` means `σ` is the signature of a syzygy | AP Thm 10; EF Thm 5.3, Algorithm 4 lines 17–18; in F5, a **non-principal** syzygy `s ∈ Syz \ PSyz` with `HT(s) = S(r)` (F5 Thm 4) | regular reduction at `σ` |
| T7 | No reduction to zero for a regular sequence | F5 Cor 3 (via Thm 4: a zero reduction exhibits a syzygy outside the principal ones, and for a regular sequence `Syz = PSyz`, F5 §4); EF Cor 7.16 (`<pot`), Cor 7.17 (`<d-pot`, homogeneous); BFS Thm 9 (matrices of full rank); AP §7.2 | regular sequence; F5 also assumes **homogeneous** input (F5 §3: "we suppose that all the polynomials are homogeneous") and its incremental position-over-term order; **not** Schreyer order |

T4 is the load-bearing theorem. F45 proves correctness only *if* the algorithm terminates (F45
Thm 4.4: "does not imply that F4/5 terminates for all inputs"). Lairez calls earlier F4-signature
descriptions unsatisfactory: "Albrecht and Perry (2010) do not prove termination and Eder and
Faugère (2017, §13) are superficial" (Lz §1). St §3.7 reports that a hybrid F4/F5 "turned out not
to be correct". The design therefore follows Lz Algorithm 8's invariant, not F45's pseudocode.

F5 itself points to the F4 route without specifying it: "from the efficiency point of view, it is
recommended to translate the algorithm in a F4 fashion" (F5 §7, before Algorithm F5). It proves
termination only "in a restricted case (when there is no reduction to zero)", for homogeneous input
(F5 §7.4, Thm 3, Cor 2), and says its proofs of correctness and termination are "only sketched"
(F5 §1). F5's own guarantees therefore cover less than T3/T4.

### 3.4 Criteria, and why they are not a pass over unsigned pairs

- **Syzygy criterion.** If a known syzygy signature `S` divides `T` with `S < T`, the pair at
  `T` s-reduces to zero (EF Def 6.3, Lemma 6.4). Syzygy signatures come from three sources:
  - Koszul syzygies `ksyz(α,β) = β̄α − ᾱβ` (EF Def 6.2; seeded in EF Algorithm 2 line 3);
  - every reduction to zero (T6);
  - coprime leading monomials (GX "Syzygies from three sources", citing RS §3).
- **Singular / rewrite criterion.** Exactly one multiple per signature needs handling (EF Lemma
  6.6). The canonical rewriter is the `⊴`-maximal element whose signature divides `T` (EF Def 7.1),
  and a pair is skipped if either generator is rewritable (EF Algorithm 3; Lemma 7.18).
- **They are the same family as F5's criteria.** F5's criterion is stated on *normalized* labelled
  polynomials: `r` with `S(r) = eF_k` is normalized if `e` is not top-reducible by
  `Id(f_{k+1},…,f_m)` (F5 Def 2). Only normalized critical pairs need to reduce (F5 Thm 1;
  `CritPair`, §7.2). It uses only the principal ("trivial") syzygies `f_i F_j − f_j F_i`: "take into
  account only the trivial syzygies … but not to compute the module of syzygies" (F5 §1). Its
  Rewritten criterion keeps one rule list per index and rejects a product `u·r_k` when a more
  recently added rule's signature divides it (F5 §6: `Add Rule` prepends, `Rewritten?`; applied in
  `Spol`, §7.2, and as condition (c) of `IsReducible`, §7.3). Both are special cases of the syzygy
  and singular criteria (EF Property 8.3; Remark 6.5 for `<pot`). F5's rewrite order is therefore
  EF's `⊴_add` (newest wins), not `⊴_rat`.
- **Rewrite order.** `⊴_add` takes the newest element. `⊴_rat` takes the least sig-lead ratio
  `s(α)/lt(ᾱ)` (EF Def 7.13; RS §3.4). With `⊴_rat`, RB computes a minimal signature GB (EF Lemma
  7.19, Cor 7.20). EF finds the difference between the two "vanish[es] for bigger computations"
  (§14.3(c)). grobx uses the sig-lead ratio (GX "Rewriting by the sig-lead ratio").

**Why they cannot filter unsigned pairs.** Every one of these criteria reads `s(·)` of basis
elements, which are a property of how each element was *derived*: an element's signature is the
label of the row it came from (§3.2). The rewrite check further needs `G ∪ H` and `⊴` (EF Algorithm
3). Zeebra's `CriticalPair` (`pairs.rs:45-72`) holds two basis indices and an lcm. Its basis
elements (`MonicElement`, `symbolic.rs:243-249`) were produced by elimination orders that are not
signature-safe (the default lets the first pair row to reach a column become its pivot,
`linalg/echelon.rs:264-289`, and the parallel path is nondeterministic,
`linalg/concurrent.rs:486-579`). So no well-defined signature exists to attach after the fact. **A
signature criterion is only sound when every element of the basis was produced by signature-safe
reduction from signed inputs.** That is #223 §5.1's conclusion, and the survey's algorithms
(Algorithms 1–5) bear it out.

### 3.5 Incremental against non-incremental

- `<pot` is incremental by index (EF Property 7.7(b)). F5 is the original instance: "since the
  algorithm is *incremental* the main loop … iterates on the number of polynomials". It computes
  Gröbner bases of `(f_m)`, `(f_{m−1}, f_m)`, …, `(f_1,…,f_m)` with `F_1 ≻ F_2 ≻ … ≻ F_m`, i.e.
  position over term with the index order reversed (F5 §1, §4, §7.1 "Algorithm incremental F5";
  EF §8 footnote 5). Each step can interreduce the
  previous basis (F5R/F5C, EF §8.1–8.2), but `H` grows enormous (§3.1 table).
- `<d-pot` and Schreyer proceed by degree, which is how Zeebra's F4 already selects (EF Property
  13.1(a) for F4/5).
- **Recommendation: non-incremental**, with batches by least signature degree. An incremental
  design would need one F4 run per generator. That conflicts with Zeebra's batch structure, and
  the survey's own experiments favour Schreyer (EF §14.3(d)).

### 3.6 Overlap with Buchberger, chain and Gebauer–Möller

- **Chain.** "The Chain criterion is completely included in the rewrite criterion of RB, without
  any further restrictions" (EF §12, after Eder [27]). ImpG2V adds Gebauer–Möller's installation
  conditions "without corrupting signatures" (EF §12.2), but explicit chain checks are redundant.
- **Product.** Under Schreyer order RB does **not** predict every product-criterion zero
  reduction (EF §12, counterexample for `<lt-pot`). The product criterion is safe to add in a
  signature algorithm (EF §12, after Gash [50]). Checking it explicitly is cheaper than adding
  principal syzygies (EF §12.3).
- **Combined effect.** Adding the product and chain criteria to RB gives "subtle" differences
  (EF Remark 14.1(b)).
- **Design consequence.** The engine uses the syzygy and rewrite criteria plus an explicit
  product check, records each mechanism's rejections separately (plan §2.2, "pairs rejected per
  mechanism"), and does **not** reuse `pairs.rs`'s Gebauer–Möller B/M/F deletion. That deletion
  is keyed to unsigned lcm structure (`pairs.rs:835-914`), and discarding a pair by it would not
  be justified by any signature theorem. Gebauer–Möller and signatures overlap, but by different
  arguments, and only the signature argument is sound for the signed pair queue.

### 3.7 Behaviour on harder inputs

Correctness (T1–T5) holds for every input under a compatible order. What changes with the input
is how much work the criteria avoid:

| Input class | What the theory says | Source |
|---|---|---|
| Regular sequence | no reduction to zero under `<pot` / `<d-pot` (homogeneous); some under Schreyer | T7; EF Table 2 |
| **Overdetermined** (`m > n`) | cannot be regular ("no overdetermined sequence can be regular"), so T7 never applies. "bad performance is expected when the system is overconstrained"; F5's suggested remedy is to compute a total-degree basis first and rerun F5 on it. Reductions to zero are "unavoidable for Trinks7 (7 equations, 6 variables)": 4 useless pairs in F5 | F5 §9.2, §9.1, Fig 9.1; St Remark 3.3 |
| Non-regular, square | zero reductions remain: Cyclic-6 still has 8 under AP's algorithm, against 16 for F5 | AP Table 1 |
| Underdetermined (`m < n`) | can be regular; "the maximal efficiency of the F5 algorithm is expected when the number of equation is less or equal than the number of variables" | F5 §9.2; BFS treats `m ≤ n` only (Thm 2) |
| Non-radical | regularity does not depend on radicality; nothing in T1–T7 uses it | (follows from the statements) |
| Positive characteristic, field equations | over F₂, adding `x_i² − x_i` to `H` strengthens the rewrite criterion | EF §9.1 (F5/2) |
| Inhomogeneous (Zeebra's corpus is affine) | select by signature degree (`≼_s` with a degree-compatible order refines sugar degree), or homogenize | EF Property 7.7(d); Remark 8.1(b); V&S 8.4(a) |
| Signature basis much larger than the reduced GB | signatures lose: yang1 is 1,333 s for SB against 5.6 s for plain Buchberger; biomd-147 builds 1,532 elements against 428 | RS Table 1 and §B.4; GX "hands over" |

grobx's documented record on these classes:

- Its 0.53 geometric time quotient over 53 instances predates handover. It includes
  15.9× / 14.8× losses on reimer-6 and biomd-103 (GX "On by default").
- Its handover tests exist "where the signatures stop paying" (GX Params).
- Its own measured gains come from **combinations** of zero tests that are partly randomized. Any
  zero test it uses is bounded at `2^−31` error per row (GX "Rows ruled zero by random
  combinations").

**None of that randomized machinery is in this RFC.** M30 excludes uncertified randomized row
skipping (plan §13).

### 3.8 Hybrid signature / plain F4, and handover

- **Restart.** grobx restarts plain F4 from the input at handover (GX "At a handover the call
  starts over in the plain run from its input"). Its tests (gap, outgrown, early round, pair-work)
  read zero-row and divisibility counts per round, with constants tuned on its own sets (GX
  "Signatures", L1698–1880). grobx states that none of them comes from a published source.
- **Reuse instead of restart.** Not in grobx, but sound by elementary argument. Every element of
  a signature basis is in `I`, and plain F4 is correct from any finite generating set of `I`. So
  seeding plain F4 with the input plus the partial signature basis cannot change the reduced
  basis it returns. Whether reuse helps is unmeasured. A signature basis can be much larger than
  the minimal one (RS §B.4), so reuse may hurt.
- **Policy for #857.** Design 1 has **no handover**. A budget stop or an unsupported input returns
  a typed error, and the caller may fall back to the shipping F4 (§7). Handover is a design-2
  candidate, and only if design 1's measurements show the outgrowth pattern on a corpus instance.
  #273's handover question is answered here: handover is a policy on top of a correct engine, not
  part of its correctness.

## 4. Correctness argument: a discarded pair cannot change the ideal or the reduced basis

The setup is a compatible module order (§3.1), signatures on every element and row, only
regular reductions (§3.2), and each batch processed as Lz Algorithm 8: rows in increasing
signature order, results inserted after the batch.

1. **Every computed element lies in `I`.** A row is `\overline{aα}` for some element `α` of the
   signed basis, or an input `e_i ↦ f_i`. Elimination forms linear combinations of rows. By
   induction every row, and so every element added, is a polynomial combination of the input
   generators. This is the provenance argument Zeebra already relies on for F4 output
   (`certify.rs` takes `⟨G⟩ ⊆ I` from provenance). The engine **never adds an element from
   outside the span**, so `⟨G⟩ ⊆ I`.
2. **Every input generator is in `⟨G⟩`.** Each `e_i` enters the queue (EF Thm 4.9's hypothesis
   "all `e_i` with `e_i < T` s-reduce to zero"). It is either reduced into an element of `G` or
   shown to s-reduce to zero. The latter means `f_i` is a combination of elements of smaller
   signature in `G`. So `I ⊆ ⟨G⟩`, and together with step 1, `⟨G⟩ = I`. A discarded *pair* never
   affects this: only input signatures carry generators, and none is discarded except by a
   criterion that proves it reduces to zero, i.e. is already in the span.
3. **A discarded pair is one that s-reduces to zero, or is covered.**
   - (a) Syzygy criterion: the pair's signature is divisible by a syzygy signature, so it
     s-reduces to zero modulo the current `G` (EF Lemma 6.4, which needs `G` to be a signature GB
     up to `T`; supplied by T3/T4's invariant).
   - (b) Rewrite/singular criterion: another multiple with the same signature is processed
     instead (EF Lemma 6.6, Lemma 7.11).
   - (c) Product criterion: safe in signature algorithms (EF §12, after Gash).
   - (d) Singular top-reducible elements: s-reduce to zero (EF Lemma 5.1).

   In every case T2's hypothesis ("every regular S-pair of signature `< T` s-reduces to zero")
   still holds after the discard.
4. **At termination `G` is a signature GB** (T3/T4), so its polynomial parts form a Gröbner
   basis of `I` (T1, with step 2's `⟨G⟩ = I`).
5. **The reduced basis is unique.** For a fixed monomial order the reduced Gröbner basis of `I` is
   unique. Interreducing any Gröbner basis of `I` with ordinary polynomial reduction gives it. So
   the final output is **coefficient-for-coefficient equal** to the shipping F4's reduced basis.
   This step uses no signatures. EF reports no end-of-run interreduction, and this step is an
   elementary consequence (the survey interreduces only between incremental steps, §8.1–8.2).

**Where this can fail, and the test that catches it** (R4 in plan §13):

- a reduction applied with `s(reducer) ≥ s(target)` corrupts a signature. Steps 3(a)–(b) then
  rest on a false invariant. EF V&S 13.2 / F45 / St §3.7 all warn about this, and St's hybrid was
  incorrect.
- a syzygy signature recorded from a row that was reduced out of order violates T6.
- a Koszul signature computed with the wrong module order.

**Defence.** In tests, an exhaustive debug assertion compares signatures on every row operation.
#857 also checks the complete basis for every corpus output against the shipping F4 and
`buchberger_reference` (`src/grobner/reference.rs`), coefficient for coefficient, not leading
terms. Plan §6.3 requires this.

### 4.1 Which corpus inputs meet which assumptions

| Instance | Correctness assumptions (T1–T6) | Regular-sequence guarantee (T7) | Note |
|---|---|---|---|
| `mq-random-10/11` (dense random quadratic, `m = n`) | met | generically expected for the homogenization; not proven per instance; and T7 does not hold under Schreyer anyway | grobx: 26 zero reductions of 782 on MQ11 (C1 §3) |
| `katsura-n` | met | expected (Bezout count attained); F5 finds 0 useless pairs on Katsura 3, 4, 5 and 10 (F5 Fig 9.1); unverified for `katsura-11` | |
| `cyclic-7` | met | **no**: the family is not regular (AP Table 1 for Cyclic-6) | non-regular control |
| `eco-12` | met | **doubtful**: F5 finds 7 useless pairs on Eco-6 as stated, and 0 after factorizing ("Eco 6 fact"; F5 Fig 9.1, §9.1) | grobx hands over at round 2 (C1 §1) |
| `noon-7` | met | not established; F5 finds 0 useless pairs on Noon8 (F5 Fig 9.1) | |
| overdetermined MQ (`m = 2n`) | met | **impossible** (St Remark 3.3) | correctness-only in #857 |

Every corpus input meets the correctness assumptions, because they ask nothing of the input. The
regularity column predicts the *performance* outcome only, and #857 must record it rather than
assume it. A Hilbert-series check against the semiregular prediction (`hilbert.rs`) is the cheap
test.

## 5. Minimum metadata and its cost

| Item | Per | Size (Zeebra `Monomial` is `[u32; N]`) | Source |
|---|---|---|---|
| shifted signature (monomial + index) | basis element, matrix row, pending signature | `4N + 4` bytes; 48 B at `N = 11` | Lz Remark 25. F5 adds "an integer (the index k of r) and a power product t" per polynomial: "the extra memory cost is very small" (F5 §9.2) |
| sig-lead ratio rank | basis element | 4–8 B | RS §3.4 |
| syzygy-signature store (minimal generators) + 32-bit divmask | syzygy | `4N + 8` B | RS §4.2; GX "Syzygies from three sources" |
| Koszul queue | pending | lazily materialized, "almost nothing" | RS §3.3 |
| base-divisor bit triangle (optional) | basis-element pair | 1 bit | RS §3.5, App. B.2 |

Order of magnitude on MQ11: grobx makes 293,761 pair decisions and 14,425 rows (C1 §2, §5). At
`N = 11` that is under 15 MB of pending signatures at the very worst, against 392 MiB peak RSS for
shipping Zeebra (plan §2.1). The base-divisor triangle for 767 elements is 37 KB. **Metadata
memory is not the risk.** The risk is a signature basis much larger than the reduced one (RS
§B.4; GX biomd-147), which #857 must report.

Bookkeeping time is the unpriced cost. RS's slow cases are dominated by "the handling of monomials
and divisor queries" and the S-pair queue (RS §5, Table 1). grobx found that pruning the queue
cost 32% of chandra-11's instructions (GX "Syzygies from three sources").

## 6. Interaction with Zeebra's code

| Component | Today | Under a signature discipline |
|---|---|---|
| `src/grobner/pairs.rs` | `CriticalPair{degree, lcm, left, right, …}` (45-72); GM B/M/F on insertion (835-914); product/chain at selection (1276-1376); min-heap by lcm degree (363-405) | Pairs are keyed by **signature**, not lcm. The queue holds signatures (one per signature, EF Lemma 6.6). Selection is by least signature degree (EF Property 7.7(d)), not `DegreeThenLcm`. GM deletion is not reused (§3.6). The `PairSchedule` and Hilbert deferral variants do not apply. **Not reusable as is**; the signed queue is new code. |
| Monomials / polynomials | `Monomial = [u32; N]`; `MonicElement{leading_monomial, terms}` (`symbolic.rs:243-249`); append-only basis with stable indices (453-464) | Reused unchanged. A signature is a `Monomial` plus index (§3.1). The append-only basis fits RB, which never removes elements (EF Algorithm 2). `divmask.rs` serves the syzygy store. |
| `src/grobner/f4/symbolic.rs` | `close_over_rows` BFS (1106-1203); one reducer per monomial by `ReducerSelection` (`FirstApplicable` by default); both halves of each pair become rows (945-970) | **Reducer choice is constrained.** Only non-rewritable multiples are admissible, and the minimal-signature or least-ratio one is preferred (EF Algorithm 5, Property 13.3(a)). Within the admissible set another choice (e.g. sparsest) "may put a penalty on efficiency … correctness and termination are not affected" (EF Property 13.3(c)). If the chosen reducer's signature exceeds a target's, that use becomes a new S-pair (EF Property 13.3(b)). **Only one half of a pair is a reductant**; the other comes from preprocessing (F45 Alg. 3 and p. 8; GX "The F4-RB matrix"). `PairMultiples::Distinct` dedup carries over as one row per signature. Interning (`MonomialMap` handles) is reused. |
| `macaulay.rs` | columns sorted descending (227-260); reducers-first A/B/C/D split (466-495); `PreprocessedRow` provenance (`symbolic.rs:719-741`) | Rows carry a signature and are **sorted by signature**. Columns are unchanged. The A/B split is valid only for (reducer, target) uses with `s(reducer) < s(target)`. A reducer row whose column already has a pivot from an equal-signature row is dropped (GX "The F4-RB matrix", after EF §6.2). Provenance becomes exact (§3.2). |
| `reduction.rs` / `structured.rs` / `parallel.rs` / `linalg/echelon.rs`, `linalg/concurrent.rs` | pair rows in row-index order, reduced against reducer pivots and earlier pair-row pivots; first pair row to reach a column becomes its pivot (`echelon.rs:264-289`); concurrent path: first writer wins a `OnceLock` (`concurrent.rs:486-579`) | see §6.1. Sequential structured elimination **is** Lz Algorithm 8 once rows are sorted by signature and every pivot use is checked. The concurrent path's first-writer-wins rule is **unsound** under signatures and must change. |
| candidate finishing, `candidate.rs`, `reduce_batch_rows` | candidate rows fully back-reduced per batch (59-140) | Back-reduction of candidate rows by **lower-signature** pivots is a regular tail reduction and allowed (§3.2). Back-reduction by a higher-signature row is not. A new element is added when its lead *changed* (EF V&S 13.2(b); Alg 4 line 13), not only when its lead is new, so the extraction rule (`reduction.rs:443-457`) differs. |
| `interreduce.rs` | final minimal basis + matrix or division interreduction (`f4/mod.rs:566-643`) | **Reused unchanged** after the signature run, on the polynomial parts (§4 step 5). Signatures are dropped first. |
| `budget.rs`, `F4Error` | eight budget fields; typed `F4Error`; `should_stop` cancellation | Reused. Signature metadata bytes are charged to the live budget. A new `F4Error` variant is needed only for "unsupported order/field for the signature engine" (§7). |
| `FiniteField` | generic trait (`fields/finite_field.rs:98`) | No change. Nothing in the theory depends on the field, beyond EF §9.1's optional field-equation syzygies. |
| `F4Options` (public; not `#[non_exhaustive]`) | 25+ public fields, `baseline()`, `recommended()`, `Default` | **Not touched in #857.** Adding a field to a struct that is not `#[non_exhaustive]` breaks callers who build it with a struct literal. The engine takes its own options type (§8.2). |

### 6.1 Does parallel forward elimination over independent targets survive?

**Yes in principle, with two changes. It is unmeasured, and EF §15(c) calls it open.**

1. **Against a fixed pivot block** (reducer rows with settled pivots), targets are independent
   exactly as today, provided each use of a pivot `P` on target `T` checks `s(P) < s(T)`. Lz T4
   allows each reductant to be reduced modulo `AG^{<σ}` independently. A pivot that fails the
   check is skipped for that target, which leaves the target's term at that column. If it is the
   leading term, it becomes a new S-pair (EF Property 13.3(b)). The check is one signature
   comparison per pivot use, a fixed cost per inner-loop step, and the work stays parallel.
2. **Among targets** (pair rows that become pivots in this batch), the ownership rule must change
   from **first writer wins** to **least signature wins**. A target `T` that reaches a column
   held by `P` either:
   - is reduced by `P` if `s(P) < s(T)`, which is allowed; or
   - **displaces** `P` if `s(T) < s(P)`, and `P` resumes reduction against `T`, which is allowed
     because `s(T) < s(P)`.

   Every operation this performs is permitted (§3.2). Displacement chains are bounded by the
   number of targets at a column. When no row can move, each column's pivot is the
   least-signature row that leads there, which is what the sequential order (Lz Algorithm 8 line
   97, "by increasing order of sig f") produces. Lead terms per signature are then the same by EF
   Lemma 4.10. **Inference, not a published result:** the sequential reference is Lz T4/T5; the
   equivalence of the displacement scheme rests on EF Lemma 4.10 and the "only permitted
   operations" argument.
3. **Price.** Displacement costs extra row operations, and the atomic claim becomes
   compare-and-swap on a (signature-rank, row) word instead of a `OnceLock`. Signature ranks can
   be precomputed per batch as dense integers, because rows are sorted once. Whether this keeps
   M28/M29's 16-worker forward scaling is #857's question R3. Design 1 runs it **serially first**
   and parallelizes only after correctness. C1's ledger suggests even a serial signature engine
   could win on MQ11 if the work falls by an order of magnitude (§8.3), but that is an estimate.

## 7. Scope of the engine (supported fields, orders, fallbacks)

- **Fields:** every `FiniteField`. Correctness (§4) is field-independent. #857 tests at least
  GF(32003) and Goldilocks (plan §6.3 asks for two fields).
- **Monomial orders:** graded orders only (grevlex first, then `GradedLexicographic`). grobx's
  signature engine is graded-only (GX "End-to-end" step 2). Signature-degree batching needs a
  degree-compatible order for EF Property 7.7(d)'s sugar argument. Lex, `Weighted` and `Block`
  return a typed `Unsupported` error. The caller falls back to the shipping F4, as for any other
  refusal.
- **Inputs:** any finite generating set. Correctness does not depend on regularity, dimension,
  overdetermination or radicality (§3.7, §4.1).

## 8. Architectures compared

### 8.1 Integrated: signature-aware path inside F4's pair/symbolic/elimination code

Signatures go into `CriticalPair`, `PreprocessedRow`, `MonicElement` and the concurrent claim
word. A `F4Options` field switches the path.

- **Complexity:**
  - edits in `pairs.rs`, `symbolic.rs`, `macaulay.rs`, `linalg/echelon.rs`,
    `linalg/concurrent.rs`, `candidate.rs` and `options.rs`;
  - every hot loop gains a branch or a generic parameter;
  - roughly 3–5 kLOC changed across shared files (an estimate from §6's table, not a count).
- **Metadata memory:** the same per-row cost as isolated, plus a per-row cost on the
  **default** path unless the path is a generic parameter, which doubles monomorphization.
- **Maintenance:**
  - highest. Every future F4 optimization must preserve two disciplines;
  - `ReducerSelection`, `PairSchedule`, `PairMultiples`, Hilbert deferral and GM all need a
    signed and an unsigned semantics, or must be rejected in combination;
  - `F4Options` is not `#[non_exhaustive]`, so the switch is a breaking public-API change.
- **Expected performance:** same as isolated once correct. In the best case it reuses parallel
  elimination sooner.
- **Risks:**
  - collides head-on with M30-P3 on the shared files (plan §12);
  - risks the shipping default path (R6) while correctness is unproven (R4);
  - the subtlest invariant (signature-safe pivots) lives in code that 16-worker performance work
    keeps changing.

### 8.2 Isolated: separate engine behind its own entry point

A new module (e.g. `src/grobner/sigf4/`) with its own pair queue, symbolic preprocessing and
elimination driver, behind a Cargo feature (e.g. `research-sigf4`) and its own function, e.g.
`sig_f4_with_options::<N, F>(&generators, order, &SigF4Options)`. It reuses `FiniteField`,
`Monomial`, `MultivariatePolynomial`, `MonomialMap` interning, `divmask.rs`, the sparse row
kernels in `linalg/` (called with signature-checked pivot lookups), `interreduce.rs` for the final
basis, and `F4Error`, the budget fields and `should_stop`.

- **Complexity:** new code only; an estimated 2.5–4 kLOC including tests, with no edits to shared
  F4 files except possibly widening a `linalg` kernel signature.
- **Metadata memory:** per §5, with zero cost on the shipping path.
- **Maintenance:**
  - a second engine to keep correct;
  - mitigated by sharing the field, monomial, kernel and interreduction layers, and by `certify.rs`
    checking its output against the shipping F4.
- **Expected performance:**
  - design 1 is serial elimination, so it loses M28/M29 parallel forward scaling until §6.1 is
    ported;
  - the range is estimated from C1, not measured (§8.3).
- **Risks:**
  - duplicated symbolic preprocessing. Workstream P's parallel interning would not reach it
    automatically;
  - a bounded line can still sprawl, which is what the effort cap is for (§10.1);
  - a wrong-but-plausible basis is caught only by complete-basis comparison, which is mandatory.

### 8.3 Expected performance range (estimates, not predictions)

From C1 §2 and §5. Do not multiply these.

- **Ceiling.** Zero-ending rows carry 92.9% (MQ11) and 93.0% (Eco-12) of Zeebra's coefficient
  products. C1 prices removing them at −46% to −66% (MQ11) and −31% (Eco-12) of 16-worker process
  wall.
- **MQ11, serial.** Zeebra's serial F4 call does 20,377 M products in 39.1 s, about 1.9 ns per
  product. grobx's signature run charges 894.5 M. At Zeebra's serial rate that work is about 1.7
  s, plus unpriced bookkeeping, against 5.7 s for shipping Zeebra at 16 workers. **If** a Zeebra
  signature engine reached grobx's work level, a serial design could be roughly 2–3× faster on
  MQ11. If it reached only 2× less work than shipping, a serial engine would be about 3–4× *slower* (10.2 G products at 1.9 ns ≈ 19 s)
  at the 16-worker point.
- **Eco-12.** grobx abandons signatures at round 2, and a no-handover run has never been measured
  (C1 §6). The expected range runs from a loss to a small gain, and #716's arm 3 decides it.
- **Overdetermined inputs.** Expected loss (§3.7).

The decisive unknown is whether grobx's 22.8× is signatures or its engine (H-S1). That is Gate A1,
which is why this RFC's go/no-go waits for it.

### 8.4 Comparison

| | Integrated | Isolated |
|---|---|---|
| Edits to shared F4 files | many (§6 table) | none or near none |
| Public API change | breaking (`F4Options` literal) | additive (new fn + options type, feature-gated) |
| Risk to shipping default | yes | no |
| Conflict with M30-P3 | direct (plan §12) | none |
| Reuse of parallel elimination | sooner | later (§6.1 port) |
| Metadata on default path | yes, unless generic | none |
| Maintenance | two disciplines in one code path | two engines, shared lower layers |
| Removal if the line fails | invasive revert | delete one module |

## 9. Recommendation

**Architecture: isolated** (§8.2). The plan already prefers it for the P3 overlap (plan §12). It
keeps the shipping path untouched while correctness is unproven (R4, R6), and it makes the
two-design stop rule cheap to enforce.

**Algorithmic variant (design 1): batched F4-RB, after Lz Algorithm 8 and EF Algorithm 4.**

1. **Module order:** Schreyer (`<lt-pot`) with shifted signatures `lm(f_i)·e_i` (Lz Remark 25; EF
   §14.3(d); RS §5).
2. **Pair queue:** one pending entry per signature (EF Lemma 6.6). Each batch takes every pending
   signature of least signature degree (Lz Algorithm 8 line 89 allows any subset; GX "A batched F4
   over signatures" uses least degree).
3. **Criteria:**
   - syzygy criterion over minimal syzygy signatures from Koszul pairs, zero rows and coprime leads
     (EF Lemma 6.4, Def 6.2; RS §3.3);
   - rewrite criterion with `⊴_rat` / sig-lead ratio (EF Def 7.13, Cor 7.20; RS §3.4);
   - explicit product criterion (EF §12);
   - no GM deletion, and no base divisors in design 1 (RS §3.5 is an optimization).
4. **Symbolic preprocessing:**
   - one reductant per signature;
   - reducers are non-rewritable multiples, chosen by least sig-lead ratio (EF Algorithm 5;
     Property 13.3);
   - a reducer of larger signature than the reductant at its own lead becomes a new S-pair (EF
     Property 13.3(b)).
5. **Elimination:**
   - rows sorted by signature;
   - each target reduced in increasing signature order by pivots of strictly smaller signature
     (BFS §2.1; Lz Algorithm 8 line 98);
   - full (tail) regular reduction (EF §14.3(b)), serial in design 1;
   - zero rows' signatures enter the syzygy store (T6);
   - rows whose lead changed become new elements (EF V&S 13.2(b)).
6. **End:** drop signatures, then run the existing `interreduce.rs` path (§4 step 5).
7. **No handover, no randomization.** Budgets and unsupported inputs return typed errors (§7).

**Design 2 (only if design 1 is correct and the evidence asks for it):** the least-signature
parallel claim of §6.1. Alternatively, a reuse-not-restart handover (§3.8) if design 1 shows the
outgrowth pattern. Not both: the two-design limit counts design 2 as the last.

**Not recommended:** Matrix-F5. It is dense and degree-by-degree with an explicit degree bound
`D` (BFS algorithm, p. 10; EF Remark 3.1, "useful and efficient only if the … system is dense").
Zeebra's matrices are a fraction of a percent dense (#223 §4.2).

## 10. Predeclarations

### 10.1 For #857 (M30-S3), fixed before any code

**Effort cap.**

- At most **two designs** (plan §6.3).
- Design 1 is capped at **3,500 net added lines under `src/`, excluding tests**, and **6
  claim-lease sessions** (24 lease-hours) to a first end-to-end result that is correct on the
  correctness corpus.
- The whole of #857 is capped at **12 sessions**.
- Reaching either cap without a correct design-1 result counts as a failed design. Two failed
  designs end the line with a documented negative result (plan §13 stop rules).

**Correctness corpus** (both GF(32003) and Goldilocks, grevlex):

- the small controls below;
- deterministic constructions whose digests #857 must record in its first commit, before any
  timing:
  - **underdetermined**: `katsura-4` without its last generator;
  - **overdetermined**: `mq-random-10` plus 10 further random quadratics from the corpus
    generator at seed 1;
  - **non-radical**: `katsura-4` with each generator squared;
  - **positive-dimensional**: `cyclic-4`.
- Each output must equal the shipping F4's reduced basis coefficient for coefficient. On the
  smallest instances it must also equal `buchberger_reference`, with Singular agreement where
  available (plan §10.3).

**Performance corpus**, canonical SHA-256. The `wide-corpus-v1` identities come from
`research/wide-corpus/cases.json` at `fa7cc30d`; the MQ10 identities from #716's contract. If
#855 freezes different identities, #855's govern and both are recorded.

| Role | Instance | Field | SHA-256 |
|---|---|---|---|
| primary (by §12.1: **reported, not gating**) | `mq-random-11` | Goldilocks | `ee76de455c5ea571d6e8286152a4b4380b9d1ea323ee63dc8f889ffa11a92af5` |
| second family (by §12.1: **primary, gating**) | `eco-12` | 2⁶⁴−353 | `e9ef0fecf3906d9283e1ce003c4489d6921fb8718f2956c39c4aaa79e52a93cb` |
| second family (alternate; by §12.1: **the second family**) | `katsura-11` | Goldilocks | `036f0a35884e82d7bc3e3bc930ee9ccbe38fbddfc81e56fa8bf190a05ae1b955` |
| same family as primary | `mq-random-10` | GF(32003) | `16422dafcdb6487ea541f976f7754112b811c85af2b3537ed10fe4ef9c8f3d7f` |
| same family as primary | `mq-random-10` | GF(2³¹−1) | `72d0ad315fc25409792625465578d18329597d3ee183e75f257774d9215803b2` |
| non-regular control | `cyclic-7` | Goldilocks | `274e9a533b788e6e440803ad61ee44d2e0c691cec045c8c3bd6607ad8c42cb11` |
| small control | `katsura-4` | Goldilocks | `00f08d221047f38741f377f52893d3d561236feecf3bce5f9108d570937f35d3` |
| small control | `katsura-4` | 2⁶⁴−353 | `f2670d770ef9a866db0a407dbd1f05827563a9af3bc4485d51a99bb3eef307b6` |
| small control | `noon-7` | Goldilocks | `c146f701505e9d4a0b2ffaec9d0047b85eba1358f885c54196115c14ced7a933` |

**Report, per run** (plan §2.2 names; each one labelled):

- pairs rejected by mechanism (syzygy: Koszul / zero-row / coprime; rewrite; product);
- reductions to zero;
- zero rows;
- pair rows adding no rank;
- coefficient products, total and on zero-ending rows;
- separately: bookkeeping time (queue, criteria, rewriting), signature-metadata bytes, and
  signature-basis size against reduced-basis size (RS §B.4);
- process wall at 1 and 16 workers, peak RSS, verification status.

The products and walls avoided **by sound criteria** are reported separately from bookkeeping
cost (plan §6.3).

### 10.2 For #858 (M30-S4): thresholds confirmed, four tightened

Plan §6.4's thresholds are confirmed, and none is loosened. Four are tightened, as marked:

| Plan §6.4 threshold | This RFC |
|---|---|
| ≥25% better complete F4 process wall on a substantial, independently verified benchmark | confirmed; **tightened**: at the shipping 16-worker operating point, n ≥ 9, and the 95% bootstrap interval of the ratio entirely ≤ 0.80 |
| improvement on a second instance from a different family (MQ10 is not distinct from MQ11) | confirmed; **tightened**: ≥10% median process-wall improvement with the 95% interval excluding 1.0 (the plan left the size unstated) |
| no regression beyond 5% on small controls | confirmed; **tightened**: judged on the 95% interval's upper bound (≤1.05), not the median, at 1 and 16 workers |
| peak RSS ≤1.25× shipping, unless a fixed-budget advantage is separately shown | confirmed |
| correct across supported fields and orders, with fallback for the rest | confirmed; **tightened**: coefficient-for-coefficient equality with the shipping reduced basis on every corpus output, and a typed `Unsupported` route for every non-graded order (§7) |
| correct cancellation, fallback, typed budget errors | confirmed |
| documentation makes no claim that signatures remove all reductions to zero on arbitrary inputs | confirmed; T7 holds only for regular sequences and not under Schreyer order (§3.1) |

## 11. #223's findings, preserved

| #223 finding | Status after this RFC |
|---|---|
| F4 and F5 reach the same `D_reg`; signatures remove rows, not columns (DZD §4.1; [`signature-based.md`](signature-based.md) §4.0) | **holds**. Nothing in EF, Lz, RS or BFS changes the degree reached. |
| 33–60% of pair rows add no rank, hence a ≈2× *row* bound | **holds as a row bound**. **#835 changes its weight:** zero-ending rows carry ~93% of coefficient products, because they are reduced across their whole width (C1 §1). A row bound is not a work bound (plan §2.2). |
| "bad performance is expected when the system is overconstrained" ([`signature-based.md`](signature-based.md) §4.4) | **holds**, now checked against the source (F5 §9.2); reinforced by St Remark 3.3 and F5 Fig 9.1 (Trinks7). |
| basic F5 is only 1.26–1.29× faster than F4 on Cyclic 7–8 ([`signature-based.md`](signature-based.md) §4.4) | **holds for Cyclic** (F5 Fig 9.2, Cyclic table), **but it is not F5's whole record.** The Katsura table #223 left unquoted is legible in the PDF. Its F4/F5 CPU-time ratios are 2.7, 3.3, 5.6, 8.6, 12.0, 17.2 and 22.4 for Katsura 7–13 (F5 Fig 9.2, "Katsura n PII 400 Mhz (Speedup)"; e.g. F4 2097 s against F5 174.2 s at n = 11). These compare one author's two implementations on one machine, so they say nothing about Zeebra's engine. They do confirm that a ≈2× **row** bound is not a **time** bound, the point #835 makes with coefficient products. |
| F5's guarantee does not cover non-regular inputs | **holds** (T7); also absent under Schreyer order. |
| the GVW rewritable criterion is not a standalone pair criterion | **holds** (§3.4). |
| signatures constrain reducer choice; policies "may become invalid rather than merely suboptimal" | **refined.** The constraint is real (EF Algorithm 5), but within the admissible set any choice remains correct (EF Property 13.3(c)). The M16/M19 pricing does not carry over; the policies themselves are not invalid. |
| "a rewrite of F4's core" | **already retracted** by #223 (EF §13: "smaller changes … of some subalgorithms"). This RFC's isolated design avoids touching the core at all. |
| Matrix-F5 is the wrong variant for sparse matrices | **holds** (§9). |

## 12. Go / no-go

**RFC-side finding: no blocker.** §4 shows the design is sound on every input, §6.1 shows
parallelism is not ruled out, and §8 shows a bounded, isolated engine is feasible. The RFC
therefore does not itself produce a no-go. The plan makes the decision depend on #716's Gate A1.
A1 asks whether, on MQ11 or Eco-12, a grobx signature arm against its comparable
signature-disabled arm shows ≥2× less coefficient work **and** ≥25% less process wall, with RSS
≤1.5× and identical verified output.

**Decision rule, fixed now:**

| A1 outcome | Decision | Consequence |
|---|---|---|
| **Pass on MQ11** (with or without Eco-12) | **GO** | #857 is unblocked with §9's design 1 and §10.1's corpus; MQ11 primary |
| **Pass on Eco-12 only** (the no-handover arm) | **GO, narrowed** | #857 proceeds with Eco-12 primary. The second-family criterion must then use `katsura-11`, not MQ |
| **Work ≥2× but wall <25%** on both | **NO-GO** | the plan's gate needs both; bookkeeping ate the gain even in a mature engine. #857 and #858 close as not planned |
| **Work <2×** on both (H-S1 falsified) | **NO-GO** | grobx's advantage is its plain engine (R1). #857 and #858 close as not planned |
| **Inconclusive** (noise overlap, incomplete or failed arms) | **DEFER** | #857 stays blocked. If not resolved within M30, it is recorded as no-go for M30 |
| **RSS >1.5× or a verified-output mismatch** in the passing arm | **NO-GO** for that arm | if no other arm passes, as for work <2× |

**Status when the rule was written (2026-11-17):** #716 had posted no A1 result. The rule above
was committed (`4d04e5bc`) before A1 reported, and it is applied below without reinterpretation.

### 12.1 Outcome: A1 passes on Eco-12 only → **GO, narrowed**

A1's results, from the #716
[verdict](https://github.com/mfaulk/zeebra/issues/716#issuecomment-6955121982) and PR #867. Setup:
pinned grobx `1854835d`, one worker, seed 0, n = 5 per arm, every attempt verified coefficient for
coefficient. Work is grobx's `subtracted` charge over the whole call.

| Instance | Signature arm against signatures off (same combination policy) | Work off ÷ on | Wall on ÷ off [95%] | RSS | A1 |
|---|---|---:|---:|---:|---|
| MQ11 / Goldilocks | default (never hands over), combinations on | 1.69× | 0.569 [0.568, 0.570] | 1.01× | fail (work) |
| Eco-12 / 2⁶⁴−353 | default (hands over at round 2), combinations on | 1.00× | 1.001 | 1.01× | fail |
| Eco-12 / 2⁶⁴−353 | no handover, combinations on | 0.91× | 1.009 | 1.04× | fail |
| **Eco-12 / 2⁶⁴−353** | **no handover, combinations and zero tests off (exact)** | **6.33×** | **0.171 [0.170, 0.191]** | **1.03×** | **pass** |
| MQ11 / Goldilocks | same exact pairing; a declared extension **outside the gate** | 8.92× | 0.116 | 1.09× | not counted |

**Mechanical application.** MQ11 fails inside the gate. Eco-12 passes on a no-handover arm with
RSS ≤1.5× and verified output. That is the row "**Pass on Eco-12 only** (the no-handover arm) →
**GO, narrowed**: #857 proceeds with Eco-12 primary. The second-family criterion must then use
`katsura-11`, not MQ."

- **#857 is unblocked.** It runs §9's design 1, the §10.1 corpus and caps, with `eco-12` / 2⁶⁴−353
  (`e9ef0fec…`) as the primary instance and `katsura-11` / Goldilocks (`036f0a35…`) as the
  second-family instance for #858's second-instance criterion.
- **#858 stays blocked** on #857.
- **Neither the predeclared corpus nor any threshold changes.**

**What the passing arm does and does not show.** It is the exact pairing: both sides use
deterministic reduction and no randomized row combinations or zero tests. That is the only route
Zeebra may take (plan §13; #714), and it matches design 1 (§9 item 7: no randomization, no
handover). With grobx's randomized combinations on, plain F4 already recovers most of the saving
(0.91–1.69×). So the gain A1 measured is signatures against **exact** plain F4, which is Zeebra's
route. The gate remains grobx-relative: it shows signatures pay in an exact engine, not that they
will pay in Zeebra (plan §6.1).

**Handover.** Handover lost time on every instance where it fired (#716 verdict: MQ10 at both
primes, Cyclic-7). That confirms §3.8's choice of no handover in design 1, and it weakens the case
for handover as design 2. If design 2 is needed, the parallel claim of §6.1 is the candidate.

### 12.2 Reconciling the pass with Eco's doubtful regularity (§4.1)

F5 finds 7 useless pairs on Eco-6 as stated, against 0 after factorizing (F5 Fig 9.1, §9.1). So
the Eco family may well not be a regular sequence, and T7's no-zero-reduction guarantee does not
apply to it. Under Schreyer order T7 would not apply anyway (§3.1).

**The measurement is the evidence, not the theorem.** Correctness (§4) does not depend on
regularity. Regularity only predicted how much the criteria save, and on Eco-12 A1 *measured* the
saving directly: 6.33× less work against exact plain F4.

The risks for #857's evaluation:

1. **The saving may not transfer.** grobx's signature engine, with base divisors and
   randomization-free reduction, is not design 1. Eco-12 is not shown to be regular, so there is
   no theorem guaranteeing that a different correct signature engine sees a comparable reduction.
   #857 must report the §2.2 quantities on Eco-12 before any wall comparison, so that a shortfall
   can be attributed to the criteria rather than to engine speed.
2. **Residual zero reductions are expected on Eco-12.** Non-regular input plus Schreyer order
   leaves some (§3.7). #857 records them as reductions to zero, not as defects.
3. **Signature-basis growth.** On non-regular input the signature basis can outgrow the reduced
   basis (RS §B.4). This is open question 2, and it is now gating in practice for the primary
   instance.
4. **`katsura-11` is the second family.** F5 finds 0 useless pairs on Katsura 3–5 and 10 (F5 Fig
   9.1), and Faugère's own Katsura F4/F5 time ratios are 2.7–22.4× (§11). That is a favourable
   prior, but grobx has not been measured on `katsura-11`, so it is a prior, not evidence.

**MQ11 as a secondary, reported-not-gating instance.** The extra exact cohort (8.92× work, 0.116
wall, outside the gate) justifies keeping `mq-random-11` / Goldilocks in #857's runs. It is
already in the §10.1 corpus as "primary", and **that row is not changed here**. It is annotated:

- by the §12 rule it is **reported, not gating**;
- the pass is credited to Eco-12, and MQ results cannot satisfy #858's second-family criterion
  (plan §6.4);
- an MQ11 result in #857 is evidence for a later decision, not for this gate.

This is an annotation, not a change to the predeclared corpus or thresholds.

**Counter naming.** grobx's `low` counter counts eliminations by the low-ratio base divisor
(#716), not "low signatures" as plan §2.2's example reads. #857 reports its own rejections by
mechanism (§10.1). A base-divisor count only appears if design 2 adds base divisors (RS §3.5).

## 13. Open questions for #857

1. Do the displacement costs of the least-signature parallel claim (§6.1) keep forward scaling?
2. How large is the signature basis against the reduced basis on MQ11 and Eco-12 (RS §B.4)?
3. Does the product criterion catch anything on the corpus that the signature criteria miss
   under Schreyer order (EF §12)?
4. Is the homogenized `mq-random-11` regular in practice? A Hilbert-series check would answer it
   (§4.1).
5. Should symbolic preprocessing share Workstream P's parallel interning? If P3 lands first, the
   isolated engine can call it rather than duplicate it (plan §12).
