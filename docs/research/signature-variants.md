# Signature variants counted against the current engine (#1194)

**Measured at:** `eea7578a` (the engine and harness are those of `2247e2e9`; `eea7578a` adds only
the campaign script). Release build with `lto=thin`, `codegen-units=16`, on a macOS M-series
laptop, one worker, **unpinned, development only**, with three other agents building. The
deciding quantities are operation counts, which do not depend on the machine or the profile. The
clocks are one solve each and are given for scale only. Data, script and full tables:
[`research/1194-signature-variants/`](../../research/1194-signature-variants/README.md).
**Background:** [`signature-f4-rfc.md`](signature-f4-rfc.md) §3.1, §3.4 and §9 (the design
choice), [`signature-based.md`](signature-based.md) §5.1 (GVW as a criterion),
[`sigf4-hairer2-attribution.md`](sigf4-hairer2-attribution.md) (#1136/#1146).

## Summary

- **Three of the four candidates were runnable without a new engine**, and they now are, behind
  `research-sigf4-variants` (`sigf4::variants`): the module orders `<lt-pot>` (Schreyer, the
  engine's design), `<d-pot>` and incremental `<pot>`, and the rewrite orders `⊴_rat` (sig-lead
  ratio, the design) and `⊴_add` (newest element). Every completed cell (33 of 35) returns
  conventional F4's reduced basis; the other two stopped on the live-entry budget.
- **`⊴_add` is not a one-line switch.** RB adds singular elements to the basis (EF Algorithm 2,
  line 13). The engine discards them, which is sound under `⊴_rat` but gave Cyclic-7 a wrong basis
  under `⊴_add` with `<d-pot>` and `<pot>`. Under `⊴_add` the engine now keeps them; a regression
  test pins it.
- **Current GVW is the engine's own design.** GVW as now understood is RB with any compatible
  module order and `⊴_rat` (EF §11.5), so under Schreyer its counts are the baseline column. The
  first GVW (2010) is `⊴_add`, measured below. The 2013 revision's extra principal syzygies give
  the rewrite criterion nothing beyond the product check and the Koszul inserts the engine already
  makes (EF §12.3). **Predicted change: none.**
- **`⊴_add` under Schreyer is the only cell that cuts work on the signature-routed rows:**
  coefficient products −15.7% on Eco-12 and −13.2% on Katsura-11, unchanged on MQ11, +8.8% on
  Cyclic-7, and **13.4× on Hairer-2**. Elements, zero reductions and pairs created are
  unchanged on Eco-12 and Katsura-11; the saving is in the rows built from each target's
  rewriter (reducer rows −21% and −34%).
- **`<d-pot>` and `<pot>` remove reductions to zero but not work.** `<pot>` reduces nothing to
  zero on four of the five rows, as EF Table 7 predicts for regular inputs, yet costs 1.4–8.9×
  the products on Eco-12, Katsura-11 and MQ11. Both cut Cyclic-7 (0.75–0.77×) and Hairer-2
  (0.49–0.74×), the rows the dispatcher already sends to conventional F4.
- **None of them controls the oversized signature basis** (#1146). Hairer-2 keeps 1,320–1,700
  elements dominated at birth under every `⊴_rat` variant, and more under `⊴_add`, against 72
  in the reduced basis.
- **Recommendation: one bounded prototype, `⊴_add` under Schreyer on the signature route.**
  Predicted reduction in coefficient products: 13–16% on the Eco and Katsura families, none on
  dense MQ. It must be gated, because Hairer-2 regresses 13×; §5 gives the gate and the
  prototype's bounds.

## 1. What can be switched

The engine is F4-RB under Schreyer shifted signatures with the sig-lead-ratio rewrite order (RFC
§9). EF §15 names the three orders that distinguish signature algorithms: the module order, the
rewrite order and the pair order. Every efficient implementation uses the pair order `≼_s`
(increasing signature), and so does the engine. The other two are switchable:

| Choice | Cells | What changed in the engine |
|---|---|---|
| Module order | `<lt-pot>` (Schreyer), `<d-pot>`, `<pot>` | `Signature::cmp_in` reads the run's order; the pending queue is keyed by `(index, degree)` under `<pot>`, so the basis of `f_0..f_i` is complete before `f_{i+1}` enters |
| Rewrite order | `⊴_rat`, `⊴_add` | the rewriter returns the newest dividing element under `⊴_add`, and singular rows join the basis (§2) |
| Generator order | `<pot>` forward and reversed | the harness reverses the input (`--reverse`) |

All are compatible module orders (EF Def 2.2) and rewrite orders (EF Def 7.1), and batches of
increasing key are processed in increasing signature order, so Lairez Theorem 62 (RFC T4) covers
every cell. The choice is a thread-local set for one serial run, so the engine's comparison call
sites are unchanged. Multi-worker runs refuse a non-default variant. The feature is off in every
timed build.

`<pot>` here has **no F5C interreduction** between indices (EF §8.2). EF's `<pot>` figures include
it, so this `<pot>` is an upper bound on what an incremental engine costs (§4).

## 2. `⊴_add` needs singular elements in the basis

EF's RB adds every non-syzygy result to `G`, singular top s-reducible or not, because "RB computes
rewrite bases, and in order to fulfill the definition it has to add all these elements"
(EF §7.2, Algorithm 2 line 13). The engine discards singular rows (EF Lemma 5.1). Under `⊴_rat`
that is harmless: a singular element has the same sig-lead ratio as the element whose multiple
it equals, so the canonical rewriter of every signature it would cover is unchanged. Under
`⊴_add` the singular element is the newest rewriter of its multiples. Discarding it hands them
to an older element, and Lemma 7.5's rewrite-basis argument no longer applies.

A first probe ran `⊴_add` with the discard. On Cyclic-7 under `<d-pot>`/`⊴_add` and
`<pot>`/`⊴_add` the basis digest differed from F4's. The `<d-pot>` run returned 210 elements
against 209, and certification failed. With singular rows kept under `⊴_add`, all three module
orders certify and match F4. `test_newest_rewriter_keeps_cyclic_7_complete`
fails without the change. Every figure below is with singular elements kept.

## 3. Counts

Coefficient products (batch-elimination multiply-accumulates) against Schreyer / `⊴_rat` on the
same row. Wide-corpus rows at 2⁶⁴−353; Hairer-2 is the M34 public panel's `sd-hairer-2@p31`.

| row | Schreyer / rat | Schreyer / add | d-pot / rat | d-pot / add | pot / rat | pot / add | pot / rat, reversed |
|---|---:|---:|---:|---:|---:|---:|---:|
| Eco-12 | 1.000 | **0.843** | 3.089 | 49.932 | 8.853 | stopped | 2.395 |
| Katsura-11 | 1.000 | **0.868** | 2.978 | 2.603 | 1.924 | 1.820 | 20.524 |
| MQ11 (dense) | 1.000 | 1.000 | 1.355 | 1.355 | 1.371 | 1.371 | 1.371 |
| Cyclic-7 | 1.000 | 1.088 | 0.768 | 1.158 | 0.754 | 1.125 | 126.627 |
| Hairer-2 | 1.000 | 13.433 † | **0.491** | 4.671 | 0.742 | 15.882 | stopped |

"Stopped" means a batch needed more than the 6 GiB live budget: Eco-12 `<pot>`/`⊴_add` asked for
10.7 GB and Hairer-2 reversed `<pot>` for 8.0 GB. † was rerun under 14 GiB after asking for
6.8 GB. All 33 completed cells return F4's `m33-basis-v1` digest.

The baseline and the two cells that matter, in full (the rest are in
[`tables.md`](../../research/1194-signature-variants/tables.md)):

| row, variant | elements | dominated at birth | pairs | Koszul | zero-row | rewrite | targets | reducer rows | to zero | singular | products | on zero rows | ms |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Eco-12, Schreyer / rat | 1,884 | 849 | 1,773,677 | 568,867 | 723,995 | 27,878 | 2,897 | 67,359 | 1,013 | 0 | 585.6 M | 323.7 M | 1,426 |
| Eco-12, Schreyer / add | 1,884 | 849 | 1,773,677 | 542,063 | 752,743 | 27,713 | 2,897 | 53,277 | 1,013 | 0 | 493.6 M | 274.4 M | 1,225 |
| Katsura-11, Schreyer / rat | 554 | 17 | 152,351 | 86,602 | 32,267 | 4,371 | 699 | 14,174 | 145 | 0 | 200.1 M | 82.6 M | 455 |
| Katsura-11, Schreyer / add | 554 | 17 | 152,351 | 86,602 | 32,267 | 4,358 | 699 | 9,352 | 145 | 0 | 173.6 M | 79.3 M | 393 |
| MQ11, Schreyer / rat (= add) | 767 | 0 | 293,761 | 129,273 | 108,247 | 3,293 | 1,307 | 11,513 | 540 | 0 | 1,744.9 M | 898.6 M | 3,482 |
| Cyclic-7, Schreyer / rat | 883 | 442 | 388,502 | 263,712 | 94,138 | 15,457 | 1,014 | 5,606 | 128 | 3 | 18.2 M | 3.6 M | 61 |
| Cyclic-7, Schreyer / add | 974 | 533 | 472,551 | 322,534 | 112,014 | 19,175 | 1,102 | 6,814 | 128 | 0 | 19.9 M | 3.4 M | 69 |
| Hairer-2, Schreyer / rat | 1,873 | 1,700 | 1,752,053 | 1,007,732 | 549,814 | 39,135 | 2,411 | 541,814 | 339 | 199 | 751.0 M | 12.0 M | 2,793 |
| Hairer-2, Schreyer / add † | 3,653 | 3,481 | 6,658,324 | 3,835,588 | 2,294,019 | 124,646 | 3,992 | 12,953,130 | 339 | 0 | 10,088.4 M | 16.6 M | 76,214 |
| Hairer-2, d-pot / rat | 1,800 | 1,635 | 1,618,121 | 1,009,939 | 425,224 | 31,196 | 2,311 | 442,197 | 316 | 195 | 368.5 M | 13.8 M | 1,873 |

### 3.1 Rewrite order

- **Where no row is singular, `⊴_add` changes only which multiple is reduced.** On Eco-12 and
  Katsura-11 the Schreyer baseline has no singular rows. Under `⊴_add` the elements, the
  signatures, the zero reductions and the pairs created are identical, and the rewrite and
  duplicate rejections move by under 2%. What changes is the target row at each signature. The
  newest element dividing it is the most recently reduced one, and its multiple needs 21%
  (Eco-12) and 34% (Katsura-11) fewer reducer rows. EF §14.3(c) reports the same direction: "the
  choice of reducers w.r.t. `⊴_add` is better in terms of sparsity". It does not transfer as a
  wall-time claim, but here products and wall fell together (Eco-12 1,426 → 1,225 ms,
  Katsura-11 455 → 393 ms, one unpinned solve each).
- **Where rows are singular, `⊴_add` must keep them, and the basis grows.** Hairer-2 has 199
  singular rows under the baseline. Kept as elements, they and their pairs take the basis from
  1,873 to 3,653 elements and the products to 13.4×. Cyclic-7 has 3 and grows 10% in elements.
- **MQ11 does not move at all.** Dense MQ has no dominated elements (0 of 767), and every count,
  products included, is identical under both orders: the two picked the same rewriter at every
  signature.

### 3.2 Module order and signature-degree gaps

- **`<d-pot>` keeps the batches and degree gaps; it changes order within a degree.** A shifted
  signature's degree is the same under `<d-pot>` and Schreyer, so each batch holds the same
  signature degree and #1136's degree-fall factor (28× on Hairer-2) is untouched. Index before
  term within a degree reduces nothing to zero on Katsura-11 and MQ11 (EF Cor 7.17 for regular
  input), but the basis grows 2.0–3.4× (Eco-12 3,710 elements, Katsura-11 1,884, MQ11 1,832) and
  products 1.4–3.1×. It halves
  Hairer-2's products and cuts Cyclic-7's by 23%. That is the pattern of EF Tables 8–11 under
  Singular's single-pair RB, where `<d-pot>` is mostly the largest basis.
- **`<pot>` removes every zero reduction on the regular rows and pays for it in elements.** Zero
  reductions are 0 on Eco-12, Katsura-11, MQ11 and Hairer-2 (EF Cor 7.16, Table 7), so the 55% of
  Eco-12's products on zero rows disappears. But without F5C each index restarts from an
  unreduced basis: Eco-12 makes 4,801 elements and 861 k reducer rows against 67 k, and products
  are 8.9× (forward) or 2.4× (reversed). The generator order matters as much as the module
  order: reversing it moves Katsura-11 from 1.9× to 20.5× and Cyclic-7 from 0.75× to 127×. No
  single rule fixes it: putting the linear generator first is the cheaper order on Eco-12 (its
  reversed order) and Cyclic-7 (its forward order), and the dearer one on Katsura-11.
- **Schreyer is the best single module order on the rows the engine is routed to.** That agrees
  with EF §14.3(d). The exceptions, Cyclic-7 and Hairer-2, are rows `GradedEngine::Adaptive`
  already sends to conventional F4 (`Shipping(DegreeSpread)` on this build). It sends Eco-12,
  Katsura-11 and MQ11 to the signature engine.

### 3.3 Signature-basis size control (#1146)

`dominated_at_birth` counts elements whose lead an older lead already divided when they were
inserted. On Hairer-2 it is 1,700 of 1,873 under the baseline, 1,635 under `<d-pot>` and 1,320
under `<pot>`. The reduced basis has 72. No runnable variant brings the signature basis near the
reduced one, and #1146's other half, completeness work above the last minimal-basis element, is
not a module-order question. Discarding dominated elements is refuted (3.1% on Eco-12, #1146),
and `⊴_add` makes the basis larger wherever it changes it. **Nothing to prototype here.**

## 4. Variants that need a new engine: read and reasoned

GVW's own paper was not read. ePrint 2010/641 is on IACR ePrint only, the mirror returned HTTP 525
and the paper is not on arXiv. The reasoning below rests on the Eder–Faugère survey (arXiv
1404.1774, read in full for #856), which reconciles every GVW revision with RB.

| Variant | What it is (EF) | Predicted counts against Schreyer / `⊴_rat` | Why |
|---|---|---|---|
| **GVW, current (GVW_HS)** | RB, any compatible module order, `⊴_rat` (§11.5; "eventually super top-reducible" is the `⊴_rat` canonical rewriter, Vocabulary 11.12(a)) | **identical** under `<lt-pot>` | it is the engine's design. A GVW J-pair is the larger-signature half, which is the half the engine's ratio ranks pick |
| GVW, 2010 | as above with `⊴_add` (§11.5) | the Schreyer / `⊴_add` column: 0.84–13.4× | measured, with singular elements kept as RB requires |
| GVW, 2013 revision | adds all principal syzygies after every new element and interreduces `H` (§12.3, Step 4b (b1)) | **identical rejections and rows**; more bookkeeping | the engine already offers every new pair's Koszul signature to the store and skips only inserts that are provably covered (#1185). EF: the extra syzygies "do not give more information to the rewrite criterion than testing for Buchberger's Product criterion directly" |
| GVW's criteria inside conventional F4 | — | not definable | `signature-based.md` §5.1: the criterion presupposes signatures on every element |
| `<pot>` with F5C (incremental, reduced basis between indices) | §8.2; EF's `<pot>` figures include it | **unknown in sign on Eco-12.** No zero reductions (measured, above); the element count falls from this `<pot>`'s 4,801 toward Schreyer's 1,884 at best | EF's affine Eco-10/11 (Singular, single-pair RB, full s-reductions) put `<pot>`+F5C/`⊴_rat` at 2^23.1 and 2^26.2 multiplications against 2^24.9 and 2^28.0 for `<lt-pot>`/`⊴_rat`, about 3.5× fewer (Tables 10–11). On homogeneous Eco it is worse (Table 6). Here the measured `<pot>` without F5C is 2.4× (reversed) to 8.9×, and an F5C step would itself be a full interreduction per index |
| `<d-top>` | — | not run | EF Remark 14.1(a): "very long running times in most of the cases" |
| Product and chain criteria added to RB | §12 | identical | the engine checks the product criterion explicitly; the chain criterion is contained in the rewrite criterion (Eder 2014, EF §12.1) |

## 5. Recommendation

**One bounded prototype: `⊴_add` under Schreyer, on the signature route only.**

- **Predicted product reduction:** 15.7% on Eco-12, 13.2% on Katsura-11, 0% on dense MQ11. These
  are measured counts on one row each. The family prediction is 13–16% on Eco and Katsura rows
  whose Schreyer / `⊴_rat` run has no singular rows. Elimination is 68–84% of signature time on
  these rows ([`m35-baseline.md`](m35-baseline.md) §2), so if elimination time follows its
  products the wall would fall by about 11–13%. That is a hypothesis for the timed read, not a
  claim.
- **Why it is cheap:** the switch exists and is correct (§2). The prototype is a deciding read,
  not new code: the M35 panel's signature-routed rows under both rewrite orders, first by counts
  and then timed on the bench host under the plan's §8 rules.
- **The gate it needs:** a row with singular rows under `⊴_rat` can regress badly under `⊴_add`
  (Hairer-2 13.4×, Cyclic-7 1.09×). A rule that switches rewrite orders mid-run is not covered by
  EF Theorem 7.6, which fixes `⊴` for the run, so the gate has to be decided before the run: the
  dispatcher's route, or an input feature. Both regressing rows are already routed to
  conventional F4, which makes the route the obvious first gate. Whether any signature-routed
  panel row has singular rows is the first thing the count read must answer.
- **Stop rule:** drop it if any signature-routed panel row's products rise under `⊴_add`, or if
  the timed read on Eco-12 and Katsura-12 does not show a wall reduction outside the noise band.

**Not recommended:** `<d-pot>`, and `<pot>` without F5C. Both are measured worse on every
signature-routed row. `<pot>` with F5C is the only unmeasured variant whose published counts
favour it on affine Eco. It needs a new engine (per-index interreduction and re-seeding), and the
measured `<pot>` here is 2.4–8.9× worse before that step, so it stays a reading note. GVW is
already the engine's design.

## 6. What this did not do

- No timing claim: every clock is one unpinned laptop solve.
- One row per family. The 13–16% is two rows. The panel read in §5 is what turns it into a family
  claim.
- `<pot>` was run in the corpus order and its reverse only. Eco-12 and Katsura-11 list their
  linear generator last and Cyclic-7 first; no other order was tried.
- Hairer-2's `<pot>`/`⊴_rat` reversed and Eco-12's `<pot>`/`⊴_add` did not finish under 6 GiB
  and were not rerun.

## 7. Reproduce

See [`research/1194-signature-variants/README.md`](../../research/1194-signature-variants/README.md).
