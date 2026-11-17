# M29-C1: where the grobx gap is on Eco-12 and MQ11 at current code (#835)

**Measured at:** Zeebra `7e18d089` (`main` after #851; the counter binary was built from
`2fe11b8d`, whose production source is identical, plus this branch's `--hilbert` flag and
zero-row census in `examples/m29_cost_model.rs`). grobx: the pinned `1854835d` driver's stock
reports from the #738 wide-corpus campaign (controller `fa7cc30d`), read from
`research/wide-corpus/campaign.json.gz`; no grobx run was repeated. Timed Hilbert arms:
2026-11-17 under `benchlock zb-835`, load 1.6–1.7.
**Host:** Threadripper PRO 5995WX, as in [the M29 cost model](m29-baseline-cost-model.md) §2.
**Evidence:** [`research/m29-c1/`](../../research/m29-c1/README.md).
**Plan:** [`MILESTONE-COMPETITIVE-F4.md`](../MILESTONE-COMPETITIVE-F4.md) §7.

## 1. Findings

1. **About 93% of Zeebra's coefficient work on both targets goes into rows that reduce to zero.**
   Eco-12 reduces 7,202 pairs and 6,331 of them (88%) give no new element. MQ11 reduces 7,059
   pairs and 6,293 (89%) give none. Those rows take 98–99% of forward products and about 93% of all
   products (5.51 of 5.92 G on Eco-12, 18.92 of 20.38 G on MQ11). They also take 98% of serial row
   time. Rows that become pivots are cheap, because they stop at their first free column. A zero
   row has to be reduced across its whole width before it is known to be zero.
2. **grobx does 12.5× (Eco-12) and 22.8× (MQ11) less coefficient work, and it removes the zero
   reductions by two different contracts.**
   - **MQ11 / Goldilocks:** grobx never hands over to plain F4. It runs **signature F4 for all
     11 rounds**. Its signature criteria discard 277,271 of 293,761 pair decisions (124,617 low
     signatures, 152,654 syzygy). It performs 782 reductions with 26 zero reductions, in matrices
     of at most 2,130 × 3,836. This is a deterministic algorithm, not a randomized shortcut.
   - **Eco-12 / 2⁶⁴−353:** grobx hands over to plain F4 at round 2. It then reduces with
     `reduce=combinations`, the randomized row-combination route that #714 audited: 1,102 plain
     reductions with 226 zero. Its matrices are *larger* than Zeebra's (27,187 × 28,055 at most,
     against 24,045 × 24,913).
3. **The gap is not a smaller matrix, and not faster arithmetic on the same work.** It is the
   number of pair rows reduced to zero. Zeebra's per-product rate is already competitive, and
   M28/M29 parallelism has shortened its wall far more than its work.
4. **Hilbert-limited pair selection, already in the crate (M22), does not remove the zero
   reductions.** The prediction is exact on MQ11 (766 predicted, 766 found). But capping batches
   leaves the zero reductions at 6,293 and only makes each one cheaper: products fall 9–20%. Batch
   overhead takes the gain back serially on MQ11. At 16 workers on MQ10, the one target where it
   helps serially (1.14–1.21×), it is 1.00–1.03× at slack 400 and 0.55–0.58× at slack 100. On
   Eco-12 the prediction is wrong (10 predicted against 876 found), and deferral hits the 200 K
   column limit. **Rejected as a C2 route.**
5. **Only one candidate has a ceiling that reaches Goal B, and plan §7 does not authorize it in
   M29:** signature-compatible pair criteria. Everything inside M29's scope is priced in §5 below,
   and their ceilings sum well short of the 2.1× still needed.

## 2. Work ledger at current code (serial, `--discovery`)

Zeebra's counters are exact: `linalg::work`'s products include each pivot's leading entry. grobx's
`subtracted` is its stock budget charge, one entry per entry of each target or lane. #713 found it
within 2% of measured MACs on MQ10 (378.6 M charges against 371.0 M products), so it is used here as
the comparable work figure. It includes grobx's discarded signature rounds and final interreduction.

| Quantity | Zeebra Eco-12 | grobx Eco-12 | Zeebra MQ11 | grobx MQ11 |
|---|---:|---:|---:|---:|
| Route | plain F4, 23 batches | signature, 2 rounds → plain, 23 rounds | plain F4, 12 batches | signature F4, 11 rounds |
| Pairs reduced | 7,202 | 1,167 (65 sig + 1,102 plain) | 7,059 | 782 |
| Zero reductions | 6,331 | 226 | 6,293 | 26 (562 zero rows) |
| Elements found | 876 | 941 pivots, 743 final | 766 | 756 pivots, 767 final |
| Max matrix rows × columns | 24,045 × 24,913 | 27,187 × 28,055 | 8,904 × 9,436 | 2,130 × 3,836 |
| Initial matrix entries, total | 27.0 M | 20.5 M | 36.6 M | 18.5 M |
| Forward products | 5,581.0 M | — | 19,333.0 M | — |
| Finishing products | 342.7 M | — | 1,044.0 M | — |
| **All coefficient work** | **5,923.7 M** | **474.8 M** (charges) | **20,377.0 M** | **894.5 M** (charges) |
| … on rows that end zero | 5,511.7 M (93.0%) | — | 18,921.7 M (92.9%) | — |
| Forward work against inherited pivots | 81.4% | — | 75.4% | — |
| Serial F4 / process wall | 13.8 s (F4 call) | 1.62 s (process) | 39.1 s (F4 call) | 2.94 s (process) |
| Serial ms per element found | 15.8 | 2.2 | 51.0 | 3.8 |

MQ10 / 2³¹−1 has the same shape: 1,528 of 1,777 pairs reduce to zero, and they carry 91.0% of
541.9 M products.

Zeebra's forward stage does no reducer-against-reducer work (`reducer_target_operations` = 0 on
every target). All 31.8 M (Eco-12) and 26.3 M (MQ11) forward applications target pair rows. So
reducer reuse across batches (#809, Simplify) acts only on the cost *per* application of a row that
still has to be reduced. It cannot remove the row.

## 3. The two work contracts

**Zeebra** reduces every pair that survives the product, chain and Gebauer–Möller criteria. It
removes 386,626 (Eco-12) and 294,417 (MQ11) pairs. A surviving pair that reduces to zero is
detected only by reducing it. That is exact and needs no external check.

**grobx on MQ11** is signature F4 with a Schreyer module order. A pair whose signature is
dominated, or is the signature of a known syzygy (Koszul, or one found from an earlier zero
reduction), is dropped *before* any matrix row is built. For a regular sequence, such as dense
random MQ with as many equations as unknowns, this F5-type criterion predicts almost every
reduction to zero (26 survive of 782). The criterion is sound for grobx's algorithm. It is not a
filter that can be grafted onto unsigned F4 pairs: it needs a signature on every basis element and
signature-compatible reduction. That is what #223 declined and #716 is set up to reassess.

**grobx on Eco-12** abandons signatures at round 2 (its own handover heuristic). It then
reduces random linear combinations of the pair rows instead of the rows themselves, which detects
an all-zero block with one reduction. #714 audited this: the advantage is real, and it does not
survive exact verification, because proving the skipped rows are zero costs the work that was
skipped. M29 excludes uncertified randomized zero skipping (§12). So on Eco-12 even grobx has no
*exact* route of its own to the figure M29 compares against.

## 4. Hilbert-limited selection, measured

`--hilbert` selects `F4Options::hilbert`. It is complete by construction: no pair is discarded.
Serial counters (one worker, `--work`; walls taken alongside other runs, so only the
batch counts and products are comparable):

| Target | Mode | Batches | Pairs | Zero | Products | vs off |
|---|---|---:|---:|---:|---:|---:|
| MQ10 / 2³¹−1 | off (observe) | 10 | 1,777 | 1,528 | 542 M | — |
| | limited+0 | 1,479 | 1,775 | 1,523 | 297 M | −45% |
| | limited+100 | 21 | 1,781 | 1,530 | 381 M | −30% |
| | limited+400 | 10 | 1,777 | 1,528 | 447 M | −18% |
| MQ11 / Goldilocks | off (observe) | 12 | 7,059 | 6,293 | 20,377 M | — |
| | limited+0 | 6,304 | 7,059 | 6,293 | 16,315 M | −20% (619.6 s serial) |
| | limited+50 / +100 / +400 | 134 / 70 / 23 | 7,059 | 6,293 | 17,412 / 17,701 / 18,590 M | −15 / −13 / −9% |
| Eco-12 / 2⁶⁴−353 | off (observe) | 23 | 7,202 | 6,331 | 5,924 M | — |
| | limited+100 | 80 | 7,141 | 6,281 | 6,647 M | +12% |
| | deferred+0 | — | — | — | — | stops: 200 K columns |

Every completed run returned the production basis. Timed under `benchlock`, MQ10, n=5 at 16
workers and n=3 at one, one binary, process wall, off/mode:

| Target | limited+100, 1w | limited+400, 1w | limited+100, 16w | limited+400, 16w |
|---|---:|---:|---:|---:|
| MQ10 / 32003 | 1.142× | 1.209× | 0.580× | 1.025× |
| MQ10 / 2³¹−1 | 1.006× | 1.143× | 0.549× | 0.999× |

The product cut is real, but it comes from reducing the same zero rows later against a larger
basis. At 16 workers, forward and finishing are parallel and the cut no longer pays for the extra
batches. Not adopted.

## 5. Ranked C2 candidates (input to #836)

The base is the 16-worker process wall after #851 ([cost model §6b](m29-baseline-cost-model.md)):
Eco-12 3,088 ms, of which symbolic is 990, forward 808, finishing 207 and interreduction 520. MQ11
is 5,716 ms, of which symbolic is 1,316, forward 2,558, finishing 262 and interreduction 346. Goal B
needs ≤1,461 ms (−52.7%) on Eco-12 and ≤2,642 ms (−53.8%) on MQ11. Fractions are of process wall,
one mechanism at a time, and are not to be multiplied.

| Rank | Candidate | Mechanism | Eco-12 | MQ11 | Basis | In M29 scope? |
|---:|---|---|---:|---:|---|---|
| 1 | **Signature-compatible pair criteria** (#716) | drop pairs before rows are built | −31% | −46% to −66% | 93% of forward+finishing products removed. MQ11's upper end also removes symbolic and construction work in proportion to matrix rows: grobx builds 14,425 rows in total against Zeebra's 60,198. On Eco-12 grobx builds 1.11× Zeebra's rows, so no symbolic credit is taken | **No.** §7 excludes full signature F4 and §12 excludes unbounded signature development. Integration is XL |
| 2 | Parallel symbolic preprocessing with parallel interning (#832, M29-D) | parallelism, not work | −24% (ceiling −32%) | −17% (ceiling −23%) | the cost model's ≈4× stage speedup with parallel interning (§6), applied to the post-#851 symbolic stage | Yes, but it is M29-D, not C2 |
| 3 | #809 Simplify (reducer reuse) | cheaper inherited applications | ≤ −8% | ≤ −10% | 75–81% of forward is inherited-pivot work. Simplify shortens reducers but cannot remove a single zero row (§2); half of that work removed at today's efficiency | Yes; low expected value |
| 4 | Field-width kernels (C2-4) | operation cost | −6% | −8% | cost model §6, after parallel finishing | Yes; small |
| 5 | Less row materialization (C2-3) | construction + extraction | ceiling −7% | ceiling −6% | stages → 0 | Yes; small |
| — | Hilbert-limited selection | defer zero rows | measured +12% work | measured −9 to −20% work, no wall gain | §4 | Rejected |
| — | Randomized combinations | skip proving rows zero | — | — | #714 | Excluded (§12) |

**Recommendation for #836: select no C2 implementation in M29.** The only mechanism large enough
for Goal B is rank 1, which the plan excludes and which is a redesign, not a bounded change. Every
in-scope candidate has a ceiling below 10% of process wall at the 16-worker operating point, except
parallel symbolic, which belongs to M29-D. Ranks 2–5 sum to −53% (Eco-12) and −47% (MQ11) only if
symbolic preprocessing is driven to zero. At plausible efficiency they sum to about −45% / −41%
(and sums overstate combined gains). That does not reach the −53% Goal B needs. By plan §12's stop rule, Goal B should close as **target missed**, and this note should be
its explanation: Zeebra's remaining gap to grobx is the 88–89% of pairs it reduces to zero. On
MQ11, removing them exactly requires signatures.

A successor milestone could take rank 1 with #716 as its research gate. Its first test is cheap:
grobx with `signatures=false`, at the same seed on MQ11, measures how much of the 22.8× is the
signature criteria rather than grobx's plain-F4 engine.

## 6. What this does not show

- grobx's charges are a proxy for its products. They were validated against measured MACs only on
  MQ10/Gf31; the #713 observer refuses characteristics ≥ 2³¹, so no 64-bit grobx MAC count exists.
- grobx's report was not re-run at current upstream, only at the pin.
- The symbolic-stage share credited to rank 1 is an estimate from matrix row counts, not a
  measurement.
- Eco-12's "exact route" claim covers grobx's default only. A signatures-on, no-handover grobx run
  on Eco-12 has not been measured; it would say whether signatures alone help there.
