# M35-H: signature pair bookkeeping, laptop stage (#1185)

**Measured at:** `2f84b2db` (candidate, on `7b95cbdd`) against `dca8a943` with the same counters
applied and the pair loop unchanged (the "Z0" arm; it is `2f84b2db`'s first half, never committed
alone). Both builds: release, `lto=thin`, `codegen-units=16`, on a macOS M4 Pro laptop,
**unpinned, development only**. No timing here is a deciding measurement; the counts do not depend
on the machine.
**Plan:** [`MILESTONE-FINITE-FIELD-COMPETITIVENESS.md`](../MILESTONE-FINITE-FIELD-COMPETITIVENESS.md)
§7.9, gate §9.9. **Background:** [`m32-signature-basis-growth.md`](m32-signature-basis-growth.md)
§§3–5 (#936), [`m33-grobx-attribution.md`](m33-grobx-attribution.md) §§2–3.

## Summary

- **The cost is the syzygy store's linear scans, at pair creation.** On Eco-12 / 2⁶⁴−353 selection
  is 21 ms of 209 ms of bookkeeping. The rest is the pair loop in `insert`, which runs 1.77 M times
  and scans the store twice per pair: once for the Koszul insert (305 M masks, 99.3% of those
  inserts are already covered) and once for the syzygy criterion (328 M masks, 90% hit). Rewriter
  scans (2.8 M entries) and the pending queue (142 k pushes) are small.
- **Adopted, exact:** ratio ranks (one integer comparison chooses the pair's larger half, and only
  that half's signature and Koszul signature are built) and query-first Koszul insertion (a
  covered pair's Koszul insert is a provable no-op and is skipped). Koszul inserts fall from
  1,773,677 to 494,283 and their masks from 305 M to 108 M. Laptop bookkeeping 209.5 → 146.3 ms
  (−30%), total 1,525 → 1,467 ms (−3.8%), medians of five alternated runs.
- **Not adopted:** Roune–Stillman's base divisors and pair bit-triangle, and the S-pair triangle
  queue (§3). Under the requirement that rejections per criterion do not move, base divisors save
  no scan here, and the queue is not where the time is.
- **Unchanged on every row checked:** the basis (`basis_m33`), every per-criterion rejection count,
  the queued pairs in order, the batches, and the syzygy store's kept and dropped entries.

## 1. Counters at Z0 (Eco-12 / 2⁶⁴−353, one worker)

`SigF4Statistics::pair_work`, printed by `sig_f4_study` as `pair_work`. "Masks" are syzygy-store
entries the 64-bit divisibility filter read; "tests" are the full divisibility tests it let
through.

| Data structure / criterion | calls | masks | tests | hits |
|---|---:|---:|---:|---:|
| store, Koszul inserts: covering check | 1,773,677 | 304,853,783 | 1,884,999 | 1,761,576 |
| store, Koszul inserts: sweep for multiples (kept inserts) | 12,101 | 7,042,665 | 12,333 | 2,880 |
| store, syzygy criterion at pair creation | 1,421,809 | 327,654,067 | 1,387,389 | 1,279,394 |
| store, syzygy criterion at selection | 18,435 | 6,176,561 | 14,667 | 13,468 |
| store, zero-row inserts | 1,013 | 1,217,626 | 1,197 | 1,013 |
| rewriter (`by_index`), entries scanned | 12,898 | 2,814,482 | 144,605 | — |

Pairs: 1,773,786 visited, 109 singular, 351,868 product, 568,867 Koszul, 723,995 zero-row,
27,878 rewrite, 98,267 duplicate; 142,415 queued, peak pending 91,102. The filter is nearly exact
(tests ≈ hits), so the scans cost what they are long: about 172 and 230 entries per call before
the first divisor.

Laptop clocks (unpinned): bookkeeping 209 ms, of which selection 21 ms and element hashing 2 ms.
The pair loop is therefore about 186 ms, and the two store scans per pair dominate it.

## 2. The change

Both parts are in `Engine::pairs` (`src/grobner/sigf4/engine.rs`); the pre-#1185 loop is kept as
the test-only `pairs_reference`, which `SigF4Options::reference_pairs` selects.

**Ratio ranks (RS §3.4).** For a pair `(β, γ)` the S-pair signature is the larger of
`(lcm/lm β)·s(β)` and `(lcm/lm γ)·s(γ)`, and the Koszul signature the larger of `lm γ·s(β)` and
`lm β·s(γ)`. Each Koszul candidate is its S-pair candidate times `gcd(lm β, lm γ)`, so both choices
are the comparison of the sig-lead ratios `s/lm` with the index as tie-break, which is
`ratio_cmp`. The engine keeps every element's rank in that order, ties sharing a rank, and compares
ranks. Equal ranks are exactly the singular pairs. Only the winner's two signatures are built. The
rewriter's ratio comparison uses the ranks too. Under `check_signatures` every new rank is checked
against `ratio_cmp` on the whole basis.

**Query-first Koszul insertion (RS §3.3; #936 §4).** The syzygy criterion runs on the pair's
signature `T` before its Koszul signature `K = gcd·T` is inserted, and a covered `T` skips the
insert: what covers `T` covers `K`, so the insert was a no-op. The query's answer, including which
source the earliest dividing entry has, is unchanged: past the product criterion `gcd ≠ 1`, so `K`
does not divide `T`, and the entries an insert drops are multiples of `K`, which do not divide `T`.
The surviving entries keep their order. Product-criterion pairs still insert `K = T`, as before.

**Tests.** `test_pair_bookkeeping_matches_the_reference_across_families` runs nine rows (Eco-7/8,
Katsura-5/7, Cyclic-5 under both orders, Noon-5, Reimer-4, a dense quadratic system; three fields)
both ways under `check_signatures`, and `…_under_the_parallel_cascade` one more. Each asserts equal
bases, equal queued-pair traces, equal batch traces, equal per-criterion counts, equal
query answers and the same store entries kept and dropped. The pinned rejection counts and batch
traces (`test_rejection_counts_by_mechanism_are_pinned`, `test_batch_traces_are_pinned_across_families`)
pass unchanged. `test_syzygy_store_matches_a_naive_model` checks the store itself, and
`test_pair_work_counts_add_up` the counters' identities.

## 3. What was not adopted, and why

**Base divisors with a pair bit-triangle (RS §3.5).** The criterion proves `s(S(α,γ)) | s(S(β,γ))`,
so a known syzygy at `(α,γ)` covers `(β,γ)` without a scan. Here the count by mechanism records
the source of the *earliest-inserted* dividing entry (`SyzygyStore::covering`), and that is part of
what must not move. The earliest divisor of `s(S(β,γ))` can precede the one that covered
`s(S(α,γ))` and carry the other source, so a base-divisor hit still needs the forward scan to the
first divisor, which is the scan the query already stops at. It saves nothing under this
constraint. It would pay only if the per-criterion attribution were relaxed (for example to
"covered" without a source), which is the owner's decision and not taken here.

**Newest-first covering scan for inserts.** An insert needs only whether some entry divides `K`, so
it may scan in any order. Scanning newest first cut the insert masks from 108 M to 79 M but moved
laptop bookkeeping by less than its noise (153.7 / 156.5 / 154.3 against 152.1 / 157.3 / 156.7 ms),
so it was dropped.

**S-pair triangle (RS §4.3).** The pending queue holds 142 k pushes on Eco-12 and selection is
21 ms in all, so a cheaper queue cannot recover a meaningful share.

**What remains.** The syzygy criterion at creation, 328 M masks for 1.42 M queries, is now the
largest bookkeeping cost. Under the earliest-source attribution any exact speedup has to make the
forward scan itself cheaper.

## 4. Laptop timings (unpinned, development only)

Medians of alternated runs, `sig_f4_study --engine sigf4 --digest-only`, one worker, ms.

| Row | runs | bookkeeping Z0 → H | total Z0 → H | `basis_m33` |
|---|---:|---:|---:|---|
| Eco-12 / 2⁶⁴−353 | 5 | 209.5 → 146.3 | 1,525 → 1,467 | `d4afa8a5…` both |
| Katsura-11 / 2⁶⁴−353 | 2 | 13.3 → 7.9 | 465 → 459 | `ae1041e0…` both |
| MQ11 (`mq-random-11`) / Goldilocks | 2 | 24.4 → 14.7 | 3,555 → 3,552 | `78e96ce2…` both |
| Cyclic-7 / Goldilocks | 2 | 21.3 → 14.7 | 69.8 → 61.5 | `4e67e231…` both |

Every per-criterion rejection count on these four rows is identical between the arms. The M33
prediction for this candidate was −150 ms on Eco-12; the exact change recovers about 63 ms
(4% of today's laptop wall), under §9.9's 8% bar on its own. The deciding read on R2, the time
share at Z0 on the bench host (the 233 ms figure) and the controls under §9.1 are left for the
bench host, and may score H in a bundle (§9.9).
