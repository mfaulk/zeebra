# Signature-basis terms as monomial-table ids (#1240), laptop stage

**Measured at:** `ffddf05c`, 2026-11-27, `examples/sig_f4_study.rs` with `--features research-sigf4`,
binary sha256 prefix `d412482ada0ad60c`. The build was the release profile with thin LTO and 16
codegen units (`CARGO_PROFILE_RELEASE_LTO=thin CARGO_PROFILE_RELEASE_CODEGEN_UNITS=16`), so absolute
times are not comparable with fat-LTO records. Every figure is a ratio or a difference within that
one binary. Machine: a 14-core Apple M4 Pro laptop running macOS. Runs used one worker, unpinned,
one process at a time, while other agents' builds held the load average between 4.5 and 11. Peak
RSS is `/usr/bin/time -l`'s maximum resident set size, because `peak_resident_bytes` reports nothing
on macOS. Evidence and scripts:
[`research/1240-sigf4-id-terms/`](../../research/1240-sigf4-id-terms/README.md).

**Verdict (laptop stage): the prototype works and the memory win is real; keep it as the
bench-host candidate. This is not the keep/reject decision.** On eight rows, holding each basis
term as a table id and a coefficient (`SigF4Options::id_terms`) gives a bit-identical basis
(`basis_m33` equal in every run). It cuts basis-term storage by 75–91%. Median peak RSS falls by
4–183 MiB, which is 12–54%. One-worker wall moves within 2% (median per-pair ratios 0.987–1.019),
inside the pairs' spread. The cost
is in symbolic preprocessing: its clock rises 1–11% under ids. Elimination dominates these rows, so
the rise does not show in wall. Rows where symbolic preprocessing is a large share of the solve were
not run, and §5 lists them for the bench host.

## 1. What the engine reads from basis terms

At `0ae2d64d`, `Element` held `terms: Vec<(Monomial<N>, F)>` and `hashes: Vec<u64>`. Every term
monomial of a basis element is a column of the batch that made it, so it is already interned in the
run's `MonomialTable`, together with its hash. The readers, in order of traffic:

| Reader | What it reads per term | Under ids |
|---|---|---|
| Symbolic preprocessing, target rows (`symbolic`) | monomial and hash of every term of `mult · element`, then one table probe for the product | the term's table entry (monomial and hash are adjacent there), then the same probe |
| Symbolic preprocessing, reducer rows | the lead's hash, then monomial and hash of `terms[1..]`, then one probe each | the same through the table |
| Elimination (`eliminate`, via `terms_of`) | coefficients only, zipped with the row's handles; monomials only under `check_signatures` | coefficients from their own vector |
| Column-space interreduction (`interreduce_in_columns`) | seed rows: monomial and hash, then a probe; reducer rows as in symbolic; then the coefficients | seed rows need no probe (`MonomialTable::local`, since the id is already known); reducers as in symbolic |
| Insertion (`insert`) | hashes every new term (`element_hashing`) | nothing: hashes come from the table |
| Lead-ideal handoff (`minimal_elements`, graded-lex only) | materializes the minimal elements as polynomials | rebuilt from the table, once |
| Final materialization (polynomial interreduction fallback, or the split and usage instruments) | every element as a polynomial | rebuilt from the table, once |
| Research instruments: `adjacent` and `split` take `(monomial, hash)` iterators; `symbolic_replay` reads monomials on its own threads | | `adjacent` and `split` collect the products from the table. `symbolic_replay` refuses ids, because it runs without the table |

The pair, ratio, criterion and reducer-search code reads only `Element::lead` and `Element::sig`.
Both are kept beside the terms, so none of that code changes. The claim cascade reads leads and
batch rows only.

So the one hot change is the symbolic read. By default a row reads its source element's terms
sequentially. Under ids each term is an indexed read of a table entry, 60 to 88 bytes on these rows. That read is
cheap next to the probe that follows, which already touches the table at random.

## 2. The prototype

`SigF4Options::id_terms`, off by default. `Element::terms` is an enum, either `Full { terms, hashes }`
or `Ids { ids: Vec<u32>, coeffs: Vec<F> }`. Readers go through a borrowed `View`, which inputs share
(they stay full). The default path's loops are the same code as before, the per-variant match is
hoisted out of every per-term loop, and every collected row is still allocated once at its length.
Each batch keeps its columns' run-wide ids (`Engine::column_ids`) only when the option is on.
`finish_batch` turns a new element's column entries straight into ids from them. Two statistics
were added to `SigF4Statistics`: `signature_basis_terms` and `signature_basis_term_bytes`, the
basis's term-storage heap bytes at the end.

Tests (`src/grobner/sigf4/tests.rs`, `test_id_terms_*`):

- On 12 configurations the id-backed run's pair trace, batch trace (every row and outcome, term for
  term), 14 counters and reduced basis all equal the default's. The configurations are Eco-7/8,
  Katsura-6/7, Cyclic-5/6, Noon-5, Reimer-4 and dense quadratics. They cover Goldilocks, the wide
  64-bit prime, GF(32003), GF(31) and Mersenne31, design 1, design 2 and the parallel cascade, the
  graded-lex handoff, both lanes, and the polynomial-interreduction fallback. Under
  `research-adjacent`, the run also uses the `Reuse` and `Flat` buffers.
- On GF(31), term bytes are at least 8 per term and below a quarter of the default's.
- The option is off by default.

The pinned batch-trace digests (`test_batch_traces_are_pinned_across_families`) are unchanged.

## 3. Laptop measurement

These are the issue's rows, plus MQ10, MQ11 and Cyclic-7. The dense quadratics are
`--generate mq-dense-N-s1 --m M`, which is `dense_mq_shaped(N, M, 1000, seed 1, planted)`. Each
row was run as pairs. The arms alternate which one goes first: 11 pairs on the six fast rows and 5
pairs on the two slow ones. The field route is used (no lane) unless the row says otherwise.
Medians, with each arm's min–max peak RSS in brackets. The last column is the median of the
per-pair `on/off` wall ratios, with their range.

| Row | Pairs | Basis | Basis terms | Term MiB default → ids | Peak RSS MiB default → ids | Δ RSS MiB | Wall s default → ids | Wall ids/default |
|---|---|---|---|---|---|---|---|---|
| Dense (14, 25), GF(31) | 11 | same | 306,496 | 19.9 → 2.3 | 64.6 [63–73] → 38.4 [37–48] | −26.3 | 2.31 → 2.30 | 0.999 (0.994–1.003) |
| Dense (16, 29), GF(31) | 5 | same | 1,231,901 | 89.3 → 9.4 | 191.8 [187–198] → 102.1 [96–110] | −89.7 | 18.57 → 18.58 | 1.000 (0.997–1.024) |
| Dense (18, 36), GF(31) | 5 | same | 2,522,841 | 202.1 → 19.2 | 380.3 [377–395] → 197.0 [193–201] | −183.3 | 65.55 → 65.58 | 1.000 (0.996–1.012) |
| Eco-12, wide 64-bit | 11 | same | 1,050,870 | 64.1 → 12.0 | 213.0 [204–234] → 167.8 [146–174] | −45.1 | 1.48 → 1.46 | 0.990 (0.962–0.999) |
| Katsura-11, 2^31 − 1 (`u64`) | 11 | same | 392,682 | 24.0 → 4.5 | 128.8 [113–143] → 111.2 [99–121] | −17.6 | 0.45 → 0.44 | 1.001 (0.977–1.011) |
| MQ10, GF(32003) (sparse ladder) | 11 | same | 117,509 | 5.8 → 0.9 | 49.3 [34–63] → 38.8 [31–52] | −10.5 | 0.19 → 0.19 | 0.987 (0.972–1.004) |
| MQ11, Goldilocks (dense wide-corpus) | 11 | same | 1,267,761 | 77.4 → 14.5 | 431.4 [414–478] → 378.4 [342–436] | −53.0 | 3.55 → 3.54 | 0.999 (0.993–1.067) |
| Cyclic-7, wide 64-bit | 11 | same | 177,721 | 8.1 → 2.0 | 20.8 [19–26] → 17.0 [13–26] | −3.8 | 0.06 → 0.06 | 0.995 (0.984–1.006) |
| Dense (14, 25), GF(31), `--lane` | 5 | same | 306,496 | 19.9 → 2.3 | 49.9 [49–50] → 39.0 [34–43] | −10.9 | 0.30 → 0.31 | 1.009 (0.975–1.032) |
| Dense (16, 29), GF(31), `--lane` | 5 | same | 1,231,901 | 89.3 → 9.4 | 198.2 [183–204] → 90.2 [88–122] | −108.0 | 2.01 → 1.99 | 1.019 (0.954–1.049) |

The default arm's term counts and bytes per term agree with #1198's count, which was made on the
bench host: 68, 76 and 84 bytes at n = 14, 16 and 18, and 64 on Eco-12. Katsura-11 is 64 bytes here
rather than 60, because this binary's 2^31 − 1 is `u64`-backed. That makes its id-backed term 12
bytes, not 8. The rows' bases and digests are in the evidence files. macOS peak RSS runs above the
issue's Linux figures (taken with #1198's counters on) by 20–80 MiB, and its spread is wide on the
small rows. Read the Δ column on the dense field-route rows, where the arms' ranges do not overlap.
There RSS falls by at least the term bytes saved: 26 MiB against 17.6 at (14, 25), 90 against 80
at (16, 29), and 183 against 183 at (18, 36). Why it falls by more on the first two was not
measured.

Stage clocks, medians over the same runs:

| Row | Symbolic ms default → ids | ids/default | Element hashing ms default → ids | Elimination ms default → ids |
|---|---|---|---|---|
| Dense (14, 25) | 22.0 → 23.2 | 1.053 | 0.77 → 0 | 2250.5 → 2248.5 |
| Dense (16, 29) | 97.4 → 108.2 | 1.111 | 3.16 → 0 | 18285.2 → 18300.1 |
| Dense (18, 36) | 258.4 → 284.9 | 1.103 | 6.70 → 0 | 64889.8 → 64919.4 |
| Eco-12 | 117.6 → 121.1 | 1.030 | 2.12 → 0 | 1133.9 → 1124.7 |
| Katsura-11 | 36.7 → 38.4 | 1.046 | 0.65 → 0 | 370.7 → 372.0 |
| MQ10 | 33.2 → 33.6 | 1.011 | 0.19 → 0 | 147.0 → 145.3 |
| MQ11 | 96.4 → 105.2 | 1.091 | 2.08 → 0 | 3215.4 → 3208.9 |
| Cyclic-7 | 7.1 → 7.3 | 1.035 | 0.24 → 0 | 36.6 → 36.8 |
| Dense (16, 29), `--lane` | 95.1 → 105.9 | 1.113 | 3.01 → 0 | 1727.4 → 1719.9 |

The issue left open whether the indirection costs or saves time. Here it costs: symbolic
preprocessing slows by 1–11%, and the slowdown grows with the basis (dense (16, 29) and (18, 36),
MQ11). Removing insertion's hashing gives back a quarter of that or more. On these rows the net
is at most 0.4% of the solve, at (16, 29) with the lane's roughly 10× faster elimination. That is
below what unpinned wall can resolve. On a row where symbolic preprocessing is half the solve, an 11% rise would be about 5% of wall.

## 4. Reading it against the issue

- The hypothesis holds: every basis term is already a table entry, and storing an id instead costs
  no new interning. On a 32-bit field, term storage is 8 bytes per term, as predicted (9.4 MiB at
  (16, 29), against the issue's estimate of 9.4).
- It is outside `max_live_bytes`, as the issue notes, so it does not address #1186's stops.
- Against #1030 §8's 16–17 MiB for M4GB at (16, 29): ids take Zeebra's laptop peak from 192 to
  102 MiB (field route) and from 198 to 90 MiB (lane). That closes about half of the gap; the
  issue expected basis storage to be most of it. The remaining 70–85 MiB on macOS is batch live memory
  (#1078), the monomial table and the allocator, in proportions not measured here.

## 5. What remains for the bench host

The keep/reject decision needs a bench-host run, as #1195 requires:

1. **Paired, pinned peak RSS and one-worker wall** (`peak_resident_bytes`, a reserved CCD) on the
   same rows, at a fat-LTO release build.
2. **Regime gate.** Basis-heavy rows: the dense `(n, m)` shapes, MQ11 and Eco-12, as development
   rows, plus held-out dense shapes and seeds. The win to score is peak RSS. Wall must not regress.
3. **Dispatch gate.** Rows where symbolic preprocessing is a large share of the solve: grid-5×5,
   Noon-9, and the M35 symbolic-heavy rows (`docs/research/adjacent-round-reuse-census.md` §6). These
   are where the 3–11% symbolic rise could reach wall. If it does, the rule to test is a cheap one:
   ids once the basis's term bytes pass a threshold. The basis's size is known per batch.
4. **Multi-worker runs** (design 2 and the claim cascade). The tests cover their correctness but
   nothing measured their wall.

If the dispatch gate shows no regression, ids could become the default and drop the `Full` arm. The
`adjacent` and `split` instruments would then read products through the table, and
`symbolic_replay` would need the table shared with its threads.
