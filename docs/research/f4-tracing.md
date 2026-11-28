# Learn/apply tracing for conventional F4: does a trace transfer? (#1190, laptop stage)

**Measured at:** `cdabb83e` (`examples/f4_trace_study.rs --seeds=30`, binary sha256 prefix
`7bef87acdd1e20eb`), 2026-11-27, on a 14-core macOS/arm64 laptop. The release profile with thin LTO
and 16 codegen units (`CARGO_PROFILE_RELEASE_LTO=thin CARGO_PROFILE_RELEASE_CODEGEN_UNITS=16`). Every
figure is a deterministic count, and nothing is timed. The counts do not depend on the machine or the
profile.

**Verdict:** traces transfer. Over primes of 2³¹ − 1 the learned trace replays exactly on **660 of
660** same-shaped instances, across dense MQ, Katsura, Eco and Cyclic. The rows a replay would skip
carry **80–98 %** of the pair-row elimination products on every family except small dense MQ, where
they carry 10–40 %. **No divergence was silent** in 1,080 comparisons. Over small primes the
divergences are accidental coefficient cancellations, and nearly all of them are harmless to a
replay that keeps the learned rows (§3). That justifies item 3 of the issue, an apply prototype with
detect-and-fall-back. Item 3 is not done here. Neither is item 4, the one-worker learn + N applies
against N full solves.

## 1. The trace

`zeebra::grobner::f4::tracing` (new) records a trace from conventional F4 through the existing
`BatchObserver` hook, so it describes the live path. `F4Options::default()` and grevlex are used.
Each round stores:

- the basis size at the start of the round, and the selected pairs (`CriticalPair`: lcm, both
  indices) after the pair criteria;
- the matrix columns (monomials, descending);
- every row's origin (multiplier, basis index, reducer or pair component);
- every row's **fate** under a reference *reducers-first* forward elimination. Reducer rows are the
  pivots they already are. Pair rows are reduced in matrix order against those pivots and against
  earlier pair rows. A pair row ends **zero** or as a **pivot** at a column, and that pivot is *new*
  when the column is not the leading monomial of any row in the round;
- the coefficient products each pair row spent, counted as pivot-row entries per subtraction. This
  is the same unit as the engine's discovery counters.

The recorder checks every round against F4: the round's new pivots must equal what the basis grew
by before the next round. A drift between the model and the engine therefore panics and cannot
pass silently. The engine's own kernels may order rows differently. That changes *which* rows end
zero, but not how many.

`compare(learned, observed)` walks the two traces and stops at the first round that differs. It
classifies that round as follows:

| Divergence | Meaning | Would a replay notice? |
|---|---|---|
| `Pairs` | Different pairs were selected: the leading monomials already differ | yes |
| `Support` | Columns or rows the learned trace lacks: a term appeared | yes, a term has no reducer |
| `SupportShrank` | Columns and rows are a strict subset of the learned ones: terms cancelled | yes; a replay that builds the learned rows carries them as zero columns |
| `Reordered` | The same columns and rows in another order | yes; harmless if the replay keeps the learned order |
| `KeptRow` | Same matrix, but a row the trace kept ends zero or at another pivot | yes, a pivot vanishes or moves |
| `SkippedRow` | Every kept row ends as learned, but a row the trace saw vanish is nonzero | **no: silent**, and an element would be missed |
| `Length` | One run has more rounds | yes |

## 2. Transfer table

The trace is learned on seed 0 and compared with seeds 1–30. There are two variants.
`coefficients` redraws every coefficient on the template's support. `constants` keeps the seed-0
coefficients and redraws only the constants. For dense MQ, `constants` plants a fresh point: the
analogue of a new guessed value or CICO target. Dense MQ is #945's shape: 2n quadratics with every
monomial of degree ≤ 2, planted. "Zero rows" is the share of pair rows that end zero. "Zero-row
products" is their share of the pair-row products, which is the elimination work a replay skips.

| family | p | variant | transfers | first divergence | median matched rounds | rounds | pair rows | zero rows | pair-row products | zero-row products |
|---|---:|---|---:|---|---:|---:|---:|---:|---:|---:|
| dense-mq-6 | 2147483647 | coefficients | 30/30 | — | — | 4 | 129 | 26.4% | 24667 | 10.6% |
| dense-mq-6 | 2147483647 | constants | 30/30 | — | — | 4 | 129 | 26.4% | 24667 | 10.6% |
| katsura-6 | 2147483647 | coefficients | 30/30 | — | — | 6 | 117 | 41.9% | 66972 | 93.0% |
| katsura-6 | 2147483647 | constants | 30/30 | — | — | 6 | 117 | 41.9% | 66972 | 93.0% |
| dense-mq-8 | 2147483647 | coefficients | 30/30 | — | — | 5 | 313 | 30.7% | 256560 | 40.2% |
| dense-mq-8 | 2147483647 | constants | 30/30 | — | — | 5 | 313 | 30.7% | 256560 | 40.2% |
| dense-mq-9 | 2147483647 | coefficients | 30/30 | — | — | 6 | 966 | 47.3% | 3498716 | 87.8% |
| dense-mq-9 | 2147483647 | constants | 30/30 | — | — | 6 | 966 | 47.3% | 3498716 | 87.8% |
| dense-mq-10 | 2147483647 | coefficients | 30/30 | — | — | 6 | 1255 | 45.8% | 12047732 | 87.1% |
| dense-mq-10 | 2147483647 | constants | 30/30 | — | — | 6 | 1255 | 45.8% | 12047732 | 87.1% |
| dense-mq-8 | 65537 | coefficients | 30/30 | — | — | 5 | 313 | 30.7% | 256560 | 40.2% |
| dense-mq-8 | 65537 | constants | 30/30 | — | — | 5 | 313 | 30.7% | 256560 | 40.2% |
| dense-mq-9 | 65537 | coefficients | 30/30 | — | — | 6 | 966 | 47.3% | 3498573 | 87.8% |
| dense-mq-9 | 65537 | constants | 30/30 | — | — | 6 | 966 | 47.3% | 3498573 | 87.8% |
| dense-mq-8 | 541 | coefficients | 21/30 | kept-row 6, reordered 3 | 1 | 5 | 313 | 30.7% | 255228 | 40.2% |
| dense-mq-8 | 541 | constants | 29/30 | kept-row 1 | 2 | 5 | 313 | 30.7% | 255228 | 40.2% |
| katsura-8 | 2147483647 | coefficients | 30/30 | — | — | 8 | 542 | 50.6% | 4458805 | 96.1% |
| katsura-8 | 2147483647 | constants | 30/30 | — | — | 8 | 542 | 50.6% | 4458805 | 96.1% |
| katsura-8 | 65537 | coefficients | 30/30 | — | — | 8 | 542 | 50.6% | 4458611 | 96.1% |
| katsura-8 | 65537 | constants | 29/30 | reordered 1 | 3 | 8 | 542 | 50.6% | 4458611 | 96.1% |
| katsura-8 | 541 | coefficients | 0/30 | kept-row 4, reordered 26 | 4 | 8 | 542 | 50.6% | 4445094 | 96.1% |
| katsura-8 | 541 | constants | 0/30 | reordered 30 | 6 | 8 | 542 | 50.6% | 4445094 | 96.1% |
| katsura-10 | 2147483647 | coefficients | 30/30 | — | — | 10 | 2422 | 56.1% | 302027693 | 97.2% |
| katsura-10 | 2147483647 | constants | 30/30 | — | — | 10 | 2422 | 56.1% | 302027693 | 97.2% |
| eco-9 | 2147483647 | coefficients | 30/30 | — | — | 16 | 1442 | 42.9% | 9113453 | 97.6% |
| eco-9 | 2147483647 | constants | 30/30 | — | — | 16 | 1442 | 42.9% | 9113453 | 97.6% |
| eco-11 | 2147483647 | coefficients | 30/30 | — | — | 19 | 6255 | 47.2% | 929937457 | 98.1% |
| eco-11 | 2147483647 | constants | 30/30 | — | — | 19 | 6255 | 47.2% | 929937457 | 98.1% |
| eco-9 | 65537 | coefficients | 0/30 | reordered 30 | 13 | 16 | 1442 | 42.9% | 9111650 | 97.6% |
| eco-9 | 65537 | constants | 0/30 | reordered 30 | 13 | 16 | 1442 | 42.9% | 9111650 | 97.6% |
| eco-9 | 541 | coefficients | 0/30 | kept-row 3, reordered 24, support-shrank 3 | 9 | 16 | 1442 | 42.9% | 9090634 | 97.6% |
| eco-9 | 541 | constants | 0/30 | kept-row 1, reordered 26, support-shrank 3 | 11 | 16 | 1442 | 42.9% | 9090634 | 97.6% |
| cyclic-6 | 2147483647 | coefficients | 30/30 | — | — | 17 | 707 | 42.1% | 551867 | 80.2% |
| cyclic-6 | 2147483647 | constants | 30/30 | — | — | 17 | 707 | 42.1% | 551867 | 80.2% |
| cyclic-7 | 2147483647 | coefficients | 30/30 | — | — | 26 | 4537 | 46.5% | 93873678 | 84.4% |
| cyclic-7 | 2147483647 | constants | 30/30 | — | — | 26 | 4537 | 46.5% | 93873678 | 84.4% |

All 1,080 comparisons in total: 889 transfer exactly, 0 are silent, and 191 diverge detectably. Every
divergence is over p = 541 or 65537.

## 3. Reading

- **Large primes: the trace is a property of the shape.** At 2³¹ − 1 every family transfers on
  every seed. That includes Cyclic-7, a 26-round run, and both variants. The counts of rounds, pair
  rows and zero rows are identical across instances, as genericity predicts.
- **Small primes: the divergences are cancellations.** `Reordered` dominates. In the one case
  inspected (eco-9 over 65537, seed 1, round 13), the column set is unchanged and one reducer is
  emitted one position earlier. A basis element lost a term to an accidental zero coefficient, which
  changes the order in which symbolic preprocessing discovers monomials, but not the closure. The
  chance of this grows with the number of coefficients produced divided by p. That is why eco-9
  diverges at round 13 over 65537 but never over 2³¹ − 1. A replay that builds the learned rows in
  the learned order, with a zero coefficient where a term cancelled, is unaffected by `Reordered` and
  `SupportShrank`. Whether it then stays exact is what the apply prototype has to check.
- **`KeptRow` is the one real departure, and it is detectable.** It appears only at p = 541: 15 of
  180 comparisons there. A kept row vanished or its pivot moved, which a replay sees as a missing
  pivot.
- **Silent failure was not observed.** `SkippedRow` needs a row that vanished in the learned run to
  survive in another run whose kept rows all behave identically. In this model that means the
  learned instance was the degenerate one. 0 of 1,080. This is not a bound. The guarantee question
  stays as the issue states it: detect-and-fall-back covers every class above except `SkippedRow`,
  so an apply mode needs either an exactness check on its result or the label of a non-default mode
  (#1184).
- **What a replay skips.** On Katsura, Eco and Cyclic, 42–56 % of the pair rows end zero, and they
  carry 80–98 % of the pair-row products, because a row that ends zero is reduced all the way down.
  This matches the ≈ 93 % that `docs/research/m33-grobx-attribution.md` §3 reports for conventional
  F4. On dense MQ the share rises with n: 10.6 % at n = 6, 40 % at n = 8, 87–88 % at n = 9–10.
  A replay also skips pair selection and symbolic preprocessing, which this study does not count.
  It still pays for building the reducer rows; dropping the reducers that only zero rows use is a
  further saving, not counted here.

## 4. What is not done

- **Item 3, the apply prototype.** Build only the kept rows (plus reducers) from the trace, check
  every kept row's pivot against the learned one, and fall back to full F4 on any mismatch.
- **Item 4, the measurement.** One-worker learn + N applies against N full solves on dense MQ, Eco
  and one parameterized family, with bit-identical bases on every transferred instance. That
  belongs on the bench host. The counts above predict the elimination share, not the wall time.
- **The signature engine.** This trace is recorded from conventional F4 only.
- **Families that matter for AO hashes.** These include round-constant changes of an
  arithmetization-oriented permutation (Poseidon, Anemoi, Griffin) over BabyBear, KoalaBear and
  Goldilocks. The `constants` variant is the closest analogue measured here.

## Reproduce

```sh
CARGO_PROFILE_RELEASE_LTO=thin CARGO_PROFILE_RELEASE_CODEGEN_UNITS=16 \
  cargo run --release --example f4_trace_study -- --seeds=30
```
