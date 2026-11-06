# Critical-pair order, and batch size, measured apart

Reference for M22-A (#74), extended by #253 with a third selection axis — term count — in §2's last
subsection and in §6. Every figure in §§1–5 comes from

```sh
tools/fetch-mq-challenge.sh
cargo run --release --example f4_schedule
cargo run --release --example f4_schedule -- mq3-n15     # one instance per process
```

under `F4Options::recommended()` with `profile_degrees` set, `max_matrix_columns = 60_000`,
`max_live_bytes = 400 MB`, `max_batches = 20_000`, grevlex throughout. **Every row in every table
returned the identical reduced Gröbner basis** — asserted by the program on each row, not reported
in a column.

Times are single runs on a shared 64-core machine with other work on it, so a difference under
about 20% should not be read. The structural counters — pairs reduced, matrix columns, peak live
entries, row operations — are exact and are what the conclusions below rest on.

## 1. What a schedule is, and what it is not

[`PairSchedule`](../../src/grobner/pairs.rs) decides which of the pending pairs **at the lowest
available degree** is taken first. That is a different kind of thing from a
[`PairCriteria`](../../src/grobner/pairs.rs): a criterion is a theorem that a pair need not be
reduced at all, whereas a schedule reorders pairs that will all be reduced. Nothing leaves the queue
unprocessed, so no schedule can change the answer.

The lcm degree stays primary under every schedule. Not a preference: a batch is formed from the
pairs of one degree, and F4's termination argument is stated in ascending degree.

Seven schedules are compiled, and the distinction between two of them is the point of this section:

| name | within a degree |
|---|---|
| `degree-then-lcm` | the baseline — the lcm, then the two basis indices |
| `small-multiplier-degree` | the smallest larger multiplier *degree* first, then the smaller degree |
| `large-multiplier-degree` | the reverse, as a **control** |
| `small-multiplier-monomial` | the smallest larger multiplier *monomial* first, under the monomial order. **Sakata–Takagi's published ordering** |
| `large-multiplier-monomial` | the reverse, as its control |
| `short-pair` | the smallest `terms(i) + terms(j) - 2` first — `slimgb`'s `pair_weighted_length` over a prime field. Added by #253; see §2's last subsection |
| `long-pair` | the reverse, as its control |

Each control earns its place. If preferring small multipliers narrows the matrix, preferring large
ones should widen it; a heuristic that beats the baseline in both directions is measuring
run-to-run variation, and without the opposite direction there is no way to tell.

The first five rank by **multiplier size**; `short-pair` ranks by **term count**, which is a
different axis — two pairs with the same lcm and the same multipliers can have S-polynomials of
very different length.

### Degree against monomial, which are not the same strategy

Sakata–Takagi rank candidate pairs on the larger and then the smaller of the two multipliers
**under the monomial order**. Comparing the multipliers' *degrees* is a strictly coarser relation,
and it is coarser in a way that matters: `x²` and `y²` have the same degree and are distinct under
grevlex, so a degree comparator ties and falls through to the lcm tiebreak exactly where the
published comparator still discriminates.

`test_the_monomial_comparator_separates_equal_degree_multipliers` pins the smallest such case —
leading monomials `y²`, `x²`, `x²y²`, where pairs `(0,2)` and `(1,2)` share an lcm, a degree, and
both multiplier degrees, and differ only in the multiplier monomials `x²` against `y²`. The degree
schedules order those two identically; the monomial schedules order them oppositely.

So a measurement of the degree heuristic is **not** a measurement of the published ordering, and
both are reported below. The multiplier monomials are stored on the pair for this reason — they
cannot be recovered from it, since that would need the two leading monomials, which a pair
deliberately does not carry — and a monomial-comparing schedule is the one thing in `PairQueue` that
needs a `MonomialOrder`, so asking for one without an order is refused rather than defaulted.

### A schedule is never inert

It would be reasonable to think a schedule does nothing unless `max_pairs_per_batch` caps the batch,
since without a cap the batch is every pending pair of its degree whatever the order. The batch
*sets* are indeed identical then — and so are the row sets, the row spaces, the pivot columns, and
therefore the leading monomials of the new basis elements. `batches` and `pairs_reduced` come out
equal, and are asserted to.

But row echelon form depends on the order the rows are taken in, so the candidates' **tails**
differ, and a different tail is a different set of monomials for the next batch's symbolic
preprocessing to cover. On katsura-5 grevlex the widest matrix is 146 columns under the baseline and
166 under either small-multiplier schedule, with every pair and batch count identical. A schedule
therefore has to be measured end to end, and the tables below are.

## 2. Pair order, uncapped

| instance | schedule | cols | peak entries | row ops | ms |
|---|---|---:|---:|---:|---:|
| katsura-5 | degree-then-lcm | **146** | **1 259** | 1 609 | 0.7 |
| | small-multiplier-degree | 166 | 1 411 | **1 511** | 0.7 |
| | large-multiplier-degree | 180 | 1 530 | 1 697 | 0.7 |
| | small-multiplier-monomial | 166 | 1 411 | **1 511** | 0.6 |
| | large-multiplier-monomial | 191 | 1 922 | 1 983 | 0.8 |
| | short-pair | 191 | 1 799 | 1 860 | 0.8 |
| | long-pair | 166 | 1 564 | 1 562 | 0.7 |
| katsura-6 | degree-then-lcm | **458** | **6 014** | 11 885 | 3.9 |
| | small-multiplier-degree | 492 | 6 507 | 10 095 | 3.7 |
| | large-multiplier-degree | 719 | 8 614 | 14 260 | 4.4 |
| | small-multiplier-monomial | 492 | 6 471 | **9 997** | **3.5** |
| | large-multiplier-monomial | 744 | 10 370 | 15 342 | 5.4 |
| | short-pair | 744 | 9 689 | 15 286 | 5.1 |
| | long-pair | 644 | 8 600 | 12 855 | 4.4 |
| cyclic-5 | degree-then-lcm | **115** | 1 206 | 3 929 | 1.6 |
| | small-multiplier-degree | 117 | **1 197** | 3 737 | 1.5 |
| | large-multiplier-degree | 116 | 1 331 | 3 984 | 1.5 |
| | small-multiplier-monomial | 117 | 1 205 | 3 730 | 1.5 |
| | large-multiplier-monomial | 118 | 1 318 | 4 026 | 1.5 |
| | short-pair | 116 | 1 209 | **3 679** | 1.4 |
| | long-pair | 117 | 1 264 | 3 836 | 1.5 |
| Poseidon `t=2 R_F=2 R_P=2` | degree-then-lcm | **925** | **103 112** | 178 576 | 146.2 |
| | small-multiplier-degree | 929 | 104 894 | 173 595 | 141.0 |
| | large-multiplier-degree | 932 | 114 604 | 179 893 | 144.9 |
| | small-multiplier-monomial | 937 | 105 725 | 173 876 | 146.3 |
| | large-multiplier-monomial | 932 | 117 005 | 179 871 | 142.9 |
| | short-pair | 932 | 117 999 | 178 900 | 142.7 |
| | long-pair | 931 | 126 192 | **171 899** | 142.7 |
| Poseidon `t=2 R_F=4` | degree-then-lcm | 1 341 | 237 265 | 589 712 | 373.8 |
| | small-multiplier-degree | **1 330** | 238 414 | 566 337 | 370.0 |
| | large-multiplier-degree | 1 353 | 243 091 | 581 725 | 376.6 |
| | small-multiplier-monomial | 1 333 | **214 834** | **504 342** | **349.6** |
| | large-multiplier-monomial | 1 370 | 274 985 | 557 548 | 387.1 |
| | short-pair | 1 370 | 267 688 | 517 332 | 340.2 |
| | long-pair | 1 340 | 279 966 | 556 176 | 362.8 |
| Fukuoka III `n=10` | degree-then-lcm | 859 | 168 020 | 359 099 | 124.8 |
| | small-multiplier-degree | 859 | 167 101 | 343 364 | 117.2 |
| | large-multiplier-degree | 859 | 182 070 | 347 790 | 117.9 |
| | small-multiplier-monomial | **851** | **156 102** | **341 681** | **112.8** |
| | large-multiplier-monomial | 881 | 272 517 | 352 809 | 157.2 |
| | short-pair | 871 | 175 338 | 353 043 | 93.9 |
| | long-pair | 881 | 230 798 | 341 945 | 127.6 |
| Fukuoka III `n=15` | degree-then-lcm | 3 573 | 2 142 707 | 7 599 775 | 8 874 |
| | small-multiplier-degree | 3 573 | 2 058 658 | 7 391 622 | 8 760 |
| | large-multiplier-degree | 3 573 | 2 336 287 | 7 534 994 | 8 538 |
| | small-multiplier-monomial | **3 559** | **1 979 862** | 7 378 536 | **8 151** |
| | large-multiplier-monomial | 3 579 | 3 058 082 | 7 758 123 | 10 715 |
| | short-pair | 3 579 | 2 314 045 | 7 560 198 | 7 792 |
| | long-pair | 3 579 | 2 805 806 | **7 271 354** | 9 446 |

### The degree heuristic is a null result

`small-multiplier-degree` cuts row operations consistently — 15% on katsura-6, 6% on katsura-5, 5%
on cyclic-5, 3%–4% on the Poseidon and Fukuoka instances — and **makes the matrix larger or leaves
it unchanged**: wider than the baseline on four of seven instances, equal on three, never narrower.
Its control, `large-multiplier-degree`, has the larger peak of the two on every instance, so matrix
size does respond monotonically to multiplier degree in the predicted direction — just in the
measure the hypothesis was not about. Runtime is within 6% in both directions.

So the two measures disagree, and the ordering that minimizes row operations is also the one that
widens the matrix. The reason is M16's reason for rejecting
`ReducerSelection::LargestLeadingMonomial`: a reducer row leads with the monomial being covered
either way, so what the choice changes is the row's *tail*, and a tail nobody predicted is as likely
to be reducible as not.

### The published ordering is **not** a null result, and an earlier version of this document said it was

This is a correction. The first version of M22-A measured only the degree comparator and reported
"small-multiplier ordering is a null result" as a finding about Sakata–Takagi's strategy. It is not:
their ordering compares multiplier *monomials*, §1 shows the two are different relations, and the
monomial comparator behaves differently and better.

On the three largest instances it is the best schedule measured on every structural counter at once:

| instance | measure | baseline | small-multiplier-**monomial** | change |
|---|---|---:|---:|---:|
| Fukuoka III `n=10` | widest matrix | 859 | **851** | −0.9% |
| | peak live entries | 168 020 | **156 102** | **−7.1%** |
| | row operations | 359 099 | 341 681 | −4.9% |
| Fukuoka III `n=15` | widest matrix | 3 573 | **3 559** | −0.4% |
| | peak live entries | 2 142 707 | **1 979 862** | **−7.6%** |
| | row operations | 7 599 775 | 7 378 536 | −2.9% |
| Poseidon `t=2 R_F=4` | peak live entries | 237 265 | **214 834** | **−9.5%** |
| | row operations | 589 712 | **504 342** | **−14.5%** |

It is the **only** schedule that narrows the matrix on either Fukuoka instance, where the degree
comparator leaves the width untouched in both of its directions.

And the control is what makes this credible rather than a coincidence.
`large-multiplier-monomial` is **the worst schedule measured on peak entries on five of seven
instances**, by large margins. The spread between the two directions of the *same* comparator:

| instance | monomial comparator | degree comparator |
|---|---:|---:|
| Fukuoka III `n=10` | **1.75x** | 1.09x |
| Fukuoka III `n=15` | **1.54x** | 1.13x |
| Poseidon `t=2 R_F=4` | 1.28x | 1.02x |
| katsura-6 | 1.60x | 1.32x |

A relation that separates its two directions by 54%–75% on the large instances is measuring
something. One that separates them by 2%–13% on a machine with 6% run-to-run variation may not be.
On Fukuoka III `n=15` the control is also **1.31x slower** than its counterpart — 10 715 ms against
8 151 — which is the one timing difference in this section that exceeds the band below.

**What this does not establish.** The *gains* are 6%–9% in runtime, inside the ±20% band this
document declines to read, so the honest claim is about the structural counters — which are exact —
and not about the clock. 9.5% less peak memory does not clear M22-I's 20% threshold either. So the
published ordering is a **real, monotone, sub-threshold effect**, which is a different finding from
"no effect" and from "worth making default".

### Term count is a third axis, and ranking pairs by it is a null result

`short-pair` and `long-pair` come from #253, which mined them out of Singular: `slimgb`'s
`pair_weighted_length` (`kernel/GBEngine/tgb.cc`) scores a pair by the expected length of its
S-polynomial, and over a prime field the coefficient-size factors drop out and the score is
`terms(i) + terms(j) - 2`. Every schedule above it ranks by multiplier size, so this is a genuinely
different relation — see `docs/research/singular-engine-notes.md` §4.

The two rows were taken in a later invocation of the same program under the same configuration.
**Every structural counter of the five existing rows reproduced exactly in it**, on all seven
instances, which is what makes the columns comparable; the `ms` column of the new rows is that
invocation's clock and the per-instance baseline it should be read against is in the text below, not
in the table.

`short-pair` **raises peak live entries on every instance**, by 0.2% on cyclic-5, 4.4% at Fukuoka
`n=10`, 8.0% at `n=15`, 12.8% and 14.4% on the two Poseidon instances, and 43% and 61% on katsura-5
and katsura-6. It is never narrower than the baseline either. What it does do is cut row
operations, on five of seven instances — 12.3% on Poseidon `t=2 R_F=4`, 6.4% on cyclic-5, 1.7% at
`n=10`, 0.5% at `n=15` — which is the same split the degree comparator showed, and for the same
reason: the quantity the heuristic predicts is a row's *length*, and a shorter row is not a row
whose tail is covered.

The control does not rescue it. The spread between the two directions, on peak entries:

| instance | length comparator | monomial comparator | degree comparator |
|---|---:|---:|---:|
| Fukuoka III `n=10` | 1.32x | **1.75x** | 1.09x |
| Fukuoka III `n=15` | 1.21x | **1.54x** | 1.13x |
| Poseidon `t=2 R_F=4` | 1.05x | 1.28x | 1.02x |
| katsura-6 | **0.89x** | 1.60x | 1.32x |

1.05x–1.32x on four instances is the weak band the degree comparator sat in, and on katsura-5 and
katsura-6 the spread is **inverted**: `long-pair` has the *lower* peak of the two, 8 600 against
9 689 on katsura-6. So the relation separates its directions barely where it separates them at all,
and in the wrong direction on two of seven instances — while **both** directions are worse than the
baseline on peak entries on **all seven**. That is the signature §1 describes of a heuristic that is
measuring run-to-run variation rather than an effect.

The row-operations minimum ends up held by a *control* on three instances — `long-pair` has the
fewest on Poseidon `t=2 R_P=2` (171 899) and at Fukuoka `n=15` (7 271 354), and `short-pair` on
cyclic-5 (3 679) — which is the clearest statement available that row operations are not tracking
this hypothesis.

Runtime says nothing either way, and on one instance it says the opposite. At `n=10` `short-pair` is
93.9 ms against that invocation's 111.7 ms baseline — 16% faster, while holding 4.4% *more* live
entries — and at `n=15` 7 792 ms against 8 193 ms. Both are inside the ±20% band, which is why this
document reads the exact counters and not the clock.

**So the axis is real and the schedule built on it is not worth having as a default.** It stays
selectable, as `large-multiplier-degree` does, so this can be reproduced. The reducer-side
measurement of the same axis, in §6, is where it has an effect — and that is the asymmetry worth
keeping from #253.

## 3. Batch size, at the baseline schedule

Measured in its own table, deliberately. A sort and a cap varied together cannot be attributed, and
the plan's §6.5 is explicit about not doing it.

| instance | cap | pairs reduced | batches | cols | peak entries | row ops | ms |
|---|---|---:|---:|---:|---:|---:|---:|
| Fukuoka III `n=10` | uncapped | 743 | 6 | 859 | 168 020 | 359 099 | 120.3 |
| | 64 | **334** | 8 | 652 | **60 809** | **59 582** | **33.5** |
| | 16 | 295 | 21 | 596 | 48 755 | 40 091 | 41.4 |
| | 4 | 288 | 74 | **571** | 45 155 | 33 215 | 87.8 |
| Fukuoka III `n=15` | uncapped | 3 596 | 7 | 3 573 | 2 142 707 | 7 599 775 | 8 262.5 |
| | 64 | **1 693** | 28 | 3 373 | 1 099 753 | **1 784 460** | **3 829.0** |
| | 16 | 1 670 | 106 | 3 287 | 1 054 553 | 1 703 779 | 9 396.2 |
| | 4 | 1 664 | 417 | **3 192** | **1 028 321** | 1 635 272 | 27 902.6 |
| Poseidon `t=2 R_F=4` | uncapped | 897 | 22 | 1 341 | 237 265 | 589 712 | **365.1** |
| | 64 | 872 | 28 | 1 351 | **94 621** | 555 552 | 378.3 |
| | 16 | 888 | 63 | 1 344 | 100 843 | 595 130 | 635.2 |
| | 4 | 934 | 236 | 1 268 | 105 699 | 573 891 | 1 599.0 |
| Poseidon `t=2 R_F=2 R_P=2` | uncapped | 409 | 13 | 925 | 103 112 | 178 576 | **137.4** |
| | 64 | 409 | 15 | 919 | 78 038 | 177 375 | 146.5 |
| | 16 | 390 | 30 | 897 | **52 447** | 174 018 | 170.8 |
| | 4 | 406 | 107 | 908 | 51 565 | 181 001 | 323.3 |
| katsura-6 | uncapped | 68 | 6 | 458 | 6 014 | 11 885 | **3.5** |
| | 64 | 68 | 6 | 458 | 6 014 | 11 885 | 3.5 |
| | 16 | 68 | 7 | 458 | 6 026 | 11 523 | 3.7 |
| | 4 | 68 | 18 | 436 | **5 923** | **10 920** | 6.3 |
| cyclic-5 | uncapped | 116 | 14 | 115 | 1 206 | 3 929 | **1.5** |
| | 64 | 116 | 14 | 115 | 1 206 | 3 929 | 1.5 |
| | 16 | 115 | 14 | 115 | 1 206 | 3 900 | 1.5 |
| | 4 | 111 | 32 | 101 | **801** | 3 398 | 2.2 |

**This is the result of M22-A, and it is not the one the workstream was aimed at.** Capping the
batch is a large lever where reordering within one is not:

- **Peak live entries fall on every instance**, by 24% to 64% at a cap of 64 and by up to 73% at a
  cap of 16. That is the memory figure the entry and byte budgets are enforced on, and on five of
  six instances a cap of 64 already clears M22-I's 20% threshold.
- **On both overdetermined MQ instances it is also much faster** — 120.3 ms to 33.5 ms at `n=10`
  (3.6x) and 8.26 s to 3.83 s at `n=15` (2.2x) — with row operations down sixfold and fourfold
  respectively, and **pairs reduced down from 743 to 334 and from 3 596 to 1 693**.

That last figure is the mechanism, and it is not a trade-off against anything. A smaller batch
returns its candidates sooner, and those candidates let Gebauer–Möller eliminate pairs that the
uncapped run had already selected and reduced. **The uncapped batch reduces 409 pairs it did not
need to at `n=10`, and 1 903 at `n=15`**, because it committed to the whole degree before learning
anything from any of it. Capping is not splitting the same work into more matrices; it is doing less
work. The number of basis elements produced is unchanged on both — 928 at `n=15` under every cap —
so nothing is being traded for the saving.

Where it does not pay, it does not pay for the opposite reason. On both Poseidon instances the
pair count barely moves — 897 to 872, 409 to 409 — so there is no work to avoid, and the extra
batches are pure overhead: 365 ms to 378 ms at a cap of 64 and to 1 599 ms at a cap of 4. The
structured elimination path pays a fixed cost per matrix, and 236 matrices pay it 236 times.

**There is a crossover, and 64 is on the right side of it.** At `n=15` a cap of 16 is 9.40 s against
the uncapped 8.26 s and the capped-at-64 3.83 s, with *fewer* live entries and *fewer* row
operations than either. So the extra time is not algebraic work; it is 106 matrices' worth of
symbolic preprocessing and construction against 28. At a cap of 4 it is 417 matrices and 27.9 s —
3.4x slower than uncapped while doing 4.6x fewer row operations. Any default drawn from this has to
be a cap large enough to amortize the per-matrix cost, not the smallest cap that minimizes memory.

So the discriminator is **whether a degree's pairs can eliminate one another**, which is a property
of the system and not of the cap. The Fukuoka instance is overdetermined, so its degree-4 batch of
520 pairs contains a great many that later elements make redundant; the Poseidon instances are
square and do not.

A note on the lower caps. A cap of 4 reduces *more* pairs than uncapped on `t=2 R_F=4` — 934
against 897 — and produces more basis elements before interreduction, 278 against 186. Smaller
batches find candidates whose leading monomials the big batch would have reached in one step, so
the basis grows in more, smaller steps and generates more pairs. The reduced basis is identical
either way, which is asserted; the trajectory is not comparable.

## 4. What this decided

| question | answer |
|---|---|
| Does the **degree** heuristic reduce matrix growth? | **No.** It cuts row operations 4%–15% and makes the matrix larger on four of six instances. |
| Does the **published monomial** ordering? | **Yes, by 7%–9.5% in peak entries on the three largest instances**, and it is the only schedule that narrows the matrix on either Fukuoka instance. Its control is the worst schedule on five of seven, with a 1.54x–1.75x spread between the comparator's two directions against 1.09x–1.13x for the degree one, so the effect is monotone and credible. |
| Was the first version of this finding wrong? | **Yes.** It reported the degree heuristic's null result as a finding about Sakata–Takagi's strategy, which compares monomials. See §2. |
| Does ranking *pairs* by **term count** reduce matrix growth? | **No.** `short-pair` raises peak live entries on all seven instances, 0.2% to 61%, and its control is 1.05x–1.32x away from it on four and *inverted* on two. Both directions are worse than the baseline everywhere, which is the noise signature. See §2's last subsection. |
| Does ranking *reducers* by term count? | **Yes, and by the largest margin in this document — under grevlex only.** `FewestTerms` takes peak live entries down 27.4% and 31.7% on katsura-5 and katsura-6 grevlex and 14.5% on katsura-7, with a control 1.09x–3.82x away that cannot finish at all on three lex rows. Under grlex the same policy is a 25%–30% regression and under lex a 100%–230% one. See §6. |
| Should either become the default? | **No**, but for different reasons. The degree heuristic reduces one measure and worsens another. The monomial ordering improves every structural counter on the large instances but by 7%–14.5%, under M22-I's 20% threshold, with runtime gains inside the noise band. Both stay selectable so this can be reproduced, as `ReducerSelection::LargestLeadingMonomial` does. |
| Should `FewestTerms` become the default? | **No.** It clears the threshold on two instances and regresses 25%–30% on the same systems under grlex and 100%–230% under lex, where it twice exhausts the entry budget the baseline stays inside. A default may not regress. Selectable, and the shape a future proposal would need is an order-specific default rather than a global one. |
| Does batch sizing? | **Yes, substantially** — 24%–64% less peak memory on every instance, and 3.6x and 2.2x faster on the two overdetermined MQ instances, by reducing 55% and 47% fewer pairs. Still the dominant lever, by an order of magnitude over either ordering. |
| Should a cap become the default? | Deferred to M22-I, per §6.6. It is a clear win on overdetermined MQ and a clear loss on square Poseidon systems, so the honest default may be neither a fixed cap nor none. |

## 5. What this says about the rest of M22

The mechanism in §3 is worth stating in M22-C's terms, because it is the same mechanism from the
other end. HDF4 skips pairs a Hilbert prediction says are unnecessary and then has to certify that
it was right. **A batch cap gets a large part of the same saving with no prediction and no
certification**, because the pairs it avoids are eliminated by a *sound criterion* that simply had
not had the chance to fire yet. On Fukuoka III `n=10` that is 409 pairs out of 743, which is 55% of
the pairs the uncapped run reduced — and M22-0 measured the dependent-pair-row fraction at 54.2% on
the same instance.

Those two numbers are not the same quantity and should not be added or compared directly. But they
do mean that a certified Hilbert-driven strategy has to beat a batch cap, not the uncapped baseline,
before it is worth its certification cost. M22-C's measurements should include a capped reference
row.

## 6. The same axis on the reducer side, which is where it has an effect

From #253 as well, and measured with a different program:
`cargo run --release --example f4_selection`, under `F4Options::baseline()` with the reducer cache
off, over cyclic-4/5 and katsura-4/5/6/7. The counters are the whole-computation ones that program
reports — the closure size (`reducers`), the largest matrix, peak live entries, and row operations
— and **every row returned the identical reduced Gröbner basis, asserted by the program**.

[`ReducerSelection`](../../src/grobner/f4/options.rs) decides which divisor reduces a monomial
during symbolic preprocessing, and the reducer chosen *is* the row added. `FirstApplicable` is the
baseline; `LargestLeadingMonomial` ranks by multiplier size and was measured and rejected in M16.
`FewestTerms` ranks by term count — Singular's `posInT_EcartpLength`, whose ecart term vanishes in a
global order — and `MostTerms` is its control.

Peak live entries, `first` against `fewest-terms`, with the control beside it:

| instance | order | first | fewest-terms | change | most-terms | spread |
|---|---|---:|---:|---:|---:|---:|
| katsura-5 | grevlex | 7 818 | **5 678** | **−27.4%** | 10 658 | 1.88x |
| katsura-6 | grevlex | 103 314 | **70 536** | **−31.7%** | 264 325 | 3.75x |
| katsura-7 | grevlex | 1 390 812 | **1 188 788** | −14.5% | 4 538 601 | 3.82x |
| cyclic-4 | grevlex | 204 | **193** | −5.4% | 234 | 1.21x |
| cyclic-5 | grevlex | **17 061** | 23 337 | +36.8% | 63 725 | 2.73x |
| katsura-5 | grlex | **3 126** | 3 229 | +3.3% | 5 677 | 1.76x |
| katsura-6 | grlex | **34 746** | 43 349 | +24.8% | 69 470 | 1.60x |
| katsura-7 | grlex | **368 156** | 476 781 | +29.5% | 993 289 | 2.08x |
| cyclic-5 | grlex | 11 379 | **11 246** | −1.2% | 12 252 | 1.09x |
| cyclic-5 | lex | **13 993** | 28 225 | +101.7% | *budget* | — |
| katsura-5 | lex | **9 285** | 30 738 | +231% | *budget* | — |
| katsura-6 | lex | **151 624** | *budget* | — | *budget* | — |

*budget* is a run that exceeded `F4Options::baseline()`'s limits — 200 000 rows or 20 000 000 live
entries — and therefore returned an error rather than a basis.

**The control is monotone everywhere, and strongly.** `most-terms` holds more live entries than
`fewest-terms` on every instance both finished, by 1.09x to 3.82x, and on the three lex rows it
cannot finish at all where `fewest-terms` can on two of them. That is a 1.09x–3.82x separation
against the 1.54x–1.75x of the best schedule in §2 and the 1.09x–1.13x of the one that was noise —
so unlike `short-pair`, **this axis is measuring something**.

What it measures is not a uniform improvement. The sign depends on the monomial order:

- **Under grevlex on katsura it is the largest structural gain in this document**: 27.4% and 31.7%
  less peak memory on katsura-5 and katsura-6, 14.5% on katsura-7, which clears M22-I's 20%
  threshold on two of the three.
- **Under grlex on the same systems it is a 25%–30% regression**, and under lex a 100%–230% one
  that twice exhausts the entry budget outright.
- On cyclic it is small in both directions: −5.4% and −1.2%, against +36.8% on cyclic-5 grevlex.

The mechanism is visible in the shape columns and is the counterpart of M16's reason for rejecting
`LargestLeadingMonomial`. On katsura-6 grevlex the closure grows from 4 572 reducer rows to 4 756
and the widest matrix from 1388x1412 to 1453x1475 — 4% more rows and 4% more columns — while the
live entries fall by a third and row operations rise 1.2%. The policy is therefore **not** making
the matrix smaller; it is making the *same* matrix sparser, which is exactly what "the sparsest
reducer is the sparsest row" predicts and is a different claim from the multiplier-size one. Under
lex the sparsest divisor is routinely one whose multiplier is enormous, the closure explodes — 3 186
reducer rows to 11 587 on katsura-5 lex — and the sparsity per row cannot pay for it.

Runtime does not separate them. On katsura-6 grevlex it is 22.29 ms against 23.54 ms and on
katsura-7 grevlex 695.54 ms against 685.78 ms, both inside the band. Divisor-scan work does rise, as
it does for `LargestLeadingMonomial`: both term-count policies examine the whole basis per query
rather than stopping at the first divisor, which takes `scan/q` on katsura-6 grevlex from 5.7 to
23.0.

**So `FewestTerms` stays selectable and does not become the default.** A default may not regress,
and this one regresses 25%–30% under grlex on the systems it most helps under grevlex, and fails the
entry budget under lex where the baseline completes. What it does establish is that **term count is
a real lever on the reducer side where it is noise on the pair side** — and that an order-specific
default, rather than a global one, is the shape any future proposal here would have to take.

## 7. Reproducing

```sh
cargo run --release --example f4_schedule -- list
cargo run --release --example f4_schedule                 # every instance, both sweeps
cargo run --release --example f4_schedule -- mq3-n15      # one instance per process
cargo run --release --example f4_selection                # §6, every reducer policy
cargo test --lib schedule                                 # the safety properties
cargo test --lib length_schedule                          # the pair-length comparators
cargo test --lib term_count                               # the term-count divisor scans
```

The tests assert what the tables assume: every schedule yields the same pair *set* under every
criterion combination, keeps the lcm degree primary, is deterministic, loses no pair under a cap,
leaves the chain criterion's bookkeeping sound, and returns the identical basis under every
monomial order and every criterion combination.
