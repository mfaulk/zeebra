# F4 degree by degree: the M22 baseline

**Measured at:** publication bound `c2dde983` — the commits that published these figures,
recovered from git rather than recorded at the time ([§10](external-comparison-protocol.md#10-the-commit-and-what-a-publication-bound-is)).

Reference for M22-0 (#74, #81). Every figure here comes from

```sh
cargo run --release --example f4_degrees
```

*The Fukuoka MQ instances were fetched with `tools/fetch-mq-challenge.sh` and the Poseidon systems
built by the research module, both moved out in #668; those rows reproduce at commit 9532a9a2.*

under `F4Options::recommended()` with `profile_degrees` and `measure_stages` set,
`max_matrix_columns = 60_000` and `max_live_bytes = 400 MB` (slack: the effective live cap is the `min` of the two budgets, so `max_live_nonzeros` bound first at 20 000 000 entries — **320 MB** over these fields' 16-byte entry; #322, #469), grevlex throughout. Machine: 64-core
x86-64, `-C target-cpu=x86-64-v3`, fat LTO. Times are single runs and are quoted to one decimal
only because the program prints them that way — they are not repeated measurements, and nothing
below rests on a difference under about 20%.

## 1. What is being measured, and why not zero rows

A batch's Macaulay matrix holds two kinds of row: the two halves of each critical pair, and the
reducer multiples symbolic preprocessing adds so that the matrix can perform the reductions
polynomial division would.

Reducer rows have **distinct leading monomials by construction** — that is the closure invariant —
so they are linearly independent and none of them ever reduces to zero. Two consequences:

1. Every zero row is a dependent *pair* row. The zero-row count is not a count of useless pairs,
   in either direction: a pair contributes two rows, and either, neither, or both can be dependent.
2. The rank a batch found above `reducer_rows` is exactly what the pair rows contributed:

   ```text
   candidate_rank_contribution = rank - reducer_rows
   ```

   Exact, and independent of the order elimination took the rows in, because rank is.

A second identity separates rank that became *basis elements* from rank that merely reproduced
relations the batch already represented. Writing `L` for the leading monomials of the input rows,
every element of `L` leads some row and is therefore a pivot column, so

```text
new basis elements = rank - |L|,    |L| = reducer_rows + distinct lcms in the batch
```

Both identities are asserted on real batches in
`src/grobner/f4/tests.rs::test_the_rank_attribution_identity_holds_on_real_batches`, not assumed.

## 2. How much of F4's work is redundant

Pair rows that added no rank, as a share of pair rows built:

| instance | vars | eqs | dependent pair rows | reducer share of rows | outcome |
|---|---:|---:|---:|---:|---|
| katsura-5, GF(2^31−1) | 5 | 5 | **40.0%** (24/60) | 83.2% | complete, 0.7 ms |
| Fukuoka III `n=10` seed 0, GF(31) | 10 | 20 | **54.2%** (806/1486) | 40.1% | complete, 123 ms |
| Fukuoka III `n=15` seed 0, GF(31) | 15 | 30 | **55.0%** (3955/7192) | 43.4% | complete, 8146 ms |
| Fukuoka VI `n=10` seed 0, as published | 10 | 7 | 58.9% (390/662) | **98.7%** | column budget crossed, 2801 ms |
| Fukuoka VI `n=10` seed 0, 3 variables pinned | 10 | 10 | 59.8% (397/664) | 93.8% | complete, 465 ms |
| Poseidon `t=3 R_F=2 R_P=1`, as generated | 9 | 8 | 57.5% (2849/4954) | 96.2% | column budget crossed, 18310 ms |
| Poseidon `t=3 R_F=2 R_P=1`, one input pinned | 9 | 9 | 46.0% (183/398) | 72.3% | complete, 13.9 ms |
| Poseidon `t=2 R_F=4 R_P=0` | 9 | 9 | 53.6% (961/1794) | 75.9% | complete, 367 ms |
| Poseidon `t=2 R_F=2 R_P=2` | 7 | 7 | 48.5% (397/818) | 79.1% | complete, 139 ms |
| Poseidon `t=2 R_F=2 R_P=0` | 5 | 5 | 33.3% (26/78) | 68.4% | complete, 0.4 ms |

**The answer is 33% to 60%, and remarkably flat across families.** It does not separate the
systems that finish from the systems that do not, it does not grow with instance size within a
family (54.2% to 55.0% from `n=10` to `n=15`), and it is not notably different between a
positive-dimensional system and its specialization (58.9% to 59.8% on type VI).

So **a scheduling change that removed every dependent pair row would at best halve the pair block**
— and the pair block is not where the rows are. That is the second column: reducer scaffolding is
40% of rows on the overdetermined MQ instances and **68% to 99%** everywhere else. On Fukuoka VI as
published, 98.7% of all rows are scaffolding, so halving the other 1.3% is not an optimization.

This is the single most important number M22-0 produces, and it is a caution: the opportunity
HDF4 addresses is real but bounded, and on these instances it is bounded well below the matrix
sizes that actually cause failure.

## 3. Where the matrices become unaffordable

Degree profiles, abridged to the two largest degrees of each run (`cols` is the widest matrix at
that degree, `MB` its peak estimated entry bytes):

| instance | peak degree | cols | MB | highest selection degree | highest column degree |
|---|---:|---:|---:|---:|---:|
| Fukuoka III `n=10` | 4 | 859 | 2.7 | 4 | 4 |
| Fukuoka III `n=15` | 4 | 3 573 | 34.3 | 4 | 4 |
| Fukuoka VI `n=10`, as published | 8 | 38 456 | 84.7 | 9 | 8 |
| Fukuoka VI `n=10`, pinned | 9 | 4 319 | 4.0 | 9 | 9 |
| Poseidon `t=3`, as generated | 10 | 42 229 | 155.3 | 11 | 10 |
| Poseidon `t=3`, one input pinned | 5 | 393 | 0.2 | 5 | 5 |
| Poseidon `t=2 R_F=4` | 5 | 1 341 | 3.8 | 5 | 5 |

Two things worth separating. **The highest selection degree exceeds the highest column degree on
the two failing runs** — degree 11 against 10, and 9 against 8 — because the budget was crossed
while building the last degree's matrix, so pairs were selected at a degree whose matrix never
existed. That is why the profile records a selection with no batch against it: the queue produced
the work and the criteria paid to examine it.

**Neither figure is the solving degree or the degree of regularity.** Both are properties of the
ideal; these are properties of a run under one configuration, and the plan's §5.3 asks for them to
be kept apart. They are.

## 4. The controlled Poseidon comparison, and what it corrects

*§4 (the controlled comparison of the nine-variable Poseidon instances against M21's state-width
frontier) was moved out with the cryptanalysis research in #668; it is preserved at commit 9532a9a2.*

## 5. Round count at fixed state width

`t = 2` throughout, so every row is square:

| instance | vars | highest selection degree | peak MB | time |
|---|---:|---:|---:|---|
| `t=2 R_F=2 R_P=0` | 5 | 4 | 0.0 | 0.4 ms |
| `t=2 R_F=2 R_P=2` | 7 | 6 | 1.7 | 139 ms |
| `t=2 R_F=4 R_P=0` | 9 | 5 | 3.8 | 367 ms |

Two round schedules that give the same S-box count do not give the same computation: `R_F=2, R_P=2`
reaches degree 6 and `R_F=4, R_P=0` reaches degree 5 with two more variables. Partial rounds add one
variable each and full rounds add `t`, so at fixed variable count a partial-round-heavy schedule has
more rounds — and more rounds is the thing that drives degree here. Three points is not a curve, and
no round-count extrapolation should be made from it.

## 6. Mutants occur, and they are not rare

Elements extracted whose own total degree is below the degree of the batch that found them:

| instance | mutant elements | elements added | share |
|---|---:|---:|---:|
| katsura-5 | 0 | 10 | 0% |
| Fukuoka III `n=10` | 65 | 168 | 39% |
| Fukuoka III `n=15` | 335 | 928 | 36% |
| Fukuoka VI `n=10`, as published | 0 | 65 | 0% |
| Poseidon `t=3`, as generated | 164 | 489 | 34% |
| Poseidon `t=3`, pinned | 38 | 65 | 58% |
| Poseidon `t=2 R_F=4` | 80 | 186 | 41% |
| Poseidon `t=2 R_F=2 R_P=2` | 37 | 107 | 35% |
| Poseidon `t=2 R_F=2 R_P=0` | 8 | 16 | 50% |

On the classical system and on the underdetermined type VI instance there are none at all; on the
MQ challenge instances and on every Poseidon system a third to a half of all new elements come out
below their batch's degree. That is enough to make M22-D worth measuring and not enough to predict
what a mutant *mechanism* would buy: Zeebra already appends these elements immediately and generates
their pairs at once, so the question M22-D has to answer is whether anything is left on the table.

**M22-D answered it, and the element count turns out to be the wrong measure.** Counting instead the
*batches* that produce a mutant and the times the schedule consequently goes back to a lower degree:
every regression in the corpus followed a batch with a mutant, and there are only zero, one or two
regressions per computation. The Poseidon `t = 3` instance produces 164 mutants over 12 of its 20
batches and **zero** regressions. See [`mutants.md`](mutants.md).

## 7. Selection-time criteria discard nothing here

The `cut` column is **zero at every degree of every instance above**. The product and chain criteria
act on a selected batch and found nothing to discard on any of these systems; all pair elimination
under `PairCriteria::ALL` happened at insertion, through Gebauer–Möller. That is not a defect — M16
measured Gebauer–Möller as the criterion that does the work — but it means a per-degree report of
selection-time rejections is, on this corpus, a column of zeros, and a scheduling experiment cannot
be credited with "the criteria fired more often".

## 8. What this decided for the rest of M22

- **M22-A is worth doing and should be measured on matrix width, not pair count.** Rows are
  dominated by reducer scaffolding, and scaffolding is a function of which multiples the chosen
  pairs need. A pair ordering that changes the closure is changing the thing that matters; one that
  only reorders the pair block is not.
- **M22-B should expect the Hilbert prediction to be least useful where it is most needed.** The
  dependent-row fraction is flat at 33–60% whether or not the instance finishes, so a model that
  predicts dependency does not predict failure.
- **M22-C's certification cost has to be compared against 123 ms and 8.1 s, not against the
  failures.** The instances where there is time to save are the ones that already complete.
- **M22-E's first result is already in §4**: the controlled comparison, which changes what M21's
  nine-variable frontier means.
- **M22-D has a measurable population** (§6) and a plausible null result (Zeebra may already
  exploit it).

## 9. Reproducing

```sh
cargo run --release --example f4_degrees            # the classical rows; see the note at the top
cargo test --lib grobner::f4::degrees               # the attribution identities
cargo test --lib test_the_degree_profile_reconciles_with_the_totals
```

The shared build cache in this checkout can serve a stale release `libzeebra`; set
`CARGO_TARGET_DIR` to a path of your own and `RUSTC_WRAPPER=""` if an example fails to compile
against an item that plainly exists.
