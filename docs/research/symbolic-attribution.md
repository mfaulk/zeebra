# Why MQ10 symbolic preprocessing is larger than msolve's (#742)

**Measured at:** `575f59d9` (frozen controls) and `f80adee9` (complete sorted-input
run), both on `a7827de1`, with no library change. The instrument and code-delta
SHA256s, base commit and raw-record SHA256s are retained in
[`metadata.json`](../../research/symbolic-attribution/metadata.json).
AMD Threadripper PRO 5995WX, release, x86-64-v3, one worker, CPU 4 under
`tools/benchlock.sh`; both runs completed. These are integer work counts, not timings.
[Raw records and reproduction](../../research/symbolic-attribution/README.md).
msolve figures are the retained 0.11.0 GF(32003) log from [#737](msolve-gap.md).

## Finding

**Reducer choice explains most of the excess, specifically the order of the
original generators in the first-applicable search.** Sorting just that prefix
by increasing leading monomial removes 7,558 rows and 7,558 columns on the
*unchanged* baseline batches. Removing duplicate pair multiples removes another
339 rows and no columns. Together these explain **89.6% of the 8,810 excess rows
and 89.1% of the 8,482 excess columns** relative to msolve.

This is an attribution, not a new library default. The remaining **913 rows and
924 columns** in the frozen comparison are a measured refusal to give an exact
cross-engine decomposition: the study does not export msolve's intermediate
bases and pair identities. Equal degree and pair counts do not prove identical
batches. Most of that residual is round 8 (774 rows / 773 columns).

## Source reference and controls

The provisioned msolve 0.11.0 source was read as a GPL reference only. No msolve
implementation is copied, linked or distributed. The release archive SHA256 is
`0f32011c4333efb662ce8f5febf6b5dc1a8e6f1e4a935361b9af5009bd5cdb98`, pinned in
`tools/external/provision.sh`. Relevant locations under its `src/neogb/`:

- `engine.c:95` / `order.c:396`: initial generators are sorted by increasing
  leading monomial before the basis search list is built.
- `symbol.c:484` (`find_multiplied_reducer`): first applicable element of the
  `lmps` list, rather than newest or sparsest. Zeebra also searches first
  applicable, but preserves the caller's generator order.
- `symbol.c:200` (`select_spairs_by_minimal_degree`): group pairs by LCM,
  deduplicate the participating generator indices, and keep one multiple of
  each generator. Both halves' information remains; repeated copies are removed.
- `update.c:169,250`: redundancy flags remove elements from the reducer list.
  The actual test includes polynomial-degree conditions and insertion history.
  Our `active` control instead removes every nonminimal leading monomial, keeping
  the earlier element on equal leads. It is deliberately not an exact emulation.

The replay constructs its own closure from public Zeebra basis snapshots. Each
baseline batch asserts exact equality with production preprocessing: rows and
origins, column encounter order, term handles, and covered leads. Deduplication
asserts identical columns and covered leads. Every arm uses the same basis,
pairs, coefficients and pair seed order; only the specified controls differ.

`input-order` stably sorts only the input-generator portion of the reducer
search by increasing leading monomial; appended elements retain their order.
It neither sorts the pair seeds nor changes their polynomial tails. Thus the
lost columns are caused by choosing different reducer multiples and the closure
of their tails, without needing a more reduced stored basis.

## Per-round attribution on frozen batches

All matrix sizes are as built. `copies` is the number of duplicate seed rows
removed, with zero columns removed in every round. The ordering effect, after
removing copies, is the difference between the first size minus `copies` and the
third size. Every removed column also removes one reducer row under this control.

| round | Zeebra rows / cols | copies | input-order + dedup rows / cols | msolve rows / cols | residual rows / cols |
|---:|---:|---:|---:|---:|---:|
| 1 | 17 / 40 | 3 | 14 / 40 | 14 / 40 | 0 / 0 |
| 2 | 98 / 196 | 1 | 94 / 193 | 82 / 178 | 12 / 15 |
| 3 | 503 / 658 | 8 | 466 / 629 | 459 / 622 | 7 / 7 |
| 4 | 1,611 / 1,695 | 51 | 1,405 / 1,540 | 1,404 / 1,538 | 1 / 2 |
| 5 | 4,290 / 4,169 | 99 | 3,452 / 3,430 | 3,430 / 3,404 | 22 / 26 |
| 6 | 6,057 / 6,292 | 10 | 4,960 / 5,205 | 4,954 / 5,199 | 6 / 6 |
| 7 | 5,710 / 6,027 | 1 | 4,906 / 5,224 | 4,877 / 5,195 | 29 / 29 |
| 8 | 12,554 / 12,020 | 163 | 10,751 / 10,380 | 9,977 / 9,607 | 774 / 773 |
| 9 | 10,435 / 10,738 | 3 | 8,906 / 9,212 | 8,889 / 9,195 | 17 / 17 |
| 10 | 11,504 / 11,851 | 0 | 9,928 / 10,275 | 9,883 / 10,226 | 45 / 49 |
| **sum** | **52,779 / 53,686** | **339** | **44,882 / 46,128** | **43,969 / 45,204** | **913 / 924** |

The `active` control excludes 5, 5, 5, 5, 5, 11, 11, 11, 13 and 13 basis elements,
respectively. It removes **zero rows and zero columns in every round**, both
alone and on top of ordering plus deduplication. It changes a few row tails:
127 fewer as-built nonzeros across the campaign, with slightly *more* forward
work. Retaining redundant reducers is not the source of the observed matrix-size
excess under this control.

## Forward work and the other reducer choices

Counts use production structured Adaptive elimination with reduced batch rows,
and the existing passive `research-work` counters. Only the forward phase is
shown; back-substitution and final interreduction are excluded. The baseline
recovers #737's **7,885,325 applications / 585,166,982 products exactly**.

| frozen arm | rows | columns | as-built nonzeros | forward applications | forward products |
|---|---:|---:|---:|---:|---:|
| baseline | 52,779 | 53,686 | 2,622,503 | 7,885,325 | 585,166,982 |
| dedup | 52,440 | 53,686 | 2,523,210 | 6,956,129 | 518,277,638 |
| active | 52,779 | 53,686 | 2,622,376 | 7,891,500 | 585,946,456 |
| newest | 57,169 | 58,077 | 7,232,180 | 8,300,833 | 1,243,415,169 |
| sparsest | 45,108 | 46,015 | 2,461,819 | 6,710,257 | 537,393,163 |
| input-order | 45,221 | 46,128 | 2,556,652 | 6,812,682 | 549,231,661 |
| input-order + dedup | 44,882 | 46,128 | 2,457,359 | 6,010,214 | 486,416,830 |
| input-order + active + dedup | 44,882 | 46,128 | 2,457,232 | 6,016,705 | 487,361,685 |

Newest is a negative control here: it more than doubles forward products.
Sparsest narrows the matrix almost as much as initial ordering, but that alone
does not minimize products. Deduplication removes only 0.64% of rows yet saves
11.4% of forward products: repeated pair rows are expensive targets.
Ordering plus deduplication saves **16.9%** of baseline forward products, leaving
**1.73x** msolve's 280,568,561. Near-equal dimensions do not imply equal work.

## Complete sorted-input check and decision

`--sorted-input` also runs ordinary F4 with the original and sorted generator
lists and asserts equality of the entire reduced polynomial vector, including
all coefficients and ordering: **247 identical reduced basis elements**. The
sorted run retains ten rounds and the original per-round pair counts. This is a
complete computation through the existing library, not a replay assumption.

| complete F4 input order | rows | columns | as-built nonzeros | forward applications | forward products |
|---|---:|---:|---:|---:|---:|
| original | 52,779 | 53,686 | 2,622,503 | 7,885,325 | 585,166,982 |
| increasing initial lead | 45,221 | 46,128 | 2,556,660 | 6,812,661 | 549,231,289 |

The sorted run's frozen deduplicated replay has 44,881 rows, 46,128 columns,
2,457,353 nonzeros and 486,416,363 forward products. Deduplication was **not**
installed in a live F4 run: its replay cannot establish a complete altered
trajectory's counts. Both published runs use the current library unchanged.

No global reducer policy or default changes in this PR. Initial ordering is
worth considering in a separate corpus-wide optimization; this single instance
does not justify making every caller's input order irrelevant to reducer choice.
The surviving cross-engine residual is not assigned to stored-tail reduction or
pair selection without intermediate msolve snapshots. #269 still owns the
back-substitution work, which none of these forward figures measures.
