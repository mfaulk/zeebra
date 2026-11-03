# Milestone: F4 Computational Efficiency

Status: complete, in review. Baseline commit `b19eefc` (`origin/main`, the merge of PR #19),
653 tests passing in debug at the start; 754 at the close, passing in debug **and** release.
passing in debug.

The preceding milestone delivered a **correct** F4. This one makes it **fast enough to be the
engine Zeebra actually uses**. The difference is not rhetorical: F4 currently loses to classical
Buchberger on five of the thirteen paired grevlex and grlex instances in
[`MILESTONE-F4.md`](MILESTONE-F4.md) §7.2, including by 2.1x on katsura-6 grevlex — the instance
the previous milestone named as the next thing to fix.

Everything here is a performance milestone on a fixed mathematical contract. `f4` and
`f4_with_options` keep their signatures and their semantics. A reduced Gröbner basis is unique for
a given ideal and order, so **every optimization in M16 is required to return the identical
sequence of polynomials the baseline returns**. That is not an aspiration; it is the acceptance
test, and it is what makes an optimization milestone safe to execute in parallel.

## 1. Objective

Zeebra is successful at this milestone if

1. the practical size of system it can solve within a fixed time and memory budget grows,
2. every optimization is justified by a measurement taken *before* it was implemented,
3. an optimization that measurement does not justify is **rejected with its evidence preserved**,
   not merged because it was written,
4. the combined engine returns exactly the baseline's basis on the whole correctness corpus, and
5. the cost of an F4 computation is attributable to a stage rather than only to the whole.

(3) is stated as an objective because the M15 report's bottleneck list is a list of *hypotheses*.
"94% of rows are reducer multiples" does not imply those multiples recur across batches, and
"13.6x fill-in" does not imply any matrix is dense. Both are measured in M16-0 before anyone acts
on them.

## 2. Scope

### In scope

Structured (block) elimination of the Macaulay matrix; divisibility indexing and reducer-selection
policy; cross-batch reuse of reducer multiples; the chain criterion and Gebauer–Möller; a dense
row-echelon backend with the sparse implementation's exact contract; density-adaptive elimination;
per-stage cost attribution; an ablation study over the four workstreams; the measurements and the
report.

### Out of scope

FGLM and order conversion. F5 and signature-based algorithms. Prime fields above 128 bits.
Cryptanalysis-specific functionality or workflows. GPU kernels. Distributed computation. Public
API redesign. Unrelated computational algebra features. Parallel elimination may be *investigated*
if a measurement strongly justifies it, but it is not a deliverable.

The motivating workloads — tens of variables, sparse low-degree systems with large intermediate
growth, degrees 2/3/5/7, 31–64 bit primes now and 128–255 bit later, zero-dimensional systems —
shape which benchmark families are run. They do not license building anything specific to them.

### Architectural decisions

| Decision | Reason |
|---|---|
| The public `f4` / `f4_with_options` signatures do not change | Every optimization is selected through `F4Options`, which has public fields and a `Default`. A caller who ignores M16 entirely gets the fastest configuration that is known-good, and a caller comparing configurations has one knob per workstream. |
| `F4Options` and `F4Statistics` are **frozen by M16-0**, with every variant A–D will need declared up front | These two files are what all four workstreams would otherwise edit simultaneously. Declaring the complete surface in M16-0 — each new arm initially delegating to the baseline — converts four merge conflicts into zero. |
| Elimination is selected by an enum, not a trait object | `F4Options` is `Clone + Debug + Eq`, which `Box<dyn EliminationBackend>` is not. Enum dispatch also keeps the backend monomorphized over `F: FiniteField`, which a trait object cannot be without boxing the field. |
| The elimination interface lives in `linalg`, and F4 calls it through two frozen functions | M16-A needs block primitives; M16-D needs to re-implement them per representation. Putting the interface in `src/linalg/echelon.rs` means A never edits a file in `linalg` and D never edits a file in `grobner`. |
| Stage timing is opt-in (`F4Options::measure_stages`) and off by default | M15 kept timing out of the inner loop, correctly. Four `Instant::now()` calls per *batch* — not per row — is the granularity that attributes cost without distorting it, and a default of `false` means the shipping path has none. |
| Cross-batch state is passed explicitly, not held in a global or a `thread_local` | A reducer cache is the one M16 optimization that makes a batch's output depend on earlier batches. Threading it as an explicit `&mut` argument is what keeps "deterministic for fixed input and options" checkable. |
| Pair criteria operate on leading monomials, not on polynomials | `SparseMultiPoly::leading_monomial` is a scan of the whole term map, and the baseline calls it three times per pair created. Gebauer–Möller needs the leading monomials of the whole basis at once; passing them is both the cheaper and the only workable interface. |
| Buchberger keeps its behaviour and remains the oracle | Unchanged from M15, and more important here: an optimization milestone with no independent oracle cannot distinguish "faster" from "wrong". |

## 3. Sub-milestones

| ID | Sub-milestone | Depends on | Branch |
|---|---|---|---|
| M16-0 | Shared interfaces, benchmarks, and execution plan | — | `feat/m16-foundation` |
| M16-A | Structured F4 elimination | M16-0 | `feat/m16-structured-f4` |
| M16-B | Symbolic preprocessing and monomial indexing | M16-0 | `feat/m16-symbolic` |
| M16-C | Improved critical-pair criteria | M16-0 | `feat/m16-pair-criteria` |
| M16-D | Dense and adaptive linear algebra | M16-0 | `feat/m16-hybrid-linalg` |
| M16-I | Integration, ablation benchmarks, and final report | A, B, C, D | `feat/m16-integration` |

A, B, C and D are each based on the **same** M16-0 commit and are not stacked on one another. They
are combined only on the integration branch, where conflicts are resolved once rather than four
times.

### 3.1 File ownership

The point of this table is that no two concurrent workstreams own the same file. A workstream that
needs a change outside its own column proposes an interface change to the integrator instead of
making it.

| Path | Owner |
|---|---|
| `src/grobner/f4/options.rs` | M16-0, then frozen |
| `src/grobner/f4/statistics.rs` | M16-0, then frozen |
| `src/grobner/f4/mod.rs` | M16-0, then the integrator |
| `src/grobner/f4/observer.rs` | M16-0, then frozen |
| `src/linalg/echelon.rs` | M16-0, then M16-D |
| `src/grobner/f4/reduction.rs`, `macaulay.rs`, `structured.rs` | M16-A |
| `src/grobner/f4/symbolic.rs`, `divisors.rs` | M16-B |
| `src/grobner/pairs.rs`, `src/grobner/buchberger.rs` | M16-C |
| `src/linalg/**` except `echelon.rs` | M16-D |
| `src/grobner/f4/tests.rs` | shared, append-only — add tests, do not rewrite existing ones |
| `benches/**`, `examples/**` | shared, append-only |
| `docs/MILESTONE-F4-OPTIMIZATION.md` | §7 onwards is per-workstream, append-only; §1–6 are the integrator's |

## 4. M16-0 — shared interfaces and the baseline

### 4.1 The option surface

One enum or flag per workstream, every variant declared now, each non-baseline variant initially
behaving exactly like the baseline so that the surface compiles and the tests pass before any
optimization exists.

```rust
pub enum EliminationBackend { Sparse, Dense, Adaptive }     // M16-D
pub enum ReductionStrategy  { Unstructured, Structured }    // M16-A
pub enum ReducerSelection   { FirstApplicable, LargestLeadingMonomial }  // M16-B
pub struct PairCriteria { product: bool, chain: bool, gebauer_moller: bool }  // M16-C

pub struct F4Options {
    // ... the M15 fields, unchanged ...
    pub elimination: EliminationBackend,
    pub reduction: ReductionStrategy,
    pub reducer_selection: ReducerSelection,
    pub criteria: PairCriteria,
    pub reuse_reducers: bool,          // M16-B
    pub measure_stages: bool,          // M16-0
}
```

`F4Options::default()` is the M15 configuration exactly, so the default path is the measured
baseline until M16-I changes it deliberately and says so. `F4Options::baseline()` names that
configuration permanently, so the ablation study can always reconstruct it even after the default
moves.

### 4.2 The elimination interface

`src/linalg/echelon.rs`, two functions, frozen:

```rust
/// Row echelon form of the whole matrix, under the chosen representation.
pub fn row_echelon_with<F: FiniteField>(
    backend: Backend, matrix: &mut SparseMatrix<F>, max_nonzeros: usize,
) -> Result<EliminationStatistics, usize>;

/// Eliminate rows `[split..]` against the pivots of rows `[..split]`, then echelonize them.
///
/// Rows `[..split]` must already have distinct leading columns and unit pivots. They are left
/// in place and are not reduced against each other, which is what lets a caller that knows its
/// upper block is already triangular skip establishing those pivots at all.
pub fn reduce_rows_against_pivots_with<F: FiniteField>(
    backend: Backend, matrix: &mut SparseMatrix<F>, split: usize, max_nonzeros: usize,
) -> Result<EliminationStatistics, usize>;
```

`Backend` is `linalg`'s own enum; `F4Options::elimination` maps onto it. `linalg` does not depend
on `grobner`, and that stays true.

The second function is the one M16-A is built on and M16-D must honour. Its contract is stated in
terms of pivots and row space, not in terms of a representation, so a dense or adaptive
implementation is substitutable.

### 4.3 The batch observer

`f4_with_options` delegates to a private generic driver taking `&mut impl BatchObserver`, and
passes a no-op that monomorphizes away. One frozen method:

```rust
pub trait BatchObserver<const N: usize, F: FiniteField> {
    fn batch(&mut self, basis: &MonicBasis<N, F>, pairs: &[CriticalPair<N>]);
}
```

This exists because every workstream's first task is a measurement on **real** batches, and the
alternative — each agent reimplementing the main loop to capture them — would give four subtly
different main loops and four incomparable measurements. `f4::observer::BatchTrace` collects
`(basis, pairs)` snapshots so a stage can be replayed, benchmarked, or counted in isolation:

- M16-A replays batches to compare block elimination against the one-pass echelon on identical
  matrices.
- M16-B counts how often the same `(basis_index, multiplier)` recurs across batches — the
  measurement that decides whether a reducer cache is worth building at all.
- M16-D harvests real Macaulay matrices to locate the sparse/dense crossover on the shapes F4
  actually produces rather than on synthetic ones.

### 4.4 Stage attribution

`F4Statistics::stages: StageTimings { symbolic, construction, elimination, extraction, total }`,
populated only when `measure_stages` is set. Four `Instant` reads per batch.

`examples/f4_profile.rs` prints the breakdown for a named configuration, which is how each
workstream reports its effect and how M16-I builds the ablation table.

`benches/f4_stages.rs` times symbolic preprocessing, matrix construction, and elimination
separately on batches captured from real runs, so a change that moves cost from one stage to
another is visible as such instead of as a small change in the total.

### 4.5 Baseline

Recorded in §6 below: machine, toolchain, profile, Criterion configuration, and the measurements.

### 4.6 Exit criteria

- The option and statistics surfaces compile with every A–D variant present and behaving as the
  baseline, and the full suite passes.
- `linalg::echelon`'s two functions exist with sparse implementations and the documented contract.
- The observer exists and `f4_with_options` returns bit-identical results through it.
- Stage attribution and the three measurement entry points run.
- Baselines for katsura-5/6/7, cyclic-5, and the deterministic quadratic systems are committed.
- The four workstreams can be started from one commit with no file in two columns of §3.1.

## 5. The four implementation sub-milestones

Each states the hypothesis, the measurement that tests it, and what "reject" looks like — because
rejecting an optimization with evidence is a successful outcome, and merging one that the
measurement did not support is not.

### 5.1 M16-A — Structured F4 elimination

**Hypothesis.** Sorting the Macaulay matrix into a reducer block above a pair block makes the
upper-left block unit upper triangular *by construction*, because symbolic preprocessing gives
every reducer row a distinct leading monomial. Writing

```text
M = [ A  B ]        A: reducer rows x reducer-lead columns, unit upper triangular
    [ C  D ]        C, D: the pair rows
```

the new pivots are exactly the pivots of `D - C A^{-1} B`, so the elimination never has to
discover `A`'s pivots and never fills in `A` or `B` at all. The baseline reduces all rows in index
order and pays for both.

**Measurement.** Replay real batches through both paths; compare row operations, peak live
nonzeros, and wall clock on the identical matrix. The reducer-row share (27–96% in M15 §7.1) is
the upper bound on what this can save, not evidence that it saves it.

**Reject if** the block path does not reduce row operations or peak nonzeros on the grevlex
instances where the reducer share is highest. Keep the one-pass path as the default in that case
and record the numbers.

**Correctness.** Candidate extraction semantics are unchanged: a candidate is still a nonzero row
whose leading monomial is not the leading monomial of any input row. The block path must produce
the same set of new leading monomials, and `f4` must return the identical basis under all three
orders.

**Owns** `src/grobner/f4/reduction.rs`, `macaulay.rs`, new `src/grobner/f4/structured.rs`.
**Must not** modify `src/linalg/**` or `f4/symbolic.rs`.

### 5.2 M16-B — Symbolic preprocessing and monomial indexing

**The §6.2 baseline reorders this workstream before it starts.** Symbolic preprocessing is 2% to
15% of the computation, and it is *smallest* on exactly the instances with the largest reducer
share — 2.1% on katsura-7 grevlex, which is 95.9% scaffolding. The preceding milestone put reducer
reuse first on the strength of that 95.9%. The breakdown says reducer rows are expensive because
they enlarge the **matrix**, which elimination then pays for, not because finding them is slow.

So the hypothesis worth pursuing is the one that produces **fewer and smaller rows**, whose benefit
lands in elimination; and the hypothesis to measure-then-probably-reject is caching, whose entire
ceiling is a fraction of 2–15%.

**Hypotheses, in the order the measurement puts them.**

1. **Smaller multipliers.** First-applicable reducer selection takes the first divisor in index
   order. Choosing the divisor with the **largest** leading monomial gives the smallest multiple,
   hence fewer new monomials, hence a smaller closure and a smaller matrix. This is the one with
   leverage on the 65–88% that elimination costs, and it must be measured by its effect on the
   **whole computation**, not on preprocessing alone — it can easily make preprocessing slower and
   the computation faster, or the reverse.
2. **Faster divisor lookup.** §6.3 confirms the scan: 4.7 to 47.2 basis elements examined per
   query, worst under lex. A degree filter, a variable-support bitmask, or a divisibility index
   should cut it. Worth having; bounded by the stage's share of the total, so worth bounded effort.
3. **Reducer reuse.** Measure the repetition rate of `(basis_index, multiplier)` across batches
   with `CacheMode::Count` **before** implementing `CacheMode::Store`. Successive batches work at
   successive degrees, so recurrence is not obvious, and the payoff is capped low either way.

**Reject if** smaller multipliers do not shrink the closure or do not shorten the computation; if
an index does not reduce scan steps per query; or if the repetition rate is low. A rejection with
the number attached is the deliverable in that case — not an unused cache.

**Correctness.** The closure invariant — every monomial of every preprocessed row that is
divisible by some `LM(g)` is the leading monomial of some row — is preserved exactly, and the
existing direct assertion of it must pass unchanged over all ten systems and three orders. Any
index must answer `find_divisor` **identically** to the linear scan, including which divisor it
picks, or reducer selection changes and with it the matrix; a differential test against the scan
is required. A cache must be deterministic and bounded.

**Owns** `src/grobner/f4/symbolic.rs`, new `src/grobner/f4/divisors.rs`.
**Must not** modify pair scheduling or elimination internals.

### 5.3 M16-C — Critical-pair criteria

**Hypothesis.** Only Buchberger's first criterion is implemented. The chain criterion and
Gebauer–Möller discard pairs *before* a matrix is built, which is strictly cheaper than reducing
them, and they are the standard reason real implementations build far fewer matrices.

**The soundness condition is the whole deliverable.** The chain criterion discards the pair
`(i, j)` when there is a `k` with `LM(f_k)` dividing `lcm(LM f_i, LM f_j)` **and both `(i, k)` and
`(k, j)` already handled**. Dropping the second half — discarding on divisibility of the lcm alone
— is unsound and is the classic way to return an incomplete basis that passes casual testing.
Gebauer–Möller is the standard insertion-time formulation of the same three conditions; it is
implemented as published and cited, with the conditions named in the code.

**Measurement.** Pairs eliminated per criterion, matrices built, and wall clock, for both engines,
over all three orders.

**Reject if** a criterion does not reduce matrices built. It cannot be rejected for being
*correct* and slow on small inputs; it can be rejected for not paying on any instance.

#### 5.3.1 A second deliverable: interreduction

§6.2 found that `reduce_grobner_basis` is **2479 ms of katsura-6 lex's 2963 ms**, which is the
largest single cost in the whole baseline. It lives in `src/grobner/buchberger.rs`, which this
workstream already owns, it is shared by both engines, and it is the same kind of work as the rest
of M16-C — removing work that does not have to be done. So it is assigned here, and reported
separately from the criteria so the two effects stay distinguishable.

The costs are visible without a profiler, and all three are quadratic in the pre-interreduction
basis size with a large constant:

- `minimize_grobner_basis` deduplicates with `monic.contains(&scaled)`: a full polynomial equality
  against every element kept so far. On katsura-6 lex the elements are both numerous and wide.
- It then calls `leading_monomial` — a scan of a polynomial's whole term map — inside a double loop
  over the basis. The leads can be taken once.
- `reduce_grobner_basis` clones all `n - 1` other polynomials once per element, to build the slice
  `normal_form` takes, before computing anything.

None of this changes the result: minimization and interreduction are defined by the properties
they establish, and the output is already canonically ordered. **The returned basis must be
identical**, which the existing uniqueness tests already check and which a direct before/after
comparison should check too.

Note that this benefits classical Buchberger as well — it calls the same function — so it is one of
the few M16 changes that improves the oracle. The oracle's *result* must not move.

**Correctness.** The computed reduced basis is unchanged — exact sequence equality against the
baseline and against `buchberger_reference`, over all three orders, under permuted generators,
duplicated generators, and redundant generators. Differential tests over generator orderings are
required, not optional: an unsound criterion typically survives the fixed corpus and fails on a
permutation.

**Owns** `src/grobner/pairs.rs`, `src/grobner/buchberger.rs`.
**Must not** modify F4 matrix construction, symbolic preprocessing, or elimination.

### 5.4 M16-D — Dense and adaptive finite-field linear algebra

**Hypothesis.** Fill-in reaches 13.6x and the F4-shaped sparse benchmark goes from 13 ms to 221 ms
for a 2x shape increase, so above some density a dense representation wins. M15 §7.3 could not
locate the crossover because it compared sparse row echelon against dense *reduced* row echelon —
strictly more work — and so is not evidence of anything about storage.

**The first deliverable is therefore a fair comparison**: dense row echelon, same pivot rule, same
normalization, same field, same input matrices, with representation-conversion time reported
separately from algorithm time.

**Then** adaptive strategies: dense row accumulators, per-row representation switching,
density-aware pivoting, dense treatment of selected blocks, buffer reuse. Note explicitly that
**global density can stay low while individual rows or blocks become dense** — M15's 13.6x is a
ratio of peak live entries to as-built entries on a matrix with thousands of columns, which is
consistent with a few very dense rows and is not evidence that the matrix is dense. A selection
policy keyed on global density would therefore be keyed on the wrong number.

**Reject** any adaptive policy whose crossover is not established by measurement. A dense backend
that loses everywhere is still a deliverable, as the honest answer to M15's open question.

**Correctness.** Dense and sparse agree on rank and row space over rectangular, singular, sparse,
dense, and fill-in-heavy matrices and over GF(7), GF(13), GF(541), GF(2^31 - 1), and a 64-bit
prime. `reduce_rows_against_pivots_with` honours the contract in §4.2 under every backend. Backend
choice cannot change a Gröbner basis: that is asserted end to end.

**Owns** `src/linalg/**`.
**Must not** modify F4 symbolic preprocessing or candidate extraction.

## 6. Baseline measurements

Machine: AMD Ryzen Threadripper PRO 5995WX, 64 cores / 128 threads, 503 GB RAM.
`rustc 1.97.0 (2d8144b78 2026-07-07)`, `cargo 1.97.0`. Release profile (`[profile.release]` is
Cargo's default: `opt-level = 3`, `debug-assertions = false`, `overflow-checks = false`).
Criterion 0.5 with `sample_size(10)`. GF(2^31 - 1) for performance, GF(7)/GF(13)/GF(541) and a
64-bit prime for correctness.

Measured at the M16-0 commit on `feat/m16-foundation`, which is the commit all four
implementation branches are based on.

### 6.1 The algorithm did not change

From `cargo run --release --example f4_statistics`. Every counter in
[`MILESTONE-F4.md`](MILESTONE-F4.md) §7.1 is reproduced **exactly** at the M16-0 commit: cyclic-5
lex still builds 32 matrices over 1222 Buchberger reductions, katsura-7 grevlex still peaks at
1 390 812 live nonzeros with 13.58x worst fill-in and 95.9% scaffolding, and all 24 rows agree
digit for digit.

That is the point of re-running them. M16-0 refactored pair scheduling onto leading monomials,
moved the product criterion into the queue, routed elimination through a backend selector, and
added an observer to the main loop. None of it changed what the algorithm does, and the counters
are how that is established rather than asserted.

### 6.2 Where the time actually goes

From `cargo run --release --example f4_profile`, which is new in M16-0. `other` is the total less
every stage: pair selection and basis bookkeeping. Milliseconds.

| system | order | total | symbolic | construction | elimination | extraction | interreduction | other |
|---|---|---|---|---|---|---|---|---|
| cyclic-4 | lex | 0.27 | 0.07 | 0.08 | 0.07 | 0.01 | 0.02 | 0.02 |
| cyclic-5 | lex | 29.97 | 3.39 | 5.20 | 14.69 | 0.24 | 6.09 | 0.36 |
| cyclic-5 | grlex | 21.79 | 2.20 | 3.44 | 14.68 | 0.16 | 0.87 | 0.44 |
| cyclic-5 | grevlex | 25.31 | 2.10 | 3.59 | **18.36** | 0.20 | 0.73 | 0.33 |
| katsura-4 | lex | 0.63 | 0.13 | 0.19 | 0.22 | 0.02 | 0.04 | 0.03 |
| katsura-5 | lex | 15.64 | 2.36 | 3.90 | 6.79 | 0.16 | 2.16 | 0.27 |
| katsura-5 | grlex | 1.95 | 0.32 | 0.52 | 0.74 | 0.04 | 0.27 | 0.05 |
| katsura-5 | grevlex | 1.87 | 0.29 | 0.48 | 0.72 | 0.04 | 0.30 | 0.05 |
| katsura-6 | lex | 2963.26 | 40.55 | 68.87 | 371.02 | 1.44 | **2479.28** | 2.09 |
| katsura-6 | grlex | 22.69 | 2.40 | 4.29 | 13.55 | 0.22 | 2.00 | 0.23 |
| katsura-6 | grevlex | 27.01 | 2.12 | 3.63 | **18.04** | 0.20 | 2.83 | 0.20 |
| katsura-7 | grlex | 509.23 | 24.58 | 37.00 | **412.53** | 1.30 | 32.37 | 1.44 |
| katsura-7 | grevlex | 896.32 | 19.05 | 34.09 | **791.81** | 1.82 | 45.30 | 4.25 |
| random-4 | lex | 7.73 | 1.33 | 2.27 | 3.74 | 0.10 | 0.13 | 0.16 |
| planted-6 | lex | 0.06 | 0.01 | 0.01 | 0.01 | 0.00 | 0.02 | 0.01 |

Three results here matter more than the rest, and two of them contradict the priority order the
preceding milestone proposed.

**Elimination is the computation.** 65% to 88% of the total on every instance above a millisecond:
791 of 896 ms on katsura-7 grevlex, 412 of 509 on katsura-7 grlex, 18.0 of 27.0 on katsura-6
grevlex. The linear algebra is where the time is, which is what M16-A and M16-D are aimed at, and
the measurement supports aiming there.

**Symbolic preprocessing is 2% to 15%, and it is smallest exactly where the reducer share is
largest.** katsura-7 grevlex is 95.9% scaffolding and spends **2.1%** of its time in symbolic
preprocessing. The preceding milestone put "reuse reducer multiples across batches" first on the
M16 list, on the strength of that 95.9%. The stage breakdown says the reducer rows are expensive
because they make the *matrix* larger — which elimination then pays for — and not because finding
them is slow. **Caching the rows attacks 2% of the cost; producing fewer of them attacks the 88%.**
That reorders M16-B: the valuable hypothesis is smaller multipliers, not reuse. The repetition rate
should still be measured, and `CacheMode::Count` exists to measure it, but the ceiling on what a
cache can win is now known and it is low.

**The final interreduction is 84% of katsura-6 under lex.** 2479 ms of 2963. That instance builds
59 matrices and returns a six-element basis, so the cost is neither in the matrices nor in the
answer but in `reduce_grobner_basis` between them. No counter in the preceding milestone could have
shown this, and it is the largest single cost anywhere in this baseline — larger than every
elimination in the table put together. It is a real finding, it is in shared machinery both engines
use, and §5.3 assigns it.

The suspects are visible in the code rather than needing a profiler: `minimize_grobner_basis`
deduplicates with `monic.contains(&scaled)`, which is a full polynomial equality against every
element kept so far; it then calls `leading_monomial` — a scan of the whole term map — inside a
double loop over the basis; and `reduce_grobner_basis` clones all `n - 1` other polynomials once
per element before taking a normal form. All three are quadratic in the pre-interreduction basis
size with a large constant, and katsura-6 lex is where that basis is both long and wide.

### 6.3 Divisor lookup really is a linear scan

From the same run. `scan/q` is basis elements examined per divisor query — one for a perfect index,
and the basis size for a scan.

| system | order | reducer rows | divisor queries | scan steps / query |
|---|---|---|---|---|
| cyclic-4 | grevlex | 102 | 151 | 4.7 |
| cyclic-5 | lex | 4823 | 5372 | 19.8 |
| katsura-5 | lex | 3186 | 3661 | 21.6 |
| katsura-6 | lex | 31816 | 33758 | **47.2** |
| katsura-6 | grevlex | 4572 | 4816 | 5.7 |
| katsura-7 | grlex | 12388 | 13073 | 22.0 |
| katsura-7 | grevlex | 25908 | 26503 | 6.1 |

The scan is confirmed, and it is worst under lex, where the intermediate basis is longest. It is
also, per §6.2, a scan inside the stage that costs 2% to 15% — so an index is worth having and is
not worth very much. The two facts belong together, and reporting the first without the second is
how a milestone spends itself on the wrong thing.

### 6.4 Reducer-multiple repetition

`CacheMode::Count` records which `(basis_index, multiplier)` pairs recur across batches without
serving anything, so the rate is measurable at the baseline. M16-B reports it; the measurement is
the gate on whether `CacheMode::Store` is implemented at all.

### 6.5 Wall clock

From `cargo bench --bench grobner`, Criterion medians at sample size 10, both engines on identical
inputs under the identical order, at the M16-0 commit. The `M15` columns are the same measurement
from [`MILESTONE-F4.md`](MILESTONE-F4.md) §7.2 on the same machine, so the two are comparable and
the difference is M16-0's own effect.

| system | order | Buchberger | F4 | F4 speedup | M15 Buchberger | M15 F4 |
|---|---|---|---|---|---|---|
| cyclic-3 | lex | 18.4 us | 18.3 us | 1.00x | 19.9 us | 19.2 us |
| cyclic-3 | grlex | 18.3 us | 18.6 us | 0.98x | 20.3 us | 19.1 us |
| cyclic-3 | grevlex | 18.3 us | 20.5 us | 0.89x | 20.6 us | 20.8 us |
| cyclic-4 | lex | 175 us | 180 us | 0.97x | 189 us | 179 us |
| cyclic-4 | grlex | 148 us | **132 us** | 1.12x | 156 us | 134 us |
| cyclic-4 | grevlex | **138 us** | 150 us | 0.92x | 160 us | 158 us |
| cyclic-5 | lex | 47.8 ms | **25.7 ms** | 1.86x | 53.3 ms | 27.1 ms |
| cyclic-5 | grlex | 57.0 ms | **20.1 ms** | 2.83x | 64.3 ms | 21.2 ms |
| cyclic-5 | grevlex | 34.2 ms | **21.6 ms** | 1.58x | 38.8 ms | 23.0 ms |
| katsura-3 | lex | 38.2 us | 41.7 us | 0.92x | 42.5 us | 42.6 us |
| katsura-3 | grlex | 29.5 us | 31.5 us | 0.93x | 32.4 us | 32.4 us |
| katsura-3 | grevlex | 29.8 us | 30.9 us | 0.96x | 33.4 us | 33.6 us |
| katsura-4 | lex | 719 us | **566 us** | 1.27x | 853 us | 567 us |
| katsura-4 | grlex | **200 us** | 233 us | 0.86x | 225 us | 244 us |
| katsura-4 | grevlex | **119 us** | 170 us | 0.70x | 136 us | 177 us |
| katsura-5 | lex | 172 ms | **14.2 ms** | **12.1x** | 191 ms | 14.8 ms |
| katsura-5 | grlex | 2.18 ms | **1.81 ms** | 1.20x | 2.47 ms | 1.92 ms |
| katsura-5 | grevlex | **1.21 ms** | 1.69 ms | 0.71x | 1.31 ms | 1.82 ms |
| katsura-6 | grlex | 36.0 ms | **22.8 ms** | 1.58x | 40.0 ms | 23.9 ms |
| katsura-6 | grevlex | **12.8 ms** | 28.1 ms | **0.46x** | 14.1 ms | 30.2 ms |
| random-3 | lex | 325 us | **278 us** | 1.17x | 362 us | 293 us |
| random-3 | grlex | **48.1 us** | 55.2 us | 0.87x | 53.9 us | 58.0 us |
| random-3 | grevlex | **32.2 us** | 41.3 us | 0.78x | 35.5 us | 42.7 us |
| random-4 | lex | 31.1 ms | **8.04 ms** | **3.86x** | 33.8 ms | 8.46 ms |
| random-4 | grlex | **748 us** | 771 us | 0.97x | 831 us | 805 us |
| random-4 | grevlex | 993 us | **885 us** | 1.12x | 1.09 ms | 940 us |
| planted-6 | lex | 53.4 us | **47.6 us** | 1.12x | 57.7 us | 48.8 us |
| planted-6 | grlex | 35.9 us | 34.8 us | 1.03x | 39.6 us | 37.1 us |
| planted-6 | grevlex | 36.1 us | 34.9 us | 1.04x | 41.1 us | 38.1 us |
| planted-8 | lex | 77.4 us | **66.6 us** | 1.16x | 90.2 us | 72.9 us |
| planted-8 | grlex | 58.8 us | 55.2 us | 1.07x | 66.0 us | 61.2 us |
| planted-8 | grevlex | 57.7 us | 57.1 us | 1.01x | 66.6 us | 62.7 us |

And the instances Buchberger does not finish here, from `grobner_f4_only`:

| system | order | F4 | M15 F4 |
|---|---|---|---|
| katsura-6 | lex | 3.06 s | 3.19 s |
| katsura-7 | grlex | 532 ms | 554 ms |
| katsura-7 | grevlex | 809 ms | 898 ms |

**M16-0 made both engines a few percent faster without changing the algorithm.** Every one of the
36 paired figures is at or below its M15 counterpart: Buchberger by 4% to 16% (katsura-5 lex 191 ms
to 172 ms, planted-8 lex 90.2 us to 77.4 us), F4 by 0% to 10% (katsura-7 grevlex 898 ms to 809 ms,
katsura-6 grevlex 30.2 ms to 28.1 ms). That is the leading-monomial refactor: `leading_monomial` is
a scan of a polynomial's whole term map, the queue asked for one per pair created, and Buchberger
asked for two more per pair to apply the product criterion. Buchberger gains more than F4 because
it creates pairs more often relative to the work it does per pair.

It is also the only *performance* change in M16-0, and it was a side effect of an interface
refactor rather than the point of it. The relative picture is unchanged: **katsura-6 grevlex is
still the worst paired result at 0.46x**, and it remains the milestone's headline target.

The three `grobner_f4_only` figures and the last few paired ones were measured while the four
implementation agents were starting up on the same machine. They came out *faster* than M15 rather
than slower, so the contamination was evidently small, but they are preliminary: §7 records an
authoritative serial re-measurement taken with the machine quiet.

## 7. Results

> Per-workstream results are appended here by A, B, C and D; the integrated result and the
> ablation study by M16-I.

### 7.1 M16-A — structured elimination

`ReductionStrategy::Structured` arranges the Macaulay matrix with the reducer multiples first,
ascending by leading column — which is descending by leading monomial, since the columns descend —
and hands that prefix to `linalg::echelon::reduce_rows_against_pivots_with` as a set of pivots that
is already established. The prefix is never read for a pivot scan, never normalized, and never
reduced against anything.

Implemented in `src/grobner/f4/structured.rs`, with the row permutation in
`MacaulayMatrix::partition_reducers_first`. `examples/f4_blocks.rs` reproduces every number below.

#### 7.1.1 The invariant holds, and it is checked rather than assumed

> **Reducer-block invariant.** Every reducer multiple has a distinct leading monomial, and no
> reducer multiple leads with a critical pair's lcm.

Symbolic preprocessing establishes both halves: a reducer is added for a monomial only when that
monomial is not yet covered, and adding it covers it, so no monomial gets two reducers; and every
pair lcm is seeded as covered before the closure starts, so no lcm gets a reducer at all. Pair rows
lead with their pair's lcm and nothing else does, which is why **two pairs sharing an lcm do not
break the claim** — the duplicate leading monomials are both in the pair block, which is the part
that gets eliminated.

`structured::check_reducer_block` returns the violation as a value rather than panicking, so the
invariant is checked in release as well as debug, and it is asserted directly on every batch of
cyclic-4 and katsura-5 under all three orders. No batch anywhere in the corpus violates it.

#### 7.1.2 The lever is the arrangement, not the function

`BlockPlan::ReducersFirstEchelon` — the same arrangement put through a full `row_echelon` — records
**identical** row operations and identical peak nonzeros to `ReducersFirstBlock` on every one of the
23 instances. That confirms the fact `linalg::echelon`'s own
`test_an_echelon_upper_block_makes_the_two_paths_agree` proves: an upper block that is already
echelon is left alone by a full pass too, so the split-aware function by itself saves only the
pivot-discovery scan, which does not show up in any counter and barely shows up in the clock. The
saving is entirely in *not reducing the reducer rows against the pair rows*, which only the
arrangement can prevent.

#### 7.1.3 Row operations go up; fill-in collapses

Replayed through `trace_batches`, so every plan eliminates the **identical** matrices and the
comparison is of eliminations rather than of computations. `ops` is row operations summed over the
batches, `peak` the largest live nonzero count any single batch reached, `fin` the final entries
summed, `ms` the elimination time. Ratios against the baseline arrangement; below 1.00 is cheaper.

| system | order | red% | ops:base | ops:blk | peak:base | pk:blk | fin:blk | ms:base | ms:blk |
|---|---|---|---|---|---|---|---|---|---|
| cyclic-4 | lex | 57.1 | 278 | 1.23 | 128 | 0.84 | 0.78 | 0.07 | 0.05 |
| cyclic-4 | grlex | 54.2 | 243 | 1.31 | 180 | 0.93 | 0.84 | 0.04 | 0.03 |
| cyclic-4 | grevlex | 59.3 | 231 | 1.54 | 204 | 1.00 | 0.91 | 0.05 | 0.03 |
| cyclic-5 | lex | 71.8 | 58 164 | 1.17 | 13 993 | 0.55 | 0.39 | 15.66 | 9.98 |
| cyclic-5 | grlex | 35.7 | 93 664 | 1.12 | 11 379 | 1.00 | 0.46 | 15.95 | 13.72 |
| cyclic-5 | grevlex | 65.5 | 79 775 | 1.54 | 17 061 | 0.49 | 0.35 | 18.24 | 15.55 |
| katsura-4 | lex | 70.5 | 824 | 1.17 | 567 | 0.68 | 0.56 | 0.23 | 0.11 |
| katsura-4 | grlex | 69.8 | 418 | 1.16 | 405 | 0.87 | 0.75 | 0.09 | 0.05 |
| katsura-4 | grevlex | 75.6 | 261 | 1.21 | 546 | 0.62 | 0.64 | 0.07 | 0.03 |
| katsura-5 | lex | 72.9 | 27 922 | 1.15 | 9 285 | 0.65 | 0.40 | 6.97 | 4.51 |
| katsura-5 | grlex | 73.7 | 4 039 | 1.31 | 3 126 | 0.66 | 0.62 | 0.77 | 0.63 |
| katsura-5 | grevlex | 87.2 | 3 179 | 1.41 | 7 818 | 0.34 | 0.37 | 0.76 | 0.59 |
| katsura-6 | lex | 77.5 | 792 478 | 1.11 | 151 624 | 0.43 | 0.28 | 410.4 | 265.2 |
| katsura-6 | grlex | 77.9 | 50 043 | 1.57 | 34 746 | 0.44 | 0.46 | 15.3 | 18.0 |
| katsura-6 | grevlex | 94.0 | 44 023 | 1.51 | 103 314 | **0.17** | 0.19 | 21.1 | 20.1 |
| katsura-7 | grlex | 80.0 | 638 769 | 1.81 | 368 156 | 0.29 | 0.33 | 469.2 | 555.0 |
| katsura-7 | grevlex | 95.9 | 608 356 | 1.83 | 1 390 812 | **0.08** | 0.11 | 806.0 | 931.0 |
| random-4 | lex | 71.1 | 20 163 | 1.07 | 6 619 | 0.91 | 0.51 | 4.26 | 2.70 |
| random-4 | grlex | 70.5 | 1 810 | 1.40 | 1 830 | 0.66 | 0.60 | 0.32 | 0.25 |
| random-4 | grevlex | 67.8 | 2 207 | 1.51 | 2 294 | 0.60 | 0.54 | 0.38 | 0.34 |
| planted-6 | lex | 27.3 | 24 | 1.00 | 42 | 0.95 | 0.88 | 0.01 | 0.01 |
| planted-6 | grlex | 33.3 | 12 | 1.00 | 30 | 1.00 | 1.00 | 0.01 | 0.00 |
| planted-6 | grevlex | 33.3 | 12 | 1.00 | 30 | 1.00 | 1.00 | 0.01 | 0.00 |

**The hypothesis as stated in §5.1 is half wrong.** Block elimination does *not* "never have to
discover `A`'s pivots and never fill in `A` or `B`" at no cost: row operations rise on every
instance that has reducer rows at all, by 1.07x to 1.83x, and they rise *most* exactly where the
reducer share is highest. The reason is structural rather than incidental. In the baseline
arrangement a pair row stops descending at the first column no earlier pair row owns — frequently a
column a reducer leads with — and becomes that column's pivot; the reducer row arriving later is
then reduced against it. With the reducers first, that column is already owned, so the pair row
keeps descending and pays another subtraction for each reducer column it passes through.

**The fill-in claim is right, and larger than the reducer share suggested.** Peak live nonzeros fall
to 0.08x on katsura-7 grevlex — 1.39 million entries to 111 thousand — 0.17x on katsura-6 grevlex,
0.29x on katsura-7 grlex, and 0.43x on katsura-6 lex. Final nonzeros fall to 0.11x and 0.19x on the
same two grevlex instances. 96% of katsura-7 grevlex's rows are reducer multiples; leaving them
untouched leaves their original sparsity intact, and the baseline was filling all of it in for
nothing.

So the two claims pull in opposite directions, and more row operations on much shorter rows is a
trade whose sign the counters cannot settle. §5.1's reject condition — "does not reduce row
operations **or** peak nonzeros on the grevlex instances where the reducer share is highest" — is
not met: peak nonzeros fall by 12x and 6x on exactly those instances.

#### 7.1.4 End to end it wins on grevlex and lex, and loses on grlex

From `cargo run --release --example f4_profile` against `-- a`, same machine, same session,
sequential. Milliseconds. `red` is reducer rows over the whole computation, from the diagnostics
table of the same runs.

| system | order | base total | A total | speedup | base elim | A elim | base red | A red |
|---|---|---|---|---|---|---|---|---|
| cyclic-4 | lex | 0.28 | 0.26 | 1.08x | 0.07 | 0.06 | 117 | 117 |
| cyclic-5 | lex | 29.0 | 26.2 | 1.11x | 14.2 | 12.1 | 4 823 | 6 537 |
| cyclic-5 | grlex | 21.8 | 18.3 | 1.20x | 14.7 | 11.4 | 1 614 | 1 511 |
| cyclic-5 | grevlex | 22.8 | 17.2 | 1.33x | 16.9 | 11.5 | 3 292 | 2 846 |
| katsura-4 | lex | 0.64 | 0.60 | 1.07x | 0.23 | 0.14 | 292 | 292 |
| katsura-5 | lex | 14.4 | 11.6 | 1.24x | 6.4 | 4.4 | 3 186 | 3 173 |
| katsura-5 | grlex | 1.73 | 1.80 | 0.96x | 0.65 | 0.61 | 560 | 555 |
| katsura-5 | grevlex | 1.88 | 1.28 | 1.47x | 0.72 | 0.39 | 666 | 534 |
| katsura-6 | lex | 3056.6 | 1463.1 | **2.09x** | 367.6 | 268.4 | 31 816 | 32 031 |
| katsura-6 | grlex | 24.6 | 25.5 | **0.96x** | 14.7 | 16.0 | 2 728 | 2 623 |
| katsura-6 | grevlex | 30.9 | 15.1 | **2.05x** | 20.7 | 8.6 | 4 572 | 2 873 |
| katsura-7 | grlex | 559.3 | 615.2 | **0.91x** | 455.6 | 514.6 | 12 388 | 12 000 |
| katsura-7 | grevlex | 864.6 | 360.8 | **2.40x** | 754.0 | 300.1 | 25 908 | 13 964 |
| random-4 | lex | 8.57 | 7.41 | 1.16x | 4.12 | 2.89 | 2 314 | 2 314 |
| random-4 | grlex | 2.94 | 0.76 | — | 0.31 | 0.25 | 268 | 253 |
| random-4 | grevlex | 0.98 | 0.94 | 1.04x | 0.38 | 0.34 | 295 | 294 |
| planted-6 | lex | 0.07 | 0.07 | 1.00x | 0.01 | 0.01 | 9 | 9 |

random-4 grlex has no speedup column because the baseline run's 2.94 ms is dominated by a 2.73 ms
interreduction that does not reproduce; its elimination, 0.31 against 0.25, is the comparable
number.

Every wall-clock number in §7.1 was taken with three sibling workstreams active on the same
machine, so the absolute milliseconds are contended and only the paired ratios — both
configurations run back to back in one session — should be read. `cargo bench --bench grobner` was
deliberately not run; the authoritative serial timing is the integrator's.

**katsura-6 grevlex is the milestone's headline target and it is now level.** M15 recorded F4 at
30.2 ms against Buchberger's 14.1 ms, a 0.47x loss. At 15.1 ms against the same baseline's 30.9 the
2.05x the structured path gains is almost exactly the deficit, so the gap §1 of this document opens
with should close — though confirming it needs Buchberger and F4 timed by the same instrument in
the same session, which §7.1 does not do and the integrator's benchmark does. katsura-7 grevlex is
2.40x faster and katsura-6 lex 2.09x faster. Repeated pairs put katsura-7 grevlex at
327/336/357/361 ms against 830/849/865/904, and katsura-6 grevlex at 14.0/14.1/14.9/15.1 against
27.5/28.8/29.3/30.9, so neither is noise.

**On the two grevlex instances the whole-computation effect is larger than the per-elimination
effect, for a reason that was not part of the hypothesis.** On the replayed batches the structured
elimination of katsura-7 grevlex is 1.16x *slower*; over the whole computation it is 2.40x faster.
The candidates the structured path emits are much sparser — final nonzeros 0.11x — so the basis
elements it appends are smaller, so fewer and smaller reducer multiples are needed, so the next
matrix is smaller. The reducer-row count over the computation falls from 25 908 to 13 964 on
katsura-7 grevlex and from 4 572 to 2 873 on katsura-6 grevlex, which is why symbolic preprocessing
(22.7 ms to 14.2) and construction (33.8 to 21.3) get faster too, in a workstream that touched
neither stage. The arrangement compounds through the basis.

That compounding is **specific to grevlex**, and the counters say so rather than being assumed.
Under lex the reducer-row count does not fall at all — 31 816 to 32 031 on katsura-6, 2 314
unchanged on random-4 — and on cyclic-5 lex it *rises*, 4 823 to 6 537, while the computation still
gets 1.11x faster. So lex's wins are the cheaper elimination on its own (katsura-6 lex 367.6 ms to
268.4) plus, on katsura-6 lex, a much cheaper final interreduction (2 579.6 ms to 1 069.3) that
comes from a different pre-interreduction basis rather than from anything this workstream touched.
Attributing katsura-6 lex's 2.09x to the elimination would be wrong; two thirds of its absolute
saving is in `reduce_grobner_basis`, which is M16-C's file.

**grlex regresses, and that is the honest result.** katsura-7 grlex is 0.91x and katsura-6 grlex
0.96x — the elimination itself is 1.13x and 1.09x slower — and the reducer-row count barely moves,
12 388 to 12 000 and 2 728 to 2 623, so there is no compounding to pay for the extra row
operations. grlex builds more, sparser matrices, where the fill-in the arrangement avoids was not
large enough to matter: pk:blk is 0.29x on katsura-7 grlex, but the absolute peak it is 0.29x of
was already a quarter of grevlex's. This is a per-order effect, and the natural follow-up is a
selection rule keyed on the reducer share or the observed fill-in — left to M16-D's adaptive work
and M16-I's defaults rather than guessed at here.

#### 7.1.5 Rejected: interreducing the reducer block

Making the upper-left block the identity on its own columns — so a pair row needs one subtraction
per reducer column instead of a chain of them — was implemented as `BlockPlan::InterreducedBlock`
and **measured and rejected**. On the replayed batches it costs more row operations than the plain
block on 17 of 23 instances (up to 2.18x the baseline on katsura-4 grlex), the same on the three
planted-6 instances, and fewer on only cyclic-5 grevlex and the two katsura-7 instances. It costs
more peak nonzeros than the plain block on every instance where the two differ at all — 0.32x
against 0.08x on katsura-7 grevlex, 0.44x against 0.17x on katsura-6 grevlex.

End to end it is worse than the plain block almost everywhere and worse than the baseline on
several instances. Milliseconds; `base` and `blk` are the §7.1.4 run, `int` a separate run with the
plan temporarily selected.

| system | order | base | blk | int |
|---|---|---|---|---|
| cyclic-5 | lex | 29.0 | 26.2 | 32.6 |
| katsura-5 | grlex | 1.73 | 1.80 | 2.80 |
| katsura-6 | grlex | 24.6 | 25.5 | 39.0 |
| katsura-6 | grevlex | 30.9 | 15.1 | 20.1 |
| katsura-7 | grlex | 559.3 | 615.2 | 853.0 |
| katsura-7 | grevlex | 864.6 | 360.8 | 389.3 |

Its one win is on the replayed katsura-7 grevlex batches in isolation — 549 ms against 806 for the
baseline arrangement and 931 for the plain block — and it does not survive being put in a
computation, because the denser basis elements it produces undo it. The plan is kept behind the
enum, documented as rejected, so the measurement can be re-run; nothing selects it.

#### 7.1.6 A correctness finding: the candidate polynomials are not invariant, the basis is

A row echelon form is not unique — it depends on the order the rows were processed in — so the two
arrangements legitimately produce **different candidate polynomials** from the same matrix. A pivot
row can differ in the pivot columns to the right of its own pivot. They happen to coincide on the
three-variable corpus, on planted-6, and on two of the three cyclic-4 instances; everywhere else —
cyclic-4 grlex upwards — they differ. `examples/f4_blocks.rs` reports this per instance in its
`poly` column.

What cannot differ is the set of pivot columns, which is fixed by the column ranks alone and
therefore by the matrix rather than by the arrangement. The input leading monomials are the same
set, so the **new** leading monomials are identical, which is exactly what candidate extraction
tests and what the next batch sees. Asserted batch by batch over the whole corpus and over
cyclic-4, katsura-4 and katsura-5, under all three orders, together with rank, dependency count,
and mutual span containment.

End to end the basis is identical, which is the acceptance test: a reduced Gröbner basis is unique.
Note, though, that the *trajectory* is not — katsura-6 lex builds 61 matrices over 4 975 pairs
structured against 59 over 4 611 unstructured — so `batches` and `pairs_reduced` are not comparable
between the two paths, and a counter that assumes they are would be reading noise. The final
interreduction on katsura-6 lex falls from 2 511–2 695 ms to 1 026–1 069 for the same reason: a
different pre-interreduction basis, not a faster `reduce_grobner_basis`. That cost is M16-C's.

#### 7.1.7 What this leaves

`Unstructured` remains the default. Moving it is M16-I's decision and the grlex regression is the
reason it should be made with the adaptive work in hand rather than now. `BatchStatistics::free_pivots`
is populated with the reducer block's size on the structured path and stays zero on the
unstructured one, as its documentation says.

One interface note for the integrator: `ReductionStrategy::Structured`'s doc comment in the frozen
`src/grobner/f4/options.rs` still reads "Not yet implemented; currently the unstructured path",
which is now false. Correcting it is a one-line documentation change in a file this workstream does
not own.

### 7.2 M16-B — symbolic preprocessing and monomial indexing

All three hypotheses §5.2 names were implemented and measured. **All three were rejected**, two of
them after the code that implements them had been written and benchmarked. What did pay was none of
them: it was how a monomial is hashed, which is what the three measurements kept pointing at.

The default configuration is unchanged — `ReducerSelection::FirstApplicable`, `CacheMode::Off` —
and `f4` returns the identical basis under every selection policy, every cache mode and all three
orders, which `test_every_configuration_agrees_with_the_baseline` asserts over the cross product.

Measured on the §6 machine and toolchain, release profile, `cargo run --release --example
f4_selection` and `--example f4_profile`. **Caveat:** three sibling workstreams were building and
running on the same machine throughout, so every wall clock here is from an interleaved A/B of two
binaries run back to back, five rounds, median reported — not from an idle machine. The counters
(`reducers`, `rows`, `cols`, `peak nz`, `row ops`, `scan/q`, `reuse`) are deterministic and are not
affected. The authoritative serial timing is the integrator's.

#### 7.2.1 Rejected: smaller multipliers (`ReducerSelection::LargestLeadingMonomial`)

Implemented as specified: the divisor whose leading monomial is largest under the order in force,
ties broken by the smaller basis index — a tiebreaker that is needed, since two basis elements can
lead with the same monomial, and is exercised by `test_find_largest_divisor_tiebreak`.

The hypothesis was that the smallest multiplier introduces the fewest new monomials, so the closure
and the matrix shrink. **It is the other way round on every instance that matters.**

| system | order | reducers first → largest | largest matrix | peak nz | row ops | total/ms |
|---|---|---|---|---|---|---|
| cyclic-4 | lex | 117 → **105** | 28x29 → 26x26 | 128 → 106 | 278 → 252 | 0.25 → **0.17** |
| cyclic-5 | lex | 4823 → **4550** | 565x351 → 532x337 | 13993 → 12200 | 58164 → 56522 | 27.9 → **25.2** |
| cyclic-5 | grlex | 1614 → 1779 | 732x228 → 726x277 | 11379 → 12019 | 93664 → 98404 | 20.5 → 23.5 |
| cyclic-5 | grevlex | 3292 → 4418 | 635x463 → 873x712 | 17061 → 55309 | 79775 → 114079 | 23.3 → 50.0 |
| katsura-5 | lex | 3186 → 3186 | unchanged | unchanged | unchanged | 13.0 → 13.4 |
| katsura-5 | grevlex | 666 → 842 | 278x291 → 390x403 | 7818 → 8907 | 3179 → 4334 | 1.63 → 2.19 |
| katsura-6 | lex | 31816 → 31816 | unchanged | unchanged | unchanged | 3005 → 3177 |
| katsura-6 | grlex | 2728 → 3913 | 644x674 → 1262x1292 | 34746 → 65129 | 50043 → 66236 | 22.1 → 36.7 |
| katsura-6 | grevlex | 4572 → 6371 | 1388x1412 → 2593x2623 | 103314 → 209347 | 44023 → 63388 | 28.6 → 61.4 |
| katsura-7 | grlex | 12388 → 22105 | 2450x2476 → 6946x7008 | 368156 → 1017564 | 638769 → 964997 | 544 → 1228 |
| katsura-7 | grevlex | 25908 → **43453** | 6810x6862 → **16750x16812** | 1.39M → **3.06M** | 608356 → 1068505 | 887 → **3045** |

katsura-7 under grevlex — the instance §6.2 identifies as the one to fix — gets a 68% larger
closure, a 2.5x larger matrix, 2.2x the peak live entries and takes **3.4x as long**. The only wins
are the lex instances of cyclic, where the closure shrinks 2–6% and the computation gets 7–10%
shorter.

The mechanism is visible once stated the right way round. The reducer row for a monomial `u` is
`(u / LM(g)) * g`, and its leading monomial is `u` whichever `g` is chosen — the multiplier's size
is not what the matrix pays for. What the matrix pays for is the row's *tail*, `(u / LM(g)) * t` for
each tail monomial `t` of `g`. A small `g` low in the basis has a tail far below its own leading
monomial, so dividing through by a large multiplier drops those monomials well down the order, where
they are likelier to be irreducible or already covered. A large `g` has a tail close to `LM(g)`, so
the tail of its multiple sits just below `u` — reducible, and each reducible monomial is another
row. Choosing the largest divisor minimizes the multiplier and maximizes the fan-out.

**Kept, not merged into the default.** The variant is reachable through `F4Options` because the
option surface declares it and the ablation study needs it; `FirstApplicable` remains the default
and the measurement above is why.

#### 7.2.2 Rejected: a divisibility index (`src/grobner/f4/divisors.rs`, reverted)

Built, tested against the reference scan, measured, and reverted in commit `fcf81df`. The structure
grouped the leading monomials by total degree — necessary condition `deg LM <= deg u` — and gave
first-applicable selection a precomputed ascending list of the indices at or below the query's
degree, so the scan it replaced was restricted to a subsequence of itself in the same order. That
construction is what makes the answer provably identical; a plainer walk over the degree groups is
not, because a divisor found in a low-degree group does not license skipping a lower-indexed one
above it — and measured, that walk examined **more** elements than the plain scan (katsura-6 lex
47.2 → 48.5).

It did reduce examinations, and it was still slower:

| system | order | scan/q scan → index | symbolic/ms scan → index |
|---|---|---|---|
| cyclic-4 | grevlex | 4.7 → 3.8 | 0.05 → 0.05 |
| cyclic-5 | lex | 19.8 → 17.9 | 3.26 → 3.27 |
| cyclic-5 | grlex | 17.4 → 12.0 | 2.25 → 2.34 |
| katsura-5 | lex | 21.6 → 19.6 | 2.27 → 2.30 |
| katsura-6 | lex | **47.2 → 44.7** | 42.8 → 44.0 |
| katsura-6 | grevlex | 5.7 → 5.3 | 2.40 → 2.48 |
| katsura-7 | grlex | 22.0 → 20.5 | **23.9 → 28.4** |
| katsura-7 | grevlex | 6.1 → 5.8 | **20.2 → 23.6** |

The scan it replaced is sequential, and that is the whole of it. Examining elements `0, 1, 2, ...`
walks one array in order and the prefetcher covers it; examining `0, 2, 5, 7, ...` reads the same
array through an index list and can take a cache miss per skip. Fewer examinations bought more
misses than they saved divisions.

**And the divisions were never the cost.** katsura-6 under lex performs 33 758 divisor queries at
47.2 elements each — 1.59 million divisibility tests, each a handful of integer comparisons — inside
a stage that is 41 ms of a 3005 ms computation. Eliminating divisor lookup *entirely* would save
about 1% of the symbolic stage's share of 1.4%. §6.3 reports the scan correctly and the scan is
nonetheless not worth indexing; the two facts belong together.

A support bitmask over the variables was measured alongside and also rejected: for these bases the
mask rarely rejects, so it adds a word operation ahead of a `checked_div` that already exits on the
first variable it fails.

#### 7.2.3 Rejected: reducer reuse (`CacheMode::Store`, measured and not merged)

`CacheMode::Count` first, as §5.2 requires, before anything was implemented. **The repetition rate
is high** — the preceding milestone's expectation of recurrence was right:

| system | order | reducer rows | reused | rate |
|---|---|---|---|---|
| cyclic-4 | lex | 117 | 34 | 29% |
| cyclic-5 | lex | 4823 | 2796 | 58% |
| cyclic-5 | grevlex | 3292 | 1417 | 43% |
| katsura-4 | lex | 292 | 225 | 77% |
| katsura-5 | lex | 3186 | 2841 | **89%** |
| katsura-6 | lex | 31816 | 30169 | **95%** |
| katsura-6 | grevlex | 4572 | 2763 | 60% |
| katsura-7 | grlex | 12388 | 7974 | 64% |
| katsura-7 | grevlex | 25908 | 16485 | 64% |
| random-4 | lex | 2314 | 2077 | **90%** |

So the gate §5.2 set is passed, and `CacheMode::Store` was implemented: the shifted terms of a
multiple — not its sparse row, whose column indices belong to one batch's column set — stored and
served. It is slower everywhere, at every one of those rates:

| system | order | reuse | symbolic/ms off → count → store |
|---|---|---|---|
| cyclic-5 | lex | 58% | 1.60 → 1.72 → 1.89 |
| katsura-5 | lex | 89% | 1.00 → 1.06 → 1.09 |
| katsura-6 | lex | 95% | 20.3 → 21.8 → 21.9 |
| katsura-6 | grevlex | 60% | 1.05 → 1.12 → 1.27 |
| katsura-7 | grlex | 64% | 13.2 → 13.9 → 14.8 |
| katsura-7 | grevlex | 64% | 9.9 → 11.8 → **14.9** |

The rate was the wrong question. What a cache avoids is building a multiple's terms, and that is one
integer addition per variable per term — a few nanoseconds for a monomial. Serving them instead
costs a hash of `(basis_index, multiplier)` and a pointer chase to a heap vector, which is more.
A 95% hit rate on work that cheap still loses. `Store` is left delegating to `Count`, and its doc
comment records the measurement.

#### 7.2.4 Merged: how a monomial is hashed

The three rejections agree on where the stage's time actually is. It is not the divisor scan and it
is not rebuilding multiples; it is the two hash-set operations the closure traversal performs for
every monomial it meets — `examined.insert`, to handle no monomial twice, and `covered.contains`, to
ask whether the invariant already holds there.

`Monomial<N>` is `[u32; N]`, which the standard library hashes through `hash_slice` as one byte
slice, under `SipHash-1-3`. SipHash is the default because it withstands adversarially chosen keys.
These keys are monomials the computation produced itself, and a caller who can choose them can
already choose the ideal, so the guarantee buys nothing here. A multiplicative word hash with a
`splitmix64` finalizer replaces it:

| system | order | symbolic/ms | total/ms |
|---|---|---|---|
| cyclic-4 | lex | 0.07 → 0.05 (−29%) | 0.30 → 0.25 |
| cyclic-5 | lex | 3.22 → 1.64 (−49%) | 29.7 → 27.6 |
| cyclic-5 | grlex | 2.25 → 1.19 (−47%) | 22.7 → 21.3 |
| cyclic-5 | grevlex | 1.83 → 0.96 (−48%) | 24.0 → 23.3 |
| katsura-4 | lex | 0.13 → 0.07 (−46%) | 0.63 → 0.56 |
| katsura-5 | lex | 2.23 → 1.11 (−50%) | 15.3 → 14.1 |
| katsura-5 | grevlex | 0.29 → 0.15 (−48%) | 1.91 → 1.74 |
| katsura-6 | lex | 41.1 → 19.4 (−53%) | 2997 → 2988 |
| katsura-6 | grlex | 2.40 → 1.25 (−48%) | 23.7 → 23.7 |
| katsura-6 | grevlex | 2.34 → 1.06 (−55%) | 31.4 → 28.7 |
| katsura-7 | grlex | 23.6 → 13.9 (−41%) | 559 → 512 |
| katsura-7 | grevlex | 18.9 → 9.63 (−49%) | 904 → 851 |
| random-4 | lex | 1.46 → 0.68 (−53%) | 8.42 → 7.29 |

Symbolic preprocessing roughly halves — 25% to 55% off, about −50% on everything above a
millisecond. The totals move 0% to 19%, which is what a stage worth 2–15% can contribute, and
katsura-6 under lex barely moves at all because §6.2's interreduction finding owns 84% of it.

Two details are load-bearing, and both were found by measuring rather than by reasoning:

- **Without the finalizer it is twice as slow as SipHash.** The low bits of a multiplicative
  accumulator depend only on the low bits of the key, and `hashbrown` takes the bucket index from
  exactly those bits. Small exponent vectors collided enough to double the stage. Two shifts and a
  multiply fix it. `test_monomial_hasher` compares the low-bit bucket spread against the standard
  hasher so this cannot regress silently.
- **A byte-at-a-time `write` is also slower than SipHash.** It is the hot path, because an integer
  array arrives as one byte slice: 28 rounds for a seven-variable monomial. Eight bytes at a time is
  the version that pays.

Nothing about the computation changes. The hasher affects iteration order of nothing that is read in
order: `Preprocessed::leading_monomials` is used only for membership, and the row sequence is built
in the deterministic order the `VecDeque` traversal produces.

#### 7.2.5 Tests added

In `symbolic.rs`: the closure invariant asserted directly under every selection policy and every
cache mode over the ten-system corpus and all three orders, and over both the widest and narrowest
batch shapes; a differential test of each policy's dispatch against its reference scan over
randomized bases and monomials, asserting the same index *and* the same quotient; a round trip of
every constructed row against independently computed polynomial arithmetic; cache clearing not
changing the rows; the largest-leading-monomial tiebreaker; and the hasher's agreement with equality
and its low-bit spread. In `tests.rs`: identical basis under both policies against `buchberger` over
the corpus, under permuted, duplicated and redundant generators, and determinism of the basis *and*
the counters across repeated runs. 698 library tests pass in debug and in release, 8 ignored, up
from 693 at the baseline.

#### 7.2.6 Notes for the integrator

- **One edit outside M16-B's column, since reverted.** Adding `src/grobner/f4/divisors.rs` required
  `pub mod divisors;` in the frozen `f4/mod.rs`. The revert removed both, so `f4/mod.rs` is
  byte-identical to the baseline on this branch. M16-A will need the same one-line addition for
  `structured.rs`.
- **`ReducerSelection::LargestLeadingMonomial`'s doc comment in `options.rs` says "Not yet
  implemented; currently first-applicable", which is now false.** `options.rs` is frozen, so it was
  left alone. It wants one line: the policy is implemented, and `FirstApplicable` is the default
  because §7.2.1 measured the alternative as 3.4x slower on katsura-7 grevlex.
- **The per-worktree `.cargo/config.toml` does not take effect.** The ambient environment sets
  `CARGO_TARGET_DIR=/buildcache/cargo-target/interactive-mfaulk`, and an environment variable
  overrides `[build] target-dir` in `.cargo/config.toml`. All four workstreams were therefore
  sharing one target directory and overwriting each other's test binaries — which showed up as the
  library test count changing between runs, at one point reporting M16-C's interreduction tests on
  this branch. Every measurement and test run reported here was taken with `CARGO_TARGET_DIR` set
  explicitly to the worktree. Anyone measuring on this machine has to do the same.
- **`cargo test --doc` fails, at the baseline commit too.** `Cargo.toml` sets `[lib] doctest =
  false`, so `cargo test` never runs them and nothing is broken; forcing them finds four untagged
  code fences of prose in `src/fft/evaluate.rs` and `src/linalg/crout.rs` that `rustdoc` tries to
  compile. Pre-existing and untouched here; worth `text` fences at some point outside M16.

### 7.3 M16-C — critical-pair criteria and interreduction

Two deliverables, reported separately because they are independent changes to the same workstream's
files. Counters are deterministic and are the primary evidence. Wall clock was taken on the §6
machine in release, but **three sibling workstreams were building on it concurrently**, so the
times below are indicative and the integrator's serial run is authoritative. The counters are not
affected by that.

Measured at `20b6602` on `feat/m16-pair-criteria`, against the `a11cbab` M16-0 baseline.

#### 7.3.1 The interreduction

§6.2 found `reduce_grobner_basis` to be 2479 ms of katsura-6 lex's 2963 ms. **None of the cost was
in the three suspects §5.3.1 named.** Instrumenting the function directly:

| | katsura-6 lex |
|---|---|
| pre-interreduction basis | 113 elements, 3660 terms |
| minimal basis | 6 elements, 174 terms |
| `minimize_grobner_basis` | 0.5 ms |
| the interreduction loop | 2534 ms |

So the quadratic deduplication and the double `leading_monomial` scan together account for 0.02% of
it, and the cloned divisor slice cannot account for anything: there are six polynomials of 174
terms to clone. All of the cost is two calls to `normal_form`, one of 1.27 s each:

```text
ELEM 0 lead=x1   7 terms -> 33 terms in 1.272936527s
ELEM 1 lead=x2  32 terms -> 32 terms in 1.271073570s
ELEM 2 lead=x3  35 terms -> 32 terms in  22.750310ms
ELEM 3 lead=x4  36 terms -> 32 terms in 374.489000µs
ELEM 4 lead=x5  32 terms -> 32 terms in  11.873000µs
ELEM 5 lead=x6^32                      in   9.819000µs
```

The cause is substitution depth, not basis size. That basis is in shape position: five elements
with linear leading monomials over one univariate of degree 32. Reducing the tail of the `x1`
element against an **unreduced** `x2` element substitutes 31 terms, each of which then has to be
reduced against an unreduced `x3` element, and so on down the chain — and the elements were being
reduced in descending leading-monomial order, which is the worst possible one.

**The fix is to interreduce in ascending leading-monomial order, writing each remainder back in
place.** Every divisor below the element being reduced is then already fully reduced, so a
substitution introduces monomials that are already in normal form. The element being reduced is
swapped to the end of the vector so that the others are a contiguous slice, which removes the clone
as well and needs no change to `normal_form`'s interface.

This cannot change the answer, and the argument is worth stating because it is what makes the
reordering safe. A remainder `r` is congruent to its element modulo the ideal, has that element's
leading monomial — minimization left it divisible by no other leading monomial, so division cannot
cancel it — and has no monomial divisible by any other element's leading monomial. Two elements
with those three properties differ by an ideal member all of whose monomials are irreducible, which
is zero. So `r` depends only on the element's leading monomial, and not on which divisor was
applied first or on whether a divisor's tail had been reduced yet; those change only how many steps
the reduction takes. Reducing an element never changes its leading monomial, which is all that
divisibility is tested against.

Interreduction, milliseconds, baseline criteria in both columns:

| system | order | M16-0 | M16-C | |
|---|---|---|---|---|
| cyclic-5 | lex | 6.09 | 0.37 | 16.5x |
| cyclic-5 | grlex | 0.87 | 0.65 | |
| katsura-5 | lex | 2.16 | 0.16 | 13.5x |
| **katsura-6** | **lex** | **2479.28** | **1.04** | **2384x** |
| katsura-6 | grlex | 2.00 | 1.75 | |
| katsura-6 | grevlex | 2.83 | 2.54 | |
| katsura-7 | grlex | 32.37 | 29.12 | |
| katsura-7 | grevlex | 45.30 | 39.85 | |

katsura-6 lex as a whole goes from 2963 ms to 520 ms. The instances that barely move are the ones
whose minimal basis is large — katsura-7 grlex returns 64 elements and 4663 terms — where the
reduction is work that genuinely has to be done rather than work done twice. Interreduction is
still the largest single stage on those two instances after the criteria are enabled.

Both engines call this function, so classical Buchberger gets the same improvement; its *result*
does not move, which the existing reference-agreement tests and a new differential test against the
naive formulation both check.

The minimization was also cleaned up — leading monomials taken once rather than once per
comparison, and duplicates compared only against elements sharing a leading monomial and term
count — but on the evidence above that is tidiness, not a measured win, and it is reported as such.

#### 7.3.2 The criteria

Buchberger's chain criterion at selection time and Gebauer–Möller pair-set minimization at
insertion time, both in `pairs.rs` and so available to both engines, each behind its own flag.

**The soundness conditions, as implemented.** The chain criterion is Cox, Little and O'Shea's
`Criterion(f_i, f_j, B)` (*Ideals, Varieties, and Algorithms* §2.10): discard `(i, j)` when some
`k ∉ {i, j}` has `LM(f_k)` dividing `lcm(LM f_i, LM f_j)` **and** neither `(i, k)` nor `(k, j)` is
in `B`. Gebauer–Möller is the published installation (Gebauer & Möller 1988, criteria B, M and F;
Becker & Weispfenning, *Gröbner Bases*, Algorithm 5.5 `UPDATE`): B discards a pending `(g1, g2)`
when `LM(h)` divides its lcm and **both** `lcm(LM g1, LM h)` and `lcm(LM h, LM g2)` differ from it;
M keeps one new pair per lcm under divisibility; F drops a relatively prime new pair *after* it has
served as an lcm representative under M, which is why F is a second pass.

Two points where the implementation is deliberately stronger than a naive reading, both stated in
the code:

1. "In `B`" is read as **"selected and processed"**, not "absent from the pending set". A pair
   selected in the same F4 batch has left the pending set but has not been reduced, and three pairs
   on one another's lcms could then each be discarded on the strength of the other two. A pair
   Gebauer–Möller removed is likewise absent from the pending set, and its own redundancy is
   justified by two pairs that are still pending — letting it witness one of those closes the loop.
   With Gebauer–Möller off, every pair leaves the pending set by being selected, so the two
   readings coincide and this is exactly the published criterion.
2. Gebauer–Möller's criterion F is Buchberger's first criterion, so it is applied only when
   `PairCriteria::product` is also set, and its eliminations are counted under `gebauer_moller` so
   that `product` keeps meaning what the baseline measured.

The invariant both installations maintain is the same: every pair not in `B` has a standard
representation modulo the final basis, justified either by a pair processed strictly earlier or by
pairs whose lcm divides its own strictly. That is what makes the justification well-founded rather
than circular, and it is why (1) is not optional.

**F4: pairs reduced, matrices built, largest matrix.** From
`cargo run --release --example pair_criteria`. `product` is the measured baseline. `chain` is
product plus the chain criterion; `gm` is product plus Gebauer–Möller; `all` is all three.

| system | order | criteria | batches | reduced | prod | chain | gm | max rows | ms |
|---|---|---|---|---|---|---|---|---|---|
| cyclic-5 | lex | product | 32 | 948 | 180 | 0 | 0 | 565 | 23.6 |
| cyclic-5 | lex | chain | 23 | 212 | 187 | 777 | 0 | 160 | 4.8 |
| cyclic-5 | lex | gm | 24 | 106 | 0 | 0 | 1169 | 161 | 3.7 |
| cyclic-5 | grevlex | product | 22 | 868 | 167 | 0 | 0 | 635 | 25.5 |
| cyclic-5 | grevlex | chain | 14 | 204 | 167 | 664 | 0 | 161 | 3.2 |
| cyclic-5 | grevlex | gm | 14 | 116 | 0 | 0 | 919 | 110 | 2.0 |
| katsura-5 | lex | product | 29 | 593 | 353 | 0 | 0 | 381 | 13.8 |
| katsura-5 | lex | chain | 19 | 188 | 353 | 405 | 0 | 166 | 4.6 |
| katsura-5 | lex | gm | 20 | 50 | 0 | 0 | 896 | 38 | 0.9 |
| katsura-6 | lex | product | 59 | 4611 | 1717 | 0 | 0 | 1954 | 556.8 |
| katsura-6 | lex | chain | 38 | 785 | 1648 | 3345 | 0 | 790 | 68.9 |
| katsura-6 | lex | gm | 107 | 231 | 0 | 0 | 20884 | 92 | 23.2 |
| katsura-6 | grlex | product | 9 | 387 | 279 | 0 | 0 | 644 | 26.3 |
| katsura-6 | grlex | chain | 6 | 214 | 279 | 173 | 0 | 378 | 9.9 |
| katsura-6 | grlex | gm | 6 | 103 | 0 | 0 | 563 | 353 | 6.5 |
| katsura-6 | grevlex | product | 8 | 147 | 129 | 0 | 0 | 1388 | 33.1 |
| katsura-6 | grevlex | chain | 6 | 93 | 129 | 54 | 0 | 754 | 9.4 |
| katsura-6 | grevlex | gm | 6 | 68 | 0 | 0 | 208 | 670 | 6.9 |
| katsura-7 | grlex | product | 11 | 1553 | 862 | 0 | 0 | 2450 | 573.8 |
| katsura-7 | grlex | chain | 7 | 616 | 862 | 937 | 0 | 1046 | 122.3 |
| katsura-7 | grlex | gm | 7 | 264 | 0 | 0 | 2151 | 1051 | 76.8 |
| katsura-7 | grevlex | product | 10 | 555 | 348 | 0 | 0 | 6810 | 928.2 |
| katsura-7 | grevlex | chain | 7 | 243 | 348 | 312 | 0 | 2817 | 146.7 |
| katsura-7 | grevlex | gm | 7 | 166 | 0 | 0 | 737 | 2633 | 110.9 |

Both criteria pay on every instance, and they pay in the currency the hypothesis named: fewer
matrices, and smaller ones. Gebauer–Möller is the stronger of the two throughout, and
**`all` is identical to `gm` in every row** — `chain` is 0 whenever Gebauer–Möller is on. That is
the expected consequence of §7.3.2 (1): a pair Gebauer–Möller removed never becomes a chain
witness, and the pair set Gebauer–Möller maintains is already lcm-minimal, so the selection-time
criterion has nothing left to find. The chain criterion earns its place as the criterion that works
without insertion-time bookkeeping, not as an addition to Gebauer–Möller.

katsura-6 lex is the one row where Gebauer–Möller *increases* the batch count, 59 to 107. It is
building many more, far smaller matrices — 92 rows against 1954 — and is 24x faster for it.

**Classical Buchberger.** From `cargo run --release --example pair_criteria -- buchberger`.

| system | order | criteria | considered | reduced | zero | prod | chain | gm | ms |
|---|---|---|---|---|---|---|---|---|---|
| katsura-4 | lex | product | 153 | 84 | 70 | 69 | 0 | 0 | 1.1 |
| katsura-4 | lex | chain | 153 | 25 | 11 | 69 | 59 | 0 | 0.4 |
| katsura-4 | lex | gm | 16 | 16 | 2 | 0 | 0 | 137 | 0.2 |
| katsura-5 | lex | product | 2415 | 1790 | 1725 | 625 | 0 | 0 | 184.2 |
| katsura-5 | lex | chain | 3240 | 134 | 58 | 813 | 2293 | 0 | 12.4 |
| katsura-5 | lex | gm | 162 | 162 | 5 | 0 | 0 | 12879 | 35.7 |
| katsura-5 | grevlex | product | 105 | 49 | 39 | 56 | 0 | 0 | 1.3 |
| katsura-5 | grevlex | chain | 105 | 33 | 23 | 56 | 16 | 0 | 0.8 |
| katsura-5 | grevlex | gm | 30 | 30 | 20 | 0 | 0 | 75 | 0.8 |
| cyclic-5 | grlex | product | 1653 | 1454 | 1401 | 199 | 0 | 0 | 63.6 |
| cyclic-5 | grlex | chain | 1653 | 144 | 91 | 199 | 1310 | 0 | 5.6 |
| cyclic-5 | grlex | gm | 147 | 147 | 94 | 0 | 0 | 1506 | 5.5 |
| katsura-6 | grlex | product | 666 | 387 | 356 | 279 | 0 | 0 | 37.6 |
| katsura-6 | grlex | chain | 666 | 133 | 102 | 279 | 254 | 0 | 11.0 |
| katsura-6 | grevlex | product | 276 | 147 | 129 | 129 | 0 | 0 | 14.5 |
| katsura-6 | grevlex | chain | 276 | 73 | 55 | 129 | 74 | 0 | 5.4 |

In the classical engine **neither criterion dominates**: on katsura-5 lex the chain criterion
reduces 134 pairs to Gebauer–Möller's 162 and is 2.9x faster, because Gebauer–Möller's criterion B
rescans the pending set on every insertion and that set is longest under lex. Elsewhere
Gebauer–Möller wins. Zero reductions — the pairs Buchberger pays full price to discover are
useless — fall from 1725 to 58 on katsura-5 lex, which is the clearest statement of what these
criteria are for.

**Combined, against the M16-0 baseline.** Both deliverables, from
`cargo run --release --example f4_profile -- c` against §6.2. Total milliseconds.

| system | order | M16-0 | M16-C | |
|---|---|---|---|---|
| cyclic-5 | lex | 29.97 | 3.85 | 7.8x |
| cyclic-5 | grevlex | 25.31 | 1.97 | 12.8x |
| katsura-5 | lex | 15.64 | 1.02 | 15.3x |
| **katsura-6** | **lex** | **2963.26** | **23.36** | **127x** |
| katsura-6 | grlex | 22.69 | 6.85 | 3.3x |
| katsura-6 | grevlex | 27.01 | 7.66 | 3.5x |
| katsura-7 | grlex | 509.23 | 76.41 | 6.7x |
| katsura-7 | grevlex | 896.32 | 105.86 | 8.5x |
| random-4 | lex | 7.73 | 1.03 | 7.5x |

**This moves the bottleneck, which the other workstreams should know.** §6.2's headline was that
elimination is 65–88% of the computation. With the criteria enabled it is 2.84 ms of katsura-6 lex's
23.36 — 12% — and symbolic preprocessing is now the largest stage there at 6.95 ms. On katsura-7
the ranking is unchanged and elimination is still 41–51%, with interreduction second. The criteria
do not make elimination faster; they remove rows, which makes the matrices small enough that the
other stages matter.

**Defaults are unchanged.** `F4Options::default()` and `PairCriteria::default()` are still the
measured baseline, per §4.1: M16-I moves the default deliberately. On this evidence the
configuration to move it to is `PairCriteria::ALL`, which is `gebauer_moller` plus `product` in
effect.

#### 7.3.3 Correctness

- Every one of the eight criteria combinations returns the criteria-free computation's basis
  exactly, in **both** engines, over all three orders: the 22-system corpus, every rotation and the
  reversal of each generator list, a duplicated generator, a scalar multiple, a generator already
  in the ideal, inconsistent systems, and 24 randomized sparse quadratic systems over GF(7) and
  GF(13).
- Every combination is also checked against `buchberger_reference`, the naive textbook
  implementation, over all three orders. That matters because the criteria-free computation shares
  the pair queue and the interreduction with the criteria-enabled one and the reference shares
  nothing; katsura-3 under lex is covered by the slow `#[ignore]`d test, as it takes the reference
  about two and a half minutes.
- A regression test pins the unsound shortcut: three leading monomials each dividing the lcm of the
  other two, where naive lcm-divisibility fires on the first pair selected and the sound criterion
  must not.
- Hand-verified unit tests assert *which* criterion eliminated a pair, one per Gebauer–Möller
  condition.
- The interreduction is checked against the naive formulation element for element, on
  pre-interreduction bases rather than on finished ones, plus the four properties it is defined by
  and idempotence.
- `test_pair_criteria_do_not_change_the_basis`,
  `test_every_configuration_agrees_with_the_baseline`, and both slow `#[ignore]`d
  engine-agreement tests pass unchanged. 703 tests pass in debug and release.

#### 7.3.4 Notes for the integrator

- `Statistics` (classical Buchberger) gained a `criteria: CriterionCounts` field, which forced a
  one-line addition to the exhaustive destructuring pattern in `examples/grobner_statistics.rs`.
  That is the only edit to existing content in an append-only file.
- `examples/pair_criteria.rs` is new and reports the tables above.
- No interface change is needed outside M16-C's files. In particular `normal_form` was left alone:
  swapping the element under reduction to the end of the vector makes the other elements a
  contiguous slice, so the clone §5.3.1 identified can be removed without touching `src/poly`.

### 7.4 M16-D — dense and adaptive linear algebra

Three backends behind `linalg::echelon`, all running the *same* algorithm — leftmost nonzero
column, first row to reach it, unit pivot, one inverse per pivot — so they agree on the resulting
matrix and on every counter in `EliminationStatistics`, and a comparison between them measures
storage and nothing else. That equality is asserted directly, including on the matrices F4 really
builds.

| backend | storage |
|---|---|
| `Sparse` | sorted-vector rows throughout. The M15 implementation, unchanged. |
| `Dense` | `DenseRows`: the whole matrix densified, eliminated, sparsified again. |
| `Adaptive` | `DenseAccumulator`: sparse pivots, and the row being reduced scattered into a dense buffer that is reused across the elimination. |

**`Adaptive` wins everywhere; `Dense` loses everywhere.** The crossover M15 §7.3 went looking for
does not exist in the range F4 produces, and the reason is not that these matrices are too sparse
for a dense representation to help at the margin — it is that nothing in them is dense at all, at
any granularity. The win that *is* available comes from a mixed representation, not a dense one.

Every wall-clock figure below was taken while three sibling workstreams were building on the same
64-core machine, so absolute times run a few percent above §6.2's. Every ratio is taken within one
session against a baseline measured in that session, which is what the contention does not move.
§7.4.6 reports the same comparison through Criterion, twice, as the stability check.

#### 7.4.1 The confound M15 §7.3 could not remove

M15 compared sparse row echelon against `gauss_jordan_elimination`, which computes the *reduced*
form — a second back-substitution pass the sparse side never performs — and correctly refused to
draw a conclusion from it. `DenseRows` removes the confound: the same pivot rule, the same
first-row-to-reach-it choice, the same unit-pivot normalization, one inverse per pivot and not one
per eliminated entry, the same statistics. `benches/sparse_linear_algebra.rs` keeps the old group
for continuity and adds `matched_echelon`, which is the comparison that can be read.

Conversion is reported apart from the algorithm throughout, because densifying a matrix is real
cost but it is not elimination. `f4_stages/conversion` and `matched_echelon/*/conversion` time it
on its own.

One asymmetry cannot be removed, so it is stated instead: **the entry budget does not bound a dense
backend's memory.** Every backend counts a nonzero the same way — a field element that is not
zero — so `peak_nonzeros` and `max_live_nonzeros` mean the same thing under all three, and the
budget is tested after every row operation under all three, with `Dense` additionally refusing
before it densifies anything. But `DenseRows` allocates `num_rows * num_columns` cells whatever the
budget says: katsura-7 grevlex's largest matrix is 6810 x 6862, which is 374 MB of field elements
to hold 112 200 entries. The budget bounds entries, not bytes, and a dense representation's bytes
are a property of the shape alone.

#### 7.4.2 Nothing in an F4 matrix is dense — not globally, not per row, not per block

From `cargo run --release --example elimination_density`. Row density is a row's nonzeros over the
matrix width; the percentiles are over every row of every matrix of the instance.

| instance | matrices | largest rows x cols | global density | row density p50 | p90 | p99 | max |
|---|---|---|---|---|---|---|---|
| cyclic-4 lex | 12 | 28 x 28 | 18.70% | 19.05% | 30.00% | 57.14% | 57.14% |
| cyclic-5 grevlex | 22 | 624 x 463 | 3.84% | 2.94% | 9.54% | 24.58% | 57.81% |
| katsura-5 lex | 29 | 381 x 249 | 9.45% | 9.81% | 16.48% | 29.41% | 32.31% |
| katsura-5 grevlex | 6 | 278 x 291 | 4.99% | 4.35% | 17.18% | 25.49% | 28.57% |
| katsura-6 lex | 59 | 1954 x 945 | 4.65% | 4.66% | 7.80% | 15.00% | 32.12% |
| katsura-6 grlex | 9 | 644 x 674 | 4.75% | 4.47% | 11.65% | 18.71% | 25.00% |
| katsura-6 grevlex | 8 | 1388 x 1410 | 1.28% | 0.65% | 5.05% | 20.13% | 25.00% |
| katsura-7 grevlex | 10 | 6810 x 6862 | 0.41% | 0.13% | 1.40% | 14.41% | 22.22% |

Density *as built* is not the whole question, though: elimination is what fills a matrix in, and
M15's 13.58x is a fill-in ratio. The quantity a per-row representation switch would actually have
to predict is **each row's own peak nonzero count during its reduction**, which no counter in
`EliminationStatistics` reports — `peak_nonzeros` is a total over the whole matrix, and a matrix
total cannot distinguish a thousand rows that doubled from one row that became full. The example
instruments the elimination to record it, on each instance's largest matrix.

| instance | rows x cols | built | peak | final | row peak density p50 | p90 | p99 | max | rows over 50% |
|---|---|---|---|---|---|---|---|---|---|
| cyclic-4 lex | 28 x 28 | 108 | 120 | 105 | 14.29% | 21.43% | 35.71% | 35.71% | 0 of 28 |
| cyclic-5 grevlex | 624 x 463 | 7 505 | 16 603 | 16 457 | 10.58% | 24.19% | 28.29% | 28.73% | 0 of 624 |
| katsura-5 lex | 381 x 249 | 6 069 | 9 285 | 9 190 | 12.85% | 28.92% | 42.57% | 42.97% | 0 of 381 |
| katsura-5 grevlex | 278 x 291 | 2 637 | 7 818 | 7 795 | 4.47% | 27.49% | 32.99% | 36.08% | 0 of 278 |
| katsura-6 lex | 1954 x 945 | 64 756 | 96 126 | 95 735 | 9.10% | 21.48% | 35.98% | 45.61% | 0 of 1954 |
| katsura-6 grlex | 644 x 674 | 15 074 | 17 002 | 16 968 | 3.86% | 7.42% | 17.66% | 22.26% | 0 of 644 |
| katsura-6 grevlex | 1388 x 1410 | 16 770 | 103 314 | 103 204 | 0.50% | 25.96% | 35.18% | 36.45% | 0 of 1388 |
| katsura-7 grevlex | 6810 x 6862 | 112 200 | 704 771 | 704 608 | 0.10% | 1.63% | 23.05% | 29.89% | 0 of 6810 |

And the quantity a *block* policy would read, on the same matrices, over 64 x 64 blocks:

| instance | blocks | densest | p99 | p90 | median | over 10% | over 50% |
|---|---|---|---|---|---|---|---|
| cyclic-5 grevlex | 80 | 13.53% | 9.23% | 7.69% | 1.20% | 1 | 0 |
| katsura-5 lex | 24 | 28.18% | 28.18% | 15.19% | 4.39% | 4 | 0 |
| katsura-5 grevlex | 25 | 19.74% | 19.74% | 8.52% | 1.35% | 1 | 0 |
| katsura-6 lex | 465 | 46.62% | 26.76% | 11.48% | 0.39% | 63 | 0 |
| katsura-6 grlex | 121 | 30.15% | 25.14% | 11.89% | 0.00% | 21 | 0 |
| katsura-6 grevlex | 506 | 19.90% | 9.89% | 2.39% | 0.00% | 5 | 0 |
| katsura-7 grevlex | 11 556 | 24.73% | 5.81% | 0.29% | 0.00% | 39 | 0 |

**Three readings, and all three matter.**

*The fill-in is real, and it is not densification.* katsura-6 grevlex goes from 16 770 live entries
to 103 314 — 6.2x — and katsura-7 grevlex from 112 200 to 704 771, 6.3x. These matrices really do
get much fuller. They also stay below 37% in the densest row of either and below 25% in the densest
64 x 64 block. M15's 13.58x is a ratio of entry counts, and §5.4's warning that it is not evidence
of density is confirmed: it is evidence of growth from a very low base.

*Global density is the wrong quantity, exactly as §5.4 predicted.* katsura-7 grevlex is 0.41% dense
as a matrix and holds rows at 22% as built and 30% at peak — a factor of 70 between the two
numbers. A policy reading the matrix would read 0.41% and conclude "very sparse" about a matrix
whose worst rows are seventy times that.

*But the right quantity does not supply a threshold either.* Over 155 matrices, and over all
12 107 rows of the eight instrumented ones, **not one row ever exceeds 50% occupancy at its own
peak and not one of the 12 777 64 x 64 blocks exceeds 50%.** The maxima are 45.61% (a row of
katsura-6 lex) and 46.62% (a block of katsura-6 lex); only that instance reaches 40% in either.
A density-keyed policy, on whichever density it read, would never fire — and a threshold set low
enough to fire would fire on matrices where `Dense` loses, which §7.4.3 shows is all of them.

**Density-keyed per-row switching, density-aware pivoting, and dense treatment of selected blocks
are therefore rejected on this measurement, before being implemented.** The two numbers that reject
them are "0 of 12 107 rows over 50%" and "0 of 12 777 blocks over 50%". Two rows *as built* do
exceed 50% — a 16-of-28 row of cyclic-4 lex and one row of a small early cyclic-5 grevlex matrix —
and both are on matrices where `Dense` is slower anyway.

#### 7.4.3 Sparse against dense, matched contract, conversion separated

Same run. Every matrix of an instance eliminated once, summed over the instance. `dense (alg)` is
the dense backend's time with its conversions subtracted out; `conv` is densify-plus-sparsify
measured on its own. Milliseconds.

| instance | sparse | dense (alg) | conv | dense (total) | dense/sparse | adaptive | sparse/adaptive |
|---|---|---|---|---|---|---|---|
| cyclic-4 lex | 0.05 | 0.06 | 0.01 | 0.07 | 1.25x | 0.05 | 1.07x |
| katsura-5 grevlex | 0.73 | 0.80 | 0.10 | 0.90 | 1.25x | 0.55 | 1.33x |
| katsura-5 lex | 6.64 | 7.79 | 0.58 | 8.37 | 1.26x | 5.14 | 1.29x |
| katsura-6 grlex | 14.76 | 22.39 | 1.42 | 23.81 | 1.61x | 8.82 | 1.67x |
| cyclic-5 grevlex | 15.80 | 26.55 | 1.25 | 27.80 | 1.76x | 10.67 | 1.48x |
| katsura-6 grevlex | 20.00 | 44.06 | 2.40 | 46.46 | 2.32x | 12.25 | 1.63x |
| katsura-6 lex | 384.85 | 580.99 | 16.77 | 597.76 | 1.55x | 230.41 | 1.67x |
| katsura-7 grevlex | 745.87 | 1299.62 | 486.13 | 1785.75 | 2.39x | 363.15 | **2.05x** |

**There is no crossover.** `Dense` is slower than `Sparse` on every instance — 1.25x to 2.39x on
total time — and it is *still* slower on every instance when conversion is subtracted out
entirely: 1.10x to 2.20x on algorithm alone. Removing the conversion does not change the
conclusion, which is the point of separating it. The dense representation loses on the algorithm,
not on the plumbing.

And the ratio **rises** with size rather than falling toward a crossover: 1.20x on a 28 x 28
matrix, 1.52x at 644 x 674, 2.20x at 1388 x 1410, 1.74x at 6810 x 6862 (algorithm only). The reason
is structural: a dense row operation costs the matrix's whole width whatever the pivot's support
is, and the pivots' support is 0.1% to 20% of the width. Widening the matrix makes that worse, not
better. A crossover would require rows at a large fraction of the width, and §7.4.2 says there are
none.

Conversion is 3% to 14% of the dense total on seven of the eight instances, and **27%** on
katsura-7 grevlex, where zeroing a 46.7-million-cell buffer to hold 112 200 entries is a quarter of
what the backend does. That is the measurement the separation was for: it is large, it is real, and
it is not what decides the comparison.

This closes M15's open question: **no sparse/dense crossover exists in the range F4 produces.**
`Backend::Dense` stays because it is the control the other two are measured against, and because "a
dense backend that loses everywhere" is exactly the deliverable §5.4 asked for.

#### 7.4.4 What does pay: a dense accumulator over sparse pivots

The sparse inner operation is a sorted merge of two rows into a scratch buffer. It allocates
nothing per operation, but it reads and rewrites *every* entry of the row being reduced however few
entries the pivot has, and swaps the result back. With pivot supports at 0.1% to 20% of the width
and rows that grow sixfold during their own reduction, that is the wrong cost in the one place it
is paid most often.

`DenseAccumulator` scatters the row into a dense buffer once, applies every pivot in time
proportional to the *pivot's* support, and gathers the row back once. The matrix stays sparse, so
the cost is one buffer of `num_columns` cells for the whole elimination rather than
`num_rows * num_columns` — 55 KB on katsura-7 grevlex against 374 MB. This is the "dense temporary
row accumulator" of §5.4, and it is the strategy that pays: 1.29x to 2.05x on every instance above
a millisecond, best on the largest.

Two details that are part of the measurement rather than extra:

- **Buffer reuse.** The accumulator is allocated once per elimination, and the gather clears only
  the span it touched, so a row operation allocates nothing and a row costs one clear of its own
  span rather than of the width. The remaining per-elimination allocation is the buffer, one row
  wide.
- **No zero test in the inner loop.** A field has no zero divisors and a sparse row stores no zero
  coefficient, so `factor * coefficient` is never zero and the test for it is dead. Removing it is
  3.4% on katsura-6 grevlex, 7.6% on katsura-6 grlex and 10.2% on katsura-5 lex, as a Criterion
  A/B against the version that kept the test (`p < 0.05` on all three).

It is **not** keyed on a density, and §7.4.2 is why: there is no threshold to key on. "Adaptive"
names a choice of representation per *role* — pivot or work — not per matrix and not per measured
density. That the policy is unconditional is also what makes determinism free: there is no observed
quantity for a choice to depend on.

#### 7.4.5 Effect on the elimination stage, per system and order

From `cargo run --release --example f4_profile -- baseline | d | d-dense`, one session so the three
columns are comparable to each other. Milliseconds.

| system | order | elim sparse | elim adaptive | speedup | elim dense | total sparse | total adaptive |
|---|---|---|---|---|---|---|---|
| cyclic-4 | lex | 0.10 | 0.05 | 2.00x | 0.10 | 0.41 | 0.25 |
| cyclic-4 | grlex | 0.04 | 0.04 | 1.00x | 0.07 | 0.18 | 0.18 |
| cyclic-4 | grevlex | 0.05 | 0.04 | 1.25x | 0.06 | 0.19 | 0.19 |
| cyclic-5 | lex | 14.41 | 8.71 | 1.65x | 23.52 | 29.06 | 23.20 |
| cyclic-5 | grlex | 14.72 | 7.90 | 1.86x | 18.39 | 21.88 | 14.40 |
| cyclic-5 | grevlex | 17.45 | 9.68 | 1.80x | 25.79 | 23.77 | 15.37 |
| katsura-4 | lex | 0.23 | 0.17 | 1.35x | 0.26 | 0.64 | 0.51 |
| katsura-4 | grlex | 0.08 | 0.07 | 1.14x | 0.09 | 0.28 | 0.24 |
| katsura-4 | grevlex | 0.06 | 0.04 | 1.50x | 0.06 | 0.20 | 0.17 |
| katsura-5 | lex | 6.59 | 4.28 | 1.54x | 8.03 | 15.25 | 11.79 |
| katsura-5 | grlex | 0.75 | 0.48 | 1.56x | 0.85 | 1.95 | 1.63 |
| katsura-5 | grevlex | 0.74 | 0.51 | 1.45x | 0.95 | 1.88 | 1.58 |
| katsura-6 | lex | 380.09 | 222.25 | **1.71x** | 673.28 | 3075.79 | 2898.44 |
| katsura-6 | grlex | 13.49 | 8.63 | **1.56x** | 20.63 | 22.50 | 18.36 |
| katsura-6 | grevlex | 19.28 | 12.11 | **1.59x** | 43.33 | 29.02 | 22.14 |
| katsura-7 | grlex | 434.37 | 240.08 | **1.81x** | 787.42 | 536.15 | 340.96 |
| katsura-7 | grevlex | 767.45 | 369.33 | **2.08x** | 1822.17 | 883.47 | 482.71 |
| random-4 | lex | 4.27 | 3.09 | 1.38x | 5.22 | 8.93 | 7.42 |
| random-4 | grlex | 0.31 | 0.21 | 1.48x | 0.30 | 0.85 | 0.71 |
| random-4 | grevlex | 0.39 | 0.29 | 1.34x | 0.38 | 0.99 | 0.88 |

**No instance regresses, under any order, in the elimination stage or in the total.** The whole
computation improves by 1.57x on katsura-7 grlex (536.2 to 341.0 ms) and **1.83x on katsura-7
grevlex** (883.5 to 482.7), which is what §6.2 predicted would happen if elimination got faster:
those two instances are 81% and 87% elimination.

The sub-millisecond rows are reported for completeness and should not be read as ratios: cyclic-4
and katsura-4 measure tens of microseconds per stage, where the clock reads and the first batch's
warm-up are a visible share. Every ratio this workstream claims is from an instance above a
millisecond.

katsura-6 lex barely moves — 3075.8 to 2898.4 — for the reason §6.2 found. Its elimination falls
by 42%, but 84% of that instance is `reduce_grobner_basis` (2579.2 ms of 3075.8), which belongs to
M16-C. That is not a failure of this workstream; it is the stage breakdown doing its job.

#### 7.4.6 Criterion, on the matrices F4 builds

From `cargo bench --bench f4_stages -- 'f4_stages/(elimination|conversion)'`, Criterion medians at
sample size 10, every batch of the instance replayed per iteration. An instrument independent of
the example's own timing loop, run twice.

| instance | run | sparse | dense | adaptive | conversion | dense/sparse | sparse/adaptive |
|---|---|---|---|---|---|---|---|
| katsura-6 grevlex | A | 20.83 | 31.29 | 12.04 | 2.26 | 1.50x | 1.73x |
| katsura-6 grevlex | B | 20.29 | 31.59 | 11.99 | 2.31 | 1.56x | 1.69x |
| katsura-6 grlex | A | 15.07 | 19.36 | 8.52 | 1.03 | 1.29x | 1.77x |
| katsura-6 grlex | B | 14.71 | 18.67 | 8.52 | 1.02 | 1.27x | 1.73x |
| katsura-5 lex | A | 6.60 | 8.55 | 4.86 | 0.59 | 1.30x | 1.36x |
| katsura-5 lex | B | 6.65 | 8.48 | 4.89 | 0.65 | 1.28x | 1.36x |
| cyclic-5 grevlex | A | 16.97 | 24.72 | 10.68 | 0.94 | 1.46x | 1.59x |
| cyclic-5 grevlex | B | 16.83 | 24.16 | 10.07 | 0.90 | 1.44x | 1.67x |

Two independent runs of the same code, taken under the same contention. Every median is within 3%
of its pair and every ratio within 5%, so the ordering — `Adaptive` fastest, `Sparse` next, `Dense`
slowest, on all four instances — is not an artifact of one run. The `dense` column here *includes*
its conversions, which the `conversion` column measures separately: subtracting it leaves `Dense`
ahead of `Sparse` on none of the four.

The ratios are smaller than §7.4.3's because Criterion's `iter_batched` clones the matrices per
iteration while the example's loop clones inside its own untimed section; the direction and the
ordering agree, which is what a second instrument is for.

#### 7.4.7 What was rejected, and the number that rejected it

| strategy | verdict | the measurement |
|---|---|---|
| Dense rows throughout | **rejected as a default, kept as the control** | slower than sparse on all 8 instances: 1.25x to 2.39x total, 1.10x to 2.20x with conversion removed; the ratio rises with size |
| Per-row sparse/dense switching keyed on density | **rejected before implementation** | 0 of 12 107 instrumented rows exceeds 50% peak occupancy; the maximum anywhere is 45.61% |
| Dense treatment of selected blocks | **rejected before implementation** | 0 of 12 777 64 x 64 blocks exceeds 50%; the densest anywhere is 46.62% |
| Density-aware pivot strategies | **rejected before implementation** | the same two distributions, and over a finite field there is no stability to pivot for, so this would trade determinism for a threshold that never fires |
| Any policy keyed on *global* density | **rejected as keyed on the wrong quantity** | katsura-7 grevlex is 0.41% dense and holds rows at 29.89% peak occupancy — a factor of 70 |
| Dense temporary row accumulator | **accepted** | 1.29x to 2.05x over sparse on real matrices, best on the largest; no regression on any instance or order |
| Buffer reuse | **accepted, inside the above** | one buffer per elimination, cleared over the touched span only; a row operation allocates nothing |

#### 7.4.8 Correctness

- Every backend produces the identical matrix and the identical `EliminationStatistics` on
  rectangular, square, singular, rank-one, sparse, dense, fill-in-heavy and degenerate shapes, over
  GF(7), GF(13), GF(541), GF(2^31 - 1) and GF(2^64 - 59)
  (`test_every_backend_agrees_on_every_shape_and_field`).
- Rank agrees with `Matrix::rank`, which is independently checked against Sage. The row space is
  certified per backend by an augmented identity block carrying the combination of original rows
  that produced each reduced row (`test_every_backend_preserves_the_row_space`).
- `reduce_rows_against_pivots_with` honours its contract under every backend at `split = 0`,
  `split = num_rows / 2` and `split = num_rows`, over all five fields: upper rows untouched, lower
  rows reduced and normalized, result equal to a full echelon of the same arrangement
  (`test_every_backend_honours_the_split_contract`). Its preconditions are now validated once in
  the interface instead of once per backend, so there is a single copy of them to keep right, and
  every backend rejects a malformed upper block
  (`test_every_backend_rejects_a_malformed_upper_block`).
- Each backend is deterministic over eight repetitions, and `Adaptive` agrees with both fixed
  backends (`test_every_backend_is_deterministic`).
- The budget refuses work mid-elimination under every backend, reporting a count above the budget,
  and a budget set at the peak behaves exactly as an unbounded run
  (`test_the_budget_is_enforced_mid_elimination`).
- `f4` returns the identical basis under every backend over the whole correctness corpus and all
  three orders, and on katsura-5 and cyclic-4 over all three
  (`test_elimination_backend_does_not_change_the_basis`,
  `test_every_backend_agrees_on_the_benchmark_systems`).
- Every backend reports the identical statistics on the Macaulay matrices of real katsura-5 runs,
  all three orders (`test_every_backend_reports_the_same_elimination_statistics`), which is what
  makes `max_live_nonzeros` mean one thing rather than three.

Both frozen signatures are unchanged and `reduce_rows_against_pivots_with`'s documented contract is
unchanged, so **no interface change is requested**. No file outside `src/linalg/**` was modified
except by appending to `src/grobner/f4/tests.rs`, `benches/**`, `examples/**`, `README.md` and this
section. `F4Options::default()` still names the baseline: making `Adaptive` the default is M16-I's
decision, and the number it needs is in §7.4.5.

## 8. Integration and the combined result

Integrated on `feat/m16-integration`, in the order D, B, A, C — least coupled first, with the full
correctness corpus run after each step. Conflicts were confined to three shared append-only files
(`README.md`, `src/grobner/f4/tests.rs`, and §7 of this document) and were resolved centrally by
reconstructing each file from the merge base plus each side's additions, which is sound because
every workstream only appended.

Test counts after each step, `cargo test --release`, in an isolated target directory: D 718,
B 736, A 753, C 754. Plus both `#[ignore]`d engine-agreement tests, which take 119 s and confirm
F4 still returns exactly what the naive textbook reference returns.

### 8.1 The three option-gated optimizations compose

`cargo run --release --example f4_ablation`. Speedup against this build's `F4Options::baseline()`,
each figure the fastest of several runs.

| configuration | cyc-4 lex | cyc-5 lex | cyc-5 grev | kat-5 lex | kat-5 grev | kat-6 grlex | kat-6 grev | kat-6 lex | kat-7 grlex | kat-7 grev |
|---|---|---|---|---|---|---|---|---|---|---|
| baseline | 1.00x | 1.00x | 1.00x | 1.00x | 1.00x | 1.00x | 1.00x | 1.00x | 1.00x | 1.00x |
| A | 1.21x | 1.07x | 1.34x | 1.24x | 1.51x | 1.00x | 1.94x | 1.37x | 0.96x | 2.61x |
| b-rejected | 1.12x | 1.08x | 0.47x | 0.96x | 0.70x | 0.64x | 0.45x | 0.95x | 0.44x | 0.31x |
| C | 2.36x | 7.85x | 13.75x | 13.81x | 1.92x | 3.95x | 4.30x | 25.20x | 8.25x | 8.90x |
| D | 1.16x | 1.60x | 1.62x | 1.24x | 1.17x | 1.54x | 1.51x | 1.60x | 1.83x | 2.09x |
| d-dense | 1.06x | 0.89x | 0.85x | 0.90x | 0.92x | 0.90x | 0.73x | 0.70x | 0.68x | 0.48x |
| A+C | 2.86x | 8.54x | 14.68x | 14.36x | 2.49x | 4.67x | 5.90x | 30.27x | 9.04x | 17.82x |
| A+D | 1.35x | 1.82x | 2.43x | 1.68x | 1.77x | 1.83x | 3.87x | 2.63x | 2.44x | 8.68x |
| C+D | 2.44x | 8.26x | 15.66x | 14.37x | 2.13x | 4.50x | 5.46x | 28.56x | 9.51x | 12.47x |
| **A+C+D** | **3.05x** | **9.30x** | **17.23x** | 14.35x | **2.87x** | **5.49x** | **7.43x** | 30.81x | **12.79x** | **27.18x** |
| A+b-rej+C+D | 2.96x | 9.42x | 12.91x | 14.95x | 2.02x | 5.33x | 4.61x | 31.51x | 10.86x | 16.01x |

**A+C+D is the fastest configuration on every instance**, and it exceeds every pair it contains.
§7 of this plan predicted the opposite for one of the three interactions — that stronger pair
criteria would eliminate the matrices structured elimination had been built to optimize. They do
not conflict, because they act on different things: **C removes matrices, A makes each surviving
matrix cheaper.** On katsura-7 grevlex, C alone is 8.90x and A alone 2.61x; A+C is 17.82x, which is
*more* than their product would suggest, because A's sparser candidates also shrink the matrices C
leaves behind.

The other two predicted interactions were real but benign. A+D (8.68x on katsura-7 grevlex) is
better than either alone despite A reducing peak live entries 22-fold — so a sparser matrix does
not leave the dense accumulator with nothing to win, because the accumulator's advantage is in
merge length per row operation rather than in density. And `d-dense` loses on nine of ten
instances, which is the same conclusion §7.4 reached in isolation.

**Two rows are not candidates.** `b-rejected` is M16-B's two optional strategies, kept so the
rejection is reproducible: it is 0.31x to 0.47x on the grevlex instances and marginally positive on
three lex ones. `A+b-rej+C+D` shows what including them would have cost — 16.01x instead of 27.18x
on katsura-7 grevlex, about 40% of the win. It is marginally ahead on three lex instances
(31.51x against 30.81x on katsura-6 lex), which is within run-to-run variation and does not survive
as a recommendation.

**One thing the ablation cannot measure, and saying so is part of the result.** Two of M16's
improvements are not option-gated: M16-B's cheaper monomial hash in symbolic preprocessing and
M16-C's rewritten interreduction are unconditional, so they are inside *every* row above including
the baseline. That is why this baseline's katsura-6 lex figure is around 500 ms where §6.2's was
2963 ms. The ablation measures what the options contribute; §8.2 measures what the milestone
contributed.

### 8.2 M16-0 against the recommended configuration

Both sides measured in the same session on an otherwise idle machine, both with
`measure_stages: true` so the instrumentation overhead is common. The M16-0 side is
`examples/f4_profile` built from `feat/m16-foundation` at `7f0b446`; the M16 side is the same
example at `recommended`. Milliseconds.

| system | order | M16-0 | M16 recommended | speedup |
|---|---|---|---|---|
| cyclic-4 | lex | 0.33 | 0.17 | 1.9x |
| cyclic-4 | grlex | 0.18 | 0.10 | 1.8x |
| cyclic-4 | grevlex | 0.19 | 0.09 | 2.1x |
| cyclic-5 | lex | 29.31 | 3.14 | 9.3x |
| cyclic-5 | grlex | 22.21 | 1.81 | 12.3x |
| cyclic-5 | grevlex | 25.39 | 1.70 | 14.9x |
| katsura-4 | lex | 0.75 | 0.14 | 5.4x |
| katsura-4 | grlex | 0.34 | 0.12 | 2.8x |
| katsura-4 | grevlex | 0.32 | 0.12 | 2.7x |
| katsura-5 | lex | 15.19 | 0.88 | 17.3x |
| katsura-5 | grlex | 1.94 | 0.65 | 3.0x |
| katsura-5 | grevlex | 2.30 | 0.62 | 3.7x |
| katsura-6 | lex | 2986.57 | 19.53 | **152.9x** |
| katsura-6 | grlex | 24.64 | 4.40 | 5.6x |
| katsura-6 | grevlex | 27.32 | 3.77 | 7.2x |
| katsura-7 | grlex | 522.22 | 46.72 | 11.2x |
| katsura-7 | grevlex | 853.10 | 32.13 | **26.6x** |
| random-4 | lex | 7.98 | 0.79 | 10.1x |
| random-4 | grlex | 0.73 | 0.33 | 2.2x |
| random-4 | grevlex | 0.86 | 0.34 | 2.5x |
| planted-6 | lex | 0.06 | 0.05 | 1.2x |

**Every instance improved**, by between 1.2x and 152.9x. The smallest gains are on the instances
that were already sub-millisecond, where fixed costs dominate and there is nothing to amortise.

### 8.3 The headline target, and the order inversion

`cargo run --release --example f4_milestone`, both engines on identical inputs in one process, with
the basis asserted equal between them wherever both can run. Milliseconds, fastest of several runs.

| system | order | Buchberger | F4 baseline | F4 recommended | vs Buchberger | M15's figure |
|---|---|---|---|---|---|---|
| cyclic-4 | lex | 0.16 | 0.16 | **0.06** | 2.72x | 1.05x |
| cyclic-4 | grlex | 0.13 | 0.11 | **0.04** | 3.11x | 1.17x |
| cyclic-4 | grevlex | 0.14 | 0.12 | **0.06** | 2.37x | 1.02x |
| cyclic-5 | lex | 45.91 | 19.37 | **2.28** | 20.10x | 1.97x |
| cyclic-5 | grlex | 56.50 | 19.08 | **1.51** | 37.44x | 3.03x |
| cyclic-5 | grevlex | 32.47 | 22.01 | **1.31** | 24.72x | 1.69x |
| katsura-5 | lex | 162.07 | 12.37 | **0.84** | 193.23x | 12.96x |
| katsura-5 | grlex | 2.08 | 1.71 | **0.62** | 3.38x | 1.29x |
| katsura-5 | grevlex | 1.11 | 1.68 | **0.61** | 1.83x | **0.72x** |
| katsura-6 | grlex | 34.55 | 21.89 | **4.02** | 8.59x | 1.67x |
| katsura-6 | grevlex | 14.10 | 29.75 | **3.26** | **4.32x** | **0.47x** |
| katsura-6 | lex | — | 495.48 | **18.34** | — | — |
| katsura-7 | grlex | — | 568.10 | **40.31** | — | — |
| katsura-7 | grevlex | — | 932.32 | **32.82** | — | — |
| planted-6 | lex | 0.05 | 0.04 | **0.03** | 1.57x | 1.18x |
| planted-6 | grlex | 0.03 | 0.03 | **0.03** | 1.19x | 1.07x |
| planted-6 | grevlex | 0.03 | 0.03 | **0.03** | 1.17x | 1.08x |

**F4 is now faster than classical Buchberger on every instance under every order.** The preceding
milestone lost on five of thirteen paired instances; the count is now zero.

The milestone's named target was katsura-6 under grevlex, where M15 recorded **0.47x** — F4 at
30.2 ms against Buchberger's 14.1 ms, the worst paired result in that report. It is now **4.32x**,
a relative improvement of 9.2x. The accompanying claim in M15 §7.2 — that "grevlex is the cheapest
order for Buchberger and, at these sizes, the *worst* order for this F4 implementation" — no longer
holds: grevlex is now F4's **best** order on katsura-6 (3.26 ms against grlex's 4.02) and on
katsura-7 (32.82 against 40.31). The inversion that report called "a direct consequence of the
fill-in" went away when the fill-in did.

### 8.4 Fill-in and memory

Peak live nonzero entries, which is the quantity `max_live_nonzeros` is enforced on and therefore
the one that decides whether a computation fits.

| system | order | M16-0 peak | M16 peak | reduction | M16-0 worst fill-in |
|---|---|---|---|---|---|
| cyclic-5 | grevlex | 17 061 | 1 206 | 14.1x | 3.58x |
| katsura-5 | grevlex | 7 818 | 1 259 | 6.2x | 2.96x |
| katsura-6 | grlex | 34 746 | 6 344 | 5.5x | 2.45x |
| katsura-6 | grevlex | 103 314 | 6 014 | 17.2x | 6.56x |
| katsura-6 | lex | 151 624 | 5 623 | 27.0x | 4.91x |
| katsura-7 | grlex | 368 156 | 33 508 | 11.0x | 3.78x |
| katsura-7 | grevlex | **1 390 812** | **27 356** | **50.8x** | **13.58x** |

M15 §7.3 called katsura-7 grevlex's growth "the clearest single cost in the whole milestone". A
50.8x reduction in peak live entries answers it, and it is the result with the most consequence
for the milestone's central criterion: what Zeebra can solve within a memory budget, not only how
fast it solves what it already could.

Two mechanisms, and they are separable. Structured elimination alone takes the peak from 1 390 812
to 63 087 by never filling in the reducer block (§7.1). The pair criteria then remove most of the
matrices entirely, taking the largest from 6810 rows to 1262 (§7.3). Neither subsumes the other.

### 8.5 Where the time goes now

`examples/f4_profile recommended`, milliseconds.

| system | order | total | symbolic | construction | elimination | extraction | interreduction |
|---|---|---|---|---|---|---|---|
| cyclic-5 | lex | 3.14 | 0.65 | **1.48** | 0.37 | 0.09 | 0.35 |
| katsura-5 | lex | 0.88 | 0.12 | **0.35** | 0.09 | 0.06 | 0.17 |
| katsura-6 | lex | 19.53 | 4.42 | **9.33** | 1.28 | 0.99 | 2.33 |
| katsura-6 | grlex | 4.40 | 0.30 | 1.11 | 0.77 | 0.11 | **1.98** |
| katsura-6 | grevlex | 3.77 | 0.31 | 1.14 | 0.80 | 0.08 | **1.33** |
| katsura-7 | grlex | 46.72 | 2.58 | 6.21 | 8.00 | 0.63 | **28.71** |
| katsura-7 | grevlex | 32.13 | 1.64 | 5.53 | 7.12 | 0.40 | **16.90** |

**The bottleneck has moved twice, and is now in two places neither of which M16 targeted.**

At M16-0, elimination was 65–88% of every instance above a millisecond. It is now 17% of
katsura-7 grlex and 7% of katsura-6 lex. The two optimizations aimed at it worked well enough to
stop it being the problem.

What is left:

- **Interreduction, again**, on the instances with large bases: 28.71 ms of katsura-7 grlex's
  46.72 (61%) and 16.90 of katsura-7 grevlex's 32.13 (53%). M16-C took it from 2479 ms to 1.04 ms
  on katsura-6 lex, where the basis has six elements. katsura-7 grlex returns **64** elements, so
  the quadratic term in the basis size is no longer negligible, and the work is genuine rather
  than wasted. It is the largest remaining cost in the milestone.
- **Matrix construction**, on the lex instances: 9.33 ms of katsura-6 lex's 19.53 (48%) and 1.48 of
  cyclic-5 lex's 3.14 (47%). This was never a target — at M16-0 it was 70 ms of 2987, 2% — and it
  is now the largest stage there, because the pair criteria replaced 59 large matrices with 107
  small ones and construction's per-matrix cost (the monomial-to-column `HashMap`, the sort) does
  not shrink with the matrix.

Both are consequences of succeeding elsewhere, which is the normal shape of a performance
milestone and the reason the stage breakdown was built in M16-0 rather than inferred at the end.

### 8.6 Correctness

The seven requirements from §7 of the plan, and how each is established:

| Requirement | How |
|---|---|
| Every input generator reduces to zero modulo the result | Asserted over the corpus; plus an independent driver asserting it directly for every criterion combination on 11 systems and 50 randomized systems |
| Every S-polynomial of the returned basis reduces to zero | Buchberger's criterion, asserted the same way — the engine-independent check, which is the only one that can catch an unsound pair criterion |
| The result is monic, reduced, and canonically ordered | Asserted against the definition, not against a known answer |
| The ideal generated by the result equals the input ideal | Exact sequence equality with `buchberger` and `buchberger_reference` wherever both run |
| Results agree with baseline F4 and reference Buchberger | 754 tests in debug and release, including the whole cross product of strategies against the baseline's basis, plus both slow reference-agreement tests |
| Results do not depend on batch size or elimination backend | Asserted for `max_pairs_per_batch` down to 1, and for all three backends over the corpus and the benchmark families |
| Resource-budget failures return explicit errors, never partial results | Five `F4Error` variants, each tested, per backend and per reduction strategy |

Differential coverage: all three monomial orders throughout; GF(7), GF(13), GF(541), GF(2^31 − 1)
and a 64-bit prime; every rotation and reversal of the generator list on three systems; duplicated,
scaled and redundant generators; and 50 randomized systems over small fields.

The criteria needed more than the corpus, because an unsound criterion returns an *incomplete*
basis and two engines sharing the criterion would agree with each other while both being wrong.
That is why the independent check is definitional — Buchberger's criterion on the returned basis —
and why the permutation differential exists: an unsound criterion typically survives a fixed
generator order and fails on a permutation.

### 8.7 What changed in the default

`F4Options::default()` is now `F4Options::recommended()`: structured elimination, all pair
criteria, the dense accumulator. It was identical to `F4Options::baseline()` for the whole
milestone and moved once, at the end, on the evidence in §8.1. `baseline()` remains public so the
measurements here can be reproduced against the configuration they were taken with — a default
that absorbed its own reference would make the comparison impossible to repeat.

`examples/f4_statistics.rs` pins itself to `baseline()` for the same reason: its table's columns
are the ones `MILESTONE-F4.md` §7.1 records, and comparing against them needs that configuration.

### 8.8 Regressions

| Regression | Status |
|---|---|
| Structured elimination alone is 0.96x on katsura-7 grlex and 1.00x on katsura-6 grlex | Real. grlex builds more, sparser matrices, so there is less fill-in to avoid. Not a regression in the recommended configuration, where A+C+D is 12.79x and 5.49x on those instances. |
| `Backend::Dense` is slower than `Backend::Sparse` everywhere | By design. It is the control the comparison needs, and §7.4's negative result is one of the milestone's deliverables. Not selected. |
| `ReducerSelection::LargestLeadingMonomial` and `CacheMode::Store` are slower | Measured and rejected; not selected. Retained so §7.2's rejection is reproducible. |
| `max_live_nonzeros` bounds entries, not bytes, so it does not bound `Backend::Dense`'s allocation | Documented on the variant rather than silently redefining the counter. A byte-aware budget is future work. |
| `batches` and `pairs_reduced` are not comparable between reduction strategies | Inherent: a different row arrangement produces different candidate polynomials and hence different later batches. Documented on `ReductionStrategy::Structured`. |

No correctness regression, and no instance slower under the recommended configuration than under
M16-0.

## 9. Definition of done, and what to do next

Zeebra's F4 is now faster than its classical Buchberger on every instance measured, under every
monomial order, having been slower on five of thirteen at the start of the milestone. The
instances the preceding milestone could not pair at all are 11–27x faster, and the one it named as
the clearest cost in the whole report needs 51x less peak memory. Every optimization is justified
by a measurement taken before it was written, and three were rejected with their evidence
preserved. That is the milestone.

### 9.1 Known limitations

- **Interreduction is the largest remaining cost** on instances with large bases: 61% of
  katsura-7 grlex. The work is genuine, but the algorithm is still quadratic in the basis size.
- **Matrix construction is now the largest stage under lex**, at 48% of katsura-6 lex, because the
  pair criteria replaced few large matrices with many small ones and construction's per-matrix
  overhead does not shrink.
- **Gebauer–Möller subsumes the chain criterion** in F4 — `chain` fires zero times when
  `gebauer_moller` is on. Both are kept because neither dominates in classical Buchberger.
- **No crossover to a dense representation exists** in the range F4 produces, so there is no
  density-switching policy and `Backend::Adaptive` reads no density at all.
- **Still single-threaded**, in both construction and elimination, on a 64-core machine.
- **No 128-bit field measurement**, unchanged from M15.
- **`solve` still uses `buchberger`.** F4 is now the faster engine on every instance including the
  small ones `solve` produces, so this should change — but `f4` returns a `Result` and `solve` does
  not, and that is an API change rather than a performance one.
- **`N` is still a const generic.**

### 9.2 Recommendations for the next milestone, in the order the measurements support

1. **Interreduction.** 61% of katsura-7 grlex, and the only remaining bottleneck that is large on
   the hardest tractable instances. Likely a better algorithm than reduce-each-against-the-rest,
   not a constant-factor fix.
2. **Matrix construction.** 48% of katsura-6 lex. The monomial-to-column map and the column sort
   are per-matrix costs paid 107 times where they used to be paid 59, and the column set of one
   batch overlaps the next. Interning monomials — which M16-B investigated and did not need for
   hashing — would be the natural approach, and this is where it would pay.
3. **Switch `solve` to F4**, with whatever error handling the public API should have. F4 is now
   faster on every instance, so the only question left is the signature.
4. **FGLM**, which M15 deferred and which is the natural next capability rather than an
   optimization: it converts a cheap grevlex basis into the lex basis solving needs, and grevlex is
   now F4's *best* order rather than its worst, which makes the conversion more attractive than it
   was.
5. **Multithreaded elimination.** The machine has 64 cores and the implementation uses one. Worth
   less than it looks now that elimination is 7–17% of the total rather than 65–88% — which is
   itself a result: M15 ranked this fifth and the ranking has not changed, but the ceiling has
   dropped.
6. **Specialized arithmetic for large prime fields**, for the 128-bit and eventually 255-bit
   support the longer-term workloads need.


## 10. References

1. Faugère, J.-C. (1999). *A new efficient algorithm for computing Gröbner bases (F4)*. Journal of
   Pure and Applied Algebra 139, 61–88. <https://doi.org/10.1016/S0022-4049(99)00005-5>
2. Gebauer, R., Möller, H. M. (1988). *On an installation of Buchberger's algorithm*. Journal of
   Symbolic Computation 6, 275–286. <https://doi.org/10.1016/S0747-7171(88)80048-8>
3. Buchberger, B. (1979). *A criterion for detecting unnecessary reductions in the construction of
   Gröbner bases*. EUROSAM '79, LNCS 72, 3–21.
4. Cox, D., Little, J., O'Shea, D. *Ideals, Varieties, and Algorithms*, Sec. 2.9–2.10, for the
   product and chain criteria and their soundness proofs.
5. Faugère, J.-C., Lachartre, S. (2010). *Parallel Gaussian elimination for Gröbner bases
   computations in finite fields*. PASCO '10, 89–97, for the block structure of a Macaulay matrix.
6. Demin, A., Gowda, S. *Groebner.jl*. <https://arxiv.org/abs/2304.06935>, and
   <https://github.com/sumiya11/Groebner.jl> for implementation architecture.
7. msolve — <https://github.com/algebraic-solving/msolve>, a mature F4 implementation.
8. The preceding milestone: [`MILESTONE-F4.md`](MILESTONE-F4.md).

Published algorithm descriptions are the primary references. Existing implementations are read for
architecture and performance strategy, under their own licenses; no code is copied.
