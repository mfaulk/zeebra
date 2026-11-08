# Wiedemann and Krylov methods: won't-do for F4, superseded deferral for FGLM

Decision record for [#58](https://github.com/mfaulk/zeebra/issues/58), in the style of
`docs/research/elimination-beyond-grobner.md`. It exists because black-box linear algebra is the
obvious thing to propose at every milestone and **the answer is different for the two places this
crate runs Gaussian elimination** — so the question needs answering once, with the measurements
attached, rather than re-derived from complexity formulas each time.

**The two conclusions, up front:**

| site | conclusion | where the live work is |
|---|---|---|
| F4 echelonization | **Won't do.** It computes the wrong object, and the arithmetic agrees even granting that it applied. Do not reopen. | nothing open on the algorithm; see §1.4 for what has actually moved this stage |
| FGLM order conversion | Deferred in M18 on measurements that still stand; the deferral has since been **reopened on new evidence**. | [#368](https://github.com/mfaulk/zeebra/issues/368) (M26-B, staged), [#224](https://github.com/mfaulk/zeebra/issues/224) (D5, the alternatives survey) |

Pinned to `30348938`. Every figure below was re-read out of the document cited beside it while
writing this record; §6 is the audit, including the four citations in #58's body that **no longer
hold as written**. Nothing here is newly measured and nothing is re-derived.

---

## 1. F4 elimination — won't do

Not "slower". **It computes the wrong object**, and that is the whole argument; the cost comparison
in §1.1 is corroboration, not the reason.

Wiedemann is a black-box method for a *solve*: given a fixed sparse operator `A`, find `x` with
`A x = b`, or find the minimal polynomial of `A`. F4's echelonization is not a solve.

- **The output is the transformed matrix.** The new basis polynomials are read off the reduced rows
  by leading monomial — `MacaulayMatrix::sparse_row_polynomial` in `src/grobner/f4/macaulay.rs`.
  There is no vector to solve for.
- **The matrices are rectangular and deliberately rank-deficient.** The rank defect *is* the
  answer: a row whose leading monomial is not new contributes nothing to the basis.
- **The operator is destroyed by the computation**, so the black-box model does not apply at all.
  One Wiedemann solve per output row, at `O(n)` matvecs each, is strictly worse than one
  elimination.

### 1.1 The arithmetic agrees, even granting it applied

katsura-7 grevlex's largest matrix is 6810 x 6862 holding 112 200 entries
(`docs/MILESTONE-F4-OPTIMIZATION.md` §7.4.1). Wiedemann needs about `2n` matvecs, so on that one
matrix: `2 * 6810 * 112 200 ~= 1.5e9` field operations.

All ten of that instance's eliminations together take **791.81 ms** (§6.2 — elimination is 791.81 of
the 896.32 ms total, and §7.4.2 records that the instance builds ten matrices). At any plausible
rate for a 64-bit prime field the matvec budget for *one* matrix exceeds the measured elimination
for *all ten*.

### 1.2 The premise Wiedemann exists to defeat is absent

Wiedemann's reason for existing is fill-in that would make elimination infeasible. M15 measured
13.58x worst-case fill-in on katsura-7 grevlex (`docs/MILESTONE-F4.md` §7.1,
`docs/MILESTONE-F4-OPTIMIZATION.md` §7.4.2) — and §7.4.2 then showed that this is **growth from a
very low base rather than densification**:

> Over 155 matrices, and over all 12 107 rows of the eight instrumented ones, not one row ever
> exceeds 50% occupancy at its own peak and not one of the 12 777 64 x 64 blocks exceeds 50%.

The maxima are 45.61% (a row of katsura-6 lex) and 46.62% (a block of katsura-6 lex). Two rows *as
built* do exceed 50% — one 16-of-28 row of cyclic-4 lex and one row of a small early cyclic-5
grevlex matrix — and both are on matrices where `Backend::Dense` is slower anyway. **Nothing in an
F4 matrix is dense at any granularity this crate has measured**, which is why §7.4.2 rejected
density-keyed per-row switching, density-aware pivoting and dense treatment of selected blocks
*before* implementing any of them.

### 1.3 And an iterative method must discard the structure the current path depends on

`linalg::reduce_rows_against_pivots_with(backend, matrix, split, max_nonzeros)`
(`src/linalg/echelon.rs`) treats the upper block as a **pre-established pivot set**: those rows are
left exactly where they are, are not normalized, and are not reduced against one another. That is
the Faugère–Lachartre split, exposed as `ReductionStrategy::Structured`, and on katsura-7 grevlex it
covers 95.9% of the rows (`docs/MILESTONE-F4-OPTIMIZATION.md` §6.2: "katsura-7 grevlex is 95.9%
scaffolding"). It is where the leverage is, and a black-box method cannot see it.

### 1.4 Do not reopen for F4

**#58's own forward-looking sentence is the part of it that has aged, and it aged in a direction
that strengthens the conclusion rather than weakening it.** It proposed "M19-D/M19-E (vectorize and
parallelize the axpy) and smaller multipliers per §6.2". All three have since been settled, and none
of them by a change of algorithm:

- **M19-D (#49)** landed, by autovectorization; explicit intrinsics measured *slower*
  (`docs/MILESTONE-SIMD-PARALLELISM.md` §2). #62's 32-bit field reopens it at eight lanes (§8).
- **M19-E (#50)** is **won't-do** (§6.1). The parallel phase performs *zero* row operations, because
  not one lower row leads with a column a reducer pivot owns: in block terms `D -= C A^-1 B` has
  `C = 0` at every leading position. `BlockPlan::ReducersFirstBlock` buys *avoided* work, not a
  parallel phase — which is §1.3's point measured from the other side.
- **Smaller multipliers** were implemented and **rejected on measurement**
  (`docs/MILESTONE-F4-OPTIMIZATION.md` §7.2.1): on katsura-7 grevlex `LargestLeadingMonomial` gives
  a 68% larger closure, a 2.5x larger matrix and **3.4x the time**, because the matrix pays for a
  row's *tail*, not for its multiplier.

What has actually moved this stage is all inside elimination as structured: the adaptive dense
accumulator over sparse pivots (§7.4.4, now `Backend::Adaptive`, 1.2x–2.0x over `Sparse`),
division-free field arithmetic, and indexing the pivot-of-column by column instead of hashing it
(#159, 28% of the default's elimination stage). §6.2's reading still stands as the shape of the
problem — "Caching the rows attacks 2% of the cost; producing fewer of them attacks the 88%" — but
producing fewer of them is, measurably, not done by choosing a different divisor.

Nothing in the FGLM half of this record bears on the F4 half, and nothing in #224, #263, #368, #76
(XL + block Wiedemann) or #220 (sparse `GF(2)` elimination against CryptoMiniSat) contests it. Each
of those cites this reasoning rather than relitigating it.

---

## 2. FGLM order conversion — deferred in M18, and since reopened

Here the shoe fits, and the pieces are closer than they look.

- `MultiplicationOperator::apply` (`src/grobner/fglm/multiplication.rs`) **is** the sparse matvec,
  already skipping zero input coefficients. Unlike F4's matrix, the multiplication operator is a
  **fixed** operator applied `N * D` times — exactly the black-box model Wiedemann needs.
- `IncrementalSpan` (`src/grobner/fglm/incremental_span.rs`) is a genuine `O(D^3)`-time dense
  echelon form in `O(D^2)` memory.
- Krylov plus Berlekamp–Massey would replace it with `2D` matvecs and `O(D)` memory.
  `docs/MILESTONE-FGLM-SCALABILITY.md` §8.5 answer 5 names this as the only route to `O(D)`.
- Only two things are missing: **Berlekamp–Massey** (`src/grobner/fglm/shape.rs`'s module doc says
  so outright — "Zeebra has no Berlekamp–Massey") and, for the general case, block Wiedemann plus
  Faugère–Mou's structured lex-basis recovery.

### 2.1 Why M18 deferred it

The deferral was a **disjointness result** rather than a cost ratio, and its three measurements
(§8.5 answer 6) are unrefuted:

1. **Where conversion is the only route, the cost is not the dependence algorithm.** Katsura-7's lex
   basis is beyond F4's limits, so FGLM is the only way to it — and 96% of that conversion was
   reducing border monomials, which sparse FGLM does not touch.
2. **Where the dense blocks dominate, the ideal is not in shape position.** planted-10's blocks are
   54x its operators (§8.5; §9.4's shipped-configuration figure is 53.9x — 20.5 MB of blocks against
   380 kB of operators), and its last variable has a minimal polynomial of degree **4** in a
   1024-dimensional quotient. **The systems where memory is the problem are exactly the systems the
   scalar shape route cannot convert.** cyclic is the same: blocks 2.6–2.8x operators (§3.5), no
   separating variable at all (§8.3).
3. **On those systems one should not be converting at all.** planted-8's lex basis takes F4 **0.04
   ms** directly against a 2.8 ms conversion (§8.5), and M17 already made the direct route the
   default.

Scalar Wiedemann yields the minimal polynomial of one element, i.e. the lex basis only **in shape
position** — and §8.3's measured shape-position set is the entire katsura family and nothing else in
the benchmark corpus, plus **76 of the 120** zero-dimensional differential fixtures.

A fourth measurement is worth keeping because it is counter-intuitive: §8.3 ran the Krylov shape
route against the lex walk and the **Krylov route was 2.7x slower at `D = 64`** (0.37x on the route,
2.018 ms against 0.749 ms). The reason is that the walk's vectors are classes of monomials, sparse
early, and `IncrementalSpan::reduce` skips a row whose pivot column is zero in the input; the powers
of a single variable densify immediately and pay close to the full `D^3 / 2`. The cubic worst case
the Wiedemann pitch assumes is not what this span actually pays on this family.

### 2.2 The trigger as #58 wrote it

One condition, and a memory wall rather than a speed one. After §8.6 the span is `D (D + 1)` cells
and the conversion's three dense blocks together are `D^2 + D (D + 1)` — which is what
`max_span_entries` counts (§8.2) — so §9.7 puts the crossing of the 20-million default at
**`D = 3162`**. At `D ~ 1e5` the span alone is ~1e10 cells and classical FGLM cannot run at all.
Wiedemann is the only route past that.

> **Revisit when both hold:** the corpus reaches `D` large enough that the span does not fit, **and**
> those instances are in shape position — otherwise the prerequisite is block Wiedemann and
> Faugère–Mou's structured lex-basis recovery, which is a milestone and not an issue.

Nothing in the M18 corpus was within three orders of magnitude of that `D`, and nothing is today.

### 2.3 What actually reopened it — and it was not that trigger

**The memory trigger has not fired. A different one did**, and a reader who only has §2.2 will
mis-scope the live work. M25's competitive baseline (`docs/research/competitive-baseline.md` §1, §2,
§9, recorded on #263) measured msolve 0.11.0 against Zeebra on one machine with byte-identical
generators, both under `benchlock`, Anemoi CICO at `p = 65537`:

| row | msolve | Zeebra | wall ratio |
|---|---:|---:|---:|
| `n5-fcico` | 1.81 s | 63.71 s | 35x |
| `n5-pcico` | 1.85 s | 39.0 s | 21x |

The **conversion stage alone is ~30x** (47.53 s against ~1.6 s), it is the largest measured
cross-library gap in M25, and **msolve reaches a lex basis by a Wiedemann scalar sequence** — a
different algorithm, not a faster implementation of the lex walk.

The reason this is new evidence rather than erosion of §8.5 is the **stage split**. §8.5's first
measurement rests on katsura-7's conversion being 96% border reduction, where sparse FGLM buys
nothing. On Anemoi `FCICO` at `N = 5` the split is the opposite: **82.8% lex walk and dependence
test**. §8.5 never measured that family, so it is not contradicted by it.

**Three limits travel with the reopening, and #368 restates all three:**

1. It reopens as "the measured conversion gap is worth a Krylov route", **not** as "sparse FGLM
   would be 30x faster". The three engines reach a lex basis by three different algorithms (Zeebra
   walks, Magma V2.26-2 spins `Get rep mat` + Keller-Gehrig, msolve runs Wiedemann), so the ratio has
   no denominator a Zeebra Krylov implementation would inherit.
2. Everything is at `p = 65537`, because msolve refuses `p = 2^64 - 353`. **Whether the deficit holds
   at 64-bit characteristic is unmeasured.**
3. It is **parity work, not frontier work.** #323 measured Anemoi `N = 6` refusing in F4 — 20 000 112
   live nonzeros against a 20 000 000 limit, one part in 180 000 — *before FGLM was reached*, so
   F4's entry budget is the first gate and the FGLM budgets the second. The route to the next Anemoi
   rung runs through #322, not through conversion.

#368 is staged accordingly, and **stage 1 can refuse the rest**: profile a second Anemoi rung and
confirm the 82.8% split is a property of the family rather than of one rung. If it does not
reproduce, the stage-1 negative result is the deliverable. #224 is the wider survey the Krylov route
is one of six candidates in; its deliverable names the measurement that would overturn §8.5, written
down **in advance**.

### 2.4 One caution on reading §3.4 for this question

#58's body argues the FGLM deferral partly from §3.4, where the lex walk is a small share of
conversion on katsura. **§3 is the M17 baseline, and §9.4 is the shipped configuration.** M18 took
katsura-7's border work from 36.60 ms to 1.44 ms and did not touch the walk, so the walk's share went
*up*:

| system | `D` | walk share, §3.4 (M17 baseline) | walk share, §9.4 (shipped) |
|---|---:|---:|---:|
| katsura-5 | 16 | 9.4% | 29% |
| katsura-6 | 32 | 4.9% | 30% |
| katsura-7 | 64 | 2.6% | 31% |
| cyclic-6 | 156 | 5.9% | 46% |
| planted-10 | 1024 | 66% | 69% |

§9.7 states the consequence directly: "The dependence test is now the whole of the remaining problem
on the systems that scale, in both time and memory." So **§3.4 must not be quoted as a current
argument against a Krylov route.** The arguments that survive M18 are §8.5's three in §2.1 above —
disjointness, not share-of-time — plus §8.3's measured 2.7x slowdown of the Krylov route on the one
family where it applies.

§9.7 also names two cheaper things to try first, both inside the existing algorithm: stop retaining
the accepted quotient vectors (half the span's cells after §8.6), and put the span's row operations
through `linalg` — the dependence test is a hand-written dense echelon update over `Vec<F>` that uses
none of the elimination machinery M16 built. `benches/fglm.rs`' `fglm_dependence` is already the
benchmark for the second.

---

## 3. The one reusable asset, worth recording

§8.5 answer 4, and this is the single most cost-reducing fact for anyone picking the FGLM half up.

§8.4's verification — evaluate each output polynomial at the multiplication operators and require the
zero vector, `O(N D)` operator applications — **carries over to a Wiedemann variant unchanged.** It
is independent of the echelon form that produced the coefficients, so a probabilistic Krylov route
choosing a random linear form or a random separating element can be exposed as **certified rather
than conjectural**. That removes the usual objection to Wiedemann in a correctness-critical setting,
and it is already built and tested in `src/grobner/fglm/shape.rs`.

Note the trap §8.4 records: reducing the output modulo the grevlex source basis is the obvious check
and is the **wrong** one. `p(t)` has degree `D` in one variable, which under grevlex is as far
outside the staircase as a monomial gets; tried, it did not finish on cyclic-6 in ten minutes.
Avoiding exactly that reduction is why one converts bases at all.

### 3.1 Smallest useful increment, if picked up

Berlekamp–Massey (~100 lines, standalone, testable against known sequences) plus a scalar Krylov
sequence `u^T T^k v` for `k < 2D` inside `fglm::shape`, which already has the shape-position detector
and the verifier. That is bounded work whose value is bounded with it — see §2.1(2) for what it
cannot convert, and #368 stage 1 for what must be measured before it is worth starting.

---

## 4. Where this class of method does earn its keep

Index-calculus-shaped linear algebra: millions of rows, a handful of nonzeros each, one nullspace
vector wanted, fill-in that would be fatal. **Neither problem in this project has that shape.**
Recorded because it is the relevant comparison, and because it is what makes the F4 answer
unambiguous rather than a close call.

---

## 5. Pointers, so a reader lands on live work

- **F4 half:** closed. `docs/MILESTONE-F4-OPTIMIZATION.md` §6.2, §7.4.1, §7.4.2 are the
  measurements; §1.4 above is what has been tried since and what came of it.
- **FGLM half:** [#368](https://github.com/mfaulk/zeebra/issues/368) is the staged implementation
  issue, [#224](https://github.com/mfaulk/zeebra/issues/224) the alternatives survey, and
  `docs/MILESTONE-FGLM-SCALABILITY.md` §8.5 and §9.7 the record they both start from. If the question
  is "should Zeebra have a Krylov conversion", the answer is in #368's stage 1, not here.
  [#167](https://github.com/mfaulk/zeebra/issues/167) is the competing claim on the same stage —
  parallel border reduction — and #224 is required to defer to it if border reduction turns out to
  bind on the cryptanalytic families.
- **Boolean setting:** #220 asks whether Zeebra's sparse `GF(2)` elimination beats
  CryptoMiniSat's Gaussian-elimination-over-XOR module on matched matrices. A narrow measurement, and
  explicitly not a reopening of §1.
- **XL:** #76 investigates XL as a differently-posed problem whose output is a kernel vector rather
  than an echelon form, and cites §1 for why block Wiedemann is not a replacement for F4
  echelonization.

---

## 6. Citation audit

Every citation in #58's body was checked against the tree at `30348938`. **Six do not hold as
written**, and all six are recorded above with the current figure rather than carried forward.

### 6.1 Verified

| citation | status |
|---|---|
| `docs/MILESTONE-F4-OPTIMIZATION.md` §7.4.1 — katsura-7 grevlex largest matrix 6810 x 6862, 112 200 entries | holds, verbatim |
| §7.4.2 — "nothing in an F4 matrix is dense"; 0 of 12 107 rows and 0 of 12 777 blocks over 50% at peak | holds; see §6.2 below for the qualifier |
| §6.2 — all ten katsura-7 grevlex eliminations total 791.81 ms of an 896.32 ms run | holds |
| §6.2 — katsura-7 grevlex is 95.9% scaffolding | holds |
| 13.58x worst-case fill-in | holds — `MILESTONE-F4.md` §7.1 and `MILESTONE-F4-OPTIMIZATION.md` §7.4.2, which reframes it as growth from a low base |
| `MacaulayMatrix::sparse_row_polynomial` | exists, `src/grobner/f4/macaulay.rs` |
| `MultiplicationOperator::apply` | exists, `src/grobner/fglm/multiplication.rs` |
| `IncrementalSpan` | exists, `src/grobner/fglm/incremental_span.rs` |
| `reduce_rows_against_pivots_with` | exists, `src/linalg/echelon.rs`; the pre-established-pivot contract is as described |
| `fglm/shape.rs` "says so outright" that Berlekamp–Massey is absent | holds — module doc, "Zeebra has no Berlekamp–Massey" |
| `MILESTONE-FGLM-SCALABILITY.md` §3.5 — katsura blocks 0.4x operators, katsura-7 96 kB against 264.5 kB, planted-10 38.4x, cyclic 2.6–2.8x | holds as the **M17 baseline** table, which §3.5 itself labels as such |
| §8.2 — M18-4 took the dense blocks 1.20x smaller | holds, all four systems |
| §8.3 — katsura family in shape position and nothing else in the corpus; cyclic has no separating variable; planted-10's last variable has degree 4 in `D = 1024` | holds |
| §8.3 — the Krylov shape route is 2.7x slower than the walk at `D = 64` | holds (0.37x on the route) |
| §8.5 answers 4 and 5, and all three bullets of answer 6 | holds |

### 6.2 Did not verify as written

1. **"The lex walk is 1.4% / 4.9% / 2.6% of conversion at `D = 16 / 32 / 64` (§3.4)."** Two of the
   three hold; **the first is wrong** — §3.4's katsura-5 row is 0.05 ms of 0.53, which is **9.4%**,
   not 1.4%. More importantly, **all three are M17-baseline figures and §9.4 supersedes them** at
   29% / 30% / 31%. See §2.4; this is the citation most likely to mislead, because it is load-bearing
   in #58's argument and the shipped number points the other way.
2. **"Normal forms grow about `D^3.3` while the lex walk grows about `D^2.3`, so the walk's share
   shrinks as `D` grows."** No document states these exponents; they are derivable from §3.4's table
   (last doubling: `D^3.36` and `D^2.35`), so the arithmetic is right but the citation is a
   derivation, not a quotation. The *conclusion* no longer holds under §9.4 — the walk's share
   **grows** — so this sentence is not carried forward.
3. **"26 of 38 random differential fixtures" in shape position.** That is the M18-4-era corpus.
   §8.3's current text is **76 of 120** zero-dimensional fixtures, and says so explicitly: "26 of 38
   on the corpus as it stood in M18-4, so 68% then and 63% after M18-5 expanded it."
4. **"The span is `D^2 + D (D + 1) / 2` cells regardless"**, giving ~200 GB at `D ~ 1e5`. That is the
   post-M18-4, pre-§8.6 accounting. §8.6 took the span to **`D (D + 1)`** (§8.5 answer 5 and the
   §8.6 table), a fifth off the storage, and §9.7 puts the `max_span_entries` crossing at
   **`D = 3162`** rather than 2828. The memory-wall conclusion is unaffected — a fifth is not an
   order of magnitude, as §9.7 itself says — but the formula and the byte figure are stale.
5. **"The right direction for that stage is M19-D/M19-E (vectorize and parallelize the axpy)."**
   M19-D landed by autovectorization with explicit intrinsics measured slower, and **M19-E (#50) is
   closed won't-do** — `docs/MILESTONE-SIMD-PARALLELISM.md` §6.1 measured the parallel block update
   never faster, at 0.36x to 1.00x, because the parallel phase performs zero row operations. See
   §1.4.
6. **"...and smaller multipliers per §6.2."** §6.2 proposed that hypothesis;
   `docs/MILESTONE-F4-OPTIMIZATION.md` §7.2.1 **implemented and rejected it** —
   `ReducerSelection::LargestLeadingMonomial` is 3.4x slower on katsura-7 grevlex. Kept as an
   ablation option, not merged into the default. See §1.4.

Neither 5 nor 6 touches the F4 conclusion: both are the *alternative* #58 recommended instead of
Wiedemann, and both closing negative leaves the stage with no open algorithmic proposal at all —
which is a reason to be precise about what §1.4 now points at, not a reason to revisit §1.

Two further notes, neither a failure:

- **Line numbers drift and are not reproduced here.** #58 cited `macaulay.rs:212`,
  `multiplication.rs:142` and `shape.rs:26`. At `30348938` `sparse_row_polynomial` is at line 210,
  `apply` is at 142, and `shape.rs`'s Berlekamp–Massey sentence spans 26–27. Symbol names and file
  paths are cited above instead.
- **`docs/MILESTONE-FGLM-SOLVING.md` has no §3.4, §3.5, §8.3 or §8.5.** Those are
  `docs/MILESTONE-FGLM-SCALABILITY.md`'s, which is what #58's body cites; the two filenames are easy
  to transpose and a reader chasing the wrong one finds M17's design document.

### 6.3 Not a citation failure, but a contradiction worth stating

§7.4.2's headline is "no row and no 64 x 64 block above 50% occupancy on any instance", which #58
quotes. The precise claim is **at each row's own peak during elimination**; §7.4.2 also records that
**two rows do exceed 50% as built** (a 16-of-28 row of cyclic-4 lex, and one row of a small early
cyclic-5 grevlex matrix). Both are on matrices where `Backend::Dense` loses anyway, so §1.2's
conclusion is unchanged — but the unqualified form is not what the document says.

---

## 7. References

- Wiedemann, D. (1986). *Solving sparse linear equations over finite fields.* IEEE Trans. Inform.
  Theory 32(1), 54–62.
- Faugère, J.-C., Gianni, P., Lazard, D., Mora, T. (1993). *Efficient computation of
  zero-dimensional Gröbner bases by change of ordering.* J. Symbolic Computation 16(4), 329–344.
- Faugère, J.-C., Mou, C. (2017). *Sparse FGLM algorithms.* J. Symbolic Computation 80, 538–569.
- Faugère, J.-C., Lachartre, S. (2010). *Parallel Gaussian elimination for Gröbner bases
  computations in finite fields.* PASCO '10, 89–97.
