# Specialized Gröbner engines: what gb, GBLA, OpenF4, MathicGB, Macaulay2, CoCoALib and Giac add

**Measured at:** not measured here — every figure is quoted from a cited source (upstream code, a
paper's table, or an earlier Zeebra document at the commit it names). Source reading only; nothing
was built or run except a header read of one data file (§1.5).

This is #267 (H11), a child of #256. It is organized by the issue's four technical questions, not by
library. Every upstream engine below is GPL or LGPL, or (MathicGB) asserts GPL in its headers
without a licence file: **algorithms and results are references only, no line may enter the MIT
crate** (`docs/research/external-provenance-policy.md`, #274). Citations are `path:line` relative
to each upstream repository root at the commit pinned in §0.

---

## 0. Sources and licences

| library | pinned commit (read 2026-11-15) | last push | licence, as verified |
|---|---|---|---|
| `ederc/gb` | `002c79c0` | 2020-11-10 | GPL-2.0 (GitHub metadata) |
| `ederc/gbla` | `2f8ebcf5` | 2018-12-21 | LGPL-2.1-or-later — policy doc table row |
| `nauotit/openf4` | `7155c6ec` | 2018-04-06 | GPL-3.0-or-later — `COPYING`, `openf4/include/ideal.h:2-10` |
| `broune/mathicgb` | `c72c945b` | 2013-10-07 | GPL-2.0-or-later asserted in headers; `LICENSE.txt` absent — policy doc §3.2 |
| `Macaulay2/mathicgb` (maintained fork) | `31cec23f` | 2026-11-13 | GPL-2.0-or-later, `README.md:12-19`, ships `gpl-2.0.txt`, `gpl-3.0.txt` |
| `Macaulay2/M2`, `M2/Macaulay2/e/` only | `ba27e776` | 2026-11-13 | **unverified from the extract**: `e/` headers carry copyright lines only (`gb-default.cpp:1`, `f4.cpp:1`); treat as GPL, reference only |
| `cocoa-official/CoCoALib` | `8f65159b` | 2026-11-06 | GPL-3.0-or-later — `COPYRIGHT-full-text`, `TmpGReductor.C:6-9` |
| `geogebra/giac` | `19a710ae` | 2026-10-12 | GPL-3.0-or-later per file, no root licence — `src/giac/cpp/cocoa.cc:85-98`; `mathml.cc`, `kadd.cc`, `tinymt32.cc` carry no GPL header |

The issue's table said MathicGB has "no licence file" and so "no grant of rights". #274 already
corrected that: the headers grant GPL-2.0-or-later and only the file is missing. The maintained
Macaulay2 fork has since added the GPL texts. The vendored `mathic` library (the KD-tree and
DivList code) is a git submodule that the M2 tarball does not contain (`e/CMakeLists.txt:9-10`), so
§2's tree internals come from MathicGB's configuration of it and from the paper.

---

## 1. Elimination kernels: GBLA and gb

### 1.1 GBLA's block structure

- **Pivot choice.** Each leading column takes the *sparsest* row leading there as its pivot; the
  rest become `C|D`, and pivot columns move left (`src/mapping.c:27-72`, citing Lachartre).
- **Tiles are 256 × 256** (`configure.ac:90`, `__GBLA_SIMD_BLOCK_SIZE`), inner sub-blocks 1 × 4
  (`:89`).
- **The default never forms `A⁻¹B`.** Mode `-s 1` (`cli/gbla.c:101`, `fl_block_sparse_dense_keep_A`
  at `:552`) reduces `C` by `A`'s rows, overwriting each cleared entry with its negated multiplier so
  `C` becomes `C·A⁻¹` (`src/elimination.c:3709-3776`). It then blocks that and computes
  `D −= (C·A⁻¹)·B` as tile products, densifies `D` and echelonizes it
  (`elim_fl_dense_D`, `src/elimination.c:2450`). Mode `-s 0` is the textbook order, `B := A⁻¹B`
  with one OpenMP task per block column (`src/elimination.c:279-386`).
- **Representation is by role, not by measurement.** `A` and `C` are sparse blocks; `B` and `D`
  are dense blocks. `__GBLA_HYBRID_THRESHOLD = 0.5` (`configure.ac:95`) applies only when
  converting `B`'s two-row multilines to blocks: a block row at least half full becomes dense
  (`src/matrix.c:784-800`). The 10% `__GBLA_DENSITY_THRESHOLD` (`configure.ac:96`) only sizes
  buffers (`src/mapping.c:2633-2650`).
- **Arithmetic.** `uint16_t` entries with a `uint64_t` accumulator (`src/types.h:35,77-83`); products
  are accumulated with negated multipliers and reduced `% p` only when a column's multiplier is read
  (`src/elimination.c:3735-3737`).
- **Parallelism.** 10, 6, 4, 2 or 1 `C` rows per OpenMP task by size (`src/elimination.c:3345-3440`);
  the `D` echelon is a short sequential pre-elimination and then a parallel phase with a locked
  waiting list (`:2109`, `:2450-2516`).

### 1.2 gb

gb does not use GBLA's blocks; its `gbla-*.c` copies are not compiled (`src/gb.c:27-42`). The
default `laopt=1` (`src/io.c:868`) densifies each lower row into an `int64` row and reduces it by the
known pivots in an unsynchronized OpenMP loop, then echelonizes `D` dense
(`src/la_ff_16.c:737`, `:1460-1505`). Options 42–44 are probabilistic: rows are grouped into
⌊√(n/3)⌋ + 1 blocks, one random combination per block is reduced, and a block stops at its first
zero (`src/la_ff_16.c:411-525`). Prime-size ladder: 16-bit coefficients below 2^15, one reduction
per row below 2^17, else a 31-bit path (`src/io.c:710-729`, `:818-825`).

### 1.3 What is new for Zeebra

Already covered, by an earlier study or by Zeebra itself:

- reducer-block-first elimination: `src/grobner/f4/structured.rs`, `BlockPlan::ReducersFirstBlock`
- the bit-width ladder and delayed reduction: `msolve-implementation.md` §2
- the √(n/3) probabilistic scheme: `groebner-jl-implementation.md`
- the waiting-list `D` echelon: `waiting-row-scheduler.md`
- two-row sharing: measured at about 2% and rejected in `multirow-reuse.md` (#715)

New:

1. **`C·A⁻¹` then one block product.** This turns the `D` update into dense tile products. It
   matters because of `docs/research/gpu-f4.md` (#225, PR #805): Zeebra's `D'` is **40–90%
   dense** while the matrix as built has almost no dense 64 × 64 tile. GBLA's choice to make `B`
   and `D` dense *by role* is the same observation, made by construction.
2. **The 0.5 per-block-row dense switch.** Zeebra deliberately keys no representation decision on
   density (`src/linalg/echelon.rs:41-45`), on the evidence that no row or tile of the matrix *as
   built* crosses 50%. That evidence does not cover `D'`. Both points are inputs to #803 (the CPU
   time split of sweep against residual), not a separate experiment.
3. **Minor: sparsest row as pivot.** Zeebra's reducer block has exactly one row per lead by
   construction (the reducer-block invariant in `structured.rs`). The choice therefore only arises
   among pair rows, where it is a pivot rule. Not pursued.

### 1.4 Buildability

Both use autotools (`gbla`: AC_PREREQ 2.69, gnu99, OpenMP, no BLAS or GMP; `gb`: C11, GMP, OpenMP,
`Makefile.am:4-15`). Neither was built. GCC 14's promotion of implicit declarations to errors is a
plausible obstacle for the 2018 GBLA tree (an inference, not tested). Since the techniques are
already characterized from source and Zeebra has its own corpus, building them is **not needed**
for any open question.

### 1.5 GBLA's matrix collection — verdict for H6 (#262)

`docs/research/f4-matrix-corpus.md` §3 established that the hpac.imag.fr catalogue survives and every
matrix file 404s, and declined to write a reader. That stands, with **one correction**: the GBLA
repository ships a real F4 matrix in its tests, `test/examples/jcf-type-f4-kat12-mat1`, in the
*old* format that `load_jcf_matrix` reads (`cli/io.c:146`, `:218-312`). Its header, read with
`od`, is **929 × 1657, p = 65521, 101 857 nonzeros** (6.6% dense), and the file is exactly the
614 878 bytes the format predicts (20-byte header, then u16 values, u32 column indices and u32 row
lengths). sha256 `36f67860582210dc1eabcf38f6ec70aa1f0fa1fa4eb9d8f75967ed70c1623ccd`.

So §3's "a test fixture that has to be invented" is not quite right, but its decision holds:

- the file is one katsura-12 matrix
- it is smaller than half of Zeebra's pinned corpus entries
- it is LGPL data, so committing it would need its own provenance decision under #274

**Verdict: the collection is not retrievable. The one surviving matrix does not justify a reader.**

---

## 2. Monomial and divisibility data structures: MathicGB

### 2.1 What it provides

- `StaticMonoLookup<UseKDTree, Data, AllowRemovals, UseDivMask>` selects `mathic::KDTree` or
  `mathic::DivList` (`src/mathicgb/StaticMonoMap.hpp:23-36`, `:128-134`).
- The runtime codes are 1 = list with divmasks, 2 = KD-tree with divmasks, 3 = list,
  4 = KD-tree (`:388-394`).
- The CLI option `divisorLookup` defaults to **2** (`src/cli/GBCommonParams.cpp:44-48`), and the
  Macaulay2 entry point hard-codes it (`src/mathicgb.cpp:948-949`).
- Tree configuration (`StaticMonoMap.hpp:111-123`):
  - `LeafSize = 1`
  - the tree divmask is on whenever the leaf divmask is
  - divisor caching is on
  - rebuilds use `RebuildRatio 0.5`, `RebuildMin 50`
- `preferSparseReducers` defaults to true (`GBCommonParams.cpp:12-17`): every divisor is enumerated
  and the one with the fewest terms is kept (`StaticMonoMap.hpp:315-344`).

### 2.2 The regime where the tree pays

Roune and Stillman, *Practical Gröbner basis computation*, ISSAC 2012, arXiv:1206.6940. §4.2 states
that the divmask-plus-tree combination "is the fastest in every case". Its own Table 3 shows
otherwise. These are signature-basis runs, not F4. Times are in seconds as printed:

| example (variables, basis size) | divmask list | divmask KD-tree | plain list |
|---|---:|---:|---:|
| katsura10 (10, 276) | 2 | 3 | — |
| joswig101 (5, 1 556) | 84 | 93 | — |
| katsura11 (11, 545) | 19 | 18 | — |
| hcyclic8 (9, 5 419) | 139 | 112 | 1270 |
| mayr42 (51, 32 362) | 835 | 273 | > 30 min |
| yang1 (48, 63 216) | 3917 | 1333 | > 8 h |

Read across the rows, the tree ties or loses at hundreds to about 1 500 basis elements. It wins at
thousands of elements, and decisively at tens of thousands with about 50 variables. This is an
inference from six rows, since the paper states no threshold. Divmasks alone reject 98–99% of
checks except on the 5-variable example (83.5%, Appendix C.3.2, Table 5).

### 2.3 Where Zeebra is, and the disposition

`docs/MILESTONE-F4-OPTIMIZATION.md` §7.2.2 measured:

- **3.8–47.2 basis elements examined per query** across cyclic-4/5 and katsura-5/6/7
- that removing divisor lookup *entirely* would save about **1% of a 1.4% stage**
- that a degree-grouped index was *slower* (23.9 → 28.4 ms on katsura-7 grlex), because it broke a
  sequential scan

`groebner-jl-gap.md` row 6.4 put the symbolic stage at 1.35%, with a 1.014× ceiling. The default
reducer rule is `ReducerSelection::FirstApplicable` (`src/grobner/f4/options.rs:307-308`), which
stops at the first divisor. The enumerate-all case MathicGB's default needs is the non-default
`FewestTerms` (`find_sparsest_divisor`, `src/grobner/f4/symbolic.rs:591`).

**Disposition: closed permanently.** Zeebra's bases are one to two orders of magnitude below the
size at which the paper's own table shows the tree winning. Reopen only with all three of:

- a shipping workload whose basis is above about 5 000 elements, or above about 30 variables
- divisor lookup measured at 5% or more of total time
- an enumerate-all reducer rule on the default path

This is the third independent rejection, after §7.2.2 and `singular-engine-notes.md` §2.3.

### 2.4 Anything else in MathicGB

Nothing further here for the F4 path:

- **Lazily parallel matrix construction** (`F4MatrixBuilder2.cpp:295-335`) is concurrent
  symbolic preprocessing, which is #592's and #728's territory.
- **The final dense echelon** (`F4MatrixReducer.cpp:393-505`) is GBLA's by-role densification of
  `D`, covered in §1.3.

Its signature engine (`SignatureGB`, `SigPolyBasis`, the base-divisor criterion, the 16/32-bit
S-pair triangle) belongs to #716's reassessment of signature methods. It is recorded there as a
source, not re-studied here.

---

## 3. Interreduction and tail reduction: CoCoALib, Macaulay2, Giac

| engine | how the reduced basis is produced | citation |
|---|---|---|
| CoCoALib | Each S-polynomial fully reduced, tail included. Homogeneous: every existing tail is reduced by each new element *before* insertion, so the basis stays reduced. Otherwise one final pass that drops divisible leads and tail-reduces the rest. Geobuckets throughout. | `src/AlgebraicCore/SparsePolyOps-reduce.C:130-141`, `:244-273`; `TmpGReductor.C:356-357`, `:650-683`; `ReductionCog.C:90-105` |
| Macaulay2 `gbA` | New elements fully reduced before insertion. Same-degree elements cancel the one term on the new lead. At the end: sort ascending, keep elements whose lead has no kept divisor, reduce each by the kept set. | `e/groebner-computations/gb-default.cpp:2072-2110`, `:2141-2144`, `:2634-2650`; `e/reducedgb-field.cpp:45-98` |
| Macaulay2 `f4` | Homogeneous only. Per-degree `gauss_reduce`, then `tail_reduce` clears pivot columns from tails, so no final step is needed. `e/gb-f4/` is a skeleton; `e/interreduce.cpp` is a 26-line stub. | `e/f4/f4.cpp:817-895`, `:1046`; `e/f4/f4-computation.cpp:53-55` |
| Giac | Each round's new rows get a full RREF. **The final interreduction builds rows from the tails only, reduces each against fixed reducer rows that are never themselves reduced, and skips the RREF.** | `src/giac/cpp/cocoa.cc:12468-12509`, `:12586-12598`, `:13132-13134`, `:13416`, `:13489`, `:13552-13555` |

**Zeebra's final interreduction does not do what Giac does.** `interreduce_by_matrix`
(`src/grobner/f4/interreduce.rs:242`) runs `reduced_row_echelon_tracked` over the **whole**
matrix, reducer multiples included. It then keeps only the rows led by some `lm(gᵢ)` (`:262-271`).

- The back-substitution among reducer rows is work whose output is discarded.
- The comment above that call records the cost on `katsura-11` grevlex: built at 11.3 M entries,
  reduced at a high-water of **103.9 M**, in a run peaking at 13 144 MB against the division route's
  533 MB.
- msolve's `reduce_final_basis` does the same as Giac: all columns non-pivot, `ncl == 0`
  (`msolve-implementation.md` §1.5, citing `f4.c:600-603`). Zeebra documented that design and
  never adopted it.

That is the one technique in this question that Zeebra lacks. It is filed as #808
and not claimed as a gain here: since #575 interreduction is 0.34% of `mq-random-10`
(`interreduction-cost.md` §3g.3), so the expected value is in **memory on the classical families**
more than in time.

**CoCoALib: nothing further here.** Geobuckets would only speed up the division route, which the
matrix route replaces. Incremental tail reduction applies to homogeneous input and gives up F4's
batching.

**Macaulay2: nothing further here.** Its ascending minimal-then-reduce pass is Zeebra's division
route, and its per-degree `tail_reduce` is `RowForm::Reduced` (#477).

---

## 4. Beyond conventional F4: OpenF4 and Giac

### 4.1 OpenF4 — the Joux–Vitse variant

**Already covered elsewhere:**

- element types as a template parameter (`openf4/include/ideal.h:66`, `matrix.h:79`)
- a dense `Element**` matrix (`matrix.h:480`)
- 64-column slices in elimination (`openf4/src/specialisation-echelonize-prime.inl:180-183`)
- centred lazy reduction (`openf4/src/element-prime.inl:53`, `:129-138`)
- normal-strategy selection (`openf4/src/ideal.inl:1010-1036`)

**New: Faugère's `Simplify`.**

- `Ideal::simplify` keeps a per-variable rule chain on each tagged polynomial. A product `x·f` is
  replaced by the *reduced row* a previous matrix produced for it (`openf4/src/ideal.inl:234-279`).
- `postprocessing` writes each reduced pivot row back over the reducer's own entry
  (`:813-824`), so the reducers improve across rounds.
- Zeebra's `ReducerCache` (`src/grobner/f4/symbolic.rs:126-138`) caches only a multiple's *shifted
  terms*, not a reduced row.
- `sagebrush-implementation.md` records that Sagebrush uses the fewest-terms heuristic "rather than
  Faugère's full `Simplify` table".
- No earlier study records it in msolve or Groebner.jl.

It changes the rows symbolic preprocessing selects and so the trajectory, and its value is
instance-dependent. It is filed as #809.

**OpenF4's GF(2) support: nothing further here.** It stores one `bool` per entry with a per-element
XOR loop (`include/element-gf2.h:126`; `specialisation-echelonize-gf2.inl:46-53`), weaker than
Zeebra's packed GF(2) (#801).

**OpenF4's GF(2^n) kernels.** Per-multiplier lookup tables (`src/element-gf2-extension.inl:224-384`)
and fused 2/4/8-row `addMult` (`include/matrix.h:353-418`). They are a niche reference for
`Gf256Mq` if GF(2^8) F4 becomes a measured workload (#804).

**Buildability.** Autotools; Givaro is needed only for primes of 2^32 and above. The repository
documents its own libgomp/libstdc++ `make check` failure (`doc/page-bug-libstdcpp.dox`). Not
built; not needed.

### 4.2 Giac

| technique | what it does | citation | in Zeebra? |
|---|---|---|---|
| learning | first prime records zero-reducing pairs and the symbolic trace; later primes replay it and print "learning failed" on a pivot mismatch | `cocoa.cc:13170-13183`, `:13444-13458`, `:14500-14511` | no. Only useful over Q, which Zeebra does not compute; msolve's LEARN/APPLY is the studied equivalent |
| probabilistic certification | an extra prime checks the reconstructed basis; `proba_epsilon` controls it | `:16960`, `:17901-17914` | Zeebra certifies exactly; nothing to take |
| 16-bit delta column indices | escape to 32-bit shifts; two shifts per 32-bit load | `:28`, `:6030-6058`, `:12322-12360` | no; see below |
| four primes per SIMD lane | `GBASIS_4PRIMES` under AVX2 | `:32-35`, `:7531`; `headers/modint.h:33` | no. A multi-modular technique; Zeebra's fields are single-prime |
| delayed reduction | `int64` accumulator, cleanup every 32 768 updates | `:7197-7280` | yes, `src/linalg/dense/accumulator.rs` |
| sparse then dense | rows compressed to their used columns, then multithreaded `smallmodrref` | `:13100-13150` | it is the `D'` densification of §1.3 |
| RUR | modular rational univariate representation beside the basis, reconstructed multi-modularly | `:15073`, `:15538`, `:15811`, `:16250-16271` | out of scope here; msolve's parametrization is the existing comparator |
| Buchberger fallback | used when few minimal-degree pairs remain | `:536-538`, `:14391-14394` | no; small-batch policy, #273-adjacent |

The 16-bit delta-coded column index is the only Giac representation idea not already examined.

- Zeebra's sparse entry is `(usize, F)`, which alignment pads to **16 bytes at any field width**
  (`docs/MILESTONE-SIMD-PARALLELISM.md` §8.4). That is why halving the field width did not shrink
  sparse storage.
- A compact index is #268's territory (compact representations). It is recorded there as a
  reference, not filed separately.

---

## 5. Results

**Negative results, recorded so they need not be re-derived:**

1. **Divisor index structures: closed permanently** (§2.3).
2. **GBLA's matrix collection: not retrievable.** No reader is worth writing for the one surviving
   matrix (§1.5).
3. **CoCoALib: nothing further here** (§3).
4. **Macaulay2, `gbA`, `f4` and `gb-f4`: nothing further here** (§3). `gb-f4` is a skeleton.
5. **OpenF4's GF(2) support: nothing further here** (§4.1).
6. **gb:** nothing beyond what the msolve and Groebner.jl studies cover (§1.2).

**Techniques Zeebra lacks, each filed as an evidence-gated follow-up rather than adopted:**

- **#808: tail-only final interreduction against fixed reducers** (Giac, msolve), against the full RREF
  in `interreduce.rs:242`. Expected value is memory on classical families.
- **#809: Faugère's `Simplify`** (OpenF4). Changes the trajectory; value instance-dependent.

**Inputs to existing work, not new issues:**

- GBLA's `C·A⁻¹`-then-tile-product order and its by-role dense `D` feed #803 and `gpu-f4.md`.
- Giac's 16-bit delta indices feed #268.
- MathicGB's signature engine feeds #716.

**Buildability.** None of the four unmaintained engines needed building: every question was
answered from source. Their build systems are recorded in §1.4 and §4.1 for whoever needs a
measured comparison later.
