# msolve 0.11.0: what it actually does, and which of it Zeebra may reimplement

Source-grounded study for #264, a child of epic #256. The companion documents are
`docs/research/external-comparands.md` (how msolve is provisioned and invoked) and
`docs/research/external-provenance-policy.md` (what may be reused — the binding constraint here).
The adapter this study was written alongside is `src/grobner/external/msolve.rs` (#259).

**Everything below was read from the pinned 0.11.0 tarball** unpacked at
`~/.local/opt/zeebra-ext/src/msolve-0.11.0`, on 2026-11-06. File:line references are to that tree
and are relative to `src/` (so `neogb/f4.c:671` means `src/neogb/f4.c:671`). Where a claim is a
measurement rather than a reading it says so and names the command.

---

## 0. The licence position, stated before anything else

msolve is **GPL-2.0-or-later**. Verified from the source headers and the licence file at the pinned
version rather than from a classifier: `neogb/la_ff_32.c:1-15` carries the standard
"either version 2 of the License, or (at your option) any later version" grant, and `COPYING` is
the GPL v2 text. Zeebra is MIT (`Cargo.toml:10`, `LICENSE-MIT`).

Three consequences, from `external-provenance-policy.md` §6 and §7:

1. **Running the binary is fine.** The adapter writes a text file, spawns a process and parses
   text. No FFI, no `build.rs`, no vendoring, no Cargo dependency. Running a program is not
   distributing it (policy §7).
2. **Reading the source for understanding is fine.** That is what this document is.
3. **Copying or transliterating any of it into Zeebra is not.** Not the C, and not a
   line-by-line Rust rendering of the C, which is a translation and therefore a derivative work.

Where an algorithm has a published description, **that** is the citation of record and the thing to
implement from (policy §6). For everything this study recommends, the reference is one of:

| technique | reference of record |
|---|---|
| F4 | Faugère, *A new efficient algorithm for computing Gröbner bases (F4)*, J. Pure Appl. Algebra 139 (1999) 61–88 |
| Faugère–Lachartre row arrangement | Faugère and Lachartre, *Parallel Gaussian elimination for Gröbner bases computations in finite fields*, PASCO 2010, 89–97 |
| GBLA (the FL implementation's own description) | Boyer, Eder, Faugère, Lachartre, Martani, *GBLA: Gröbner Basis Linear Algebra Package*, ISSAC 2016 |
| Gebauer–Möller criteria | Gebauer and Möller, *On an installation of Buchberger's algorithm*, J. Symbolic Comput. 6 (1988) 275–286 |
| FGLM | Faugère, Gianni, Lazard, Mora, J. Symbolic Comput. 16 (1993) 329–344 |
| **Sparse-FGLM** | **Faugère and Mou, *Sparse FGLM algorithms*, J. Symbolic Comput. 80 (2017) 538–569** |
| Barrett reduction | Barrett, CRYPTO '86, LNCS 263, 311–323 |
| msolve as a system | Berthomieu, Eder, Safey El Din, *msolve: A Library for Solving Polynomial Systems*, ISSAC 2021, 51–58 |

**Groebner.jl is the worked example of a licence-compliant adaptation, and of its cost.**
`Groebner.jl`'s own `src/Groebner.jl:8-15` names msolve as upstream, names the licence, and
enumerates what it took (the monomial encodings and the hashtable). The result is GPL. That is the
template *and* the warning: an adaptation done honestly is possible, and it relicenses the
adapting project. Policy §5.4 draws the conclusion — reading Groebner.jl's hashtable **is** reading
msolve's, the two readings are not independent, and both are reference-only.

A practical note for anyone extending this study: `neogb` is a **unity build**. `neogb/gb.c:30-51`
`#include`s the `.c` files directly, which is why nearly everything is `static inline` and why
`io.c` can call into `la_ff_*.c`. "File" boundaries in `neogb/` are not translation-unit
boundaries, so a grep that stops at one file will miss callers.

---

## 1. The F4 pipeline

### 1.1 Three phases per round

`neogb/f4.c:671`, `core_f4`. The loop at `f4.c:700` runs exactly three phases:

| phase | call | file:line |
|---|---|---|
| select + symbolic preprocessing | `preprocessing(mat, bs, md)` | `f4.c:706` |
| columns, sort, linear algebra, reinsertion | `compute_new_elements(mat, bs, md, errp)` | `f4.c:709` |
| pair-set update (Gebauer–Möller) | `update(bs, md)` | `f4.c:712` |

`compute_new_elements` (`f4.c:418`) is in turn `convert_hashes_to_columns` (`f4.c:430`) →
`sort_matrix_rows_decreasing(mat->rr, mat->nru)` (`f4.c:431`) → `linear_algebra` (`f4.c:432`) →
`convert_sparse_matrix_rows_to_basis_elements` (`f4.c:446`) → `clean_hash_table(sht)` (`f4.c:449`).

Termination is `update`'s return (`update.c:325-336`): done when a constant entered the basis or
the pair list is empty. After the loop: `process_redundant_elements` (`f4.c:723`),
`reduce_final_basis` (`f4.c:726`).

**Degree selection** is not in `f4.c`. `select_spairs_by_minimal_degree` (`symbol.c:200`) sorts the
pair set (`symbol.c:226`), takes `mdeg = ps[0].deg` (`symbol.c:228`), and selects every pair of
that degree (`symbol.c:256-261`). Its own header comment concedes the strategy is the only one
implemented (`symbol.c:196-197`: *"at the moment only selection by minial degree of the spairs is
supported"*). The `-m` cap is honoured but **never splits an lcm class** (`symbol.c:268-276`),
which is a correctness requirement rather than a nicety.

### 1.2 The hash table is the architecture

This is the single most important structural difference from Zeebra, and everything in §4.1
follows from it.

Monomials are **not bit-packed**. `data.h:101-117` documents the layout as a plain `exp_t`
(`uint16`) vector with the total degree in slot 0 — `[deg, e_1, ..., e_n]`, or
`[deg_b1, e_1..e_k, deg_b2, e_k+1..e_n]` for a two-block elimination order. So the representation
is the same shape as Zeebra's `Monomial<N>` (`src/poly/multivariate/monomial.rs:15-19`, `[u32; N]`),
one width narrower and with the degree cached.

What msolve adds is **interning plus a short divisor mask**:

* The hash is **random-linear and therefore additive** (`hash.c:836-838`:
  `h += ht->rn[j] * a[j];`). Additivity is load-bearing: the hash of a product is the sum of
  hashes, so `find_multiplied_reducer` can pass a precomputed delta rather than rehashing
  (`symbol.c:539`: `const hi_t h = hdm.val - hdb[b[OFFSET]].val;`).
* `sdm_t` is a `uint32_t` **divmask** (`data.h:83`). Bits are allocated across variables —
  `ht->bpv = (CHAR_BIT * sizeof(sdm_t)) / nv` bits per variable (`hash.c:59-62`) — and the
  per-bit thresholds are computed **from the actual input's exponent range**, once, after reading:
  `steps = (max_exp[i] - min_exp[i]) / ht->bpv` in `calculate_divmask` (`hash.c:460-464`), called
  at `engine.c:93`. `generate_short_divmask` (`hash.c:396-418`) then sets bit `ctr` iff
  `a[dv[i]] >= dm[ctr]`.
* Divisibility is tested mask-first (`hash.c:486-489`):

  ```c
  /* short divisor mask check */
  if (ht->hd[b].sdm & ~ht->hd[a].sdm) {
    return 0;
  }
  ```

  falling through to an unrolled exponent comparison only when the masks cannot decide. A
  commented-out `/* printf("! no sdm decision !\n"); */` at `hash.c:496` shows the hit rate was
  instrumented at some point.

There are **two live hash tables**, and the reason is the point:

1. The **basis** table `bht` (`hash.c:46`), `hsz = 2^init_hts`, lives for the whole run.
2. A **secondary/"symbolic"** table `sht` (`hash.c:184`), created per F4 run at `f4.c:377` and
   deliberately *small* — `min = max(3, init_hts - 5)` (`hash.c:198-199`). It holds exactly the
   monomials of the current matrix, and it is wiped every round by `clean_hash_table`
   (`f4.c:449`, `hash.c:924-932`, a `memset` and `eld = 1`).

   **Its entries are the matrix columns.** `convert.c:325-326` says so: *"all elements in the sht
   hash table represent exactly one column of the matrix"*.
3. The two tables **share** the divmask thresholds, the variable selection and the random hash
   vector (`hash.c:203-208`), so hashes and masks are comparable across them. Hence
   `free_shared_hash_data` (`hash.c:234`) existing separately from `free_hash_table`.

`PARALLEL_HASHING` is **compiled off** (`data.h:42`), which is why symbolic preprocessing is
single-threaded (§1.5) and why `check_insert_in_hash_table`'s `#pragma omp critical`
(`hash.c:807`) is dead.

### 1.3 Symbolic preprocessing, and the reducer search

`symbolic_preprocessing` (`symbol.c:558`) walks the symbolic table linearly in two passes
(`symbol.c:596-602` over pre-existing entries, `symbol.c:603-615` over entries appended *during*
the first pass). The second loop is the closure: `sht->eld` is simultaneously the loop bound and
the insertion cursor, so it terminates exactly when no new monomial appears. Zeebra's closure is
the same fixed point, reached with an explicit `VecDeque` worklist and a `MonomialSet`
(`src/grobner/f4/symbolic.rs:28-40`), and its module doc states the same invariant.

`find_multiplied_reducer` (`symbol.c:493`) searches **only the non-redundant lead monomials**
`bs->lmps`/`bs->lm`, and the scan is pure bit arithmetic (`symbol.c:514`, `:524-527`):

```c
const sdm_t ns = ~hdm.sdm;
...
while (i < lml && lms[i] & ns) {
    i++;
}
```

So the common case — "this basis element cannot possibly divide" — costs one AND and one branch,
with no exponent array touched. `bs->lm` is a cached array of divmasks precisely so that this loop
never dereferences the hash table.

### 1.4 Matrix construction: the column map is a side effect

A matrix row is one `hm_t*` (`uint32_t*`) with a six-word prelude (`data.h:52-59`): `DEG`,
`BINDEX`, `MULT`, `COEFFS`, `PRELOOP`, `LENGTH`, then the data. From `OFFSET` onward the row holds
**monomial hashes, overwritten in place by column indices**. Coefficients are not in the row:
`row[COEFFS]` indexes a separate array-of-arrays, so a reducer row **shares** the basis's
coefficient array rather than copying it (`hash.c:1356`, `hash.c:1378`) — F4's "multiply by a
monomial" is free in the coefficient domain, and msolve collects that for free.

`convert_hashes_to_columns` (`convert.c:299`) then:

* allocates exactly one column per symbolic-table entry (`convert.c:327`);
* counts pivot columns by `idx == 2` (`convert.c:332-339`);
* **sorts** `hcm` (`convert.c:340`);
* sets `ncl`/`ncr`/`nc` (`convert.c:351-353`);
* writes the inverse map back into the `idx` field itself (`convert.c:357-361`).

The `idx` field of `hd_t` (`data.h:93-99`) is thus multi-purpose: `0` unseen, `1` seen non-pivot,
`2` known pivot, and after conversion **the column index**. The monomial→column map is not a
separate data structure at all; it is a field msolve was already paying for.

Two consequences worth stating plainly:

* **The A|B / C|D split falls out of the sort.** `monomial_cmp_pivots_drl` (`order.c:459`) compares
  `idx` *first* (`order.c:469-478`, gated by `#define ORDER_COLUMNS 1`, `data.h:43`), so pivot
  columns sort to the front and `ncl` is just a count. No permutation step exists.
* **Entries within a row are deliberately not sorted.** `convert.c:405-413` explains why: rows are
  scattered into a dense `int64_t` accumulator for reduction anyway, *"Once a row is finally
  reduced it is copied back to a sparse representation, now in the correct term order since it is
  coming from the correctly sorted dense row."* Row **order** is sorted (`f4.c:431`); entry order
  is not, because it is recovered for free.

### 1.5 Interreduction is two different things

Conflating them is easy and would make a stage comparison wrong.

**(a) Per-round interreduction of the new pivots.** Always on, *inside* the linear algebra, and
**sequential**: `la_ff_32.c:2729-2766`, a backwards sweep guarded by
`if (st->nf == 0 && st->in_final_reduction_step == 0)` (`la_ff_32.c:2729`). So elements entering
the basis each round are already mutually reduced.

**(b) Final reduction of the whole basis.** A separate phase, `reduce_final_basis` (`f4.c:570`),
called once (`f4.c:726`), gated by `-r` (default `1`, `msolve/main.c:515`). It builds one matrix
from all non-redundant elements as **lower** rows, runs `symbolic_preprocessing` to find reducers
for the tails (`f4.c:599`), then forces every column non-pivot so `ncl == 0` (`f4.c:600-603`), and
calls `exact_linear_algebra` (`f4.c:616`) — **exact, never probabilistic, whatever `-l` says**.
It is pinned to one thread by `in_final_reduction_step` (`la_ff_32.c:2614`).

This is Zeebra's `interreduction` stage (`src/grobner/f4/statistics.rs:32-40`) and msolve's
`reduce gb` line. **Both are single-threaded in both implementations**, and in Zeebra it is
currently 61% of katsura-7 grlex (§3).

### 1.6 Redundancy, and the output filter

`bs->red[i]` is a per-element flag; `lmps[0..lml)` is the compacted index list of non-redundant
elements; `lm[0..lml)` caches their divmasks for §1.3's scan (`data.h:179-200`).

The interesting detail is that redundancy marking is **sugar-aware** (`update.c:178-182`):

```c
if (bs->red[lmps[i]] == 0
        && check_monomial_division(lm, nch, bht)
        && bs->hm[lmps[i]][DEG]-bht->hd[lm].deg >= dd) {
    bs->red[lmps[i]]  = 1;
```

The `DEG - hd.deg` term is the sugar excess, so a lower-sugar element is never declared redundant
by a higher-sugar divisor. `process_redundant_elements` (`f4.c:482`) then does a full pairwise
sweep and compacts (`f4.c:513-521`); what survives **is** the minimal generating set.

### 1.7 Parallelism, in one sentence

Essentially all of it is one OpenMP loop over the to-be-reduced rows of one matrix. The canonical
site is `la_ff_32.c:2641-2643`:

```c
#pragma omp parallel for num_threads(nthrds) \
    private(i, j, k, sc) \
    schedule(dynamic)
```

Each task reduces one row into a private slice of one flat scratch allocation
(`la_ff_32.c:2646`: `drl = dr + omp_get_thread_num() * ncols`). Publication of a new pivot is
**lock-free**, a single CAS (`la_ff_32.c:2697`):

```c
k = __sync_bool_compare_and_swap(&pivs[npiv[OFFSET]], NULL, npiv);
```

inside a `do { ... } while (!k)` retry (`la_ff_32.c:2666-2700`): a thread that loses the race for a
pivot column re-reduces its row against the winner. The subtle part is in the comment at
`la_ff_32.c:2689-2692` — normalization must happen *before* the CAS, "otherwise the reduction may
lead to wrong results in a parallel computation since other threads might directly use the new
pivot once it is synced." There is exactly one `#pragma omp critical` in all of the linear algebra
(`la_ff_32.c:2842`), guarding an append to a shared counter in the saturation path.

Outside linear algebra: column rewriting is parallel (`convert.c:365`, `:383`, `:661`); the
Gebauer–Möller sweep over *old* pairs is parallel (`update.c:124`); the second GM pass is
intrinsically sequential (early `break`, order-dependent); lcm insertion and redundancy marking are
parallel only under `PARALLEL_HASHING`, which is off (`update.c:95-98`, `:172-175`). **Symbolic
preprocessing has no `#pragma omp` at all** — there is none anywhere in `symbol.c` — because both
its loops mutate the shared symbolic hash table.

### 1.8 The tracer, and why it exists

Over **Q**, the combinatorial part of F4 is prime-independent for a lucky prime. `LEARN_TRACER`
records which reducers and multipliers each matrix used; `APPLY_TRACER` replays it, skipping pair
selection, Gebauer–Möller and symbolic preprocessing entirely (`f4.c:711` skips `update`;
`preprocessing` routes to `generate_matrix_from_trace`, `symbol.c:642`). The per-row
`mat->rba` bit arrays (`symbol.c:625-629`, set at `la_ff_32.c:367-371`) record *which* reducers
were actually used, and `construct_trace` (`tools.c:63`) keeps only those — so a replayed matrix is
smaller than the matrix that was learned from.

Divergence is the bad-prime detector, in three places: wrong count of new elements
(`f4.c:435-443`), wrong leading term (`f4.c:455-466`), unexpected zero reduction
(`la_ff_32.c:2683-2687`).

**Zeebra has no analogue and does not need one yet**: it computes over a single prime field, so
there is no multi-prime run to amortize a trace over. This is noted because it is the largest
single piece of msolve's F4 that is *not* a candidate for Zeebra, and because it explains why
msolve's design puts so much weight on recording multipliers (`MULT`, `BINDEX`) in every row.

### 1.9 `-q`: the signature-based path, which is a dead end

`core_sba_schreyer` (`sba.c:639`) is a real F5/GVW-style implementation with syzygy and rewrite
criteria (`sba.c:673-674`). It is also almost unreachable: `use_signatures` defaults to 0
(`msolve/main.c:507`), the only call site is `msolve/msolve.c:4062`, and that branch
**hard-codes the characteristic to 1073741827** regardless of the user's prime
(`msolve/msolve.c:4039`, announced at `:4052-4056`) and **requires homogeneous input**, exiting
otherwise (`:4045-4049`). Only 32-bit arithmetic exists for it. Everywhere else
`use_signatures != 0` is fatal (`engine.c:138-143`, `:156-160`, `:173-177`).

So msolve is **not** evidence that signature-based F5 pays in practice. `docs/research/signature-based.md`
§4.4 already declined #223 on other grounds; this is a second, independent reason not to revisit it
on msolve's account.

---

## 2. The per-bitwidth elimination kernels

### 2.1 There are three, not four, and the dispatch is not where the comments say

**Correction to #269's premise, part one.** The issue names four prime-field kernels including
`src/neogb/la_ff_small_prime.c`. That file does not exist. The pinned tree has:

```
neogb/la_ff_8.c   neogb/la_ff_16.c   neogb/la_ff_32.c   neogb/la_qq.c
```

and `la_qq.c` is not a fourth bitwidth (§2.6).

**Correction part two.** `set_function_pointers()` is an **empty stub** (`io.c:1285-1290`,
body `(void)st;`), as are `reset_function_pointers` (`io.c:1333-1340`) and
`reset_trace_function_pointers` (`io.c:1341-1346`). Every comment in the tree that says "linear
algebra, depending on choice, see `set_function_pointers()`" — `modular.c:273`, `modular.c:477`,
`f4sat.c:155`, `nf.c:89` and others — points at a mechanism that was replaced and not removed.

Real dispatch is a nested `switch` in `linear_algebra()` (`io.c:878-958`), outer on `st->ff_bits`
(`io.c:885`), inner on `st->laopt`. And `-l 43` is unreachable: the validator whitelists only
`{1, 2, 42, 44}` and silently rewrites anything else to `2` (`io.c:700-704`).

### 2.2 The bitwidth ladder, and the dead branch in it

`set_ff_bits` (`io.c:621-639`):

| characteristic | `ff_bits` | file:line |
|---|---|---|
| `0` (rationals) | `0` | `io.c:622-623` |
| `p < 2^8` | `8` | `io.c:625-626` |
| `2^8 <= p < 2^16` | `16` | `io.c:628-629` |
| `p >= 2^16` | `32` | `io.c:631-634` |

The `p < 2^23` test at `io.c:631` is **vestigial — both arms assign 32.** The same ladder, with the
same dead branch, is written out twice more (`io.c:601-619` as the predicate `check_ff_bits`, and
inline at `meta_data.c:38-48`).

**The finer dispatch that actually matters is not `ff_bits`.** `io.c:782-787`:

```c
static inline int use_17_bit_reduction(const uint32_t fc)
{
    return fc < ((uint32_t)1u << 18);
}
```

Note the name/threshold mismatch — "17-bit" but the test is `< 2^18`. The thin wrappers in `io.c`
use it to pick between two genuinely different 32-bit kernels (`io.c:1095-1114`, and the same
pattern at `:1065-1078`, `:1116-1135`, `:1137-1151`, `:1153-1165`).

**So there are four live prime-field reduction schedules, not three**: 8-bit, 16-bit, "17-bit"
(`p < 2^18`) and "31-bit" (`2^18 <= p < 2^31`).

### 2.3 Narrow kernels do not buy a narrow accumulator

The coefficient types are unsigned, residues in `[0, p)` (`data.h:71-73`):

```c
typedef uint8_t cf8_t;
typedef uint16_t cf16_t;
typedef uint32_t cf32_t;
```

**But the accumulator is `int64_t` in all three** — `la_ff_8.c:98`, `la_ff_16.c:98`,
`la_ff_32.c:309` and `:968`. So `ff_bits` is about *storage* for the sparse reducer rows, not about
arithmetic width. The two things it buys:

1. **Bytes streamed.** 1 or 2 bytes per coefficient instead of 4, in a loop that is otherwise
   memory-shaped.
2. **SIMD lanes**, which follows directly from (1):

| kernel | AVX-512 step | AVX2 step | NEON step |
|---|---|---|---|
| 8-bit | 64 coeffs/iter (`la_ff_8.c:178`, `:183`) | 32 (`la_ff_8.c:346`, `:351`) | 16 (`la_ff_8.c:448`, `:455`) |
| 16-bit | 32 (`la_ff_16.c:181`, `:186`) | 16 (`la_ff_16.c:275`, `:280`) | 8 (`la_ff_16.c:335`, `:341`) |
| 32-bit | 16 (`la_ff_32.c:376`, `:383`) | 8 (`la_ff_32.c:430`, `:437`) | 16 / 8 |

The 8-bit AVX-512 path multiplies 32 `int16` lanes with `_mm512_mullo_epi16` (`la_ff_8.c:186`) off
a pre-broadcast 16-bit multiplier (`la_ff_8.c:175-176`); the 32-bit path manages 8
`_mm512_mul_epu32` lanes and burns a `_mm512_srli_epi64(redv, 32)` to reach the odd ones
(`la_ff_32.c:395`, `:407`).

### 2.4 Two reduction schedules, and the one Zeebra's benchmark prime does *not* get

This is the finding with the most leverage in the whole study.

**Below `2^18` — true delayed reduction.** `reduce_dense_row_by_known_pivots_sparse_17_bit`
(`la_ff_32.c:308-580`). The multiplier is pre-negated so every multiply-accumulate is a
non-negative `+=` (`la_ff_32.c:365`: `const int64_t mul = mod - dr[i];`), and the scalar inner loop
has **no modular correction at all** (`la_ff_32.c:545-550`):

```c
for (; j < len; j += UNROLL) {
    dr[ds[j]]   +=  mul * cfs[j];
    dr[ds[j+1]] +=  mul * cfs[j+1];
```

The *only* reduction is one `%` per column, taken lazily when the outer cursor arrives
(`la_ff_32.c:349-352`). Each product is under `p^2 < 2^36` and the accumulator holds `2^63`, so
roughly `2^27` accumulations are safe — far above any realistic row count, which is why nothing
checks. **One `%` per matrix entry, zero per multiply-accumulate.** The 8-bit and 16-bit kernels
use the identical schedule (`la_ff_8.c:151-152`, `:165`, `:528-534`; `la_ff_16.c:152-153`, `:167`,
`:378-384`).

**At or above `2^18` — per-MAC branchless correction.** `..._31_bit` (`la_ff_32.c:967-1244`). Here
`p^2` can reach `2^62`, so the accumulator cannot drift. `mod2 = fc * fc` (`la_ff_32.c:985`), and
the loop subtracts then conditionally adds back using the sign bit as a mask
(`la_ff_32.c:1204-1213`):

```c
dr[ds[j]]   -=  mul * cfs[j];
...
dr[ds[j]]   +=  (dr[ds[j]] >> 63) & mod2;
```

`(x >> 63)` is all-ones when negative, so this is a branchless conditional add maintaining
`0 <= dr[k] < p^2`. **One correction per multiply-accumulate** — a mask-and-add rather than a
division, but not free, and not delayed.

The implied bound is `p < 2^31.5`, because `mod2` is computed in signed 64-bit. msolve's authors
say so, and concede they have no fix (`la_ff_32.c:2344-2346`):

```c
 * Note: We cannot apply this trick to the reduction itself, there we
 * cannot restrict the multiplier to be < 2^31, so we have to handle the
 * fc > 2^31 case differently.
```

A **genuine** 32-bit kernel handling `p` up to `2^32` does exist, with split hi/lo accumulators and
Barrett folding constants (`la_ff_32.c:1660-1661`), and it is `#if 0`-ed out from
`la_ff_32.c:1631` to `:1739` (its tracer twin from `:1742` to `:1840`, marked
`/* unused at the moment */`). It also contains the only place in the file where unrolling was
measured and **rejected**: `/* loop unrolling is slower */` (`la_ff_32.c:1703`).

**The consequence for every Zeebra-vs-msolve comparison at 31 bits.** Zeebra's benchmark field is
`Zp2147483647` / `Mersenne31`, `p = 2^31 - 1`. That is `ff_bits == 32` and fails
`use_17_bit_reduction`, so msolve runs the **31-bit per-MAC-corrected** kernel. msolve's delayed
reduction — the thing that looks like its advantage — **is not in play on the instances Zeebra
benchmarks**. It is in play only for `p < 2^18`, where Zeebra has no corresponding field in its
benchmark set at all.

### 2.5 SIMD: real, extensive, and non-portable

* `__AVX2__`, `__AVX512F__`: **zero occurrences.** msolve uses its own autoconf macros, not the
  compiler's.
* `#pragma omp simd`: **zero.** `restrict` on a kernel pointer: **zero** (the only hits are in the
  bundled `sort_r.h` and in English prose).
* Intrinsic calls: `la_ff_32.c` 130, `la_ff_8.c` 66, `la_ff_16.c` 46. Zero everywhere else —
  including `la_qq.c`, `convert.c` and `hash.c`.
* Dispatch is **compile-time only**: a per-kernel `#if HAVE_AVX512_F / #elif HAVE_AVX2 /
  #elif __aarch64__ / #else` chain (headers at `la_ff_8.c:24-29`, `la_ff_16.c:24-29`,
  `la_ff_32.c:24-29`; bodies at e.g. `la_ff_32.c:374`, `:428`, `:466`, `:538`). **No runtime CPU
  check and no function multiversioning.**
* The flags come from a bare `AX_EXT` at `configure.ac:73`, which probes the *build* host's CPUID
  and both `#define`s `HAVE_AVX2`/`HAVE_AVX512_F` and injects `-mavx2`/`-mavx512f` into
  `SIMD_FLAGS` (`m4/ax_ext.m4:234-235`, `:316-317`), reaching the kernels via
  `libneogb_la_CFLAGS` in `neogb/Makefile.am`. There is no `--enable-avx` switch.

So **a stock msolve build is native-only codegen**: it may not run on a host lacking the build
host's ISA. In this checkout, `config.h:21` has `HAVE_AVX2 1` and `config.h:36` leaves
`HAVE_AVX512_F` undefined, so the comparand being measured is the AVX2 build.

There is also unconditional 4× scalar unrolling driven by one macro (`data.h:47-49`), with the
remainder precomputed per row into the `PRELOOP` slot:

```c
 * NOTE: if one changes UNROLL then also code needs to be changed:
#define UNROLL  4
```

### 2.6 `la_qq.c` is not multi-modular

Worth stating because the name invites the opposite reading. `la_qq.c` is **exact fraction-free
integer Gaussian elimination** with GMP: the accumulator is `mpz_t *dr` (`la_qq.c:73`, `:168`),
fractions are avoided by cross-multiplying through an LCM (`la_qq.c:124-126`), the MAC loop is
`mpz_submul` (`la_qq.c:137-143`), and every finished row has its content stripped by
`remove_content_of_sparse_matrix_row_qq` (`la_qq.c:24-70`) to stop coefficient blow-up. No SIMD,
no probabilistic variant.

The multi-modular strategy is elsewhere: `modular.c` runs F4 per lucky prime
(`generate_lucky_primes`, `modular.h:92-121`), and CRT plus rational reconstruction live in
`crt/mpz_CRT_ui.c:77`, `crt/mpq_reconstruct.c:205`/`:262` and `msolve/lifting-gb.c`. One detail
matters for reading msolve's own timings: the production Q path starts at prime `2^30`
(`msolve/msolve.c:2171`, `:4772`, `:4946`), so it is **always** `ff_bits == 32` and always past
`2^18` — i.e. always §2.4's per-MAC-corrected kernel, never the delayed one.

---

## 3. Sparse-FGLM

### 3.1 It is Faugère–Mou, and Zeebra's FGLM is not

msolve implements the **scalar Wiedemann / Berlekamp–Massey variant**, not classical FGLM. The
structures are named for it (`msolve/msolve-data.h:130-135`: `vecinit` *"init vector used in
Wiedemann's implementation"*), and the three pieces are:

* **Krylov iteration** — `generate_sequence_verif` (`fglm/fglm_core.c:662-741`), repeated
  matrix-vector product with a pointer swap (`:678-690`), `2D` products total, harvesting `2D`
  scalars at `:737-739`.
* **Berlekamp–Massey** — `compute_elim_poly` (`fglm_core.c:745-752`), calling FLINT's
  `nmod_berlekamp_massey_add_points` / `_reduce`. The minimal generator `V1` is the eliminant.
* **Hankel solving instead of Gaussian elimination** — `invert_hankel_matrix`
  (`fglm_core.c:203-367`) and `solve_hankel` (`:369-440`). This is the Faugère–Mou step that
  recovers coordinates in `O~(D)` from the same scalar sequence.

A **block** Wiedemann path exists and is unfinished: `fglm_core.c:585-660` under `#ifdef BLOCKWIED`,
whose caller ends `fprintf(ERRSTREAM, "Implementation to be completed\n"); exit(1);`
(`fglm_core.c:1414-1423`).

**Zeebra's FGLM is the classical 1993 algorithm.** `src/grobner/fglm/conversion.rs:1-17` says so:
monomials are visited in increasing lex order, each one's residue class is tested for dependence
against an incremental span, and the dependences are the lex basis. That is linear algebra over the
quotient, `O(D^3)`-shaped in the worst case, against sparse-FGLM's `2D` matrix-vector products.

### 3.2 What is sparse about the multiplication matrix

`sp_matfglm_t` is at `msolve/msolve-data.h:110-124` (not in `fglm/`). The stored `dense_mat` is a
plain row-major `nrows × ncols` block — **nothing about the coefficients is sparse.** What is
sparse is that only `nrows` of the `ncols` rows are stored at all: the rest are *unit vectors*,
encoded as index pairs `triv_idx`/`triv_pos`. The worked example at `msolve-data.h:91-107` shows a
5×5 matrix stored as 2 rows plus three index pairs.

So the product costs `nrows × ncols` multiply-adds plus `ncols - nrows` **copies**
(`sparse_mat_fglm_mult_vec`, `fglm_core.c:451-487`; the copies at `:460-462`). The honest statement
of the algorithm's cost is msolve's own operation count at `fglm_core.c:1628`:
`2 * nrows * ncols^2`. **The win over dense FGLM comes entirely from `nrows << D`** — 11 against 32
on katsura-5 at `p = 1073741827`, measured here.

The **free/non-free split** is built in `msolve/hilbert.c:3489-3854`. For each basis monomial `m`,
`m * x_n` either stays in the basis (unit row, `hilbert.c:3758-3767`), lands exactly on a GB
leading monomial (**free part** — the row is read straight off the GB, `hilbert.c:3774-3786`), or
lands on a proper multiple (**non-free part** — a genuine normal form must be computed by a
separate F4 call, `hilbert.c:3665-3687`). `nnfs` counts the latter (`hilbert.c:3692`). So in the
verbose output I measured — `degree of ideal 32`, `#dense rows 11`, `#normal forms 0`,
`total density 89.2%` — `#normal forms 0` means the staircase was generic and every one of the 11
dense rows came free from the basis.

There is a second-order sparsity exploitation too: `dst` records, per dense row, the length of the
trailing run of zeros (`hilbert.c:3828-3837`), and the kernels shorten the dot product with it
(`linalg-fglm.c:640`).

### 3.3 The kernels, the prime bound, and a window where msolve is unguarded

The kernels that matter are in `fglm/linalg-fglm.c`, dispatched at `fglm_core.c:463-482` with the
usual compile-time `HAVE_AVX512_F / HAVE_AVX2 / else` chain. **`fglm/matrix-mult.c` — the file with
the Barrett `_MODRED32` and the `2^30 < p < 2^31` comment (`matrix-mult.c:69-93`) — is dead code**:
its only entry point `sparse_matfglm_mul` (`:271-300`) is called only from the `#ifdef BLOCKWIED`
path. (It also contains a latent bug that is harmless only because it is dead:
`fglm_core.c:597` computes `preinv = 2^(62) / prime`, where `^` is C's XOR, so `2^62 == 60`.)

The live AVX2 kernel accumulates **eight** products before folding
(`_nmod32_vec_dot3_split_avx2`, `linalg-fglm.c:443-621`; eight `_mm256_mul_epu32` accumulations,
then one 56-bit carry extraction at `:547-552`, one `NMOD_RED` at `:618-620`). That needs
`8p^2 < 2^64`, i.e. `p < 2^30.5`. Hence the guard value `1518500213`.

**And here is a real defect.** `linalg-fglm.c:33-39` documents the safe modulus as `1515531528`:

```c
//  -> modulus <= DOT2_ACC8_MAX_MODULUS   (about 2**30.5, slightly less)
#define DOT2_ACC8_MAX_MODULUS UWORD(1515531528)
```

Neither `DOT2_ACC8_MAX_MODULUS` nor `DOT2_ACC8_MAX_LEN` is **ever compared against anything** in
msolve's tree. They are documentation. So the runtime guard admits `p <= 1518500212` while the
kernel's stated precondition stops at `1515531528`, leaving a **2 968 684-wide window** of primes
that run to completion with no accumulation guarantee. The scalar fallback is worse: its
constraints are an open `FIXME` (`linalg-fglm.c:48`), so on a non-AVX2 host the prime bound is
undocumented and unchecked.

`src/grobner/external/msolve.rs`'s `MAX_CHARACTERISTIC_ELIMINANT` is therefore set to the
**documented-safe** `1515531529` (exclusive) rather than to msolve's own guard: a possibly-wrong
answer is worse for this milestone than a row marked unsupported, and no Zeebra benchmark prime
lies in the window.

### 3.4 Above the bound, msolve does not terminate — and that is provable

The guard at `fglm_core.c:1384-1389` returns `NULL`. Three sites carry the same condition and
**three different error policies**:

| site | function | on failure |
|---|---|---|
| `fglm_core.c:1384` | `nmod_fglm_compute_trace_data` (first/learning prime) | `return NULL` |
| `fglm_core.c:1586` | `nmod_fglm_compute_apply_trace_data` (replay prime) | **`exit(1)`** |
| `fglm_core.c:1804` | `nmod_fglm_guess_colon` (`-C`) | `return NULL`, **and the caller never checks** — `msolve/msolve.c:4406` then dereferences it at `:4420` |

Only the first is reachable in a normal run, and only for `gens->field_char >= 1518500213`: over Q
the lift prime is capped below the bound (`msolve/msolve.c:2247-2251`), while a user-supplied prime
goes straight in (`:2261-2263`).

The `NULL` is then **laundered into the genericity signal**. `msolve.c:1740-1752` sets
`*success = 0; *dim = 0; *dquot_ori = dquot;` — the *same* triple used when the staircase is
genuinely not generic (`msolve.c:1724-1734`). That becomes return code 1, documented at
`msolve.c:2113-2114` as *"not in generic position"* (`:2446`), which reaches the `goto restart`
handler at `msolve.c:4513-4533`.

**That loop cannot exit**, from two source facts:

* `add_linear_form_to_input_system` has no failure path — its final statement is `return 1;`
  (`msolve.c:649`).
* once a linear form exists, `undo_variable_order_change` short-circuits
  (`msolve.c:482-484`: `if (gens->linear_form_base_coef > 0) { return 0; }`), so
  `change_variable_order_in_input_system` returns 0 forever after.

So with the default `-c2` the steady state is: fresh basis → FGLM → prime still too large →
code 1 → add another linear form → `goto restart`. Each round grows the system, so successive
attempts get *slower*.

**Measured, and it matches exactly.** katsura-5 over `GF(2^31 - 1)`: 25 353 `Adding a linear form`
occurrences and 1.37 M lines of `Prime 2147483647 is too large.` in eight seconds, `degree of ideal`
never printed, no exit. `-c0` turns it into one clean failure.

### 3.5 Genericity: three gates, and the one `-d` controls

Easy to conflate, and the adapter has to distinguish them.

* **Gate A — "too many normal forms"**, at matrix-build time, `msolve/hilbert.c:3607-3630`. This is
  where **`-d` acts**: `threshold` is a fraction of `dquot - len_xn` chosen by the `-d` value
  (`hilbert.c:3609-3622`; `-d0` → 0, `-d1` → ¼, `-d2` → ½ (default), `-d3` → ¾, `-d4` →
  unlimited). Raising `-d` raises the budget of normal forms msolve will compute to repair a
  non-generic staircase **in place**, instead of bailing out to variable reordering and linear
  forms. This is the flag that avoids §3.4's loop for genuinely non-generic input — and it is a
  much better answer than `-c 0`.
* **Gate B — shape position**, `fglm_core.c:1467`: `if (dimquot == param->degelimpol)`. Full-degree
  minimal polynomial means shape position and the clean Hankel parametrization runs; otherwise the
  radical-only path does (`fglm_core.c:1083`). It is re-checked independently at
  `msolve/msolve.c:1753`, which on failure runs a **second FGLM with a fresh random projection**
  and cross-checks with `equal_param` (`msolve.c:1623-1630`).
* **Gate C — "Ideal not in generic position"**, the message the adapter sees,
  `fglm_core.c:1531-1536`. The actual test is a randomized per-coordinate verification
  (`fglm_core.c:1146-1202`): for each coordinate that is neither a linear-form leading variable nor
  missing its square from the monomial basis (`:1150-1151`), a random `lambda` is drawn, the
  parametrization recomputed from the twisted sequence, and compared (`:1174-1177`). Only the first
  failing index is recorded.

Two more latent defects, recorded because they affect what an adapter can trust: a constant
eliminant triggers `goto restart` **only under `info_level > 1`** (`fglm_core.c:1461-1465`), so at
low verbosity a degenerate eliminant silently falls through; and `fglm_core.c:1589` `exit(1)`s where
its sibling returns `NULL`.

### 3.6 Parallelism in FGLM is almost nil

**Two** `#pragma omp` directives in all of `src/fglm/` — `linalg-fglm.c:637` and `:1109`, both:

```c
#pragma omp parallel for num_threads (st->nthrds) lastprivate(i)
        for (i=0; i < nrows-2; i+=3)
```

i.e. the row loop of the dense part of a *single* matrix-vector product, in blocks of three. The
Krylov iteration is inherently serial (each product feeds the next), Berlekamp–Massey is serial,
and the whole FGLM is run single-threaded during the initial step anyway
(`msolve/msolve.c:1851-1854`: *"F4 and FGLM are run using a single thread"*). The real parallelism
in the multi-modular phase is **across primes** (`msolve/msolve.c:1858-1859`), not inside FGLM.

### 3.7 No complexity claims, and no Faugère–Mou citation

Worth recording, because it bears on policy §6. There are **no paper citations and no complexity
statements anywhere in `src/fglm/`**. The nearest things are a hybrid-cutoff heuristic comment
(`berlekamp_massey.c:241-244`, ending `TODO: find cutoff`), the FLINT-inherited accumulation bound
(`linalg-fglm.c:34-39`), and the operation count at `fglm_core.c:1628`. The only bibliographic
reference in the whole distribution is the msolve system paper in `README.md:236-244` — **not**
Faugère–Mou.

So implementing sparse-FGLM in Zeebra means implementing it **from Faugère–Mou (2017)**, which is
the citation of record anyway, with msolve's source read only as evidence about engineering. That
is the comfortable case rather than the awkward one.

---

## 4. Hypotheses, each with the measurement that would settle it

**The premise this section does *not* use.** `MILESTONE-F4-OPTIMIZATION.md` §6.2's "elimination is
65–88% of F4 runtime" is obsolete; it predates M16's own optimizations. §8.5 of the same document
is the current attribution:

| system | order | total | symbolic | construction | elimination | extraction | interreduction |
|---|---|---|---|---|---|---|---|
| cyclic-5 | lex | 3.14 | 0.65 | **1.48 (47%)** | 0.37 | 0.09 | 0.35 |
| katsura-6 | lex | 19.53 | 4.42 | **9.33 (48%)** | 1.28 (7%) | 0.99 | 2.33 |
| katsura-6 | grevlex | 3.77 | 0.31 | 1.14 | 0.80 | 0.08 | **1.33 (35%)** |
| katsura-7 | grlex | 46.72 | 2.58 | 6.21 | 8.00 (17%) | 0.63 | **28.71 (61%)** |
| katsura-7 | grevlex | 32.13 | 1.64 | 5.53 | 7.12 (22%) | 0.40 | **16.90 (53%)** |

Elimination is **7–22%**. The two largest stages are **interreduction** and **matrix
construction**. #269's title still carries the old number; a correction is filed on that issue.

### 4.0 The stage-name mapping, which is why any of this is measurable

msolve is the only comparand in the M25 set that reports a stage breakdown, and its stage names are
**Zeebra's**. From `neogb/meta_data.c:285-327`, `fglm/fglm_core.c:84-87` and
`msolve/msolve.c:3800-3808`:

| msolve label | source | Zeebra `StageTimings` field |
|---|---|---|
| `select` | `meta_data.c:296` | — (Zeebra does not time pair selection separately) |
| `symbolic prep.` | `meta_data.c:299` | `symbolic` |
| `update` | `meta_data.c:303` | — (Zeebra's pair-set update is inside `other`) |
| `convert` | `meta_data.c:308` | **`construction`** |
| `linear algebra` | `meta_data.c:312` | **`elimination`** |
| `reduce gb` | `meta_data.c:317` | **`interreduction`** |
| `overall(elapsed)` (block 1) | `meta_data.c:287` | the F4 total |
| `overall(elapsed)` (block 2) | `fglm_core.c:85` | **no counterpart** — sparse-FGLM |
| `rational param(elapsed)` | `msolve.c:3802` | no counterpart |
| — | | `extraction` (folded into msolve's convert/basis-add) |

**Four of Zeebra's five stages have a direct msolve counterpart**, so §8.5's attribution can be
checked against an independent F4 stage by stage rather than end to end. That is what makes the
hypotheses below testable rather than rhetorical. Note the two blocks that share the label
`overall(elapsed)` for different quantities — the adapter disambiguates by which named stages the
block contains, because msolve's resolution is **10 ms** (`%.2f sec`) and a block breakdown means
nothing on an instance that finishes in microseconds.

### H1 — The monomial→column map should be a side effect, not a per-matrix structure

**Target stage: `construction`, 48% of katsura-6 lex and 47% of cyclic-5 lex.** The largest
remaining cost on the lex instances, and never a target of M16.

Zeebra rebuilds the column mapping per matrix: `MacaulayMatrix::build` collects distinct monomials
into a `HashSet`, sorts them (`src/grobner/f4/macaulay.rs:86`), then builds a
`HashMap<Monomial<N>, usize>` (`:88`) and fills rows through it. §8.5 names exactly this —
*"construction's per-matrix cost (the monomial-to-column `HashMap`, the sort) does not shrink with
the matrix"* — and notes the pair criteria replaced 59 large matrices with 107 small ones, so the
per-matrix cost is now paid more often.

msolve pays none of it. The monomials are already interned in the per-round symbolic table, the
column index is written into the `idx` field they already have (`convert.c:357-361`), and the A|B
split falls out of the same sort that orders the columns (`order.c:469-478`). There is no hash map
and no separate permutation.

**What Zeebra would do:** make symbolic preprocessing hand out column indices as it interns
monomials, so construction is a scatter rather than a build-then-lookup. This is a reimplementation
of the *idea* — interning with an index — not of msolve's code, and the idea is not msolve's
invention; it is how F4 implementations have organized matrices since Faugère (1999) §2.1 and is
described in GBLA (ISSAC 2016). **Licensing verdict: reimplementable from the published
description. No adaptation of msolve's code needed, and none permitted.**

**The measurement.** `examples/f4_profile recommended` already reports `construction` as a separate
stage. Instrument the current path to split `construction` into (a) the `HashSet`+sort, (b) the
`HashMap` build, (c) the row scatter, on katsura-6 lex and cyclic-5 lex. If (a)+(b) is under a
third of `construction`, the hypothesis is refuted and the cost is in the scatter, where msolve has
no advantage. **Refutation condition stated up front**, because this is the hypothesis most likely
to be wrong: the `HashMap` already uses `BuildMonomialHasher` (`src/poly/multivariate/monomial_hash.rs`),
a multiplicative FxHash chosen over SipHash for exactly this reason, so the lookup may already be
cheap.

### H2 — A divmask would cut the reducer search, and Zeebra has no equivalent

**Target stage: `symbolic`, 23% of katsura-6 lex (4.42 of 19.53).** Third largest there.

Zeebra's `Monomial<N>` is `[u32; N]` and nothing more (`src/poly/multivariate/monomial.rs:15-19`);
a grep for `divmask`/`sdm` across `src/` returns nothing. Every divisibility question is answered by
comparing exponent arrays.

msolve answers the common negative case in one AND (`hash.c:486-489`), with per-variable bit
thresholds calibrated to the input's own exponent range (`hash.c:460-464`), and keeps a cached
array of just the divmasks of non-redundant lead monomials so the reducer scan never touches the
hash table (`symbol.c:514`, `:524-527`).

**Licensing verdict: the technique is reimplementable; the calibration is the part to be careful
about.** A divisor bitmask over monomials is standard and long predates msolve — it is in
MathicGB (Roune and Stillman, ISSAC 2012) and the Gebauer–Möller literature. msolve's *specific*
choice — 32 bits split evenly across variables with thresholds from measured min/max exponents — is
an engineering decision read here as evidence, and Zeebra should arrive at its own by measurement
rather than by copying the constants.

**The measurement.** Count divisibility tests and their outcomes in Zeebra's
`find_multiplied_reducer` equivalent on katsura-6 lex and katsura-7 grlex, then compute the
fraction that a 32-bit mask with input-calibrated thresholds would decide negatively without an
exponent comparison. The hypothesis is worth implementing only if that fraction is high **and**
`symbolic` is a large enough share to matter — which is instance-dependent: it is 23% of katsura-6
lex but 5% of katsura-7 grlex. A counter-only experiment settles it before any kernel is written.

### H3 — Sparse-FGLM is the one algorithmic replacement with a real asymptotic argument

Zeebra's FGLM is classical (`src/grobner/fglm/conversion.rs:1-17`), msolve's is Faugère–Mou (§3.1).
This is not an engineering difference; it is a different algorithm with a different complexity, and
the gap widens with the quotient dimension `D`.

The concrete lever is §3.2: the multiplication matrix by `x_n` has only `nrows` non-unit rows, and
`nrows << D` whenever the staircase is generic — 11 against 32 on katsura-5, measured. msolve's own
operation count is `2 · nrows · D^2` (`fglm_core.c:1628`) against classical FGLM's `D^3`-shaped
cost.

**Licensing verdict: reimplementable, and comfortably so.** Faugère–Mou, J. Symbolic Comput. 80
(2017) 538–569 is the citation of record and is already named in the provenance policy's table for
this very issue. msolve's source contains **no** citation and **no** complexity statement (§3.7),
so there is nothing to be gained from it beyond engineering detail — and the two engineering
details most worth having are both independently published: Berlekamp–Massey via half-GCD
(msolve uses FLINT's `nmod_poly_hgcd`, `berlekamp_massey.c:273`) and the structured Hankel solve.
**What must not happen** is transliterating `fglm_core.c`'s `invert_hankel_matrix` or
`solve_hankel`; those are GPL C and a Rust rendering of them is a derivative work.

**The measurement.** This is the one hypothesis that needs no new instrument.
`src/grobner/fglm/statistics.rs` already reports `FglmStageTimings`, and the adapter already
extracts msolve's `quotient_dimension` and `eliminant_degree`. Run both on the katsura rungs over
`p = 1073741827` — **not** `Mersenne31`, which is above msolve's eliminant ceiling (§3.3) — and plot
conversion time against `D`. Classical FGLM should show a steeper slope. If it does not, the
asymptotic argument does not bite at the corpus's `D` and the work should wait for larger
instances. `cyclic-4` must be excluded: it is positive-dimensional (`benchmark_systems.rs:10-15`)
and msolve correctly returns `[1, 4, -1, []]` rather than an eliminant, so it is not a conversion
row at all.

### 4.4 Three things *not* to adopt, recorded so they are not revisited

* **Per-bitwidth kernels below 32 bits — not yet, and for a reason that is already measured.**
  #269 asks whether msolve's `la_ff_8.c`/`la_ff_16.c` show that per-field specialization pays.
  Zeebra has already run the storage-width experiment: `MILESTONE-SIMD-PARALLELISM.md` §8.2
  measured `Mersenne31` (4 bytes) against `Zp2147483647` (8 bytes) at a fixed entry count and found
  **2.36x** (1.802 → 0.765 ns/entry), flat from 8 KB to 128 MB — and corrected its own premise in
  doing so: the kernel is **ALU-bound at both widths**, not bandwidth-bound, and the cause is that a
  64-bit Montgomery reduction is 128-bit arithmetic LLVM will not vectorize while a 32-bit one is
  64-bit arithmetic it will. §5.3 had earlier caught the confound that made hand-written AVX2 look
  good (`u32` against `u64` arrays, so AVX2 moved half the bytes).

  So **Zeebra independently arrived at msolve's rationale for its 32-bit kernel and measured the
  cause.** Going below 32 bits is a genuinely open question, but it is narrower than #269 states,
  and it is not where the next gain is: §8.2 measured the already-written 8-lane AVX2 kernel at
  1.7–3.0x, which is **#149**, and elimination is 7–22% of total (§4 preamble). Ship #149 first and
  re-ask afterwards.

  One more reason to discount the comparison: §2.4 — msolve's delayed-reduction schedule is not
  even active at Zeebra's benchmark prime. At `p = 2^31 - 1` msolve runs the per-MAC-corrected
  kernel, so whatever advantage its narrow kernels have is invisible on the instances being
  compared.

* **Compile-time-only SIMD dispatch — no.** msolve's `AX_EXT` approach (§2.5) produces native-only
  binaries with no runtime check and no multiversioning. For a distributed Rust library that is a
  non-starter, and Zeebra's `target.*.rustflags` floor of `-C target-cpu=x86-64-v3` plus runtime
  feature detection is the better shape. Recorded because msolve's kernel inventory looks
  attractive and its *dispatch* should not be copied along with it.

* **The tracer — not applicable.** §1.8. It amortizes F4's combinatorics across many primes, and
  Zeebra computes over one prime field. There is nothing to amortize.

---

## 5. What was found that is not about Zeebra at all

Recorded because a comparand's defects bound what its measurements mean, and because the adapter
had to handle two of them.

1. **The eliminant path does not terminate above `p = 1518500213`** (§3.4), proved from source and
   measured. Routed to a capability bound in `src/grobner/external/msolve.rs`.
2. **A 2 968 684-wide window of primes runs with no accumulation guarantee** (§3.3): the runtime
   guard is looser than the documented-safe modulus, and the documented constants are never
   enforced.
3. **A factor naming an undeclared variable is silently dropped.** `store_exponent`
   (`iofiles.c:26-73`) splits each term on `*` and matches every factor against the declared names
   with a full `strcmp` — which is the *good* news, and is exactly why msolve is immune to the
   `x1`/`x10` prefix collision (§5a). But the matching loop (`iofiles.c:57-62`) has no `else`:

   ```c
   for (k = 0; k < gens->nvars; ++k) {
       if (strcmp(gens->vnames[k], var) == 0) {
           ((gens->exps) + pos)[k] = strtol(ev, NULL, 10);
           break;
       }
   }
   ```

   Measured: `x*z-1` with only `x,y` declared yields the leading ideal `{x, y^2}` instead of
   `{x*z, y^2}` — exit 0, `#invalid equations 0`, no signal anywhere. The adapter checks every
   identifier in every generator against the declared order before running. (Duplicate variable
   names, by contrast, msolve *does* catch: `iofiles.c:1005`, exit 1.)
4. **The genericity recovery exits 0 after substituting a different ideal** — `-c 2` permutes the
   variables and appends a new one carrying a random linear form (`msolve.c:511-546`,
   `msolve.c:144-148`), and at the default `-v 0` says nothing. The adapter compares the output's
   variable list against the instance's on every run.
5. **`-v 1`'s advisory output goes to stderr, not stdout.** `neogb/streams.h:24-26` defines
   `OUTSTREAM stdout`, `VERBSTREAM stderr`, `ERRSTREAM stderr`; measured, `-v 1` puts zero bytes on
   stdout. `external-comparands.md` §3.8 said stdout; corrected there by #332. Immaterial to the
   adapter (the supervisor merges both streams) but it matters to anyone driving msolve by hand
   with `2>/dev/null`.
6. **`-C` can dereference NULL**: `nmod_fglm_guess_colon` returns `NULL` (`fglm_core.c:1808`) and
   `msolve/msolve.c:4406`'s caller never checks before `:4420` dereferences it.
7. **`-l 43` is silently rewritten to `-l 2`** (`io.c:700-704`), so the `_2` probabilistic variants
   are unreachable from the CLI.
8. **A constant eliminant only recovers under `-v 2`**: the `goto restart` at
   `fglm_core.c:1461-1465` is nested inside `if (info_level > 1)`.
9. **`-q` hard-codes the characteristic** to 1073741827 regardless of the input
   (`msolve/msolve.c:4039`) and requires homogeneous input.

None of these is a reason to distrust msolve as a *basis* comparand: `-g 2` agreed exactly with
Zeebra's F4 on katsura-4, katsura-5, katsura-6, cyclic-4 and cyclic-5 over `GF(2^31 - 1)`, on
leading monomials and cardinality (#259's test suite). They bound what the **eliminant** rows can
say.

### 5.1 The prefix collision, which msolve gets right

Recorded as a **positive** result, because it is the one hazard in this milestone that cross-engine
agreement provably cannot catch. At ten or more variables `x1` is a prefix of `x10`, so a greedy
tokenizer reads `x1*x10` as `x1*x1*0`. Every engine is handed the same bytes, so such a misparse
makes all of them agree on the *wrong* ideal — four tools agreeing and disagreeing with nothing,
which is indistinguishable from success by the check this milestone otherwise relies on. The only
valid test is against the input.

msolve is safe, by construction and by measurement:

* **By construction.** `store_exponent` (`iofiles.c:26-73`) is delimiter-based, not greedy: it
  splits each term on `*` or end-of-string, extracts the factor name up to `^` or the factor end,
  and matches with `strcmp(gens->vnames[k], var) == 0` — a whole-string comparison, never
  `strncmp`.
* **By measurement.** 53 distinct degree-2 monomials over `x1..x14`, pairing every single-digit
  index with every double-digit one in both orders of appearance, were handed to
  `msolve -g 1`. A set of distinct degree-2 monomials is pairwise non-dividing, so the reduced
  basis of the monomial ideal they generate *is* that set — and msolve returned all 53, identical
  as a set. Pinned as a live test in `src/grobner/external/msolve.rs`.

So no corpus rung is at risk from this through msolve — which matters because the corpus names its
variables `x1..xN` (`corpus.rs`'s `text_instance`), i.e. **the naming with the hazard in it**, and
its rungs go well past nine variables. The adapter's own identifier check (defect 3 above) had to
be whole-token for the same reason, or it would have rejected what msolve accepts.

---

## 6. Status of the stage-by-stage comparison

§4.0 establishes that the mapping exists and is direct for four of Zeebra's five stages. The
*numbers* — msolve's stage breakdown beside Zeebra's §8.5 table on the same instances — are
deliberately **not** in this document, for two reasons rather than one.

The lesser reason is scheduling: the measurement was queued under `tools/benchlock.sh` behind other
agents' long-running jobs and had not acquired the lock. The better reason is that it should be
taken on **#261's corpus** rather than on the hand-rolled Katsura inputs this study's author
generated to establish msolve's input format. A corpus rung's identity is a frozen digest that a
test asserts (`src/grobner/external/corpus.rs`, `ladder()`), so a figure taken outside it has no
warrant that it is about the problem it claims to be. The queue slot was released rather than held.

The adapter's own tests were moved onto the corpus for the same reason: `corpus_pair` in
`msolve.rs`'s test module builds each rung through `corpus::instance` and asserts its digest
against `ladder()`, so the recorded fixtures and the live agreement test run **the exact instances
the sweep will**. One consequence worth noting: the corpus's `REFERENCE_CHARACTERISTIC` is
`2^31 - 1`, which is **above** `MAX_CHARACTERISTIC_ELIMINANT` (§3.3) — so the corpus's reference
field supports basis comparisons against msolve and **not** eliminant comparisons. An eliminant
sweep needs a second characteristic below `1515531529`.

That second characteristic now exists as a **generated** field rather than only as a label:
`corpus::ALTERNATE_CHARACTERISTIC = 2^30 + 3 = 1073741827`, the prime msolve's own `kat6-31.ms`
declares. Before #425 the corpus put the requested characteristic in the `FieldSpec` and generated
over the reference field regardless, so these tests' `P30` rungs were systems reduced mod `2^31 − 1`
labelled mod `2^30 + 3` — a well-formed input file for a different ideal. `P30` is now
`corpus::ALTERNATE_CHARACTERISTIC` rather than a literal, so a prime the corpus has no compiled
field for is a build error here instead of a silently mislabeled instance.

The corpus also settles the naming question in §4.0's favour: it names rungs **by variable count**,
never by the literature's family index, which is the same convention as msolve's `katN` (§4.0) —
so `katsura-6` means the same six-variable system to both, and the digests confirm it.

So the measurement is **filed, not estimated**. It is cheap — seconds of msolve per rung, three
repeats — and it needs only two things this study already supplies: the adapter captures msolve's
stages into `Measurement::stages` with msolve's own labels, and §4.0 says which Zeebra field each
one corresponds to. Note before taking it that msolve's resolution is **10 ms** (`%.2f sec`), so
the rungs below katsura-7 will quantize every stage to zero.

What can be said without it, because it is structural rather than numerical: msolve times
`select` and `update` as separate stages and Zeebra does not. Zeebra measured its pair criteria at
**0.3–0.7%** of total on katsura-6/7 (`MILESTONE-SIMD-PARALLELISM.md` §6.2). Whether msolve's
`select` + `update` is a comparable share on the same instance is exactly the kind of question the
mapping makes askable, and it should be asked before anyone concludes that one implementation's
pair handling is cheap because the other's is.
