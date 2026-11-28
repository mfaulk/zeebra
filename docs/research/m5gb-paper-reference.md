# M5GB, the authors' implementation, on ordinary prime-field ideals (#1165)

**Status:** laptop stage done. **Eligibility: conditionally eligible** as a #1030-style arm for
grevlex reduced bases over odd primes p < 2³², on systems with no zero, duplicate or redundant
generator, and only with every basis canonicalized and verified (§8). It is not a deciding
measurement, and it gives #1032's R-m5 route no positive evidence: on every dense row measured it
is slower than Zeebra's shipping F4 (§7).

**Measured at:** `8cdcc5d9` (`runs-upstream`, `runs-repair-interreduce`) and `381de5a4`
(`runs-hash-probe`, `runs-hash-narrow`), both on main `dca8a943`, and the Zeebra timings are
`dca8a943`'s F4. Those commits were later squashed into the single commit that adds this note, so
that no commit in the history carries the GPL-derived patch files (§2). The harness is the same
apart from where it reads the patches and the digest check, and the patch digests recorded in
every `.build` sidecar still match. macOS 15.7.3 arm64 (M4 Pro, 14 cores), Apple clang 17.0.0
(clang-1700.6.3.2), Zeebra example in release with thin LTO and 16 codegen units, unpinned, one
worker, 2026-11-27. Every timing here is a **laptop development figure**: it describes ARM64
behaviour and does not satisfy #1030's or M35's workstation protocol. No figure is pooled across
variants. Evidence: [`research/1165-m5gb-paper-reference/`](../../research/1165-m5gb-paper-reference/README.md).

Parent: #1030. Feeds: #1032 (gated, unchanged). Corrects:
[`m4gb-m5gb-reference.md`](m4gb-m5gb-reference.md) §3.2 and §7, which said this code was not public.

## 1. Identity and pins

| What | Pin |
|---|---|
| Paper | Hauke et al., M5GB, arXiv:2208.00844 |
| Reference | `extgit.isec.tugraz.at/krypto/m5gb` (the paper's `extgit.iaik.tugraz.at` URL redirects there) at `16ef968db7f3c2d1899e915e0904034672b8afee`, 2022-06-22; two commits in all |
| Mathic | `broune/mathic` `66b5d74f8417459414cbf3753cfa9a0128483cbd` (2013-08-27), the head of the upstream the README points through |
| Memtailor | `broune/memtailor` `722a30ce258eb38bee0a834406aed60a06f32d1d` (2013-08-09) |
| Host | macOS 15.7.3 (24G419), `uname -m` = arm64, Apple clang 17.0.0 (clang-1700.6.3.2) |
| Second reference | SymPy 1.13.3 in a scratch virtualenv (not a repository dependency) |

The repository does not pin Mathic or Memtailor; these are the pins chosen here. The tree is a
fork of MathicGB: `code/project/m5gb/` holds the 112 C/C++ files, among them `M5GB.cpp`,
`Reducer_M5GB.cpp` (reducer 27) and `M5GBSigPolyBasis.cpp`. It is run as
`runm5gb M5GB <file> -reducer 27`. One correction to the issue's reading: `code/bench_f101/` holds
198 GF(101) toys (`.ideal`), 11 for each n = 5–22, not 18 at n = 9.

**Installed references on this Mac.** `which Singular msolve sage magma M2` finds none. The
independent references are Zeebra's F4 (`examples/m5gb_paper_reference.rs`, `F4Options::default()`,
one worker) and SymPy's `groebner` over GF(p), used on rows with n ≤ 6.

## 2. Build and licence

**Native ARM64 build: yes, with five build-only changes.** `tools/external/provision-m5gb-paper.sh`
fetches the three trees to `~/.cache/zeebra-external/m5gb-paper/` and compiles them straight into
one binary: Mathic and Memtailor come with autotools, which this host lacks, and their library
source lists are short (`Makefile.am`). Flags are upstream's (`-std=c++14 -O3 -g
-DMATHICGB_NO_TBB`, no `-DNDEBUG`), less `-ggdb`; `g++` becomes `clang++`, and `-Bdynamic`, which
`ld64` lacks, is dropped by linking objects. It takes about 16 s at four jobs.

**The patches are not in this repository.** They are derived from GPL-2.0-or-later code (each
carries upstream context lines), so they live beside the fetched source, in `$M5GB_PATCH_DIR`
(default `~/.cache/zeebra-external/m5gb-paper/patches/`). The repository holds only their SHA-256
digests, `tools/external/m5gb-paper/patches.sha256`. The provisioner exits with status 3 if a patch
is missing or its digest does not match, and each `.build` sidecar records the digest of the
patches it was built with. The descriptions below are enough to recreate each patch. Line numbers
are upstream's, at the pinned commits, before any patch is applied. A recreated patch will match
the committed digest only if it is byte-identical, so a recreation should be recorded as a new
digest, not passed off as the original.

**Build-only patches** (`mathic-build-clang.patch`, `m5gb-build-clang.patch`). None changes
behaviour. They fix what clang rejects and g++ accepted, and the Macaulay2 forks of Mathic and
MathicGB carry the same fixes.

| Patch | Upstream site | clang's complaint | Change |
|---|---|---|---|
| `mathic-build-clang.patch` | Mathic `src/mathic/DivList.h:169-170`, in `DivList<C>::const_iterator` | the two comparison operators that take a `DivList::iterator` by value are defined inline, while `iterator` is still incomplete | keep only their declarations in the class; define both out of line as `DivList<C>::const_iterator` member templates after the `iterator` class closes (after `:222`), with the same bodies |
| | Mathic `src/mathic/Geobucket.h:174`, `Geobucket::Bucket` | `GeoFront`'s default template argument names `Bucket`, which is private at that point | add a `public:` access specifier immediately before the `Bucket` struct |
| `m5gb-build-clang.patch` | M5GB `code/project/m5gb/SPairs.hpp:251-254`, the two `friend` declarations of `constructPairData` and `destructPairData` | unknown type `Index` inside the friend declarations | spell both `Index` parameters of each declaration as `mathic::PairQueueNamespace::Index` |
| | M5GB `code/project/m5gb/MathicIO.hpp:477-489`, `MathicIO::writeTerm` | assignment to the `const Coefficient` parameter `coef` when negating it (`:482`) | copy `coef` into a local at the top of the function, negate the local instead, and use the local in the following `isOne` test and the value write |
| | M5GB `code/project/m5gb/Reducer_M5GB.cpp:45-51`, nested `struct customCompare` in `Reducer_M5GB` | it refers to non-static `mRing` from a nested type | delete the struct; nothing uses it |

**Diagnostic variants**, each built as its own binary with its own `.build` sidecar and record
set, never as the reference. Each patch applies on top of the two build-only patches.

- **`m5gb-hash-narrow.patch`** (§6). In `Reducer_M5GB.cpp`, immediately after each of the two
  places where the reducer computes the hash of the product monomial (`:372` and `:435`), it masks
  the hash to its low 4 bits, so the reducer maps see only 16 distinct keys. `Poly` is untouched.
- **`m5gb-hash-probe.patch`** (§6). Counters only, with no change to behaviour.
  - `MonoMonoid.hpp`: after `MonoVector::end()` (`:1556-1558`), it adds a `const` accessor that
    returns the i-th monomial of the vector in constant time, built from the begin iterator offset by
    i times the monoid's entry count.
  - `Poly.hpp`: in `Poly::append`, in the branch where `occupancyMap` already holds the new
    term's hash (`:114-116`), it counts the merge whenever the stored monomial at that index differs
    from the incoming one. The counter is a function-local static reached through a public static
    accessor added just before the class's `private:` section (`:350`).
  - `Reducer_M5GB.cpp`: beside `irreducibleTermMap` (`:136`) it adds a map from each hash key to
    the exponent vector first seen under it, with a lookup counter and a collision counter. A
    `probe(hash, monomial)` member compares the exponents on every later hit. A call to it goes
    after each of the two hash computations (`:372`, `:435`). Three lines at the end of the
    statistics printout (`:103-109`) print the three counts, labelled `hash-probe lookups:`,
    `hash-probe reducer-map collisions:` and `hash-probe poly-append collisions:`. Those are the
    labels the adapter parses.
- **`m5gb-repair-interreduce.patch`** (§5), 15 changed lines in `M5GB.cpp`. This is a correctness
  change, so it is a different reference.
  - The constructor's pair loop (`:84`) runs to the size of the signature basis `GB` instead of
    the input count.
  - In `interreduce`, where a reduced generator is inserted into the scratch `PolyBasis` (`:130`),
    it inserts the unreduced generator instead when the reduction is zero.
  - After the write-back loop (after `:159`), a slot left empty by a generator that reduced to
    zero is erased from the input vector, and the index is stepped back.

**Licence, read per [`external-provenance-policy.md`](external-provenance-policy.md) §1.**

- **M5GB: GPL-2.0-or-later, asserted in the headers only.** 109 of the 112 files open with
  MathicGB's two-line notice (for example `M5GB.cpp:1-2`). It claims a 2012 MathicGB copyright,
  disclaims warranty, and licenses the file as GPL v2.0 or later, pointing to `LICENSE.txt`. `main.cpp`,
  `rewrite_order.hpp` and `stdinc.h` carry nothing. There is no `LICENSE.txt` and no file matching
  `licen*` or `copying*`, and `README.md` states no licence. The cross-check is MathicGB itself,
  whose 118 headers carry the same sentence over the same missing file (policy §3.2). The
  M5GB-specific files (`M5GB.cpp`, `Reducer_M5GB.cpp`) carry the inherited header unchanged, with
  no separate grant from the M5GB authors. **Class: algorithmic reference only; run as a subprocess.**
  Same as the issue expected, and the same mechanism as MathicGB and Giac.
- **Mathic at the pin: no grant.** No licence file, and one header (`src/mathic/HashTable.h:1-2`)
  that carries MathicGB's sentence. The maintained `Macaulay2/mathic` (`62fe3187`, `README.md:23-30`)
  states LGPL-2.0-or-later for every file. It is built locally as M5GB's dependency, never vendored.
- **Memtailor: BSD-3-Clause** (`license.txt`; `src/memtailor/Arena.cpp:1-2`).

The policy's table carries all three rows.

## 3. Contract and adapter

`tools/external/m5gb-paper/` is standalone: nothing in `src/grobner/external/` changes.

- **Input.** MathicGB's ideal format: `<p> <n> 1 1…1` (one all-ones grading over the default
  `revlex` base order, i.e. grevlex), the generator count, one generator per line, with variables
  as the letters `a…z A…Z`. That caps n at 52.
- **Orders.** Grevlex maps x_i to the i-th letter. Lex is `lex 0`, and MathicGB's lex ranks the
  *last* letter highest (`LexBaseOrderFromRight`), so the adapter writes x_i as letter n − 1 − i.
  This was found by a wrong answer on the first lex row, not assumed. The reader also accepts
  weighted gradings and `schreyer`; neither was tested.
- **No field equations, no Boolean ring.** `M5GB::M5GB` (`M5GB.cpp:59-81`) inserts the
  interreduced inputs and nothing else. The positive-dimensional rows (homogeneous with m < n,
  affine underdetermined, cyclic-4) would get a different reduced basis if field equations were
  added, and all verify.
- **Output is a signature basis, not the reduced basis.** `-outputResult on` writes `<file>.gb`,
  one `index signature  polynomial` line per element. On 171 of the 201 verified upstream rows
  the raw output has more elements than the reduced basis, and only 14 are already reduced. The
  adapter minimizes, interreduces and then checks that **every** raw element reduces to zero
  modulo the result. Without that check, dropping a non-minimal element of a set that is not a
  Gröbner basis could hide a lost generator. That work is part of M5GB's complete-task cost in any
  later timing. Here it is pure Python and recorded per row (`canonical.reduction_steps`,
  `canonical.seconds`), not timed as the reference's.
- **Comparison.** The canonical basis must equal Zeebra's (and SymPy's, where it ran) polynomial
  for polynomial. A planted point is never used as evidence.
- **Caps (declared before the first run).** One process per row, 60 s wall and 4 GiB RSS. macOS
  does not bind `ulimit -v`, so the RSS cap is a watchdog that samples `ps -o rss` every 50 ms and
  kills the process group. Peak RSS is read exactly from `wait4`. The two `rss-cap` rows stopped at
  4097 and 4104 MiB, so the overshoot was under 8 MiB.

## 4. Correctness (unmodified reference)

230 rows (`manifest.json`): the authors' 44 toys with n ≤ 8; 72 dense rows from
`corpus::dense_mq_shaped` at GF(101) (n ∈ {6, 8, 10}, m/n ∈ {1.5, 2, 3}, density 1000 and 500,
seeds 116501–116502, planted and unplanted); 20 larger dense rows at GF(31) and GF(65521)
(n ∈ {12, 14, 16}); 72 controls (redundant, duplicate and zero generators, unit ideals,
homogeneous m ∈ {3, 4, 5, 7} at n = 5, affine underdetermined, sparse, cubic, triangular,
nonradical, monomial, cyclic-4, a single generator, 5 lex rows, and a field sweep); and 2 rows built
on a hash collision (§6). The seeds are fresh: M35's MQ rows use seed = n.

| family | rows | verdicts |
|---|---|---|
| authors' toys | 44 | verified 44 |
| dense, GF(101) and the field sweep | 92 | verified 90, wall-cap 2 (both at p ≈ 2⁶³) |
| dense, n = 12–16 | 20 | verified 20 |
| controls | 72 | verified 46, SIGSEGV 19, wall-cap 4, rss-cap 2, wrong 1 |
| hash collision | 2 | wrong 1, verified 1 |

Every dense row at p < 2³² verifies, planted and unplanted. The unplanted rows are unit ideals,
and M5GB reaches `{1}` correctly when the unit appears *during* the computation. Zeebra and SymPy
agree on every row both answered. The failures are all in §5 and §6.

**Fields.** The product of two residues is formed in `uint64` (`PrimeField.hpp:226`, coefficients
are `long`, `PolyRing.hpp:92`), so the arithmetic is exact only for p < 2³². The sweep stops at the
limit it found:

| p | rows | verdicts |
|---|---|---|
| 31, 32003, 65521 | 11 each | verified 9, SIGSEGV 2 (§5) |
| 101 | 95 | verified 88, SIGSEGV 7 (§5) |
| 2147483647 | 9 | verified 7, SIGSEGV 2 |
| 4294967291 (largest prime < 2³²) | 9 | verified 7, SIGSEGV 2 |
| 4294967311 (smallest prime > 2³²) | 9 | verified 6, SIGSEGV 2, **wrong 1** (cyclic-4) |
| 9223372036854775783 | 9 | wall-cap 6, rss-cap 2, verified 1 (the triangular toy) |

Past 2³² the first products that overflow give a wrong basis, and near 2⁶³ almost nothing
terminates. **The widest admissible field is p < 2³², up to 4294967291.** GF(2) was not tested.

## 5. Zero inputs crash the preprocessing

**Unmodified, every input whose initial interreduction produces a zero crashes**: duplicate and
redundant generators, a zero generator, and a unit ideal visible in the input (a constant, `{x, x − 1}`,
`{f, f + 1}`). That is all 19 SIGSEGV rows, at every field. Crash reports from the `-g` build place
them in M5GB's own preprocessing, not in MathicGB:

- `M5GB::interreduce` (`M5GB.cpp:91-165`) moves each input out of its slot (`:135`) and writes it
  back only when its reduction is nonzero (`:146-150`). A generator that reduces to zero leaves a
  null slot, and the next round dereferences it (`:122`). The same loop inserts a zero into a
  `PolyBasis`, which cannot hold one, when an *other* generator reduces to zero (`:129-131`).
- A zero generator survives `interreduce` (it prints a diagnostic that an input polynomial is null), but the pair
  loop runs over the input count, not the basis size (`M5GB.cpp:84`), and reads past the end of the
  basis.

**A repair, kept as a separate result set.** `m5gb-repair-interreduce.patch` is 15 changed lines:
drop an empty slot, keep the unreduced generator when its reduction is zero, and loop over
`GB->size()`. With it, all 58 controls at p < 2³² verify, unit ideals included
(`runs-repair-interreduce.jsonl`). It is a correctness change to the reference, so its rows are
**never** pooled with the unmodified ones, and an arm built on it would be "M5GB with a #1165
repair", not the authors' code. For a cohort of dense MQ rows the question does not arise: none of
the 112 dense rows triggers it.

## 6. The hash-key concern

The concern was that caches keyed by a monomial's hash could hand back a result for a different
monomial. **It is real, at three sites, and one of them is demonstrated on the unmodified build.**

**The hash.** `computeHash` (`MonoMonoid.hpp:1882-1893`) is the dot product of the exponents with
coefficients drawn by `srand(0); rand()` (`:233`), truncated to the 32-bit exponent type
(`PolyRing.hpp:90`). It is linear, so a colliding pair stays colliding under multiplication by any
monomial, and the coefficients depend on the C library: a collision on macOS is not one on glibc.
MathicGB's own reducer table compares monomials after the hash (`PolyHashTable.hpp:59-67`). The
three M5GB-specific sites do not:

1. **`Poly::append`** (`Poly.hpp:112-133`, map at `:355`, keyed by `unsigned int`) merges a term
   into any earlier term with the same hash and drops its monomial. Every polynomial goes through
   it, the input parser included (`MathicIO.hpp:412`).
2. **`irreducibleTermMap`** (`Reducer_M5GB.cpp:136`; read at `:374`, `:462`; written at `:199`,
   `:410`, `:519`) marks a term irreducible. At depth 0 a hit returns `nullptr` (`:377-380`), which
   `processSPair` reads as a singular reduction and discards (`M5GB.cpp:240-243`).
3. **The store `M`** (`Reducer_M5GB.cpp:144`; `:384-390`, `:437-456`, `:567-569`) holds reduced
   multiples, and a hit is used as the reduction of the term looked up.

**Demonstration.** `hash_collision.py` finds colliding pairs under this host's `rand()`. The first,
at n = 12, is x1·x7³·x8²·x9 and x3·x5²·x10·x11·x12², both of degree 7. The input
`x1*x7^3*x8^2*x9 + x3*x5^2*x10*x11*x12^2` comes back as the basis `{x1*x7^3*x8^2*x9}`: the parser
merged the two terms. Zeebra's answer is the input. **Verdict: wrong, silently, exit status 0**,
on the unmodified build and on the repair build alike. Putting the two monomials in different
generators (`collision-separate`) verifies.

**Forced collisions.** `hash-narrow` cuts the reducer-map keys to 4 bits and leaves `Poly` alone.
Of 150 rows at GF(31) and GF(101), 137 crash with SIGSEGV and 4 exit 255 after Mathic reports a
duplicate entry inserted into its KD tree. The 8 that verify make at most 18 reducer-map lookups in the probe run, and
the one other row (`nonradical-lex`, 18 lookups) comes back **wrong**. So the two maps take
whatever the key returns.

**How likely is it unforced?** The hash is linear, so the birthday estimate is wrong for it. A
collision is a lattice vector, and on this host the smallest has degree 7 at n = 12 and degree 6–7
at n = 16, with none up to degree 9 at n = 10 or degree 12 at n = 8
(`collisions-darwin-arm64.jsonl`). The `hash-probe` build records, per row, every lookup whose key
was first seen with a different monomial. Over its 212 rows (every upstream row at p < 2³²; wall
cap raised to 300 s because the probe is slower) it made **776 M reducer-map lookups with no
collision**, 224 M of them on the n = 16, m = 32 row. The only collision anywhere is the
constructed parser row. Its verdicts match upstream's row for row.

**Reading.** The collision risk is a property of n and the degrees reached, not of the field. On
the dense rows here it did not fire, and verification catches it when it does, as the demonstration
shows. A repair would key the maps and `occupancyMap` by the monomial, a change of the same size as
§5's. It was not made: verification already isolates the failure, and a repaired build would be a
third reference to keep apart.

## 7. Development measurements

Laptop, unpinned, one worker, one repetition. "M5GB s" is the process wall, including writing its
signature basis and `.stats`, and excluding the adapter's canonicalization. "Zeebra s" is
`F4Options::default()` in process, from the reference run on the same row.

| row | M5GB s | Zeebra s | M5GB peak RSS MiB | raw elements | raw terms | verdict |
|---|---|---|---|---|---|---|
| n10 m15 GF(101) planted | 0.30 | 0.05 | 71 | 275 | 30 684 | verified |
| n10 m20 GF(101) planted | 0.13 | 0.02 | 44 | 170 | 11 019 | verified |
| n12 m18 GF(31) planted | 4.62 | 0.92 | 237 | 686 | 179 065 | verified |
| n12 m24 GF(31) planted | 0.56 | 0.11 | 87 | 352 | 45 792 | verified |
| n12 m36 GF(31) planted | 0.13 | 0.01 | 51 | 190 | 13 661 | verified |
| n14 m28 GF(31) planted | 3.72 | 0.57 | 352 | 686 | 181 714 | verified |
| n14 m42 GF(31) planted | 0.44 | 0.04 | 94 | 307 | 37 611 | verified |
| n16 m32 GF(31) planted | 25.75 | 16.07 | 923 | 1 271 | 644 543 | verified |
| n16 m48 GF(31) planted | 1.66 | 0.95 | 218 | 515 | 98 799 | verified |
| n12 m18 GF(65521) planted | 4.56 | 1.00 | 232 | 686 | 185 020 | verified |
| n14 m28 GF(65521) planted | 3.74 | 0.61 | 411 | 686 | 187 925 | verified |
| n16 m32 GF(65521) planted | 24.05 | 17.17 | 921 | 1 271 | 666 118 | verified |

- **M5GB is slower than Zeebra on every dense row**: 1.4–1.7× at n = 16, 4.6–6.5× at n = 12–14,
  and up to 10× where both are small. Field width barely moves it (GF(31) against GF(65521)).
  Unplanted rows cost the same as planted ones.
- **Against #1030's M4GB this is far slower.** At (n, m) = (16, 32) and GF(31), M4GB took 0.51 s
  on the same Mac ([`m4gb-m5gb-reference.md`](m4gb-m5gb-reference.md) §5.1, seeds 1–2; M4GB's
  counters do not depend on the seed, §9). M5GB takes about 50× that. The paper's prototype is a
  signature-based Buchberger, one S-pair at a time: 616 462 S-pairs reduced at (16, 32).
- **Work counters** (from its stdout; all in the records): at (16, 32), 1 271 basis elements,
  807 085 S-pairs considered, 558 205 reductions, a store `M` of 6 300 reduced multiples
  (`Entry count`) and 903 M term merges (`Actual reductions`). Its `Approximated memory consumption
  … MB` line divides bytes by 1024 once, so the unit is KiB (16 755 KiB here). The adapter's
  canonicalization of that output took 166 s of pure Python: an F4-quality interreduction would be
  needed before this cost could be charged fairly.

## 8. Eligibility decision

**Conditionally eligible as a #1030-style arm**, with the conditions part of the arm's definition:

1. **Fields and orders:** odd primes p < 2³², grevlex (lex verified on small controls only). The
   largest verified prime is 4294967291.
2. **Inputs:** no zero, duplicate or redundant generator and no unit visible in the input
   (unmodified, these crash, §5). A cohort that contains them must record the crash as a
   capability failure, or use the repair as a separately named arm.
3. **Verification is mandatory, not a courtesy.** The raw output is a signature basis, so the
   adapter's canonicalization is part of the complete task and must be timed with it. The three
   hash-keyed sites (§6) can return a wrong basis with exit status 0, so an unverified M5GB timing
   is never publishable.

**What it does not do:** support #1032. The issue asked whether R-m5 has anything behind it on
ordinary prime-field ideals. On this evidence the paper's implementation is 1.4–10× slower than
Zeebra's shipping F4 and about 50× slower than M4GB on the shapes measured, so its signature-aware
reductors show no performance case on this family. That is development evidence on one laptop. It
does not change #1032's gate, which needs a route-specific mechanism and transfer argument in any
case.

## 9. What is left

- **Bench host (not done here):** a qualification run under `docs/guide/benchmarking.md`, with
  pinned CPUs and its own allocation, against grobx and the best qualified Zeebra configuration.
  That needs its own allocation or substitution decision; it is not M35 time by default. The
  hash-collision pairs must be recomputed there with `hash_collision.py`, because glibc's `rand()`
  differs from macOS's.
- **Not done, by the stop rule:** a repair of the hash-keyed caches (§6), and fields beyond
  p < 2³², which would mean rewriting the arithmetic.

## 10. Reproduce

The commands are in [`research/1165-m5gb-paper-reference/README.md`](../../research/1165-m5gb-paper-reference/README.md).
`python3 research/1165-m5gb-paper-reference/summarize.py {verdicts,fields,dense,probe}` prints
this note's tables from the records.
