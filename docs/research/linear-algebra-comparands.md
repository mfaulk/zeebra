# Linear algebra against FFLAS-FFPACK, SpaSM, M4RI and FLINT (#1209, laptop stage)

**Status:** laptop development stage, 2026-11-28. The harness, the provisioning and the
verification are done. The pinned 1- and 16-worker read is left for the bench host (§7).
**Measured at:** `05006dd8`. The Zeebra binary (`examples/linalg_comparands`) and all four drivers
come from that commit. The run used the matrix-size caps that the next commit on the branch writes
into `tools/external/linalg-comparands.py`, and that commit changes nothing else.
Build: the repository's release profile (fat LTO, one codegen unit), `RUSTFLAGS` unset. The drivers
are built at `-O3` by Apple clang 17.
**Host: Apple M4 Pro laptop (14 cores, 48 GB), macOS 15.7.3, unpinned.** Another agent was building
on the same machine throughout. The 1-minute load was 3.65 at the start and 3.88 at the end.
**Every timing here is an unpinned laptop development figure. None is a deciding measurement**, and
none satisfies `docs/research/external-comparison-protocol.md`. Read them as ratios between arms of
one session. Treat any ratio within 1.5× as unresolved.
**Data:** [`research/1209-linalg-comparands/`](../../research/1209-linalg-comparands/): `laptop.tsv`
(medians of 3), `laptop-verify.txt` and `drivers.txt`.

## 1. Question

Zeebra's linear algebra had been measured only from inside Gröbner engines, so the share of each
end-to-end gap that belongs to elimination was inferred rather than measured. This note measures
it on matrices, against four linear-algebra libraries. Each library runs as a separate process
on exported files. None is linked into Zeebra (`external-provenance-policy.md` §7).

## 2. Harness

- **Export.** `linalg_comparands export <corpus-label>` captures an F4 batch from the matrix corpus
  (`f4-matrix-corpus.md`) and writes it as SMS, reducer rows first. The `.meta` sidecar records the
  prime and the reducer split. `synthetic` writes dense and uniformly sparse matrices (6 nonzeros
  per row) from a seeded splitmix64.
- **Drivers.** `tools/external/linalg-drivers/` holds one small MIT program per library, with a
  shared protocol (`common.h`):
  - FLINT `nmod_mat_rref` / `nmod_mat_mul`;
  - M4RI `mzd_echelonize(full)` / `mzd_mul`;
  - FFLAS-FFPACK `ReducedRowEchelonForm` (PLUQ) / `fgemm`, with `pReducedRowEchelonForm` and the
    parallel `fgemm` above one thread;
  - SpaSM `spasm_echelonize` + `spasm_rref`.
- **Provisioning.** `tools/external/provision-linalg.sh` builds M4RI 20260122, Givaro 4.2.2,
  FFLAS-FFPACK 2.5.0 and SpaSM `09c40943` from pinned sources (sha256 checked) and builds the
  drivers. FLINT 3.6.0 and GMP come from Homebrew on macOS and from `provision.sh`'s prefix on
  Linux. BLAS is OpenBLAS, held at one thread.
- **Zeebra arms** (`linalg_comparands rref`):
  - `f4`: the shipped forward kernel (`Backend::Adaptive` at one worker, `concurrent::Dispatch`
    above it), with the reducer block taken as pivots, then `RowForm::Reduced`'s back-substitution;
  - `lane`: #945/#1183's `u32` lane plus the same back-substitution;
  - `blocked`: #1193's recursive dense echelon, for p ≤ 46 337;
  - `gf2`: packed Four Russians, k = 8;
  - `matrix`: `gauss_jordan_elimination`, the path behind `Matrix::rank`.
  - Products use `&Matrix * &Matrix` and the `blocked` product.
- **Verification before timing.** Every arm runs once. Its rank and the FNV digest of its canonical
  RREF (or of the product) must equal the first arm's, or the script exits 1 before it times
  anything. SpaSM picks its own pivots and returns the RREF of A·Q. The driver detects when that is
  not the canonical form, and `linalg_comparands canon` then reduces it outside the timed region.
  **All 46 tasks agreed** (`laptop-verify.txt`). The Rust and C digests are pinned against each
  other in `digests_match_the_c_drivers`.
- **Timing.** Each cell is its own process. Cells are interleaved within each of 3 repetitions, and
  the median is reported. Only the library call is timed, not I/O or conversion. Zeebra's RREF
  figure includes the back-substitution, because every comparand produces a full RREF.

## 3. F4 corpus batches: elimination is not where Zeebra trails

Median ms. Ratios are the comparand ÷ Zeebra's best arm at the same worker count. Above 1, Zeebra
is faster.

| Batch (shape) | Zeebra best @1 | SpaSM @1 | FLINT @1 | FFLAS @1 | Zeebra f4 @4 | SpaSM @4 |
|---|---:|---:|---:|---:|---:|---:|
| katsura-7 grevlex m31 default (361×369) | 0.9 ms | 5.4 ms (6×) | 7.6 ms | 12.8 ms | 0.8 ms | 1.7 ms (2.1×) |
| cyclic-6 lex m31 default (1026×1048) | 2.1 ms | 23.2 ms (11×) | 139 ms | 251 ms | 2.2 ms | 5.9 ms (2.7×) |
| mq-random-6 grevlex p31 baseline (3305×3342) | 8.2 ms | 407 ms (50×) | 3 504 ms | — | 8.0 ms | 102 ms (13×) |
| katsura-7 grevlex m31 baseline (6810×6862) | 15.1 ms | 1 662 ms (110×) | 26 002 ms | — | 14.5 ms | 425 ms (29×) |
| mq-random-10 grevlex p31 default (12391×12020) | 637 ms (lane) | 8 678 ms (14×) | — | — | 539 ms | 2 288 ms (4.2×) |
| katsura-6 lex p64 baseline (1954×945) | 7.0 ms | — | 309 ms (44×) | — | 3.7 ms | — |
| cyclic-7 grevlex GF(2) default (1146×795) | 0.8 ms (gf2) | — | 85 ms | 18.3 ms | — | — |

- **On every prime-field batch, Zeebra's shipped kernel is 6–110× ahead of SpaSM at one worker**,
  and further ahead of the dense tools, which pay the full cubic cost on sparse batches.
- SpaSM's figure is dominated by `spasm_rref`. On mq-random-10, `spasm_echelonize` alone took
  1.13 s in the verification run, still above Zeebra's full RREF of 0.78 s.
- The `f4` arm is helped by its input: it receives the reducer split, which SpaSM has to rediscover
  through its structural pivot search. That is the shape F4 hands its eliminator, so the comparison
  is the one that matters for F4. It is not a claim about general sparse matrices (§4).
- **GF(2):** M4RI is 0.5 ms against Zeebra's packed route at 0.8 ms (1.6×), within the noise band.
- **Workers:** four workers buy Zeebra nothing on the small batches and 1.44× on mq-random-10.
  SpaSM scales 3–4×, which narrows its gap without closing it.

**What this says about the end-to-end gaps** (2.5–7× at 31 bits, 18–36× on dense small-prime MQ,
M35 baseline, PR #1175): on the batches this corpus pins, elimination against these libraries
does not account for the gaps. That is consistent with
[`f4-matrix-corpus.md`](f4-matrix-corpus.md) §0 and points at work volume and the other stages, as
#1193 concluded for dense MQ (§8 there: the gap is in how much work there is, #1080, not in the
arithmetic). **The share itself is not measured here.** It needs the #1033 dense-MQ captures and
per-batch attribution of a full solve, both on the bench host (§7).

## 4. Synthetic matrices: where Zeebra is behind

Median ms at one worker. Ratios are Zeebra's best arm ÷ the best comparand, so above 1 Zeebra is
behind. (`—` means the arm or tool does not apply.)

| Matrix | Zeebra f4 | lane | blocked | best comparand | Zeebra best ÷ it |
|---|---:|---:|---:|---|---:|
| dense 1000², p = 32003 | 302 ms | 50 ms | 38 ms | FFLAS 29 ms | 1.32 |
| dense 2000², p = 32003 | 2 311 ms | 331 ms | 230 ms | FFLAS 146 ms | 1.58 |
| dense 2000², p = 65521 | 2 307 ms | 466 ms | — | FFLAS 143 ms | 3.25 |
| dense 2000², 2³¹ − 1 | 2 017 ms | 494 ms | — | FLINT 842 ms | 0.59 |
| dense 2000², BabyBear | 2 358 ms | 509 ms | — | FLINT 840 ms | 0.61 |
| dense 2000², 2⁶⁴ − 59 | 3 195 ms | — | — | FLINT 1 032 ms | 3.10 |
| dense 4000², GF(2) | 4 037 ms | — | — (gf2 41 ms) | M4RI 11.7 ms | 3.5 (gf2) |
| sparse 4000², p = 32003 | 2 417 ms | 404 ms | 1 262 ms | FFLAS 1 089 ms | 0.37 |
| sparse 4000², 2³¹ − 1 | 2 134 ms | 606 ms | — | FLINT 6 157 ms | 0.10 |
| sparse 4000², GF(2) | 526 ms | — | — (gf2 20.6 ms) | M4RI 20.7 ms | 1.0 (gf2) |

- **The shipped F4 kernel on a dense matrix is 16× behind FFLAS-FFPACK** (2000², p = 32003). The
  `u32` lane closes it to 2.3×, and #1193's blocked prototype to 1.6×. This is the dense-residual
  class that #1193 and #1196 target, and the lane is opt-in (#1123).
- **At 65521 the lane is 3.25× behind FFLAS**, against 2.3× at 32003. 65521 is above
  `MAX_LANE_PRIME`, so it takes the 31-bit lane's wider accumulator. FFLAS is unchanged, because
  both primes are below 2²⁶ in `Modular<double>`.
- **At 31 bits the lane is ahead of both comparands** (0.59–0.66× of FLINT). FFLAS falls back to
  `Modular<int64_t>`, off its BLAS path, and is 1.9× slower than FLINT here. On the bench host's
  x86-64 that path has SIMD that arm64 lacks, so this ranking must be re-read there.
- **64-bit primes** have no lane. The `f4` arm is 3.1× behind FLINT at one worker and 2.5× at four.
- **GF(2) dense:** Zeebra's packed route is 3.5–4× behind M4RI, as #272 anticipated. At 4000²,
  sparse, they are level.
- **Workers:** at four workers the `f4` arm gains about 3.2× on dense inputs. The lane and blocked
  arms have no parallel route, so at four workers FLINT and FFLAS lead every dense row.

## 5. General-purpose `Matrix` operations

These are the routines a library caller reaches. Median ms at one worker. `Matrix` has no parallel
route.

| Operation | `Matrix` | best comparand | ratio |
|---|---:|---:|---:|
| rank (Gauss–Jordan), 1000², p = 32003 | 678 ms | FFLAS 29 ms | 23× |
| rank, 1000², 2³¹ − 1 | 629 ms | FLINT 118 ms | 5.3× |
| rank, 1000², 2⁶⁴ − 59 | 947 ms | FLINT 146 ms | 6.5× |
| product, 1000², p = 32003 | 356 ms | FFLAS 42 ms | 8.5× |
| product, 1000², 2³¹ − 1 | 315 ms | FLINT 258 ms | 1.22× |
| product, 1000², 2⁶⁴ − 59 | 1 355 ms | FLINT 313 ms | 4.3× |
| product, 2000², GF(2) | — (`blocked` 262 ms) | M4RI 2.9 ms | 90× |

- **Far enough behind to matter to a caller:**
  - `Matrix::rank`, `inverse` and `determinant` all go through generic row-at-a-time elimination,
    5–23× behind;
  - the small-prime product is 8.5× behind, where `blocked::multiply` already matches FFLAS at
    0.69–0.95× (500²–2000²);
  - Zeebra has no packed GF(2) product.
- **Close enough to leave alone:** the 31-bit product (1.2×).
- These are candidates to file once the bench host confirms the ratios. They are not filed from
  laptop figures.

## 6. Caveats

- **FLINT is built without BLAS**, both from Homebrew and in `provision.sh`. Its `nmod_mat` is
  therefore not at its best on small primes, where it is 3–4× behind FFLAS. A BLAS-enabled FLINT is
  a bench-host option, but not a pinned one.
- **M4RI is built without OpenMP**, upstream's default, so it has only a one-thread arm.
- **SpaSM cannot run GF(2).** Its dense fallback asserts p ≥ 3 in Givaro's `ModularBalanced<float>`.
- **Size caps.** Dense comparands stop at 50 M cells: FLINT took 148 s on mq-random-10 at one
  thread. FFLAS above 2²⁶ stops at 5 M cells: it did not finish mq-random-10 in 5 minutes.
  `Matrix` stops at about 1000², where its cubic generic path costs seconds.
- **Workers.** "Four workers" means four OpenMP or FLINT threads for the comparands and four
  `concurrent` workers for Zeebra's `f4` arm, on an unpinned machine under load.

## 7. Left for the bench host

- **The pinned read.** It runs `tools/external/linalg-comparands.py --set bench --workers 1,16`
  inside `tools/bench-job.sh`. The bench set takes dense sizes to n = 8000, as #1209 asks. Each
  comparand also needs a default-thread arm, on top of the one-thread arm.
- **Provisioning on Linux.** `provision-linalg.sh`'s Linux branch (OpenBLAS by pkg-config, FLINT
  from `provision.sh`'s prefix) has not been run.
- **The #1033 dense-MQ captures** (n = 18, 20 at GF(31) and GF(32003)). They are the batches where
  §4's dense gap would bite. Exporting them needs the archive route of `f4-matrix-files.md`, which
  this harness does not yet read.
- **The per-batch share of each end-to-end gap**, the one deliverable of #1209 that a matrix-only
  run cannot give.
