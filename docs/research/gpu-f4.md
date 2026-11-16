# GPU F4: the Type V record, and whether Zeebra's matrices give a dense kernel anything to do

**Measured at:** `8dbf9bcf` plus this change's `examples/block_density.rs` (#225). Every figure in
§3 is an exact count — shapes, nonzeros, ranks, multiply-adds — not a timing, so it does not depend
on load, pinning or the benchmark lock, and it reproduces from
`cargo run --release --example block_density` (and `-- large`) at any commit where the pinned F4
matrix corpus has not moved; the corpus verifies its own digests before anything is measured. Raw
output: [`research/gpu-f4/block-density-default.md`](../../research/gpu-f4/block-density-default.md)
and [`research/gpu-f4/block-density-large.md`](../../research/gpu-f4/block-density-large.md). The
large capture took 2 min 22 s wall and 1.83 GB peak RSS, as an unpinned single run; that is a cost
note, not a benchmark.

This is #225, a child of #69. #86's reconciliation comment of 2026-11-13 already settles the
programme-level position — no GPU implementation is scheduled, and each GPU proposal needs a
specific reachable public input and a measured multicore CPU baseline first. This document adds
the two things #225 owns: what the published record does and does not establish, and a tile-level
density measurement that can falsify or narrow the dense-kernel direction cheaply.

---

## 1. The record, as published

Read 2026-11-15 from <https://www.mqchallenge.org/> and its two Type V detail pages. Verbatim
fields:

| | 2026/09/17 | 2023/08/22 (previous Type V record) |
|---|---|---|
| Names | "Ting Li, Yao Sun" | "Ting Li, Yao Sun" |
| m, n | 21, 31 | 20, 30 |
| Algorithm | "Improved F4 via smaller matrices" | "Improved F4 algorithm for similar polynomial systems" |
| Hardware | "2 x RTX 5090 (32 GB each), 16 CPU threads (Intel 6530, 2.1 GHz), 256 GB RAM" | "1 x AMD Ryzen Threadripper 3970X, 192GB RAM, 2 x GeForce RTX 3080Ti" |
| Running time | "722,188 seconds (8 days 8 hours 36 minutes)" | "21.72 days (Total wall-clock time)" |
| Variables fixed | "We randomly assigned values to 11 variables" | "We guessed 11 variables" |
| Subsystems | "A verified solution was found after completing 80 instances", about 9,027 s each | "A solution was found after solving 245 subsystems", 15,319 s average |
| What the GPU did | "Each instance was processed using 16 CPU threads and two NVIDIA GeForce RTX 5090 GPUs." | "the elimination is effectively accelerated by GPUs." |
| Matrix claim | "We used a modified F4 algorithm that constructs more compact matrices" | "takes advantage of more memory and the sparsity of matrices when eliminating matrices" |
| References | none | none |

The 2026 page says the algorithm will be described "in a future paper". **No paper, preprint or
talk was found** (searched: IACR ePrint abstract pages, the CHES/TCHES 2026 accepted lists — whose
only Li and Sun paper is an S-box circuit result — arXiv 2026 F4 papers, and the authors' pages;
DBLP was unreachable). Earlier Li–Sun work found is on GVW, not F4, and is not claimed as the basis.
Sakata–Takagi (TCHES 2026, ePrint 2023/1650), which is behind the **Type VI** record, reports
single- and multi-core runs and no GPU; it is not this method.

### 1.1 What the pages do establish

The arithmetic on the pages is self-consistent, and it settles the workload's shape even without a
paper:

- 80 × 9,027 s = 722,160 s against the reported 722,188 s, so the 2026 instances ran **one at a
  time, each on the whole machine**. 245 × 15,319 s / 2 = 21.72 days, matching the 2023 report's two
  concurrent single-thread processes.
- Fixing 11 of 31 variables leaves **21 equations in 20 variables over GF(2^8)** per instance — a
  square-plus-one system, many medium problems rather than one large one. That agrees with #197's
  field-then-shape analysis (PR #617) that signature-shape records are many medium slices.
- An instance run as m = 21, n = 20 succeeds with probability around 1/256 for one overdetermining
  equation, so 80 and 245 instances are both ordinary draws for a guess-and-solve loop.

### 1.2 What they do not establish

- **Where the 2026 GPUs work.** The 2023 page says the elimination; the 2026 page says only that
  each instance used them. Inferring that the 2026 GPUs still echelonize is reasonable and
  **unconfirmed**.
- **What "smaller" or "more compact" matrices means.** Nothing on either page says whether it is
  fewer rows by a criterion, a degree or Hilbert cap, fewer columns, or a reuse across "similar
  polynomial systems" — the phrase the 2023 algorithm name used, which suggests sharing structure
  across the guessed subsystems. Per #69's rule, the mechanism is recorded as **unknown**, not
  inferred from the algorithm string. There is therefore nothing algorithmic to hand to #74 (B1,
  closed) yet.
- **Whether the GPU or the algorithm made the record.** Between 2023 and 2026 the system grew by
  one variable and one equation and the per-subsystem time fell from 15,319 s to 9,027 s, while the
  hardware changed from two single-thread processes with RTX 3080 Ti cards to sixteen threads per
  instance with RTX 5090s. Algorithm, CPU parallelism and GPU generation all moved at once, so the
  two records cannot separate them. #69's closing requirement — say whether a benefit comes from
  algorithm, parallelism, memory or hardware — cannot be met from these sources.

## 2. Zeebra's reach

Zeebra can now build a GF(2^8) MQ system: `Gf256Mq` (modulus 0x11D) is exported beside AES
`Gf256` (0x11B), which retires #225's "cannot construct a Type V instance" gap. Two gates remain:
external verification of extension-field answers lacks an agreed defining-polynomial convention
with Singular (#86 comment), and the pinned matrix corpus has **no random-MQ entry over GF(2^8)** —
its GF(2^8) entries are cyclic systems. The challenge instances themselves and their tooling stay
outside this library (#668).

## 3. Tile density of the matrices F4 really builds

`examples/block_density.rs` walks the pinned corpus (`src/grobner/f4/matrix_corpus.rs`,
`docs/research/f4-matrix-corpus.md`): the largest batch of each entry, as F4's live path built
it, digest-checked. It replaces the issue's proposed `elimination_density` run because that
example's fixed list is katsura and cyclic only, while the corpus also covers random MQ, the
default and baseline presets, and GF(2) and GF(2^8). Classical, random MQ and small-characteristic
classes are covered; **structured CICO is not**, since no CICO system is in the corpus and that
tooling moved out with #668.

Two matrices per entry, tiled 64 × 64 — the warp-sized block `elimination_density.rs` already used
— with a tile "dense" when at least half full:

- **As built**, in the `[A B; C D]` arrangement `ReductionStrategy::Structured` eliminates:
  reducer rows first, ascending by leading column, then pair rows.
- **The pair-row residual `D' = D − C A⁻¹ B`**, on the columns no reducer leads: what the
  Faugère–Lachartre split would hand a dense kernel after a sparse triangular sweep on the CPU.
  Before and after its own echelon, since that echelon is where fill-in happens.

### 3.1 As built: nothing for a dense tile kernel

| entry | rows × cols | density | max tile | nz in dense tiles |
|---|---|---:|---:|---:|
| katsura-7/grevlex/m31/default | 361 × 369 | 7.9% | 17.7% | 0.0% |
| katsura-7/grevlex/m31/baseline | 6810 × 6862 | 0.2% | 29.7% | 0.0% |
| katsura-6/lex/m31/baseline | 1954 × 945 | 3.5% | 52.2% | 2.5% |
| cyclic-6/grevlex/m31/default | 159 × 175 | 23.5% | 46.7% | 0.0% |
| mq-random-6/grevlex/p31x64/default | 757 × 756 | 2.8% | 25.1% | 0.0% |
| mq-random-10/grevlex/p31x64/default | 12554 × 12020 | 0.5% | 35.2% | 0.0% |
| mq-random-14/grevlex/p31x64/default-64m | 75091 × 76194 | 0.4% | 46.1% | 0.0% |
| cyclic-7/grevlex/gf2/default | 1146 × 795 | 9.3% | 30.4% | 0.0% |
| cyclic-6/grevlex/gf256/default | 130 × 163 | 10.9% | 17.7% | 0.0% |

Representative rows; the raw file has all eighteen entries. **Across every entry one tile in the
whole corpus is half full**, and it holds 2.5% of one matrix's nonzeros. A dense kernel handed the
Macaulay matrix as built would spend nearly all its arithmetic on zeros. This is the result #58's
structural argument predicts, and it is now a measurement over real matrices.

### 3.2 After the sparse sweep: the residual is dense, and it is the larger share of the work

| entry | D' rows × cols | D' density | nz in dense tiles | rank | echelon density |
|---|---|---:|---:|---:|---:|
| katsura-7/grevlex/m31/default | 98 × 106 | 67.0% | 59.1% | 43 | 69.5% |
| katsura-6/lex/m31/baseline | 1126 × 117 | 40.1% | 93.0% | 86 | 40.1% |
| cyclic-6/grevlex/m31/default | 102 × 118 | 52.4% | 72.7% | 55 | 51.6% |
| mq-random-6/grevlex/p31x64/default | 98 × 97 | 68.7% | 68.7% | 39 | 75.3% |
| mq-random-10/grevlex/p31x64/default | 1468 × 934 | 43.9% | 86.1% | 579 | 52.3% |
| mq-random-14/grevlex/p31x64/default-64m | 7680 × 8783 | 63.1% | 90.8% | 3504 | 65.2% |
| cyclic-7/grevlex/gf2/default | 774 × 423 | 25.1% | 21.8% | 267 | 27.6% |
| cyclic-6/grevlex/gf256/default | 80 × 113 | 24.2% | 0.0% | 44 | 24.7% |

Multiply-adds, from the same run: the sparse sweep's count is exact (one per reducer entry
applied); the dense count is what a dense echelon of `D'` performs at its measured rank,
`Σ_k (rows − k − 1)(cols − k − 1)` — the work a tile kernel would execute whatever `D'`'s
sparsity, and an **upper bound** on what Zeebra's sparse backends do on the same block.

| entry | sweep multiply-adds | dense `D'` echelon multiply-adds | dense share |
|---|---:|---:|---:|
| katsura-7/grevlex/m31/default | 272,854 | 281,134 | 50.7% |
| mq-random-6/grevlex/p31x64/default | 576,733 | 239,174 | 29.3% |
| mq-random-6/grevlex/p31x64/baseline | 1,354,377 | 28,720 | 2.1% |
| mq-random-10/grevlex/p31x64/default | 269,509,492 | 455,423,258 | 62.8% |
| mq-random-14/grevlex/p31x64/default-64m | 34,940,392,155 | 149,608,384,160 | 81.1% |
| cyclic-7/grevlex/gf2/default | 865,179 | 50,970,478 | 98.3% |

What this shows:

1. **The dense-sub-block reading of #225 question 2 is the live one, and the full-matrix reading
   is not.** Once the reducer block is swept out, the residual is 40–90% dense over prime fields
   and the dense tiles carry 60–95% of its nonzeros. Fill-in during its echelon is small (density
   moves a few points), so the residual is dense from the start rather than becoming dense.
2. **The dense share grows with the instance.** On random MQ it goes from 29% (n = 6) to 63%
   (n = 10) to 81% (n = 14) of the multiply-adds in the dense model. The baseline preset reverses
   it (2.1% at mq-random-6): `F4Options::default()`'s smaller matrices leave a residual that is a
   larger fraction of less work. Zeebra's own matrix reduction therefore *raises* the dense share
   rather than lowering it.
3. **The blocks are small for a GPU.** The largest residual, mq-random-14's, is 67.5 M cells:
   270 MB at four bytes a cell, under 1% of one 32 GB card. Every other residual is under 1.4 M
   cells, a size at which host–device transfer and launch overheads would dominate any device. Only
   the n = 14 rung is in the regime where a device kernel could plausibly amortize its transfer.
4. **GF(2) and GF(2^8) residuals are sparser** (24–28%) on the cyclic systems the corpus holds, but
   the dense model still puts 97–98% of the multiply-adds there, because those residuals are wide
   relative to their sweep. Whether a GF(2^8) *random MQ* residual — the record's actual shape —
   looks like the prime-field MQ rows or like these cyclic rows is not measured; the corpus has no
   such entry.

The counts compare a sparse sweep with a dense echelon model, not two measured times. Zeebra's
shipped elimination does the `D'` part sparsely and does fewer multiply-adds than the dense count
whenever `D'` has zeros, so §3.2's shares are **not** a CPU time split and support no speedup
figure.

## 4. The prior a GPU proposal must address

From `docs/MILESTONE-SIMD-PARALLELISM.md` §8.2–§8.4, unchanged: the scalar elimination kernel is
**ALU-bound**, flat to within 7% in ns/entry over working sets spanning four orders of magnitude,
at 15.9 GB/s; only the eight-lane AVX2 kernel reaches the bytes (45 GB/s in cache, 26.9 GB/s out);
and `Backend::Adaptive`, the shipped default, gains **0.98×–1.04×** from halving the field width
because its cost is sparse-index traversal and scatter/gather, not cell traffic.

§3 refines where that prior applies. It applies to the sweep — the `C A⁻¹ B` phase is exactly the
index-traversal-bound work, and it stays on the CPU under any split. It does not decide the
residual, which is a dense block where cell throughput, not index traversal, is the cost — the
regime where §8.3's lane win existed and where a device's throughput is relevant. #149's negative
shipping decision is about the full-matrix `Backend::Dense` path that no configuration selects; it
is not a measurement of a dense kernel on `D'`.

## 5. Rental criterion

No hardware is rented or bought, and no GPU dependency is added. Before either, in order:

1. **CPU phase split, no GPU needed.** On the largest batch of `mq-random-14` (the corpus's
   `default-64m` entry), measure Zeebra's elimination time split between the sparse sweep and the
   residual's echelon, under the #86 reconciliation contract (matched build, pinned, interleaved,
   best multicore CPU configuration). If the residual echelon is under **half** the batch's
   elimination time, no device can make that batch's elimination 2× faster, and the answer is no
   without renting.
2. **Named kernel and input.** Dense echelon of `D'` over a 31-bit prime (and GF(2^8) once a random
   MQ GF(2^8) entry is pinned), on that batch, verified against the CPU result row for row.
3. **Threshold.** The whole batch — CPU sweep, both transfers of `D'`, device echelon, result
   copy-back — must take **≤ 0.5×** the best measured multicore CPU time for the same batch on the
   same host, with host RSS and device memory reported. Below 2× the answer is no.
4. **Prerequisites already met or retired.** #149 is closed (rejected), and F4 has live-entry and
   live-byte budgets (#490, #659); per #86 those budgets are scoped contracts, not whole-process or
   VRAM limits, so transfer peaks and device scratch are priced separately.

## 6. Position

**Defer.** The Type V record does not change #69's default-no: its mechanism is unpublished, and
the two record pages cannot separate algorithm, CPU parallelism and GPU generation. What changed is
the shape of a possible yes. Zeebra's matrices are useless to a dense kernel as built, but after the
sparse reducer sweep they leave a 40–90% dense residual that grows with the instance and carries,
in the dense model, 63–81% of the multiply-adds on the two largest random MQ rungs. If any GPU
kernel is ever proposed for F4, it is the dense echelon of `D'` on instances at least the size of
`mq-random-14`, gated by §5 step 1, which needs no GPU.

Handoffs: the density and work-share numbers to #86 (E1); the "mechanism unknown" finding to #69;
the missing GF(2^8) random-MQ corpus entry and §5 step 1 as follow-up issues.
