# GPU suitability of Zeebra's kernels: runtime share and arithmetic intensity, per field width (#86)

**Measured at:** `25d9588a` (this issue's instrument commit; its `src/` is identical to `main` at
`6a69522f`), 2026-11-18, for §3's ceilings, §2's BN254 / GF(2^8) / Goldilocks / Mersenne31 stage
rows and every `D'` count in §4. Ceilings and stage clocks ran under `tools/benchlock.sh zb-86`
(load 1.90 → 2.20; [`benchlock.log`](../../research/gpu-kernels/benchlock.log)), one worker on CPU
48 and sixteen on CPUs 48–63, five interleaved repetitions, no CCD reservation. The untimed
`D'` count ran beside them on CPU 42. Rows reused from earlier campaigns keep their own commits:
the M30 final cohort at `e4826153` (instrument `5515c412`), `residual-split.md` at `ca65b34d`,
`8a68368f` and `86db23f7`/`8313d77d`, `sparse-matvec-throughput.md` at `55a7af25`, and
`characteristic-two-linear-algebra.md` §7 at `db5c5c05`.
**Evidence:** [`research/gpu-kernels/`](../../research/gpu-kernels/README.md). Every table below is
printed by `research/gpu-kernels/analyze.py` into [`tables.md`](../../research/gpu-kernels/tables.md),
or is a count file beside it.
**Scope:** public systems only (Katsura, Cyclic, Eco, seeded random MQ, generated in-crate or
digest-pinned). Cipher-derived instances are out of scope for this public record (#668), so the
issue's "one real instance from the cryptanalysis epic" is replaced by the public corpus.
No GPU was used and no code under `src/` changed.

This is E1 of #69. It builds on `gpu-f4.md` (#225: tile density of `D'`), `residual-split.md`
(#803/#816/#828: the time split of an F4 batch) and `sparse-matvec-throughput.md` (#87: the
Krylov operator kernel), and does not re-measure what they settled.

---

## 1. Verdict

**No-go for E4 (#89) at this commit.** No kernel passes both of #86's filters on a complete public
instance:

- Every F4 elimination kernel is **arithmetic- or index-bound, not bandwidth-bound**, on every field
  width (§3). The intensity filter therefore excludes nothing, and the decision falls to runtime
  share and structure.
- The one dense, regular kernel F4 produces — the echelon and back-substitution of the pair-row
  residual `D'` after the Faugère–Lachartre sweep — is about **6%** of a complete `mq-random-10`
  run at 16 workers (ceiling **1.07×**), and an estimated **~48%** of the bounded `mq-random-14`
  run, the largest public input (ceiling **~1.9×** before any transfer). Both are under the 2×
  threshold `gpu-f4.md` §5 step 3 sets for a rental.
- The kernels with large shares — the sparse forward elimination (15–75% of the F4 call at 16
  workers) and symbolic preprocessing (4–36%) — are on the negative list for structural reasons (§5).

The top-ranked candidate stays the `D'` block on large 31-bit MQ instances (§6). What would change
the verdict is in §7.

## 2. Runtime share, per field width

Share of the F4 call (this issue's rows) or of process wall (M30 rows), medians of five, stage
clocks on. `forward` is the sparse forward elimination (parallel at 16 workers), `backward` the
candidate finishing.

| instance / field | width | workers | wall ms | symbolic | construction | forward | backward | interreduction | rest | source |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|
| mq10 / GF(32003) | 15 b in u32 | 16 | 238.9 | 18.8% | 8.4% | 34.6% | 7.4% | 6.2% | 24.3% | M30 `e4826153` |
| mq-10 / 2³¹−1 | 31 b in u64 | 16 | 187.5 | 24.6% | 9.8% | 36.0% | 8.4% | 7.8% | 13.6% | `25d9588a` |
| katsura11 / 2³¹−1 | 31 b in u64 | 16 | 1105.4 | 12.8% | 5.8% | 37.8% | 4.3% | 10.2% | 29.1% | M30 |
| katsura-9 / Goldilocks | 64 b | 16 | 219.9 | 22.6% | 7.3% | 36.7% | 7.0% | 11.7% | 14.2% | `25d9588a` |
| mq11 / Goldilocks | 64 b | 16 | 4630.7 | 6.4% | 3.1% | 55.1% | 5.7% | 7.6% | 22.2% | M30 |
| eco12 / 2⁶⁴−353 | 64 b | 16 | 2353.6 | 10.9% | 5.5% | 34.5% | 9.1% | 22.6% | 17.4% | M30 |
| katsura-9 / BN254 Fr | 254 b, 4 limbs | 16 | 1233.4 | 3.8% | 2.6% | **75.4%** | 12.9% | 2.5% | 2.6% | `25d9588a` |
| cyclic-7 / BN254 Fr | 254 b | 16 | 365.5 | 9.9% | 4.3% | 51.1% | 20.1% | 3.4% | 11.0% | `25d9588a` |
| mq-10 / GF(2⁸) `Gf256Mq` | 8 b in u64 | 16 | 476.1 | 9.5% | 4.0% | **65.2%** | 12.5% | 3.4% | 5.6% | `25d9588a` |
| katsura-9 / BN254 Fr | 254 b | 1 | 12893.9 | 0.6% | 0.2% | 95.0% | 3.9% | 0.2% | 0.2% | `25d9588a` |
| mq-10 / 2³¹−1 | 31 b | 1 | 959.8 | 8.1% | 1.6% | 83.3% | 3.9% | 1.2% | 1.9% | `25d9588a` |

`rest` is extraction, other in-F4 bookkeeping and (M30 rows) work outside the F4 call. Every row and
the 1-worker rows are in `tables.md`. `katsura11` in the M30 naming and `katsura-10` here are the same
11-variable system (both censuses count 4,376,252,738 forward products).

**The field width changes the answer, as the issue predicted, but towards elimination.** At 16
workers elimination (forward + backward) is 21–61% of the call for 31- and 64-bit fields, 71–88%
for BN254 and 78% for GF(2⁸), whose multiply is a table walk (§3). The same katsura-9 system takes
5.6× longer over BN254 than over Goldilocks at 16 workers, and nearly all of the difference is
elimination. GF(2) is not in this table: its packed route (#777) solves the public dense Boolean MQ
ladder in 3.6–64 ms at `db5c5c05` (`characteristic-two-linear-algebra.md` §7.2), below any device's
launch-and-transfer floor, so it is listed in §5 on absolute size.

## 3. Arithmetic intensity and the CPU bound, measured

### 3.1 The shipped step, per field

`gpu_kernel_census ceilings` times the inner loop of `DenseAccumulator::subtract_scaled` — read a
`(usize, F)` pivot entry, `acc[c] -= v · factor` with Shoup's prepared factor, nonzero bookkeeping —
with the pivot entries resident in L2 (256 KiB), one CCD's L3 (16 MiB) and DRAM (1 GiB), and a
contiguous L1 loop of the same operation as the arithmetic ceiling. One core, M products/s, medians:

| field | cell B | logical B / product | L1 contiguous | L2 | L3 | DRAM | DRAM ÷ L2 | DRAM logical GB/s |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| GF(32003) u32 | 4 | 24 | 3472.7 | 590.1 | 586.7 | 602.1 | 1.02 | 14.5 |
| 2³¹−1 u64 | 8 | 32 | 2233.7 | 757.8 | 773.2 | 760.2 | 1.00 | 24.3 |
| Goldilocks | 8 | 32 | 933.0 | 614.5 | 585.0 | 585.8 | 0.95 | 18.7 |
| 2⁶⁴−353 | 8 | 32 | 551.9 | 592.8 | 566.9 | 557.7 | 0.94 | 17.9 |
| BN254 Fr | 32 | 104 | 46.2 | 39.5 | 42.1 | 41.1 | 1.04 | 4.3 |
| GF(2⁸) `Gf256Mq` | 8 | 32 | 144.3 | 133.8 | 133.7 | 130.2 | 0.97 | 4.2 |

One core's streaming read measured 16.2 GB/s in the same run (#87 measured 26.3 GB/s at
`55a7af25`; the reference loop differs).

**Moving the pivot entries from L2 to DRAM changes the step's rate by at most 6% on any field.** A
bandwidth-bound kernel would slow by the cache-to-DRAM ratio, so the step is not bandwidth-bound at
any width. Two different limits apply:

- **Index-bound at 31 bits.** The contiguous L1 loop runs 3–6× faster than the scatter. The
  indexed read-modify-write limits the step, not the multiply.
- **Arithmetic-bound at 64 bits and above, and over GF(2⁸).** The scatter reaches 63–107% of the
  L1 ceiling (2⁶⁴−353 107%, BN254 89%, GF(2⁸) 90%), so the multiply is the limit.

### 3.2 F4's forward elimination against those ceilings

Intensity is computed from the serial entry census (`--features research-work`): coefficient
products, plus dense-row loads, scans and gathers, each costed at the bytes it touches. These are
logical bytes. No hardware counters are readable on this host (`perf_event_paranoid=2`, #87 §1).

| instance / field | forward products | logical B / product | products / logical B | 1-worker G products/s | step ceiling (L3) | 16-worker logical GB/s |
|---|---:|---:|---:|---:|---:|---:|
| mq10 / GF(32003) (M30) | 518.3 M | 24.3 | 0.041 | 0.599 | 0.587 | 152 |
| mq-10 / 2³¹−1 | 518.3 M | 32.5 | 0.031 | 0.648 | 0.773 | 250 |
| katsura11 / 2³¹−1 (M30) | 4,376 M | 32.2 | 0.031 | 0.765 | 0.773 | 338 |
| katsura11 / 2⁶⁴−353 (M30) | 4,376 M | 32.2 | 0.031 | 0.574 | 0.567 | 235 |
| eco12 / 2⁶⁴−353 (M30) | 5,581 M | 32.2 | 0.031 | 0.565 | 0.567 | 221 |
| mq11 / Goldilocks (M30) | 19,333 M | 32.1 | 0.031 | 0.551 | 0.585 | 243 |
| katsura-9 / Goldilocks | 465.8 M | 32.4 | 0.031 | 0.477 | 0.585 | 187 |
| katsura-9 / BN254 Fr | 465.8 M | 105.3 | 0.0095 | 0.038 | 0.042 | 53 |
| mq-10 / GF(2⁸) | 514.0 M | 32.5 | 0.031 | 0.160 | 0.134 | 54 |

What the numbers show:

1. **F4's serial forward pass runs at 82–102% of the isolated step's ceiling** on every prime
   field. The GF(2⁸) row exceeds it (119%) because F4's coefficients reach the table multiply's
   fast path more often than the ceiling's random draws do. The pass is the step, at the step's
   speed.
2. **The same work at the same bytes runs at different speeds on different moduli.** Katsura11 does
   4,376 M products over 32.2 logical bytes each at both 2³¹−1 and 2⁶⁴−353, and runs 1.33× faster
   at 2³¹−1. A bandwidth-bound kernel could not tell the two moduli apart.
3. **At 16 workers the logical traffic is 152–338 GB/s on 31/64-bit fields.** That is above the
   112 GB/s that sixteen threads stream from DRAM (#87 §2), so the working set is served from L3,
   not DRAM. Over BN254 and GF(2⁸) it is 53–54 GB/s, with arithmetic limiting.
4. **Intensity is low and fixed by the width:** 0.031 products per logical byte at 64-bit cells,
   0.041 at 32-bit, 0.0095 at BN254. Expressed as a device's machine balance, every sparse F4 kernel
   would be bandwidth-bound on a GPU even though none is on this CPU. For the sparse kernels
   offload would trade the CPU's arithmetic and index limit for the device's bandwidth limit, and
   no device bandwidth is measured here (E4's job).

### 3.3 The dense residual `D'`

`block_density residual-work` counts the shipped backend's work on `D'` alone, exactly
([`residual-work-25d9588a.md`](../../research/gpu-kernels/residual-work-25d9588a.md)):

| batch | `D'` rows × cols | sweep products | shipped echelon products | shipped back-substitution products | dense-model echelon multiply-adds | `D'` cells |
|---|---|---:|---:|---:|---:|---:|
| `mq-random-10` default, 2³¹−1 | 1,305 × 934 | 239.5 M | 50.9 M | 27.5 M | 394.6 M | 1.22 M |
| `mq-random-14` default-64m, 2³¹−1 | 6,740 × 8,783 | 30.24 G | 26.71 G | 18.97 G | 126.45 G | 59.2 M |
| `mq-random-8` default, GF(2⁸) | 190 × 312 | 25.4 M | 0.59 M | 0.32 M | 3.13 M | 0.06 M |

- **On the CPU**, `D'` runs through the same sparse step (§3.1), so its intensity is §3.2's 0.031
  products per logical byte. It is not bandwidth-bound either.
- **For a device the relevant intensity is per byte transferred.** A dense echelon of
  `mq-random-14`'s `D'` does 126.45 G multiply-adds on 59.2 M cells. At 4 bytes a cell, `D'` there
  and back is 474 MB, so the kernel does **267 multiply-adds per transferred byte**. That is the only
  kernel in the crate with a transfer intensity in the hundreds. `mq-random-10`'s is 40, and its
  `D'` is 4.9 MB one way, where launch and transfer latency dominate (`gpu-f4.md` §3.2 item 3).
- **A dense kernel does 2.8× the shipped CPU's arithmetic on `mq-random-14`** (126.45 G
  against 45.68 G echelon plus back-substitution products). The dense model's count is fixed by
  shape and rank, while the sparse backend skips `D'`'s 37% zeros as they arise. A device must be
  more than 2.8× faster per multiply-add before it breaks even on arithmetic alone.

## 4. Add-with-carry, per field

**The issue's premise is wrong at the ISA level.** NVIDIA's PTX has carry-propagating integer
instructions: `add.cc`, `addc`, `sub.cc`, `subc`, `mad.cc` and `madc`, with a `CC.CF` carry flag. The
32-bit forms date from PTX ISA 1.2, the 64-bit forms from 4.3 (`sm_20`+). See *PTX ISA*, §9.7.2
"Extended-Precision Integer Arithmetic Instructions",
<https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#extended-precision-integer-arithmetic-instructions>,
read 2026-11-18. `mul.wide` exists only for 16- and 32-bit operands (§9.7.1.3), so a 64×64→128
product is assembled from `mul.lo.u64` and `mul.hi.u64`. **The penalty is limb width, not missing
carries.** How the hardware lowers these instructions is not public in the PTX document and is not
measured here.

| field | CPU limbs (64-bit) | 32-bit limbs | CPU step ceiling, M/s (§3.1, L1) | CPU cost vs 2³¹−1 | GPU-side penalty |
|---|---:|---:|---:|---:|---|
| GF(32003), 2³¹−1 | 1 | 1 | 3472.7 / 2233.7 | 1× | none: one 32×32→64 product per multiply |
| Goldilocks, 2⁶⁴−353 | 1 | 2 | 933.0 / 551.9 | 2.4–4.0× | about 4 partial products per multiply, from 2-limb operands |
| BN254 Fr (`montgomery_256`) | 4 | 8 | 46.2 | 48× | 64 partial products for the schoolbook product, plus as many for Montgomery reduction, against the CPU's 16 + 16 |
| GF(2⁸) `Gf256Mq` | — | — | 144.3 | 15× | table or carry-less arithmetic, not integer limbs; carries do not apply |

The partial-product counts are limb arithmetic, not measurements. The 31- and 64-bit fields carry
little or no penalty. BN254's grows with the square of the limb count, which is 4× worse on 32-bit
words than on the CPU's 64-bit `mulx` before any carry handling. BN254 is also where elimination's
share is largest (§2), so the penalty falls where the share is.

## 5. Negative list

These are not GPU candidates. Each entry gives the structural reason and the measured figure behind
it, as #58 did for Wiedemann.

1. **F4 symbolic preprocessing** — 4–36% of the call at 16 workers (§2). Monomial hashing,
   divisor queries and reducer selection are data-dependent lookups into a growing table, with
   allocation per batch. There is no fixed-modulus arithmetic to batch. M30's parallel symbolic work
   (#878, #884) is the CPU answer.
2. **F4's sparse forward elimination over the matrix as built** — 15–75% of the call. #58: the
   operator is consumed by the computation, the batch is deliberately rank-deficient, and its shape
   exists only after symbolic preprocessing. `gpu-f4.md` §3.1: one tile in the whole pinned corpus
   is half full. §3 here: the CPU step is index- or arithmetic-bound at 0.031 products per logical
   byte, which is bandwidth-bound territory on any device.
3. **The reducer sweep `C A⁻¹ B` on its own** — row-independent against a read-only block (#828
   runs it on workers), but each row's pivot sequence depends on its own fill. It is the same sparse
   step as item 2. It stays on the CPU under every split `gpu-f4.md` considered.
4. **Candidate finishing (backward)** — 4–20% of the call, sparse, and already parallel (#845).
5. **Matrix construction and extraction** — 3–15%: sort, scatter and gather of row maps. This is
   data movement with no arithmetic.
6. **Interreduction** — 2–23% (Eco-12 23%), sparse polynomial reduction against a changing basis.
   It has item 2's structure at a smaller size.
7. **Krylov / Wiedemann sparse matvec** — not on the F4 route (#58: it computes the wrong object
   for F4). On the FGLM-side operators #87 measured (`sparse-matvec-throughput.md` §7), the real
   operator is 3.1 MB even over BN254, each dependent step is under 1 ms, and per-step
   synchronization dominates beyond 16–32 workers. A device would face launch latency per Krylov step.
8. **NTT** — **0% of every F4 and FGLM route**. Neither calls `fft::multiply`
   (`multicore-ntt.md`, reachability table). Its reachable callers are Graeffe root finding,
   resultants and Reed–Solomon, none on a solve route measured here.
9. **Packed GF(2) elimination** — shipped (#777). Whole public solves take 3.6–64 ms
   (`characteristic-two-linear-algebra.md` §7.2), and the bit-packed kernel is gather-bound
   (#87 §7). There is no device-sized work.
10. **MQ hybrid enumeration (B2, #75)** — **not in this crate.** #75 declined crossbred, and the
    enumeration research moved out with #668, so Zeebra has no kernel to classify. The issue's
    "strongest candidate in the crate" does not exist here.
11. **Dense `Matrix` multiplication** (`matmul-register-tiling.md`) — no caller on any F4 or solve
    route measured here.

## 6. Ranked candidates

Expected benefit is the Amdahl ceiling: the device does the kernel's share in zero time, the CPU
does everything else, and transfers cost nothing. It is an upper bound.

| rank | kernel | field | measured share | intensity | CPU bound | ceiling | filters |
|---:|---|---|---|---|---|---:|---|
| 1 | dense echelon and back-substitution of `D'` after the FL sweep | 31-bit prime; 64-bit unmeasured | `mq-random-10` complete run: ~6% at 16 workers (§6.1); `mq-random-14` bounded run: ~48% estimated; echelon 29% and all `D'` work 65% of the serial FL batch (`residual-split.md` §3) | 267 multiply-adds per transferred byte (dense model); 0.031 products per logical byte on CPU | index-bound, not bandwidth | 1.07× (mq-random-10); ~1.9× (mq-random-14, bounded) | intensity passes; share fails on every complete public instance |
| 2 | sparse forward elimination | BN254 | 75% of katsura-9 at 16 workers | 0.0095 products per logical byte | arithmetic (89% of L1 ceiling) | 4.1× if all of it moved | structurally negative (§5 item 2); worst limb penalty (§4) |
| 3 | sparse forward elimination | GF(2⁸) | 65% of mq-10 at 16 workers | 0.031 | arithmetic (table multiply) | 2.9× | structurally negative; no limb arithmetic to gain from |

### 6.1 How the `D'` shares were formed

- **`mq-random-10`, complete, 16 workers, default forward order.** `D'` work on the largest batch is
  50.9 M + 27.5 M = 78.4 M products. That is 14.5% of the run's 541.9 M forward and backward
  products (this issue's census). Elimination is 44.4% of the 16-worker call (§2), so
  `D'` ≈ 0.145 × 0.444 ≈ **6.4%** of the run. These are forward-order products. The FL order
  that isolates `D'` is 1.12–1.16× faster on this instance (`residual-split.md` §8.1), which
  does not move the ceiling materially. This is a product-weighted share, which §3.2 item 1
  supports: the pass runs at the step's rate. Ceiling 1/(1 − 0.064) = 1.07×.
- **`mq-random-14`, 16 workers, parallel FL order (`residual-split.md` §8.1, `8313d77d`).** The run
  is bounded: it stops at `TooManyRows` after nine batches, in 86 s. Its 61 s `forward_ns` is sweep
  plus `D'` echelon, and its 13 s `backward_ns` is `D'` back-substitution. Splitting the 61 s by the
  largest batch's product counts (30.24 G sweep, 26.71 G echelon) puts the `D'` echelon at about
  28.6 s, so `D'` work is about 41.6 s of 86 s (48%), with a ceiling of about 1.9×. That
  attribution is an estimate. The FL route does not clock the sweep apart from `D'`, and the other
  eight batches' splits are not counted. The bracket is 13 s (15%, back-substitution alone) to
  74 s (86%, all of forward and backward).

## 7. Recommendation for E4 (#89)

**Do not rent.** Neither filter is what fails: the intensity filter passes every F4 kernel (none
is bandwidth-bound on the CPU), and the one regular, high-transfer-intensity kernel fails the share
filter on every complete public instance.

If E4 runs one experiment later, it should be candidate 1, and only once both of these hold:

1. **A complete public instance where `D'` work is ≥ 50% of the best multicore CPU time, measured
   rather than prorated.** That needs the FL route's sweep and `D'` echelon clocked apart at 16
   workers. The clocks live in `src/grobner/f4/`, inside M31's contention area, so the work is
   filed as #918 instead of being done here.
2. **`gpu-f4.md` §5 step 3's protocol unchanged:** dense echelon of `D'` over a 31-bit prime,
   verified row for row against the CPU candidates. The whole batch must take ≤ 0.5× the best
   multicore CPU time, counting both transfers, with host RSS and device memory reported. The device
   must also be more than 2.8× faster per multiply-add than the CPU's sparse path just to match its
   arithmetic (§3.3).

**What would reopen the wide-field question** is a BN254 instance whose elimination share stays at
75% under the best CPU route, together with a measured device Montgomery-multiply rate. The limb
penalty in §4 is arithmetic, so only a device measurement can settle it, and E4 owns that.

## 8. What this does not establish

- **No device was measured.** Every GPU statement is structural, or comes from NVIDIA's PTX ISA
  document.
- **Logical bytes, not physical.** Without hardware counters, line and DRAM traffic are not
  measured. The bandwidth conclusion rests on §3.1's residency invariance and §3.2 item 2's
  modulus dependence, not on a byte count.
- **The `mq-random-14` share is an estimate on a bounded run** (§6.1).
- **Instances.** Cipher systems are out of scope (#668). GF(2⁸) has one MQ rung in the pinned
  corpus (`gpu-f4.md` §3.3) and one generated system here. BN254 has no MQ instance, because
  `CaseField` draws coefficients below a `u64` prime.
- **Load.** The timed rows ran at load 1.9–2.2 beside the untimed count on CPU 42. Shares are
  ratios within a run. The absolute times are labelled with commit and load and nothing more.
