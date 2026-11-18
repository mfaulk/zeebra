# M31-S3: signature-F4 serial overhead — results (#903)

**Status:** measured, 2026-11-18. All three changes pass §7.4's bar and merge in order (#911, #913,
#914); on Eco-12 the stack takes design 1 from 3,594 to 2,481 ms (0.693×) with identical algebra on every row.
**Measured at:** `acbaf12c` (the #901 freeze, parent of change 1), `f903e087` (change 1,
interreduction), `56fe5fea` (change 2, bookkeeping) and `f9f8a18c` (change 3, symbolic), each built
from a `git archive` of that commit; binary SHA-256s in
[`research/m31-sigf4-serial/binaries.sha256`](../../research/m31-sigf4-serial/binaries.sha256).
The measured commits are tagged `measured/903-interreduce`, `measured/903-bookkeeping` and
`measured/903-symbolic`.
**Plan:** [`MILESTONE-COMPETITIVE-SIGNATURE-F4.md`](../MILESTONE-COMPETITIVE-SIGNATURE-F4.md) §4.1
H3, §6.3, §7.4, §8.5, §10.

## 1. The three changes

Each touches `src/grobner/sigf4/` only; no shipping-F4 file changed.

1. **Interreduction (#911).** The engine's final stage now takes #879's tail-only matrix route
   (`MatrixInterreductionMethod::TailsOnly`) instead of the full echelon form. Its precondition —
   monic rows at distinct leads, which every closure of a minimized basis has — always holds here,
   so no fallback condition is needed. Under callgrind the full echelon's back-substitution among
   reducer multiples was 26.6% of Eco-12's instructions; the tail sweep skips it. Earlier minimal
   filtering was not pursued: `minimal_basis_for_interreduction` is under 1% of instructions. The
   shipping parallel route does not apply at one CPU (design 1's placement) and was not tried.
2. **Bookkeeping (#913).** The syzygy store kept each signature's divisibility mask inside a
   64-byte entry and found covers with an iterator chain; masks now live in their own array and are
   filtered eight at a time into a hit word, in insertion order, so the *first* covering entry —
   which decides Koszul versus zero-row attribution — is unchanged. The rewriter's per-index list
   carries its signature masks the same way, `mask()` sets each variable's band in one shift, and a
   pending entry stores two element ids instead of two 48-byte multipliers (recomputed from the
   leads when read), so the queue's peak shrinks about 2.5×.
3. **Symbolic (#914).** The closure hashed every term to deduplicate columns and elimination hashed
   every term again to find its column. The closure now keeps the handle each lookup returned,
   renumbers handles to column positions once the columns are sorted, and elimination builds its
   sparse rows by array lookup. Reducer masks are scanned from a contiguous array. Reducer choice is
   untouched. #861's parallel interning was not used: design 1 runs pinned to one CPU (#901's arm,
   `m30-sigf4/run.py`), where a worker team has nothing to run on, and the shipping interner's
   inputs (`MonicBasis`, critical pairs, `ReducerSelection`) do not carry signatures, so calling it
   would mean modifying `symbolic_intern.rs`, which §12 rule 3 forbids inside a sig-F4 PR.

## 2. Method

Plan §10.4, design 1 only (`sig_f4_study --engine sigf4 --workers 1`), which is the arm the
gate names. Four binaries, one per commit, each from a `git archive` built into a private target
directory (`--release`, fat LTO, one codegen unit, `x86-64-v3`). Every child is a fresh process
pinned to CPU 8 inside a `tools/bench-reserve.sh` reservation of CCDs 1-2, under `benchlock`
(`research/m31-sigf4-serial/benchlock.log`), with `tools/cpu-context.sh` snapshots before and after
it: 1-minute load 0.70-2.67, zero compiler processes at every snapshot. The four arms run in one
interleaved campaign, rotated one place per repetition (`m30-sigf4/run.py`'s `plan`), n = 9, so
each change is paired with its own parent in every repetition. Ratios are head ÷ parent process
wall per repetition; the interval is a 95% bootstrap of their median (20,000 draws). The corpus is
§10.3's as far as the instrument reaches:

- MQ10 is not in it: `sig_f4_study` only takes the Goldilocks and 2⁶⁴−353 fields, and its MQ rows
  are MQ11.
- eco-14 is not in it: #901's freeze probe found design 1 at the 180 s solve cap there
  (`research/m31-baseline/probe.jsonl`), so there is no wall to pair.
- katsura-9 and noon-8 (held out) panicked in all 72 corpus-campaign attempts, because the freeze's
  `sig_f4_study` instantiates only 4, 7, 11 and 12 variables. They were run afterwards in a second
  campaign (`heldout`) from binaries whose only difference is two more instantiations in the
  example's dispatch (§3.2). No held-out figure was looked at before every change was final.

Algebra is compared on every complete child: every non-timing statistic (`pairs_created`,
`pairs_singular`, each rejection count by mechanism, targets, reducer rows, reductions to zero,
coefficient products, element and syzygy counts, matrix shapes) and the basis SHA-256 must be one
value across both arms and all nine repetitions. `signature_metadata_bytes` is excluded because it
is a memory estimate that change 2 shrinks by design (the pending entry is smaller), and the new
interreduction-matrix fields are instruments. Callgrind instruction counts (one Eco-12 run per
variant, outside the lock) chose what to change; no figure here comes from them.

While this ran, #910 and #899 merged to `main`, so change 1's parent there is `13e63076`, not the
freeze. Neither touches the design-1 path: #910's additions to `sigf4/engine.rs` are all under
`#[cfg(feature = "research-sigf4-replay")]`, which these builds do not enable, and #899's are in
certification and shipping-F4 error variants. The measured pairs therefore stand for each change against its parent on `main`.

Run: `BINS=… OUT=… bash research/m31-sigf4-serial/campaign.sh corpus|heldout`, then
`bash research/m31-sigf4-serial/tables.sh`.

## 3. Results

### 3.1 Each change against its parent (complete design-1 process wall, n = 9 each)

Every row below has identical algebra across the pair and all repetitions (`algebra identical`
column of [`tables.md`](../../research/m31-sigf4-serial/tables.md)), and every basis digest equals
the freeze's. RSS is the median paired peak-RSS ratio.

| Row | Change 1 ÷ freeze [95%] | RSS | Change 2 ÷ change 1 [95%] | RSS | Change 3 ÷ change 2 [95%] | RSS |
|---|---|---:|---|---:|---|---:|
| **Eco-12 / 2⁶⁴−353** | **0.896** [0.895, 0.906] | 0.785 | **0.910** [0.902, 0.915] | 0.992 | **0.851** [0.843, 0.854] | 1.008 |
| Katsura-11 / Goldilocks | 0.997 [0.972, 0.999] | 1.028 | 0.998 [0.988, 1.009] | 1.000 | 0.864 [0.856, 0.878] | 0.991 |
| Katsura-11 / 2⁶⁴−353 | 0.997 [0.974, 1.000] | 1.029 | 0.995 [0.990, 1.005] | 0.999 | 0.855 [0.850, 0.863] | 0.994 |
| MQ11 / Goldilocks | 0.991 [0.982, 0.995] | 1.003 | 0.998 [0.993, 0.999] | 1.000 | 0.925 [0.923, 0.930] | 1.000 |
| Cyclic-7 / Goldilocks | 0.990 [0.983, 0.999] | 1.000 | 0.814 [0.808, 0.825] | 0.991 | 0.855 [0.844, 0.863] | 1.012 |
| Cyclic-7 / 2⁶⁴−353 | 0.991 [0.981, 1.005] | 1.003 | 0.824 [0.811, 0.845] | 0.983 | 0.854 [0.826, 0.868] | 1.019 |
| katsura-4 / Goldilocks | 0.991 [0.951, 1.042] | 1.025 | 1.001 [0.976, 1.032] | 0.934 | 0.999 [0.970, 1.022] | 1.022 |
| katsura-4 / 2⁶⁴−353 | 0.988 [0.966, 1.016] | 1.020 | 0.979 [0.968, 1.035] | 0.927 | 0.993 [0.968, 1.048] | 1.007 |
| noon-7 / Goldilocks | 0.985 [0.971, 0.997] | 1.000 | 0.979 [0.968, 0.995] | 0.997 | 0.899 [0.889, 0.910] | 1.007 |

The stack against the freeze: Eco-12 **0.693** [0.690, 0.699] (3,594.3 → 2,481.0 ms), Katsura-11
0.852 / 0.847, MQ11 0.914, Cyclic-7 0.692 / 0.697, noon-7 0.862, katsura-4 0.986 / 0.995. katsura-4
runs in 5.7 ms, so its intervals are process-start noise; its largest upper bound, 1.048, is inside
the 1.05 limit.

### 3.2 Held-out rows (reported, not gating; run after the changes were final)

| Row | Change 1 ÷ freeze [95%] | RSS | Change 2 ÷ change 1 [95%] | RSS | Change 3 ÷ change 2 [95%] | RSS |
|---|---|---:|---|---:|---|---:|
| katsura-9 / 2⁶⁴−353 | 0.983 [0.979, 0.991] | 1.017 | 0.987 [0.981, 1.006] | **1.141** | 0.857 [0.855, 0.861] | 0.942 |
| noon-8 / 2⁶⁴−353 | 1.006 [0.992, 1.012] | 1.001 | 0.946 [0.940, 0.951] | 1.010 | 0.893 [0.871, 0.906] | 1.000 |

Same placement and checks, n = 9, 72 children, load 1.34-2.52, no compilers; algebra identical.
These binaries add the `("wide64", 8 | 9)` dispatch arms to the example and nothing else (PR #911
adds them on `main`). katsura-9's change-2 RSS ratio, 1.141, is above the 1.10 limit on a 10.8 MiB
process: +1.5 MiB, reproducible outside the lock. It is not heap: valgrind's massif puts both
binaries' heap peak at exactly 6,617,576 bytes on that row, and the engine's own metadata estimate
falls 28% (133,035 → 95,719 bytes). Held-out rows are reported, not gating (§10.3), so it does not
change the verdict, and nothing was tuned on it; it is recorded here as the one bound a figure
crossed. eco-14 (held out) was not run, for the reason in §2.

### 3.3 Where the time went (design 1, in-process stage clocks, medians of the same children)

| Row | Arm | Elimination | Interreduction | Bookkeeping | Symbolic | Sum | Call | Process wall | Peak RSS MiB |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|
| wide64/eco-12 | base | 1,715.8 | 703.1 | 459.5 | 456.8 | 3,335.1 | 3,395.2 | 3,594.3 | 208.2 |
| wide64/eco-12 | interreduce | 1,704.0 | 252.0 | 550.6 | 458.0 | 2,964.6 | 3,032.2 | 3,218.8 | 163.4 |
| wide64/eco-12 | bookkeeping | 1,747.4 | 252.0 | 226.8 | 463.1 | 2,689.3 | 2,769.5 | 2,954.4 | 162.1 |
| wide64/eco-12 | symbolic | 1,293.9 | 258.0 | 219.2 | 454.0 | 2,225.1 | 2,296.6 | 2,481.0 | 163.3 |
| goldilocks/katsura-11 | base | 569.2 | 109.7 | 19.5 | 164.9 | 863.3 | 886.9 | 1,060.4 | 106.1 |
| goldilocks/katsura-11 | interreduce | 576.7 | 106.0 | 18.8 | 161.0 | 862.5 | 884.5 | 1,059.6 | 109.1 |
| goldilocks/katsura-11 | bookkeeping | 574.9 | 106.6 | 17.0 | 161.8 | 860.3 | 886.2 | 1,058.7 | 109.1 |
| goldilocks/katsura-11 | symbolic | 423.9 | 107.5 | 14.5 | 154.3 | 700.3 | 730.7 | 917.6 | 108.1 |
| goldilocks/mq-random-11 | base | 3,919.2 | 561.5 | 33.7 | 466.6 | 4,981.1 | 5,086.7 | 5,695.5 | 357.1 |
| goldilocks/mq-random-11 | interreduce | 3,879.2 | 492.8 | 32.3 | 452.3 | 4,856.7 | 4,939.2 | 5,532.2 | 358.1 |
| goldilocks/mq-random-11 | bookkeeping | 3,841.1 | 495.0 | 33.2 | 454.0 | 4,823.2 | 4,917.1 | 5,506.8 | 358.1 |
| goldilocks/mq-random-11 | symbolic | 3,462.0 | 496.3 | 25.0 | 432.0 | 4,415.3 | 4,502.1 | 5,094.3 | 358.1 |
| goldilocks/cyclic-7 | base | 150.4 | 19.3 | 515.8 | 121.8 | 807.3 | 844.1 | 865.7 | 68.9 |
| goldilocks/cyclic-7 | interreduce | 148.7 | 18.8 | 511.1 | 123.1 | 801.8 | 832.5 | 853.6 | 68.9 |
| goldilocks/cyclic-7 | bookkeeping | 148.4 | 19.1 | 355.1 | 120.3 | 642.9 | 677.2 | 697.3 | 68.2 |
| goldilocks/cyclic-7 | symbolic | 56.1 | 18.9 | 350.5 | 113.0 | 538.4 | 573.7 | 595.4 | 69.1 |

Read with care:

- **Change 1** cut Eco-12's interreduction 2.79× (703 → 252 ms) and its peak RSS from 208 to 163 MiB,
  because the full echelon form's fill-in among reducer multiples never happens. Katsura-11 and
  MQ11 interreduce small matrices, so they barely move. Eco-12's bookkeeping clock rose 459 → 551 ms
  in the same arm although no bookkeeping code changed. It holds across the nine repetitions and is
  not explained here; allocator or page-cache state is a guess, not a tested one. It does not change
  the verdict: the process wall fell 10.4%.
- **Change 2** cut Eco-12's bookkeeping 2.43× against its parent (551 → 227 ms; 2.03× against the
  freeze's 459) and Cyclic-7's 1.45× (511 → 355 ms), the two rows where bookkeeping is large; the
  others have under 35 ms of it.
- **Change 3** moved **elimination**, not symbolic: Eco-12 1,747 → 1,294 ms, Katsura-11 575 → 424,
  MQ11 3,841 → 3,462, Cyclic-7 148 → 56, while the symbolic clock stayed flat. The saving is the
  second hash of every term, which ran inside `eliminate` when it built the sparse rows. The
  closure does the lookups it did before plus a renumbering pass and the contiguous lead-mask scan,
  and its clock is flat. Products, rows and pivots are unchanged, so the saving is row
  construction, not the cascade #904 owns. The symbolic stage itself is therefore not compressed
  (H3's symbolic leg: 1.0×).

## 4. Verdicts

Against §7.4's bar (Eco-12 ≥ 3% better with the interval excluding 1.0, no row's upper bound above
1.05, peak RSS ≤ 1.10× the parent, identical algebra):

| Change | Eco-12 ratio [95%] | Worst upper bound (row) | Worst RSS ratio | Algebra | Verdict |
|---|---|---|---:|---|---|
| 1 interreduction (#911) | 0.896 [0.895, 0.906] | 1.042 (katsura-4 / Goldilocks) | 1.029 | identical | **pass** |
| 2 bookkeeping (#913) | 0.910 [0.902, 0.915] | 1.035 (katsura-4 / 2⁶⁴−353) | 1.000 | identical | **pass** |
| 3 symbolic (#914) | 0.851 [0.843, 0.854] | 1.048 (katsura-4 / 2⁶⁴−353) | 1.019 | identical | **pass** |

H3 (§4.1) asked for ≥ 2× on at least two of the three stages on Eco-12. Against the freeze's stage
clocks, interreduction is 2.79× (703 → 252 ms) and bookkeeping 2.03× (459 → 219 ms); the symbolic
stage is 1.0× (457 → 454 ms). **H3 holds on two stages**, and the symbolic leg is not compressed:
change 3's gain is in row construction, which the stage clocks count as elimination.

Signature-basis outgrowth (§4.3 item 5) was measured only: Eco-12 still builds 1,885 signature
elements for 743 reduced ones and Cyclic-7 3,083 for 209 (identical counts in every arm, as the
algebra check requires). No provenance-preserving reduction was attempted.

## 5. Stage table for Gate A

Re-measured on `main` once #914 merges, and posted on #904.
