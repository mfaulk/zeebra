# Multirow sparse pivot reuse, separated from SIMD (#715)

**Measured at:** binaries built from `c45bf1eb` (`mq10_profile` stock SHA-256 `df065c48…`, `research-multirow`
SHA-256 `1a1e57e1…`); native campaign controller `ebebd9dc`, declared extension and MQ14 probe
controller `65a616b5`. Those controller commits change only `tools/`, CI and `research/`, never
`src/`, `examples/`, `Cargo.*` or `.cargo/` — the runner refuses to start otherwise. Campaign
date 2026-11-14 UTC. Threadripper PRO 5995WX, `taskset -c 0-3`, one solver worker, rustc 1.99.1,
release profile (fat LTO, one codegen unit), `target-cpu=x86-64-v3` for every arm, system allocator.
Every timed process ran inside one `tools/benchlock.sh` hold per phase.

## Decision

**Reject integrating four-row scalar reuse; defer the SIMD increment, which was not reached.**
Scope: the shipped `F4Options::default()` route (structured reduction, adaptive backend,
candidate-only backward), GF(32003) and GF(2147483647), the public MQ10, Cyclic-5 and Katsura-6
instances, one worker. No production default changes, and no integration issue is filed.

- **The mechanism is real and large in work terms.** On MQ10 four-row bands read each sparse pivot
  for **2.49 targets on average**, cutting pivot entries read from 585.2 M to 237.2 M (**2.47x**)
  with identical arithmetic. Every MQ10 batch shares, and the shared fraction is highest in the
  batches that carry the work.
- **It turns into about 2% of forward elimination, not more.** Native cohort: four-row scalar
  forward is a paired median **0.974x** (range 0.875–1.003) of single-row at GF(32003) and
  **0.978x** (0.963–1.025) at GF(2147483647), inside the feature-absent stock control's own spread
  (0.919–1.064). The declared ten-pair extension (§5) gives **0.980x** (0.946–1.018) and **0.979x**
  (0.954–1.012), eight of ten pairs below one at each prime; process wall **0.980x** and **0.985x**.
  The sign is probably favourable; the size is a fiftieth, against a 2.47x cut in reads. Pivot reads
  are not where forward elimination spends its time, and 2% does not pay for a second forward
  kernel, its budget-accounting difference and its tests.
- **The interleaved four-lane layout is slower outright**: 1.154x and 1.112x forward, 1.114x and
  1.092x process wall, outside every control range. It executes 1.32x the coefficient products, and
  the compiler did not widen its all-lane update (§4), so it measures layout plus zero-lane work, not
  SIMD. A real vector kernel would have to recover that 11–15% first.
- **Memory is not the constraint.** Lane scratch is at most 376 KiB (either band layout, wide prime) beside
  a 36–38 MiB process peak, and peak RSS medians are within 0.6 MiB across all four arms. The
  larger MQ14 rung is refused by the live-entry budget in every arm (§6).

Upstream's eligibility gate (mean row length >= 64) admits MQ10 batches 3–9 and nothing in the
Cyclic/Katsura controls; those controls are sub-millisecond forward passes where the band
bookkeeping costs 1.14x–1.43x, invisible in a 5 ms process.

## 1. What was built

`src/linalg/dense/band.rs`, compiled only under the `research-multirow` cargo feature and selected
per thread with `zeebra::linalg::multirow::with_mode`. Without the feature the crate is unchanged
except that `DenseAccumulator`'s fields are `pub(super)`; with it, `Mode::Single` (the default)
still runs the production loop, and the single branch is one thread-local read per matrix.
`accumulated_row_echelon` and `accumulated_reduce_rows_against_pivots` dispatch, so the band
reaches exactly the forward pass the adaptive backend runs. Backward reduction, symbolic
preprocessing and scheduling are untouched. The kernel is generic over `FiniteField`: no field is
specialized and no unsafe code is added.

| Arm | Representation | Pivot read | Update |
|---|---|---|---|
| `stock` | feature-absent binary | once per target | production loop |
| `single` | feature binary, `Mode::Single` | once per target | production loop |
| `band4` | four production `DenseAccumulator`s | once per band step | one lane: the production `subtract_scaled`; two to four: one pass over the pivot, each lane's cells hoisted (`shared::<K>`) |
| `lanes4` | one `Vec<[F; 4]>`, lanes interleaved per column | once per band step | one lane: strided scalar; two to four: fixed-width all-lane body, zero factor in idle lanes |

`stock` against `single` is the instrumentation/dispatch control. `single` against `band4` isolates
reuse at identical products and field arithmetic. `band4` against `lanes4` adds the layout an
all-lane kernel needs and the zero-lane products it executes.

## 2. Ordering and correctness

Rows `[first..]` are processed in bands of four consecutive rows (a shorter final band if fewer
remain). Within a band the sweep repeatedly takes `c`, the smallest leading column over the active
lanes, and the set `S` of active lanes leading at `c`:

- if `c` has a pivot, every lane in `S` subtracts it with its own leading coefficient as factor;
- otherwise the **lowest-indexed** lane of `S` is normalized and becomes `c`'s pivot, written back
  into the matrix at once so later lanes and bands read it; the rest of `S` see the new pivot on the
  next step;
- a lane that reaches zero is retired as a zero row.

Equivalence with the single-row loop, which finishes row `i` before starting `i + 1`:

1. A lane's leading column never decreases: subtracting a pivot that leads at the lane's own leading
   column only writes at or after that column. The sweep's `c` is therefore non-decreasing, and a
   lane whose leading column exceeds `c` never again has a nonzero at `c`.
2. A lane consults the pivot map only at its own current leading column. So lane `j` can be affected
   by another lane `i` of the band only through a pivot `i` creates at a column `j` later reaches.
3. If `i < j` creates the pivot at `c`, `j` reaches `c` only while `i` also leads there (1), and the
   lowest index wins, so `j` subtracts `i`'s final normalized row — exactly what the single-row loop
   does, since `i` had already stopped at `c` there.
4. If `i > j` creates the pivot at `c`, then `j` did not lead at `c` at that step (it would have won),
   so by (1) it never needs `c`. A lower lane never sees a higher lane's pivot, as in sequential order.
5. By induction on sweep steps, every lane applies the same pivots in the same order with the same
   factors, and is normalized at the same column, as the single-row loop. Field operations are exact,
   so rows, pivot map, rank, zero rows, row operations and pivot inversions are identical.

Two things legitimately differ. Up to four rows are out of the matrix at once, so the live-entry
count can peak higher or lower than single-row (`peak_nonzeros` is not compared); the budget check
is still applied after every update, and a refusal is still reported. And the work is reordered
across rows, not within one.

Tests (`cargo test --features research-multirow --lib linalg::dense::band`, also in CI), each
comparing both band modes with the production adaptive backend row for row:

| Test | Covers |
|---|---|
| `test_intra_band_new_pivot_feeds_later_lanes` | a pivot discovered in a band reduces later lanes of the same band; the census sees it |
| `test_shared_column_is_read_once` | lanes sharing a column take one read; applied/read entry counts exact |
| `test_zero_and_cancelling_rows` | cancelling rows, empty rows, an all-zero band |
| `test_partial_bands` | 1–9 rows, so every partial-band width |
| `test_rank_deficient_and_degenerate` | duplicated rows, zero width, zero rows, tall narrow rank-2 |
| `test_random_matrices_across_fields` | 120 random matrices over GF(13), GF(32003), GF(2^31−1) at 5–80% density |
| `test_block_reduction_against_an_upper_block` | the two-phase entry point with a monic upper block, and split 0 |
| `test_budget_refusal` | a budget the single-row loop exceeds is refused by both bands |
| `test_full_basis_equality_on_real_systems` | identical reduced bases and batch count under `F4Options::default()` for Katsura-5 and Cyclic-5/4 at both primes |
| `test_mode_defaults_to_single_and_restores` | the default is single-row and `with_mode` restores it |

As a red check, promoting the *highest*-indexed lane instead of the lowest fails six of these tests.
In the campaign every completed answer of every arm matched the complete, independently
Singular-verified reference basis coefficient for coefficient at the pinned input digest, and the
batch/pair/degree trajectory matched the first verified run of its cell.

## 3. Activation and crossover

Exact counters from the `band4` census; they are properties of the matrices and identical across
repetitions and between `band4` and `lanes4`. "Reuse" is target updates per distinct pivot read;
"read saving" is pivot entries applied over pivot entries read.

| Instance | p | eligible rows | updates | distinct reads | reuse | entries applied | entries read | read saving | reads shared by 1/2/3/4 lanes | intra-band pivot uses | lane scratch |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---|---:|---:|
| MQ10 | 32003 | 3554 | 7 885 325 | 3 161 741 | 2.49 | 585 166 982 | 237 151 584 | 2.47x | 784 028 / 866 435 / 676 685 / 834 593 | 1362 | 188 KiB |
| MQ10 | 2147483647 | 3554 | 7 885 548 | 3 161 763 | 2.49 | 585 195 178 | 237 162 965 | 2.47x | 783 994 / 866 436 / 676 650 / 834 683 | 1362 | 376 KiB |
| Katsura-6 | both | 136 | 4808 | 2247 | 2.14 | 81 509 | 36 978 | 2.20x | 734 / 788 / 402 / 323 | 65 | 2.4 / 4.8 KiB |
| Cyclic-5 | both | 232 | 1532 | 838 | 1.83 | 23 437 | 12 523 | 1.87x | 393 / 222 / 197 / 26 | 125 | 0.9 / 1.8 KiB |

Per MQ10 batch (identical at both primes to the precision shown):

| batch | rows | columns | eligible rows | mean target entries | mean pivot entries | upstream gate (>= 64) | reuse | read saving |
|---:|---:|---:|---:|---:|---:|---|---:|---:|
| 0 | 17 | 40 | 10 | 10.4 | 15.9 | no | 1.57 | 1.75x |
| 1 | 98 | 196 | 28 | 16.5 | 16.9 | no | 1.51 | 1.49x |
| 2 | 503 | 658 | 144 | 48.1 | 42.9 | no | 2.15 | 2.06x |
| 3 | 1611 | 1695 | 458 | 137.4 | 74.2 | yes | 2.43 | 2.33x |
| 4 | 4290 | 4169 | 884 | 211.5 | 80.1 | yes | 2.52 | 2.42x |
| 5 | 6057 | 6292 | 338 | 227.3 | 54.5 | yes | 1.96 | 1.92x |
| 6 | 5710 | 6027 | 114 | 258.7 | 49.1 | yes | 1.51 | 1.51x |
| 7 | 12554 | 12020 | 1468 | 279.3 | 77.7 | yes | 2.66 | 2.59x |
| 8 | 10435 | 10738 | 96 | 304.0 | 45.6 | yes | 2.03 | 2.06x |
| 9 | 11504 | 11851 | 14 | 294.0 | 44.7 | yes | 1.53 | 1.55x |

Every Cyclic-5 and Katsura-6 matrix has a mean target of at most 32 entries, so none passes the upstream
gate; Cyclic-5's first three batches share nothing. The crossover in work terms is early — sharing
appears by MQ10's batch 2 — but §4 shows no crossover in time on any shape measured, so a density
gate would select where the band does least harm rather than where it wins. Unsupported here and not
measured: extension fields, GF(2), fields wider than 64 bits, and the dense or sparse backends; the
band is reachable only through `Backend::Adaptive`.

## 4. Three-arm results

Five interleaved fresh-process repetitions per arm and cell, arm order rotated each repetition, 120
of 120 attempts verified. Three further attempts were excluded and re-run because a build started on
the machine during them (retained under `excluded_attempts`, with the processes seen). START load
1.89 and END load 1.92 on the lock log; per-attempt pre-run load 1.9–4.1. Forward is the F4
forward-elimination stage clock, the only stage the band changes; backward medians agree within
2.5 ms across arms. Ratios are per-repetition pairs against `single`, which is what survives
ambient load; absolute milliseconds are this session's only.

| Instance | p | arm | forward ms, median (range) | F4 call ms | process wall ms | peak RSS MiB | forward / single, paired median (range) | wall / single |
|---|---:|---|---:|---:|---:|---:|---:|---:|
| MQ10 | 32003 | stock | 1022.2 (1012.3–1105.1) | 1195.0 | 1221.0 | 36.8 | 1.031 (0.919–1.064) | 1.021 |
| MQ10 | 32003 | single | 1042.6 (982.1–1102.8) | 1228.6 | 1257.8 | 36.6 | 1 | 1 |
| MQ10 | 32003 | band4 | 996.5 (965.5–1017.5) | 1173.2 | 1201.9 | 36.7 | **0.974 (0.875–1.003)** | 0.984 |
| MQ10 | 32003 | lanes4 | 1177.1 (1169.7–1207.9) | 1358.4 | 1384.9 | 36.8 | **1.154 (1.067–1.211)** | 1.114 |
| MQ10 | 2147483647 | stock | 1138.7 (1102.3–1184.6) | 1322.3 | 1349.9 | 37.5 | 0.997 (0.964–1.024) | 0.995 |
| MQ10 | 2147483647 | single | 1146.3 (1112.4–1170.9) | 1331.8 | 1359.9 | 36.9 | 1 | 1 |
| MQ10 | 2147483647 | band4 | 1128.0 (1077.2–1198.6) | 1319.2 | 1349.1 | 37.4 | **0.978 (0.963–1.025)** | 0.981 |
| MQ10 | 2147483647 | lanes4 | 1241.0 (1232.5–1298.6) | 1417.2 | 1446.6 | 37.2 | **1.112 (1.053–1.133)** | 1.092 |
| Katsura-6 | 32003 | band4 / lanes4 | 0.3 / 0.3 | 0.9 / 0.9 | 5.0 / 5.0 | — | 1.261 / 1.422 | — |
| Katsura-6 | 2147483647 | band4 / lanes4 | 0.3 / 0.3 | 0.9 / 0.9 | 5.0 / 5.0 | — | 1.135 / 1.361 | — |
| Cyclic-5 | 32003 | band4 / lanes4 | 0.1 / 0.1 | 0.6 / 0.6 | 5.1 / 5.1 | — | 1.285 / 1.428 | — |
| Cyclic-5 | 2147483647 | band4 / lanes4 | 0.1 / 0.2 | 0.6 / 0.7 | 5.0 / 5.0 | — | 1.148 / 1.363 | — |

Controls' single-row forward passes are 0.1–0.2 ms, so their ratios are resolution-limited and their
process walls cannot separate the arms; they are reported as the small-matrix cost of band
bookkeeping, not as solve-time evidence. [`table.md`](../../research/multirow-reuse/table.md) has
every cell; RSS is the process's own `VmHWM` at exit.

**Where the SIMD arm stands.** The fixed-width all-lane body was written so the compiler could widen
it, and it did not. Disassembling the GF(32003) instance of `band::eliminate_from` in the measured
binary finds `vpmuludq` only in a loop that broadcasts one factor across consecutive columns of a
single lane — normalization — and none in the all-lane update, which compiles to four unrolled
scalar Montgomery products. The GF(2147483647) instance (a `u64`-backed element) has no `vpmuludq`
at all. So `lanes4` is a lane-*shaped* arm: it isolates the interleaved layout and the 1.32x
zero-lane products a vector kernel must also pay, and it costs 11–15% before any vector instruction
is involved. An explicit 4 x 32-bit kernel would need raw Montgomery access to `PrimeFieldElement32`
— the representation problem `docs/MILESTONE-SIMD-PARALLELISM.md` §10.1 already priced — and would
have to recover both that 11–15% and the further margin needed to beat `single`. That is a
prediction this study cannot test, which is why the SIMD increment is deferred rather than rejected.

## 5. Declared extension

The native cohort left `band4`'s MQ10 sign inside the stock control's spread, which the contract
calls inconclusive. One bounded extension was declared in the runner before it ran (commit
`65a616b5`, `--phase extension`): ten further repetitions (5–14) of `single` and `band4` only, MQ10
at both primes, the pair order alternating each repetition, same binaries, gate and lock. It was not
extended again. All 40 attempts verified; none was excluded; pre-run load 1.8–2.2.

| p | pairs | forward band4/single, median (range) | pairs below 1 | process wall band4/single, median (range) | single forward ms | band4 forward ms |
|---:|---:|---:|---:|---:|---:|---:|
| 32003 | 10 | 0.980 (0.946–1.018) | 8 | 0.980 (0.953–1.020) | 1036.2 | 1015.5 |
| 2147483647 | 10 | 0.979 (0.954–1.012) | 8 | 0.985 (0.960–1.023) | 1162.4 | 1143.3 |

Read with the native cohort, fifteen pairs per prime put the four-row scalar arm about 2% ahead on
forward elimination, with every range still crossing one. That is the whole of the reuse effect this
route offers at four rows: no further repetitions are proposed, because a sharper estimate of a 2%
effect would not change the decision.

## 6. Runtime, RSS and the reachable frontier

MQ10's whole process peaks at 36–38 MiB in every arm, and the band's scratch is four accumulator
rows either way — four separate rows (`band4`) or one four-wide row (`lanes4`) — 188 KiB at
GF(32003) and 376 KiB at GF(2147483647), against one row for single-row. Peak
RSS medians differ by at most 0.6 MiB across arms, inside their own repetition ranges. The band
also holds up to four target rows out of the matrix at once, which changes the live-entry count the
budget sees; the full bases are unchanged, but a refusal can land at a different count.

The larger rung, `mq-random-14` (`--phase probe`, one attempt per arm and prime, same lock, 60 s /
2 GiB child caps), shows exactly that and nothing more. Every arm is **refused by the default
32 000 000 live-entry budget**, not by a cap: `TooManyNonzeros` at 32 000 270 (single, stock) and
32 005 274 (`band4`, `lanes4`) at GF(32003), 32 000 112 and 32 006 217 at GF(2147483647). No arm
reaches a basis, so none is verified, and the reachable frontier is the same for all four.

| p | arm | outcome | process wall to refusal s | observed peak RSS MiB |
|---:|---|---|---:|---:|
| 32003 | stock / single | budget refusal | 18.5 / 18.6 | 727 / 731 |
| 32003 | band4 / lanes4 | budget refusal | 16.6 / 19.2 | 728 / 728 |
| 2147483647 | stock / single | budget refusal | 19.5 / 19.3 | 740 / 744 |
| 2147483647 | band4 / lanes4 | budget refusal | 18.4 / 20.2 | 742 / 745 |

These are single attempts that stop at a budget, so their walls are not speedups; they are recorded
because a stop is a result. The live-entry budget, not RSS or time, bounds this rung for every arm,
and multirow reuse does not move it.

## 7. Relation to earlier decisions

The SIMD rejections in `docs/MILESTONE-SIMD-PARALLELISM.md` (#49, #149, #541) concerned updating a
pivot's dense span. Nothing here revives that: every band arm walks the pivot's sparse entries only,
and the rejection stands. What this adds is the other half of upstream's band mechanism — one pivot
read for several targets — and the answer that, on the shipped route, the reads it saves were not
the cost. That is consistent with §10.2's finding that the shipped loop is bound by its scatter into
the accumulator rather than by streaming the pivot: `band4` keeps every scatter and removes only the
streaming. Upstream's own reports (grobx `MANUAL.md`, Katsura-12 488 M versus 1595 M pivot reads)
are the same kind of work figure as §3 and, as #715 anticipated, do not carry over to time here.

## 8. What was not measured

- No explicit SIMD kernel; see §4.
- No hardware cycle or cache counters: no `perf` is installed on this machine at the time of the
  campaign, so the attribution of the residual cost to scatter rather than read is inferred from the
  counters and §10.2, not observed.
- Randomized reduction is not part of Zeebra's F4, so the issue's randomized-interaction factor has
  no arm here; #714's controls apply to grobx only.
- Eight-row bands, other band widths and band-eligibility gates.
- No full basis was verified for MQ14 (no independent reference is retained); §6 compares arms with
  one another only.
- Extension fields, GF(2) and wider fields: unsupported by this prototype's measurement, not by its
  generic code, which the tests run at GF(13), GF(32003) and GF(2^31−1).

## 9. Reproducing

```bash
export CARGO_TARGET_DIR=/buildcache/cargo-target/zeebra-715 RUSTC_WRAPPER=""
cargo build -j24 --release --example mq10_profile            # copy out as the stock binary
cargo build -j24 --release --features research-multirow --example mq10_profile
ZEEBRA_MACHINE=trpro-5995wx ZEEBRA_AFFINITY=0,1,2,3 tools/benchlock.sh multirow-715 taskset -c 0-3 \
  python3 tools/external/multirow-study.py --stock <stock> --binary <multirow> \
  --scratch <dir> --output research/multirow-reuse/native.json.gz --phase native --build-commit c45bf1eb
python3 research/multirow-reuse/summarize.py research/multirow-reuse/native.json.gz
```

`--phase extension` and `--phase probe` run §5 and §6. The runner refuses an uncommitted tree, a
build source that differs from `--build-commit`, an undeclared machine or affinity, or an existing
output; it waits up to 30 minutes for no build process and a one-minute load under 8 before every
attempt, and re-runs (retaining) an attempt during which a build started. A single attempt is
`mq10_profile <p> --problem=<name> --stages --multirow=single|band4|lanes4`.
