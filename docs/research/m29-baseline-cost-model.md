# M29 frozen baseline and 16-worker F4 cost model (#834)

**Measured at:** `847c4030`. Its production source (`src/`, `Cargo.lock`) is byte-identical to
`main` at `da5b658c` (#841, pair-multiple dedup shipped). The instrument commits on top of it add
only `examples/m29_cost_model.rs`, `tools/cpu-context.sh` and `research/m29-baseline/`. Campaign
date: 2026-11-16, 17:00–18:45 EST. Each suite ran under its own `tools/benchlock.sh zb-834` window.
**Host:** Threadripper PRO 5995WX (`ZEEBRA_MACHINE=5995wx`), `amd-pstate-epp`, `performance`
governor, boost on, kernel 7.3.3. Builds use Rust 1.99.1 (`58cf8f9c3`), release, fat LTO, one
codegen unit, `x86-64-v3`, `RUSTC_WRAPPER=""`, `CARGO_INCREMENTAL=0`.
**Evidence:** [`research/m29-baseline/`](../../research/m29-baseline/README.md) holds the
campaign scripts, the per-child records, the frozen identities and the generated
[tables](../../research/m29-baseline/tables.md).
**Plan:** [`MILESTONE-COMPETITIVE-F4.md`](../MILESTONE-COMPETITIVE-F4.md) §4.

## 1. Findings

1. **The 16-worker F4 call is now dominated by serial stages.** Forward elimination is the only
   parallel stage. It scales 10.7× (MQ10/32003), 11.5× (MQ10/2³¹−1), 13.1× (Eco-12) and 14.4×
   (MQ11) at 16 workers, so it is near-linear and has little headroom left. At 16 workers the
   serial stages take **71–76%** of the F4 call on MQ10 and Eco-12, and **63%** on MQ11.
2. **Candidate finishing (the backward stage) is serial, and it is the largest single opportunity
   on the wide targets.** It takes 770 ms on Eco-12 (21% of process wall) and 2,078 ms on MQ11
   (27%). It gets slightly *slower* at 16 workers (1w/16w = 0.93–0.95, the #827 clock effect). No
   M29 issue owns it; this report files #845 for it.
3. **Symbolic preprocessing is the largest stage on MQ10 and Eco-12 at 16 workers**: 29–32% of
   process wall on MQ10 and 27% on Eco-12.
4. **#828 (parallel FL) cannot reach its 15% gate on any target from this cost model.** The
   forward stage it replaces is 22–34% of process wall and already runs at 67–90% parallel
   efficiency. A parallel FL that kept serial FL's measured work saving (about 16% of forward work)
   at today's efficiency recovers about 4–5%.
5. **#831, measured here at the frozen commit**, is worth 0.71× of process wall on MQ11 serially and
   0.84× at 16 workers. Elsewhere it is 0.89–0.91× serially and 0.96–0.97× at 16 workers, with RSS
   unchanged (0.98–1.00×).
6. **Distance to the goals** (process wall, 16 workers): MQ10 is 2.7× exact-mode msolve at 32003
   and 1.9× at 2³¹−1 (target ≤1.5×). Eco-12 is 2.05× grobx and MQ11 2.36× (target ≤0.90×).
   Goal B needs a 2.28× / 2.63× Zeebra speedup. Against the serial-stage ceilings in §6, that
   needs finishing, symbolic and interreduction all parallelized *and* a real cut in forward work.
   No single mechanism suffices.

## 2. Frozen identities

Full record: [`identities.json`](../../research/m29-baseline/identities.json), with path,
size and SHA-256 for every executable, plus each driver's `--version` JSON.

| Engine | Executable | Version / source | SHA-256 (prefix) |
|---|---|---|---|
| Zeebra cost model | `m29_cost_model` (release) | `847c4030`, production source `da5b658c` | `20f8cb4efa46ea71` |
| Zeebra census | `m29_cost_model_work` (`research-work`) | same | `9906ffa576708dc1` |
| Zeebra comparand driver | `zeebra_driver` (#820) | same | `6594e43916b4d626` |
| Zeebra wide runner | `wide_corpus` (#821, catalog check only) | same | `ce3453311bdacf8b` |
| msolve | `~/.local/opt/zeebra-ext/bin/msolve` | 0.11.0 | `557470de2e13aaa2` |
| grobx | `grobx-driver` (rebuilt from `tools/external/grobx-driver`) | grobx 0.73.3 @ `1854835d`, raw (randomized) mode | `40035ef86d0854f7` |
| groebner-rs | `groebner-rs-driver` (rebuilt from `tools/external/groebner-driver`) | groebner 0.6.0 @ `c3e1d630` | `81dc5c4ce1fd7223` |
| Julia / Groebner.jl | `julia-1.11.7/bin/julia` | Julia 1.11.7 (not timed here) | `0ae4f4b3ab931de6` |
| Singular | `/usr/bin/Singular` | 4.4.1 (reference only, not timed) | `08a5400c9d298342` |
| Sagebrush | `sagebrush-gb-driver` | present, not timed | `83cfc6a292432a36` |

The shared prefix's `grobx-driver` and `groebner-rs-driver` symlinks point into swept
`/buildcache` targets (`zeebra-683-driver`, `zeebra-678`) and are **dangling**. Both drivers were
rebuilt from their pinned lockfiles into this campaign's private target, with the provisioning
scripts' flags. The prefix was not modified. The two drivers' `build`/`build_metadata` hashes are
in `identities.json`.

**Inputs.** MQ10 is `corpus::instance("mq-random-10")`, with its ladder digest asserted at both
primes. Eco-12/2⁶⁴−353 and MQ11/Goldilocks are the frozen #738 rows from
`research/wide-corpus/cases.json`. The instrument refuses a row whose canonical text does not hash
to its pinned digest (`e9ef0fec…` and `ee76de45…`). Every Zeebra run of a target returned one and
the same basis (one SHA-256 over 38 runs per target: 247, 247, 743 and 767 elements).

## 3. Measurement policy (post-#827)

This is task 5 of #834, and it applies to every M29 figure:

- **Process wall is authoritative.** Never clock-normalize. Stage clocks are taken in separate
  runs (`--stages`), because they cost MQ10 3.8–11.5% in the past (#827). Here the clocked and
  unclocked process walls agree to within 1%.
- **Log the context beside the figure, per child.** `tools/cpu-context.sh` snapshots before and
  after: load, each pinned CPU's L3 domain (CCD), core and `scaling_cur_freq`, governor, boost, and
  the number of running compilers. `costmodel.py` also samples the pinned CPUs' clocks every 25 ms.
- **Placement is fixed and CCD-aligned.** A run with *w* workers is pinned to CPUs 8…8+*w*−1. One
  and four workers sit on one CCD, eight fill CCD 1, sixteen span CCDs 1–2. The comparand
  controller keeps its own policy, the first *p* physical cores.
- **Compare serial stages only in the same parallel context.** The serial stages run 6–14% slower
  at 16 workers than at one (symbolic: MQ10 81.7 → 92.8 ms, Eco-12 949 → 1006 ms). That is #827's
  boost hysteresis, and it is not a work change.
- **Pair the denominator.** Every ratio is formed per repetition from runs adjacent in the same
  rotation, then its median is taken. Arm order rotates each repetition.
- **Compiler activity is recorded, not hidden.** Another worktree ran fat-LTO `cargo test --release`
  builds throughout. Four compiler processes were live at the start of every cost-model child, on
  other cores, at 1-minute load 2.8–6.7. The figures are reported with that context. The
  comparand controller refuses outright while a compiler runs, which is why its MQ10 cohort is split
  into windows (§4).

## 4. Worker curves and the comparands

Zeebra, `m29_cost_model`, fresh process (startup, input parse, F4, basis output), stage clocks off,
n=3:

| Target | 1 worker ms | 4 workers ms | 8 workers ms | 16 workers ms | 16w speedup |
|---|---:|---:|---:|---:|---:|
| MQ10 / GF(32003) | 1166.0 [1149.0, 1199.5] | 494.1 [490.8, 500.8] | 369.8 [368.8, 370.7] | 325.4 [321.1, 329.1] | 3.63× |
| MQ10 / GF(2³¹−1) | 981.1 [977.0, 995.9] | 422.9 [420.9, 428.8] | 328.9 [325.4, 329.3] | 296.0 [293.3, 296.4] | 3.34× |
| Eco-12 / 2⁶⁴−353 | 13449.7 [13248.1, 13757.2] | 5739.1 [5650.7, 5747.5] | 4295.0 [4292.4, 4325.1] | 3709.8 [3682.8, 3748.1] | 3.63× |
| MQ11 / Goldilocks | 43358.1 [41686.7, 43825.3] | 14791.7 [14691.9, 15093.4] | 10053.2 [9935.8, 10160.2] | 7649.9 [7541.2, 7747.7] | 5.60× |

Against the earlier figures, the 16-worker cells moved from #820's 340.7/314.1 ms (MQ10) and #821's
3,880/9,230 ms (Eco-12/MQ11). Most of the MQ11 move is #831 (§7). Serial MQ11 now completes in
43 s. It hit #821's 60 s wall.

**MQ10 against exact-mode msolve**: `comparand-scaling.py`, every answer verified against #739's
exact references, fresh process with I/O. The controller stops a window the moment any compiler
starts on the machine, and another worktree's builds ended windows 1 and 2 early. MQ10_WINDOWS

**Wide targets against grobx and groebner-rs** (`wide-corpus.py`, one worker, CPU 8, three passes).
grobx's basis is text-identical to Zeebra's. groebner-rs's agrees with grobx under the controller's
canonical comparison:

| Target | grobx ms (n=3) | groebner-rs ms (n=3) | Zeebra 16w ms | Zeebra / grobx | Zeebra needed for a 10% lead | speedup needed |
|---|---:|---:|---:|---:|---:|---:|
| Eco-12 / 2⁶⁴−353 | 1806.0 [1748.1, 1862.4] | 3311.6 [3204.4, 3317.8] | 3709.8 | 2.05× | ≤1625 | 2.28× |
| MQ11 / Goldilocks | 3236.3 [3209.6, 4067.0] | 9834.7 [9796.8, 10130.3] | 7649.9 | 2.36× | ≤2913 | 2.63× |

grobx measured 1,619/2,925–3,326 ms in #738, on CPU 2. Eco-12 here is 1,806 ms, and nothing in this
campaign separates the placement difference from the ambient load (§3), so the 10% lead is set
against this session's figure. These are common-budget comparisons: Zeebra on 16 cores, grobx
serial (its only supported mode).

## 5. Cost model per target

Stage clocks on, n=3 medians, 16 workers unless stated. *Share* is of the 16-worker process wall
in §4, which is the figure a mechanism must move. *Outside F4* is process wall minus the F4 call:
startup, input parsing and basis formatting. Full 1/4/8/16 tables:
[tables.md](../../research/m29-baseline/tables.md).

| Stage, 16 workers | MQ10/32003 ms (share) | MQ10/2³¹−1 | Eco-12 | MQ11 |
|---|---:|---:|---:|---:|
| F4 call (clocked total) | 292.1 | 264.8 | 3445.9 | 6890.3 |
| symbolic preprocessing | 92.8 (28.5%) | 94.0 (31.8%) | 1005.9 (27.1%) | 1307.6 (17.1%) |
| matrix construction | 23.1 (7.1%) | 22.6 (7.6%) | 146.5 (3.9%) | 210.6 (2.8%) |
| forward elimination (parallel) | 83.9 (25.8%) | 68.3 (23.1%) | 811.7 (21.9%) | 2569.3 (33.6%) |
| candidate finishing (serial backward) | 54.3 (16.7%) | 40.9 (13.8%) | 770.0 (20.8%) | 2078.4 (27.2%) |
| extraction | 9.1 (2.8%) | 9.2 (3.1%) | 70.1 (1.9%) | 135.5 (1.8%) |
| interreduction | 13.6 (4.2%) | 13.5 (4.6%) | 516.1 (13.9%) | 346.7 (4.5%) |
| other in-F4 | 15.5 (4.8%) | 15.5 (5.2%) | 130.5 (3.5%) | 245.8 (3.2%) |
| outside F4 | 31.9 (9.8%) | 32.4 (10.9%) | 221.4 (6.0%) | 697.3 (9.1%) |
| **serial share of the F4 call** | **71%** | **74%** | **76%** | **63%** |
| serial share at 1 worker | 17% | 18% | 19% | 10% |
| forward-stage speedup 1→16 | 10.75× | 11.54× | 13.12× | 14.37× |
| finishing 1w / 16w | 0.93 | 0.95 | 0.94 | 0.94 |

**Work, matrices and memory.** `F4Statistics` from the clocked runs. Counters are identical at
every worker count except the parallel schedule's own (lost publications, reservations):

| Counter | MQ10/32003 | MQ10/2³¹−1 | Eco-12 | MQ11 |
|---|---:|---:|---:|---:|
| batches | 10 | 10 | 23 | 12 |
| pairs reduced / pair halves removed (#831) | 1,777 / 339 | 1,777 / 339 | 7,202 / 1,414 | 7,059 / 3,753 |
| matrix rows, total / of which reducers | 52,440 / 49,225 | 52,440 / 49,225 | 162,030 / 149,040 | 60,198 / 49,833 |
| largest matrix rows × columns | 12,391 × 12,020 | 12,391 × 12,020 | 24,045 × 24,913 | 8,904 × 9,436 |
| fill, entries / (rows × cols), weighted | 0.51% | 0.51% | 1.23% | 7.28% |
| initial entries, summed over batches | 2,523,210 | 2,523,227 | 26,993,014 | 36,569,205 |
| row applications (`row_operations`) | 7,427,960 | 7,428,169 | 33,927,390 | 27,756,303 |
| forward coefficient products (serial census) | 518.3 M | 518.3 M | 5,581 M | 19,333 M |
| — against inherited (reducer) pivots | 270.7 M (52.2%) | 270.7 M (52.2%) | 4,541 M (81.4%) | 14,569 M (75.4%) |
| — against pivots discovered in the batch | 247.6 M (47.8%) | 247.6 M (47.8%) | 1,040 M (18.6%) | 4,764 M (24.6%) |
| finishing products / targets | 23.6 M / 250 | 23.6 M / 250 | 342.7 M / 876 | 1,044 M / 766 |
| peak live entries, 1w → 16w | 1.15 M → 1.79 M | 1.15 M → 1.79 M | 4.14 M → 5.19 M | 7.02 M → 8.78 M |
| finishing reservation (entries) | 1.10 M | 1.10 M | 4.05 M | 5.21 M |
| parallel-forward reservation / workspace | 1.79 M / 1.4 MB | 1.79 M / 2.2 MB | 5.19 M / 4.6 MB | 8.78 M / 1.7 MB |
| estimated peak matrix bytes, 16w | 30.2 MB | 31.1 MB | 86.8 MB | 142.5 MB |
| lost publications, 16w | 504 | 623 | 1,770 | 874 |
| peak RSS, 1w → 16w | 33 → 39 MiB | 34 → 41 MiB | 182 → 198 MiB | 355 → 390 MiB |

"Inherited" products are those against a pivot whose row precedes the batch's first pair row: the
reducer sweep. "Discovered" products are those against a pivot found among the pair rows in this
batch. The split comes from the serial `--discovery` census. Under parallel forward it is the same
algebra on a different schedule, plus the lost publications above. Every row application in the
structured route targets a pair row, so the census's reducer-target count is zero.

## 6. Predicted maximum recoverable improvement per mechanism

Each row prices one mechanism alone against the 16-worker process wall, with today's measured
stage times. **Ceiling** sets the stage it acts on to zero. **Plausible** applies the best evidence
on record for what the mechanism achieves. Estimates must not be multiplied. Re-profile after each
merge (plan §11).

| Mechanism | Acts on | MQ10/32003 | MQ10/2³¹−1 | Eco-12 | MQ11 | Basis for "plausible" |
|---|---|---:|---:|---:|---:|---|
| **#831** pair-multiple dedup (shipped) | symbolic + forward | **measured 0.974×** | **0.970×** | **0.962×** | **0.839×** | §7, at this commit |
| **#828** parallel FL — ceiling | forward | −25.8% | −23.1% | −21.9% | −33.6% | forward → 0 |
| #828 — plausible | forward | −4.1% | −3.7% | −3.5% | −5.4% | serial FL's −16% forward work (PR #829 MQ10 1139 → 992 ms), at today's 67–90% efficiency |
| #828 — needed for its 15% gate | forward | −58% of forward | −65% | −68% | −45% | — |
| **#832** parallel symbolic — plausible as prototyped | symbolic | −7.8% | −8.7% | −7.5% | −4.7% | #827's 1.38× stage speedup at 16 workers |
| #832 — with parallel interning (≈4×) | symbolic | −21.4% | −23.8% | −20.3% | −12.8% | hypothetical; the commit is ~⅔ of the stage today |
| #832 — ceiling | symbolic | −28.5% | −31.8% | −27.1% | −17.1% | symbolic → 0 |
| **parallel candidate finishing** (new, #845) | backward | −15.1% | −12.6% | −19.2% | −25.3% | targets are independent over read-only pivots; at the forward stage's measured efficiency |
| — ceiling | backward | −16.7% | −13.8% | −20.8% | −27.2% | finishing → 0 |
| **C2-1** work-avoiding exact reduction (#836) | forward + finishing products | −4.3% per 10% of products removed | −3.7% | −4.3% | −6.1% | linear in products at unchanged efficiency |
| **C2-2** #809 Simplify, reducer reuse — ceiling | inherited forward work (+ part of symbolic) | −13.5% | −12.0% | −17.8% | −25.3% | all inherited-pivot products removed. Unattainable in full, because Simplify shortens reducers and does not delete them. Needs #835's ledger |
| **C2-3** less row materialization — ceiling | construction + extraction | −9.9% | −10.7% | −5.8% | −4.5% | stages → 0 |
| **C2-4** field-width kernels | forward + finishing arithmetic | −9.8% | −8.5% | −9.8% | −14.0% | a 1.3× kernel on both stages. If finishing is parallelized first: −6% / −5% / −5% / −8% |
| (not proposed) parallel interreduction — ceiling | interreduction | −4.2% | −4.6% | −13.9% | −4.5% | stage → 0 |
| (not proposed) basis output — ceiling | outside F4 | ≤ −9.8% | ≤ −10.9% | ≤ −6.0% | ≤ −9.1% | includes unavoidable startup; worth measuring on MQ11 (697 ms) |

**Reading against the goals.**

- **Goal A, 2³¹−1** (needs about −22% to reach ≤1.5× of msolve's 158 ms best). Parallel
  finishing (−12.6%) plus prototype-grade parallel symbolic (−8.7%) roughly reaches it on paper.
  Re-measure after each, rather than add the two.
- **Goal A, 32003** (needs about −45%, from about 325 ms to ≤179–184 ms). Even finishing, symbolic
  with parallel interning, and plausible FL together sum to about −40% before interaction. Goal A
  at 32003 needs work reduction as well, not only parallelism.
- **Goal B** (Eco-12 −56%, MQ11 −62%). The parallelism ceilings for finishing, symbolic and
  interreduction sum to 62% on Eco-12 and 49% on MQ11. A realistic parallel efficiency leaves both
  short. The remainder has to come from removing forward work, and on these targets 75–81% of that
  work is the reducer sweep (inherited pivots). That is the C1 question #835 is set up to answer.

**Gate (plan §4) applied.** #828's claimed benefit is not supported by the current 16-worker cost
model. The forward stage it replaces is near-linear already, so its 15% gate requires cutting
45–68% of forward work. That is about three to four times serial FL's measured saving. #828 should
run only as the bounded feasibility experiment the plan already limits it to, and should be closed
on a miss. #832 is supported only with parallel interning. On MQ10 and Eco-12 its prototype figure
(−8%) falls short of the plan's 10% threshold.

## 7. #831, measured at the frozen commit

`--pair-multiples every` against the default `distinct`, process wall, n=3 paired:

| Target | Workers | Every ms | Distinct ms | Distinct / Every | halves removed | RSS ratio |
|---|---:|---:|---:|---:|---:|---:|
| MQ10/32003 | 1 | 1253.2 | 1142.3 | 0.912× | 339 | 0.993× |
| MQ10/32003 | 16 | 334.3 | 325.7 | 0.974× | 339 | 0.978× |
| MQ10/2³¹−1 | 1 | 1097.6 | 1002.2 | 0.910× | 339 | 0.992× |
| MQ10/2³¹−1 | 16 | 308.2 | 297.9 | 0.970× | 339 | 0.984× |
| Eco-12 | 1 | 15043.2 | 13334.9 | 0.887× | 1,414 | 1.001× |
| Eco-12 | 16 | 3832.0 | 3665.2 | 0.962× | 1,414 | 1.000× |
| MQ11 | 1 | 59429.7 | 42032.1 | 0.707× | 3,753 | 0.991× |
| MQ11 | 16 | 9028.8 | 7602.1 | 0.839× | 3,753 | 1.000× |

This agrees with #841's own figures at `9d3e45a7`: MQ10 0.89–0.97×, and Katsura-11 0.80× serial
and 0.91× at 16 workers. It adds the wide targets. MQ11 is the largest effect recorded for #831:
3,753 of 14,118 pair halves were repeats.

## 8. What this does not show

- n=3 per Zeebra cell and n=3 per wide comparand, with MQ10 comparand cells split across controller
  windows. That is enough to rank stages, not enough to grade a goal. #837's final protocol (≥9
  interleaved measurements) still applies.
- The comparands were not re-run at 1/4/8/16 on the wide targets. grobx's pinned driver is serial,
  and wide-corpus refuses comparand workers above one.
- No exact certification was run here. Zeebra's wide bases are text-identical to grobx's, and that
  is agreement between engines, not proof (plan §2.2). MQ10 answers are verified against #739's
  references.
- Julia/Groebner.jl was not timed. It is startup-dominated on these rows (#738) and is not the
  best comparand on any target.
- "Plausible" figures are models built from this cost table and earlier evidence, not
  measurements.
