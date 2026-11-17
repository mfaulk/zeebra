# M29 frozen baseline and 16-worker F4 cost model (#834)

**Measured at:** `7251e775` (the quiet campaign, every figure in §1–§7 unless marked), and
`6e2b93ea` (PR #843's head, the §6a cross-check, with this branch's `examples/m29_cost_model.rs`
overlaid). `7251e775`'s production source (`src/`, `Cargo.lock`) is byte-identical to `main` at
`60e99587` (#842). `6e2b93ea` is #843's parallel FL on that same base. The superseded first pass
(§9) was measured at `847c4030` and `772be618`, pre-rebase hashes whose production source is `main`
at `da5b658c`. Quiet campaign: 2026-11-16, 19:59–20:57 EST, no compiler running at the start or
end of any child, 1-minute load 1.1–4.1 (FL cross-check 1.7–9.8), seven `tools/benchlock.sh zb-834`
windows with nothing else queued.
**Host:** Threadripper PRO 5995WX (`ZEEBRA_MACHINE=5995wx`), `amd-pstate-epp`, `performance`
governor, boost on, kernel 7.3.3. Builds use Rust 1.99.1 (`58cf8f9c3`), release, fat LTO, one
codegen unit, `x86-64-v3`, `RUSTC_WRAPPER=""`, `CARGO_INCREMENTAL=0`.
**Evidence:** [`research/m29-baseline/quiet/`](../../research/m29-baseline/quiet/tables.md) holds the
quiet campaign's per-child records, identities and generated tables. The first pass stays in
[`research/m29-baseline/`](../../research/m29-baseline/README.md), unpooled.
**Plan:** [`MILESTONE-COMPETITIVE-F4.md`](../MILESTONE-COMPETITIVE-F4.md) §4.

## 1. Findings

1. **The 16-worker F4 call is now dominated by serial stages.** Forward elimination is the only
   parallel stage. It scales 10.7× (MQ10/32003), 10.8× (MQ10/2³¹−1), 12.5× (Eco-12) and 14.1×
   (MQ11) at 16 workers, so it is near-linear and has little headroom left. At 16 workers the
   serial stages take **72–76%** of the F4 call on MQ10 and Eco-12, and **63%** on MQ11.
2. **Candidate finishing (the backward stage) is serial, and it is the largest single opportunity
   on the wide targets.** It takes 738 ms on Eco-12 (21% of process wall) and 2,061 ms on MQ11
   (28%). It gets *slower* at 16 workers (1w/16w = 0.89–0.93, the #827 clock effect).
3. **#843's parallel FL removes that stage, and that is where its gain comes from (§6a).** Measured
   against the default order from the same binary at 16 workers: **1.145× on Eco-12 and 1.272× on
   MQ11** (F4 call; 1.134× / 1.243× process wall), with the same basis. The serial backward stage
   falls from 770 to 83 ms on Eco-12 and from 2,042 to 171 ms on MQ11. Forward elimination grows
   by about 230 ms on both. **The cost model's #828 prediction (−3.5% / −5.4%) was wrong**: it
   priced FL as a forward-work cut and missed that FL moves candidate finishing into the parallel
   phase. Priced as that, the model predicts −12.4% / −22.7% against −11.8% / −19.5% measured.
4. **Symbolic preprocessing is the largest stage on MQ10 and Eco-12 at 16 workers**: 29–32% of
   process wall on MQ10 and 27% on Eco-12.
5. **#831, measured at this commit**, is worth 0.71× of process wall on MQ11 serially and 0.84×
   at 16 workers. Elsewhere it is 0.90× serially and 0.96–0.97× at 16 workers, with RSS unchanged
   (0.97–1.00×).
6. **Distance to the goals** (process wall, 16 workers): MQ10 is 2.77× exact-mode msolve at 32003
   and 1.93× at 2³¹−1 (target ≤1.5×). Eco-12 is 2.21× grobx and MQ11 2.53× (target ≤0.90×), so
   Goal B needs a 2.45× / 2.81× Zeebra speedup. Against the serial-stage ceilings in §6, that needs
   finishing (or #843), symbolic and interreduction all parallelized *and* a real cut in forward
   work. No single mechanism suffices.
7. **What the quiet rerun changed.** Zeebra's 16-worker walls moved by −1.2% to +0.1% on MQ10 and
   −3.5% / −2.8% on the wide targets. Its serial walls fell 5.6–7.7%, so the first pass's compiler
   load hurt the one-worker cells most. The serial comparands got faster too (grobx −10% / −9%), so
   every Zeebra/comparand ratio is *worse* than first reported (§9). Only the #828 conclusion
   reversed, and that was a modelling error, not noise (§6a).

## 2. Frozen identities

Full record: [`quiet/identities.json`](../../research/m29-baseline/quiet/identities.json), with
path, size and SHA-256 for every executable, plus each driver's `--version` JSON.

| Engine | Executable | Version / source | SHA-256 (prefix) |
|---|---|---|---|
| Zeebra cost model | `m29_cost_model` (release) | `7251e775`, production source `60e99587` | `750a6f7335d21781` |
| Zeebra cost model, #843 head | `m29_cost_model` built at `6e2b93ea` + this example | #843, base `60e99587` | `41fe7437cc221803` |
| Zeebra census | `m29_cost_model_work` (`research-work`) | first pass, `da5b658c` (counts only, §5) | `9906ffa576708dc1` |
| Zeebra comparand driver | `zeebra_driver` (#820) | `7251e775` | `6594e43916b4d626` |
| Zeebra wide runner | `wide_corpus` (#821, catalog check only) | `7251e775` | `ce3453311bdacf8b` |
| msolve | `~/.local/opt/zeebra-ext/bin/msolve` | 0.11.0 | `557470de2e13aaa2` |
| grobx | `grobx-driver` (rebuilt from `tools/external/grobx-driver`) | grobx 0.73.3 @ `1854835d`, raw (randomized) mode | `40035ef86d0854f7` |
| groebner-rs | `groebner-rs-driver` (rebuilt from `tools/external/groebner-driver`) | groebner 0.6.0 @ `c3e1d630` | `81dc5c4ce1fd7223` |
| Julia / Groebner.jl | `julia-1.11.7/bin/julia` | Julia 1.11.7 (not timed here) | `0ae4f4b3ab931de6` |
| Singular | `/usr/bin/Singular` | 4.4.1 (reference only, not timed) | `08a5400c9d298342` |
| Sagebrush | `sagebrush-gb-driver` | present, not timed | `83cfc6a292432a36` |

`zeebra_driver` and `wide_corpus` rebuilt at `7251e775` came out byte-identical to the first
pass's. The shared prefix's `grobx-driver` and `groebner-rs-driver` symlinks point into swept
`/buildcache` targets (`zeebra-683-driver`, `zeebra-678`) and are **dangling**. Both drivers were
rebuilt from their pinned lockfiles into this campaign's private target, with the provisioning
scripts' flags. The prefix was not modified.

**Inputs.** MQ10 is `corpus::instance("mq-random-10")`, with its ladder digest asserted at both
primes. Eco-12/2⁶⁴−353 and MQ11/Goldilocks are the frozen #738 rows from
`research/wide-corpus/cases.json`. The instrument refuses a row whose canonical text does not hash
to its pinned digest (`e9ef0fec…` and `ee76de45…`). Every Zeebra run of a target returned one and
the same basis: one SHA-256 over 60 runs per MQ10 target and 80 per wide target, counting #843's
FL runs (247, 247, 743 and 767 elements).

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
- **Compare serial stages only in the same parallel context.** The serial stages run 1–19% slower
  at 16 workers than at one (symbolic: MQ10 78.8 → 93.5 ms, Eco-12 895 → 961 ms). That is #827's
  boost hysteresis, and it is not a work change.
- **Pair the denominator.** Every ratio is formed per repetition from runs adjacent in the same
  rotation, then its median is taken. Arm order rotates each repetition.
- **Compiler activity is recorded, not hidden.** The quiet campaign recorded zero compilers at the
  start and end of all 280 children, and every comparand window completed on its first attempt.
  The first pass ran beside another worktree's fat-LTO builds and is kept separately (§9).

## 4. Worker curves and the comparands

Zeebra, `m29_cost_model`, fresh process (startup, input parse, F4, basis output), stage clocks off,
n=5, median [min, max]:

| Target | 1 worker ms | 4 workers ms | 8 workers ms | 16 workers ms | 16w speedup |
|---|---:|---:|---:|---:|---:|
| MQ10 / GF(32003) | 1076.7 [1071.5, 1100.4] | 446.4 [442.6, 460.5] | 366.3 [365.9, 367.5] | 321.6 [320.5, 323.6] | 3.36× |
| MQ10 / GF(2³¹−1) | 917.1 [913.9, 924.6] | 403.1 [397.6, 420.3] | 328.7 [327.8, 330.1] | 296.2 [295.9, 299.3] | 3.09× |
| Eco-12 / 2⁶⁴−353 | 12692.7 [12674.8, 12714.9] | 5313.6 [5264.9, 5323.2] | 4224.7 [4209.1, 4230.8] | 3581.6 [3564.6, 3587.2] | 3.54× |
| MQ11 / Goldilocks | 40596.5 [40532.1, 40632.9] | 13711.8 [13641.0, 13805.3] | 9808.4 [9790.7, 9847.5] | 7432.8 [7402.2, 7442.6] | 5.47× |

Against the earlier figures,
the 16-worker cells moved from #820's 340.7/314.1 ms (MQ10) and #821's 3,880/9,230 ms
(Eco-12/MQ11). Most of the MQ11 move is #831 (§7). Serial MQ11 now completes in 41 s. It hit #821's
60 s wall.

**MQ10 against exact-mode msolve**: `comparand-scaling.py`, every answer verified against #739's
exact references, fresh process with I/O, one window, n=5 per cell:

| Engine (n=5) | GF(32003) 1w | 4w | 8w | 16w | GF(2³¹−1) 1w | 4w | 8w | 16w |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| Zeebra (`zeebra_driver`) | 1063.7 | 450.0 | 368.7 | 326.6 | 916.0 | 412.0 | 332.5 | 305.1 |
| msolve 0.11.0 (exact) | 214.7 | 121.7 | **117.8** | 147.6 [125–1005] | 233.4 | **157.9** | 467.0 | 370.2 [201–832] |
| groebner-rs (randomized) | 117.7 | 83.3 | 89.0 | 96.8 | 154.5 | 95.7 | 97.1 | 108.9 |
| grobx (randomized raw, serial only) | 337.6 | — | — | — | 158.0 | — | — | — |

Milliseconds, medians. msolve at 16 threads, and at 8 on 2³¹−1, is erratic on a quiet machine too,
so its best configuration within 16 cores is taken, as plan §2.1 requires:

| Field | Zeebra 16w ms | best exact msolve ≤16 cores ms | Zeebra / msolve | Zeebra needed for ≤1.5× | speedup needed |
|---|---:|---:|---:|---:|---:|
| GF(32003) | 326.6 | 117.8 (8 threads) | 2.77× | ≤176.7 | 1.85× |
| GF(2³¹−1) | 305.1 | 157.9 (4 threads) | 1.93× | ≤236.8 | 1.29× |

This reproduces #820 (Zeebra 340.7/314.1 ms, msolve 116.8/167.0 ms) to within 6%.

**Wide targets against grobx and groebner-rs** (`wide-corpus.py`, one worker, CPU 8, five passes).
grobx's basis is text-identical to Zeebra's. groebner-rs's agrees with grobx under the controller's
canonical comparison:

| Target | grobx ms (n=5) | groebner-rs ms (n=5) | Zeebra 16w ms | Zeebra / grobx | Zeebra needed for a 10% lead | speedup needed |
|---|---:|---:|---:|---:|---:|---:|
| Eco-12 / 2⁶⁴−353 | 1623.5 [1618.9, 1636.0] | 3037.0 [2936.1, 3055.3] | 3581.6 | 2.21× | ≤1461 | 2.45× |
| MQ11 / Goldilocks | 2935.4 [2931.0, 2941.9] | 9046.4 [9015.8, 9056.6] | 7432.8 | 2.53× | ≤2642 | 2.81× |

grobx measured 1,619/2,925–3,326 ms in #738 on CPU 2, which the quiet figures now match. These are
common-budget comparisons: Zeebra on 16 cores, grobx serial (its only supported mode).

## 5. Cost model per target

Stage clocks on, n=5 medians, 16 workers unless stated. *Share* is of the 16-worker process wall
in §4, which is the figure a mechanism must move. *Outside F4* is the clocked runs' process wall
minus their F4 call: startup, input parsing and basis formatting. Full 1/4/8/16 tables:
[quiet/tables.md](../../research/m29-baseline/quiet/tables.md).

| Stage, 16 workers | MQ10/32003 ms (share) | MQ10/2³¹−1 | Eco-12 | MQ11 |
|---|---:|---:|---:|---:|
| F4 call (clocked total) | 292.0 | 262.9 | 3375.0 | 6799.4 |
| symbolic preprocessing | 93.5 (29.1%) | 93.4 (31.5%) | 960.6 (26.8%) | 1259.8 (16.9%) |
| matrix construction | 23.1 (7.2%) | 22.9 (7.7%) | 144.2 (4.0%) | 208.7 (2.8%) |
| forward elimination (parallel) | 81.1 (25.2%) | 67.7 (22.9%) | 811.6 (22.7%) | 2544.8 (34.2%) |
| candidate finishing (serial backward) | 55.0 (17.1%) | 41.0 (13.8%) | 737.5 (20.6%) | 2061.3 (27.7%) |
| extraction | 9.1 (2.8%) | 9.2 (3.1%) | 68.0 (1.9%) | 128.6 (1.7%) |
| interreduction | 14.1 (4.4%) | 13.6 (4.6%) | 522.9 (14.6%) | 339.8 (4.6%) |
| other in-F4 | 16.1 (5.0%) | 15.2 (5.1%) | 130.2 (3.6%) | 256.4 (3.4%) |
| outside F4 | 32.7 (10.2%) | 33.9 (11.4%) | 206.7 (5.8%) | 645.5 (8.7%) |
| **serial share of the F4 call** | **72%** | **74%** | **76%** | **63%** |
| serial share at 1 worker | 17% | 18% | 19% | 10% |
| forward-stage speedup 1→16 | 10.73× | 10.77× | 12.51× | 14.10× |
| finishing 1w / 16w | 0.89 | 0.89 | 0.89 | 0.93 |

**Work, matrices and memory.** `F4Statistics` from the clocked runs. Counters are identical at
every worker count except the parallel schedule's own (lost publications, reservations). The
product census is the first pass's serial `--discovery` run: it counts operations, not time, and
`7251e775` changes no F4 code it counts.

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
| peak live entries, 1w → 16w | 1.15 M → 1.79 M | 1.15 M → 1.78 M | 4.14 M → 5.19 M | 7.02 M → 8.76 M |
| finishing reservation (entries) | 1.11 M | 1.10 M | 4.05 M | 5.19 M |
| parallel-forward reservation / workspace | 1.79 M / 1.4 MB | 1.78 M / 2.2 MB | 5.19 M / 4.6 MB | 8.76 M / 1.7 MB |
| estimated peak matrix bytes, 16w | 30.3 MB | 31.0 MB | 86.9 MB | 142.2 MB |
| lost publications, 16w | 575 | 619 | 1,721 | 858 |
| peak RSS, 1w → 16w | 33 → 39 MiB | 34 → 41 MiB | 182 → 198 MiB | 355 → 390 MiB |

"Inherited" products are those against a pivot whose row precedes the batch's first pair row: the
reducer sweep. "Discovered" products are those against a pivot found among the pair rows in this
batch. Under parallel forward it is the same algebra on a different schedule, plus the lost
publications above. Every row application in the structured route targets a pair row, so the
census's reducer-target count is zero.

## 6. Predicted maximum recoverable improvement per mechanism

Each row prices one mechanism alone against the 16-worker process wall, with today's measured
stage times. **Ceiling** sets the stage it acts on to zero. **Plausible** applies the best evidence
on record for what the mechanism achieves. Estimates must not be multiplied. Re-profile after each
merge (plan §11).

| Mechanism | Acts on | MQ10/32003 | MQ10/2³¹−1 | Eco-12 | MQ11 | Basis for "plausible" |
|---|---|---:|---:|---:|---:|---|
| **#831** pair-multiple dedup (shipped) | symbolic + forward | **measured 0.964×** | **0.966×** | **0.965×** | **0.836×** | §7, at this commit |
| **#828/#843** parallel FL — **measured** | finishing → forward | #843: 0.86–0.89× | — | **0.882×** | **0.805×** | §6a, process wall, paired |
| #828 — as originally modelled (wrong) | forward | −4.0% | −3.7% | −3.6% | −5.5% | serial FL's −16% forward work (PR #829) at today's efficiency. Missed the stage FL actually removes (§6a) |
| #828 — remodelled | finishing → forward | — | — | −12.4% | −22.7% | finishing → finishing / forward speedup, plus FL's measured forward growth |
| **#832** parallel symbolic — plausible as prototyped | symbolic | −8.0% | −8.7% | −7.4% | −4.7% | #827's 1.38× stage speedup at 16 workers |
| #832 — with parallel interning (≈4×) | symbolic | −21.8% | −23.6% | −20.1% | −12.7% | hypothetical; the commit is ~⅔ of the stage today |
| #832 — ceiling | symbolic | −29.1% | −31.5% | −26.8% | −16.9% | symbolic → 0 |
| **parallel candidate finishing** (#845) | backward | −15.5% | −12.6% | −18.9% | −25.8% | targets are independent over read-only pivots; at the forward stage's measured efficiency. **Measured (§6b): −11.2% / −8.5% / −13.9% / −22.6%, shipped in the default order** |
| — ceiling | backward | −17.1% | −13.8% | −20.6% | −27.7% | finishing → 0 |
| **C2-1** work-avoiding exact reduction (#836) | forward + finishing products | −4.2% per 10% of products removed | −3.7% | −4.3% | −6.2% | linear in products at unchanged efficiency |
| **C2-2** #809 Simplify, reducer reuse — ceiling | inherited forward work (+ part of symbolic) | −13.2% | −11.9% | −18.4% | −25.8% | all inherited-pivot products removed. Unattainable in full, because Simplify shortens reducers and does not delete them. Needs #835's ledger |
| **C2-3** less row materialization — ceiling | construction + extraction | −10.0% | −10.8% | −5.9% | −4.5% | stages → 0 |
| **C2-4** field-width kernels | forward + finishing arithmetic | −9.8% | −8.5% | −10.0% | −14.3% | a 1.3× kernel on both stages. If finishing is parallelized first: −6% / −6% / −6% / −8% |
| (not proposed) parallel interreduction — ceiling | interreduction | −4.4% | −4.6% | −14.6% | −4.6% | stage → 0 |
| (not proposed) basis output — ceiling | outside F4 | ≤ −10.2% | ≤ −11.4% | ≤ −5.8% | ≤ −8.7% | includes unavoidable startup; worth measuring on MQ11 (646 ms) |

**Reading against the goals.**

- **Goal A, 2³¹−1** (needs about −22%: from 305 ms to ≤237 ms, 1.5× msolve's 157.9 ms best).
  Parallel finishing (−12.6%) plus prototype-grade parallel symbolic (−8.7%) sum to −21%, just
  short on paper. #843's own MQ10 figure (1.12–1.16×, −11 to −14%) is in the same range as the
  finishing row. Re-measure after each, rather than add the two.
- **Goal A, 32003** (needs about −46%: from 327 ms to ≤177 ms, 1.5× msolve's 117.8 ms). Finishing,
  symbolic with parallel interning and interreduction together sum to about −42% before
  interaction. Goal A at 32003 needs work reduction as well, not only parallelism.
- **Goal B** (Eco-12 −59%, MQ11 −64%). The parallelism ceilings for finishing, symbolic and
  interreduction sum to 62% on Eco-12 and 49% on MQ11. A realistic parallel efficiency leaves both
  short. The remainder has to come from removing forward work, and on these targets 75–81% of that
  work is the reducer sweep (inherited pivots). That is the C1 question #835 is set up to answer.

**Gate (plan §4) applied, revised.** The first version of this section said #828's benefit was not
supported by the cost model. That rested on the misattribution in §6a and is withdrawn. Measured,
#843 clears the 15% gate on MQ11 (−19.5% process wall) and misses it on Eco-12 (−11.8%) and, by
#843's own figures, on MQ10 (−11 to −14%). #843 and #845 act on the same serial stage. With #843
merged, finishing would be 83 ms on Eco-12 and 171 ms on MQ11 (2.3% of process wall each), so #845
should be re-scoped against #843 rather than run beside it. #832 is supported only with parallel
interning. On MQ10 and Eco-12 its prototype figure (−7 to −9%) falls short of the plan's 10%
threshold.

## 6a. #828 cross-check: parallel FL measured on the wide targets

The coordinator asked why PR #843 measured 1.12–1.16× on MQ10 and 1.28× on Katsura-11 when §6
predicted −4 to −5%. #843's head (`6e2b93ea`) was built in a separate private target with this
branch's `m29_cost_model` overlaid, so `--batch-order forward|fl` selects
`BatchOrder::{Forward, FaugereLachartre}` with no source change. Both arms come from that one
binary, at 16 workers on CPUs 8–23, interleaved with rotated order, n=5 per arm, in one benchlock
window. A second window (`flstages`) repeated the pairs with stage clocks on. All 40 runs returned
the production basis.

| Target | default order ms (F4 call) | FL ms | default / FL, F4 call | default / FL, process wall |
|---|---:|---:|---:|---:|
| Eco-12 / 2⁶⁴−353 | 3396.1 [3380.6, 3402.8] | 2962.1 [2959.9, 2977.5] | **1.145×** [1.137, 1.149] | 1.134× |
| MQ11 / Goldilocks | 6757.8 [6749.6, 6782.3] | 5314.8 [5293.3, 5329.3] | **1.272×** [1.268, 1.276] | 1.243× |

Stage clocks on, medians, ms:

| Target | order | symbolic | construction | forward | backward | extraction | interreduction | row applications |
|---|---|---:|---:|---:|---:|---:|---:|---:|
| Eco-12 | default | 958.1 | 143.5 | 807.1 | 769.8 | 67.4 | 506.1 | 33.9 M |
| Eco-12 | FL | 987.8 | 134.4 | 1040.9 | **83.2** | 74.8 | 508.0 | 39.0 M |
| MQ11 | default | 1261.2 | 207.4 | 2548.2 | 2041.8 | 126.1 | 333.3 | 27.9 M |
| MQ11 | FL | 1316.4 | 252.0 | 2778.7 | **170.7** | 145.3 | 368.5 | 22.8 M |

**Reconciliation.** §6 priced #828 as a cut in forward work: serial FL's −16% forward work, applied
to a stage that is 23–34% of process wall and already near-linear. The measurement shows a
different mechanism. Under FL the candidate rows are reduced inside the parallel forward phase, so
the serial backward stage nearly disappears (−687 ms on Eco-12, −1,871 ms on MQ11). Forward grows by
234 / 231 ms to absorb that work. Forward *work* does not consistently fall: row applications rise
15% on Eco-12 and fall 18% on MQ11. So the gain is the parallel-finishing row of §6, not the FL
row. Pricing it that way, the finishing row's −18.9% / −25.8% less the measured forward growth
(6.5% / 3.1% of process wall) predicts −12.4% / −22.7%. Measured is −11.8% / −19.5%, which is
within about 3 points. The remaining gap is the small growth in symbolic, construction and
extraction under FL (+30 to +60 ms), which the model does not cover.

The model's stage table was right; the attribution of FL to a stage was wrong. Two lessons for the
M29 gate: price a mechanism by the stages it actually moves, measured with stage clocks, and
expect #843 and #845 to compete for the same 21–28% of process wall.

## 6b. #845 measured: parallel candidate finishing in the default order

**Measured at:** base `6a78e91a`, new `6efb70a5` (records and provenance in
[`research/m29-845/`](../../research/m29-845/README.md)). Same host and 16-worker pinning as §6a,
fresh process per run, three arms interleaved with rotated order in two `benchlock zb-845`
windows: base, new (both the default forward order) and base with `--batch-order fl` (#843).
Load was 1.2–7.4 with no compiler running, so absolute walls are slightly above §4's quiet figures;
ratios are paired per window. Every run returned the production basis.

Process wall, n=5, median [min, max], ms:

| Target | base | #845 | base / #845 | base FL | base / FL | RSS #845 / base | RSS FL / base |
|---|---:|---:|---:|---:|---:|---:|---:|
| MQ10 / GF(32003) | 326.5 [324.6, 327.3] | 290.0 [288.4, 323.5] | **1.126×** | 285.1 | 1.145× | 1.00× | 0.98× |
| MQ10 / GF(2³¹−1) | 301.4 [300.3, 304.5] | 275.8 [275.0, 277.6] | **1.093×** | 272.0 | 1.108× | 1.02× | 1.02× |
| Eco-12 / 2⁶⁴−353 | 3585.1 [3575.3, 3658.9] | 3087.9 [3077.6, 3096.1] | **1.161×** | 3158.3 | 1.135× | 1.00× | 1.14× |
| MQ11 / Goldilocks | 7383.4 [7371.2, 7400.7] | 5716.2 [5707.7, 5725.0] | **1.292×** | 5937.5 | 1.244× | 1.00× | 1.12× |

Stage clocks on, n=3, medians, ms:

| Target | arm | symbolic | forward | backward (finishing) | interreduction |
|---|---|---:|---:|---:|---:|
| MQ10 / 32003 | base / #845 / FL | 94 / 93 / 91 | 81 / 80 / 89 | 54.4 / **17.8** / 7.9 | 14 / 14 / 14 |
| Eco-12 | base / #845 / FL | 953 / 991 / 987 | 811 / 808 / 1034 | 768 / **207** / 83 | 505 / 520 / 511 |
| MQ11 | base / #845 / FL | 1254 / 1316 / 1312 | 2555 / 2558 / 2779 | 2033 / **262** / 171 | 336 / 346 / 365 |

**Reading.** #845 takes finishing off the serial path without moving work anywhere else: forward is
unchanged (FL grows it by 220–230 ms on the wide targets), and the finishing stage runs 3.7× (Eco-12)
to 7.8× (MQ11) faster at 16 workers. That is why it beats parallel FL on both Goal B targets
(−13.9% / −22.6% process wall against −11.9% / −19.6% for FL), and with no RSS growth, where FL
costs 12–14%. On MQ10, FL is still 1–2% ahead: its finishing stage is smaller still, and MQ10's
forward stage absorbs FL's growth less visibly. #845 meets its gate (≥10% on a wide target, no MQ10
regression, RSS ≤1.15×) and ships in the default order. The §6 row predicted −18.9% / −25.8% at the
forward stage's efficiency; finishing's measured efficiency is lower (a wave barrier and targets of
very uneven cost), so the measured gain is 74% (Eco-12) to 88% (MQ11) of that prediction.

**Distance to the goals after #845** (16-worker process wall against §4's comparand figures): MQ10
is 290.0 / 117.8 = 2.46× msolve at 32003 and 275.8 / 157.9 = 1.75× at 2³¹−1 (target ≤1.5×). Eco-12 is
3087.9 / 1623.5 = 1.90× grobx and MQ11 5716.2 / 2935.4 = 1.95× (target ≤0.90×), so Goal B still
needs 2.11× / 2.16×. Symbolic preprocessing is now the largest stage on every target but MQ11.

## 7. #831, measured at this commit

`--pair-multiples every` against the default `distinct`, process wall, n=5 paired:

| Target | Workers | Every ms | Distinct ms | Distinct / Every | halves removed | RSS ratio |
|---|---:|---:|---:|---:|---:|---:|
| MQ10/32003 | 1 | 1182.9 | 1069.1 | 0.904× | 339 | 0.992× |
| MQ10/32003 | 16 | 334.1 | 322.3 | 0.964× | 339 | 0.971× |
| MQ10/2³¹−1 | 1 | 1015.1 | 919.1 | 0.905× | 339 | 0.992× |
| MQ10/2³¹−1 | 16 | 307.4 | 297.1 | 0.966× | 339 | 0.981× |
| Eco-12 | 1 | 14094.2 | 12664.6 | 0.898× | 1,414 | 0.999× |
| Eco-12 | 16 | 3707.9 | 3580.0 | 0.965× | 1,414 | 0.997× |
| MQ11 | 1 | 57164.4 | 40580.6 | 0.710× | 3,753 | 0.991× |
| MQ11 | 16 | 8884.5 | 7419.8 | 0.836× | 3,753 | 0.998× |

This agrees with the first pass to within 1.5 points and with #841's own figures at `9d3e45a7`:
MQ10 0.89–0.97×, and Katsura-11 0.80× serial and 0.91× at 16 workers. It adds the wide targets.
MQ11 is the largest effect recorded for #831: 3,753 of 14,118 pair halves were repeats.

## 8. What this does not show

- n=5 per cell. That is enough to rank stages and to resolve the FL cross-check, whose paired
  ratios spread less than 1%. It is not enough to grade a goal. #837's final protocol (≥9
  interleaved measurements) still applies.
- FL was cross-checked on the wide targets only. The MQ10 and Katsura-11 FL figures are #843's.
- The comparands were not re-run at 1/4/8/16 on the wide targets. grobx's pinned driver is serial,
  and wide-corpus refuses comparand workers above one.
- No exact certification was run here. Zeebra's wide bases are text-identical to grobx's, and that
  is agreement between engines, not proof (plan §2.2). MQ10 answers are verified against #739's
  references.
- Julia/Groebner.jl was not timed. It is startup-dominated on these rows (#738) and is not the
  best comparand on any target.
- "Plausible" and "remodelled" figures are models built from this cost table and earlier
  evidence, not measurements.

## 9. Superseded first pass (kept as evidence, not pooled)

The first pass ran at `847c4030`/`772be618` (production source `da5b658c`), 17:00–18:59 EST, n=3,
with another worktree's fat-LTO builds live (four compilers at the start of every cost-model child,
load 2.8–6.7). Its MQ10 comparand cohort had to be taken in three windows because the controller
stops when a compiler starts. Its records and tables are in
[`research/m29-baseline/`](../../research/m29-baseline/tables.md). Headline figures, for
comparison only:

| | MQ10/32003 | MQ10/2³¹−1 | Eco-12 | MQ11 |
|---|---:|---:|---:|---:|
| Zeebra 16w process wall, first pass → quiet (ms) | 325.4 → 321.6 | 296.0 → 296.2 | 3709.8 → 3581.6 | 7649.9 → 7432.8 |
| Zeebra 1w, first pass → quiet (ms) | 1166.0 → 1076.7 | 981.1 → 917.1 | 13449.7 → 12692.7 | 43358.1 → 40596.5 |
| best comparand, first pass → quiet (ms) | 117.8 → 117.8 | 165.7 → 157.9 | 1806.0 → 1623.5 | 3236.3 → 2935.4 |
| Zeebra / comparand, first pass → quiet | 2.77× → 2.77× | 1.85× → 1.93× | 2.05× → 2.21× | 2.36× → 2.53× |
| finishing share of wall, first pass → quiet | 16.7% → 17.1% | 13.8% → 13.8% | 20.8% → 20.6% | 27.2% → 27.7% |
| #831 at 16w, first pass → quiet | 0.974× → 0.964× | 0.970× → 0.966× | 0.962× → 0.965× | 0.839× → 0.836× |

Every stage share in §5 moved by less than 1.5 points, so the first pass's ranking of mechanisms
stands. Its #828 verdict does not, for the reason in §6a.
