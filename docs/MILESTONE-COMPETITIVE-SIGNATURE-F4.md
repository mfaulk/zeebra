# M31 — Signature-F4 Wall-Time Conversion and Competitive Performance

**Status:** planning, 2026-11-18. No M31 measurement has been taken and no M31 code exists.
**Predecessor:** M30 — Signature-Based Work Avoidance and Parallel Symbolic F4
([`MILESTONE-SIGNATURE-SYMBOLIC-F4.md`](MILESTONE-SIGNATURE-SYMBOLIC-F4.md), §15 integration
report; tracker #854, closed).
**Planning base:** `main` at `f0715369` (#895). PRs #896, #897 and #898 were open, green and
unmerged at planning time (§4).
**Measured at:** not measured here. Every figure is quoted from the M30 report §15 (final `main`
`e4826153`, instrument `5515c412`, evidence in [`research/m30-final/`](../research/m30-final/README.md)),
from [#857's prototype report](research/m30-sigf4-prototype.md) (`2d589a80` design 1, `7d85eee5`
design 2), from [the signature RFC](research/signature-f4-rfc.md) and from the bodies of PRs #896
(`c49479bb`), #897 (`9548555d`) and #898 (commits in `research/m30-one-worker-drift/`), each of
which carries its own commit. Figures derived here (§6.3) are labelled as estimates.
**Tracking issue:** [#900](https://github.com/mfaulk/zeebra/issues/900).
**Project:** [Zeebra #7](https://github.com/users/mfaulk/projects/7); label `M31`. Priority is the
Project field (P0 → High, P1 → Medium, P2 → Low). A conditional issue also carries `blocked` until
its gate's evidence is posted on it. There is no native GitHub milestone object; milestones in this
repository are labels and documents.

**Focus:** one question. M30 showed that an independently implemented, sound signature-F4 does
9.7–22.8× fewer coefficient products than shipping F4 with identical bases. Can Zeebra turn that
saving into a reproducible wall-clock advantage over its own current F4, and, ideally, over the
strongest open-source comparands?

## 1. Vision and executive summary

> **M31 — Signature-F4 Wall-Time Conversion and Competitive Performance.** Determine, with
> predeclared gates, whether Zeebra's signature-F4 engine can be made faster than current shipping
> F4 in complete, verified wall time by parallelizing signature-safe elimination and reducing the
> engine's serial overhead, and whether the result is competitive with leading open-source solvers.

The most important output is a **decision**: does the signature engine carry a large enough,
general enough advantage to justify production qualification? Making the experimental engine
faster is a means to that decision, not the goal.

**Why this is a bounded problem.** On Eco-12, the primary instance, design 1 takes 3,625.5 ms
against 2,338.6 ms for 16-worker shipping F4 (M30 §15.4). The target (§6, Target 1) needs it at or
below 1,754 ms (median) — a cut of about 1.87 s, or 52% of its wall. #857's stage clocks put 1.70 s
in serial elimination and 1.70 s in three other serial stages (§3.3). **Neither half alone is
enough** (§6.3): even removing elimination entirely leaves 1.93 s, and removing all three other
stages leaves 1.93 s. Both must move. That fixes the shape of the milestone:

- **Workstream S-par (critical path):** M31-S1 decides whether the cross-target elimination cascade
  can be parallelized under the signature discipline, and how much; M31-S2 builds at most one design
  only if S1 passes Gate A.
- **Workstream S-ser (parallel with S1):** M31-S3 attacks symbolic preprocessing, pair bookkeeping
  and final interreduction in the signature engine, each change measured on complete wall.
- **Qualification:** M31-S4 (dispatch and opt-in qualification) only if S2 + S3 clear the entry
  gate. Shipping F4's default does not change in M31.
- **Reliability, off the critical path:** #899 bounds certification by its own deadline.
- **Closeout:** M31-I runs the predeclared final cohort.

Workstream P of M30 (conventional F4 symbolic preprocessing) is **not** continued as a campaign:
#896 caps its remaining serial pieces at 6.6% of MQ10's F4 call (§4.2).

## 2. What M30 established

All figures are historical and commit-specific. M31-0 re-measures them before any M31 comparison.

### 2.1 Shipping conventional F4 at 16 workers (M30 §15.2, final `main` `e4826153`, n = 9, process wall)

| Instance | Complete F4 | Freeze → final | Peak RSS |
|---|---:|---:|---:|
| MQ10 / GF(32003) | 237.7 ms | 0.825 | 43 MiB |
| MQ10 / GF(2³¹−1) | 219.8 ms | 0.808 | 45 MiB |
| Eco-12 / 2⁶⁴−353 | 2,350.5 ms | 0.767 | 199 MiB |
| MQ11 / Goldilocks | 4,642.5 ms | 0.810 | 393 MiB |
| Katsura-11 / 2³¹−1 | 1,108.8 ms | 0.777 | 149 MiB |
| Katsura-11 / 2⁶⁴−353 | 1,326.5 ms | 0.809 | 149 MiB |
| Cyclic-7 / 2⁶⁴−353 | 140.5 ms | 0.985 | 21 MiB |

These are `m29_cost_model` rows. `sig_f4_study`'s own F4 arm, built at the same commit, measured
2,338.6 ms on Eco-12 and 1,342.0 ms on Katsura-11 / Goldilocks (M30 §15.4). **Ratios in this plan
use the instrument's own paired F4 arm, never a wall from another binary or session.**

### 2.2 Signature-F4 work saving (#857 §3.1, `2d589a80`; census at `e4826153`)

| Instance | F4 products | Sig-F4 products | Reduction | F4 → sig-F4 reductions to zero | Sig basis / reduced |
|---|---:|---:|---:|---:|---|
| Eco-12 / 2⁶⁴−353 | 5.924 G | 0.611 G | 9.7× | 6,326 → 1,013 | 1,885 / 743 |
| MQ11 / Goldilocks | 20.377 G | 1.745 G | 11.7× | 6,293 → 540 | 767 / 767 |
| Katsura-11 | 4.556 G | 0.200 G | 22.8× | 3,936 → 145 | 561 / 537 |
| Cyclic-7 / Goldilocks | — | 0.019 G | — | — → 128 | 3,083 / 209 |

Every measured run's reduced basis equals shipping F4's coefficient for coefficient. Katsura-11's
F4 counts are at 2³¹−1 / 2⁶⁴−353 and its sig-F4 counts at Goldilocks (§15.4 note).

### 2.3 Signature-F4 wall (M30 §15.4 at `e4826153`; #857 §3.3 at `2d589a80` / `7d85eee5`)

| Row | Design 1 (serial) | F4-16 (same binary) | d1 ÷ F4-16 [95%] | d2 ÷ F4-16 at the freeze |
|---|---:|---:|---:|---:|
| Eco-12 / 2⁶⁴−353 (primary) | 3,625.5 ms | 2,338.6 ms | **1.550** [1.545, 1.561] | 1.010 [1.003, 1.018] |
| Katsura-11 / Goldilocks (second family) | 1,049.2 ms | 1,342.0 ms | **0.782** [0.774, 0.788] | 0.486 [0.481, 0.494] |
| MQ11 / Goldilocks (reported, not gating) | — | — | 0.961 at the freeze | 0.512 at the freeze |
| Cyclic-7 / Goldilocks (non-regular control) | — | — | 5.647 at the freeze | 6.965 at the freeze |
| katsura-4, noon-7 (small controls) | — | — | katsura-4 upper bounds 1.10–1.21; noon-7 0.506 | — |

Design 2 was **not** re-measured at the final `main`. Its freeze-time ratios are against a reference
that M30's Workstream P later made 0.767× faster on Eco-12, so they are not current. At equal
workers the saving is real: design 1 is 0.287× one-worker F4 on Eco-12 and 0.110× on Katsura-11.
Peak RSS on Eco-12 was 1.05× (d1) and 1.11× (d2) shipping; on Cyclic-7 3.5×.

### 2.4 Where design 1's time goes (#857 §3.2, one run, `2d589a80`)

| Instance | Elimination | Interreduction | Bookkeeping | Symbolic | Sum | Sig metadata |
|---|---:|---:|---:|---:|---:|---:|
| Eco-12 | 1.698 s | 0.696 s | 0.534 s | 0.465 s | 3.393 s | 16.1 MiB |
| MQ11 | 4.084 s | 0.553 s | 0.032 s | 0.453 s | 5.122 s | 1.4 MiB |
| Katsura-11 | 0.587 s | 0.108 s | 0.019 s | 0.162 s | 0.876 s | 1.1 MiB |
| Cyclic-7 | 0.145 s | 0.019 s | 0.517 s | 0.122 s | 0.803 s | 10.8 MiB |

Every stage is serial in design 1. Design 2 parallelized pre-reduction against each batch's fixed
reducer block: Eco-12 elimination fell from 1.70 s to 1.22 s but products rose from 0.611 G to
0.743 G, because the **cross-target cascade** — targets in a batch reducing one another in signature
order — stayed serial (#857 §5). That cascade is the RFC §6.1 item 2 question, never attempted.

### 2.5 Competitive position (M30 §15.2; mode and worker counts are part of every figure)

| Task | Zeebra F4 16w | Strongest comparand | Ratio | Kind |
|---|---:|---|---:|---|
| MQ10 / 32003 | 237.7 ms | groebner-rs 83.3 ms (4w, randomized combinations, verified) | 2.85× | 16w vs 4w |
| MQ10 / 32003 | 237.7 ms | msolve exact 117.0 ms (8w) | 2.03× | 16w vs 8w |
| MQ10 / 2³¹−1 | 219.8 ms | groebner-rs 97.6 ms (4w, verified) | 2.25× | 16w vs 4w |
| MQ10 / 2³¹−1 | 219.8 ms | msolve exact 158.5 ms (4w) | 1.39× | 16w vs 4w |
| Eco-12 | 2,350.5 ms | grobx raw randomized 1,613.7 ms (1w) | 1.46× | 16w vs 1w; equal-worker 7.76× |
| MQ11 | 4,642.5 ms | grobx raw randomized 2,914.0 ms (1w) | 1.59× | 16w vs 1w; equal-worker 13.6× |
| Katsura-11 / 2⁶⁴−353 | 1,326.5 ms | grobx raw randomized 547.0 ms (1w) | 2.43× | 16w vs 1w; equal-worker 16.1× |
| Cyclic-7 / 2⁶⁴−353 | 140.5 ms | grobx raw randomized 116.3 ms (1w) | 1.21× | 16w vs 1w; equal-worker 2.27× |

**None of these is an equal-worker comparison except the column so labelled.** grobx's adapter
refuses more than one worker. grobx raw randomized mode is uncertified; its certified mode took
283 s and 11.4 GB on Eco-12. Design 1's serial Eco-12 wall (3.63 s) is 2.25× grobx raw at one
worker each; parity with grobx raw on Eco-12 needs the signature engine at ≤1.61 s.

## 3. Results since the M30 report, and what they change for M31

Verified on 2026-11-18 against GitHub. "Open" means unmerged at planning time; M31-0 records which
of these are on `main` at its freeze.

| Work | State | Finding | Effect on M31 |
|---|---|---|---|
| #878 / #861 adaptive parallel interning | merged `d6aa0526` | shipping default; Eco-12 symbolic 3.87×, F4 −23.3% | the reference got faster; sig-F4's own symbolic stage does **not** use it (`sigf4/engine.rs` `symbolic`) — a reuse candidate for S3 |
| #870 / #857 sig-F4 designs 1 and 2 | merged `833bb6bb`; #858 closed not planned | §2.2–§2.4 | the engine M31 starts from, behind `research-sigf4` |
| #879 tail-only interreduction | merged `5452ae13`; default decision is #877 (open) | katsura-11 grevlex echelon tails: stage 27.1 → 1.65 s, VmHWM 2,880 → 636 MB; level under the shipping default at one unpinned rep | S3 may apply it to the signature basis where its preconditions hold; #877's default question stays outside M31 |
| #882 half-GCD Wiedemann | merged `28e4e063` | ~1.64× complete conversion at dimension 78,125 | not M31 scope (solving, not F4) |
| #893 / #891 instrument worker caps | merged `207b60f8` | three studies inherited the 16-thread symbolic team | fixed; M31 instruments must record the team (§10.4) |
| #895 / #886 `Auto` clamps to `available_parallelism` | merged `f0715369` | default worker caps now clamp | fixed; **#894** found on the way (concurrent forward kernel ~10% faster than serial at one CPU on Katsura-11) — outside M31 (§8) |
| #896 / #888 residual symbolic attribution | **open**, green (`c49479bb`) | stitch + merge walk = **6.6%** of MQ10's 207.8 ms F4 call; a 12-worker team saves 0–2% of F4 but costs Katsura-8 1.029× | **no** conventional symbolic campaign in M31 (§4.2) |
| #897 / #887 parallel certificate, `PreparedDivisors` | **open**, green (`9548555d`) | Eco-12 certified in 65.5 s, MQ11 60.7 s, Katsura-11 27.1 s, Cyclic-7 0.03 s at 16 workers; one worker still >660 s on Eco-12 | certificate throughput is **not** an M31 workstream; #899 (deadline, typed partial result) is |
| #898 / #890 one-worker drift | **open**, green | 1.024–1.035× on Eco-12's serial closure from #878's code placement; process wall 0.997–1.005; immaterial | no M31 work |

### 3.1 Consequences

1. **Certification.** If #897 merges, Zeebra can certify every substantial M31 output itself inside
   the 600 s verification budget at 16 workers. M31's correctness contract (§9) assumes it. If #897
   has not merged when M31-0 freezes, M31-0 records that and wide-field verification falls back to
   grobx certified mode as in M30 (32 GiB cap on Eco-12, declared).
2. **Conventional symbolic preprocessing** is not a lever for M31 (§4.2).
3. **The reference moved and may move again.** Any change merged to shipping F4 during M31 moves
   the denominator of every gate. §10.2 fixes how that is handled.

## 4. Hypotheses and unknowns

### 4.1 Hypotheses (unmeasured)

- **H1 — cascade parallelism.** The cross-target cascade inside a signature batch has a dependency
  structure (target T needs pivot P only if `s(P) < s(T)` and P's lead is in T's support after
  earlier reductions) whose critical path is short enough that 16 workers can cut Eco-12's
  elimination stage ≥3.5× against design 1 without raising coefficient products more than 25%.
  *Falsified* if S1's replay of real Eco-12 batches gives a critical-path bound below 3.5×, or if
  displacement or redundant work adds more than 25% products.
- **H2 — displacement soundness.** RFC §6.1 item 2's least-signature-wins pivot ownership, with
  displaced rows resuming, yields for each column the least-signature pivot the sequential
  Lairez Algorithm 8 order would produce, so the batch's new elements and the final reduced basis
  are those of a valid sequential signature-safe reduction. This is an **inference** in the RFC, not
  a published result. Individually permitted reductions do not by themselves prove it (§9.2).
- **H3 — serial overhead is compressible.** Signature-aware symbolic preprocessing can reuse #861's
  parallel interning; pair bookkeeping can be cut by better data structures; and interreduction of
  the 1,885-element signature basis can be cut by applying the shipping parallel or tail-only route.
  Together ≥2× on at least two of the three stages on Eco-12.
- **H4 — dispatch.** A pre-solve classifier using only cheap features (input size, degrees,
  field, first-batch signature-basis growth and rejection mix) can route Cyclic-7-like inputs and
  tiny inputs to shipping F4 at negligible overhead while keeping Eco-12 and Katsura-11 on the
  signature path.

### 4.2 Not hypotheses (settled; do not reopen without new evidence)

- Conventional symbolic preprocessing's remaining serial pieces cap at 6.6% of MQ10's F4 call
  (#896). A new campaign needs a measured end-to-end case first.
- Signature handover inside a solve was net-negative wherever grobx fired it (#716; M30 §15.6
  item 4). An in-solve handover is excluded from M31 (§13) unless a new planning decision admits it.
- Randomized row combinations and uncertified zero tests are excluded (M30 §13; #714).

### 4.3 Unknowns M31 must answer

1. The critical-path length and dependency width of the cascade on real batches (S1).
2. Whether displacement terminates with bounded extra work, and its synchronization cost (S1/S2).
3. Whether exact row-level equality with design 1 is required, or only equality of the batch's new
   basis elements and syzygy signatures, or only of the final reduced basis (S1 must decide and
   justify; §9.2).
4. How much of design 1's 0.245 s of unaccounted Eco-12 wall (3.638 s process − 3.393 s staged)
   is startup, parsing or minimal-basis work (M31-0).
5. Whether the signature basis outgrowth (Eco-12 1,885 vs 743; Cyclic-7 3,083 vs 209) can be cut
   without losing provenance the criteria need (S3).

## 5. Goals

1. Freeze a baseline of shipping F4, design 1 and design 2 at one commit, with the current stage
   decomposition and an Amdahl budget (M31-0).
2. Answer H1/H2 rigorously enough for a go / no-go on a parallel cascade (M31-S1, Gate A).
3. If go: one bounded parallel-elimination design, measured on complete wall (M31-S2, Gate B).
4. Independently: bounded serial-overhead reductions (M31-S3).
5. If the combined engine clears the entry gate: dispatch and opt-in qualification (M31-S4, Gate C).
6. Certification bounded by its own deadline with a typed partial result (#899).
7. A final cohort and report that keeps work, parallel speedup, end-to-end wall and competitive
   position apart (M31-I, Gate D).

## 6. Success tiers (fixed now; scored as written; not to be rewritten after measurement)

The final report scores each criterion as **met**, **missed** or **not attempted**, with the reason.

### 6.1 Minimum — decisive research evidence

1. M31-0 freezes a reproducible baseline (shipping F4, design 1, design 2, comparands) and publishes
   the signature-engine stage decomposition and the §6.3 budget re-derived from fresh measurements.
2. M31-S1 publishes the cascade dependency statistics on real Eco-12 and Katsura-11 batches, a
   correctness argument with explicit open proof obligations, a performance ceiling, and a go /
   no-go read against Gate A.
3. At least one of: a bounded S2 experiment, a bounded S3 change, or a mathematically justified
   rejection, **resolves H1 or H3** with reproducible evidence.
4. M31-I publishes the report, including every negative and stopped result.

Minimum may be met without any production integration.

### 6.2 Target — the signature path qualifies as a supported opt-in

All of the following, on the final M31 code, against shipping F4 built from the same commit, n ≥ 9
per arm, interleaved fresh processes, at the 16-worker operating point unless stated:

1. **Primary, Eco-12 / 2⁶⁴−353:** signature path ÷ shipping F4 **median ≤ 0.75 and 95% bootstrap
   upper bound ≤ 0.80**.
2. **Second family, Katsura-11 / Goldilocks:** median ≤ 0.90 with the 95% interval excluding 1.0.
   MQ results cannot satisfy this criterion.
3. **Small and unfavourable controls** (katsura-4 at Goldilocks and 2⁶⁴−353, noon-7, Cyclic-7 /
   Goldilocks), through the opt-in entry point including any dispatch: 95% upper bound ≤ 1.05 at
   1 and 16 workers.
4. **Memory:** peak RSS ≤ 1.25× shipping F4 on every corpus row.
5. **Correctness:** §9's complete contract on every output; coefficient-for-coefficient equality
   with shipping F4's reduced basis on every corpus output; independent certification of every
   substantial output.
6. **Behaviour:** typed `Unsupported` for every non-graded order; typed budget errors; wall-budget
   cancellation at safe points; no panic under adversarial scheduling (S2 tests).
7. **No default change.** Shipping F4 remains the library default.

**The discrepancy this resolves.** M30 plan §6.4 wrote "≥25% better complete F4 process wall",
i.e. a ratio ≤ 0.75. RFC §10.2 "tightened" it to "95% interval entirely ≤ 0.80", which constrains
the interval but admits a median between 0.75 and 0.80, and #857 §4 applied only the interval
form; M31's brief also quoted "≤ 0.80×". **M31 requires both** (median ≤ 0.75 and upper
bound ≤ 0.80), so neither historical wording is weakened. Against M30's 2,338.6 ms Eco-12 F4 arm
that is ≤ 1,754 ms median (≤ 1,871 ms at the upper bound); these are anchors, and only M31-0's and
M31-I's paired arms are read. Criterion 3 differs from #858 in one declared way: controls are
measured **through the opt-in entry point**, so a dispatch that routes them to shipping F4 is
allowed, and its overhead counts against the 1.05 bound.

### 6.3 Feasibility arithmetic (derived from §2.4; estimates, not predictions)

Required cut from design 1 on Eco-12: 3,625.5 − 1,754 ≈ **1.87 s**. Each row subtracts the saved
stage time (from #857's single-run stage clocks at `2d589a80`) from design 1's 3,625.5 ms median
at `e4826153` and divides by that binary's 2,338.6 ms F4-16 arm. Mixing those two commits is why
this is an estimate.

| Scenario | Elimination | Interreduction | Bookkeeping | Symbolic | Projected wall | ÷ F4-16 |
|---|---|---|---|---|---:|---:|
| Elimination free, rest unchanged | 1.698 → 0 | — | — | — | ~1.93 s | 0.82 |
| Other stages free, elimination unchanged | — | 0.696 → 0 | 0.534 → 0 | 0.465 → 0 | ~1.93 s | 0.82 |
| Moderate | 3× | 1.5× | 1.25× | 2× | ~1.93 s | 0.82 |
| Required shape | ≥3.5× | ≥2× | ≥1.5× | ≥3× | ~1.58 s | 0.67 |
| Optimistic | 6× | 3× | 2× | 3.9× (#861's Eco-12 factor) | ~1.13 s | 0.48 |

So **both workstreams are necessary and neither is sufficient**. Gate A therefore reads the
combined projection, and M31-0 must re-derive the table from fresh stage clocks at the freeze. A
stage ceiling is an upper bound on its saving; projections are not multiplied with each other
beyond this additive Amdahl sum, and none is reported as a result.

### 6.4 Stretch — competitive leadership

On at least one of Eco-12 / 2⁶⁴−353, MQ11 / Goldilocks or Katsura-11 / 2⁶⁴−353, the opt-in
signature path at 16 workers reaches a **median ≤ 1.00× and 95% upper bound ≤ 1.05×** the strongest
relevant comparand's best supported configuration (today grobx raw randomized at one worker; also
groebner-rs at its best worker count), on the same pinned input, verified. It is reported as
"Zeebra 16w vs grobx 1w (best supported configuration)", with the equal-worker row beside it, and
with the guarantee difference stated: grobx raw is randomized and uncertified; grobx certified,
groebner-rs verified and Zeebra deterministic + certified are separate rows. MQ10 against msolve
exact and groebner-rs is reported, not scored, unless the signature path runs it.

### 6.5 Research stretch (scored separately from competitive success)

A parallel signature-elimination algorithm whose correctness argument discharges every S1 proof
obligation, with adversarial-schedule tests, that cuts the Eco-12 elimination stage ≥ 3× against
design 1 at 16 workers with coefficient products within 1.25× design 1's.

## 7. Work packages

| WP | Issue | Priority | Kind | Blocked by |
|---|---|---|---|---|
| Tracker | [#900](https://github.com/mfaulk/zeebra/issues/900) | High | tracking | its children |
| Workstream S anchor | [#889](https://github.com/mfaulk/zeebra/issues/889) (reused) | High | anchor | S1–S4 |
| M31-0 baseline, protocol, model | [#901](https://github.com/mfaulk/zeebra/issues/901) | High (P0) | required | — |
| M31-S1 parallel-cascade feasibility | [#902](https://github.com/mfaulk/zeebra/issues/902) | High (P0) | required, research | — (Gate A reads #901) |
| M31-S3 serial overhead | [#903](https://github.com/mfaulk/zeebra/issues/903) | High (P0) | required | #901 (freeze, before measuring) |
| M31-S2 bounded parallel elimination | [#904](https://github.com/mfaulk/zeebra/issues/904) | High (P0) | **conditional**, `blocked` | #901, #902 (Gate A) |
| M31-S4 dispatch and opt-in qualification | [#905](https://github.com/mfaulk/zeebra/issues/905) | Medium (P1) | **conditional**, `blocked` | #903, #904 (Gate C entry) |
| M31-C certification deadline | [#899](https://github.com/mfaulk/zeebra/issues/899) (reused) | Medium (P1) | required | — |
| M31-I final cohort and report | [#906](https://github.com/mfaulk/zeebra/issues/906) | High (P0) | closeout, `blocked` | all of the above |

### 7.1 M31-0 — baseline, protocol and performance model (#901)

Freeze at one commit, as M30-0 did (§10.1): Zeebra source, executables and SHA-256s
(`m29_cost_model`, `sig_f4_study`, `zeebra_driver`, `wide_corpus`), toolchain and profile, input
digests (§10.3), every option (F4 and `SigF4Options`, including `workers`), comparand identities
reused from M30-0 unless a new one is declared, host and placement. Measure, interleaved, n = 9:
shipping F4 at 1/4/8/16 workers, design 1, design 2 at 16 workers, on the §10.3 corpus. Stage clocks
as a separate campaign (n = 5). Publish the §6.3 table re-derived, with design 1's unaccounted wall
attributed (§4.3 item 4), and a per-batch decomposition of Eco-12's elimination into
reducer-block work and cross-target-cascade work (design 2's split, measured on the same batches)
so S1 starts from the measured cascade share. Reuse M29/M30 scripts (`research/m29-baseline/`,
`research/m30-final/campaign.py`, `research/m30-sigf4/campaign.sh`); no new harness.
Deliverables: `docs/research/m31-baseline.md`, `research/m31-baseline/`.

### 7.2 M31-S1 — signature-safe parallel elimination feasibility (#902)

Documents and a read-only instrument; no engine change except feature-gated counters. Must:

1. Formalize the batch: targets, reducer block, pivots, signatures, the admissibility predicate.
2. Analyse pivot ownership by least signature; whether a lower-signature row may displace a
   pivot; whether the displaced row may resume; termination (a potential function over
   (signature rank, column) per row); equivalence to a valid sequential order.
3. Decide what equality is required (§9.2) and justify it.
4. Price displacement: extra row operations, compare-and-swap traffic, memory.
5. Consider schedules that avoid displacement: signature-rank wavefronts, column-block
   partitioning, speculative reduction with validation, deterministic two-phase claims, and
   F4-RB / F4/5 or concurrent sparse-elimination literature (Eder–Faugère survey §13–§15; Lairez
   2022; Faugère's F4/5 and F5 papers; Roune–Stillman 2012; Faugère–Lachartre and its parallel
   successors), from the papers, not abstracts.
6. Replay real Eco-12 and Katsura-11 batches from design 1 and record the dependency DAG: width,
   critical-path length weighted by coefficient products, and the share of work on it. From that,
   an elimination-stage ceiling at 4/8/16 workers for each candidate schedule, with displacement
   overhead included.
7. Read Gate A (§8.1) and recommend one design, or no-go.

Deliverable: `docs/research/m31-parallel-signature-elimination.md` and the replay instrument.

### 7.3 M31-S2 — bounded experimental parallel signature elimination (#904, conditional)

**Blocked** until Gate A passes on #902 with #901's numbers. One design, the one S1 selects,
isolated under `src/grobner/sigf4/` behind `research-sigf4`. Requirements: §9 in full; signature
eligibility asserted on every pivot application under `check_signatures`; deterministic output or a
proof that internal nondeterminism yields the same new elements, syzygy signatures and reduced
basis; displaced rows, zero reductions and new elements handled; bounded scratch and metadata
charged to the live budget; wall-budget cancellation at batch and pivot safe points; no `unsafe`
without a written publication/lifetime argument and a loom-style or deterministic-scheduler test.
Measured as elimination stage **and** complete process wall against design 1 and shipping F4.
Caps in §8.5. Gate B (§8.2) decides.

### 7.4 M31-S3 — signature-engine serial overhead (#903)

At most **three** bounded changes, one per stage, each its own PR with its own interleaved A/B on
complete wall:

1. **Symbolic:** reuse or adapt `symbolic_intern.rs`'s parallel interning for the signature
   engine's closure, keeping least-signature reducer selection (`reducer()`) deterministic.
2. **Bookkeeping:** pair queue, Koszul / zero-row syzygy lookup (`SyzygyStore::covering` is a
   per-index linear scan filtered by divisibility masks), rewrite lookup and allocation; reduce Eco-12's 1.78 M pair decisions'
   cost without changing which pairs are rejected (the rejection counts by mechanism must stay
   identical).
3. **Interreduction:** the engine calls `interreduce_by_matrix` with `F4Options::default()` limits
   on the signature basis; evaluate passing the shipping parallel route, #879's tail-only route
   where its precondition (fixed reducer rows) holds, and dropping non-minimal elements earlier.

Each change must keep the algebra identical (pairs, rejections by mechanism, reductions to zero,
products, basis) unless the PR proves a difference sound and reports it. A change that does not
improve Eco-12 complete design-1 wall by ≥ 3% with the interval excluding 1.0, and regresses no
corpus row beyond 1.05 upper bound, is recorded and not merged. Signature-basis outgrowth (§4.3
item 5) is in scope only as measurement, unless a provenance-preserving reduction is found.

A **fourth** change, reducing per-batch setup in the signature engine (#901 measured 0.484 s of
Eco-12 design-1 elimination there, serial in both designs), was authorized by the owner on #900,
under the same line and session cap and the same gate. Its outcome is recorded in
[`research/m31-sigf4-serial.md`](research/m31-sigf4-serial.md) §5.2.

### 7.5 M31-S4 — adaptive dispatch and opt-in production qualification (#905, conditional)

**Blocked** until the combined S2 + S3 engine, measured on #904/#903's final commits, meets Target
criterion 1 (Eco-12) on an n ≥ 9 interleaved run. Then:

1. A **pre-solve** dispatch policy (H4) from features available before or within the first batch,
   with its overhead measured. An in-solve handover is out of scope (§4.2).
2. A supported opt-in public entry point (an `F4Options`-adjacent option or a separate function),
   documented, with typed refusals and fallbacks. No default change.
3. The complete §6.2 Target gate, read as Gate C.

### 7.6 M31-C — certification deadline and typed partial result (#899, reused)

Reused as filed. Scope: a certification wall budget separate from the solver's; cancellation
between reductions; a typed stop distinct from `CertificationFailed`; correct cleanup of the scoped
team; API compatibility (`CertificationReport` is not `#[non_exhaustive]`, so a new field is a
breaking change to weigh). Builds on #897; if #897 has not merged, #899 waits for it. Verification
time stays outside solver wall in every report.

### 7.7 M31-I — final competitive cohort and integration report (#906)

Blocked on every work package finishing or terminating at its gate. Runs §11's cohort at the final
M31 commit beside the M31-0 freeze, interleaved, and writes §15 of this document.

## 8. Dependency graph and go / no-go gates

```
#901 M31-0 freeze ──┬──────────────► Gate A (read on #904) ──► #904 S2 ──► Gate B
                    │                       ▲                                │
#902 M31-S1 ────────┼───────────────────────┘                                ▼
                    └──► #903 S3 (≤3 changes) ───────────────────────► S2+S3 combined
                                                                             │ Target 1 met?
                                                                             ▼
                                                     #905 S4 dispatch + qualification ──► Gate C
#899 M31-C certification deadline (independent) ─────────────────────────────┐
                                                                             ▼
                                                     #906 M31-I final cohort ──► Gate D
```

No cycles: every edge points from an earlier to a later package. **Critical path:** #901 → #902 →
Gate A → #904 → (combine with #903) → #905 → #906. #903 and #899 run beside it.

### 8.1 Gate A — feasibility (on #904, decided from #901 + #902)

Unblock #904 only if all hold:

1. S1's correctness argument covers the selected schedule, with every remaining proof obligation
   listed and none of them load-bearing for termination or for the admissibility of reducers.
2. S1's replay gives the selected schedule an Eco-12 elimination-stage ceiling **≥ 3.5×** design 1 at
   16 workers, displacement and redundant work included, with projected products ≤ 1.25× design 1.
3. Combining that ceiling with S3's measured savings (or, before S3 lands, its stage ceilings) in
   #901's re-derived §6.3 table projects Eco-12 at **≤ 0.70×** shipping F4-16. The 0.05 margin
   below the 0.75 target exists because ceilings are upper bounds.

**If Gate A fails:** #904 and #905 close as not planned with the evidence; S3 still completes (its
changes help Katsura-11 and MQ11, where elimination dominates); M31-I reports. Do not substitute
another signature algorithm.

### 8.2 Gate B — prototype (on #904)

S2 passes if, n ≥ 9 interleaved at 16 workers on Eco-12: the elimination stage is ≥ 2.5× faster
than design 1; complete wall ÷ design 1 has median ≤ 0.75 and 95% upper bound ≤ 0.80; products ≤ 1.25× design 1; peak RSS ≤ 1.25× design 1;
and every §9 check holds. A failed or capped S2 closes as completed with a negative result; it is
not followed by a second design without a new planning decision recorded on #900.

### 8.3 Gate C — production qualification (on #905)

The complete §6.2 Target. If any criterion fails, the engine stays experimental behind
`research-sigf4` and no opt-in API is published. The default solver never changes in M31.

### 8.4 Gate D — competitive closeout (on #906)

If the engine qualifies but misses §6.4, M31-I publishes the exact remaining gap per comparand and
the stage decomposition that explains it. No new optimization starts from #906.

### 8.5 Effort and resource caps (predeclared)

| Package | Cap |
|---|---|
| #901 | 4 claim-lease sessions; no library change beyond instrument flags |
| #902 | 6 sessions; code limited to a feature-gated replay instrument (≤ 800 lines) |
| #903 | 3 changes, each ≤ 800 net lines under `src/`, excluding tests, and ≤ 4 sessions |
| #904 | **one design**; ≤ 2,500 net lines under `src/grobner/sigf4/`, excluding tests; ≤ 8 sessions to a correct end-to-end result on §10.3's correctness corpus; ≤ 12 sessions total. Reaching a cap without a correct result is a failed design (Gate B fails) |
| #905 | ≤ 1,500 net lines; ≤ 8 sessions |
| Benchmarks | caps per arm in §10.5; no campaign beyond the protocol's repetitions |

Exceeding any cap is a new planning decision by the owner, recorded on #900, not an implicit
extension.

## 9. Correctness and independent certification

### 9.1 Contract for every output

1. **Equality:** the reduced basis equals shipping F4's coefficient for coefficient on every corpus
   output.
2. **Gröbner and reduced:** reducedness, and Buchberger's criterion over all pairs, by
   `certify_f4_output` (parallel after #897) or grobx certified mode.
3. **Ideal equality, both directions.** Input ⊆ ⟨G⟩ is checked by the certificate (each generator
   reduces to zero). ⟨G⟩ ⊆ input ideal is **not** implied by reducedness and Buchberger's criterion:
   it is established by equality with an independently computed reduced basis of the same input
   (Singular on MQ10 and small systems; grobx certified on the wide rows; `buchberger_reference` on
   the smallest) — reduced Gröbner bases are unique per ideal and order. A matching hash between two
   Zeebra engines alone is not evidence.
4. **Signature invariants** under `SigF4Options::check_signatures` on the correctness corpus:
   `s(pivot) < s(target)` on every cross-target use, lead ≤ shifted signature monomial, no new
   element top-reducible at a smaller-or-equal signature.

### 9.2 What the parallel cascade must additionally prove (S1 obligations, S2 tests)

- Each pivot application is signature-safe at the moment it is applied, including when the pivot
  was itself produced or displaced inside the same batch.
- Displacement terminates, with a bound on extra row operations.
- The set of new basis elements (lead, signature) and of new zero-row syzygy signatures equals the
  sequential design 1's for the same batch, **or** S1 proves that a different but valid set yields
  the same final reduced basis and does not unsoundly enlarge the syzygy store. S1 states which,
  and S2 tests that, not merely the final hash.
- Rewrite and syzygy criteria remain sound when their stores are updated by concurrent batches'
  results (or the design serializes those updates).
- Behaviour on non-regular (Cyclic-7), non-radical, overdetermined and underdetermined inputs
  (RFC §10.1's constructions, digests pinned in `src/grobner/sigf4/corpus.rs`).
- Concurrency tests under deterministic adverse scheduling (forced interleavings, randomized yield
  points with a fixed seed, every worker count 1–16), not only repeated runs.

### 9.3 Fields and orders

GF(32003), GF(2³¹−1), Goldilocks and 2⁶⁴−353 in the corpus; at least two fields in every unit
test; grevlex and graded-lex. Lex, `Weighted` and `Block` return typed `Unsupported`.

## 10. Benchmark protocol and resource budgets

M31 reuses M29/M30's protocol ([`m30-protocol.md`](research/m30-protocol.md)) and tools:
`tools/benchlock.sh`, `tools/bench-reserve.sh`, `tools/cpu-context.sh`, `tools/rss-guard.sh`,
`examples/m29_cost_model.rs`, `examples/sig_f4_study.rs`, `research/m29-final/verdicts.py`,
`comparand-scaling.py`, `wide-corpus.py` and the grobx / groebner-rs / msolve adapters. **No new
harness.** `tools/check-measurement-provenance.sh` applies to every document.

### 10.1 Freeze and arms

M31-0 freezes the commit, executables, comparand identities and inputs. Every later comparison
builds the arm at its own head **and** the reference at the freeze or at its merge base, in
separate private target directories, interleaved; never against a published wall.

### 10.2 When shipping F4 moves

If a change to shipping F4 merges during M31, gates are read against shipping F4 **at the evaluated
commit**, built from the same tree. M31-I additionally reports against the M31-0 freeze. Measurements
from different intermediate commits are never combined into one "final" configuration.

### 10.3 Corpus (pinned now; held-out rows fixed before any S2/S3 timing)

The performance corpus is RFC §10.1's, by canonical SHA-256 (`signature-f4-rfc.md` §10.1), plus
M30's held-out rows:

| Role | Instance | Field |
|---|---|---|
| primary (gating) | Eco-12 | 2⁶⁴−353 |
| second family (gating) | Katsura-11 | Goldilocks |
| competitive (reported) | Katsura-11 | 2⁶⁴−353 (grobx reference field) |
| reported, same family as each other | MQ11 | Goldilocks |
| reported | MQ10 | GF(32003), GF(2³¹−1) |
| unfavourable control (gating via entry point) | Cyclic-7 | Goldilocks; 2⁶⁴−353 reported |
| small controls (gating) | katsura-4 | Goldilocks, 2⁶⁴−353 |
| small control (gating) | noon-7 | Goldilocks |
| held out (reported; never used for tuning) | katsura-9, noon-8, eco-14 (`wide-corpus-v1`) | 2⁶⁴−353 |

M31-0 records each held-out row's SHA-256 from `research/wide-corpus/cases.json` before any S2/S3
timing. If eco-14 does not complete under shipping F4 at 16 workers within §10.5's caps, M31-0
drops it and records why; it is not replaced by a row chosen after seeing results. Held-out rows are never used to choose a design or a threshold. No private or
application-specific system enters the corpus.

### 10.4 Method

- Fresh process per run; arms interleaved and rotated per repetition; n ≥ 9 for any gate and for
  M31-I; n ≥ 5 for exploration. Medians with 95% bootstrap intervals; ratios paired per repetition.
- Worker curves 1, 4, 8, 16. The primary cohort's budget stays **16 workers** as in M29/M30; it is
  not raised to make a result look competitive. A 32- or 64-worker row is exploratory and labelled.
- `tools/bench-reserve.sh reserve 1,2` for timed sessions, released at session end; children
  CCD-aligned; `tools/cpu-context.sh` around each child; affinity, cgroup CPU limit, actual worker
  count and the symbolic team size recorded per child (#883/#891 lesson).
- Build before reserving. `CARGO_TARGET_DIR=/buildcache/cargo-target/zeebra-<issue>`,
  `TMPDIR=$CARGO_TARGET_DIR/tmp`, `RUSTC_WRAPPER=""`; release, fat LTO, one codegen unit,
  `x86-64-v3`.
- One benchmark campaign on the machine at a time, under `benchlock`.
- Retain: source commits, toolchain, flags, executable SHA-256s, input digests, solver
  configurations, every attempt including failures, CPU placement and load, basis and certificate
  digests. Tag measured commits `measured/<issue>-<slug>` before squash-merging.

### 10.5 Resource budgets (declared per arm before execution)

- Solve: 180 s wall; 8 GiB memory (`rss-guard`), as M30.
- Certification: 600 s wall, separate from the solve, at 16 workers; grobx certified Eco-12 at
  32 GiB (as M30 declared), every other grobx row at 8 GiB.
- A prototype needing a larger cap than shipping F4 reports that as a result, not as a cap change.

### 10.6 Fair comparison

As M30 §10.5 and §2.5 above: worker counts and modes on every row; equal-worker and
best-supported-configuration rows separate; randomized vs deterministic and raw vs certified never
merged. A new comparand needs its own adapter, source pin and execution contract under
`tools/external/` before any figure is quoted.

## 11. Public/private and licensing boundaries

- Zeebra is the public, general-purpose library. M31's algorithms are general and belong here.
  The corpus is the public generic one (MQ, Katsura, Cyclic, Eco, Noonburg). No application-specific
  systems, parameters, datasets or research notes enter Zeebra, and no M31 package needs access to
  any private repository.
- grobx is GPL-3.0-only; Zeebra is MIT. grobx's papers, manual and measurements are references.
  Its instrumentation stays under `tools/external/grobx-driver/research/` per
  [`external-provenance-policy.md`](research/external-provenance-policy.md). Every Zeebra signature
  change is implemented independently from published algorithms.

## 12. Parallel development and merge sequencing

**Tracks (one writer per checkout; own `git worktree`, own branch, own `CARGO_TARGET_DIR`):**

- **Track A — feasibility:** #902 (documents and a replay instrument). Starts immediately.
- **Track B — serial overhead:** #903, after #901's freeze. Its three changes merge one at a time.
- **Track C — reliability:** #899. Independent; touches `src/grobner/f4/certify.rs` and
  `src/poly/` only. Waits for #897 to merge.
- **Track D — benchmarking:** #901 first; later each gate's measurement and #906.

**File contention.** `src/grobner/sigf4/engine.rs` is the magnet: S1's instrument counters, S3's
three changes and S2's elimination all touch it. Rules:

1. #902's instrument keeps its counters in a new file under `src/grobner/sigf4/` and adds at most
   call sites to `engine.rs`.
2. #903's changes land **before** #904 starts coding, where possible (#904 cannot start until
   Gate A anyway). If #904 starts while an #903 change is open, #903 merges first and #904 rebases;
   #903's changes are smaller and independently gated.
3. #903's symbolic change reads `src/grobner/f4/symbolic_intern.rs` and should call it rather than
   modify it. Any change to shipping F4 files (`symbolic*.rs`, `interreduce.rs`, `parallel.rs`,
   `src/linalg/`) is a separate PR with its own shipping-F4 A/B and must not ride inside a sig-F4 PR.
4. #905 owns the public-API surface (`src/grobner/mod.rs`, options) and starts after S2/S3 merge.
5. `examples/sig_f4_study.rs` is shared: each package adds its own flags; conflicts are resolved by
   the later rebaser.

Sequence: freeze → S1 + S3 (+ C) → Gate A → S2 → combined measurement → S4 → final cohort →
report. Re-measure after each merge; never multiply estimates.

## 13. Risks, exclusions and stop rules

| # | Risk | Mitigation |
|---|---|---|
| R1 | The cascade is inherently sequential on Eco-12 (long signature chains) | S1 measures the critical path before any code; Gate A |
| R2 | Displacement is unsound or non-terminating in a corner the tests miss | S1's proof obligations; §9.2 adversarial tests; equality of new elements per batch, not only final hash |
| R3 | Synchronization costs eat the parallel gain | S1 prices CAS and displacement; Gate B reads complete wall |
| R4 | Serial overhead is irreducible without a representation rewrite | S3's cap; a negative result is acceptable; rewrites excluded |
| R5 | Shipping F4 gets faster mid-milestone and moves the gate | §10.2: paired arms from the evaluated tree |
| R6 | Signature basis outgrowth (Cyclic-7 15×) makes the path unsafe in general | dispatch (S4) and the 1.05 control gate through the entry point |
| R7 | Result looks competitive only through a changed worker budget or mode | §10.4 budget fixed at 16; §10.6 labelling |
| R8 | Noise on a shared 64-core host | benchlock, reservations, paired ratios, n ≥ 9 |
| R9 | GPL contamination | §11 |
| R10 | Scope drift into another signature algorithm or a solver rewrite | one-design cap; stop rules |

**Exclusions:** a second parallel-elimination design; an in-solve signature→F4 handover; F5,
Matrix-F5 or GVW as new engines; randomized or uncertified reduction; conventional symbolic
preprocessing campaigns (§4.2); FGLM, block Wiedemann or Krylov work; GPU; out-of-core; a new
runtime; general monomial/polynomial representation rewrites; changes to shipping F4 defaults;
application-specific work.

**Stop rules.** Gate A fails → #904/#905 close not planned, S3 completes, report. Gate B fails or a
cap is hit → #904 closes with its negative result; #905 closes not planned unless S3 alone met
Target 1. Gate C fails → engine stays experimental, nothing published as supported. Gate D fails →
publish the gap. The milestone does not continue because a more ambitious hypothesis failed.

**Not in M31, related and left as independent backlog:** #894 (concurrent forward kernel's one-CPU
advantage on Katsura-11, Low), #877 (tail-only interreduction as default, including lex), #888 (open
until #896 merges; its finding caps the opportunity), #887 (closes with #897), #890 (closes with
#898). None blocks an M31 package. Any of them may be worked independently, but must not delay the
critical path or share a PR with M31 work.

## 14. Issue tracker

| WP | Issue | New / reused | Priority | Blocked by | Labels |
|---|---|---|---|---|---|
| tracker | [#900](https://github.com/mfaulk/zeebra/issues/900) | new | High | children | `M31` |
| S anchor | [#889](https://github.com/mfaulk/zeebra/issues/889) | reused (was M30 `opportunity`) | High | #902–#905 | `M30`, `M31` |
| M31-0 | [#901](https://github.com/mfaulk/zeebra/issues/901) | new | High | — | `M31` |
| M31-S1 | [#902](https://github.com/mfaulk/zeebra/issues/902) | new | High | — | `M31` |
| M31-S3 | [#903](https://github.com/mfaulk/zeebra/issues/903) | new | High | #901 | `M31` |
| M31-S2 | [#904](https://github.com/mfaulk/zeebra/issues/904) | new | High | #901, #902 | `M31`, `blocked` |
| M31-S4 | [#905](https://github.com/mfaulk/zeebra/issues/905) | new | Medium | #903, #904 | `M31`, `blocked` |
| M31-C | [#899](https://github.com/mfaulk/zeebra/issues/899) | reused | Medium | — (#897 merge) | `M31` |
| M31-I | [#906](https://github.com/mfaulk/zeebra/issues/906) | new | High | all above | `M31`, `blocked` |

Hierarchy: #901, #889, #899 and #906 are native sub-issues of #900; #902–#905 are sub-issues of
#889. Dependencies are native "blocked by" relations.

## 15. Planned final scoreboard and report (M31-I fills this section)

### 15.1 Verdicts, kept apart

1. **Algorithmic work** (§2.2 quantities: pairs rejected by mechanism, reductions to zero, zero
   rows, coefficient products, signature-basis size) — final engine vs shipping F4 and design 1.
2. **Parallel speedup** of the signature engine (1/4/8/16 workers; per stage).
3. **End-to-end wall** — signature path vs shipping F4 at the same commit (Target).
4. **Competitive position** — vs the strongest comparand per row (Stretch).

### 15.2 Primary scoreboard template

| Task | Shipping F4 16w | Sig path 16w | Sig ÷ F4 [95%] | Sig RSS ÷ F4 | Comparand (mode, workers) | Sig ÷ comparand [95%] | Equal-worker ratio | Verification |
|---|---:|---:|---:|---:|---|---:|---:|---|
| Eco-12 / 2⁶⁴−353 | | | | | grobx raw (1w); grobx certified | | | |
| Katsura-11 / Goldilocks | | | | | — | | | |
| Katsura-11 / 2⁶⁴−353 | | | | | grobx raw (1w) | | | |
| MQ11 / Goldilocks | | | | | grobx raw (1w) | | | |
| MQ10 / 32003, 2³¹−1 | | | | | msolve exact, groebner-rs (best w) | | | |
| Cyclic-7 | | | | | grobx raw (1w) | | | |
| controls, held-out rows | | | | | — | | | |

### 15.3 Per-row detail

Process wall; peak RSS and live-entry budget; workers and actual CPU allocation; 95% intervals;
pair rejections by category; reductions to zero; coefficient products; signature-basis size;
symbolic, elimination, bookkeeping and interreduction times; dispatch decision and its cost;
certification status and time (outside solve wall); every timeout, refusal and stopped experiment.

### 15.4 Success tiers, criterion by criterion; negative, inconclusive and stopped results; issue dispositions; follow-ups

As M30 §15.5–§15.8.
