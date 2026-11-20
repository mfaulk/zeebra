# M32-Q: qualification of the adaptive graded path (#941)

**Status:** complete, 2026-11-20. **Gate Q fails** (T4, T7, T8). The held-out set passes. Recommendation for #937: keep the option opt-in (§6).
**Measured at:** freeze F2 = `f427e8d7` (`main` after #950) plus this PR's option, head `f8ec0b4c`
(tag `measured/941-head`), against the M31 reference entry point `c1d93389` (tag
`measured/927-base`; its `src/` is identical to `ce67df76`'s, not `8715c8ed`'s). Each executable was built from a
`git archive` into its own target directory (release, fat LTO, one codegen unit, x86-64-v3,
`--features research-sigf4`, `RUSTC_WRAPPER=""`, `CARGO_INCREMENTAL=0`); SHA-256s are in
[`binaries.sha256`](../../research/m32-qualification/binaries.sha256).
**Plan:** [`MILESTONE-ADAPTIVE-F4.md`](../MILESTONE-ADAPTIVE-F4.md) §6.2 (T3–T9), §7.5, §8.2 (Gate Q),
§8.3 (F2), §9, §10. **Evidence:** [`research/m32-qualification/`](../../research/m32-qualification/README.md).
**Decision:** #937 (the owner's). Nothing here changes a default.

## 1. The option

`F4Options::graded_engine: GradedEngine` is `Conventional` at every preset. With `Adaptive`:

| Entry point | Graded order (grevlex, graded-lex) | Lex, `Weighted`, `Block` |
|---|---|---|
| `f4_with_options`, `f4_reported` | `f4_signature`'s dispatch (signature engine or conventional F4), same basis | conventional F4 |
| solvers on them (`solve_zero_dimensional_with_options` with `GrevlexF4ThenFglm`, the planner's grevlex attempts) | as above | conventional F4 |
| `f4` (no options), `f4_observed`, `f4_observed_reported` (observer promised conventional batches) | conventional F4 | conventional F4 |
| any call with `max_batches` or `max_pairs_per_batch` set | conventional F4 (those count conventional F4's batches) | conventional F4 |

- **Statistics.** `F4Statistics::graded_route: Option<SignatureDispatch>` records the decision.
  When the dispatch picks conventional F4, including a fallback, the statistics are conventional
  F4's own. On the signature route only `batches`, the matrix extents, `elements_added` and
  `bytes_per_entry` are filled.
- **Budgets.** Wall, matrix, basis-size and certification budgets mean the same on both routes, and
  the size-limit fallback is typed and uses the remaining wall. The signature engine's live budget
  is now the smaller of `max_live_bytes` and the live-entry allowance in bytes (equal at every
  preset), but **it is charged only in the parallel cascade**; at one worker the signature route has
  no live-byte budget (§5).
- **Semver.** A new public field on two exhaustive structs: an exhaustive literal breaks,
  `..Default::default()` does not (`CHANGELOG.md`, 0.y).
- **Size.** 170 net lines under `src/` excluding tests, against the 1,200-line cap.

## 2. Freeze and the threshold re-check

`git diff 588d2a44 f427e8d7 -- src/` (Gate R's revision-1 head to F2) adds only
`cfg(feature = "research-sigf4-split")` blocks, which the measured build does not enable. #940
merged no `src/`. The engine and dispatch the four thresholds were fitted on are therefore the ones
measured here, and #941's re-fit trigger (S1 merged after the fit) did not occur. The predeclared
re-check (posted on #941 before any timed child) reads the dev cells each threshold governs:

- `SIGNATURE_CROSSOVER_VARIABLES` (10..=10) and `SIGNATURE_CROSSOVER_WORKERS` (4): MQ10, adaptive ÷
  conventional at 1/4/8/16 (T3).
- `SIGNATURE_SMALL_TEAM_VARIABLES` (10) and `SIGNATURE_SMALL_TEAM` (8): katsura-9, noon-7 and
  noon-8, adaptive ÷ M31 (T4).

**Result: the thresholds stand, and the one allowed re-fit was not used.** Decided on dev rows and
posted on #941 before `held` ran, with an amendment after #958's triage.

Every crossover cell passes:

- MQ10, ad ÷ f4, at 1/4/8/16 workers: 0.432 / 1.008 [0.990, 1.016] / 1.002 / 0.997 on GF(32003),
  and 0.487 / 0.995 / 1.001 / 0.995 on GF(2³¹−1).

Of the small-team cells, noon-7 (0.972 [0.966, 0.979]) and noon-8 (1.005 [0.989, 1.016]) pass.
**katsura-9 at 16 workers fails: 1.036 [1.034, 1.040] against 1.03.** That triggers the rule, but no
threshold value can clear the cell:

- **The gap is not the team cap.** The same gap is there at one worker, where no threshold applies
  (1.047 [1.044, 1.048]).
- **The adaptive wrapper is not the cause.** A same-protocol diagnostic, outside Gate Q
  (`diag-katsura9.jsonl.gz`, n = 11, interleaved, under the reservation, load ≤ 1.54), put the
  option path ÷ the head's own `f4_signature` entry at 0.999 [0.996, 1.003] at 1 worker and 0.996
  [0.994, 1.002] at 16.

A second diagnostic built F2 (`diag-katsura9-f2.jsonl.gz`):

| Ratio | 1 w | 16 w |
|---|---|---|
| head entry ÷ F2 entry (same protocol) | 1.014 [1.009, 1.033] | 1.015 [1.012, 1.017] |
| F2 entry ÷ M31 entry | 1.029 [1.021, 1.034] | 1.024 [1.020, 1.027] |

**Protocol confound (#958).** Every head-side arm ran `--repeat 21`, and every `m31` arm ran
`--calls 20`. The two protocols differ in three ways: which result is held live, whether the drop
is timed, and the size of the summary. So every katsura-9 ratio against `m31`, the gated cell
included, compares across protocols.

Gate R revision 1's head `588d2a44` has F2's timed library and read 1.006 / 0.989 there. The
leading suspect for the ~2.5% F2 ÷ M31 gap is therefore the harness, not the library. The head ÷
F2 1.5% compares like with like. The serial route reads nothing this PR changed, so code layout
under fat LTO is the likely cause of that 1.5%, but that is not shown.

## 3. Gate Q

Paired median ratio, ad ÷ reference [95% bootstrap of the median]. Grevlex throughout. Full tables
are in [`tables.md`](../../research/m32-qualification/tables.md). Three cells took §10.3's single
n = 12 extension on width alone; they are shown at the pooled n = 21.

| Criterion | Cells | Result | Verdict |
|---|---|---|---|
| T3 MQ10 ÷ f4 ≤ 1.05, 1/4/8/16 w | 2 fields × 4 | worst upper 1.026 (GF(32003), 4 w, before extension; 1.016 pooled) | pass |
| T4 ÷ m31 ≤ 1.03 at 16 w | katsura-11 ×2, mq-11, eco-12, noon-7, noon-8, katsura-9 | **katsura-9 1.036 [1.034, 1.040]**: fail, with a plausible measurement-protocol confound tracked in #958 (§2). All others ≤ 1.016 upper | **fail** |
| T4 absolute ÷ f4 at 16 w | katsura-11 ≤ 0.50; mq-11 ≤ 0.50; eco-12 ≤ 0.70 | 0.456 / 0.461; 0.456; **eco-12 0.733 [0.731, 0.736]** | **fail** |
| T5 unfavourable/small ÷ f4 ≤ 1.05, 1 and 16 w | cyclic-7 ×2, katsura-4 ×2, noon-7 | worst upper 1.030 (cyclic-7 / 2⁶⁴−353, 1 w); katsura-4 1.014–1.016 (the dispatch's feature pass on a 6 ms row) | pass |
| T6 peak RSS: ad ÷ f4 ≤ 1.25, ad ÷ m31 ≤ 1.10 | dev and held | worst 1.078 and 1.068 | pass |
| T7 correctness | 16 rows × 2 orders | §5 | **fail** (graded-lex) |
| T8 behaviour | §5 | the 1-worker live gap, graded-lex memory, thread high-water | **fail** |
| T9 dispatch ≤ 50 µs, ≤ 0.1% of wall | every adaptive child | max 6.9 µs; worst share 0.0021% | pass |

**Eco-12's absolute bound** assumed that S1 (#939/#940) would land. It did not, and ad ÷ M31 is 1.007
[1.000, 1.009], so the miss is the engine's ceiling, not the option.

**Foreign load.** The peer job `ca-39-rf4-rp4-s2` held the exclusive lock until 10:05:28 EST.
`zb-941` started at the same second under `benchlock`
([benchlock.log](../../research/m32-qualification/benchlock.log)), so **no timed child overlapped
it**. 50 dev children (rep 0 and part of rep 1, 10:05:28–10:08:52) started at load1 4.1–12.1. That
was the load average decaying from the peer's 32 threads, plus this campaign's own 16. cpu-context
shows no compiler. Each of those children is one of 9 interleaved pairs, and no verdict depends on
one pair, so nothing was re-run for it. `small` had none above 4. `held` had three, all in eco-11
rep 1, at ≤ 4.3.

## 4. Held-out rows (read once)

This set was read once, after the re-check decision was posted. ad ÷ f4, n = 9, gated at 1 and 16
workers (≤ 1.05):

| Row | 1 w | 4 w (info) | 8 w (info) | 16 w | Route at 16 w |
|---|---|---|---|---|---|
| mq-random-10 / Goldilocks | 0.171 [0.168, 0.173] | 0.992 | 1.002 | 1.002 [0.990, 1.011] | worker crossover |
| katsura-10 / GF(2³¹−1) | 0.207 [0.206, 0.208] | 1.005 | 1.000 | 1.001 [0.986, 1.011] | worker crossover |
| eco-11 / GF(2³¹−1) | 0.313 [0.305, 0.318] | 0.627 | 0.737 | 0.794 [0.791, 0.799] | signature |

**Pass.** Peak RSS ad ÷ f4 is 0.85–1.02.

## 5. Correctness, behaviour and resources (§9, T7, T8)

The `check` suite read each cell once:

- 16 rows over GF(32003), GF(2³¹−1), Goldilocks and 2⁶⁴−353;
- grevlex and graded-lex;
- the option at 1–16 workers;
- conventional F4 at 1 and 16;
- certification at 16;
- groebner-rs at 8 and Singular 4.4.1 on the narrow fields;
- a 1 s wall budget.

**Grevlex: correct everywhere.** Every completed child of a row agrees on one digest. On all 16
rows that digest equals conventional F4's and groebner-rs's. Singular agrees on all five
narrow-field rows. The four M31 grobx-certified digests match, and certification passed on every
row. Beside this, the `grobner::external` coverage assertion ran with
`ZEEBRA_REQUIRE_MSOLVE=1`: 343/343 tests, with msolve from `tools/external/env.sh`'s prefix. So did
the live Singular sweep, which passed. Both exercise conventional F4.

**Graded-lex: the signature route fails (#961).** Where the dispatch keeps conventional F4, the
option is fine. That covers the small, degree-spread and worker-crossover cases, and both noon
rows, which finish faster on the signature route. Every other row the dispatch sends to the
signature engine fails, while conventional F4 finishes it, often in seconds:

| Row (graded-lex) | f4 1 w / 16 w | ad (signature route) |
|---|---|---|
| katsura-9 / 2⁶⁴−353 | 0.3 s / 0.1 s | over 8 GiB (rss-guard kill), 1/4/8/16 w |
| katsura-11, both wide fields | 23 s / 2.9 s | over 8 GiB, 1/4/8/16 w |
| mq-random-11 / Goldilocks | typed `TooManyLiveNonzeros` | over 8 GiB, 1/4/8/16 w |
| mq-random-10 / Goldilocks, katsura-10 / GF(2³¹−1) | 35 s, 2.1 s | over 8 GiB at 1 w |
| mq-random-10 / GF(32003) and GF(2³¹−1) | 1.0 s | 180 s wall at degree 14, 1 w |
| eco-12 / 2⁶⁴−353 | 13.9 s | 180 s wall at 1 w; 50–58 s via the `TooManyLiveBytes` fallback |
| eco-11 / GF(2³¹−1) | 1.3 s | 40 s (`TooManyRows` fallback) at 1 w; 21–22 s at 4–16 w |

The plain `f4_signature` entry reproduces the katsura-9 case without the option: 25 s, stopped at
degree 7, 1.9 GB. So this is S2's engine under graded-lex, not the routing. The 8 GiB kills happen
at 16 workers, where the 512 MB live budget is charged, so the growth lies outside live matrix
entries. Every completed graded-lex child agrees with conventional F4 and the references.

**T8.**

- **Budgets.** Wall (both 1 s cases stop typed, within 1,023–1,351 ms), certification, matrix,
  basis-size and size-limit fallback are covered by unit tests and by the `check` suite.
  **The live budget is not charged at one worker (#962), and no budget except wall time bounds
  graded-lex memory (#961).**
- **Thread high-water.** Exceedances read peak −2 against the worker cap, and all of them are on a
  conventional-F4 route (degree spread, worker crossover, fallback):
  - 16 children are over the cap, 15 of them by exactly one;
  - one certification child reads 25 at 16 w.

  The signature route never exceeded its cap. Whether the +1 is conventional F4's coordinator or the
  sampler's baseline was not separated: the `f4` arms were not sampled.
- **Determinism and cancellation.** Equal bases and statistics across workers 1/2/4/8/16, repeated
  (`graded_engine_tests`). Wall and certification stops are typed with partial progress, and the
  fallback is typed with the remaining wall.

**Limitation.** The naive `buchberger_reference` does not finish katsura-4 in release, so it was
dropped as a reference arm. groebner-rs, Singular, msolve (through the coverage assertion) and the
grobx certificates are the independent references.

## 6. Recommendation for #937

**Keep `GradedEngine::Adaptive` opt-in. Do not promote it to the default for graded orders.**
Nothing here changed a default. Reasons, strongest first:

1. **Graded-lex is unsafe on the signature route (#961).** A caller who opts in under graded-lex can
   exhaust memory on systems that conventional F4 solves in a fraction of a second. A default must
   not do that. The guide and `GradedEngine`'s documentation now say to use the option under
   grevlex only.
2. **The budgets do not hold at one worker (#962).** The live-byte budget is not charged on the
   serial cascade. That breaks §9.3's "budgets mean the same on every route".
3. **T4 fails twice.**
   - katsura-9 ÷ M31 at 16 w reads 1.036: fail, with a plausible measurement-protocol confound
     tracked in #958. This is neither a confirmed regression nor an artifact.
   - Eco-12 misses its absolute bound (0.733 against 0.70) because S1 did not land.

The grevlex case for the option is real:

- 0.43–0.49x on MQ10 at one worker, neutral at 4–16;
- 0.46x on katsura-11 and mq-11 at 16 w;
- 0.17–0.31x on the held-out rows at one worker;
- no change elsewhere, correct everywhere, and dispatch costs ≤ 7 µs.

A narrower promotion, grevlex only after #962 is fixed, would be the natural next proposal for
#937, re-qualified on a T4 read that #958 has cleared of the protocol confound.

**Follow-ups:** #961 (graded-lex, High), #962 (serial live budget, Medium), #958 (katsura-9
protocol), all under #938.
