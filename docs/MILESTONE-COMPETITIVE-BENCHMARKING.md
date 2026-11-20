# M33 — Competitive F4 Performance and Reproducible Benchmarking

**Status:** planned, 2026-11-20. No M33 measurement has been taken. §§1–15 are the plan, fixed
before measurement; §17 will hold the integration report (M33-I, #975), written from §16's
template.
**Predecessor:** M32 — Adaptive F4 ([`MILESTONE-ADAPTIVE-F4.md`](MILESTONE-ADAPTIVE-F4.md);
tracker #938, **open**; final report #942, **open**, draft PR #960).
**Planning base:** `main` at `dfd984c0`.
**Measured at:** `8715c8ed`, `7b25a1ee`, `f8ec0b4c`, `2f661626` (quoted; nothing new). Every figure in §§3–4 is quoted from M31's final cohort at
`8715c8ed` ([`research/m31-final/tables.md`](../research/m31-final/tables.md)), the M32 baseline
at `7b25a1ee` ([`m32-baseline.md`](research/m32-baseline.md)), M32 Gate Q at `f8ec0b4c`
([`m32-qualification.md`](research/m32-qualification.md)), or the #739 comparand cohort at
`2f661626` ([`comparand-scaling.md`](research/comparand-scaling.md)), each named where used.
Ratios marked *derived* divide figures from different sessions and are not measurements.
**Tracking issue:** [#965](https://github.com/mfaulk/zeebra/issues/965).
**Project:** [Zeebra #7](https://github.com/users/mfaulk/projects/7); label `M33`. Priority is the
Project field. A dependent issue carries `blocked` until its prerequisite posts its evidence.
Milestones here are labels and documents, not GitHub milestone objects.

**Focus.** Zeebra has never beaten grobx or msolve at an equal worker count on a substantive
complete solve. M33 tries to, on a small number of predeclared rows, with one or two well-attributed
changes per competitor. It also turns the measurement tooling into something an agent can submit
to and walk away from.

## 1. Vision and executive summary

> **M33 — Competitive F4 Performance and Reproducible Benchmarking.** Win at least one
> statistically supported, equal-worker, complete-solve comparison against grobx and one against
> msolve on frozen public instances. Make long performance experiments run reliably beside
> ongoing development.

M33 has two objectives with equal standing:

- **A — competitive performance.** Two tracks. **Track G** targets grobx at one worker on wide
  primes. grobx computes on one thread whatever it is asked (§3.2), so one worker is the only
  equal-worker comparison. **Track M** targets msolve at 1/4/8/16 workers on primes below 2³¹,
  the only fields msolve supports.
- **B — benchmarking infrastructure.** A durable job layer over the existing tools
  (`benchlock`, `bench-reserve`, `cpu-context`, `rss-guard`, `attempt_journal.py`), measured
  isolation quality, a recorded development/publication mode, and one shared comparison and
  reporting path.

The audit (§§2–4) changed three things relative to the initial proposal:

1. **The msolve gap is smaller than the historical table says, and the best target may not be
   MQ10.** M31's 3.07× and 2.29× divided the signature cascade by msolve. Since #950 (M32 S2),
   MQ10 routes to conventional F4 from 4 workers, so the same cells read 2.40× and 2.07×
   (*derived*). msolve's Katsura-11 at GF(32003) takes 1.40 s at one worker and 0.58 s at
   8 (#739). Zeebra's signature route does wide-prime Katsura-11 in 0.95 s at one worker. Nobody
   has measured the two side by side; M33-0 does that first.
2. **grobx Track G must align output handling first.** Zeebra's process wall includes a harness
   basis render (138 ms of Eco-12's 2,557 ms at one worker; 464 ms on MQ11). A driver that does
   not render does not pay it (`m32-baseline.md` §5). M33-0 fixes the timed region before any
   ratio is quoted.
3. **The adopted Track G configuration is not yet resource-safe.** The signature route at one
   worker does not charge `max_live_bytes` (#962). The graded-lex signature route exhausts
   memory (#961). M33-Q cannot admit a one-worker signature win until #962 is fixed. #961 is
   either fixed or the claim is scoped to grevlex with a typed refusal shown elsewhere.

## 2. Current status and predecessor milestone

M32 is **not closed**. As of `dfd984c0`:

| Item | State |
|---|---|
| #940 parallel signature symbolic (S1b) | closed **unmerged**. Gate S failed twice (Noon-7 at 16 w, 1.057 against ≤ 1.05). Tags `measured/940-gate-s`, `measured/940-gate-s2` |
| #927 adaptive dispatch (S2) | merged (#950, `f427e8d7`) |
| #941 Gate Q | merged (#957, `041a21ef`). **Fails** T4, T7 and T8. Held-out passes |
| #937 default decision | closed. **The adaptive graded path stays opt-in** |
| #942 final cohort and report | **open**. Draft PR #960 predates Gate Q's merge |
| #958 katsura-9 2.5% drift, #964 quiet unfused A/B | open, claimed |
| #961 graded-lex OOM/stall, #962 no 1-worker live budget | open bugs, unclaimed |

**Dependency.** M33's baseline freeze **F0** (§11.4) is the commit that #942 measures as M32's
final revision. Once #942 merges, M33-0 builds F0 from it. Until then:

- M33-0's pre-registration (corpus admission, the held-out draw, comparand re-pinning, the msolve
  thread census) may proceed.
- Track B may proceed.
- No M33 performance figure is taken.

M32's preliminary figures (#960's draft) are not M33 baselines.

## 3. Existing competitive evidence

Every ratio is Zeebra wall ÷ competitor wall, process wall time, deterministic Zeebra output.
"Equal-worker" means the same requested worker count. Below that is labelled
*best-supported-configuration* (BSC).

### 3.1 Track G — grobx (raw randomized mode, 1 worker; M31 final, `8715c8ed`, n = 9)

| Row | grobx ms | Zeebra sig 1 w ÷ grobx [95%] | Zeebra sig 16 w ÷ grobx (BSC) | M32 baseline sig 1 w ms (`7b25a1ee`) |
|---|---:|---:|---:|---:|
| Eco-12 / 2⁶⁴−353 | 1,746.5 | **1.464** [1.391, 1.565] | 0.999 [0.948, 1.063] | 2,557 (→ 1.464, *derived*) |
| Katsura-11 / 2⁶⁴−353 | 580.6 | 1.578 [1.480, 1.654] | 1.056 [0.989, 1.106] | 915 (→ 1.576, *derived*) |
| MQ11 / Goldilocks | 3,130.9 | 1.711 [1.624, 1.814] | 0.679 [0.645, 0.720] | 5,338 (→ 1.705, *derived*) |
| Cyclic-7 / 2⁶⁴−353 | 126.7 | 2.230 [2.106, 2.336] | 1.149 | — |

- grobx is pinned at `1854835d` (0.73.3); its driver refuses requests above one worker
  (`grobx-comparand.md`).
- Raw mode is randomized (fixed-seed Xoshiro) and uncertified. Certified mode is a separate,
  much slower row (Eco-12 308 s, 10.6 GiB).
- grobx raw ran 4–9% slower in M31's session than in M30's with the same executable, so these
  ratios carry session sensitivity.
- No M32 figure changes the equal-worker gap. M32's gains were at 16 workers or against
  conventional F4.

### 3.2 Track M — msolve (exact, 0.11.0; characteristic < 2³¹ only)

| Row | Workers | msolve ms | Zeebra ÷ msolve | Source |
|---|---:|---:|---:|---|
| MQ10 / GF(32003) | 1 | 221.0 | 4.91 (conv F4) / 2.11 (sig route, *derived*) | M31 window; M32-Q |
| | 4 | 127.5 | 3.06 / 3.11 (*derived*) | ″ |
| | 8 | 117.0 | 2.37 (conv) — historical 3.067 was the sig route | M31 `tables.md` |
| | 16 | 125.5 | 1.91 | ″ |
| MQ10 / GF(2³¹−1) | 1 | 239.2 | 3.88 / 1.90 (sig, *derived*) | ″ |
| | 4 | 163.4 | 2.02 — historical 2.291 was the sig route | ″ |
| | 8 | 467.2 | 0.54 — **msolve anomaly**, not a win (§8.4) | ″ |
| | 16 | 215.4 | 1.05 | ″ |
| Katsura-11 / GF(32003) | 1 / 4 / 8 | 1,398.7 / 676.1 / 579.7 | **unmeasured**. Zeebra's wide-prime sig route is 949 ms at 1 w | #739 `2f661626` |
| Katsura-11 / GF(2³¹−1) | 1 / 8 | 1,532.8 / 715.5 | unmeasured | #739 |
| Cyclic-7 / GF(32003) | 1 / 2 | 82.5 / 71.7 | unmeasured; below the substantive floor (§5.2) | #739 |

- msolve's thread use has never been recorded, only process CPU/wall. At 16 workers its intervals
  are wide ([0.12, 0.88] s on MQ10) and process CPU reaches 8.9 s. That looks like spinning, not
  parallel work (`research/comparand-scaling/README.md`).
- msolve-gap's mechanisms (13.9× wall, 579.7 M back-substitution products, 4.77× per-product
  cost) were measured at `99a81844` and predate #749's candidate-only backward reduction (579.7 M
  → 23.6 M products). **They are stale and are not M33 evidence.**

### 3.3 Where Zeebra already leads at equal workers

- **groebner-rs at one worker:** 0.800 / 0.405 / 0.556 on Eco-12 / Katsura-11 / MQ11 (M31).
- **msolve:** nowhere, except the GF(2³¹−1) 8-worker anomaly.
- **grobx:** nowhere.

## 4. Current implementation and bottlenecks

### 4.1 One worker, wide primes (signature route, M32 baseline `7b25a1ee`, medians, ms)

| Row | Wall | Symbolic | Elimination | Bookkeeping | Interreduction | Harness render |
|---|---:|---:|---:|---:|---:|---:|
| Eco-12 / 2⁶⁴−353 | 2,565 | 462 | 1,326 | 230 | 269 | 138 |
| Katsura-11 / Goldilocks | 949 | 158 | 452 | 16 | 110 | — |
| MQ11 / Goldilocks | 5,345 | 442 | 3,652 | 27 | 509 | 464 |

- Elimination is 48–68% of the wall.
- Interning is 61–86% of the symbolic stage.
- The unfused multiply-then-intern build measured 0.60× symbolic on Eco-12 and 0.64× on MQ10,
  but **1.16× on Katsura-11**. It was measured at load 18–20, is unexplained, and #964 is
  re-reading it quietly.
- Wide primes admit no delayed reduction (#270). The row update uses Shoup multiplication
  (#779).
- Eco-12's gap to grobx is mostly **reductions to zero** under conventional F4: 6,331 of 7,202
  reduced pairs, 93% of coefficient work, against grobx's 226. grobx avoids them with randomized
  row combinations (`m29-grobx-attribution.md`).
- The signature route removes much of this zero work. No document yet reports what fraction of
  its 1,326 ms elimination is useful versus zero, or its per-product cost against grobx's. That
  is G1's first question.
- An *exact* variant of grobx's route is the open #955.

### 4.2 Small primes, multicore (conventional F4 from 4 workers)

- MQ10 / GF(32003) walls: 1,085 / 383 / 274 / 241 ms at 1/4/8/16 workers. At 1 worker the
  signature route is used: 473 ms, of which symbolic is 205 and elimination 191.
- Elimination backends:
  - `Backend::Adaptive` (`src/linalg/dense/accumulator.rs`): a dense scratch row against sparse
    pivots, reduced on every update.
  - `Sparse` and `Dense` exist beside it.
  - There is **no delayed-reduction kernel** in production. The GF(32003) pilot won 28% on
    arithmetic and was rejected on a Noon-6 regression (#269, `elimination-kernels.md`).
  - There are no explicit SIMD intrinsics (x86-64-v3 autovectorization only). Sparse entries are
    16 bytes each (#268, deferred).
- Dense planted MQ over GF(31) spends 93% in the forward pass at a flat cost per row-op × column
  (#945). #918 (separate FL sweep and D′ clocks) is its measurement prerequisite.
- The MQ10 signature route spends 35% of engine time after its last essential element (#946).
- **No current-code decomposition against msolve exists.** That is M1's first deliverable.

### 4.3 Refuted or closed (do not reopen without new evidence)

- Multirow reuse (#715): 2.47× fewer pivot reads, only 0.974× forward.
- An AVX2 dense-span kernel (#149/#541).
- Delayed reduction at 31 bits or wider (#270).
- A fixed density threshold across fields (#269).
- Reducer-search indexes (2–6% of symbolic).
- The stitch/merge walk (#888, 6.6% cap).
- Discarding dominated signature elements (3.1% of Eco-12).
- Packed exponents.
- #940's parallel symbolic design as built (§6.3).

## 5. Benchmark portfolio and selection methodology

### 5.1 Sources

M33 reuses `research/wide-corpus/cases.json`, `research/public-corpus/` and the M31/M32 pins
(`research/m32-baseline/pins.json`, catalog SHA `43f42f5e…`). It also reuses the existing drivers
(`tools/external/grobx-driver`, msolve via `tools/external/comparand-scaling.py`) and
`CompetitiveRecord` (`src/grobner/external/board.rs`). New instances come only from existing
generators (Katsura, Eco, Cyclic, Noonburg, seeded dense random MQ). Each is identified by its
input SHA-256.

### 5.2 Admission rule (applied by M33-0 before any M33 timing)

An instance is admissible to a track when **all** of the following hold:

1. **Field supported** by the competitor: msolve characteristic < 2³¹; grobx any of its wide
   adapters' fields.
2. **Valid task:** grevlex, a zero-dimensional or positive-dimensional ideal, full reduced
   Gröbner basis requested, input digest recorded.
3. **Substantive:**
   - Competitor process wall ≥ 300 ms at the compared worker count, taken from prior records
     (#739, M31) where they exist, or from one *admission* run that is not timed for any gate.
   - Both process walls ≥ 2× the Katsura-4 startup control (`external-comparison-protocol.md`
     §7).
   - Rows below the floor use the small-system procedure (§11.6) and cannot count as a win.
4. **Bounded:** every arm finishes within 180 s and 8 GiB at its slowest worker count; grobx raw
   within 8 GiB.
5. **Verifiable:** the reduced basis digest agrees across Zeebra, the competitor and one
   independent reference (Singular below 2³¹; groebner-rs or grobx certified on wide fields).

### 5.3 Sets (fixed by M33-0 and posted on #965 before any M33 timing)

| Set | Track G (grobx, 1 w) | Track M (msolve, 1/4/8/16 w) |
|---|---|---|
| **Development** | Eco-12 / 2⁶⁴−353 (primary); Katsura-11 / 2⁶⁴−353; MQ11 / Goldilocks | MQ10 / GF(32003), GF(2³¹−1); Katsura-11 / GF(32003), GF(2³¹−1) |
| **Controls** (no regression; not competitive targets) | Cyclic-7, Noon-7, Noon-8, katsura-9 at 2⁶⁴−353; Katsura-11 / Goldilocks; katsura-4 small control | Cyclic-7 / GF(32003); Noon-7 / GF(32003); Eco-11 / GF(2³¹−1); katsura-4 control |
| **Held-out** (drawn, §5.4) | 2 instances | 2 instances |

### 5.4 Held-out draw

M33-0 does the draw before any M33 measurement:

- It lists every admissible instance in the families Katsura 8–12, Eco 10–13, Cyclic 6–8,
  Noon 7–8 and MQ 9–11.
- For MQ it uses **fresh generator seeds**: seeds 1–8 of the existing MQ generator, never a seed
  used in M29–M32.
- It excludes every instance named in any M29–M32 development, control or held-out table.
- Per track, it sorts the candidates by `SHA-256("M33-holdout" ‖ track ‖ input digest)` and takes
  the first two that pass §5.2 in the admission run.
- At most one may be MQ.

The draw script, the candidate list and the result are committed under `research/m33-baseline/`.
The two held-out instances are **not timed for Zeebra performance** until Gate D (§13).
Admission runs record only pass/fail against §5.2's floor and ceiling.

### 5.5 Primary targets (hypotheses, confirmed or replaced by M33-0's baseline)

- **Track G primary: Eco-12 / 2⁶⁴−353 at 1 worker.** It has the smallest gap (1.46×) and the
  largest signature-route stages to attack. Secondary: Katsura-11 / 2⁶⁴−353 (1.58×).
- **Track M primary: chosen by M33-0** between MQ10 and Katsura-11 at GF(32003) or GF(2³¹−1),
  by the smallest equal-worker gap at a non-anomalous worker count (§8.4).

## 6. Falsifiable performance hypotheses (unmeasured)

| Id | Hypothesis | Falsified if |
|---|---|---|
| **H0** | Zeebra's signature route is within 1.25× of msolve at 1 worker on Katsura-11 at a small prime | M33-0 measures > 1.25× |
| **HG1** | A removable share of Eco-12's 1-w signature elimination is reductions to zero or redundant row work; avoiding it exactly cuts ≥ 15% of wall | G1 counts show zero/redundant rows carry < 15% of elimination products |
| **HG2** | An interning layout change (unfused multiply → batched intern, or better probe locality) cuts ≥ 8% of 1-w wall on Eco-12 **without** slowing Katsura-11 by > 2% | #964's quiet read or G1's attribution shows the Eco-12 symbolic gain < 0.85×, or Katsura-11 is still slower after one bounded explanation attempt |
| **HG3** | ≥ 5% of 1-w wall is non-algorithmic: basis materialization, render or harness | G1's decomposition shows < 5% outside the four stages under the aligned timed region (§11.3) |
| **HM1** | On the Track M primary, Zeebra's per-useful-product cost (ns), not work count, explains most of the gap | M1 finds coefficient products ≥ 1.5× msolve's |
| **HM2** | A size/density-gated delayed-reduction dense forward kernel for p < 2¹⁶ (u16 pivots, u64 accumulators) cuts forward time ≥ 25% on qualifying matrices, with a measured crossover | M1/M2 cannot find a crossover that leaves every control within 1.05× |
| **HM3** | Zeebra's 4→8→16 scaling is limited by a measurable serial stage or synchronization, not bandwidth | M1's critical-path trace shows bandwidth-bound elimination at 8 w (scaling flat while the serial share is < 10%) |

Each WP that tests a hypothesis states its predicted end-to-end gain before Gate B (§13).

## 7. Benchmarking infrastructure objectives

What exists (audited):

- **`benchlock.sh`:** flock queue and START/END log.
- **`bench-reserve.sh`:** cgroup cpuset CCD reservation; default CCDs 1–2, CPUs 8–23 with SMT
  siblings 72–87 held idle.
- **`cpu-context.sh`:** load, frequency, governor, boost, compiler count.
- **`rss-guard.sh`:** memory guard.
- **`check-measurement-provenance.sh`:** checks that measured documents carry their commit.
- **`attempt_journal.py` (`StudyJournal`):** frozen header/plan/limits, a hash-chained fsynced
  journal, exit before verdict, refusals and stops. Used by only one study.
- **Per-campaign `campaign.py`/`summarize.py`:** copied between milestones, resumed by a manual
  `--start-rep`.
- **`CompetitiveRecord` → `history.json` → `COMPETITIVE.md`.**

What is missing:

- job and attempt IDs, a persistent queue, status, cancel, and resume that skips completed
  attempts;
- binary-hash verification at launch;
- a recorded measurement mode;
- SMT-sibling and per-CPU busy accounting;
- accounting for the 24 self-hosted `Runner.Listener` processes of other repositories on this
  machine;
- fixed clock (#954);
- one shared statistics/verdict implementation;
- a performance CI tier.

| Objective | WP | Extends |
|---|---|---|
| B1 durable jobs: manifest, prebuilt binaries by hash, job/attempt IDs, queue, status, cancel, timeout, resume, preserved failures | M33-B1 #967 | `attempt_journal.py`, `benchlock.sh`, `bench-reserve.sh run`, `research/m31-baseline/campaign.py`'s `plan`/`run_one` |
| B2 isolation and calibration; dev/publication modes; contamination criteria | M33-B2 #968 (+ #954) | `cpu-context.sh`, `bench-reserve.sh`, `docs/guide/benchmarking.md` |
| B3 (= B4 of the request) shared comparison, verdicts and scoreboard; B5 CI tiers | M33-B3 #969 | the `summarize.py` family, `CompetitiveRecord`, `.github/workflows/rust.yml` |

**Not built:** a service, a database or a daemon that outlives its job. Every state file is a
versioned file under one directory, and the runner is an ordinary process under `benchlock`.

## 8. Success tiers (fixed now; scored as written by M33-I)

M33-I scores each criterion **met**, **missed** or **not attempted**, with the reason. A missed
competitive target permits a Minimum closeout, reported as missed.

### 8.1 Minimum

- **M-1.** Baseline frozen at F0 (§11.4). Competitive gaps re-measured in one session per
  track, under the aligned timed region (M33-0).
- **M-2.** Current-code decompositions published for both competitors: stage clocks, work
  counters and per-product cost (G1, M1).
- **M-3.** At least one candidate per track taken through Gate B, or a Gate A record explaining
  why none qualifies (G2, M2).
- **M-4.** At least one real M33 campaign run end-to-end through the B1 job runner under a CCD
  reservation while other agents built and tested. Its benchlock and cpu-context records show
  the concurrent load (B1, B2).
- **M-5.** Complete provenance, correctness evidence and an integration report including every
  negative result (M33-I).

### 8.2 Target

- **T-G.** One equal-worker (1 w) complete-solve win against grobx raw on a Track G development
  row, **confirmed** at Gate D (§8.4).
- **T-M.** One equal-worker win against msolve on a Track M row at a non-anomalous worker count,
  confirmed at Gate D.
- **T-B.** An agent submits a job, works on something else, and later retrieves a complete,
  verified, summarized result. This is shown by ≥ 3 M33 campaigns run through B1, with ≥ 1
  interrupted and resumed without repeating a successful attempt.
- **T-Q.** M33-Q passes for every adopted change (§12), including #962 fixed.
- **T-R.** No unacceptable regression on controls and held-out rows (§12.2).

### 8.3 Stretch

- **S-1.** Two equal-worker wins per competitor on distinct families.
- **S-2.** One win with an upper bound ≤ 0.833 (Zeebra ≥ 20% faster).
- **S-3.** Zeebra's 4 → 16 worker speedup on the Track M primary improves by ≥ 15% against F0.
- **S-4.** A publication-mode scoreboard (§11.2), regenerated from retained records by one
  command.
- **S-5.** Fewer manual steps in a campaign: from manifest to tables with no hand edits, against
  M32's `run.sh` + `--start-rep` + `summarize.py` copy.

### 8.4 What counts as a win

- **Instance and objective.**
  - Identical input digest, field, variable order and grevlex order.
  - Full reduced Gröbner basis with its digest equal to the independent reference.
  - Zeebra deterministic against grobx raw randomized, or msolve exact. The guarantee difference
    is printed on the row and never merged.
- **Workers.**
  - Equal requested workers; observed threads recorded (§11.5).
  - For msolve, the compared count must be one where msolve's median is within 1.10× of its own
    best over {1, 4, 8, 16} in the same session. A win at a count where msolve is anomalously slow
    is reported as **"win against an msolve scaling anomaly"** and does not score T-M.
- **Statistic.**
  - Ratio = median(Zeebra) ÷ median(competitor), process wall, over ≥ 9 interleaved repetitions
    per arm.
  - 95% percentile bootstrap, 20,000 draws, each side resampled independently.
  - **Win:** median < 1 and upper bound < 1.
  - A row whose interval spans 1 after n = 9 gets **one** predeclared extension of n = 12, pooled
    and read once. Otherwise it is *inconclusive*.
- **Confirmation (Gate D).**
  - Development-row wins are **exploratory**: several rows were screened.
  - A win scores T-G or T-M only if the same row wins again in the Gate D publication session
    (§11.2) on the frozen final revision, **and** Zeebra's ratio on that track's held-out rows is
    no worse than the development row's ratio + 0.15.
  - A held-out row that is itself a win is reported as such. A held-out row that is not a win does
    not cancel a confirmed development win, but is reported beside it.

## 9. Work packages

Each issue body carries the full specification. Here is the summary.

### 9.1 M33-0 — baseline, corpus, scoreboard and cost model (#966, High)

- **Part 1 (claimable now):**
  - the admission rule and held-out draw (§5);
  - comparand re-pin: verify grobx 0.73.3 and msolve 0.11.0 against the latest upstream release,
    and pin the current release (keeping the M31 pin as a continuity row);
  - grobx's actual thread use under a 16-worker request;
  - an msolve thread census at 1/4/8/16 (`/proc/<pid>/task` sampling and `-t`);
  - the aligned timed region in every driver (§11.3).
- **Part 2 (after #942 merges):**
  - build F0;
  - the baseline cohort: both tracks' development and control rows, Zeebra and competitor
    interleaved in one session per track, 1/4/8/16 w for Track M and 1 w (+16 w BSC) for
    Track G;
  - publish the competitive scoreboard and a cost model (§6.3-style additive estimate) per primary
    row;
  - name the Track M primary.
- **Cap:** 5 sessions; ≤ 500 net lines of driver/harness change; no library behaviour change.

### 9.2 M33-B1 — durable benchmark jobs (#967, High, claimable now)

- A `tools/bench-job` CLI with `submit`, `status`, `cancel`, `run` and `resume`.
- The job directory lives under `/buildcache/bench-jobs/<job-id>/`.
- `manifest.json` is immutable and content-addressed. It records the arms with binary SHA-256,
  the source commit and the build flags. It also records the instances with digests, the worker
  counts, the CPU set, the limits, the repetitions, the interleave plan, the mode and the seed.
- Binaries are copied into the job directory at submit time and re-hashed before every attempt.
- The runner executes attempts under `benchlock` + `bench-reserve run` and records into a
  `StudyJournal`. Attempt ID = `(job, plan index, attempt n)`.
- Resume skips any plan index with a recorded exit. Every non-success outcome stays in the
  journal: failed, timed out, refused, cancelled or stopped.
- Submit refuses a dirty tree or a binary not built from the named commit's `git archive`. A job
  never rebuilds.
- `campaign.py`'s `plan`/`run_one` are moved into a shared module so M29–M32 campaigns keep
  replaying.
- **Cap:** ≤ 1,500 net lines (Python/shell incl. tests); 4 sessions.

### 9.3 M33-B2 — isolation, calibration and measurement modes (#968, High, claimable now)

- **Extend `cpu-context`** to record:
  - per-CPU busy % over the attempt, including SMT siblings;
  - `scaling_min/max_freq`;
  - package power where readable (RAPL);
  - temperature;
  - kernel version;
  - process counts of compilers, `Runner.Listener` workers and other `benchlock` owners.
- **Fold #954 (fixed clock) in as a sub-issue.** It stays opt-in and root-gated; its sudoers or
  systemd change is documented separately and reversible.
- **Calibrate.** Run A/A and paired A/B on Eco-12 1 w and MQ10 16 w while CCDs 0, 3–7 carry:
  - nothing;
  - a `cargo build -j48`;
  - a memory-bandwidth load (STREAM-like, on the non-bench CCDs).

  Report ratio drift and absolute drift per condition.
- **Contamination criteria** (§11.2), computed per attempt and stored in the journal.
- **`--mode dev|publication`** recorded in the manifest and enforced by the runner.
- **Cap:** ≤ 800 net lines; 4 sessions; ≤ 3 calibration sessions of ≤ 2 h on the reserved
  CCDs.

### 9.4 M33-B3 — shared comparison, reporting and CI tiers (#969, Medium, claimable now)

- One Python module, `tools/bench_stats.py`, replacing the copied `interval()`/precision-rule
  code. It provides:
  - paired ratio;
  - independent-resample ratio;
  - the §8.4 win rule;
  - the precision and extension rule;
  - verdicts: `win`, `loss`, `inconclusive`, `regression`, `no-regression`, `stopped`.
- `bench-job report` renders tables (wall, RSS, stages, scaling curves, provenance, verification
  status) from a journal.
- A bridge emits `CompetitiveRecord` rows so the publication scoreboard keeps using
  `history.json` → `COMPETITIVE.md`.
- **CI:**
  - PR CI adds only the unit tests of these tools (inside `agent-scripts`).
  - Nightly adds a 2-attempt `bench-job` smoke on katsura-4 with timing ignored.
  - No performance gate runs in GitHub CI: there is no self-hosted runner for this repository, and
    the owner wants PR CI fast.
- **Cap:** ≤ 1,000 net lines; 3 sessions.

### 9.5 M33-G1 — attribute the 1-worker grobx gap (#970, High, blocked by M33-0)

- **Per Track G development row**, for Zeebra's signature route and conventional F4:
  - stage clocks plus the outside-stage split;
  - work counters: pairs generated and rejected, rows reduced, reductions to zero, coefficient
    products, matrix dimensions and nonzeros, basis sizes;
  - per-product cost.
- **For grobx**, the same counters via `grobx-work-study.py` (read-only instrumentation of a
  local build; no GPL code enters Zeebra).
- **Answers:**
  - What fraction of signature elimination is zero or redundant work (HG1)?
  - Read #964's quiet unfused A/B and, if it holds, explain Katsura-11's regression (HG2).
  - How large is the non-algorithmic share under the aligned region (HG3)?
  - Does #955's exact zero-skipping have a costed design, from its existing analysis?
  - Does #877's tail-only interreduction or #894's concurrent-kernel-at-1-CPU effect apply to
    these rows?
- **Output:** `docs/research/m33-grobx-attribution.md`, a ranked candidate list with estimated
  end-to-end gain per row, and **at most two** candidates proposed for G2 with Gate A records.
- **Cap:** 4 sessions; instrumentation ≤ 400 net lines behind an existing research feature.

### 9.6 M33-G2 — bounded wide-field experiments (#971, Medium, blocked by G1)

- At most **two** principal candidates, each through Gates B–C (§13).
- Expected file scope: `src/grobner/sigf4/` (symbolic, interning, engine),
  `src/poly/multivariate/monomial_hash.rs` and the interreduction route.
- `src/linalg/` only if G1 names an elimination-kernel candidate, and then sequenced with M2
  (§10.2).
- Reviving #940's parallel symbolic design requires a written hypothesis for its Noon-7 and
  1-w failures **and** an owner decision on #965.
- **Cap:** ≤ 1,500 net lines under `src/` per candidate, excluding tests; ≤ 8 sessions per
  candidate; one corrective iteration after a failed gate.

### 9.7 M33-M1 — attribute the equal-worker msolve gap (#972, High, blocked by M33-0)

- **Per Track M development row at 1/4/8/16 w:**
  - forward and backward coefficient products;
  - sparse row applications and mean row length;
  - matrix dimensions and nonzeros;
  - arithmetic throughput (products/s);
  - time per useful (nonzero-result) reduction;
  - peak RSS and memory traffic (`perf stat` uncore/LLC-miss counters where available);
  - worker utilization, synchronization wait and serial-stage critical path.
- **msolve's counts** via the existing `msolve-count.py`.
- **Includes #918** (clock the FL sweep apart from D′) as a sub-issue.
- **Answers:** HM1, and HM3. It also re-tests the #269 crossover on current code at the relevant
  matrix shapes for HM2.
- **Reviews** #945 (dense small-prime forward) and #946 (post-essential tail), choosing **at most
  two** M2 candidates with Gate A records.
- **Output:** `docs/research/m33-msolve-attribution.md`.
- **Cap:** 4 sessions; ≤ 400 net lines of instrumentation.

### 9.8 M33-M2 — bounded small-prime experiments (#973, Medium, blocked by M1)

- At most **two** principal candidates.
- Expected file scope: `src/linalg/dense/`, `src/linalg/concurrent.rs`, `src/fields/` (small-prime
  arithmetic), `src/grobner/f4/faugere_lachartre.rs` and `parallel.rs`.
- Any representation change must be gated by a measured size/density/field crossover. No
  unconditional backend switch, and no generic linear-algebra rewrite.
- **Cap:** ≤ 1,500 net lines under `src/` per candidate, excluding tests; ≤ 8 sessions per
  candidate; one corrective iteration.

### 9.9 M33-Q — correctness, resource safety and held-out qualification (#974, High, blocked)

- **Blocked by** G2, M2 and **#962**.
- Qualifies the merged F2 revision (§11.4) against F0 on every adopted change. It applies §12's
  contract across supported fields (31-bit, 2⁶⁴−59, 2⁶⁴−353, Goldilocks, GF(2) where routed)
  and orders (grevlex, graded-lex, lex refusal and fallback).
- Includes the budget and cancellation suite, and the control set at the relevant worker counts.
- **Reads the held-out set once** (Gate D, Zeebra vs F0) before M33-I's publication session.
- #961 must be fixed, **or** every M33 claim on the signature route must be stated as
  grevlex-only, with graded-lex refused or routed to conventional F4 by a typed rule that Q tests.
- **Cap:** ≤ 1,000 net lines (tests and harness); 5 sessions.

### 9.10 M33-I — publication campaign and integration report (#975, High, blocked)

- **Blocked by** M33-0, B1, B2, B3, G2, M2 and Q.
- One publication-mode session per track at F3 (§11.4).
- **Contents:**
  - every development, control and held-out row against both competitors;
  - Track M at 1/4/8/16 w;
  - Track G at 1 w plus 16 w BSC;
  - groebner-rs as a reference row.
- Scored against §8. Report in §17 from §16's template. Evidence in `research/m33-final/`;
  measured commits tagged.
- **Cap:** 3 sessions; no library change.

### 9.11 Reused issues

| Issue | Role in M33 | Re-parented? |
|---|---|---|
| #954 fixed clock | sub-issue of B2; its proposal stands | yes → #968 |
| #918 FL sweep clock | sub-issue of M1 | yes → #972 (was #69) |
| #955 exact zero-skipping | G1 input; a G2 candidate only via a Gate A record | yes → #970 |
| #962 1-w live budget | **required** before Q | no (stays under #938); linked; `M33` label added |
| #961 graded-lex sig OOM | required or scoped out by Q | no; linked; `M33` label added |
| #964 quiet unfused A/B | G1 input (HG2) | no |
| #945, #946, #877, #894 | candidate inputs to M1/G1; adopted only through a Gate A record | no |
| #888 | not M33. Measured at a 6.6% cap; nothing to build | — |

## 10. Dependency graph and parallel execution

### 10.1 Graph

```
#942 (M32-I) ──► M33-0 Part 2 (F0 + baseline) ──┬──► G1 ──► G2 ──┐
M33-0 Part 1 (claimable now) ───────────────────┘   └──► M1 ──► M2 ──┼──► Q ──► I
                                                    #962 ─────────────┘     ▲
B1 (now) ──► B3 report/bridge (B3 stats lib now) ───────────────────────────┤
B2 (now; #954 inside) ─────────────────────────────────────────────────────┘
```

- **Critical path:** #942 → M33-0 → {G1 → G2, M1 → M2} → Q → I.
- **Claimable at planning time:** M33-0 (Part 1), B1, B2, B3, and #962 (an M32 bug that M33
  needs).
- G1 and M1 run concurrently. They touch disjoint instrumentation and measure under the CCD
  reservation, one campaign at a time through `benchlock`.
- B2's calibration campaigns use B1 once it merges; until then they use `bench-reserve run`
  directly.

### 10.2 File ownership (writers)

| Area | Owner | Rule |
|---|---|---|
| `src/grobner/sigf4/`, `src/poly/multivariate/monomial_hash.rs` | G2 | M2 does not touch these |
| `src/linalg/dense/`, `src/linalg/concurrent.rs`, `src/fields/`, `src/grobner/f4/{faugere_lachartre,parallel}.rs` | M2 | G2 touches these only if G1 names an elimination candidate; then G2 waits for M2's open PR to merge |
| `src/grobner/sigf4/budget*`/live accounting | #962 | lands before G2's first PR, or G2 rebases on it |
| `tools/bench-job*`, `tools/external/attempt_journal.py` | B1 | |
| `tools/cpu-context.sh`, `tools/bench-reserve.sh`, `tools/bench-clock.sh` | B2 | |
| `tools/bench_stats.py`, `.github/workflows/rust.yml` | B3 | |
| `research/m33-*/` | the WP named in the directory | |

**One writer per checkout** (CLAUDE.md §1): each WP works in its own `git worktree`, with a
private `CARGO_TARGET_DIR=/buildcache/cargo-target/zeebra-<issue>` and `RUSTC_WRAPPER=""`.

## 11. Benchmark methodology and statistical protocol

### 11.1 Identity

Every attempt records:

- solver, source commit, executable SHA-256, compiler version and flags;
- field and representation; variable order and monomial order; input digest;
- requested output (full reduced basis) and seed(s);
- requested and **observed** workers; CPU affinity;
- process wall, in-process solve time and per-stage clocks;
- peak RSS; work counters; basis digest; verification status and time;
- every refusal, timeout, budget stop and cancellation.

Zeebra arms are built from `git archive` of their commit: release profile, fat LTO, one codegen
unit, `x86-64-v3`. Competitors use their pinned provision scripts; toolchain and ISA differences
are printed on the row.

### 11.2 Modes

| | **dev** | **publication** |
|---|---|---|
| Purpose | keep/drop a change; Gates B–C | Gate D; the competitive scoreboard |
| Placement | `bench-reserve reserve 1,2`, children pinned to physical CPUs 8–23, siblings idle | the same placement **and** an exclusive `benchlock`, with no foreign campaign |
| Rest of machine | builds, tests and agents allowed | no compiler/linker processes during attempts; other repositories' runners idle (B2 checks) |
| Clock | recorded | fixed (#954) if B2 qualifies it; otherwise boost, recorded, and the same for every arm |
| Statistic | paired Zeebra ÷ Zeebra ratios; A/A control per session | absolute medians; Zeebra ÷ competitor with independent resampling |
| Validity | an attempt is **contaminated** if, over its interval, any bench CPU or its SMT sibling shows > 5% foreign busy time, or the bench CPUs' median frequency deviates > 3% from the session median. Contaminated attempts are retained, flagged and excluded from verdicts. A session with > 20% contaminated attempts is void and re-run whole | the dev rule, plus load1 on the non-bench CCDs < 4 and no compiler process in `cpu-context` |

B2 may tighten these thresholds after calibration; it may not loosen them without an owner
decision on #965.

**Promotion.** A candidate advances dev → publication only through Gates C and D. A dev-mode
absolute figure is never published as a competitive result.

### 11.3 Timed region (aligned by M33-0)

The timed region is process wall from `exec` to exit. Inside it, every solver:

- parses the input;
- computes the full reduced basis;
- holds the basis in its native in-memory form;
- prints only a digest computed by a common routine over the canonical serialization (#920's
  order).

Basis rendering for verification happens **after** the clock stops, or in a separate verification
process. In-process solve time is recorded beside it where the driver exposes it. Where a
competitor cannot avoid printing its basis, M33-0 measures that cost and reports both ratios.

### 11.4 Freezes

- **F0** — M32's final revision once #942 merges.
- **F1** — per gate: the head and its merge base, each from `git archive` into its own target
  dir, interleaved in one job.
- **F2** — qualification (Q): a pinned commit after G2 and M2 merge or close.
- **F3** — final (I): the final revision, with F0 rebuilt beside it.

If measured paths (`src/grobner/`, `src/linalg/`, `src/fields/`, `src/poly/`) change between F2
and F3, M33-I reports against both and records `git log F2..F3 --numstat`. Measured commits are
tagged `measured/<issue>-<slug>` before squash-merging.

### 11.5 Workers

- **Track G:** 1 worker each. Zeebra 16 w vs grobx 1 w is a separate BSC row.
- **Track M:** 1/4/8/16 workers, both solvers, one physical core per worker (CPUs 8–23, siblings
  idle).
- **Observed thread counts** are sampled from `/proc/<pid>/task` during each attempt. A row whose
  observed count disagrees with the request is labelled.
- 16 logical CPUs on a reservation is not evidence of 16 active workers.

### 11.6 Repetitions and statistics

- Fresh process per attempt; arms interleaved and rotated per repetition; deterministic seeds
  recorded.
- n ≥ 9 for every gate and for the final campaign; n ≥ 5 for exploration.
- Zeebra ÷ Zeebra: paired-per-repetition ratio. Zeebra ÷ competitor: independent resampling.
  Both use a 95% percentile bootstrap with 20,000 draws, implemented once in B3.
- **Precision rule.** A gate is readable only if its interval half-width ≤ half the distance
  between threshold and 1.0. Otherwise one predeclared n = 12 extension is pooled and read once.
- **Rows under 300 ms process wall** use the warm-call method: k = 21 warm calls per process,
  median per process, n ≥ 31 processes. Process wall is reported beside the warm-call figure.
  They never score a win.
- Verification time is reported separately and never included.
- No unfavourable attempt is removed. Contaminated ones are flagged under §11.2 and kept.

## 12. Correctness and resource-safety requirements

### 12.1 Contract for every adopted change

- Identical reduced-basis digests against F0 and the independent reference on every row and field
  in Q's suite.
- No new nondeterminism: 3 repeated runs per row at 1 and 16 w give identical digests.
- Time, matrix-size, live-memory and cancellation budgets enforced with typed failures, at
  1 worker as well as many (#962).
- Size-limit fallback and typed refusals preserved.
- No performance obtained by disabling or loosening a budget, skipping certification where it was
  previously performed, or randomizing without an exact check.

### 12.2 Regression thresholds (Gate C and Q)

- **Wall.** On every substantive control row (≥ 300 ms) at each relevant worker count:
  - paired ratio vs F0 upper bound ≤ 1.05;
  - small controls ≤ 1.05 by the warm-call method.
- **RSS.** Peak RSS ≤ 1.25× F0 on every control. Any growth > 1.10× is explained in the PR.
- **Held-out.** No held-out row slower than F0 (upper bound ≤ 1.05).
- **Signature route.** No configuration is called production-safe while #961/#962 are open.

## 13. Experiment gates, budgets and stop rules

| Gate | Evidence | Pass |
|---|---|---|
| **A — attribution** | current measured bottleneck (G1/M1), predicted end-to-end gain on named rows (additive estimate), falsifiable hypothesis, file scope, line estimate | predicted gain ≥ 8% of the target row's wall, and the candidate is not in §4.3 |
| **B — bounded prototype** | isolated stage A/B + ≥ 1 substantive complete solve; digests; peak RSS | target-row paired wall ratio upper bound ≤ 0.95; digests equal; RSS ≤ 1.25× |
| **C — integration** | merged-shape PR vs its merge base on development + control rows at relevant workers (dev mode, one B1 job) | development-row gain holds (upper ≤ 0.97); §12.2 controls pass |
| **D — confirmation** | Q's held-out read + I's publication session | §8.4 |

- Thresholds are posted on the WP issue **before** each gate's measurement.
- **A failed gate stops the candidate.** One bounded corrective iteration is allowed, with a
  written hypothesis for the failure and ≤ 2 sessions; then stop.
- The held-out set is read once. No candidate is tuned after Gate D.
- Negative results are written up in the WP's research note and closed as findings, not left
  open.

| Package | Cap |
|---|---|
| M33-0 | 5 sessions; ≤ 500 net lines; no library behaviour change |
| B1 | 4 sessions; ≤ 1,500 net lines |
| B2 | 4 sessions; ≤ 800 net lines; ≤ 3 calibration sessions of ≤ 2 h |
| B3 | 3 sessions; ≤ 1,000 net lines |
| G1, M1 | 4 sessions each; ≤ 400 net lines instrumentation |
| G2, M2 | ≤ 2 candidates each; ≤ 1,500 net `src/` lines and ≤ 8 sessions per candidate |
| Q | 5 sessions; ≤ 1,000 net lines |
| I | 3 sessions; no library change |
| Machine | one timed campaign at a time on the reserved CCDs; reservations released at session end |

Exceeding a cap, adding a third candidate to a track, or reviving #940 is an owner decision
recorded on #965.

## 14. Public/private boundary and licensing

- Zeebra owns general algorithms, finite fields, Gröbner bases, performance tooling, public
  benchmarks, and correctness and safety testing.
- Every M33 instance is a public generic system: Katsura, Eco, Cyclic, Noonburg, seeded dense MQ.
- M33 needs no data, model or result from the private `mfaulk/cryptanalysis` repository. A
  request from it enters as an ordinary issue that states a generic requirement with a public
  reproducer, and joins M33 only by a decision recorded on #965.
- grobx and msolve are studied as references, run through their pinned provision scripts and
  instrumented only in local builds outside the crate.
- No GPL code is copied into Zeebra's MIT source. Algorithms are re-derived from papers and
  documented behaviour under
  [`external-provenance-policy.md`](research/external-provenance-policy.md).

## 15. Issue tracker and execution sequence

| WP | Issue | Labels | Priority | Native parent | Blocked by |
|---|---|---|---|---|---|
| tracker | [#965](https://github.com/mfaulk/zeebra/issues/965) | `M33`, `blocked` | High | — | children |
| M33-0 | [#966](https://github.com/mfaulk/zeebra/issues/966) | `M33` | High | #965 | Part 2 only: #942 |
| M33-B1 | [#967](https://github.com/mfaulk/zeebra/issues/967) | `M33` | High | #965 | — |
| M33-B2 | [#968](https://github.com/mfaulk/zeebra/issues/968) | `M33` | High | #965 | — |
| ↳ fixed clock | [#954](https://github.com/mfaulk/zeebra/issues/954) (reused) | `M33` | Medium | #968 | — |
| M33-B3 | [#969](https://github.com/mfaulk/zeebra/issues/969) | `M33` | Medium | #965 | — |
| M33-G1 | [#970](https://github.com/mfaulk/zeebra/issues/970) | `M33`, `blocked` | High | #965 | #966 |
| ↳ exact zero-skipping | [#955](https://github.com/mfaulk/zeebra/issues/955) (reused) | `M33` | Medium | #970 | — |
| M33-G2 | [#971](https://github.com/mfaulk/zeebra/issues/971) | `M33`, `blocked`, `performance` | Medium | #965 | #970 |
| M33-M1 | [#972](https://github.com/mfaulk/zeebra/issues/972) | `M33`, `blocked` | High | #965 | #966 |
| ↳ FL sweep clock | [#918](https://github.com/mfaulk/zeebra/issues/918) (reused) | `M33` | Medium | #972 | — |
| M33-M2 | [#973](https://github.com/mfaulk/zeebra/issues/973) | `M33`, `blocked`, `performance` | Medium | #965 | #972 |
| M33-Q | [#974](https://github.com/mfaulk/zeebra/issues/974) | `M33`, `blocked` | High | #965 | #971, #973, #962 |
| M33-I | [#975](https://github.com/mfaulk/zeebra/issues/975) | `M33`, `blocked` | High | #965 | all above |
| prerequisite | [#962](https://github.com/mfaulk/zeebra/issues/962) (M32 bug) | `M32`, `M33` | High | #938 | — |
| scoped | [#961](https://github.com/mfaulk/zeebra/issues/961) (M32 bug) | `M32`, `M33` | Medium | #938 | — |

- **Claimable at planning time:** #966 (Part 1), #967, #968, #969, #954, #918, #962.
- #955 is claimable as research. G1 decides whether it becomes a G2 candidate.
- Whoever posts a gate's passing evidence removes `blocked` from the dependent issue.

## 16. Integration report template (§17, written by M33-I)

- **17.0 Header.** F0/F2/F3 commits, dates, mode per session, reservation and clock state,
  attempt counts by outcome, comparand identities (source, version, executable SHA), job IDs,
  evidence path `research/m33-final/`.
- **17.1 Status.** One paragraph per tier. Then four verdicts kept apart:
  1. algorithmic work (products, zero reductions, basis sizes);
  2. stage speedups;
  3. complete process wall against F0;
  4. competitive position.
- **17.2 Competitive scoreboard.** Per row and worker count:
  - Zeebra F0, Zeebra F3 and competitor medians;
  - F3 ÷ competitor [95%];
  - verdict (win / loss / inconclusive / anomaly);
  - observed threads; RSS of both; guarantee/mode of both;
  - verification reference and time;
  - set (development, control, held-out).
- **17.3 Scaling curves.** Track M at 1/4/8/16 w for both solvers; Zeebra stage clocks per worker
  count.
- **17.4 Memory.** Peak RSS per row; F3 ÷ F0 and ÷ competitor.
- **17.5 Optimizations.** Each candidate's Gate A–D record, the predicted vs measured gain, and
  adopted or dropped.
- **17.6 Correctness and safety.** Digests, references, budget/cancellation suite, #961/#962
  disposition.
- **17.7 Infrastructure.** Campaigns run through B1, interruptions and resumes, contamination
  rates per mode, calibration results, manual steps removed.
- **17.8 Success criteria.** A table scoring every §8 criterion met / missed / not attempted, with
  evidence.
- **17.9 Remaining gaps.** Per competitor: equal-worker and BSC gaps, the guarantee difference,
  and the decomposition explaining what remains.
- **17.10 Negative, inconclusive and stopped results.** Every failed gate, stopped experiment,
  refusal, timeout, contaminated session and anomaly row.
- **17.11 Dispositions and follow-ups.** Every M33 issue's outcome; follow-ups filed on Project #7
  with Priority and linked to #965.
