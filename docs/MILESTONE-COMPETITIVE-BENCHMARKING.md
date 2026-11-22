# M33 — Competitive F4 Performance and Reproducible Benchmarking

**Status:** integration report written, 2026-11-22 (§17, M33-I #975). Minimum met; T-G and T-M
missed (T-M not confirmed at Gate D, owner decision 16). §§1–15 are the plan, fixed before
measurement; §17 is the report, written from §16's template.
**Predecessor:** M32 — Adaptive F4 ([`MILESTONE-ADAPTIVE-F4.md`](MILESTONE-ADAPTIVE-F4.md);
tracker #938, **open**; final report #942, **open**, draft PR #960).
**Planning base:** `main` at `dfd984c0`.
**Measured at:** §17: F3 = F2 = `db181c51` and F0 `31e334bd` (built from `9d6f16e4`), sessions of
2026-11-22 (`research/m33-final/`). §§3–4: `8715c8ed`, `7b25a1ee`, `f8ec0b4c`, `2f661626` (quoted; nothing new). Every figure in §§3–4 is quoted from M31's final cohort at
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

## 17. Integration report (M33-I, #975)

### 17.0 Header

| | |
|---|---|
| **F0** | `31e334bd` (tag `measured/966-f0`), built from `git archive 9d6f16e4` (`src/`, `Cargo.toml`, `Cargo.lock` identical to F0). `sig_f4_study` SHA-256 `f8c844ee…`. M33-0's build of the same tree was `d00a6baf…`: the build directory is embedded in the binary (#1021) |
| **F2** | `db181c51` (tag `measured/974-f2`), Q's qualified revision |
| **F3** | **= F2 = `db181c51`**. `git log db181c51..c579aead --numstat -- src/grobner src/linalg src/fields src/poly` is empty, so there is one report, not two. `sig_f4_study` SHA-256 `beecc346…` |
| **Build** | `--features research-sigf4`, release, fat LTO, one codegen unit, x86-64-v3, rustc 1.99.1, `RUSTC_WRAPPER=""`, `CARGO_INCREMENTAL=0` |
| **Comparands** (#966 pins, `research/m33-baseline/pins.json`) | grobx 0.155.1 `8005a2a1`, driver `fdd6aeec…` (raw randomized; certified on Eco-12); groebner-rs driver `c3e1d630`, `c1eb0b04…`; msolve 0.11.0 release tarball, `557470de…` |
| **Mode** | Publication (§11.2), every job: exclusive benchlock, CCDs 1–2 reserved, children on CPUs 8–23 with siblings idle. No compiler, no runner and load1 < 4 at the start of each job and judged per attempt. Clock: boost, recorded and the same for every arm (#954 is not qualified). Clock rule per arm (owner decision 1) |
| **Sessions** | 2 of the 3 allowed, both valid. **Track G**, 2026-11-22 15:51–17:13Z: jobs `92e26e267f3d` (n = 9), `7fa0250e1309` (top-up, n = 5) and `d5db6121722d` (grobx certified). **Track M**, 17:13–18:26Z: jobs `ea52bc970e59` (n = 9) and `b5a15591d188` (top-up, n = 5) |
| **Attempts** | 2,913. All `ok`: no failure, timeout, cap or cancellation. 279 contaminated, all by the per-arm clock rule (65/792, 40/440, 112/1,080 and 62/600; 8–10% per job). Plus one **refused** grobx certified attempt (`output-bytes`, below) |
| **Evidence** | [`research/m33-final/`](../research/m33-final/README.md): records, journals, references, census and logs. [`tables.md`](../research/m33-final/tables.md) holds every table, regenerated by `summarize.py` |

### 17.1 Status

**Minimum: met.** M-1 to M-5 all hold (17.8). The baseline was frozen at F0 and both gaps were
re-measured (#991). Both decompositions are published (#992, #993). Each track has candidates
through Gate B, or a Gate A stop record. Many campaigns ran through B1 beside other agents'
builds. This report carries every negative result.

**Target: T-G missed. T-M missed (not confirmed at Gate D, owner decision 16).** The rest of Target is met.
- **T-G.** No Track G development row wins. The closest is Katsura-11 / 2⁶⁴−353 at **1.195**.
- **T-M.** Both Katsura-11 development rows win again at 8 workers: **0.452** on GF(2³¹−1) and
  **0.536** on GF(32003). Gate D requires every held-out row of the track at that count to read
  ≤ the development ratio + 0.15, and held-out mq-random-10-s1 reads 1.689 against 0.602, so the
  win is not confirmed (17.8).
- **T-B, T-Q and T-R: met.**

**Stretch: S-4 and S-5 met; S-1, S-2 and S-3 missed.** S-2's only candidate, Katsura-11 /
GF(2³¹−1) at 8 w (upper 0.453), is the win Gate D does not confirm.

The four verdicts, kept apart:

1. **Algorithmic work.** Unchanged by construction. Every basis is bit-identical, and the
   adopted changes (#994, #1001) change data layout and the interreduction route, not which
   products are computed. The work counts are #992's and #993's.
2. **Stage speedups**, from the signature route at 1 w, F3 against F0:
   - Eco-12: symbolic 448 → 209 ms and interreduction 273 → 90 ms;
   - Katsura-11: symbolic 156 → 68 ms and interreduction 120 → 43 ms;
   - elimination does not change.
3. **Complete process wall against F0.** F3 ÷ F0 is below 1 in 66 of 73 paired cells:
   - structured wide rows at 1 w: 0.71–0.85;
   - Katsura at small primes, 4–16 w: 0.64–0.69;
   - MQ at 4–16 w: flat (0.99–1.01).

   The largest upper bound on a substantive row is 1.029 (MQ10 / GF(32003), 4 w).
4. **Competitive position.**
   - **Track G:** Zeebra still loses every equal-worker row to grobx raw. The gap narrowed from
     1.52–1.73× to 1.20–1.48× on the development rows.
   - **Track M:** Zeebra wins Katsura at non-anomalous counts and loses MQ10 at 4–8 w by
     1.9–2.8×.

### 17.2 Competitive scoreboard

Process wall, median ms. Ratio = F3 ÷ competitor [95%, independent bootstrap, 20,000 draws].
Pooled n is 14 per cell (9 + 5) less contaminated attempts. "−digest" removes Zeebra's in-process
digest (grobx and msolve build or write their bases inside their walls). Full rows are in
`tables.md` (F0 ÷ competitor, F3 ÷ F0, every control).

**Track G, equal workers.** Zeebra's signature route at 1 w (deterministic) against grobx 0.155.1
raw at 1 w (randomized, uncertified). The verification reference is groebner-rs at 1 w.

| Row | Set | grobx | F0 | F3 | **F3 ÷ grobx** | −digest | Verdict | F3 ÷ F0 |
|---|---|---:|---:|---:|---:|---:|---|---:|
| Eco-12 / 2⁶⁴−353 | dev (primary) | 1,618.6 | 2,453.0 | 1,994.7 | **1.232 [1.220, 1.258]** | 1.177 | loss | 0.812 |
| Katsura-11 / 2⁶⁴−353 | dev | 553.9 | 850.5 | 662.0 | **1.195 [1.169, 1.219]** | 1.043 | loss | 0.778 |
| MQ11 / Goldilocks | dev | 2,907.6 | 5,042.7 | 4,310.2 | **1.482 [1.469, 1.492]** | 1.392 | loss | 0.853 |
| Katsura-12 / 2⁶⁴−353 | held-out | 3,759.1 | 4,826.4 | 4,049.4 | **1.077 [1.075, 1.087]** | 0.985 | loss | 0.839 |
| mq-random-10-s1 / 2⁶⁴−353 | held-out | 1,710.0 | 5,570.0 | 4,018.2 | **2.350 [2.319, 2.368]** | 2.323 | loss | 0.722 |

Controls: every one is a loss, from 1.216 (Katsura-11 / Goldilocks) to 4.521 (Cyclic-7). The
exception is Katsura-4, at 10 ms under the 300 ms floor: 1.114 [0.996, 1.189], inconclusive.

**Track G, best-supported configuration.** Zeebra at 16 w against grobx at 1 w. Kept separate;
it never scores, and grobx computes on one thread whatever it is asked (#966):
- development rows: Eco-12 0.721, Katsura-11 0.659, MQ11 0.444;
- held-out rows: Katsura-12 0.408, mq-random-10-s1 0.518;
- Cyclic-7, Noon-7/8, Katsura-9 and Katsura-4 still lose.

**Track G, guarantee references.**
- **groebner-rs 1 w (verified).** F3 is faster on every substantive row but Cyclic-7 (2.43×) and
  mq-random-10-s1 (2.67×). Eco-12 reads 0.672.
- **grobx certified, Eco-12, 1 w.** One attempt, 281.4 s and 10.6 GiB, with its digest equal to
  the reference. Then the job stopped `refused: output-bytes`: the driver's 1.7 GB reply
  exceeded the journal's 1 GiB budget, so n = 1 of 9 (#1020). F3 ÷ certified = 0.007.

**Track M, equal workers.** Zeebra's default dispatch (exact, deterministic) against msolve 0.11.0
(exact, deterministic), at 1/4/8/16 w. *anom* marks a count where msolve's median is more than
1.10× its own best in this session.

| Row | Set | w | msolve | F0 | F3 | **F3 ÷ msolve** | anom | Verdict |
|---|---|---:|---:|---:|---:|---:|---|---|
| Katsura-11 / GF(2³¹−1) | dev (primary) | 4 | 749.8 | 525.5 | 356.1 | 0.475 [0.469, 0.483] | no | inconclusive (n: msolve 4 clean of 14) |
| | | **8** | 711.0 | 493.3 | 321.3 | **0.452 [0.449, 0.453]** | no | **win** (M33-0: 0.691) |
| | | 1 / 16 | 1,561.6 / 2,624.0 | | 585.5 / 340.0 | 0.375 / 0.130 | yes | anomaly |
| Katsura-11 / GF(32003) | dev | **8** | 582.4 | 485.6 | 312.5 | **0.536 [0.535, 0.539]** | no | **win** (M33-0: 0.840) |
| | | 1 / 4 / 16 | | | | 0.422 / 0.514 / 0.480 | yes | anomaly |
| MQ10 / GF(2³¹−1) | dev | 4 | 175.0 | 336.0 | 335.5 | 1.917 [1.881, 1.935] | no | loss |
| | | 8 | 467.6 | 236.5 | 235.8 | 0.504 [0.503, 0.506] | yes | anomaly |
| | | 1 / 16 | | | | 1.333 / 0.687 | yes | loss / inconclusive (n 8) |
| MQ10 / GF(32003) | dev | 4 / 8 | 134.6 / 117.3 | | 377.7 / 262.3 | 2.806 / 2.236 | no | loss |
| | | 1 / 16 | | | | 1.456 / 1.001 | yes | loss / inconclusive (n 8) |
| mq-random-10-s1 / GF(2³¹−1) | held-out | 1 / 4 / 8 | 966 / 972 / 551 | | 3,835 / 1,372 / 932 | 3.968 / 1.411 / **1.689** | yes / yes / no | loss |
| | | 16 | 2,303.5 | | 745.1 | 0.323 | yes | anomaly |
| Katsura-12 / GF(32003) | held-out | 1 / 4 / 8 | | | | 0.366 / 0.417 / **0.453** | yes | anomaly (8 w: msolve 1.105× its best) |
| | | 16 | 2,925.2 | 2,166.2 | 1,403.4 | 0.480 [0.476, 0.484] | no | **win** |

Controls:
- **Cyclic-7:** loss at 1–8 w (1.7–2.8×).
- **Noon-7 and Eco-11:** faster at 4–8 w, but their intervals miss the precision rule, so
  inconclusive (0.49–0.72).
- **16 w:** every control count is anomalous.
- **Katsura-4:** small, inconclusive.

Zeebra's 4- and 8-worker MQ10 medians sit at 230–380 ms. msolve's sit at 117–175 ms, under §5.2's
300 ms floor. So MQ10 at 4–8 w is "small" by the plan's admission rule. It is scored as a loss
because its lower bound exceeds 1, and the small-row rule only stops a win.

**Verification.** All 2,913 attempts' `m33-basis-v1` digests equal the row's independent
reference: Singular std/redSB below 2³¹, groebner-rs at 1 w on the wide fields. The references
were re-run once, off-bench, before the sessions, and all 21 agree with M33-0's. Verification
time is reported apart from every ratio:
- groebner-rs: 0.0–14.0 s;
- Singular: 0.0–524.7 s (Katsura-12 / GF(32003)).

**Observed threads** (one census attempt per arm and cell; `threads-*.jsonl`):
- msolve uses exactly its `-t`;
- grobx and groebner-rs use 1–2;
- Zeebra's entry reports 16 concurrent threads where the signature route's parallel cascade runs.
  It reports fewer where the per-phase teams start and stop between samples, as #991 found.

### 17.3 Scaling (Track M)

| Row | Solver | 1 w | 4 w | 8 w | 16 w | 4→16 |
|---|---|---:|---:|---:|---:|---:|
| Katsura-11 / GF(2³¹−1) | F0 | 731.0 | 525.5 | 493.3 | 503.5 | 1.04× |
| | F3 | 585.5 | 356.1 | 321.3 | 340.0 | **1.05×** |
| | msolve | 1,561.6 | 749.8 | 711.0 | 2,624.0 | 0.29× |
| MQ10 / GF(2³¹−1) | F3 | 337.0 | 335.5 | 235.8 | 212.6 | 1.58× |
| | msolve | 252.7 | 175.0 | 467.6 | 309.2 | 0.57× |

**S-3 is missed.** F3's 4→16 speedup on the primary is 1.05× against F0's 1.04×, a 1% gain where
15% is needed.

The adopted changes cut the primary's wall by a third at every count (F3 ÷ F0 0.65–0.69 at
4–16 w). Its curve stays flat beyond 4 w, because the serial share #993 measured is still there:
at 8 w the entry call is 231 ms of the 321 ms wall. msolve is non-monotone on three rows: MQ10 /
GF(2³¹−1) at 8 w, and 16 w on every row except MQ10 / GF(32003). The stage clocks per worker
count are in `tables.md`.

### 17.4 Memory

| Row | F3 peak RSS | F3 ÷ F0 | F3 ÷ competitor |
|---|---:|---:|---:|
| Eco-12 / 2⁶⁴−353, sig 1 w | 142 MiB | 0.842 | 3.94 (grobx 36 MiB) |
| Katsura-11 / 2⁶⁴−353, sig 1 w | 95 MiB | 0.829 | 1.72 |
| MQ11 / Goldilocks, sig 1 w | 257 MiB | 0.707 | 2.85 |
| Katsura-12 / 2⁶⁴−353, sig 1 w | 342 MiB | 0.836 | 2.99 |
| mq-random-10-s1 / 2⁶⁴−353, sig 1 w | 245 MiB | **1.037** | 4.31 |
| Katsura-11 / GF(2³¹−1), entry 8 w | 89 MiB | 0.813 | 1.94 (msolve ≤ 46 MiB) |
| MQ10 / GF(2³¹−1), entry 1–16 w | 46 MiB | 1.000 | 1.00 |

- **F3 ÷ F0:** ≤ 1.04 on every row, and 0.71–0.85 on the structured ones.
- **Competitor figures** are the guarded child tree's maximum, an upper bound (#990). A 46 MiB
  reading is that floor, not the solver's own peak.
- **grobx certified** on Eco-12 peaked at 10.6 GiB.

### 17.5 Optimizations

| Candidate | Track | Gate A (predicted) | Gate B | Gate C | Here (F3 ÷ F0, publication) | Outcome |
|---|---|---|---|---|---|---|
| G2-1 run-wide monomial table (#994) | G | Eco-12 −10.1% | 0.906 [0.898, 0.915]; stage falsifier missed (0.466 > 0.45); owner decision 4 | 17 of 18 cells; MQ11 at 1 w 0.993 [0.977, 1.007]; owner decision 9 | combined with G2-2 below | **adopted** `2f8253f3`; no MQ11 gain claimed |
| G2-2 interreduction in column space (#1001) | G | Katsura-11 −14.7% | 0.890 [0.873, 0.911]; stage falsifier missed (0.368 > 0.30); owner decision 10 | 18 of 18 cells | Eco-12 0.812, Katsura-11 0.778, MQ11 0.853 (both changes) | **adopted** `db181c51` |
| K-IR signature-route interreduction on workers (#973) | M | Katsura-11 / GF(2³¹−1) 8 w ≥ 8% needed | — | — | — | **stopped at Gate A**: 30.3% parallelizable < 35% |
| W fewest-terms reducer + FL order (#997) | M | MQ10 / GF(2³¹−1) 4 w ≈ 8.9% | — | — | — | **deferred** out of M33 (owner decision 5) |

Predicted against measured:
- G1 predicted the two G candidates together at about 1.32× grobx on Eco-12, short of T-G.
  Measured here: **1.232**.
- M1 predicted T-M missed on MQ10. Here MQ10 is a loss at 4–8 w.
- The Katsura-11 / GF(2³¹−1) win widened from 0.691 to **0.452**. That came from G2's
  signature-route changes, which the entry point takes on that row, not from any Track M
  candidate.

### 17.6 Correctness and safety

Q (#974) passed at F2 = F3 under owner decisions 11–14, and Gate D under decision 15. The record
is [`m33-qualification.md`](research/m33-qualification.md):

| Suite | Result |
|---|---|
| Safety | 4/4 `m33_safety`, 1/1 `m33_thread_cap`, 9/9 `cascade_tests` |
| Correctness | 71 of 71 rows (2 by decision 13) |
| Regression | 56 of 56 cells (3 by decision 14) |

- **This campaign:** every digest equals its reference (17.2). No attempt failed, timed out or hit
  a budget.
- **#962:** fixed by #986.
- **#961:** mitigated, not fixed. #986 routes graded-lex to F4, and #961 stays open as the engine
  defect.
- **#1002**, the team-teardown race: open, outside M33.
- Per §12.2, no signature-route configuration is called production-safe while #961 is open.

### 17.7 Infrastructure

- **B1 campaigns.** M33 ran 58 `bench-job` jobs across #966–#975 (53 before this issue, 5 here).
- **Interruption and resume (T-B).** Track M's main job was SIGKILLed mid-attempt at
  17:18:10Z: attempt `ea52bc970e59:113`, msolve on Katsura-12 at 4 w. `status` read `interrupted`.
  `bench-job resume` continued from index 113. The finished job holds 1,080 attempts with no
  duplicate attempt id or cell, so no successful attempt was repeated. Logs are in
  `research/m33-final/logs/`.
- **Contamination** in publication mode here: 8.2–10.4% per job, all clock-rule flags, and foreign
  load ≤ the rule everywhere. For comparison:
  - dev mode under the per-arm rule: 8 of 9 re-judged sessions valid (#998);
  - Q's Gate D read: void at 22%.
- **Cells short of n.** Clock-rule flags concentrate on a few cells, so 15 cells stayed short of 9
  clean attempts even after the top-ups. Two of them are Track M rows that could score: Katsura-11
  / GF(2³¹−1) at 4 w (msolve 4 clean of 14) and MQ10 at 16 w (anomalous anyway).
- **Manual steps.** M32 needed `run.sh`, `--start-rep` and a copied `summarize.py`. M33 goes from
  `campaign.py manifest` to `bench-job submit/run`, `extract`, `summarize.py` and `board`. One
  hand-written file remains: `sessions.json`, which names the sessions of record.
- **Scoreboard.** `bench-job scoreboard` could not be used as is (#1019), so the 209 board rows
  were written by `campaign.py board`. `cargo run --release --example competitive -- --write`
  regenerates `COMPETITIVE.md` from `history.json`.
- **Calibration** results are #985's and #998's.

### 17.8 Success criteria

| Criterion | Verdict | Evidence |
|---|---|---|
| M-1 | **met** | F0 frozen; one-session re-measure per track (#991; [`m33-baseline.md`](research/m33-baseline.md)) |
| M-2 | **met** | G1 (#992) and M1 (#993): stage clocks, work counters, per-product cost |
| M-3 | **met** | Track G: G2-1 and G2-2 through Gate B (and C). Track M: K-IR's Gate A stop record (#995) |
| M-4 | **met** | M33-0's jobs ran under the CCD 1–2 reservation beside builds at load 1–150 (cpu-context in every attempt) |
| M-5 | **met** | This section; every attempt retained in `research/m33-final/` and the WP directories; negatives in 17.10 |
| **T-G** | **missed** | No development row wins. Best: Katsura-11 1.195 [1.169, 1.219]; Eco-12 1.232 [1.220, 1.258] |
| **T-M** | **missed (not confirmed at Gate D, owner decision 16)** | Katsura family: the development row wins again at 8 w, 0.452 [0.449, 0.453] on GF(2³¹−1) and 0.536 [0.535, 0.539] on GF(32003), msolve non-anomalous; held-out Katsura-12 / GF(32003) reads 0.453, with msolve at 1.105× its own best. Gate D bar = dev ratio + 0.15 (0.602, 0.686), and held-out mq-random-10-s1 / GF(2³¹−1) reads 1.689 at 8 w, outside it. A per-family reading was considered and rejected by decision 16 |
| T-B | **met** | 58 B1 jobs; `ea52bc970e59` interrupted and resumed with no repeated attempt |
| T-Q | **met** | Q passed for #994 and #1001, with #962 fixed (decisions 11–14) |
| T-R | **met** | Q's regression and Gate D reads (decisions 14, 15). Here, F3 ÷ F0's largest upper bound on a substantive row is 1.029, and RSS ≤ 1.04× |
| S-1 | **missed** | No Track G win; Track M wins are one family (Katsura) |
| S-2 | **missed** | The only row with upper ≤ 0.833, Katsura-11 / GF(2³¹−1) 8 w (0.453), is not confirmed at Gate D (decision 16) |
| S-3 | **missed** | 4→16 speedup on the primary: F3 1.05×, F0 1.04× (+1% against +15%) |
| S-4 | **met** | Publication-mode rows from retained records: `campaign.py board --append`, then `competitive --write` |
| S-5 | **met** | 17.7: from manifest to tables with no hand edits, except the sessions-of-record list |

### 17.9 Remaining gaps

**grobx, Track G.**
- **Equal workers:** 1.20–1.48× on the development rows. Katsura-12 is 1.077, and 0.985 without
  Zeebra's digest.
- **Best-supported configuration:** Zeebra 16 w is ahead on the structured rows (0.41–0.72) and
  behind on Cyclic-7 and Noon.
- **Guarantees:** grobx raw is randomized and uncertified. Certified, it is 140× slower on Eco-12.
- **Decomposition** (#992 against F3's stages): Eco-12 is still about 375 ms short. F3 has removed
  most of the symbolic (−239 ms) and interreduction (−183 ms) shares G1 attributed. What remains
  is bookkeeping (233 ms), the digest (89 ms) and in-call glue. Elimination is at parity with
  grobx. On MQ11 the gap is still elimination, which grobx avoids with randomized zero tests
  (#955).

**msolve, Track M.**
- **MQ10 at 4–8 w:** 1.9–2.8×. The cause is elimination work: 1.9× msolve's products, and a higher
  per-product cost at GF(32003) (#993). The candidate is deferred (#997).
- **Katsura at 4–16 w:** Zeebra wins by work count (0.07× msolve's products, #993). Its own curve
  is flat from 4 w (17.3).
- **Guarantees:** both solvers are exact and deterministic.

### 17.10 Negative, inconclusive and stopped results

- **T-G, T-M, S-1, S-2 and S-3 missed** (above). T-M's Katsura-11 wins repeat but are not confirmed at Gate D (decision 16). HG2 was falsified as stated, and HM1 falsified (#992, #993).
- **Stopped or deferred:**
  - K-IR stopped at Gate A (#995).
  - W deferred (#997).
  - Gate A stage falsifiers were missed by G2-1 (0.466) and G2-2 (0.368). The owner ruled Gate B
    governs.
  - G2-1's MQ11 Gate C cell failed (0.993 [0.977, 1.007]). No MQ11 gain is claimed (decision 9).
- **Void sessions:**
  - all four M33-0 sessions under the per-cell clock rule;
  - G1's session;
  - M1's `k` and `fl` sessions;
  - Q's Gate D read (22%; decision 15);
  - three of Q's top-up jobs.

  Under the per-arm rule (#998), 8 of the 9 pre-Q sessions are valid. Neither session here is
  void.
- **Here:**
  - 279 contaminated attempts, retained and excluded;
  - 15 cells short of 9 clean attempts (17.7);
  - one refused grobx certified attempt (#1020);
  - inconclusive rows: Katsura-4 on both tracks, Noon-7 and Eco-11 at 4–8 w, and Katsura-11 /
    GF(2³¹−1) at 4 w (n short).
- **Anomaly rows** (a Zeebra ratio below 1 at a count where msolve is anomalous; none scores T-M):
  - MQ10 / GF(2³¹−1) at 8 w (0.504);
  - Katsura-11 at 1 and 16 w on both fields, and at 4 w on GF(32003);
  - Katsura-12 / GF(32003) at 1–8 w;
  - mq-random-10-s1 at 16 w;
  - Noon-7 at 1 w, Eco-11 at 1 w, and Katsura-4 at 16 w.
- **Not a result:** Katsura-12 / 2⁶⁴−353 reads 0.985 [0.981, 0.994] without the digest. The
  predeclared statistic includes the digest, and the row is a loss.

### 17.11 Dispositions and follow-ups

| Issue | Disposition |
|---|---|
| #966 M33-0, #967 B1, #969 B3, #970 G1, #972 M1, #918 | closed, delivered |
| #971 G2 | closed; both candidates adopted (#994, #1001) |
| #973 M2 | closed; K-IR stopped at Gate A, W deferred to #997 |
| #974 Q | closed; passed under decisions 11–15 |
| #996 per-arm clock rule | closed (#998) |
| #962 | closed, fixed by #986 |
| #975 M33-I | this report (#1018) |
| #968 B2 | open (still claimed); its deliverables are merged (#981, #983, #985); left for its holder to close |
| #954 fixed clock | open; not qualified, so publication ran at boost |
| #961 graded-lex signature route | open as the engine defect; mitigated by routing (#986) |
| #955 exact zero-skipping | open; the MQ11 elimination gap (17.9) |
| #978, #987, #990, #997, #1002 | open follow-ups |
| #965 tracker | left open for the owner; T-M scored by decision 16 |
| **New:** #1019 (Medium) | bench-job scoreboard: rows never pair, ignore per-arm workers and carry no invariants |
| **New:** #1020 (Low) | grobx certified reply exceeds the journal's output budget |
| **New:** #1021 (Low) | archive builds of one commit are not bit-reproducible across directories |
