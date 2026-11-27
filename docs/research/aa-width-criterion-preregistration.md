# A/A width criterion: preregistered amendment (#1180)

**Status:** DRAFT for owner sign-off. Nothing here binds until the owner signs §6 on #1180. No
deciding session has run, and none may run before the sign-off.

**Measured at:** `5451e9f853c8f24bafed6875218a175de441e3f0`, the `C` of every binary in #1107. No
new measurement was taken. Every figure is recomputed from #1107's retained records by
`research/1180-aa-width/analyze.py`, and the full tables are in `research/1180-aa-width/tables.md`.

**Amends:** H1's row of §6 in
[the #1106 protocol](concurrent-benchmark-calibration-protocol.md): the clause "Loaded CI width ≤
1.5× the idle CI width of the same cell and session", and nothing else. **Follows:**
[#1107's results](concurrent-benchmark-calibration.md) §5. **Gates:** #1108.

## 0. Why

#1107's preregistered verdict was no-go for #1108. Of the 32 failing held-out H1 units, 30 failed
only the width clause. That clause does not separate load from idle. Judged as if it were a loaded
block, the closing W0 fails it against the opening W0 in 4 of 14 held-out cells and in 6 of 22 cells
overall. `test_analyze.py` reproduces both counts from the committed records.

Most of the weakness is in how units combine. A workload passes dev A/B only if all 14 of its
held-out H1 units pass: 7 cells × 2 sessions. On resampled idle data, the clause fails 17.7% of
units, so a workload with no load at all fails it **93% of the time**. In 70% of simulated
campaigns, every one of the seven workloads fails, a false no-go (§2.2). A criterion that is judged
14 times per workload needs a per-unit false-failure rate near 0.4%, not near 20%.

Two facts about the statistic make the clause noisy:

- The width of a percentile-bootstrap CI of a median at n = 30 depends on a few order statistics
  near the centre. Idle widths for the same cell ranged from 0.0031 to 0.0188.
- The clause compares one such width with another. The reference is a single n = 30 block, so a
  narrow opening W0 fails every loaded block of that session in that cell. That is what happened
  to s1 H-D16 (opening width 0.0043, failed under 6 of 7 workloads) and s2 H-P1 (0.0031, failed
  under 5 of 7).

## 1. What changes and what does not

| | |
|---|---|
| **Replaced** | H1's width clause, by §3's scale test |
| **Unchanged** | H1's median clause (1 ± 0.010) and CI band (±0.025 at 1 worker, ±0.040 at 16). H2, H3 and their gates. The decision rule of §6: a workload passes class 2 only if every H1, H2 and H3 unit passes, with no majority rule and no re-run |
| **Out of scope** (#1180) | H4, H5, H6 and `dev`'s clock rule (#954). Their #1107 failures stand. H6 is not refitted (§4) |

## 2. Candidates and their idle-vs-idle false-failure rates

### 2.1 Candidates

| | Criterion: a loaded A/A unit fails when |
|---|---|
| **A0** | its CI width > 1.5 × the opening W0's width (#1107 as run) |
| **A1** | its CI width > 1.5 × the pooled-W0 width: both W0s pooled (60 ratios) and resampled at the loaded n |
| **A2** | its CI width > 1.5 × the wider of the two W0 widths |
| **B** | a one-sided permutation test finds it more dispersed than both W0s pooled, at p ≤ α = 1 − 0.95^(1/14) = 0.00366 (§3) |
| **C** | its CI half-width > 0.010 (§7.2's design target: a 2% effect is then `precise` in `tools/bench_stats.py`'s sense) |

The issue names three kinds of candidates. A1 is "pool both W0s", A2 is "the two W0s per session",
B is "a permutation over reps against the idle distribution", and C is "bound the half-width
absolutely".

### 2.2 How the rates were checked

**Observed.** Each session's closing W0 is judged as if it were a loaded block, against the opening
W0 alone. These are the only real idle-vs-idle comparisons in the records, 22 A/A cell-sessions. A1
and A2 use both W0s as the reference, which leaves no idle block to judge, so they have no observed
row.

**Resampled.** For each cell and session, both W0 A/A series are pooled (60 ratios) and treated as
one idle distribution. Each of 200 trials draws an opening W0, a closing W0 and seven "loaded" blocks
of n = 30 from it, with replacement, and judges every candidate on each block. No block differs from
idle, so every failure is a false failure. A workload fails when any of its 14 held-out units fails.
A trial is a false no-go when all seven workloads fail. Run settings: 2,000 bootstrap draws and
1,000 permutations.

### 2.3 Results

| Candidate | Observed, held-out (14) | Observed, all A/A (22) | Resampled, per unit | Resampled, per workload | Resampled, false no-go |
|---|---|---|---|---|---|
| A0 1.5 × opening W0 | 4 | 6 | 0.177 | **0.931** | **0.700** |
| A1 1.5 × pooled W0s | — | — | 0.125 | 0.849 | 0.455 |
| A2 1.5 × wider W0 | — | — | 0.064 | 0.609 | 0.090 |
| **B scale test, α = 0.00366** | **0** | **0** | **0.002** | **0.031** | **0.000** |
| C half-width ≤ 0.010 | 0 | 0 | 0.029 | 0.350 | 0.000 |

Supporting figures, all in `tables.md`:

- **B's calibration.** At p ≤ 0.05, B flags 0 of 22 observed A/A comparisons and 2 of 42 idle pair
  series, A/B pairs included. 42 × 0.05 = 2.1 are expected.
- **No fixed multiple works.** For a width-ratio rule to fail one unit in 273, the multiple would
  have to be 3.49 against the opening W0, or 2.67 against the pooled W0s. A 2.7× bar on an A/A
  width no longer says anything useful about load.
- **C depends steeply on the bound.** Its per-workload false-failure rate is 0.350 at 0.010, 0.061 at
  0.0125, 0.010 at 0.015 and 0 at 0.020. A bound that is tight enough to matter fails idle cells
  often. A bound loose enough to pass idle is mostly implied by the CI band already.
- **Power, synthetic.** Each loaded block's log-dispersion was multiplied by g, centre unchanged.
  This uses no loaded data from #1107. Fraction of held-out units failed:

| Candidate | g = 1.5 | g = 2 | g = 3 |
|---|---|---|---|
| A0 | 0.506 | 0.758 | 0.940 |
| B | 0.117 | 0.422 | 0.837 |
| C | 0.237 | 0.491 | 0.767 |

  B pays for its low false-failure rate with power per unit. Over a workload's 14 units, though, a
  load that widens every cell by 1.5× is caught with probability 1 − (1 − 0.117)^14 ≈ 0.82, and one
  that widens every cell by 2× with probability ≈ 0.9995. A0's power comes at a false-failure rate
  of 93% per workload. A0 cannot tell a 1.5× widening from no load (0.506 against 0.177 per unit).

The observed A0 rate (6 of 22, 0.27) is above the resampled one (0.18). That gap is within binomial
noise at 22 units (P(≥ 6) ≈ 0.18 at p = 0.177), and the resampled null ignores within-session drift.
§5 lists the limits of both checks.

**What was not done.** No candidate was applied to #1107's loaded blocks. Doing so would let the
outcome choose the criterion, and #1107's data cannot decide (#1180). The choice in §3 rests on
§2.3's idle rates and synthetic power alone.

## 3. The amendment (proposed for sign-off)

H1's width clause is replaced by:

> **Loaded A/A dispersion.** The loaded A/A series is not more dispersed than the same cell's idle
> A/A series in the same session, by a one-sided permutation test at per-unit α = 1 − 0.95^(1/u),
> where u is the number of held-out H1 units per workload (u = 14: 7 cells × 2 sessions, so
> α = 0.003657).

Precisely, per held-out cell × loaded workload × session:

1. **Idle reference.** Both of the session's W0 A/A series for the cell, pooled: opening and
   closing, 60 ratios at n = 30. A session without its closing W0 does not decide (§4).
2. **Centring.** Take the log of every ratio. Centre each series, loaded and pooled idle, on its own
   median. A location shift is H1's median clause's to judge, not this one's.
3. **Statistic.** T = median |centred loaded| ÷ median |centred idle|: a ratio of median absolute
   deviations.
4. **Permutation.** Pool the 90 centred values. 20,000 times, shuffle them with
   `random.Random(bench_stats._seed(f'{session} {workload} {slot} {cell} {num}/{den} scale'))`,
   split them into 30 and 60, and recompute T\*. p = (1 + #{T\* ≥ T}) / 20,001.
5. **Verdict.** The unit fails this clause when p ≤ α. The reason string gives T and p.

Its idle-vs-idle false-failure rate is **bounded by α per unit and by 5% per workload** when idle
repetitions are exchangeable. On #1107's records it is 0.002 per unit and 0.031 per workload,
resampled, and 0 of 22 observed (§2.3).

**Owner's choice at sign-off.** C may be added as a further clause if the owner wants an absolute
precision floor under load, at a half-width bound the owner names. Its stated idle-vs-idle rate per
workload is then added to B's: 0.010 at 0.015, or 0.061 at 0.0125. This draft does not add it. The
CI band already bounds the half-width at about 0.025 (1 worker) and 0.040 (16 workers). H3 tests
detectability of a real ≈4% effect directly.

**Implementation, before the first deciding session.** `calib.aa_gate` gains the clause in place of
the width comparison. `summarize.py` passes both W0 series as the idle reference. Tests:
- the clause passes when the loaded and idle series are the same values;
- it fails when the loaded series is a 4× widening;
- p never reaches 0;
- the seed string is as in step 4.

The code and the tests merge, and the summarizer's SHA is posted on #1180, before the first deciding
job.

## 4. Deciding sessions

- **Two fresh sessions on different days**, about 7.5 h each. #1107's s1 ran 8.1 h and s2 8.1 h, so
  budget 8 h. The cells, arms, n = 30, interleaving, order rule (seed = the session's date), stops
  (§7.3) and rule sets are #1107's, through the same harness at tag
  `measured/1107-concurrent-calibration`. Binaries are the signed `C` (`prepare.py` refuses others).
- **The same reservation and clock as #1107:** the §5.3 fallback, CCDs 1–2, with the boost clock
  recorded. If #1104's policy or #954's fixed clock has landed by then, the owner states at sign-off
  which one applies. A change from #1107 is allowed, because these sessions decide alone and are
  never pooled with #1107's. The change must be stated before the first job.
- **Workloads:** W1–W5, as in #1107. W6 stays dropped.
- **Only the new sessions' held-out cohort decides.** #1107's records are not pooled, re-judged or
  used to tune anything further.
- **H6 and the `candidate` rule set:** #1107's frozen `limits.json` (SHA-256 `283ba430…41f4`) is
  reused unchanged, not refitted. H6 is out of scope (#1180), and the decision table's `candidate`
  column is reported, not relied on.
- **A session that loses its closing W0**, for example to a stop, does not decide. A replacement
  session runs.
- **The verdict** is §9's go/no-go for #1108, with H1 as amended. The results doc states it. If it is
  go, the doc names the workloads allowed for class 2.

## 5. Limits of this check

- **Resampling assumes exchangeable idle repetitions.** It draws with replacement from 60 values and
  ignores drift between the opening and closing W0. Within-session drift in #1107 was 0.959–1.032.
- **Little real data.** The observed check has 22 A/A comparisons. It compares 30 against 30, while
  the amendment compares 30 against 60, so the observed check uses a smaller reference than the
  amendment will.
- **The other clauses' rates are not estimated.** Only the width clause's false-failure rate is
  estimated here. H1's median and band clauses keep their own idle rate. No idle A/A unit failed them
  in #1107 (11 cells × 4 W0s).
- **Power is synthetic.** It is measured against a scale-only widening and says nothing about other
  effects of load, which the median clause, the band, H2 and H3 judge.

## 6. Sign-off package (for the owner, on #1180)

1. Accept, amend or reject §3's clause. If C is added, state its bound.
2. The per-workload false-failure budget for the clause. 5% is proposed, which fixes α at u = 14.
3. The reservation and clock for the deciding sessions (§4).
4. That #1107's `limits.json` is reused unchanged (§4).

Until items 1–4 are posted on #1180, and §3's implementation has merged, no deciding session runs.
