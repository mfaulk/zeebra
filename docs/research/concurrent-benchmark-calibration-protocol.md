# Concurrent-benchmark calibration: preregistered protocol (#1106)

**Status:** preregistration, written before any deciding measurement. **The gates in §6 were
accepted by the owner on 2026-11-25**, after the pilot (§7.1), with two amendments: the A/A CI band
of the 16-worker cells is widened to ±4% (§6), and `m5` is dropped on every cell whose idle wall is
under 1.5 s (§4.2). They bind #1107 once this amendment merges. The sign-off package (§11) is on
#1106.

**Measured at:** not measured here — every figure is quoted from a cited source: #985 at binary
`31e334bd` (`research/m33-calibration/`), #848 at `faa015e6` (`research/bench-reserve/`), #841 at
`9d3e45a7`, #1033 at `00c9f29f` (`research/1033-dense-rebaseline/`) and M33-0 at `b3c15ff3`
(`research/m33-baseline/`). This document runs nothing.

**Parent:** #1103 (work package C1). **Blocks:** #1107 (C2). **Inputs from:** #1104 (CCD
reservation policy), #1105 (telemetry), #954 (clock mode). Written at `main` `bc45d7a9`,
2026-11-23.

## 0. Why this is written first

#1107 will decide which concurrent workloads a benchmark may tolerate, and for which measurement
classes. If the hypotheses, subjects, gates or stopping rules were chosen after the data, the policy
would be fitted to that data. Everything #1107 decides is therefore fixed here: what is measured,
on what, how many times, what counts as passing, and which data may be used to fit anything.

Two facts shape the design:

- **#985 is not held-out evidence.** It ran one session per condition at n = 9, on Eco-12 and MQ10
  only. Those subjects have been looked at, so here they are the **calibration** cohort. Nothing is
  judged on them.
- **A sleep cannot detect differential contention.** #985's only slow arm, `s5`, is the same binary
  plus a sleep. It shows a 5% difference stays *detectable* under load. It cannot show that two
  arms with different memory intensity keep their *ranking*. This protocol adds a memory-sensitive
  synthetic arm (`m5`, §4.2) and real pairs whose arms differ in memory traffic (§4.3–§4.4).

### Measurement classes

Classes as in #1103. #1107 fills in the decision table (§9) for each.

| Class | Decides | Evidence this protocol produces |
|---|---|---|
| 1. Correctness and resource safety | Output equivalence, timeouts, RSS ceilings | Digest agreement per attempt only. Never gated on contamination |
| 2. Development A/B (Zeebra ÷ Zeebra) | Whether a change is faster | H1, H2, H3 |
| 3. Cross-engine (Zeebra ÷ grobx or msolve) | Competitive ratios | H4 |
| 4. Publication absolute | Figures compared across days | H5. Strict `publication` mode stays available and unchanged whatever H5 shows |

## 1. Hypotheses

Every hypothesis is judged on the **held-out cohort** (§3.2) only, under each loaded workload W1–W6
against W0 from the same day. Gate values are in §6.

| | Statement | Falsified by |
|---|---|---|
| **H1** A/A | Under each workload, the A/A paired ratio on reserved CCDs meets the A/A gate | Any held-out cell × workload whose A/A median or CI is outside the gate, or whose loaded CI is wider than the allowed multiple of its idle width |
| **H2** A/B ranking | For pairs whose arms differ in memory intensity (the real pairs H-S16 and H-P1; `m5` is not on any held-out cell, §4.2), the loaded paired ratio stays within the A/B gate of the idle ratio, and its sign does not change | Any such pair × workload outside the gate, or whose loaded median is on the other side of 1.0 from its idle median |
| **H3** small effects | A true 2–5% effect detected idle (CI excludes 1) is still detected under load | Detection in fewer loaded sessions than the gate's fraction |
| **H4** cross-engine | Zeebra ÷ grobx at 1 worker and Zeebra ÷ msolve at 16 workers stay within the cross-engine gate of their idle ratio. Clock treatment per #954's state (§5.5) | Any cross-engine pair × workload outside the gate |
| **H5** absolute | An absolute wall under load stays within ±2% of idle | Any held-out cell × loaded workload whose median wall of arm `a` differs from idle by more than 2%. **Expected to fail** on #985 (Eco-12 1 w: 1.175x under STREAM, 1.088x under builds). Testing it settles whether any absolute figure may ever come from a concurrent session |
| **H6** telemetry sufficiency | The attempts whose #1105 shared-resource telemetry exceeds a limit `L` are exactly the attempts whose ratios move. `L` is fitted on the calibration cohort (§8.4) and judged once on the held-out cohort | Held-out recall or false-flag rate outside the H6 gate |

H1–H4 are judged per workload. A workload may pass for one measurement class and fail for another.
That is the point of §9's table, and a mixed result is a result, not a failure of the campaign.

## 2. Background workloads

Every workload:

- runs on the **unreserved CPUs only**, under `taskset -c "$REST"`, where `REST` is every logical
  CPU outside the job's reservation, siblings included (§5.3);
- starts only once the job holds its lock and its state is `running`, and is killed, by process
  group, when the job ends. This is the pattern of `research/m33-calibration/run.sh`;
- is logged in the session's `events.log` with its start and stop times, command line, `REST`, and
  the `uptime` load at each.

`$W` is the campaign's private directory, `/buildcache/cargo-target/zeebra-1107`. Never `$HOME`.
`$SRC` is a `git archive` of the frozen commit `C` (§5.1) under `$W`, used only as build-load input.

| Id | Workload | Command (run in a loop where shown, under `setsid taskset -c "$REST"`) |
|---|---|---|
| **W0** | idle | nothing of ours. Other agents' activity is recorded, not controlled |
| **W1** | light build | `cd $SRC; while :; do touch src/lib.rs; CARGO_TARGET_DIR=$W/load-w1 cargo build -q -j8 --tests; done` after one warm build |
| **W2** | heavy build (#985) | `cd $SRC; while :; do CARGO_TARGET_DIR=$W/load-w2 cargo clean -q; CARGO_TARGET_DIR=$W/load-w2 cargo build -q -j48 --tests; done` |
| **W3** | CI-like tests | `cd $SRC; while :; do CARGO_TARGET_DIR=$W/load-w3 cargo test -q -j16 --lib -- --test-threads=16; done` after one warm build. The real `system.slice` runners do whatever they do; their activity is recorded (#1105's `runner_workers_on_bench` and per-CCD load), not controlled |
| **W4-8**, **W4-16**, **W4-32** | DRAM bandwidth, three intensities | `$W/stream 8`, `$W/stream 16`, `$W/stream 32`, where `stream` is `research/m33-calibration/stream.c` built with `cc -O2 -pthread` |
| **W5** | mixed | W2 and W4-16 together |
| **W6** | I/O (optional) | `while :; do CARGO_TARGET_DIR=$W/load-w2 cargo clean -q; dd if=/dev/zero of=$W/io.bin bs=1M count=32768 oflag=direct status=none; rm -f $W/io.bin; done` |

W6 is optional. If it is dropped, the report says so and §9's I/O row reads "not calibrated".

All loaded workloads run as the same user in the default slice, as an agent's build would. None is
placed in `zbbench.slice`.

## 3. Subjects

Two cohorts, **disjoint by family and by scale**. Thresholds and limits may be fitted on the
calibration cohort only. The held-out cohort is judged once, with everything frozen.

### 3.1 Calibration cohort: #985's subjects

| Cell | Instance | Binary and engine | Workers | Idle wall (source) |
|---|---|---|---:|---|
| C-E1 | `wide64/eco-12` | `sig_f4_study --engine entry` | 1 | 2.55 s (#985) |
| C-M1 | `gf32003/mq-random-10` | `sig_f4_study --engine entry` | 1 | 0.46 s (#985) |
| C-M16 | `gf32003/mq-random-10` | `sig_f4_study --engine entry` | 16 | 0.24 s (#985) |
| C-P16 | `mq10-32003` | `m29_cost_model`, `--pair-multiples every` vs `distinct` | 16 | 0.30 s F4 call (#841) |

Families: Eco, random MQ. Scales: Eco n = 12, MQ n = 10.

### 3.2 Held-out cohort: chosen now, not changed later

| Cell | Instance | Binary and engine | Workers | Idle wall (source) | Why it is here |
|---|---|---|---:|---|---|
| H-K16 | `gf32003/katsura-11` | `sig_f4_study --engine entry` | 16 | 0.49 s (M33-0 Track M) | Katsura-11 at 16 workers |
| H-D16 | `gf31/mq-dense-15-s15` (`--generate`) | `sig_f4_study --engine entry` | 16 | 0.49 s (#1033 attribution) | the dense GF(31) MQ family of #945/#1068 |
| H-C1 | `wide64/cyclic-7` | `sig_f4_study --engine entry` | 1 | 0.61 s, `sig` arm (M33-0 Track G) | a wide-prime family #985 did not use |
| H-P1 | `katsura11-m31` | `m29_cost_model`, `--pair-multiples every` vs `distinct` | 1 | 9.3 s vs 7.5 s F4 call (#841) | the real large-effect pair (§4.4) |
| H-S16 | `cyclic7-wide64` (qualified in the pilot, §4.3) | `m29_cost_model`, `--pair-multiples every` vs `distinct` | 16 | 0.157 s `every` (pilot) | the real small-effect pair |
| X-G1 | `wide64/katsura-11` | `sig_f4_study --engine entry` vs `grobx-driver` 0.155.1 | 1 | 0.87 s vs 0.57 s (M33-0 Track G) | H4, Zeebra ÷ grobx at equal workers |
| X-M16 | `gf32003/katsura-11` | `sig_f4_study --engine entry` vs `msolve -t 16` | 16 | 0.49 s vs 0.68 s (M33-0 Track M) | H4, Zeebra ÷ msolve at 16 workers, small prime |

Families: Katsura, dense MQ, Cyclic. Scales: Katsura n = 11, dense MQ n = 15, Cyclic n = 7. None
is an Eco or a random-MQ row, and none has n = 10 or n = 12. The two cohorts are disjoint on both
axes. #1107's summarizer asserts this from the manifests and refuses to judge if it does not hold
(§8.6).

X-M16 reads as an msolve `anomaly` in M33-0 (msolve at 16 threads slower than at 8). It stays: H4
asks whether the ratio moves under load, not whether msolve scales, and an engine with a noisy
16-thread wall is exactly the case a cross-engine table meets.

## 4. A/B pairs

Every pair has a known idle effect, measured idle in the same session as the loaded data it is
compared with (W0 of the same day, §5.4).

### 4.1 `s5`: synthetic, sleep (insensitive to contention)

#985's arm unchanged: the A binary, then a sleep of 5% of its own measured wall
(`research/m33-calibration/run.sh`, the `slow5` wrapper). It is kept as the control that contention
should *not* move. Its fixed cost (a shell, `date` ×2, `awk`, `sleep`: about 10–25 ms) is why it
reads 1.06–1.09 on the sub-second cells. That is a known offset, not a defect.

### 4.2 `m5`: synthetic, memory (sensitive to contention by construction)

The A binary, then a **fixed amount of DRAM work**, tuned to cost 5% of A's wall idle. A sleep
costs the same time under any load. A fixed amount of memory traffic costs more time when another
process is using the bandwidth. So `m5` is the positive control for H2 and H6: if bandwidth load
moves anything, it moves `m5/a`.

**The sweep.** `research/concurrent-calibration/sweep.c` (written in #1107, specified here):

```text
sweep <threads> <passes>
```

- Allocates, per thread, three `double` arrays of 64 MiB each (192 MiB per thread, as `stream.c`),
  first-touches them, then runs exactly `passes` triad passes `a[i] = b[i] + 3.0 * c[i]` over them,
  and exits. The work is a fixed count, never a duration.
- `threads` is the arm's worker count. The threads inherit the attempt's CPU affinity, so they run
  on the bench CPUs and nowhere else.
- `a` is `volatile` so the stores are not elided, as in `stream.c`.

**The wrapper** has the same shape as `s5`'s, so the fixed shell overhead is common to both
synthetic arms:

```sh
#!/bin/sh
"$BIN" "$@"; rc=$?
"$SWEEP" "$THREADS" "$PASSES"
exit $rc
```

**Idle tuning, once per cell, in the pilot (§7.1), W0 only.**

1. Measure `t_A`, the median process wall of arm `a` over 9 idle repetitions.
2. Measure `t_1`, the median wall of `sweep <threads> 1` over 9 idle repetitions on the same CPUs,
   and `t_0`, the median of `sweep <threads> 0` (allocation and first touch only).
3. Set `passes = max(1, round((0.05 · t_A − t_0) / (t_1 − t_0)))`.
4. Validate: 9 idle rotated repetitions of `a`, `m5`. Accept if the median `m5/a` is in
   [1.04, 1.06]. Otherwise scale `passes` once by `0.05 / (median − 1)`, rounding, and validate
   again. If the second validation also fails, the cell's `m5` is reported as untuned and excluded
   from H2 and H6, and the report says so.
5. Record `threads`, `passes`, `t_A`, `t_0`, `t_1` and both validations per cell in the manifest's
   `context`, and in the sign-off package (§11).

If `t_0` alone exceeds `0.05 · t_A` (allocation too costly for a sub-second cell), halve the
per-thread arrays to 32 MiB, still beyond any one CCD's 32 MiB L3 once three arrays are counted,
and repeat from step 2. Record the size used.

**Amended after the pilot (owner, 2026-11-25): `m5` runs only on cells whose idle wall is at
least 1.5 s.** The pilot (`research/concurrent-calibration/pilot/`) found that on every sub-second
cell, allocation and first touch alone take longer than the 5% budget, even at 32 MiB. `t_0` was
58 ms for 1 thread and 256 ms for 16, against budgets of 12–23 ms, so `m5/a` read 1.20–2.12 and
could not be tuned. Smaller arrays would fit in L3 and stop being a bandwidth control. Of the cells
here, only C-E1 qualifies, tuned at 32 MiB and 13 passes and validated at 1.043. So `m5` is a
calibration-cohort control, used by H6's fit (§8.4). On the held-out cohort, H2's and H3's positive
control is the real small pair H-S16 (§4.3), and the large pair H-P1 (§4.4).

### 4.3 Real, small effect (2–5%, arms differ in memory traffic)

`F4Options::pair_multiples` (#841): `Distinct`, the default, seeds each repeated pair multiple once;
`Every` seeds both halves. `Distinct` drops forward-elimination rows, so the two arms differ in the
rows the forward pass streams through memory, not only in arithmetic. One binary,
`m29_cost_model`, runs both arms through `--pair-multiples every|distinct`, so the two arms share a
commit and a build.

Idle effects from #841 (`9d3e45a7`, paired median `distinct/every` on the F4 call, 16 workers):

| Target | Workers | `every` ms | `distinct` ms | Ratio | Forward ms `every` → `distinct` |
|---|---:|---:|---:|---:|---|
| MQ10 / 32003 | 16 | 302.8 | 291.0 | 0.963 | 96 → 88 |
| MQ10 / 2³¹−1 | 16 | 276.6 | 267.8 | 0.970 | 78 → 71 |
| Katsura-11 / 2³¹−1 | 16 | 1,636.9 | 1,489.0 | 0.910 | 555 → 443 |

These are F4-call ratios. Process wall adds the same fixed cost to both arms, so the process-wall
effect is somewhat smaller.

- **Calibration cohort:** C-P16 (`mq10-32003`, 16 workers), 3.7% idle on #841's data.
- **Held-out cohort:** the first of these candidates, in this order, whose **idle** process-wall
  effect in the pilot (9 rotated repetitions, W0) has a median `distinct/every` in [0.95, 0.98] and
  a 95% CI below 1.0:
  1. `cyclic7-wide64`, 16 workers;
  2. `katsura11-wide64`, 16 workers;
  3. `katsura11-m31`, 16 workers.

  Qualification looks only at the idle effect size, which H2 and H3 take as given. It never looks
  at loaded data, so it fits nothing that is later judged. The qualifying target becomes H-S16 and
  is recorded in the sign-off package.

  **Qualified in the pilot: H-S16 = `cyclic7-wide64`**, `distinct/every` 0.965 [0.953, 0.973] idle
  (`katsura11-wide64` 0.891 and `katsura11-m31` 0.895, both too large).

If none qualifies, the protocol does what #1106's stop condition says: H3's held-out evidence is
the synthetic `m5` and `s5` arms only, and the missing real small pair is a stated limitation that
#1110 must carry. MQ10 is not used as a held-out substitute: it is a calibration family.

### 4.4 Real, large effect (≥ 10%)

H-P1: `katsura11-m31` at 1 worker, `--pair-multiples every` vs `distinct`. #841 measured 0.803
[0.779, 0.811] on the F4 call (9,340 ms → 7,502 ms; forward 8,379 → 6,583 ms). This is #831's
gate row.

### 4.5 Arms per cell

| Cells | Arms (rotated each repetition) |
|---|---|
| C-E1 | `a`, `a2` (the same binary: A/A), `s5`, `m5` |
| C-M1, C-M16, H-K16, H-D16, H-C1 | `a`, `a2` (A/A), `s5`. No `m5`: idle wall under 1.5 s (§4.2) |
| C-P16, H-P1, H-S16 | `every`, `distinct`, `distinct2` (A/A on the default arm) |
| X-G1 | `entry`, `entry2` (A/A), `grobx155` |
| X-M16 | `entry`, `entry2` (A/A), `msolve` |

## 5. Design

### 5.1 Binaries

All Zeebra binaries are built once, at the commit `C` that is `main` when #1107 starts, from
`git archive C`, `--locked`, release, fat LTO, one CGU, `x86-64-v3`, `RUSTC_WRAPPER=""
CARGO_INCREMENTAL=0`, in `$W`:

| Binary | Recipe |
|---|---|
| `sig_f4_study` | `cargo build --release --locked --features research-sigf4 --example sig_f4_study` |
| `m29_cost_model` | `cargo build --release --locked --features external-runners --example m29_cost_model` |
| `grobx-driver` 0.155.1 | `research/m33-baseline/grobx-pin.sh`, `8005a2a1`. SHA-256 must equal `research/m33-baseline/pins.json` |
| `msolve` | as pinned in `research/m33-baseline/pins.json`. SHA-256 must equal the pin |
| `stream`, `sweep` | `cc -O2 -pthread` from `research/m33-calibration/stream.c` and `research/concurrent-calibration/sweep.c` at `C` |

`C` and the SHA-256 of every binary go into the sign-off package before the first deciding job.
A binary whose hash differs from the package is a different instrument, and its data does not
count.

Argument vectors, with `bench-job` placeholders:

```text
sig_f4_study   --field {field} --name {name} [--generate] --engine entry --workers {workers} --digest-only --wall-s 600
m29_cost_model --target {target} --workers {workers} --pair-multiples {every|distinct} --wall-s 600
grobx-driver   {inputs[grobx]}                   # request file as research/m33-baseline/campaign.py writes it
msolve         -f {inputs[ms]} -o /dev/stdout -t {workers} -g 2
```

### 5.2 Interleaving

As `bench-job`: every repetition runs every arm of a cell once, in an order rotated by one each
repetition (`interleave: rotate`). Cells run in manifest order within a repetition. One job per
(cohort, workload, session).

### 5.3 Placement and reservation

Worker placement follows the M29 contract: CPUs `8 … 8 + w − 1`, siblings idle.

| Workers | Reservation (#1104's policy; until it lands, the fallback) | `REST` for the load |
|---|---|---|
| 1 | 1 CCD: CCD 1, CPUs 8–15 and siblings 72–79 (fallback: CCDs 1–2) | `0-7,16-71,80-127` (fallback: `0-7,24-71,88-127`) |
| 16 | 2 CCDs: CCDs 1–2, CPUs 8–23 and siblings 72–87 | `0-7,24-71,88-127` |

A job mixing 1- and 16-worker cells reserves two CCDs and uses the 16-worker `REST`. Which policy
was in force is recorded per job. Data under the fallback and under #1104's policy are not pooled.

### 5.4 Sessions and order

- A **session** is one day's run of every workload, W0 first and again last (the drift check, as
  #848's A2), the loaded workloads in between in a randomized order:
  `python3 -c "import random; w=['W1','W2','W3','W4-8','W4-16','W4-32','W5','W6']; random.Random(YYYYMMDD).shuffle(w); print(w)"`
  with the session's date as the seed. The order is printed into `events.log` before the first
  job.
- Every (cohort, workload) condition is repeated in **at least 2 sessions on different days**.
- Loaded data is compared with the **W0 of the same session**. Idle and loaded data from different
  days are never paired.
- Both cohorts run in every session, calibration first. The held-out jobs' data are not opened
  until §8.4's limits are frozen (§8.5).

### 5.5 Clock

Whatever #954's state is when #1107 starts, every arm of every cell gets the same treatment, and
`tools/cpu-context.sh`'s clock mode is recorded per attempt:

- #954 landed and adopted: the fixed clock, at the frequency #954 set, for the whole campaign;
- otherwise: boost, recorded, the same for every arm (the M33 rule).

A campaign that changes clock mode partway restarts from the pilot.

### 5.6 Machine-time budget

Rough per-session cost at n = 15, from the idle walls in §3 and `bench-job`'s ~0.5 CPU-s snapshot
per attempt: about 5 minutes per workload for the calibration cohort, and about 13 minutes per
workload for the held-out cohort (H-P1 dominates at ~25 s per repetition). With W0 twice and eight
loaded workloads, a session is about 3 hours of reserved CCDs, two sessions about 6 hours.

**Corrected after the pilot.** That estimate understated the harness. The pilot measured 1.4 s
(1 worker) to 1.9 s (16 workers) of harness time per attempt beyond the timed wall. At n = 30
(§7.2), with `m5` only on C-E1 (§4.2), the estimate is about 49 minutes per workload (calibration
~15, held-out ~33), **about 8 hours of reserved CCDs per session and 16 hours over two
sessions**. #1107 splits a session across days only if every workload's W0 is still the same
day's (§5.4). #1107
schedules it around M34's campaigns (check `benchlock.log` and the M34 board first).

## 6. Gates (ACCEPTED 2026-11-25)

These are the starting values #1106 proposed, made precise, as the owner accepted them after the
pilot. The one change is the A/A CI band on 16-worker cells. At n = 30, the cap of §7.2, the
pilot predicts idle A/A half-widths of about ±2.8% (C-M16) and ±3.1% (C-P16). Against ±2.5%, those
cells would fail H1 idle, which §7.3 treats as an instrument failure. Raising n to 60 instead was
considered and declined: at the pilot's ~1.4–1.9 s of harness time per attempt, it adds about
6.5 h of reserved CCDs (§5.6). The cost of the wider band is that a 16-worker A/A cannot rule out a
4% instrument error, so 16-worker conclusions are weaker than 1-worker ones, and the report says
so. The sign-off is recorded on #1106.

| Gate | Accepted value | Unit judged |
|---|---|---|
| **A/A** (H1) | Median within 1.000 ± 0.010. 95% CI within [0.975, 1.025] on 1-worker cells and **[0.960, 1.040] on 16-worker cells**. Loaded CI width ≤ 1.5× the idle CI width of the same cell and session | held-out cell × workload × session |
| **A/B** (H2) | \|loaded median − idle median\| ≤ 1.5 percentage points, with the 95% CI of that difference within ±2.5 pp. Sign unchanged: loaded and idle medians on the same side of 1.0 | real pair (H-S16, H-P1) × workload × session |
| **Small-effect detection** (H3) | Of the loaded sessions in which the 2–5% pair was detected idle (CI excludes 1), ≥ 90% also detect it loaded | real small pair H-S16, per workload, pooled over sessions |
| **Cross-engine** (H4) | \|loaded ratio ÷ idle ratio − 1\| ≤ 0.03 | X-G1, X-M16 × workload × session |
| **Absolute** (H5) | \|loaded median wall ÷ idle median wall − 1\| ≤ 0.02, arm `a` (or `entry`, or `distinct`) | held-out cell × workload × session |
| **Telemetry** (H6) | On the held-out cohort, the frozen limit flags ≥ 90% of moved pairs (recall), and ≤ 20% of the pairs it flags are unmoved (false-flag rate) | held-out cohort, per workload class |

The H6 values (recall 0.9, false-flag 0.2) are this protocol's addition; #1106 named H6 but no
number. They are proposed on the same terms as the rest.

**How a gate becomes a decision.** A workload passes a measurement class when every gate that class
depends on passes for every held-out unit under that workload: class 2 needs H1, H2 and H3; class 3
needs H1 and H4; class 4 needs H5. One failing unit fails the workload for that class. There is no
majority rule and no re-run of a failing unit.

The CI of the A/B difference (H2) is a percentile bootstrap over repetitions of
`median(loaded ratios) − median(idle ratios)`, the two sides resampled independently, 20,000 draws,
seeded by the cell key, by the same `random.Random(seed)` and percentile indices as
`tools/bench_stats.py`.

## 7. Sample sizes and stopping

### 7.1 Pilot (exploratory, decides nothing)

- Labeled `pilot` in every manifest's `context` and stored under
  `research/concurrent-calibration/pilot/`. Its attempts are kept and published, and **excluded
  from every decision**.
- Budget: at most 1 hour of reserved-CCD time.
- Runs: W0 and W4-32 on the calibration cohort at n = 9; the `m5` idle tuning (§4.2) on every
  cell that has an `m5` arm; the §4.3 qualification of the held-out small pair, W0 only.
- It looks at no held-out cell under load.

### 7.2 Fixing n

From the pilot's W0 and W4-32 calibration data, for each cell, let `h` be the larger of the two A/A
95% CI half-widths at n₀ = 9. Then

```text
n = min(30, max(15, ceil(n₀ · (h / 0.010)²)))
```

so the predicted A/A half-width is at most 1%. The largest `n` over the calibration cells is used
for every cell of both cohorts. If the cap of 30 binds, the report says so and the A/A gate is
judged at n = 30 regardless. n is recorded in the sign-off package before the first deciding job.

**Fixed by the pilot: n = 30 for every cell. The cap binds on all four calibration cells.** The
larger half-widths at n₀ = 9 were C-E1 2.6%, C-M1 2.4%, C-M16 5.1% and C-P16 5.8%, all idle. The
16-worker cells' predicted half-widths at n = 30 are why §6 widens their A/A band.

### 7.3 Stopping

- **No optional stopping.** Every deciding job runs its fixed n. M33's predeclared extension rule
  (`EXTENSION_N` in `tools/bench_stats.py`) does **not** apply here.
- **Instrument stop.** If the **idle** A/A of any calibration or held-out cell fails the A/A gate in
  a session, that session stops and its data is retained and labeled `instrument-failure`. Two
  instrument failures stop the whole campaign. That is an instrument problem, not a load result, and
  the report says so rather than judging anything.
- **Censoring.** An attempt that times out is censored at the wall limit and kept. A cell with any
  censored attempt is reported as censored and is not judged.
- **Digests.** An attempt whose basis digest differs from its cell's reference is a correctness
  finding. It stops the campaign and is filed as a bug.

## 8. Analysis

### 8.1 Statistics

- Paired ratios per repetition with `tools/bench_stats.paired_ratios`; the median and its 95%
  percentile-bootstrap CI with `paired_ratio(…, seed=<cell key>)`, 20,000 draws. Zeebra ÷ Zeebra
  only.
- Cross-engine ratios with `independent_ratio`, as M33 did, each side resampled independently.
- Absolute walls: the median of arm `a` per cell and session.

### 8.2 Three rule sets, all reported

Each result is computed three times:

| Rule set | Attempts used |
|---|---|
| **raw** (primary) | every complete attempt with the reference digest |
| **dev** | `raw` less those `tools/bench_contamination.py`'s dev rules flag, at the verdict version current at `C` |
| **publication** | `raw` less those its publication rules flag |

plus the **candidate** rule set fitted in §8.4. The decision table (§9) names which rule set an
`allowed` entry relies on. The contamination and rejection rate under each rule set is reported per
workload.

### 8.3 Also reported

- **Rank changes:** for every A/B and cross-engine pair, whether its order changes between idle and
  loaded.
- **Within-session drift:** the ratio of the median over the first third of repetitions to the
  median over the last third, per cell and workload.
- **Development throughput:** the wall of a fixed reference build — `cargo build --release --tests
  -j48` of `$SRC` from clean, in `$W/ref-build`, on `REST` — three times with no benchmark running
  and three times while a calibration job runs under W0. Reported as the median ratio. This is the
  cost of the reservation to the rest of the machine.

### 8.4 Fitting the telemetry limit (H6), calibration cohort only

A pair (one repetition of one arm pair in one cell) is **moved** when its loaded paired ratio lies
outside the 2.5–97.5 percentile range of that cell's W0 paired ratios in the same session.

For each #1105 signal `s` in the list below, a pair is flagged when `s` of either attempt exceeds
`L_s`. `L_s` is the threshold that maximizes Youden's J (recall − false-positive rate) for flagging
moved pairs on the calibration cohort, all workloads pooled; ties go to the lower threshold. The
final rule is the single signal with the largest J, or the OR of the two best signals if that
raises J by at least 0.05. Signals, by #1105's field names where they exist:

- per-CPU foreign time on the bench CPUs and on their siblings;
- `compilers_on_bench` and `runner_workers_on_bench`;
- the per-CCD load vector (largest element and the element of any CCD that shares the bench CCDs'
  memory controller);
- PSI `memory` and `cpu`, `some` and `full`, as deltas over the attempt, system-wide and for
  `zbbench.slice`;
- major faults and the `/proc/vmstat` reclaim and swap deltas;
- memory bandwidth (resctrl MBM or uncore events) where #1105 reports it available. A signal that
  is unavailable on any attempt is not eligible: unavailable never passes a check that requires it.

The fitted rule, its `L` values and J, go into `research/concurrent-calibration/limits.json`. Its
SHA-256 is posted on #1106 or #1107 **before** any held-out data is opened.

### 8.5 Judging the held-out cohort

Held-out journals are collected but not summarized until `limits.json` is frozen. Then the held-out
cohort is summarized once, with H1–H6 judged against §6 under every rule set. Any later change to
`limits.json` or to the summarizer is a new analysis, reported apart, and cannot replace the first.

### 8.6 Script interfaces (written in #1107)

```text
research/concurrent-calibration/run.sh <cohort> <workload> <session-label>
    one bench-job job plus its background load, as research/m33-calibration/run.sh
research/concurrent-calibration/extract.py --job <job dir> --out <records.jsonl.gz>
    one record per attempt: cell, arm, repetition, wall, digest, status, verdicts, #1105 telemetry
research/concurrent-calibration/fit_limits.py --records <calibration records…> --out limits.json
    §8.4; refuses held-out records
research/concurrent-calibration/summarize.py --records <records…> --limits limits.json --out tables.md
    §8.1–§8.3 and §8.5; asserts cohort disjointness (§3) and refuses a limits.json whose hash differs
    from the one posted
```

## 9. Decision table (template; #1107 fills it in)

One entry per workload class and measurement class: `allowed`, `allowed under rule set <R>` (§8.2,
including the fitted telemetry limit), or `quiet machine only`. Class 4 is `quiet machine only`
unless H5 passes, which #985 makes unlikely.

| Workload class | 1. Correctness | 2. Dev A/B | 3. Cross-engine | 4. Publication absolute |
|---|---|---|---|---|
| W0 idle | allowed | | | |
| W1 light build | allowed | | | |
| W2 heavy build | allowed | | | |
| W3 CI-like tests | allowed | | | |
| W4 DRAM bandwidth (8 / 16 / 32) | allowed | | | |
| W5 mixed | allowed | | | |
| W6 I/O | allowed | | | |

Class 1 is `allowed` everywhere by construction: correctness and resource-safety tests are never
gated on contamination (#1103).

## 10. Retention

- Every attempt is kept: contaminated, censored, timed-out, instrument-failure and pilot attempts
  included, with its journal and `cpu-context.sh` snapshots, under `research/concurrent-calibration/`.
- Negative results are published. A workload that fails a class is a finding, and the report names
  it.
- Each record carries the binary SHA-256s, `C`, the reservation policy, the clock mode, the session
  label and the workload.

## 11. Sign-off package

Before #1107's first deciding job, a comment on #1106 records, verbatim:

1. the accepted gate values (§6), as the owner states them;
2. `C`, and the SHA-256 of every binary in §5.1;
3. the `m5` tuning per cell (§4.2) and the qualified held-out small pair, or that none qualified
   (§4.3);
4. n (§7.2);
5. the reservation policy in force (§5.3) and the clock mode (§5.5).

Items 2–5 come from the pilot and the build. Only item 1 needs the owner. Until item 1 is posted,
#1107 stays `blocked`.

**Posted on #1106, 2026-11-25:** items 2–5 from the pilot (`C` = `5451e9f8`), and item 1, the
owner's acceptance of §6 with the two amendments above.

## 12. What this protocol does not do

- It runs nothing deciding. That is #1107.
- It implements no telemetry (#1105) and no new mode (#1108). It names the #1105 signals it will
  use.
- It does not change strict `publication` mode, existing verdict versions, or any default.
