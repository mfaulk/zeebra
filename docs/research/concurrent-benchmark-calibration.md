# Concurrent-benchmark calibration: results (#1107)

**Status:** final. The preregistered verdict is **no-go for #1108**. The owner chose on 2026-11-26
to publish it unchanged, with §5's control as a separate finding, and filed the follow-up under §7.

**Measured at:** `C` = `5451e9f853c8f24bafed6875218a175de441e3f0` for every Zeebra binary, on the
§5.3 fallback reservation (CCDs 1–2, bench `8-23,72-87`), boost clock (#954 open). The harness is
`research/concurrent-calibration/` with `tools/bench-job`'s `arms[].instances` (`93f96542`), tagged
`measured/1107-concurrent-calibration`. Sessions s1-20261125 (16:45–00:51) and s2-20261126
(08:00–16:08). The limits are `limits.json` SHA-256 `283ba430…41f4`, posted on #1107 before any
held-out record was summarized. Every table is `research/concurrent-calibration/tables.md`.

This runs [the protocol](concurrent-benchmark-calibration-protocol.md) as signed on 2026-11-25. The
owner decided two budget points the same day: the budget counts reservation wall-hours, and W6
(I/O) is dropped. Nothing else departs from the protocol.

## 1. What ran

- Two sessions, each W0, then the seven loaded workloads in the seed's order, then W0. Both
  cohorts ran in each slot, with n = 30 per cell: 36 jobs and 18,360 attempts.
- **No §7.3 stop.** Every attempt's basis digest matched `references.json`, and no attempt was
  censored.
- **Idle A/A passed at all four W0s.**
- **The `m5` positive control works.** Under W4-32 it shifted by +0.034 [+0.022, +0.044] in s1 and
  by +0.031 [+0.024, +0.036] in s2.
- **One harness-bug stop**, at 17:00 on s1. The m29 A/A was paired against the effect arm; it was
  fixed in `1420417d`, with a test. Recomputed, it passes. It is recorded in
  `data/harness-bug-stops.json` and not counted toward §7.3.
- **Two measured caveats**:
  - **W2 is lighter than its name.** A clean `cargo build -j48 --tests` of this crate is mostly one
    `rustc` at about 2 CPUs, with a load average of 4–8. W2's row speaks for "a Zeebra rebuild", not
    for a 48-job multi-crate build.
  - **Throughput (§8.3).** A clean reference build beside a calibration job takes 1.023× its wall
    alone: 2057 s against 2014 s, median of 3 each.

## 2. Decision table (§9, held-out cohort, as preregistered)

| Workload | Correctness | Dev A/B (H1–H3) | Cross-engine (H1, H4) | Publication absolute (H5) |
|---|---|---|---|---|
| W0 | allowed | allowed | reference | reference |
| W1–W5 (all seven) | allowed | quiet machine only | quiet machine only | quiet machine only |
| W6 | allowed | not calibrated (dropped) | not calibrated | not calibrated |

**Go/no-go for #1108: no-go.** No loaded workload passes dev A/B on the held-out data under any
rule set.

## 3. Hypotheses, held-out cohort, raw

| H | Result | Units |
|---|---|---|
| H1 A/A under load | **fails** in every loaded workload. 30 of the 32 failing units fail only the "loaded CI width ≤ 1.5× idle" clause. One median falls outside 1 ± 0.010 (W4-32 H-P1, 0.9900), and one CI is outside the band (W1 X-G1) | 32 of 98 fail |
| H2 A/B preserved | **passes everywhere**. The largest \|Δmedian\| from idle is 0.009, and no rank changed in any session | 70 of 70 pass |
| H3 small real effect | **passes everywhere**. The ≈4% H-S16 effect is detected loaded in every idle-detected session | 7 of 7 |
| H4 cross-engine ratio | fails under W4-16, W4-32 and W5: bandwidth pressure moves Zeebra and grobx/msolve differently, by up to +4.1% (+0.0412) | 9 of 28 fail |
| H5 absolute | fails under every workload; W4-16, W4-32 and W5 fail in nearly every cell, as §2 of the protocol expected | 63 of 98 fail |
| H6 frozen limit | **fails everywhere**. `vmstat_majfault > 2`, the best single signal on calibration (Youden J = 0.29), reaches recall 0.92 only under W1, and does so by flagging most pairs (false-flag 0.69). Elsewhere recall is ≤ 0.46 | 0 of 7 |

The `dev` and `publication` rule sets do not rescue anything:

- **`dev`** rejects about 46% of idle W0 attempts. Nearly every rejection is "bench clock … off the
  session median". Under boost, a 1-worker cell leaves 15 bench cores idle and clocked down. This
  is #954's problem, and it is measured here.
- **`publication`** rejects 47% of idle attempts and 99.9–100% of loaded ones.

### Correction made while summarizing

The first summary marked H5 "allowed under rule set publication" for W4-8 and W4-32. That verdict
rested on the one cell per workload that kept any samples. A cell the rule set had emptied produced
no unit, so it could not fail. `abs_gate` now fails on fewer than two samples per side, matching
H1's "too few pairs" (`test_absolute_gate_fails_without_samples`). The table above is after the fix.

## 4. Drift

Within-session A/A drift (first third ÷ last third) ranges from 0.959 to 1.032. No session changed
an A/B rank.

## 5. Finding: H1's width clause does not separate load from idle

The clause compares a loaded A/A CI's width with the width of the session's *opening* W0. The same
test was applied to the *closing* W0 against the opening W0, idle against idle. It fails in 4 of the
14 held-out cells (H-C1, H-D16 and X-G1 in s1; H-S16 in s2) and in 6 of 22 cells overall, about
29%. Loaded cells fail it in 30 of 98, about 31%.

A 95% bootstrap CI's width from n = 30 is itself noisy: idle widths here range from 0.0031 to
0.0188 for the same cell. A 1.5× bar between two such estimates fails about a quarter to a third of
the time when nothing changed. In this campaign, the binding criterion of the go/no-go measures
mostly that noise, not load.

Descriptively, and not a verdict: with that clause removed, the remaining dev A/B failures are W1
(X-G1's CI) and W4-32 (H-P1's median at the band edge). W2, W3, W4-8, W4-16 and W5 would pass
H1–H3 on these data.

## 6. What this means

- **#1108 stays gated.** By the preregistered rule, no workload qualifies for concurrent dev A/B. The
  measurements underneath are favorable: H2 and H3 held in every unit, and A/B effects kept their
  size, sign and rank under every load. That is the question #1108 actually depends on.
- **Absolute figures need a quiet machine** (H5), and so do **cross-engine ratios** under
  memory-bandwidth load (H4). Both match #985.
- **The contamination signals do not identify moved pairs** (H6). A future limit needs a signal
  closer to the bench CCDs' memory traffic than the system-wide counters #1105 collects.
- **#954 matters for `dev`'s clock rule.** On boost, half the idle data is rejected for clock
  spread alone.
- **The 5% → 2% question.** A ≈4% real effect stayed detectable under every load, so detecting
  effects of 2–5% concurrently is supported. The required A/A band is the open part.

## 7. Follow-up

The follow-up issue preregisters a replacement for H1's width clause that is calibrated against the
idle-vs-idle spread, and decides #1108 on fresh sessions under it. This campaign's records are
retained so that its criterion can be checked for sense on them, but a criterion chosen after seeing
these data does not decide on them. That follow-up is #1180; its draft amendment and the check are
in [aa-width-criterion-preregistration.md](aa-width-criterion-preregistration.md).

## 8. Data

`research/concurrent-calibration/data/`:

- `s*/records-*.jsonl.gz`: one record per attempt, with verdicts and signals.
- `s*/events.log`: each session's event log.
- `journals/*.jsonl.gz` and `journals/*.header.json`: the bench-job journals without stdout blobs;
  the digests are in the records.
- `harness-bug-stops.json`.

Reproduce the summary:

```bash
python3 -I research/concurrent-calibration/summarize.py \
    --records research/concurrent-calibration/data/s*/records-*.jsonl.gz \
    --limits research/concurrent-calibration/limits.json \
    --limits-sha 283ba430c2ee8a98546937fd2b700b4d34921dd0531e6e681305873a8cad41f4 \
    --throughput research/concurrent-calibration/throughput.json --out research/concurrent-calibration/tables.md
```
