# M31-S4: pre-solve dispatch and opt-in qualification of signature F4 (#905)

**Status:** complete, 2026-11-18. **Gate C passes** on every §6.2 criterion as written; the
signature path ships as the opt-in `grobner::f4_signature`. The library default does not change.
**Measured at:** `5bd0db63` (both arms from one `sig_f4_study` binary built from a `git archive` of
that commit, release, fat LTO, one codegen unit, x86-64-v3, `--features research-sigf4`; SHA-256 in
[`research/m31-sigf4-dispatch/binaries.sha256`](../../research/m31-sigf4-dispatch/binaries.sha256)).
Exploratory single runs in §2 and §5 are from the same binary or from `3ffc3bed`'s tree and are not
gating.
**Plan:** [`MILESTONE-COMPETITIVE-SIGNATURE-F4.md`](../MILESTONE-COMPETITIVE-SIGNATURE-F4.md) §4.1
(H4), §6.2, §7.5, §8.3, §8.5, §9, §10. **Entry evidence:** [`m31-sigf4-parallel.md`](m31-sigf4-parallel.md) §4.

## 1. What was built

- **`grobner::f4_signature(generators, order, &F4Options)`** and `f4_signature_reported`, which also
  returns a `SignatureDispatch` (route, features, dispatch time). Same output contract as
  `f4_with_options` under the same options. `signature_route` gives the decision without solving.
- **Typed refusals.** Lex, `Weighted` and `Block` return `SigF4Error::Unsupported` before either
  engine runs, on every route. Budgets are `SigF4Error::Budget(F4Error)` in the shipping F4's terms.
- **Fallback.** A signature-engine size refusal (`TooManyBasisElements`, `TooManyRows`,
  `TooManyColumns`, `TooManyLiveBytes`) reruns the shipping F4 with the remaining wall budget; the
  route reports `Shipping(Fallback(limit))`. Time budgets and certification are never fallen back.
- **Certification budget (#912).** The signature engine certifies on its workers through
  `certify_f4_output_within` when `max_certify_time` is set; a stop is
  `CertificationTimeBudgetExceeded`, never a rejection — the shipping path's #909 behaviour.
- **Gating.** No new feature. The engine is dependency-free, so it now compiles in every build
  behind the public entry point; `grobner::sigf4` (its options, statistics, replay and corpus) stays
  public only under `research-sigf4`. A non-research feature would hide the supported path from
  default CI and buy nothing, the reasoning `external-runners` already records in `Cargo.toml`.

## 2. The dispatch rule (H4)

Features, read in one pass over the generators' terms before any solve: variables that appear,
nonzero generators, least nonlinear degree, greatest degree. No instance name or digest.

| Condition, in order | Route |
|---|---|
| no nonlinear generator | shipping (`Linear`) |
| fewer than 6 variables appear | shipping (`Small`) |
| greatest degree − least nonlinear degree > 1 | shipping (`DegreeSpread`) |
| otherwise | signature engine, parallel cascade when more than one worker |

**First-batch features were not usable.** The plan admits features from within the first batch.
On five of the eight tuning rows that batch is the lone linear generator (one target, no pairs, no
rejections), so it carries no signal; the rule is pre-solve only.

**Why these two thresholds.** The rule is asymmetric: misrouting a favourable input to the shipping
F4 loses its saving, misrouting Cyclic-7 the other way cost 4.6× (#904). So the signature engine
gets only the region where every row measured favoured it. Exploratory serial single runs
(`3ffc3bed`, `ci-release`, signature design 1 ÷ shipping F4-1, GF(2³¹−1), none of them corpus or
held-out rows):

| Input | Degrees | Signature ÷ F4 | Signature basis / reduced |
|---|---|---:|---:|
| katsura-5, -6, -7, -8, -10 | 2 (and 1) | 0.34–0.50 | ≤ 1.24 |
| mq-random-6, mq-planted-10, mq-planted-wide-10 | 2 | 0.36–0.40 | ≤ 1.08 |
| cyclic-5 | 1..5 | 0.61 | 2.4 |
| cyclic-6 | 1..6 | 2.07 | 7.3 |
| cyclic-8 | 1..8 | 37.0 | 88.6 |

Spread degrees are where the signature basis outgrows the reduced one (Cyclic-7: 3,083 against 209,
#857), and every input with nonlinear degrees within one of each other ran faster serially. The
variable floor is the corpus small control: katsura-4 is process startup on every arm, and at 16
workers design 2's per-batch thread team cost it 8% (`m31-baseline.md` §3.1). Held-out rows were not
consulted for either threshold.

**Overhead.** Median in-process dispatch time 0.3–3.3 µs per row (§3's last column), at most 0.002%
of any row's wall; the routed controls' paired ratios sit at 0.99–1.01.

## 3. Gate C (plan §6.2)

Method: plan §10.4. n = 9 per arm, fresh process per child, arms rotated per repetition, CCD-aligned
`taskset` from CPU 8, `rss-guard` at 8 GiB, 180 s cap, CCDs 1–2 reserved with
`tools/bench-reserve.sh` and released at session end, under benchlock
([`campaign.py`](../../research/m31-sigf4-dispatch/campaign.py), records `*.jsonl.gz`,
[`tables.md`](../../research/m31-sigf4-dispatch/tables.md)). Arms: `f4` shipping F4 and `en` the
entry point, `--workers W`, same binary (plan §10.2). Ratios paired per repetition, 95% bootstrap of
the median (20,000 draws). Machine 1-minute load 0.8–9.3 outside the reservation. 324 of 324 timed
children and 13 of 13 certification children completed.

| Criterion | Value | Read |
|---|---|---|
| 1. Eco-12 / 2⁶⁴−353, 16 w: median ≤ 0.75, upper ≤ 0.80 | **0.712** [0.705, 0.715] | pass |
| 2. Katsura-11 / Goldilocks, 16 w: median ≤ 0.90, interval excludes 1.0 | **0.442** [0.438, 0.447] | pass |
| 3. katsura-4 / Goldilocks, 1 w and 16 w: upper ≤ 1.05 | 0.987 [0.961, 1.031]; 1.002 [0.995, 1.015] | pass |
| 3. katsura-4 / 2⁶⁴−353, 1 w and 16 w | 0.994 [0.983, 1.028]; 0.990 [0.974, 1.021] | pass |
| 3. noon-7 / Goldilocks, 1 w and 16 w | 0.490 [0.471, 0.493]; 0.569 [0.558, 0.579] | pass |
| 3. Cyclic-7 / Goldilocks, 1 w and 16 w | 1.007 [0.972, 1.032]; 0.990 [0.983, 1.012] | pass |
| 4. Peak RSS ≤ 1.25× shipping on every corpus row | worst 1.013 (katsura-4 / Goldilocks, 16 w) | pass |
| 5. Equality with shipping F4 | one basis digest per row across both arms and all repetitions, 13/13; equal to M31-0's digests on the 11 rows it ran | pass |
| 5. Independent certification | `certify_f4_output` on the entry point's output, every row, `checks_passed` and `is_complete`, 13/13 (Eco-12 66.9 s, MQ11 62.0 s at 16 workers) | pass |
| 6. Behaviour | typed `Unsupported` for Lex, `Weighted`, `Block` on every route; typed wall, matrix and certification-budget errors; wall cancellation between batches and in interreduction; #904's adverse-scheduling suite (1–16 workers, forced interleavings) unchanged and green | pass |
| 7. No default change | `f4`, `f4_with_options` and every solver untouched | pass |

§9.1 item 3 (⟨G⟩ ⊆ input) rests on equality with the shipping F4's reduced basis, whose digests
equal M31-0's on the rows that run independently checked there; MQ10's two rows are the exception,
since `m29_cost_model` records no comparable digest.

Reported rows at 16 workers (not scored by §6.2):

| Row | Route | Entry ÷ F4 [95%] | RSS ratio |
|---|---|---:|---:|
| Katsura-11 / 2⁶⁴−353 | signature | 0.450 [0.445, 0.455] | 0.763 |
| MQ11 / Goldilocks | signature | 0.441 [0.440, 0.445] | 0.938 |
| Cyclic-7 / 2⁶⁴−353 (1 w; 16 w) | shipping | 1.003; 1.004 | 1.00 |
| **MQ10 / GF(32003)** | signature | **1.611** [1.584, 1.617] | 0.651 |
| **MQ10 / GF(2³¹−1)** | signature | **1.745** [1.734, 1.776] | 0.815 |
| katsura-9 / 2⁶⁴−353 (held out) | signature | 0.576 [0.566, 0.581] | 0.908 |
| noon-8 / 2⁶⁴−353 (held out) | signature | 0.616 [0.612, 0.623] | 0.828 |

eco-14 is absent: M31-0 dropped it under §10.3 (shipping F4-16 stops at its live-nonzero limit).

## 4. Caps (plan §8.5)

One claim-lease session. Net lines: about 290 under `src/` excluding tests (the entry point, the
engine's order check and budgeted certification, the gating), 250 of tests, 57 in `sig_f4_study`,
plus the campaign scripts — against 1,500.

## 5. Known gap: MQ10 at 16 workers

The entry point routes MQ10 to the signature engine (degrees all 2, 10 variables) and loses 1.6–1.75×
there. It is not a dispatch overhead: exploratory single runs (`5bd0db63`, CPUs 8–23, GF(32003))
put the signature engine at 418 ms serially against shipping F4-1's 1,048 ms, but at 16 workers
shipping F4 drops to 200 ms while the entry point stays at 342 ms, of which the signature engine's
serial symbolic preprocessing is 188 ms. MQ11, the same family one size up, wins 0.44×. No pre-solve
feature in this rule separates MQ10 from katsura-9 and noon-8 (both favourable) without fitting a
threshold to MQ10, and §6.2 reports MQ10 rather than scoring it, so the rule was not changed after
the read. Parallel signature symbolic preprocessing (H3's first half) is the follow-up that would
close it (#927); a dispatch feature on the worker count against problem size is the cheaper alternative.
