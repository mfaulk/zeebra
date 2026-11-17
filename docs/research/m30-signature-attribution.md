# M30-S1: grobx signature F4 on, off and without handover (#716)

**Measured at:** controller `c143b178` (grobx primary cohort) and `dd951927` (MQ11 extension); Zeebra
census binary built from `e03284d6` (`examples/m29_cost_model.rs` with two added targets); production `src/` identical to the M30 freeze `4f5784c5` (this branch changes no
`src/` file). grobx pin `1854835d`; stock driver build `9267861f…` (the same build identity as
#855's driver); research driver SHA-256 `f2cb4ce6…`, overlay identity `d1171bef…`.
**Host:** Threadripper PRO 5995WX, one solver worker pinned to CPU 8 inside the reserved CCD 1
(`tools/bench-reserve.sh run`), load 1.2–1.5 across the primary cohort and 1.3–2.5 across the extension.
**Evidence:** [`research/m30-signature/`](../../research/m30-signature/README.md).
**Plan:** [`MILESTONE-SIGNATURE-SYMBOLIC-F4.md`](../MILESTONE-SIGNATURE-SYMBOLIC-F4.md) §6.1.

## 1. Verdict

**Gate A1 passes, on Eco-12 only, and only in the exact-reduction comparison.**

| Instance | Signature arm | Against | Work, off ÷ on | Wall, on ÷ off [95%] | RSS, on ÷ off | Output | A1 |
|---|---|---|---:|---:|---:|---|---|
| MQ11 / Goldilocks | default (never hands over) | signatures off | **1.69×** | 0.569 [0.568, 0.570] | 1.01 | identical | **fails** (work < 2×) |
| Eco-12 / 2⁶⁴−353 | default (hands over at round 2) | signatures off | 1.00× | 1.001 [0.991, 1.005] | 1.01 | identical | fails |
| Eco-12 / 2⁶⁴−353 | no handover | signatures off | 0.91× | 1.009 [0.999, 1.019] | 1.04 | identical | fails |
| Eco-12 / 2⁶⁴−353 | no handover, combinations off | signatures off, combinations off | **6.33×** | **0.171** [0.170, 0.191] | 1.03 | identical | **passes** |
| Eco-12 / 2⁶⁴−353 | default, combinations off | signatures off, combinations off | 6.33× | 0.172 [0.171, 0.180] | 1.15 | identical | passes |

Work is grobx's own `subtracted` charge summed over every run of the call (rounds, input echelon,
final interreduction), discarded signature rounds included. Every arm's work is identical across its
five repetitions. "Combinations off" is the #714 overlay's `research_policy=none`: no randomized
plain row combinations and no randomized signature zero tests, so both sides reduce every row
deterministically. That pairing (same combination policy on both sides) was committed in
`summarize.py` before the pilot ran.

What the verdict means:

1. **Signatures pay in grobx when the alternative is exact plain F4.** On Eco-12, deterministic
   signature F4 does 6.3× less work and finishes in 17% of the wall of deterministic plain F4. Plain
   F4 there reduces 7,207 pairs, 6,331 to zero — the same 6,331 Zeebra reduces to zero (§4).
2. **Against randomized plain F4 the signature advantage disappears or nearly does.** grobx's
   default reaches Eco-12's 528.8 M by handing over to plain F4 with random row combinations, which
   collapse a zero block with one reduction. Signatures kept to the end do 582.0 M. On MQ11, where
   grobx never hands over, the combination-reduced plain arm does 1.69× the work, short of the 2×
   bar, but takes 1.76× the wall.
3. **Zeebra's relevant comparison is the exact one.** M29 §12 and #714 exclude uncertified randomized
   zero skipping, so Zeebra has no combination route. The question #716 answers for M30-S2 is
   whether a sound criterion removes the zero rows Zeebra pays for, and on Eco-12 it does. MQ11's
   exact comparison (§3.2, a declared extension outside the gate) agrees: 8.92× work, 0.116 wall.
4. **The gate is grobx-relative**, as plan §6.1 says. It shows signatures pay in *an* engine; it does
   not show they will pay in Zeebra, whose plain engine and arithmetic differ.

The declared MQ11 extension (§3.2) gives the same answer there: exact signature F4 does 8.92× less
work in 0.116 of the wall of exact plain F4. It is supplementary and not counted toward the gate.

By plan §6.1, #857 (M30-S3) proceeds, gated by #856's RFC. #858 remains conditional on S3.

## 2. Arms, method and what was measured

Arms, same input, seed 0, one worker, pinned grobx:

| Arm | Request | Route |
|---|---|---|
| `stock` | ordinary driver, no overlay | grobx default |
| `default` | research driver, no research keys | signatures with adaptive handover |
| `sig-off` | `research_signatures=false` (public `Params.signatures=false`) | plain F4 only |
| `no-handover` | `research_handover=false` | signature run to the end |
| `*-nocomb` | the above plus `research_policy=none` | no plain combinations, no signature zero tests |

The handover switch reuses the engine's own no-handover path, the one a cofactor-tracking call
already selects (`handover=off` in the run line); no handover threshold is edited
([overlay](../../tools/external/grobx-driver/research/signature/overlay.py)). Combinations were
crossed on Eco-12 and MQ10 / 2³¹−1 as the plan asks; at 32003 grobx never combines plain rows
(its threshold is p ≥ 46,341).

- 150 primary attempts: six instances, 4–7 arms each, n = 5, fresh process per attempt, case and arm
  order rotated and reversed on alternate repetitions. **All 150 verified**; no stop, refusal or
  failure. A declared one-attempt pilot preceded it and is retained as a diagnostic (11 of its 30
  attempts failed on a decoder bug in this study's ledger, not in grobx).
- Caps: 60 s / 2 GiB per child process (the #716 contract); the largest observed was 10.1 s and
  118 MiB.
- Wall is process wall, spawn to reap, including answer encoding. RSS is the larger of the tree's
  `VmHWM` and the driver's own kernel high water.
- Verification is outside the timed process. MQ10 answers are compared coefficient for coefficient
  with the retained Singular-verified bases (#683); wide-field answers are canonicalized and compared
  with the basis on which grobx, groebner-rs, Groebner.jl and (except MQ11) Zeebra agreed in the
  #738 wide corpus ([`references.json`](../../research/m30-signature/references.json)). Every arm on
  an instance returned the byte-identical answer.
- Work counters are grobx's stock report: per-round `subtracted` is its budget charge, one per entry
  of each target row or lane, which #713 found within 2% of measured MACs on MQ10 / 2³¹−1. No observer
  is switched on in timed runs, so the counters cost nothing. That proxy is unvalidated at 64 bits
  (§7).
- Overlay control: the research driver against the stock driver, same requests, same structural path
  and answer on all six instances. Wall ratio 0.99–1.02 on the four wide instances, **1.09–1.11 on
  MQ10** (CI [1.08, 1.12]). Every comparison in this note is within the research binary, so the
  ratios are unaffected; absolute MQ10 walls of the research arms run about 10% high.

## 3. Results

### 3.1 All arms

Medians of five; work and route are identical across repetitions.

| Instance | Arm | Wall ms [min, max] | RSS MiB | Work (M charges) | Route | Reductions / to zero | Zero rows |
|---|---|---:|---:|---:|---|---:|---:|
| MQ11 / Goldilocks | default | 2,991 [2,986, 2,995] | 117 | 970.7 | sig 11 | 782 / 26 | 562 |
| | no-handover | 2,991 [2,980, 3,003] | 116 | 970.7 | sig 11 | 782 / 26 | 562 |
| | sig-off | 5,254 [5,249, 5,262] | 116 | 1,636.3 | plain 11 | 840 / 84 | — |
| Eco-12 / 2⁶⁴−353 | default | 1,690 [1,679, 1,696] | 45 | 528.8 | sig 2 → plain 23 | 1,167 / 226 | — |
| | no-handover | 1,703 [1,690, 1,720] | 46 | 582.0 | sig 17 | 3,058 / 1,155 | 1,179 |
| | sig-off | 1,687 [1,682, 1,704] | 44 | 528.8 | plain 23 | 1,102 / 226 | — |
| | default-nocomb | 1,740 [1,727, 1,818] | 51 | 591.5 | sig 17 | 3,051 / 1,179 | 1,179 |
| | no-handover-nocomb | 1,724 [1,721, 1,931] | 46 | 591.5 | sig 17 | 3,051 / 1,179 | 1,179 |
| | sig-off-nocomb | 10,104 [10,073, 10,140] | 44 | 3,746.0 | plain 23 | 7,207 / 6,331 | 6,331 |
| MQ10 / 32003 | default | 386 [384, 390] | 16 | 378.6 (83.8 discarded) | sig 9 → plain 10 | 2,434 / 1,779 | 1,797 |
| | no-handover | 122 [122, 122] | 20 | 88.0 | sig 10 | 661 / 252 | 270 |
| | sig-off | 292 [292, 296] | 15 | 294.8 | plain 10 | 1,775 / 1,529 | 1,529 |
| MQ10 / 2³¹−1 | default | 175 [173, 176] | 17 | 119.1 (82.2 discarded) | sig 9 → plain 10 | 968 / 304 | 268 |
| | no-handover | 140 [139, 145] | 20 | 86.3 | sig 10 | 664 / 246 | 270 |
| | sig-off | 65 [65, 66] | 15 | 36.9 | plain 10 | 306 / 60 | — |
| | default-nocomb | 457 [453, 459] | 16 | 371.9 (87.0 discarded) | sig 9 → plain 10 | 2,429 / 1,797 | 1,797 |
| | no-handover-nocomb | 144 [144, 148] | 20 | 91.1 | sig 10 | 656 / 270 | 270 |
| | sig-off-nocomb | 340 [339, 345] | 15 | 284.9 | plain 10 | 1,775 / 1,529 | 1,529 |
| Katsura-11 / Goldilocks (held out) | default | 559 [555, 571] | 37 | 166.5 | sig 10 | 693 / 124 | 242 |
| | no-handover | 558 [554, 565] | 36 | 166.5 | sig 10 | 693 / 124 | 242 |
| | sig-off | 1,089 [1,087, 1,097] | 37 | 312.5 | plain 11 | 656 / 128 | — |
| Cyclic-7 / Goldilocks (held out) | default | 120 [117, 120] | 13 | 27.9 (6.8 discarded) | sig 10 → plain 26 | 1,026 / 128 | 30 |
| | no-handover | 82 [81, 85] | 14 | 19.7 | sig 22 | 1,036 / 177 | 187 |
| | sig-off | 98 [97, 104] | 13 | 21.1 | plain 26 | 683 / 98 | — |

"Reductions" and "to zero" are grobx's own counts. With randomized tests on, they include each test
combination (one reduction per combination), so they are not pair counts; "—" for zero rows marks
plain combination rounds, which print no zero-row figure. The nocomb rows and the MQ10 / 32003 plain
rows are exact per-row counts.

### 3.2 MQ11 without combinations (declared extension)

Declared after the primary cohort and before running it (commit `dd951927`), because the plan crossed
combinations only on Eco-12 and MQ10, which left MQ11 without an exact plain arm. Same caps, n = 5,
all 15 verified. It is supplementary: the gate rows in §1 keep their predeclared pairing.

| Arm | Wall ms [min, max] | RSS MiB | Work (M charges) | Route | Reductions / to zero | Max matrix |
|---|---:|---:|---:|---|---:|---|
| no-handover-nocomb | 5,448 [5,435, 5,479] | 116 | 1,841.0 | sig 11 | 1,318 / 562 | 2,130 × 3,836 |
| default-nocomb | 5,449 [5,438, 5,473] | 118 | 1,841.0 | sig 11 | 1,318 / 562 | 2,130 × 3,836 |
| sig-off-nocomb | 46,905 [46,876, 47,091] | 106 | 16,415.1 | plain 11 | 7,049 / 6,293 | 8,904 × 9,436 |

Exact signature F4 against exact plain F4 on MQ11: **8.92× less work, wall 0.116 [0.116, 0.117],
RSS 1.09×, identical output** — the same reading as Eco-12, and it would clear every A1 bar. grobx's
exact plain F4 reduces 7,049 pairs, 6,293 to zero: Zeebra reduces 7,059, also 6,293 to zero (§4).
Its 16.4 G charges sit 1.24× below Zeebra's 20.4 G serial products, so grobx's plain engine is not
where its MQ11 lead comes from.

MQ11's 22.8× gap (C1) decomposes, all within grobx and against the same answer:

| Step | Work (M) | Factor |
|---|---:|---:|
| exact plain F4 | 16,415.1 | — |
| exact signature F4 (criteria only) | 1,841.0 | 8.92× |
| signature F4 with randomized zero tests (grobx default) | 970.7 | 1.90× |
| *for comparison:* plain F4 with randomized combinations | 1,636.3 | 10.0× below exact plain |

Signature criteria are the single largest factor, and they are the only one that is deterministic.
The randomized zero tests in the signature run, like the plain combinations, are uncertified
shortcuts that #714 and M29 §12 exclude from Zeebra.

### 3.3 Pair decisions by mechanism (the §2.2 quantities, kept apart)

Signature run, from the stock `ran` line (one run; MQ10 rows are the no-handover arm):

| Instance | Considered | Base divisor: low ratio | high ratio | Equal sig-lead ratio | Syzygy criterion | Koszul (coprime) | Queued |
|---|---:|---:|---:|---:|---:|---:|---:|
| MQ11 | 293,761 | 124,617 | 0 | 0 | 152,654 | 782 | 15,708 |
| Eco-12 | 1,773,786 | 565,050 | 106,053 | 109 | 935,669 | 3,557 | 163,348 |
| MQ10 / 2³¹−1 | 78,210 | 31,750 | 3,041 | 87 | 34,523 | 518 | 8,291 |
| Katsura-11 | 153,181 | 75,815 | 243 | 830 | 63,156 | 448 | 12,689 |
| Cyclic-7 | 364,231 | 97,279 | 9,302 | 900 | 224,016 | 51 | 32,683 |

**Correction to plan §2.2 and C1:** grobx's `low` is not "low signature". It counts S-pairs eliminated
by the *low-ratio base divisor* (Roune–Stillman 2012 §3.5, Theorems 7/8): a faster, strictly weaker
form of the syzygy criterion that never removes a pair the syzygy criterion would keep. `high` is the
high-ratio base divisor. So on MQ11 all 277,271 eliminated pairs are syzygy-criterion eliminations
(152,654 tested directly, 124,617 short-cut through base divisors), and none is a separate
"low-signature" mechanism. Queued signatures can still be dropped when a round takes them, if a
syzygy learned since divides them (`dropped=` per round in the report).

Plain run, from the overlay's passive tally of grobx's Gebauer–Möller update (signatures-off arm):

| Instance | Updates | B (chain) dropped | Product skipped | M/F redundant | Kept |
|---|---:|---:|---:|---:|---:|
| MQ11 | 767 | 0 | 46,183 | 240,529 | 7,049 |
| Eco-12 | 888 | 809 | 74,064 | 255,066 | 8,011 |
| MQ10 | 256 | 55 | 11,363 | 19,027 | 1,830 |
| Katsura-11 | 539 | 1 | 20,331 | 119,139 | 4,465 |
| Cyclic-7 | 592 | 349 | 3,867 | 80,768 | 2,997 |

grobx's plain F4 keeps 7,049 MQ11 pairs and 8,011 Eco-12 pairs; Zeebra reduces 7,059 and 7,202.
The two plain engines start from essentially the same pair set.

The four reduction quantities, at the exact (nocomb) arms where they are comparable:

| Instance / arm | Pairs reduced | Reductions to zero | Zero rows | Pair rows adding no rank | Work (M) |
|---|---:|---:|---:|---:|---:|
| Eco-12, signature | 3,051 signatures | 1,179 | 1,179 | — | 591.5 |
| Eco-12, plain | 7,207 | 6,331 | 6,331 | — | 3,746.0 |
| MQ10 / 2³¹−1, signature | 656 | 270 | 270 | — | 91.1 |
| MQ10 / 2³¹−1, plain | 1,775 | 1,529 | 1,529 | — | 284.9 |

grobx does not report rank per pair row; the last-but-one column is Zeebra's metric (§4).

### 3.4 What the other instances add

- **Handover is net-negative on every instance where it fires here.** MQ10 at both primes hands over
  after nine signature rounds and restarts from the input: 386 ms against 122 ms kept (32003), 175
  against 140 (2³¹−1); 82–87 M charges are thrown away. Cyclic-7 hands over after ten rounds: 120 ms
  against 82. On Eco-12 the early handover costs nothing measurable (35,724 charges discarded).
- **With both sides exact, signatures win wherever measured:** 6.33× less work on Eco-12 and 3.13× on
  MQ10 / 2³¹−1 (no-handover against signatures off, combinations off on both).
- **With grobx's randomized mechanisms on** (signature zero tests in the signature run, plain
  combinations where p ≥ 46,341), the no-handover/off work ratio is 3.35× on MQ10 / 32003 (the plain
  side cannot combine there), 1.88× on Katsura-11, 1.69× on MQ11, 1.07× on Cyclic-7, 0.91× on Eco-12
  and 0.43× on MQ10 / 2³¹−1. The ranking follows how much the plain side's combinations recover.
- **Randomized plain combinations are the competing mechanism.** They cut grobx's plain work 7.1× on
  Eco-12 and 7.7× on MQ10 / 2³¹−1, enough that plain F4 with combinations is grobx's fastest route on
  MQ10 / 2³¹−1 (65 ms, against 140 ms for signatures). #714 showed that saving does not survive exact
  verification.
- **Signature bookkeeping is not visible in RSS** at these sizes: the largest RSS ratio is 1.33
  (MQ10 / 32003, 20 against 15 MiB).

## 4. Reconciling #223's row fraction with C1's

One `m29_cost_model --discovery --workers 1` record per instance, one binary, one window
([`census.jsonl.gz`](../../research/m30-signature/census.jsonl.gz),
[`reconcile.py`](../../research/m30-signature/reconcile.py)). Katsura-5 and Cyclic-5 at 2³¹−1 are the
two #223 instances that are public and generic (Fukuoka instances are not redistributable and the
CICO rows are application-specific, plan §4). All four on today's defaults.

| Instance | Pairs reduced | Reductions to zero (pairs − elements) | Pair rows | Pair rows adding no rank | Pair rows per pair | Products on zero-ending rows |
|---|---:|---:|---:|---:|---:|---:|
| Katsura-5 | 30 | 20 (66.7%) | 56 | 20 (35.7%) | 1.87 | 81.0% |
| Cyclic-5 | 116 | 75 (64.7%) | 220 | 75 (34.1%) | 1.90 | 70.2% |
| Eco-12 | 7,202 | 6,326 (87.8%) | 12,990 | 6,331 (48.7%) | 1.80 | 93.0% of 5,923.7 M |
| MQ11 | 7,059 | 6,293 (89.1%) | 10,365 | 6,293 (60.7%) | 1.47 | 92.9% of 20,377.0 M |

**The two figures are the same rows over different denominators, and they do not contradict.** A
selected pair becomes up to two Macaulay rows (its two halves; `PairMultiples::Distinct` and reducer
reuse remove some). When the pair reduces to zero, one half typically becomes the pivot for the
pair's lcm column and the other reduces to zero against it. So a pair that contributes nothing
still contributes one row of rank to its own matrix: per pair, 88–89% are wasted; per pair row,
49–61%. Because a pair that reduces to zero leaves one zero row (6,331 zero rows against 6,326 such
pairs on Eco-12, equal elsewhere), the per-row fraction is the per-pair fraction divided by the pair
rows per pair, which reproduces every row of the table. #223's 33–60% was the per-row figure on smaller instances
under `F4Options::recommended()`; on today's defaults Katsura-5 reads 35.7% (#223: 40.0%, 24 of
60, under `recommended()`), and the per-row figure rises with size as the per-pair figure does.

Two consequences for the gate. First, #223's "≈2× ceiling" is a ceiling on **pair rows**, and C1's
93% is a share of **products**: the zero-ending rows are the expensive ones because a pivot row stops
at its first free column while a zero row is reduced across its full width. Removing the zero
reductions removes up to 93% of Zeebra's products on these two instances, not half its rows'
worth. Second, the cross-engine check holds: grobx's exact plain F4 on Eco-12 builds 12,990 pair
rows (`given`) and reduces 6,331 rows to zero, exactly Zeebra's 12,990 and 6,331. grobx's exact
plain arm is therefore a faithful stand-in for Zeebra's route on Eco-12, and its 6.33× gap to exact
signature F4 is the size of the work a sound criterion removes there.

## 5. Criteria map and what a graft would need

Source read at the pin (`src/f4.rs` `enter`, `src/sig.rs`, `MANUAL.md` §Signatures); every
mechanism below presupposes the ones above it.

| Mechanism (grobx counter) | Source criterion | Prerequisite | Graftable onto unsigned F4? |
|---|---|---|---|
| Module order, signatures on every element | Schreyer order; Lairez 2022 §5.7 Thm 62; Gao–Volny–Wang 2016 §3 | a signature per basis element and per row; rows reduced in increasing signature order | — (this *is* the engine) |
| Signature-safe (F4-RB) reduction | Eder–Faugère 2017 §6.2, §13–14 | reducers chosen by sig-lead ratio; a reducer is dropped or reduced as a reductant by signature | no: changes reducer choice, which Zeebra's batched elimination currently picks freely |
| `syzygy` | syzygy criterion, Eder–Faugère §6.1 | known syzygy signatures, learned from every reduction to zero and from Koszul pairs | no: needs both rows above |
| `koszul` | relatively-prime criterion, Roune–Stillman 2012 §3.3 | signatures | no |
| `low` / `high` | base divisors, Roune–Stillman 2012 §3.5, Thms 7/8 | sig-lead ratios; strictly weaker than the syzygy criterion | no |
| `equal` | singular / rewrite criterion, Eder–Faugère §6.2 | sig-lead ratios | no |
| signature zero tests | `monagan-2017` §2 as grobx cites it; randomized | probability bound 2⁻³¹ per test | excluded (uncertified, M29 §12) |
| handover | grobx heuristic (`handover-time.*`) | none; restarts from the input | not a criterion |

None of the eliminations is a standalone pair filter: each needs signatures on every element and
signature-compatible reduction, which confirms #223's GVW finding for the whole family, not only for
the rewrite criterion. The plain F4 criteria grobx uses (B, product, M/F) are the ones Zeebra already
has. What this campaign changes is #223's quantitative premise, not its structural one: the row
ceiling (§4) understates the product saving, and the measured saving in an engine where the
criteria are sound is 6.3–8.9× in work on the two gate instances.

Feasibility, for #856 to decide between:

- **Selected criteria on minimum metadata.** Not available: no criterion above is sound without the
  full signature invariant. Reject.
- **A separate, opt-in signature engine** (F4/5- or F4-RB-shaped, batched by signature degree, exact
  reduction, no randomized zero tests), with a handover to the shipping plain engine. Supported by
  this evidence; its cost is a second reducer-selection path, signature and syzygy storage (not
  separately measured here, §7), and a correctness argument per Lairez Thm 62's invariant. Generic
  over prime fields: nothing here is characteristic-specific. **Defer to #856 for the go/no-go.**
- **Continued deferral.** Not supported by the gate.

grobx's handover heuristic should not be copied: it lost on every instance where it fired (§3.4).

## 6. Hypotheses

- **H-S1** (most of grobx's MQ11 advantage over Zeebra comes from signature criteria): **supported in the exact frame, falsified in the literal one.** As literally
  stated (public `signatures=false`, default settings), grobx's plain arm does 1,636 M against 971 M:
  comparable work, because randomized combinations recover most of what signatures save. Against
  exact plain F4, which is the route Zeebra is allowed, signature criteria account for 8.92× of the
  22.8× and grobx's plain engine for about 1.24× (§3.2).
- **H-S2** (on Eco-12 signatures without handover help less than randomized combinations): **supported.**
  Against combination-reduced plain F4 they do 0.91× the work at the same wall; against exact plain F4
  they do 6.3× less. Eco-12 *is* a signature target for an exact engine.
- **H-S3 / H-S4** are #856's to address. This campaign adds: handover cost more than it saved on
  every instance where it fired; a non-regular instance (Cyclic-7) still favoured signatures kept to
  the end; and no instance here showed a bookkeeping cost large enough to reverse an exact comparison.

## 7. What this does not show

- grobx's `subtracted` charges are a proxy for multiply-accumulates, validated to 2% only on MQ10 /
  2³¹−1 (#713); the #713 observer refuses characteristics ≥ 2³¹, so no 64-bit product count exists.
- Signature/syzygy metadata size and bookkeeping time are not separated: the report has stage clocks
  (`select`, `symbolic`, `update`) but no signature-specific memory figure; RSS is the only bound.
- Held-out instances use the Goldilocks field only; MQ10 is the larger-MQ rung below MQ11. MQ12 and
  above were not run.
- Seeds other than 0 were not sampled; the signature zero tests and plain combinations are seeded.
- Zeebra has no signature arm. Whether Zeebra's batched elimination can host signature-safe
  reduction at grobx's cost is #856's question.
