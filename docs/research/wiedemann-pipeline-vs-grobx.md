# M34 WP E: the certified-Wiedemann lex pipeline against pinned grobx's lex route (#1039, M-5)

**Status:** Complete. The demonstration holds on the box-staircase chain family (`adaptive` ÷ grobx
0.07–0.39 on five deciding rows, three held out) and goes to M34-C, conditional on a forced grobx
F4-lex run; no routing change; #731 stands with a note.
**Measured at:** `5cce19f0` (tag `measured/1039-wiedemann-lex`) for every Zeebra figure:
`examples/lex_pipeline.rs`, release, fat LTO, one CGU, x86-64-v3. The deciding read's binary is built
from `git archive` of the tag (SHA-256 `a2b9f5e7…424d`). The development figures in §3 came from a
working-tree build of the same source. grobx 0.155.1 at `8005a2a1` (the #1029 pin), driver SHA-256
`fdd6aeec…83bc`, `order: lex`, raw, one worker. **Host:** Threadripper PRO 5995WX.
**Data:** [`research/1039-wiedemann-lex/`](../../research/1039-wiedemann-lex/). `tables.md` there is
regenerated from the records by `summarize.py`.
**Pre-declaration:** [#1039 comment](https://github.com/mfaulk/zeebra/issues/1039#issuecomment-7107987349),
posted before the deciding read.

## 1. Question and rule

Zeebra already ships certified scalar Wiedemann order conversion (#368,
[`certified-wiedemann.md`](certified-wiedemann.md)): `ConversionStrategy::Adaptive`, the default,
tries up to three random projections when D ≥ 128 and the last multiplication matrix is sparse,
certifies the reconstructed shape relations exactly, and otherwise falls back to the classical
walk. #1039 asks whether that existing code makes a **complete** lex-basis task faster than pinned
grobx's lex route on some identifiable family. No conversion algorithm is added.

The hypothesis and rule are the issue's, unchanged (plan §9.4), quantified in the pre-declaration:

- **Demonstration:** on at least two deciding rows, at least one held out, `adaptive` ÷ grobx has
  median ≤ 0.667 and upper 95% bound < 0.75 (plan §9.5's development bar).
- **Disproved** if every deciding row has median ≥ 0.833, or if the advantage exists only where
  Zeebra's grevlex stage already wins by itself.
- **Controls** (non-shape, nonradical) are reported with the fallback cost included.
- **Routing change** only if the adaptive rule's regret exceeds 1.2× on rows of two families.
- **#731 reconsidered** only if a Wiedemann-routed operator stores more than about 10 entries per
  column or is not cache-resident.

## 2. Contract, arms and what each engine pays

Same input text (the grobx driver's request JSON, read by both), field, variable order and lex
output; the ideal is never radicalized. The `m33-basis-v1` digest of every completed lex basis
agrees across all arms of every row, in development and in the deciding read.

| Arm | Route | Timed region (process wall, fresh process) | Acceptance |
|---|---|---|---|
| grobx155 | grobx's own lex entry: grevlex (signature F4, restarted at wider word sizes when FGLM overflows), then FGLM if zero-dimensional and D ≤ 65535, else F4 in lex | parse, all runs, FGLM, text | probabilistic (`reduce=tests`) |
| `zb-adaptive` | grevlex F4 (signature dispatch) → `fglm_to_lex_with_options`, `ConversionStrategy::Adaptive` | F4, quotient basis, operators, sequence, reconstruction, certificate, retries, fallback walk, lex polynomials | certified randomized when Wiedemann ran, else deterministic |
| `zb-wiedemann` | as above, `ConversionStrategy::Wiedemann` (projections regardless of size) | as above | certified randomized |
| `zb-classical` | as above, `ConversionStrategy::Classical` | as above | deterministic |
| `zb-direct-lex` | conventional F4 under lex (the signature dispatch is graded-only) | F4 | deterministic |

- **Budget.** `FglmOptions::recommended()` refuses every D > 4096 with
  `QuotientDimensionExceeded`, before the adaptive rule is consulted, although the Wiedemann route
  needs O(D) workspace. Every row the hypothesis is about therefore needs a caller-lifted budget.
  The `lifted` budget used here raises the D tripwire to 2²¹ and the span and operator budgets to
  12 GiB; the classical walk still refuses where its dense blocks (≈ 2D² cells) exceed that
  (`SpanStorageExceeded`, a typed refusal, not a timing).
- **The comparand route.** The driver exposes one lex entry point and grobx picks the route. The
  plan asks for "the faster of grobx's supported lex routes (FGLM, F4-lex)"; a forced F4-lex run is
  upstream-only (#1029 §8.3) and is not measured. At D > 65535 grobx's own choice *is* F4-lex.
- **grobx certified** is not scored (#1020 open). Zeebra's guarantee is the stronger one on every
  row.

## 3. Development observations (one attempt per arm, unreserved, decides nothing)

`research/1039-wiedemann-lex/probe-explore.jsonl`, CPUs 40–47, 300 s cap. Every figure here is a
single development attempt; the deciding figures are in §4.

| Row | D | grobx ms | `adaptive` ms (route) | `classical` ms | `direct-lex` ms |
|---|---|---|---|---|---|
| `wd-4-6` | 1,296 | 61 | 41 (Wiedemann) | 275 | 11 |
| `wd-5-5` | 3,125 | 541 | 173 (Wiedemann) | 4,436 | 21 |
| `wd-4-10` | 10,000 | 5,283 | 1,240 (Wiedemann) | 36,876 | 21 |
| `wdsq-4-10` (nonradical) | 20,000 | 24,144 | 2,393 (Wiedemann) | > 300 s | 3,962 |
| `wd-6-6` | 46,656 | > 300 s (deadline) | 11,733 (Wiedemann) | refused (span) | 1,027 |
| `wd-5-10` | 100,000 | 722 (F4-lex) | 40,898 (Wiedemann) | refused (span) | stopped (F4 budget) |
| `wdns-4-10` (non-shape) | 20,000 | 5,390 | 156,987 (3 projections, then classical) | 158,336 | 31 |
| `wdnr-4-10` (nonradical non-shape) | 20,000 | 5,574 | 160,093 (fallback) | 158,210 | 21 |
| `cyclic-7` (non-shape) | 924 | 184 | 876 (fallback) | 621 | stopped |
| `katsura-12` | 2,048 | 19,058 | 57,534 (classical: dense operator) | 57,373 | stopped |
| `pquad-10-1` | 1,024 | 1,783 | 4,126 (Wiedemann) | 3,648 | stopped |
| `pquad-12-1` | 4,096 | 95,391 | 212,575 (Wiedemann) | 201,939 | stopped |

Stage splits that explain the shape of this table:

- **Chain rows.** Both engines' grevlex stage is under a millisecond (the input is already a grevlex
  basis). On `wd-4-10` grobx spends 5.24 s in FGLM; Zeebra spends 0.45 s on the 2D-term sequence,
  0.67 s on reconstruction and 0.11 s certifying. Conversion is the whole difference.
- **Non-shape controls.** Three projections cost 2.9 s, then the dense classical walk costs 153 s
  at D = 20,000. grobx's FGLM is unaffected by shape position (5.4 s). The fallback, not the
  projections, is what loses.
- **Dense-operator rows.** On `katsura-12` operator construction alone is 40.1 s (grobx's whole
  route is 19.1 s); on `pquad-12-1` Zeebra's grevlex F4 alone (45.7 s) is 4.8x grobx's grevlex
  stage (9.5 s). No conversion route can close those gaps.
- **Direct lex.** On the chain family Zeebra's lex F4 is two orders of magnitude faster than either
  conversion: the chain is nearly triangular under lex. It is the best Zeebra route on every chain
  row except the nonradical `wdsq-4-10`, where Wiedemann wins (2.4 s against 4.0 s).

## 4. Deciding read

Four `tools/bench-job` **publication**-mode sessions on CCDs 1–2 (CPUs 8–23), rotating interleave,
600 s / 16 GiB caps: `n9` (job `05a26851f550`), `n3` (`1bb75c879cf3`), `classical`
(`33d5de1b9ac7`), and `replace` (`f658dbec76f0`, a three-repetition top-up of every `n9` arm).
Records: `research/1039-wiedemann-lex/records-*.jsonl.gz`; every table below is `tables.md`.

**Contamination.** 56 of `n9`'s 486 attempts were flagged contaminated: 52 on the per-arm clock
rule, 12 with a foreign compiler running (a sibling agent's release build, about 17:38 UTC) and 2 on
rest-of-machine load; an attempt can carry several. That is 11.5%, under the 20% void rule, so the
session stands. The flagged attempts are excluded and never timed. The `replace` job, which was not
declared before the read, tops every `n9` cell back up to at least nine clean attempts; its
repetitions are pooled into the medians and kept apart in the paired regret. The other sessions: `n3` 2 of 60 contaminated (both on the clock
rule, both replaced by job `94aed1e56361`), `classical` 0 of 27, `replace` 10 of 162. After pooling,
every scored deciding cell holds at least nine clean attempts. Three cells stay at eight: grobx on
the context row `cyclic-7`, and two 16-worker `direct-lex` cells, which are reported and never
scored.

### 4.1 The cross-engine table (one worker, scored)

Medians in ms; n is clean attempts; `classical` is n = 3 from its own session.

| Row | Role | D | grobx (n) | `adaptive` (n) | `adaptive` ÷ grobx [95%] | `classical` | `direct-lex` |
|---|---|---|---|---|---|---|---|
| `wd-4-10` | development | 10,000 | 2,432 (12) | 595 (10) | **0.24** [0.24, 0.25] | 34,438 | 22.4 |
| `wdsq-4-10` (nonradical) | development | 20,000 | 22,638 (10) | 2,268 (10) | **0.10** [0.10, 0.10] | 339,765 | 3,553 |
| `wd-3-30` | held out | 27,000 | 7,415 (12) | 2,886 (9) | **0.39** [0.38, 0.39] | 221,068 | 23.4 |
| `wd-4-12` over 2³¹−1 | held out | 20,736 | 14,563 (12) | 1,912 (12) | **0.13** [0.13, 0.13] | 187,298 | 54.2 |
| `wdsq-5-6` (nonradical) | held out | 15,552 | 24,599 (12) | 1,734 (10) | **0.07** [0.07, 0.07] | 268,533 | 8,102 |
| `wd-4-6` | context | 1,296 | 36.1 (10) | 26.0 (12) | 0.72 [0.71, 0.73] | 152 | 7.5 |
| `cyclic-7` (non-shape) | context | 924 | 93.9 (8) | 430 (12) | 4.58 [4.55, 4.61] | 317 | stopped |
| `katsura-11` | context | 1,024 | 1,213 (11) | 3,357 (11) | 2.77 [2.74, 2.81] | 3,444 | stopped |
| `pquad-10-1` | context | 1,024 | 883 (12) | 2,080 (10) | 2.36 [2.33, 2.40] | 1,863 | stopped |

Every completed basis of every row has one `m33-basis-v1` digest across all arms and both engines.
`stopped` is Zeebra's lex F4 on its default budget.

- **Deciding rows.** Every deciding row, development and held out, meets the pre-declared bar
  with room to spare: `adaptive` ÷ grobx is 0.07–0.39, and every upper 95% bound is below 0.40. The
  held-out rows came from a different support (`wd-3-30`: three variables), a different field
  width (`wd-4-12` over 2³¹−1) and a different scale and nonradical shape (`wdsq-5-6`), and none of
  them was run before the pre-declaration. **The demonstration holds.**
- **Disproof clause.** Both engines spend under a millisecond in grevlex on every deciding row,
  because the input is already a grevlex basis. The advantage is all in the conversion. Neither
  disproof condition is met.
- **Best qualified configuration.** On the radical chain rows Zeebra's own `direct-lex` is 27–123x
  faster than its Wiedemann pipeline and 110–320x faster than grobx. On the two nonradical rows the
  pipeline is the best Zeebra route: `wdsq-4-10` 2.27 s against `direct-lex` 3.55 s, and `wdsq-5-6`
  1.73 s against 8.10 s.

### 4.2 Controls and the D > 65535 switch (n = 3)

| Row | D | grobx route | grobx ms | `adaptive` ms (route) | `adaptive` ÷ grobx [95%] | `classical` | `direct-lex` ms |
|---|---|---|---|---|---|---|---|
| `wd-6-6` | 46,656 | FGLM | 417,315 | 11,069 (Wiedemann) | 0.03 [0.03, 0.03] | refused (span) | 961 |
| `wd-5-10` | 100,000 | **F4-lex** | 647 | 39,146 (Wiedemann) | 60.5 [59.5, 61.5] | refused (span) | stopped (F4 budget) |
| `wdns-4-10` (non-shape) | 20,000 | FGLM | 5,208 | 148,106 (3 projections → classical) | 28.4 [28.3, 28.7] | 144,491 | 25 |
| `wdnr-4-10` (nonradical non-shape) | 20,000 | FGLM | 5,232 | 147,196 (3 projections → classical) | 28.1 [28.0, 29.0] | 144,453 | 25 |

- **`wd-6-6`.** The largest FGLM-routed row: grobx's FGLM takes 417 s and 3.4 GiB, Zeebra's pipeline
  11.1 s and 32 MiB. The ratio grows with D.
- **The D > 65535 switch.** At D = 10⁵ grobx abandons FGLM for F4 in lex and finishes in 0.65 s;
  Zeebra's pipeline needs 39 s, and Zeebra's own lex F4 stops on its default budget. The
  pipeline's advantage ends exactly where grobx stops using FGLM.
- **Controls.** On the non-shape rows the three failed projections cost 2.8 s, then the classical
  walk costs 144 s and 6.1 GiB; grobx's FGLM is unaffected (5.2 s). The pipeline is 28x slower, and
  the fallback, not the projections, is what loses: `adaptive` is 1.02–1.03x `classical`.

### 4.3 Sixteen workers (reported apart, never scored)

Zeebra's FGLM is serial and the chain rows have no grevlex work, so 16 workers change nothing there:
`adaptive` on `wd-4-10` takes 601 ms at 16 w against 595 ms at 1 w, and `wd-3-30` 2.92 s against
2.89 s. Only the dense rows gain, through grevlex F4 and nothing else: `katsura-11` 1.42 s against
3.36 s, `pquad-10-1` 1.61 s against 2.08 s, `cyclic-7` 0.32 s against 0.43 s. Even at 16 workers
against grobx's one, Zeebra is slower on `katsura-11` (1.17x) and `pquad-10-1` (1.83x).

## 5. Routing finding

Regret is `adaptive` ÷ the faster of `classical` and `wiedemann`.

| Row | `adaptive` route | `adaptive` ms | `wiedemann` ms | `classical` ms | regret [95%] |
|---|---|---|---|---|---|
| `wd-4-10` | Wiedemann | 595 | 595 | 34,438 | 1.00 [0.99, 1.01] paired |
| `wdsq-4-10` | Wiedemann | 2,268 | 2,261 | 339,765 | 1.00 [0.99, 1.00] paired |
| `wd-3-30` | Wiedemann | 2,886 | 2,905 | 221,068 | 1.00 [0.99, 1.00] paired |
| `wd-4-12` | Wiedemann | 1,912 | 1,900 | 187,298 | 1.00 [0.99, 1.02] paired |
| `wdsq-5-6` | Wiedemann | 1,734 | 1,733 | 268,533 | 1.00 [0.99, 1.01] paired |
| `wd-4-6` | Wiedemann | 26.0 | 26.0 | 152 | 1.00 [0.99, 1.01] paired |
| `wd-6-6` | Wiedemann | 11,069 | 10,899 | refused | 1.02 [0.99, 1.04] paired |
| `wd-5-10` | Wiedemann | 39,146 | 38,918 | refused | 1.01 [0.99, 1.01] paired |
| `wdns-4-10` | 3 projections → classical | 148,106 | 147,269 | 145,001 | 1.03 [1.02, 1.03] paired |
| `wdnr-4-10` | 3 projections → classical | 147,196 | 147,358 | 144,453 | 1.02 [1.02, 1.04] paired |
| `cyclic-7` | 3 projections → classical | 430 | 429 | 317 | **1.36** [1.34, 1.37] |
| `katsura-11` | classical (`DenseOperator`) | 3,357 | 3,767 | 3,444 | 0.97 [0.97, 1.00] |
| `pquad-10-1` | Wiedemann | 2,080 | 2,080 | 1,863 | 1.12 [1.10, 1.14] |

"paired" pairs repetitions within one session; the others are independent ratios against the
`classical` session.

- **Where the rule picks Wiedemann** (every chain row, `pquad-10-1`) it is the faster route by
  6–155x on the chain rows, and classical is refused outright at D ≥ 46,656. On `pquad-10-1` it
  is slower than classical by 12% (2.08 s against 1.86 s), under the bar.
- **Where the rule falls back**, the failed projections are the regret: 2–3% on the D = 20,000
  non-shape controls, where the classical walk dominates, and 1.36 on `cyclic-7`, the one row over
  1.2x, where the failed projections are 26% of the route.
- **Dense operators.** On `katsura-11` the `D²/4` test sends the route to classical, and forcing
  Wiedemann there costs 12% more (3.77 s against 3.36 s). The rule is right. *(Later: #1233 removed
  most of the operator stage from the Wiedemann route, so this comparison has to be made again
  before the rule is relied on; see [`wiedemann-last-operator.md`](wiedemann-last-operator.md).)*

**No routing change.** Regret exceeds 1.2x on one row of one family (`cyclic-7`), and the
pre-declared rule needs two families. The nearest miss, `pquad-10-1` at 1.12x, is the dense-operator
case §6 describes; a density cut of about 10 stored entries per column would remove it, but it is
below the bar and is passed to #1017 as a feature rather than changed here.

## 6. Operator census and #731

`research/1039-wiedemann-lex/probe-operators.jsonl` (`lex_pipeline --arm probe`, development, the
operator is deterministic).

| Row | D | last operator: stored entries / column | unit columns | dense columns | stored MiB | route |
|---|---|---|---|---|---|---|
| `wd-4-10` | 10,000 | 0.20 | 0.90 | 0 | 0.26 | Wiedemann |
| `wdsq-4-10` | 20,000 | 0.25 | 0.95 | 0 | 0.53 | Wiedemann |
| `wd-6-6` | 46,656 | 0.33 | 0.83 | 0 | 1.31 | Wiedemann |
| `wd-5-10` | 100,000 | 0.20 | 0.90 | 0 | 2.59 | Wiedemann |
| `cyclic-7` | 924 | 18.9 | 0.86 | 0 | 0.29 | fallback |
| `katsura-11` | 1,024 | 264 | 0.67 | 290 | 2.56 | classical |
| `katsura-12` | 2,048 | 514 | 0.67 | 572 | 10.1 | classical |
| `pquad-10-1` | 1,024 | 239 | 0.75 | 252 | 1.99 | Wiedemann |
| `pquad-12-1` | 4,096 | 871 | 0.77 | 924 | 29.0 | Wiedemann |

On every row the hypothesis is about, the operator is what #731 modelled: under one stored entry
per column, mostly unit columns, a few MiB at most. #731 stands there. **Two rows contradict #731's
cost model**, and both are Wiedemann-routed: `pquad-10-1` and `pquad-12-1` store 239 and 871
entries per column, and `pquad-12-1`'s 29 MiB nearly fills one CCD's 32 MiB L3. By the
pre-declared trigger, #731's rejection is reopened **for dense-operator shape rows only**. On those
rows block Krylov cannot reach grobx: Zeebra's grevlex F4 alone is 0.64 of grobx's whole lex route
on `pquad-10-1` and 0.48 on `pquad-12-1` (development), and operator construction costs about as
much again. The reconsideration therefore stays a note on #731, not a new issue.

## 7. Features for #1017

Posted on #1017. In short:

- **D** costs nothing after the quotient basis. The shipping D ≤ 4096 tripwire refuses every row
  the Wiedemann route wins.
- **Stored entries per column** of the last operator separate the chain family (≤ 0.33) from
  everything else (≥ 18.9). The rule's `D²/4` cut lets `pquad-*` (239–871) through to a Wiedemann
  route that is no faster than classical.
- **Cyclicity** is what separates `wd-4-10` from `wdns-4-10`, whose operators are identical in
  density. No feature computed before projecting predicts it; the failed projections themselves
  cost about 2% of the D = 20,000 fallback and 26% of the `cyclic-7` route.
- **The comparand's route** changes at D = 65535 (§4.2).

## 8. Disposition

**The demonstration holds, on a narrow family, and no code change follows.**

- Zeebra's shipped certified-Wiedemann pipeline completes a lex basis 2.6–14x faster than pinned
  grobx's lex route on every deciding row (`adaptive` ÷ grobx 0.07–0.39, three held-out rows
  among them), and 38x faster on `wd-6-6`. The whole difference is the conversion.
- The family is the box-staircase chain the pre-declared class predicate names: a grevlex basis
  already, 10⁴ ≤ D ≤ 65535, a last operator of at most one stored entry per column. Outside it the
  pipeline loses: 28x on the non-shape controls (the classical fallback), 60x at D = 10⁵ (grobx
  switches to F4-lex), 2.4–4.6x on Katsura, Cyclic and dense planted quadratics (Zeebra's grevlex
  stage and operator construction).
- On the radical chain rows Zeebra's own lex F4 beats the pipeline by 27–123x. The pipeline is the
  best Zeebra route only on the nonradical rows (`wdsq-*`), where it is 1.6–4.7x faster than lex
  F4 and 10–14x faster than grobx.
- `FglmOptions::recommended()` refuses every winning row (D > 4096) before the adaptive rule runs;
  every figure here used a caller-lifted budget.
- No routing change (§5). #731 stays rejected for the family it modelled, with the dense-operator
  note (§6).

**Handed to M34-C (#1044).** Plan §9.4 sends a demonstration that meets §9.5's development bar to
M34-C for confirmation, and this one meets it: both development rows have median ≤ 0.24 and upper
bound ≤ 0.25. The class predicate is the one pre-declared on #1039. Two gaps must close before
M34-C can score it:

- **The faster grobx route.** §9.4 sets the comparand to the faster of grobx's FGLM and F4-lex.
  Only grobx's own choice (FGLM below D = 65535) was measurable here. At D = 10⁵ grobx's F4-lex
  takes 0.65 s, so a forced F4-lex run on the deciding rows could reverse every ratio. It needs
  the upstream route switch (#1029 §8.3).
- **grobx certified** (#1020), printed beside raw.

**Outcome for #1028's log:** no opportunity for code. The pipeline already ships, and nothing here
justifies a prototype, a routing change or block Krylov. The cross-engine claim waits on M34-C.

## 9. Limits

- **The family.** Every row on which the pipeline wins is a chain whose generators already form a
  grevlex basis with a box staircase. It is the `wiedemann_conversion` family the issue names, and
  it is artificial. No natural benchmark row in this note (Katsura, Cyclic, planted dense
  quadratics) has a sparse cyclic last operator.
- **grobx's route.** grobx chooses FGLM up to D = 65535. A forced F4-lex run below that threshold
  is not reachable through the driver and was not measured. On the chain rows grobx's
  F4-lex may be far faster than its FGLM, as it is at D = 10⁵ (§4.2).
- **grobx certified** is not scored (#1020). grobx raw is probabilistic and Zeebra's pipeline is
  exactly certified, so the guarantee gap favours grobx in every scored ratio.
- **Process RSS.** The harness's floor reading is 21 MiB on short attempts, so small RSS figures are
  bounds, not measurements.
- **The top-up job** was added after the pre-declaration, to replace contaminated attempts. It
  adds repetitions of the declared arms on the declared rows and changes no row, arm or threshold.
