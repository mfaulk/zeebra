# #1078 (M35 D): reducer-row layouts and the §9.4 memory read

**Verdict: reject.** No arm meets the declared criteria on every row. The control below shows that carrying the
layout dispatch moves the default's wall time by −9% to +4.4%. The arms therefore do not merge, even as opt-in options. They live at tag
`measured/1078-row-layout` (`SigF4Options::row_layout`, `m34_matrix --row-layout`), and only this directory
lands on `main`.

Provenance:

| What | Commit | Tag | Job |
|---|---|---|---|
| Census (`census.jsonl.gz`) | `d6889a0a044b258eb1f913d9744908b09dba5f61` | `measured/1078-layout-census` | `census.py run`, one run per row, byte counts are deterministic |
| Read (`timing.jsonl.gz`, `refused.jsonl.gz`) | `ade74bd55ae68988287cd164a6a6d7a7b6dae945` | `measured/1078-row-layout` | bench-job `1bdd3a3a7f57` (7 reps), `8f595b528c0d` (1 rep), publication mode, CPUs 8-23 reserved |
| Control (`control.jsonl.gz`) | `ade74bd5…` against `d6889a0a…` | both tags | bench-job `4dfc5d571932` (7 reps) |

## The arms

Every arm is the forced signature engine at one worker. Each one changes how the serial cascade stores a batch:

- `baseline`: each reducer row is a `Vec<(u32 column, F)>`.
- `source`: each reducer row is a column list plus a borrow of its source polynomial's terms. Each coefficient is read from the source, and no copy is made.
- `u16`: when a batch has at most 65,536 columns, columns are batch-local `u16`. Coefficients go in a separate array, and the target rows are split the same way.
- `both`: `source` and `u16` together.

The layout is used only in the serial cascade (`workers <= 1`, no parallel cascade, no small-prime lane, no reuse census). Otherwise the engine falls back to `baseline` (`tests::test_row_layout_is_baseline_under_a_lane_or_workers`). Every arm returns the baseline's basis (`tests::test_every_row_layout_keeps_the_basis_and_meets_its_census`, and `digests=1` on every row below).

## Census (`census.py table census.jsonl.gz`)

Peak live storage for each arm, relative to `baseline`. The census runs with `--research-envelope`, so it reaches the peak of a row the 512 MB budget refuses.

| Row | Baseline peak | source | u16 | both | Wide batches |
|---|---:|---:|---:|---:|---:|
| m31/mq-dense-20 (refused) | 960 MiB | 0.644 | 0.625 | 0.388 | 0/5 |
| m31/mq-dense-18 | 249 MiB | 0.663 | 0.653 | 0.429 | 0/5 |
| m31/mq-random-12 | 1061 MiB | 0.255 | 1.000 | 0.255 | 6/22 |
| m31/katsura-11 | 21 MiB | 0.321 | 0.636 | 0.201 | 0/11 |
| m31/noon-9 | 49 MiB | 0.391 | 1.000 | 0.314 | 2/17 |

On every row the census measured, *source* cuts the peak. *u16* cuts it only when the peak batch is narrow. On sparse MQ and Noon-9, the peak sits in a batch wider than 65,536 columns, so *u16* leaves it at 1.0×. The live account is a small part of RSS on the structured rows (Noon-9 at m31: 49 MiB live against 607 MiB RSS), which is why the RSS ratios below barely move there.

## The read (`read.py decide timing.jsonl.gz refused.jsonl.gz`)

The criteria were declared on #1078 before the run. They apply to each arm:

1. live ≤ 0.80× baseline on every timing row;
2. the wall ratio's upper 95% bound is ≤ 1.03;
3. digests agree;
4. m31/mq-dense-20 completes under the shipping 512,000,000-byte budget where `baseline` stops.

| Arm | Rows meeting 1-3 | Refused case | Result |
|---|---:|---|---|
| source | 3/18 | stops (649 MB) | FAIL |
| u16 | 9/18 | stops (629 MB) | FAIL |
| both | 3/18 | **completes** | FAIL |

Wall ratio (arm over baseline, median and 95% interval). The live ratio is in parentheses.

| Row | Baseline | source | u16 | both |
|---|---:|---:|---:|---:|
| gf32003/mq-dense-15 | 3.97 s | 1.116 (0.77) | 1.058 (0.75) | 1.107 (0.53) |
| m31/mq-dense-15 | 3.27 s | 1.202 (0.66) | 1.004 [0.996-1.018] (0.63) | 1.180 (0.40) |
| m31/mq-dense-16 | 9.64 s | 1.543 (0.66) | 0.900 (0.63) | 1.514 (0.41) |
| m31/mq-dense-18 | 62.2 s | 1.947 (0.66) | 0.971 (0.65) | 1.921 (0.43) |
| gf32003/mq-random-11 | 19.3 s | 1.227 (0.51) | 0.990 (1.00) | 1.218 (0.51) |
| m31/katsura-12 | 3.00 s | 1.342 (0.32) | 0.973 (0.63) | 1.328 (0.20) |
| gf32003/katsura-11 | 0.53 s | 1.051 (0.54) | 0.976 (0.76) | 1.052 (0.30) |
| goldilocks/katsura-11 | 0.58 s | 1.021 (0.32) | 1.077 (0.64) | 1.020 (0.20) |
| m31/eco-12 | 1.50 s | 1.117 (0.39) | 0.981 (0.66) | 1.098 (0.27) |
| goldilocks/eco-12 | 1.76 s | 1.098 (0.39) | 1.100 (0.66) | 1.092 (0.27) |
| goldilocks/cyclic-7 | 0.09 s | 1.029 (0.44) | 1.064 (0.67) | 1.028 (0.30) |
| m31/noon-9 | 1.45 s | 0.979 (0.39) | 1.007 (1.00) | 0.984 (0.31) |
| goldilocks/noon-9 | 1.46 s | 0.972 (0.39) | 1.003 (1.00) | 0.987 (0.31) |

`read.py decide` prints the full 18 rows.

What the read says:

- ***source* trades time for memory, and the cost grows with the row.**
  - The cost runs from 2% to 95%, and it is worst on dense MQ, where the reducer rows are long and reused across many targets.
  - Each pivot reads its coefficient through the source polynomial's `(Monomial, F)` terms, not a packed copy. The likely cause, which this read did not profile, is that the inner loop then streams the wider terms on every reuse.
  - *source* is a net win only on Noon-9, where reducer rows are short and used once.
- ***u16* is free at 32 bits, but it misses the live criterion where it matters.**
  - On the 32-bit fields its wall interval stays under 1.03 on 12 of 14 rows, and the median is below 1.0 on 8. mq-dense-16 at m31 gains 10%. The two misses are gf32003/mq-dense-15 (1.058) and gf32003/cyclic-7 (hi 1.034).
  - On Goldilocks it costs 6–10% on Katsura, Eco and Cyclic. The read did not profile why.
  - It cannot reduce the peak on the rows whose peak batch is wide (sparse MQ, Noon), so criterion 1 fails there by construction.
- ***both* is the only arm that rescues the refused case.**
  - It is also the only arm under 512 MB in the census (0.388 × 960 MiB = 372 MiB). The read confirmed that it completes.
  - It carries *source*'s wall cost (1.92× on mq-dense-18), so a 512 MB budget that *both* lets through is cheaper bought by raising the budget.

## Control: the default's cost of the dispatch

`read.py control control.jsonl.gz` compares the `baseline` arm at `ade74bd5` with the census commit `d6889a0a`, whose cascade has no layout variants. This checks whether merging the opt-in arms slows the default.

| Row | `baseline` at ade74bd5 / d6889a0a | n (layout/census) |
|---|---:|---:|
| m31/mq-dense-15 | 0.909 (0.899-0.915) | 7/7 |
| m31/mq-dense-16 | 0.984 (0.980-0.991) | 7/7 |
| gf32003/mq-random-11 | 0.996 (0.994-0.998) | 7/6 |
| m31/katsura-12 | 0.944 (0.938-0.952) | 7/7 |
| gf32003/eco-12 | 1.022 (1.017-1.034) | 7/7 |
| m31/noon-9 | 1.044 (1.037-1.052) | 7/7 |
| goldilocks/cyclic-7 | 1.004 (0.999-1.012) | 6/5 |

Four attempts were flagged as contaminated and excluded. Digests agree on every row.

The dispatch is not neutral. It moves the default's wall time by between −9% and +4.4%, in both directions, and the read did not profile why. A +4.4% on Noon-9 is outside the 1.03 bound the arms themselves were held to. **The engine and harness changes on `feat/1078-row-layout` are therefore not merged.** Only this directory lands on `main`. The measured commits stay reachable through their tags, and the arms can be rebuilt from `measured/1078-row-layout`.

## Follow-ups

- *u16* restricted to fields of at most 32 bits is the near-miss. It meets the wall bound on 12 of 14 32-bit rows, but it fails criterion 1 by construction on wide-peak rows. It is not filed: the memory it saves is on rows that already fit the budget.
