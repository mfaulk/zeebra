# Zeebra cryptanalysis scoreboard

Generated. Every row is one registered problem; a problem's identity is the digest of its parameters, not its name. **The three classes are never added together** — an engineering surrogate's witness is not evidence about a public challenge.

## Official problems

The externally specified problems, unmodified. A witness here is a witness for the public challenge.

| problem | identity | vars | eqs | best result | external status |
|---|---|---:|---:|---|---|
| `poseidon31-cico-rf6-rp6` | `f36d914ee7d2` | 116 | 104 | not attempted | solved externally, verified 2026-04-10 |
| `poseidon31-cico-rf6-rp8` | `dfc1041fc131` | 118 | 106 | not attempted | solved externally, verified 2026-05-06 |
| `poseidon31-cico-rf6-rp10` | `cf06393b5cd6` | 120 | 108 | not attempted | solved externally, verified 2026-07-06 |
| `fukuoka-mq-III-n10-seed0` | `ae24edf8efc8` | 10 | 20 | **verified witness** in 124.0 ms (as published) | published with its answer |
| `fukuoka-mq-III-n15-seed0` | `0552d3b51070` | 15 | 30 | **verified witness** in 8999.9 ms (as published) | published with its answer |
| `fukuoka-mq-III-n20-seed0` | `434135c809f6` | 20 | 40 | not attempted | published with its answer |
| `fukuoka-mq-VI-n10-seed0` | `2558f4bccd7d` | 10 | 7 | not attempted | published with its answer |
| `fukuoka-mq-VI-n15-seed0` | `0345980a26d8` | 15 | 10 | not attempted | published with its answer |
| `fukuoka-mq-III-n55-seed0` | `f3ac89821637` | 55 | 110 | not attempted | no public solution recorded as of 2026-11-05 |

## Faithful reductions

The official field, state width, `k`, constants and objective; fewer rounds. A witness here says **nothing** about the official target it reduced from.

| problem | identity | vars | eqs | best result | external status |
|---|---|---:|---:|---|---|
| `poseidon31-cico-t16-rf2-rp0` | `56ccc99d85e0` | 46 | 34 | not attempted | — |
| `poseidon31-cico-t16-rf2-rp2` | `af93deb46aa5` | 48 | 36 | not attempted | — |
| `poseidon31-cico-t16-rf2-rp4` | `08e66c87a885` | 50 | 38 | not attempted | — |
| `poseidon31-cico-t16-rf4-rp0` | `a9242143a8c6` | 78 | 66 | not attempted | — |
| `poseidon31-cico-t16-rf4-rp2` | `80957f3ccf46` | 80 | 68 | not attempted | — |
| `poseidon31-cico-t16-rf4-rp4` | `2d8f8531107d` | 82 | 70 | not attempted | — |
| `poseidon31-cico-t16-rf6-rp0` | `78215e51ccef` | 110 | 98 | not attempted | — |
| `poseidon31-cico-t16-rf6-rp2` | `4e79a017932d` | 112 | 100 | not attempted | — |
| `poseidon31-cico-t16-rf6-rp4` | `82a1d6d3a18d` | 114 | 102 | not attempted | — |

## Engineering surrogates

Surrogates: reduced width, planted targets. Evidence about the implementation, not about any challenge.

| problem | identity | vars | eqs | best result | external status |
|---|---|---:|---:|---|---|
| `poseidon-t2-rf2-rp0-planted` | `9e98ebc3abec` | 5 | 5 | **verified witness** in 0.9 ms (as generated) | — |
| `poseidon-t2-rf2-rp2-planted` | `84cde35887fd` | 7 | 7 | **verified witness** in 167.2 ms (as generated) | — |
| `poseidon-t2-rf4-rp0-planted` | `ebd238585cc0` | 9 | 9 | **verified witness** in 393.1 ms (as generated) | — |
| `poseidon-t3-rf2-rp1-planted` | `036ea475c0b1` | 9 | 8 | stopped: max_matrix_columns (a Macaulay matrix needed more than the 60000 columns allowed, at degree 11; last completed stage generation) | — |

## Where the unfinished runs stopped

A higher degree is **not** nearer a solution: this table is a diagnostic, not a progress bar. Each row names the bound that bound, the degree reached, and the last stage that completed.

| problem | formulation | outcome | deg | last deg done | max cols | peak MB |
|---|---|---|---:|---:|---:|---:|
| `poseidon-t3-rf2-rp1-planted` | as generated | stopped: max_matrix_columns (a Macaulay matrix needed more than the 60000 columns allowed, at degree 11; last completed stage generation) | 11 | 10 | 42229 | 155.3 |

