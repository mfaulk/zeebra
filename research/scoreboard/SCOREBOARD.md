# Zeebra cryptanalysis scoreboard

Generated. Every row is one registered problem; a problem's identity is the digest of its parameters, not its name. **The three classes are never added together** — an engineering surrogate's witness is not evidence about a public challenge.

## Official problems

The externally specified problems, unmodified. A witness here is a witness for the public challenge.

| problem | identity | vars | eqs | best result | external status | published method |
|---|---|---:|---:|---|---|---|
| `poseidon31-cico-rf6-rp6` | `f36d914ee7d2` | 116 | 104 | not attempted | solved externally, verified 2026-04-10 | Villard-style bivariate resultant, one full round skipped — 1 d 17 h on 128 CPU cores [eprint 2026/1905, Bak and Hostettler, Table 4], not attributed to the verified submission |
| `poseidon31-cico-rf6-rp8` | `dfc1041fc131` | 118 | 106 | not attempted | solved externally, verified 2026-05-06 | round skip, interpolation, Graeffe root finding; no resultant — 7 h on 96 RTX 5090 GPUs [eprint 2026/1254, Sanso and Vitto, Section 4.2 and Table 1], not attributed to the verified submission |
| `poseidon31-cico-rf6-rp10` | `cf06393b5cd6` | 120 | 108 | not attempted | solved externally, verified 2026-07-06 | no public method |
| `poseidon256-cico-2025-rf6-rp11` | `341728ee0a3d` | 31 | 30 | not attempted | no public solution recorded as of 2026-11-05 | — |
| `poseidon256-cico-2025-rf6-rp16` | `d63ef953e886` | 36 | 35 | not attempted | no public solution recorded as of 2026-11-05 | — |
| `poseidon64-cico-2025-rf6-rp13` | `442f473600ad` | 68 | 62 | not attempted | no public solution recorded as of 2026-11-05 | — |
| `anemoi64-cico-n1-fcico` | `8228cbc3d18e` | 2 | 2 | not attempted | published with its answer | — |
| `anemoi64-cico-n1-pcico` | `ce10ff6c5750` | 2 | 2 | not attempted | published with its answer | — |
| `anemoi64-cico-n2-fcico` | `ef9b02569e32` | 4 | 4 | not attempted | published with its answer | — |
| `anemoi64-cico-n2-pcico` | `4d31f9c78de0` | 3 | 3 | not attempted | published with its answer | — |
| `anemoi64-cico-n3-fcico` | `b9868196b3ef` | 6 | 6 | not attempted | published with its answer | — |
| `anemoi64-cico-n3-pcico` | `504c96c59a37` | 4 | 4 | not attempted | published with its answer | — |
| `anemoi64-cico-n4-fcico` | `95bc61726779` | 8 | 8 | not attempted | published with its answer | — |
| `anemoi64-cico-n4-pcico` | `b61cd0a62722` | 5 | 5 | not attempted | published with its answer | — |
| `anemoi64-cico-n5-fcico` | `a56639921520` | 10 | 10 | not attempted | published with its answer | — |
| `anemoi64-cico-n5-pcico` | `d285b0cf43aa` | 6 | 6 | not attempted | published with its answer | — |
| `fukuoka-mq-III-n10-seed0` | `ae24edf8efc8` | 10 | 20 | **verified witness** in 106.4 ms (as published) | published with its answer | — |
| `fukuoka-mq-III-n15-seed0` | `0552d3b51070` | 15 | 30 | **verified witness** in 7798.5 ms (as published) | published with its answer | — |
| `fukuoka-mq-III-n20-seed0` | `434135c809f6` | 20 | 40 | stopped: max_live_nonzeros at degree 5 | published with its answer | — |
| `fukuoka-mq-VI-n10-seed0` | `2558f4bccd7d` | 10 | 7 | **verified witness** in 577.8 ms (slice(3 fixed, seed 7)) | published with its answer | — |
| `fukuoka-mq-VI-n15-seed0` | `0345980a26d8` | 15 | 10 | stopped: campaign reached no verdict | published with its answer | — |
| `fukuoka-mq-III-n55-seed0` | `f3ac89821637` | 55 | 110 | not attempted | no public solution recorded as of 2026-11-05 | — |

## Faithful reductions

The official field, state width, `k`, constants and objective; fewer rounds. A witness here says **nothing** about the official target it reduced from.

| problem | identity | vars | eqs | best result | external status | published method |
|---|---|---:|---:|---|---|---|
| `poseidon31-cico-t16-rf2-rp0` | `56ccc99d85e0` | 46 | 34 | **verified witness** in 6.0 ms (resultant, slice(12 fixed, seed 1)) | — | — |
| `poseidon31-cico-t16-rf2-rp2` | `af93deb46aa5` | 48 | 36 | **verified witness** in 47598.5 ms (resultant, slice(12 fixed, seed 1)) | — | — |
| `poseidon31-cico-t16-rf2-rp4` | `08e66c87a885` | 50 | 38 | **verified witness** in 3274316.5 ms on 32 workers (resultant, slice(12 fixed, seed 1)) | — | — |
| `poseidon31-cico-t16-rf4-rp0` | `a9242143a8c6` | 78 | 66 | **verified witness** in 50638.1 ms (resultant, slice(12 fixed, seed 1)) | — | — |
| `poseidon31-cico-t16-rf4-rp2` | `80957f3ccf46` | 80 | 68 | stopped: max_live_nonzeros at degree 4 | — | — |
| `poseidon31-cico-t16-rf4-rp4` | `2d8f8531107d` | 82 | 70 | stopped: max_live_nonzeros at degree 4 | — | — |
| `poseidon31-cico-t16-rf6-rp0` | `78215e51ccef` | 110 | 98 | stopped: max_live_nonzeros at degree 4 | — | — |
| `poseidon31-cico-t16-rf6-rp2` | `4e79a017932d` | 112 | 100 | stopped: max_live_nonzeros at degree 4 | — | — |
| `poseidon31-cico-t16-rf6-rp4` | `82a1d6d3a18d` | 114 | 102 | stopped: max_live_nonzeros at degree 4 | — | — |

## Engineering surrogates

Surrogates: reduced width, planted targets. Evidence about the implementation, not about any challenge.

| problem | identity | vars | eqs | best result | external status | published method |
|---|---|---:|---:|---|---|---|
| `poseidon-t2-rf2-rp0-planted` | `9e98ebc3abec` | 5 | 5 | **verified witness** in 0.8 ms (as generated) | — | — |
| `poseidon-t2-rf2-rp2-planted` | `84cde35887fd` | 7 | 7 | **verified witness** in 141.2 ms (as generated) | — | — |
| `poseidon-t2-rf4-rp0-planted` | `ebd238585cc0` | 9 | 9 | **verified witness** in 348.3 ms (as generated) | — | — |
| `poseidon-t3-rf2-rp1-planted` | `036ea475c0b1` | 9 | 8 | stopped: max_matrix_columns at degree 11 | — | — |

## Where the unfinished runs stopped

A higher degree is **not** nearer a solution: this table is a diagnostic, not a progress bar. Each row names the bound that bound, the degree reached, and the last stage that completed.

| problem | formulation | outcome | deg | last deg done | max cols | peak MB |
|---|---|---|---:|---:|---:|---:|
| `poseidon31-cico-t16-rf2-rp0` | as generated | stopped: max_live_nonzeros at degree 6 | 6 | 5 | 36284 | 108.2 |
| `poseidon31-cico-t16-rf2-rp0` | slice(12 fixed, seed 0) | basis only, no witness | 4 | 4 | 17424 | 102.8 |
| `poseidon31-cico-t16-rf2-rp2` | as generated | stopped: max_matrix_columns at degree 6 | 6 | 5 | 50148 | 195.1 |
| `poseidon31-cico-t16-rf2-rp2` | slice(12 fixed, seed 0) | stopped: max_live_nonzeros at degree 4 | 4 | 3 | 40182 | 212.9 |
| `poseidon31-cico-t16-rf2-rp4` | as generated | stopped: max_matrix_columns at degree 6 | 6 | 5 | 70244 | 311.9 |
| `poseidon31-cico-t16-rf2-rp4` | slice(12 fixed, seed 0) | stopped: max_live_nonzeros at degree 5 | 5 | 4 | 8642 | 24.8 |
| `poseidon31-cico-t16-rf4-rp0` | as generated | stopped: max_matrix_columns at degree 6 | 6 | 5 | 81800 | 246.2 |
| `poseidon31-cico-t16-rf4-rp0` | slice(12 fixed, seed 0) | stopped: max_live_nonzeros at degree 4 | 4 | 3 | 12861 | 22.0 |
| `poseidon31-cico-t16-rf4-rp2` | as generated | stopped: max_live_nonzeros at degree 5 | 5 | 4 | 21098 | 24.0 |
| `poseidon31-cico-t16-rf4-rp2` | slice(12 fixed, seed 0) | stopped: max_live_nonzeros at degree 4 | 4 | 3 | 15363 | 23.7 |
| `poseidon31-cico-t16-rf4-rp4` | as generated | stopped: max_live_nonzeros at degree 5 | 5 | 4 | 24441 | 29.8 |
| `poseidon31-cico-t16-rf4-rp4` | slice(12 fixed, seed 0) | stopped: max_live_nonzeros at degree 4 | 4 | 3 | 18706 | 26.2 |
| `poseidon31-cico-t16-rf6-rp0` | as generated | stopped: max_live_nonzeros at degree 5 | 5 | 4 | 28794 | 30.6 |
| `poseidon31-cico-t16-rf6-rp0` | slice(12 fixed, seed 0) | stopped: max_live_nonzeros at degree 4 | 4 | 3 | 23059 | 25.0 |
| `poseidon31-cico-t16-rf6-rp2` | as generated | stopped: max_live_nonzeros at degree 5 | 5 | 4 | 31296 | 34.9 |
| `poseidon31-cico-t16-rf6-rp2` | slice(12 fixed, seed 0) | stopped: max_live_nonzeros at degree 4 | 4 | 3 | 25561 | 29.3 |
| `poseidon31-cico-t16-rf6-rp4` | as generated | stopped: max_live_nonzeros at degree 5 | 5 | 4 | 34639 | 40.7 |
| `poseidon31-cico-t16-rf6-rp4` | slice(12 fixed, seed 0) | stopped: max_live_nonzeros at degree 4 | 4 | 3 | 28904 | 35.1 |
| `poseidon31-cico-t16-rf2-rp0` | slice(12 fixed, seed 0) | the slice is empty, which says nothing about the problem | 4 | 4 | 17424 | 102.8 |
| `poseidon31-cico-t16-rf2-rp0` | slice(12 fixed, seed 3) | the slice is empty, which says nothing about the problem | 4 | 4 | 17424 | 102.8 |
| `poseidon31-cico-t16-rf2-rp0` | slice(12 fixed, seed 4) | the slice is empty, which says nothing about the problem | 4 | 4 | 17424 | 102.8 |
| `poseidon31-cico-t16-rf2-rp0` | slice(12 fixed, seed 5) | the slice is empty, which says nothing about the problem | 4 | 4 | 17424 | 102.8 |
| `poseidon31-cico-t16-rf2-rp0` | slice(12 fixed, seed 7) | the slice is empty, which says nothing about the problem | 4 | 4 | 17424 | 102.8 |
| `poseidon-t3-rf2-rp1-planted` | as generated | stopped: max_matrix_columns at degree 11 | 11 | 10 | 42229 | 155.3 |
| `poseidon-t3-rf2-rp1-planted` | as generated | stopped: max_matrix_columns at degree 11 | 11 | 10 | 42229 | 155.3 |
| `fukuoka-mq-VI-n15-seed0` | slice(5 fixed, seed 0) | stopped: max_live_nonzeros at degree 9 | 9 | 8 | 20146 | 217.9 |
| `fukuoka-mq-VI-n15-seed0` | slice(5 fixed, seed 1) | stopped: max_live_nonzeros at degree 9 | 9 | 8 | 20146 | 217.8 |
| `fukuoka-mq-VI-n15-seed0` | slice(5 fixed, seed 2) | stopped: max_live_nonzeros at degree 9 | 9 | 8 | 20146 | 217.9 |
| `fukuoka-mq-VI-n15-seed0` | slice(5 fixed, seed 3) | stopped: max_live_nonzeros at degree 9 | 9 | 8 | 20146 | 217.8 |
| `fukuoka-mq-VI-n15-seed0` | slice(5 fixed, seed 4) | stopped: max_live_nonzeros at degree 9 | 9 | 8 | 20146 | 217.9 |
| `fukuoka-mq-VI-n15-seed0` | slice(5 fixed, seed 5) | stopped: max_live_nonzeros at degree 9 | 9 | 8 | 20146 | 217.9 |
| `fukuoka-mq-VI-n15-seed0` | slice(5 fixed, seed 6) | stopped: max_live_nonzeros at degree 9 | 9 | 8 | 20146 | 217.9 |
| `fukuoka-mq-VI-n15-seed0` | slice(5 fixed, seed 7) | stopped: max_live_nonzeros at degree 9 | 9 | 8 | 20146 | 217.8 |
| `fukuoka-mq-VI-n15-seed0` | campaign over 8 slices | stopped: campaign reached no verdict | 0 | none | 0 | 0.0 |
| `fukuoka-mq-III-n20-seed0` | as published | stopped: max_live_nonzeros at degree 5 | 5 | 4 | 10147 | 195.5 |
| `poseidon-t3-rf2-rp1-planted` | as generated | stopped: max_matrix_columns at degree 11 | 11 | 10 | 42229 | 155.3 |
| `fukuoka-mq-VI-n10-seed0` | slice(3 fixed, seed 1) | the slice is empty, which says nothing about the problem | 9 | 9 | 5103 | 4.7 |
| `fukuoka-mq-VI-n10-seed0` | slice(3 fixed, seed 3) | the slice is empty, which says nothing about the problem | 9 | 9 | 5104 | 4.6 |

