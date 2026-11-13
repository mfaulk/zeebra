# Hard wide-field board (#738)

**Measured at:** `4ea1463afd6fec817dbb16b5226da65b8a7b9477`, `fa7cc30d7810c2f8a988fd8df9f30e69a83b7490`.

One worker, affinity 2; 60 s / 2 GiB per solver attempt.
Each attempt runs in a fresh process. Native wall includes the complete runner; external wall
is the supervised solver process and excludes version probing. Wrapper wall is also retained.
All completed bases are normalized in the declared field and compared coefficient for coefficient.
Ratios are Zeebra/comparand wall and require both operands ≥2× their measured Katsura-4 startup control.
BN254 is capability-only: it has no external oracle and no ratios. These are single observations, not medians.

| Field | Row | Zeebra s/status | Julia s/status | groebner-rs s/status | grobx s/status | Z/Julia | Z/rs | Z/grobx | Exact bases agreeing |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|
| wide64 | katsura-4 | 0.007 | 8.187 | 0.006 | 0.006 | — | — | — | 4 |
| wide64 | katsura-9 | 0.376 | 9.530 | 0.071 | 0.022 | — | 5.309x | 17.081x | 4 |
| wide64 | katsura-11 | 24.190 | 12.601 | 2.187 | 0.569 | — | 11.062x | 42.550x | 4 |
| wide64 | katsura-14 | 32000401 live nonzero entries were needed, over the limit of 32000000 | wall-60s | wall-60s-native | wall-60s-native | — | — | — | 0 |
| wide64 | cyclic-7 | 0.526 | 8.274 | 0.205 | 0.122 | — | 2.573x | 4.322x | 4 |
| wide64 | cyclic-11 | 32002281 live nonzero entries were needed, over the limit of 32000000 | wall-60s | wall-60s-native | wall-60s-native | — | — | — | 0 |
| wide64 | mq-random-10 | 11.608 | 12.086 | 1.591 | 0.517 | — | 7.295x | 22.433x | 4 |
| wide64 | mq-random-11 | wall-65s-tree | 23.372 | 9.418 | 2.925 | — | — | — | 3 |
| wide64 | mq-random-12 | wall-65s-tree | wall-60s | wall-60s-native | 20.642 | — | — | — | 1 |
| wide64 | mq-random-14 | wall-65s-tree | wall-60s | wall-60s-native | wall-60s-native | — | — | — | 0 |
| wide64 | mq-random-16 | 64387723 live nonzero entries were needed, over the limit of 32000000 | wall-60s | wall-60s-native | wall-60s-native | — | — | — | 0 |
| wide64 | eco-12 | 34.581 | 14.072 | 2.965 | 1.619 | — | 11.663x | 21.366x | 4 |
| wide64 | eco-14 | wall-65s-tree | wall-60s | wall-60s-native | wall-60s-native | — | — | — | 0 |
| wide64 | eco-18 | 90177302 live nonzero entries were needed, over the limit of 32000000 | wall-60s | wall-60s-native | wall-60s-native | — | — | — | 0 |
| wide64 | noon-7 | 0.569 | 8.656 | 0.175 | 0.028 | — | 3.242x | 20.414x | 4 |
| wide64 | noon-8 | 32000101 live nonzero entries were needed, over the limit of 32000000 | 13.029 | 1.435 | 0.128 | — | — | — | 3 |
| wide64 | noon-11 | symbolic preprocessing needed more than the 200000 rows allowed | wall-60s | wall-60s-native | wall-60s-native | — | — | — | 0 |
| goldilocks | katsura-4 | 0.007 | 8.044 | 0.007 | 0.006 | — | — | — | 4 |
| goldilocks | katsura-9 | 0.347 | 9.050 | 0.069 | 0.022 | — | 5.000x | 15.784x | 4 |
| goldilocks | katsura-11 | 24.714 | 12.092 | 2.127 | 0.547 | — | 11.621x | 45.198x | 4 |
| goldilocks | katsura-14 | 32000401 live nonzero entries were needed, over the limit of 32000000 | wall-60s | wall-60s-native | wall-60s-native | — | — | — | 0 |
| goldilocks | cyclic-7 | 0.563 | 8.086 | 0.176 | 0.116 | — | 3.201x | 4.838x | 4 |
| goldilocks | cyclic-11 | 32002281 live nonzero entries were needed, over the limit of 32000000 | wall-60s | wall-60s-native | wall-60s-native | — | — | — | 0 |
| goldilocks | mq-random-10 | 13.054 | 12.569 | 1.682 | 0.501 | — | 7.761x | 26.059x | 4 |
| goldilocks | mq-random-11 | wall-65s-tree | 25.034 | 9.961 | 3.326 | — | — | — | 3 |
| goldilocks | mq-random-12 | wall-65s-tree | wall-60s | 57.319 | 20.497 | — | — | — | 2 |
| goldilocks | mq-random-14 | wall-65s-tree | wall-60s | wall-60s-native | wall-60s-native | — | — | — | 0 |
| goldilocks | mq-random-16 | 64387723 live nonzero entries were needed, over the limit of 32000000 | wall-60s | wall-60s-native | wall-60s-native | — | — | — | 0 |
| goldilocks | eco-12 | 36.272 | 13.761 | 2.950 | 1.624 | — | 12.296x | 22.341x | 4 |
| goldilocks | eco-14 | wall-65s-tree | wall-60s | wall-60s-native | wall-60s-native | — | — | — | 0 |
| goldilocks | eco-18 | 90177302 live nonzero entries were needed, over the limit of 32000000 | wall-60s | wall-60s-native | wall-60s-native | — | — | — | 0 |
| goldilocks | noon-7 | 0.575 | 8.699 | 0.176 | 0.027 | — | 3.264x | 21.064x | 4 |
| goldilocks | noon-8 | 32000101 live nonzero entries were needed, over the limit of 32000000 | 13.119 | 1.487 | 0.127 | — | — | — | 3 |
| goldilocks | noon-11 | symbolic preprocessing needed more than the 200000 rows allowed | wall-60s | wall-60s-native | wall-60s-native | — | — | — | 0 |
| bn254 | katsura-9 | 3.116 | unsupported (>u64 contract) | unsupported (>u64 contract) | unsupported (>u64 contract) | — | — | — | no external oracle |
| bn254 | cyclic-7 | 4.863 | unsupported (>u64 contract) | unsupported (>u64 contract) | unsupported (>u64 contract) | — | — | — | no external oracle |
| bn254 | mq-random-10 | wall-65s-tree | unsupported (>u64 contract) | unsupported (>u64 contract) | unsupported (>u64 contract) | — | — | — | no external oracle |
| bn254 | eco-12 | wall-65s-tree | unsupported (>u64 contract) | unsupported (>u64 contract) | unsupported (>u64 contract) | — | — | — | no external oracle |
| bn254 | noon-7 | 2.484 | unsupported (>u64 contract) | unsupported (>u64 contract) | unsupported (>u64 contract) | — | — | — | no external oracle |

Raw inputs, complete bases, versions, binary hashes, limits, stderr, and watchdog stops:
[campaign.json.gz](campaign.json.gz). Frozen identities: [cases.json](cases.json).
