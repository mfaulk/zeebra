# #1135 development re-read: the gate on Gate H's P8 cells

Re-reads `research/m34-gate-h/results/attempts.jsonl` (tag `measured/1012-matrix`, bench
host, 16 workers). Medians of clean completed repetitions of process wall, in ms. These rows
fitted the gate; they are not evidence for it.

## All development records with both cells (118)

- gate agrees (10% tolerance): 94 of 118
- worst regret under the gate: 1.53 (`gen-phosphorylation-5@p31`)
- geometric-mean regret: gate 1.078, w1 1.054, wmax 1.207

## Records in the 100 ms - 300 s band (18)

- gate agrees (10% tolerance): 18 of 18
- worst regret under the gate: 1.08 (`zb-col-grid-4x5@p31`)
- geometric-mean regret: gate 1.011, w1 1.300, wmax 1.045

| record | Bezout | gate | P8-w1 | P8-w16 | w1 / w16 | agrees |
|---|---:|:-:|---:|---:|---:|:-:|
| `sd-raksanyi@p31` | 6 | 1 | 6.2 | 7.7 | 0.79 | yes |
| `sd-geometry-heron-1@p31` | 8 | 1 | 6.3 | 8.0 | 0.79 | yes |
| `zb-toric-segre-3x3@p31` | 512 | 1 | 6.3 | 7.9 | 0.79 | yes |
| `sd-geometry-heron-1@p64` | 8 | 1 | 6.3 | 7.8 | 0.81 | yes |
| `sd-heron@p64` | 32 | 1 | 6.3 | 7.9 | 0.80 | yes |
| `gen-chandrasekhar-h-4@p31` | 16 | 1 | 6.4 | 7.8 | 0.81 | yes |
| `sd-heron@p31` | 32 | 1 | 6.4 | 7.9 | 0.80 | yes |
| `gen-phosphorylation-2@p31` | 64 | 1 | 6.4 | 8.3 | 0.77 | yes |
| `zb-col-path-8@p64` | 384 | 1 | 6.4 | 8.1 | 0.79 | yes |
| `zb-col-path-12@p31` | 6,144 | 16 | 6.4 | 8.7 | 0.74 | **no** |
| `zb-col-path-8@p31` | 384 | 1 | 6.4 | 8.1 | 0.79 | yes |
| `sd-hairer-1@p64` | 18 | 1 | 6.4 | 7.8 | 0.83 | yes |
| `zb-col-path-12@p64` | 6,144 | 16 | 6.4 | 8.6 | 0.75 | **no** |
| `zb-col-wheel-5@p64` | 64 | 1 | 6.5 | 8.4 | 0.77 | yes |
| `sd-ellipsoid-2@p31` | 162 | 1 | 6.5 | 7.7 | 0.84 | yes |
| `zb-col-wheel-5@p31` | 64 | 1 | 6.5 | 8.4 | 0.77 | yes |
| `sd-hairer-1@p31` | 18 | 1 | 6.5 | 7.7 | 0.84 | yes |
| `gen-phosphorylation-2@p64` | 64 | 1 | 6.5 | 8.4 | 0.77 | yes |
| `gen-phosphorylation-2-nonzero@p64` | 384 | 1 | 6.5 | 8.0 | 0.82 | yes |
| `gen-chandrasekhar-h-4@p64` | 16 | 1 | 6.5 | 8.0 | 0.82 | yes |
| `zb-toric-segre-3x3-slice-s1@p31` | 16 | 1 | 6.6 | 8.6 | 0.76 | yes |
| `sd-raksanyi@p64` | 6 | 1 | 6.6 | 8.0 | 0.82 | yes |
| `sd-ellipsoid-4@p64` | 1,500 | 1 | 6.6 | 7.9 | 0.83 | yes |
| `sd-ellipsoid-4@p31` | 1,500 | 1 | 6.6 | 7.9 | 0.84 | yes |
| `gen-phosphorylation-2-nonzero@p31` | 384 | 1 | 6.6 | 7.9 | 0.84 | yes |
| `zb-col-tree-8-s1@p31` | 384 | 1 | 6.7 | 8.5 | 0.79 | yes |
| `zb-col-tree-8-s1@p64` | 384 | 1 | 6.7 | 8.7 | 0.77 | yes |
| `gen-phosphorylation-3@p64` | 512 | 1 | 6.7 | 9.9 | 0.68 | yes |
| `sd-weispfenning-94@p31` | 100 | 1 | 6.8 | 7.5 | 0.90 | yes |
| `sd-ellipsoid-2@p64` | 162 | 1 | 6.8 | 8.0 | 0.84 | yes |
| `zb-toric-rnc-8-slice-s1@p31` | 128 | 1 | 6.8 | 8.8 | 0.77 | yes |
| `zb-toric-rnc-5@p31` | 64 | 1 | 6.8 | 8.0 | 0.86 | yes |
| `gen-phosphorylation-3@p31` | 512 | 1 | 6.9 | 9.9 | 0.69 | yes |
| `sd-weispfenning-94@p64` | 100 | 1 | 6.9 | 7.9 | 0.87 | yes |
| `sd-cassou@p64` | 1,344 | 1 | 7.0 | 7.9 | 0.89 | yes |
| `sd-cassou@p31` | 1,344 | 1 | 7.0 | 7.8 | 0.90 | yes |
| `zb-col-gnm-12-21-s1@p31` | 4,096 | 16 | 7.1 | 10.6 | 0.67 | **no** |
| `zb-col-gnm-12-21-s1@p64` | 4,096 | 16 | 7.1 | 10.3 | 0.69 | **no** |
| `gen-chandrasekhar-h-5@p31` | 32 | 1 | 7.2 | 7.9 | 0.91 | yes |
| `zb-reimer-4@p31` | 120 | 1 | 7.2 | 8.2 | 0.87 | yes |
| `sd-singular-schwarz-7@p31` | 128 | 1 | 7.2 | 9.7 | 0.74 | yes |
| `zb-col-gnm-12-17-s2@p31` | 4,096 | 16 | 7.3 | 11.1 | 0.66 | **no** |
| `gen-chandrasekhar-h-5@p64` | 32 | 1 | 7.4 | 8.1 | 0.91 | yes |
| `zb-reimer-4@p64` | 120 | 1 | 7.4 | 8.1 | 0.91 | yes |
| `zb-col-gnm-12-17-s2@p64` | 4,096 | 16 | 7.4 | 11.3 | 0.66 | **no** |
| `sd-singular-schwarz-7@p64` | 128 | 1 | 7.4 | 9.9 | 0.76 | yes |
| `gen-phosphorylation-4@p31` | 4,096 | 16 | 7.6 | 11.6 | 0.65 | **no** |
| `zb-col-grid-3x4@p31` | 4,096 | 16 | 7.6 | 10.8 | 0.71 | **no** |
| `gen-phosphorylation-4@p64` | 4,096 | 16 | 7.7 | 11.5 | 0.67 | **no** |
| `zb-col-grid-3x4@p64` | 4,096 | 16 | 7.8 | 10.8 | 0.73 | **no** |
| `gen-phosphorylation-4-nonzero@p31` | 32,768 | 16 | 8.3 | 8.9 | 0.92 | yes |
| `gen-phosphorylation-4-nonzero@p64` | 32,768 | 16 | 8.3 | 8.9 | 0.93 | yes |
| `gen-chandrasekhar-h-6@p31` | 64 | 1 | 8.3 | 10.6 | 0.78 | yes |
| `gen-chandrasekhar-h-6@p64` | 64 | 1 | 8.6 | 10.9 | 0.79 | yes |
| `zb-toric-segre-3x5-slice-s1@p31` | 256 | 1 | 9.2 | 13.3 | 0.70 | yes |
| `sd-singular-schwarz-8@p31` | 256 | 1 | 9.3 | 12.3 | 0.75 | yes |
| `gen-phosphorylation-5@p31` | 32,768 | 16 | 9.4 | 14.3 | 0.65 | **no** |
| `sd-singular-schwarz-8@p64` | 256 | 1 | 9.5 | 12.3 | 0.77 | yes |
| `gen-phosphorylation-5@p64` | 32,768 | 16 | 9.6 | 14.3 | 0.67 | **no** |
| `zb-cyclic-6@p31` | 720 | 1 | 10.4 | 11.3 | 0.92 | yes |
| `zb-toric-segre-4x4-slice-s1@p31` | 512 | 1 | 10.6 | 15.1 | 0.70 | yes |
| `zb-eco-8@p31` | 1,458 | 1 | 10.8 | 13.9 | 0.78 | yes |
| `zb-eco-8@p64` | 1,458 | 1 | 11.1 | 13.8 | 0.80 | yes |
| `zb-cyclic-6@p64` | 720 | 1 | 11.1 | 11.2 | 0.99 | yes |
| `zb-noon-5@p31` | 243 | 1 | 11.2 | 11.6 | 0.96 | yes |
| `zb-noon-5@p64` | 243 | 1 | 11.5 | 12.0 | 0.96 | yes |
| `sd-butcher@p31` | 4,608 | 16 | 11.6 | 12.1 | 0.96 | yes |
| `sd-butcher@p64` | 4,608 | 16 | 11.9 | 12.5 | 0.95 | yes |
| `zb-col-gnm-12-17-s1@p31` | 4,096 | 16 | 12.5 | 18.6 | 0.67 | **no** |
| `zb-col-gnm-12-17-s1@p64` | 4,096 | 16 | 12.6 | 18.5 | 0.68 | **no** |
| `zb-col-tree-12-s1@p31` | 6,144 | 16 | 12.7 | 16.8 | 0.76 | **no** |
| `gen-phosphorylation-6@p31` | 262,144 | 16 | 13.0 | 18.2 | 0.71 | **no** |
| `gen-phosphorylation-6@p64` | 262,144 | 16 | 13.0 | 18.0 | 0.72 | **no** |
| `zb-col-tree-12-s1@p64` | 6,144 | 16 | 13.0 | 17.0 | 0.76 | **no** |
| `gen-chandrasekhar-h-7@p31` | 128 | 1 | 13.3 | 16.0 | 0.83 | yes |
| `zb-col-ktree2-12-s1@p31` | 4,096 | 16 | 13.5 | 20.1 | 0.67 | **no** |
| `zb-col-ktree2-12-s1@p64` | 4,096 | 16 | 13.5 | 20.3 | 0.66 | **no** |
| `gen-chandrasekhar-h-7@p64` | 128 | 1 | 14.1 | 16.6 | 0.85 | yes |
| `gen-phosphorylation-6-nonzero@p31` | 2,621,440 | 16 | 14.9 | 15.2 | 0.98 | yes |
| `gen-phosphorylation-6-nonzero@p64` | 2,621,440 | 16 | 15.0 | 15.8 | 0.95 | yes |
| `sd-singular-schwarz-9@p31` | 512 | 1 | 15.1 | 18.4 | 0.82 | yes |
| `sd-singular-schwarz-9@p64` | 512 | 1 | 15.6 | 19.1 | 0.82 | yes |
| `gen-phosphorylation-7@p31` | 2,097,152 | 16 | 17.4 | 23.0 | 0.76 | **no** |
| `gen-phosphorylation-7@p64` | 2,097,152 | 16 | 17.9 | 23.7 | 0.76 | **no** |
| `sd-fourbodyproblem@p31` | 1,000 | 1 | 25.8 | 23.4 | 1.10 | **no** |
| `sd-fourbodyproblem@p64` | 1,000 | 1 | 28.1 | 25.2 | 1.11 | **no** |
| `gen-chandrasekhar-h-8@p31` | 256 | 1 | 32.2 | 33.9 | 0.95 | yes |
| `gen-chandrasekhar-h-8@p64` | 256 | 1 | 34.3 | 36.0 | 0.95 | yes |
| `sd-singular-schwarz-10@p31` | 1,024 | 1 | 36.3 | 80.0 | 0.45 | yes |
| `zb-katsura-9@p31` | 256 | 1 | 37.8 | 36.4 | 1.04 | yes |
| `sd-singular-schwarz-10@p64` | 1,024 | 1 | 38.1 | 81.4 | 0.47 | yes |
| `zb-katsura-9@p64` | 256 | 1 | 41.4 | 38.9 | 1.06 | yes |
| `sd-hairer-2@p31` | 4,608 | 16 | 49.5 | 48.0 | 1.03 | yes |
| `sd-hairer-2@p64` | 4,608 | 16 | 52.0 | 50.1 | 1.04 | yes |
| `sd-hairer-2-1@p31` | 4,608 | 16 | 52.5 | 49.9 | 1.05 | yes |
| `sd-hairer-2-1@p64` | 4,608 | 16 | 56.4 | 52.7 | 1.07 | yes |
| `zb-noon-7@p31` | 2,187 | 16 | 79.4 | 84.7 | 0.94 | yes |
| `zb-noon-7@p64` | 2,187 | 16 | 84.8 | 90.6 | 0.94 | yes |
| `zb-col-grid-4x5@p31` | 1,048,576 | 16 | 103.0 | 110.9 | 0.93 | yes |
| `zb-col-grid-4x5@p64` | 1,048,576 | 16 | 103.2 | 110.0 | 0.94 | yes |
| `gen-chandrasekhar-h-9@p31` | 512 | 1 | 105.3 | 103.1 | 1.02 | yes |
| `gen-chandrasekhar-h-9@p64` | 512 | 1 | 114.5 | 109.8 | 1.04 | yes |
| `zb-reimer-6@p31` | 5,040 | 16 | 132.8 | 82.5 | 1.61 | yes |
| `zb-reimer-6@p64` | 5,040 | 16 | 156.2 | 90.0 | 1.74 | yes |
| `zb-cyclic-7@p31` | 5,040 | 16 | 238.5 | 142.4 | 1.68 | yes |
| `zb-cyclic-7@p64` | 5,040 | 16 | 284.7 | 152.4 | 1.87 | yes |
| `gen-chandrasekhar-h-10@p31` | 1,024 | 1 | 396.3 | 542.8 | 0.73 | yes |
| `gen-chandrasekhar-h-10@p64` | 1,024 | 1 | 420.6 | 585.5 | 0.72 | yes |
| `zb-col-grid-5x5@p64` | 33,554,432 | 16 | 1,231.4 | 1,217.1 | 1.01 | yes |
| `zb-col-grid-5x5@p31` | 33,554,432 | 16 | 1,236.5 | 1,212.5 | 1.02 | yes |
| `gen-chandrasekhar-h-11@p31` | 2,048 | 16 | 1,622.2 | 1,336.1 | 1.21 | yes |
| `gen-chandrasekhar-h-11@p64` | 2,048 | 16 | 1,739.2 | 1,404.6 | 1.24 | yes |
| `zb-eco-12@p31` | 118,098 | 16 | 1,920.7 | 1,263.7 | 1.52 | yes |
| `zb-eco-12@p64` | 118,098 | 16 | 2,148.2 | 1,337.7 | 1.61 | yes |
| `zb-katsura-12@p31` | 2,048 | 16 | 4,153.7 | 2,012.2 | 2.06 | yes |
| `zb-katsura-12@p64` | 2,048 | 16 | 4,625.4 | 2,147.1 | 2.15 | yes |
| `gen-chandrasekhar-h-12@p31` | 4,096 | 16 | 7,019.0 | 5,030.3 | 1.40 | yes |
| `gen-chandrasekhar-h-12@p64` | 4,096 | 16 | 7,641.9 | 5,304.1 | 1.44 | yes |
