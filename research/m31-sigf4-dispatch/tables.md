| Row | Workers | n | F4 ms | Entry ms | Entry ÷ F4 [95%] | RSS ÷ F4 [95%] | Route | Dispatch µs |
|---|---:|---:|---:|---:|---:|---:|---|---:|
| gf32003/mq-random-10 | 16 | 9 | 236.7 | 378.9 | 1.611 [1.584, 1.617] | 0.651 [0.648, 0.658] | Signature | 0.9 |
| goldilocks/cyclic-7 | 16 | 9 | 143.7 | 143.3 | 0.990 [0.983, 1.012] | 0.997 [0.990, 1.015] | Shipping(DegreeSpread) | 0.5 |
| goldilocks/katsura-11 | 16 | 9 | 1,390.6 | 613.6 | 0.442 [0.438, 0.447] | 0.760 [0.756, 0.763] | Signature | 0.8 |
| goldilocks/katsura-4 | 16 | 9 | 5.9 | 6.0 | 1.002 [0.995, 1.015] | 1.013 [0.984, 1.022] | Shipping(Small) | 0.3 |
| goldilocks/mq-random-11 | 16 | 9 | 4,844.6 | 2,144.9 | 0.441 [0.440, 0.445] | 0.938 [0.937, 0.939] | Signature | 3.3 |
| goldilocks/noon-7 | 16 | 9 | 181.6 | 102.9 | 0.569 [0.558, 0.579] | 0.853 [0.757, 0.874] | Signature | 0.6 |
| m31/mq-random-10 | 16 | 9 | 221.9 | 387.7 | 1.745 [1.734, 1.776] | 0.815 [0.807, 0.834] | Signature | 0.9 |
| wide64/cyclic-7 | 16 | 9 | 143.3 | 143.7 | 1.004 [0.996, 1.016] | 1.000 [0.991, 1.012] | Shipping(DegreeSpread) | 0.5 |
| wide64/eco-12 | 16 | 9 | 2,417.9 | 1,713.9 | 0.712 [0.705, 0.715] | 0.849 [0.846, 0.852] | Signature | 0.8 |
| wide64/katsura-11 | 16 | 9 | 1,355.9 | 609.2 | 0.450 [0.445, 0.455] | 0.763 [0.760, 0.766] | Signature | 0.8 |
| wide64/katsura-4 | 16 | 9 | 6.0 | 6.0 | 0.990 [0.974, 1.021] | 0.993 [0.947, 1.047] | Shipping(Small) | 0.3 |
| wide64/katsura-9 (held out) | 16 | 9 | 73.0 | 42.0 | 0.576 [0.566, 0.581] | 0.908 [0.901, 0.921] | Signature | 0.5 |
| wide64/noon-8 (held out) | 16 | 9 | 931.3 | 574.9 | 0.616 [0.612, 0.623] | 0.828 [0.812, 0.834] | Signature | 3.1 |
| goldilocks/cyclic-7 | 1 | 9 | 289.8 | 291.0 | 1.007 [0.972, 1.032] | 1.003 [0.997, 1.010] | Shipping(DegreeSpread) | 0.5 |
| goldilocks/katsura-4 | 1 | 9 | 5.9 | 5.8 | 0.987 [0.961, 1.031] | 1.001 [0.977, 1.019] | Shipping(Small) | 0.3 |
| goldilocks/noon-7 | 1 | 9 | 194.9 | 94.7 | 0.490 [0.471, 0.493] | 0.821 [0.820, 0.823] | Signature | 0.5 |
| wide64/cyclic-7 | 1 | 9 | 268.1 | 268.6 | 1.003 [0.988, 1.008] | 1.002 [0.994, 1.005] | Shipping(DegreeSpread) | 0.5 |
| wide64/katsura-4 | 1 | 9 | 5.8 | 5.8 | 0.994 [0.983, 1.028] | 0.994 [0.963, 1.001] | Shipping(Small) | 0.3 |

## Gate C (plan §6.2), read mechanically

- wide64/eco-12 at 16 workers: 0.712 [0.705, 0.715] — **pass**
- goldilocks/katsura-11 at 16 workers: 0.442 [0.438, 0.447] — **pass**
- goldilocks/katsura-4 at 1 worker(s), upper ≤ 1.05: 0.987 [0.961, 1.031] — **pass**
- goldilocks/katsura-4 at 16 worker(s), upper ≤ 1.05: 1.002 [0.995, 1.015] — **pass**
- wide64/katsura-4 at 1 worker(s), upper ≤ 1.05: 0.994 [0.983, 1.028] — **pass**
- wide64/katsura-4 at 16 worker(s), upper ≤ 1.05: 0.990 [0.974, 1.021] — **pass**
- goldilocks/noon-7 at 1 worker(s), upper ≤ 1.05: 0.490 [0.471, 0.493] — **pass**
- goldilocks/noon-7 at 16 worker(s), upper ≤ 1.05: 0.569 [0.558, 0.579] — **pass**
- goldilocks/cyclic-7 at 1 worker(s), upper ≤ 1.05: 1.007 [0.972, 1.032] — **pass**
- goldilocks/cyclic-7 at 16 worker(s), upper ≤ 1.05: 0.990 [0.983, 1.012] — **pass**
- peak RSS ≤ 1.25× on every corpus row (median paired ratio): worst goldilocks/katsura-4 1.013 — **pass**
- one basis digest per row across arms and repetitions: 13/13 rows — **pass**
- certification of every row (entry arm, certify_f4_output): 13/13 rows — **pass**
- every child completed: 0 failures [] — **pass**

All measured criteria: **pass**
