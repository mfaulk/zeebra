| condition | cell | n | A median s | abs drift vs idle | A/A median [95% CI] | within ±2.5% | 5% arm median [95% CI] | detected | contaminated (dev) |
|---|---|---:|---:|---:|---|---|---|---|---:|
| idle | gf32003/mq-random-10 1w | 9 | 0.459 | 1.000x | 1.001 [0.985, 1.036] | no | 1.063 [1.050, 1.098] | yes | 0/27 |
| idle | gf32003/mq-random-10 16w | 9 | 0.240 | 1.000x | 0.989 [0.983, 1.002] | yes | 1.086 [1.069, 1.091] | yes | 0/27 |
| idle | wide64/eco-12 1w | 9 | 2.549 | 1.000x | 0.999 [0.986, 1.011] | yes | 1.056 [1.053, 1.062] | yes | 11/27 |
| idle | wide64/eco-12 16w | 9 | 1.715 | 1.000x | 0.997 [0.981, 1.002] | yes | 1.053 [1.035, 1.056] | yes | 11/27 |
| build | gf32003/mq-random-10 1w | 9 | 0.490 | 1.069x | 1.002 [0.997, 1.034] | no | 1.067 [1.057, 1.417] | yes | 8/27 |
| build | gf32003/mq-random-10 16w | 9 | 0.240 | 1.002x | 0.999 [0.980, 1.020] | yes | 1.087 [1.076, 1.093] | yes | 7/27 |
| build | wide64/eco-12 1w | 9 | 2.775 | 1.088x | 0.994 [0.985, 1.008] | yes | 1.050 [1.041, 1.063] | yes | 0/27 |
| build | wide64/eco-12 16w | 9 | 1.757 | 1.024x | 1.005 [0.995, 1.027] | no | 1.057 [1.042, 1.082] | yes | 18/27 |
| stream | gf32003/mq-random-10 1w | 9 | 0.495 | 1.078x | 1.001 [0.997, 1.007] | yes | 1.066 [1.063, 1.075] | yes | 1/27 |
| stream | gf32003/mq-random-10 16w | 9 | 0.256 | 1.067x | 1.000 [0.990, 1.014] | yes | 1.095 [1.074, 1.123] | yes | 0/27 |
| stream | wide64/eco-12 1w | 9 | 2.996 | 1.175x | 1.005 [0.970, 1.012] | no | 1.048 [1.038, 1.065] | yes | 0/27 |
| stream | wide64/eco-12 16w | 9 | 1.936 | 1.129x | 0.993 [0.982, 1.003] | yes | 1.046 [1.035, 1.054] | yes | 8/27 |

- idle: 22/108 attempts contaminated (20%), session void: yes; reasons: bench clock x22
  - observed: max sibling busy 0.64%, p90 bench foreign 0.40%, median rest load 1.7, max compilers 0
- build: 33/108 attempts contaminated (31%), session void: yes; reasons: bench clock x28, sibling x14, bench foreign x3
  - observed: max sibling busy 100.00%, p90 bench foreign 2.53%, median rest load 6.9, max compilers 59
- stream: 9/108 attempts contaminated (8%), session void: no; reasons: bench clock x9
  - observed: max sibling busy 1.16%, p90 bench foreign 0.87%, median rest load 36.4, max compilers 4
