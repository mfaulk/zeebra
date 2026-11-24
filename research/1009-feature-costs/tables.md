# #1009 feature extraction costs (78 records)

Small inputs: the cheapest arm completes within 1.00 s (72 of 78 records). Threshold: 1.000% per feature, 2.000% for the set.

## Extraction cost

| feature | median cost | max cost | median ratio, small | worst ratio, small | worst record | small inputs over threshold | failing solves at most | verdict | worst cold ratio, small |
|---|---:|---:|---:|---:|---|---:|---:|---|---:|
| `system_shape` | 2.9 µs | 67.5 µs | 0.160% | 2.501% | `sd-fourcircles@p31` | 8 / 72 | 130.7 µs | FAIL | 99.714% |
| `is_homogeneous` | 15 ns | 301 ns | 0.001% | 0.067% | `sd-raksanyi@p31` | 0 / 72 | — | pass | 8.528% |
| `incidence` | 1.3 µs | 15.9 µs | 0.069% | 1.536% | `sd-raksanyi@p31` | 2 / 72 | 61.7 µs | FAIL | 13.615% |
| `linear_subsystem` | 112 ns | 10.1 µs | 0.009% | 0.991% | `sd-raksanyi@p64` | 0 / 72 | — | pass | 7.005% |
| `scalar_substitutions` | 495 ns | 39.0 µs | 0.033% | 1.114% | `sd-raksanyi@p31` | 2 / 72 | 61.7 µs | FAIL | 7.558% |
| `support_profile` | 6.0 µs | 84.1 µs | 0.327% | 6.545% | `sd-fourcircles@p31` | 20 / 72 | 372.6 µs | FAIL | 35.792% |
| `leading_profile` | 594 ns | 16.8 µs | 0.041% | 0.480% | `sd-czapor-86a@p31` | 0 / 72 | — | pass | 2.775% |
| `all seven` | 11.6 µs | 213.3 µs | 0.616% | 10.530% | `sd-raksanyi@p64` | 19 / 72 | 372.6 µs | FAIL | 142.114% |

## Repeat session

| feature | worst ratio, small | small inputs over threshold | verdict |
|---|---:|---:|---|
| `system_shape` | 2.937% | 9 / 72 | FAIL |
| `is_homogeneous` | 0.076% | 0 / 72 | pass |
| `incidence` | 1.664% | 2 / 72 | FAIL |
| `linear_subsystem` | 0.985% | 0 / 72 | pass |
| `scalar_substitutions` | 1.094% | 2 / 72 | FAIL |
| `support_profile` | 7.261% | 20 / 72 | FAIL |
| `leading_profile` | 0.481% | 0 / 72 | pass |
| `all seven` | 10.433% | 19 / 72 | FAIL |

## Per record

| record | n | m | cheapest arm | cheapest solve | entry route | all seven | ratio | costliest feature |
|---|---:|---:|---|---:|---|---:|---:|---|
| `sd-bjoerk-8@p31` | 8 | 9 | f4 | 10.4 ms | Shipping(DegreeSpread) | 64.8 µs | 0.624% | `system_shape` |
| `sd-bjoerk-8@p64` | 8 | 9 | f4 | 11.1 ms | Shipping(DegreeSpread) | 66.7 µs | 0.603% | `system_shape` |
| `sd-butcher@p31` | 8 | 8 | f4 | 3.7 ms | Shipping(DegreeSpread) | 12.5 µs | 0.339% | `support_profile` |
| `sd-butcher@p64` | 8 | 8 | f4 | 4.5 ms | Shipping(DegreeSpread) | 14.6 µs | 0.328% | `support_profile` |
| `sd-caprasse@p31` | 4 | 4 | f4 | 263.3 µs | Shipping(Small) | 4.4 µs | 1.676% | `support_profile` |
| `sd-caprasse@p64` | 4 | 4 | entry | 285.8 µs | Shipping(Small) | 5.0 µs | 1.743% | `support_profile` |
| `sd-cassou@p31` | 4 | 4 | entry | 544.5 µs | Shipping(Small) | 6.4 µs | 1.174% | `support_profile` |
| `sd-cassou@p64` | 4 | 4 | entry | 582.7 µs | Shipping(Small) | 7.3 µs | 1.257% | `support_profile` |
| `sd-czapor-86a@p31` | 3 | 3 | f4 | 39.4 µs | Shipping(Small) | 3.6 µs | 9.028% | `support_profile` |
| `sd-czapor-86a@p64` | 3 | 3 | f4 | 38.5 µs | Shipping(Small) | 3.8 µs | 9.815% | `support_profile` |
| `sd-ellipsoid-2@p31` | 10 | 4 | f4 | 110.4 µs | Shipping(DegreeSpread) | 4.5 µs | 4.037% | `support_profile` |
| `sd-ellipsoid-2@p64` | 10 | 4 | f4 | 130.7 µs | Shipping(DegreeSpread) | 4.9 µs | 3.773% | `support_profile` |
| `sd-ellipsoid-4@p31` | 10 | 4 | f4 | 212.9 µs | Shipping(DegreeSpread) | 4.3 µs | 2.031% | `support_profile` |
| `sd-ellipsoid-4@p64` | 10 | 4 | f4 | 214.1 µs | Shipping(DegreeSpread) | 5.0 µs | 2.323% | `support_profile` |
| `sd-ellipsoid-m2@p31` | 10 | 4 | none | stopped ≥ 903.3 ms | Shipping(DegreeSpread) | 4.3 µs | < 0.000% | `support_profile` |
| `sd-ellipsoid-m2@p64` | 10 | 4 | none | stopped ≥ 883.4 ms | Shipping(DegreeSpread) | 5.0 µs | < 0.001% | `support_profile` |
| `sd-fee-1@p31` | 4 | 4 | f4 | 337.0 µs | Shipping(Small) | 6.2 µs | 1.841% | `support_profile` |
| `sd-fee-1@p64` | 4 | 4 | f4 | 358.1 µs | Shipping(Small) | 7.0 µs | 1.954% | `support_profile` |
| `sd-fourbodyproblem@p31` | 6 | 6 | f4 | 13.2 ms | Shipping(DegreeSpread) | 5.9 µs | 0.045% | `support_profile` |
| `sd-fourbodyproblem@p64` | 6 | 6 | entry | 14.0 ms | Shipping(DegreeSpread) | 7.0 µs | 0.050% | `support_profile` |
| `sd-fourcircles@p31` | 2 | 3 | f4 | 56.1 µs | Shipping(Small) | 5.7 µs | 10.125% | `support_profile` |
| `sd-fourcircles@p64` | 2 | 3 | f4 | 64.5 µs | Shipping(Small) | 6.2 µs | 9.559% | `support_profile` |
| `sd-hairer-1@p31` | 8 | 6 | f4 | 251.4 µs | Signature | 4.8 µs | 1.898% | `support_profile` |
| `sd-hairer-1@p64` | 8 | 6 | f4 | 265.7 µs | Signature | 6.4 µs | 2.405% | `support_profile` |
| `sd-hairer-2-1@p31` | 13 | 12 | f4 | 36.5 ms | Shipping(DegreeSpread) | 17.2 µs | 0.047% | `support_profile` |
| `sd-hairer-2-1@p64` | 13 | 12 | entry | 37.1 ms | Shipping(DegreeSpread) | 20.1 µs | 0.054% | `support_profile` |
| `sd-hairer-2@p31` | 13 | 11 | f4 | 34.2 ms | Shipping(DegreeSpread) | 15.8 µs | 0.046% | `support_profile` |
| `sd-hairer-2@p64` | 13 | 11 | f4 | 35.6 ms | Shipping(DegreeSpread) | 18.6 µs | 0.052% | `support_profile` |
| `sd-heron@p31` | 7 | 4 | f4 | 52.6 µs | Shipping(DegreeSpread) | 2.9 µs | 5.471% | `support_profile` |
| `sd-heron@p64` | 7 | 4 | f4 | 54.6 µs | Shipping(DegreeSpread) | 3.5 µs | 6.405% | `support_profile` |
| `sd-raksanyi@p31` | 8 | 4 | f4 | 58.5 µs | Signature | 5.4 µs | 9.225% | `support_profile` |
| `sd-raksanyi@p64` | 8 | 4 | f4 | 61.7 µs | Signature | 6.5 µs | 10.530% | `support_profile` |
| `sd-robot-fabrice24@p31` | 9 | 9 | f4 | 5.1 ms | Signature | 19.3 µs | 0.379% | `support_profile` |
| `sd-robot-fabrice24@p64` | 9 | 9 | f4 | 5.5 ms | Signature | 20.7 µs | 0.378% | `support_profile` |
| `sd-robot-jcf26@p31` | 34 | 34 | entry | 9.8 ms | Shipping(DegreeSpread) | 148.2 µs | 1.513% | `support_profile` |
| `sd-robot-jcf26@p64` | 34 | 34 | f4 | 10.3 ms | Shipping(DegreeSpread) | 160.6 µs | 1.561% | `support_profile` |
| `sd-robot-romin@p31` | 12 | 7 | f4 | 1.1 ms | Signature | 6.0 µs | 0.563% | `support_profile` |
| `sd-robot-romin@p64` | 12 | 7 | f4 | 1.1 ms | Signature | 7.2 µs | 0.656% | `support_profile` |
| `sd-robot-rr@p31` | 15 | 16 | f4 | 2.0 ms | Signature | 17.6 µs | 0.868% | `support_profile` |
| `sd-robot-rr@p64` | 15 | 16 | f4 | 2.1 ms | Signature | 21.1 µs | 0.985% | `support_profile` |
| `sd-rose@p31` | 3 | 3 | entry | 399.5 µs | Shipping(Small) | 4.1 µs | 1.027% | `support_profile` |
| `sd-rose@p64` | 3 | 3 | f4 | 407.9 µs | Shipping(Small) | 4.6 µs | 1.126% | `support_profile` |
| `sd-schiele@p31` | 5 | 4 | entry | 356.7 µs | Shipping(Small) | 7.9 µs | 2.217% | `support_profile` |
| `sd-schiele@p64` | 5 | 4 | f4 | 372.6 µs | Shipping(Small) | 8.7 µs | 2.324% | `support_profile` |
| `sd-signaltheory-f633@p31` | 10 | 9 | f4 | 3.4 ms | Shipping(WorkerCrossover) | 16.5 µs | 0.488% | `support_profile` |
| `sd-signaltheory-f633@p64` | 10 | 9 | entry | 3.5 ms | Shipping(WorkerCrossover) | 18.6 µs | 0.534% | `support_profile` |
| `sd-signaltheory-f744@p31` | 12 | 12 | f4 | 16.0 ms | Signature | 26.3 µs | 0.164% | `support_profile` |
| `sd-signaltheory-f744@p64` | 12 | 12 | f4 | 16.9 ms | Signature | 29.3 µs | 0.174% | `support_profile` |
| `sd-signaltheory-f855@p31` | 14 | 15 | f4 | 66.1 ms | Shipping(DegreeSpread) | 116.7 µs | 0.177% | `support_profile` |
| `sd-signaltheory-f855@p64` | 14 | 15 | f4 | 67.4 ms | Shipping(DegreeSpread) | 115.3 µs | 0.171% | `support_profile` |
| `sd-signaltheory-f966@p31` | 16 | 24 | none | stopped ≥ 18.27 s | Shipping(DegreeSpread) | 213.3 µs | < 0.001% | `support_profile` |
| `sd-signaltheory-f966@p64` | 16 | 24 | none | stopped ≥ 22.25 s | Shipping(DegreeSpread) | 206.9 µs | < 0.001% | `support_profile` |
| `sd-singular-schwarz-10@p31` | 10 | 10 | entry | 49.4 ms | Shipping(WorkerCrossover) | 19.0 µs | 0.038% | `support_profile` |
| `sd-singular-schwarz-10@p64` | 10 | 10 | entry | 51.2 ms | Shipping(WorkerCrossover) | 20.8 µs | 0.041% | `support_profile` |
| `sd-singular-schwarz-11@p31` | 11 | 11 | entry | 62.4 ms | Signature | 22.6 µs | 0.036% | `support_profile` |
| `sd-singular-schwarz-11@p64` | 11 | 11 | entry | 62.1 ms | Signature | 24.4 µs | 0.039% | `support_profile` |
| `sd-singular-schwarz-7@p31` | 7 | 7 | f4 | 1.8 ms | Signature | 10.3 µs | 0.585% | `support_profile` |
| `sd-singular-schwarz-7@p64` | 7 | 7 | f4 | 1.8 ms | Signature | 11.0 µs | 0.607% | `support_profile` |
| `sd-singular-schwarz-8@p31` | 8 | 8 | entry | 3.8 ms | Signature | 11.8 µs | 0.308% | `support_profile` |
| `sd-singular-schwarz-8@p64` | 8 | 8 | entry | 3.7 ms | Signature | 13.3 µs | 0.357% | `support_profile` |
| `sd-singular-schwarz-9@p31` | 9 | 9 | entry | 7.8 ms | Signature | 15.1 µs | 0.194% | `support_profile` |
| `sd-singular-schwarz-9@p64` | 9 | 9 | entry | 7.7 ms | Signature | 16.6 µs | 0.216% | `support_profile` |
| `sd-trinks-1@p31` | 6 | 7 | f4 | 117.0 µs | Signature | 6.9 µs | 5.932% | `support_profile` |
| `sd-trinks-1@p64` | 6 | 7 | f4 | 129.3 µs | Signature | 8.7 µs | 6.765% | `support_profile` |
| `sd-trinks@p31` | 6 | 6 | f4 | 150.0 µs | Signature | 6.2 µs | 4.128% | `support_profile` |
| `sd-trinks@p64` | 6 | 6 | f4 | 164.9 µs | Signature | 7.7 µs | 4.694% | `support_profile` |
| `sd-verschelde-chemkin@p31` | 13 | 13 | f4 | 4.2 ms | Signature | 17.7 µs | 0.417% | `support_profile` |
| `sd-verschelde-chemkin@p64` | 13 | 13 | f4 | 4.6 ms | Signature | 20.5 µs | 0.448% | `support_profile` |
| `sd-verschelde-gametwo5@p31` | 5 | 5 | f4 | 2.3 ms | Shipping(Small) | 11.5 µs | 0.505% | `support_profile` |
| `sd-verschelde-gametwo5@p64` | 5 | 5 | entry | 2.5 ms | Shipping(Small) | 13.4 µs | 0.537% | `support_profile` |
| `sd-verschelde-gametwo6@p31` | 6 | 6 | f4 | 93.3 ms | Signature | 33.1 µs | 0.035% | `system_shape` |
| `sd-verschelde-gametwo6@p64` | 6 | 6 | f4 | 98.9 ms | Signature | 31.3 µs | 0.032% | `support_profile` |
| `sd-verschelde-gametwo7@p31` | 7 | 7 | f4 | 6.51 s | Signature | 78.6 µs | 0.001% | `system_shape` |
| `sd-verschelde-gametwo7@p64` | 7 | 7 | f4 | 7.77 s | Signature | 76.2 µs | 0.001% | `support_profile` |
| `sd-verschelde-virasoro@p31` | 8 | 8 | entry | 10.9 ms | Signature | 16.8 µs | 0.154% | `support_profile` |
| `sd-verschelde-virasoro@p64` | 8 | 8 | entry | 11.2 ms | Signature | 18.4 µs | 0.165% | `support_profile` |
| `sd-weispfenning-94@p31` | 3 | 3 | f4 | 254.1 µs | Shipping(Small) | 2.4 µs | 0.960% | `support_profile` |
| `sd-weispfenning-94@p64` | 3 | 3 | entry | 265.4 µs | Shipping(Small) | 3.0 µs | 1.146% | `support_profile` |

## Coverage

| question | records |
|---|---:|
| variables n (range) | 2–34 |
| generators m (range) | 3–34 |
| max degree (range) | 2–12 |
| terms (range) | 12–796 |
| m > n | 12 |
| m = n | 44 |
| m < n | 22 |
| every generator homogeneous | 2 |
| degree 2, no linear generator | 16 |
| incidence graph splits (> 1 component) | 0 |
| a declared variable unused | 0 |
| a nonzero constant generator | 0 |
| greedy elimination width (range) | 1–24 |
| width work cap reached | 0 |
| affine-linear rank > 0 | 32 |
| inconsistent linear part | 0 |
| a scalar substitution | 36 |
| a univariate generator | 12 |
| binomials > half the generators | 6 |
| a monomial generator | 2 |
| a duplicate generator | 4 |
| a leading monomial divisible by another | 50 |
| every initial pair coprime | 0 |
| overlap work cap reached | 0 |
| top-degree density (range) | 3.3e-05–1 |
| an arm completed within the wall | 74 |
| small (cheapest ≤ 1 s) | 72 |
