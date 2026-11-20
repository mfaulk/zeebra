## Timing (adaptive option ÷ reference, paired; median [95%])

| criterion | row | w | n | ref | ref ms | ad ms | ad ÷ ref [95%] | half-width | bound | read | route | team |
|---|---|---:|---:|---|---:|---:|---:|---:|---:|---|---|---:|
| T3 | gf32003/mq-random-10 | 1 | 9 | f4 | 1080.70 | 466.32 | 0.432 [0.424, 0.443] | 2.2% | 1.05 | pass | Some(Signature) | 1 |
| T3 | gf32003/mq-random-10 | 4 | 21 | f4 | 397.32 | 396.56 | 1.008 [0.990, 1.016] | 1.3% | 1.05 | pass | Some(Shipping(WorkerCrossover)) | 4 |
| T3 | gf32003/mq-random-10 | 8 | 9 | f4 | 280.53 | 280.80 | 1.002 [0.998, 1.007] | 0.5% | 1.05 | pass | Some(Shipping(WorkerCrossover)) | 8 |
| T3 | gf32003/mq-random-10 | 16 | 9 | f4 | 243.23 | 242.35 | 0.997 [0.991, 1.003] | 0.6% | 1.05 | pass | Some(Shipping(WorkerCrossover)) | 16 |
| T5 | goldilocks/cyclic-7 | 1 | 9 | f4 | 284.76 | 286.37 | 1.003 [0.993, 1.020] | 1.3% | 1.05 | pass | Some(Shipping(DegreeSpread)) | 1 |
| T5 | goldilocks/cyclic-7 | 16 | 9 | f4 | 145.68 | 145.66 | 1.001 [0.983, 1.018] | 1.8% | 1.05 | pass | Some(Shipping(DegreeSpread)) | 16 |
| T4 | goldilocks/katsura-11 | 16 | 21 | m31 | 618.46 | 618.29 | 0.998 [0.989, 1.004] | 0.7% | 1.03 | pass | Some(Signature) | 16 |
| T4 abs | goldilocks/katsura-11 | 16 | 9 | f4 | 1362.50 | 618.29 | 0.456 [0.451, 0.460] | 1.0% | 0.5 | pass | Some(Signature) | 16 |
| T4 | goldilocks/mq-random-11 | 16 | 9 | m31 | 2148.77 | 2135.87 | 1.000 [0.992, 1.008] | 0.8% | 1.03 | pass | Some(Signature) | 16 |
| T4 abs | goldilocks/mq-random-11 | 16 | 9 | f4 | 4682.83 | 2135.87 | 0.456 [0.454, 0.467] | 1.4% | 0.5 | pass | Some(Signature) | 16 |
| T5 | goldilocks/noon-7 | 1 | 9 | f4 | 210.17 | 97.80 | 0.463 [0.455, 0.475] | 2.2% | 1.05 | pass | Some(Signature) | 1 |
| T5 | goldilocks/noon-7 | 16 | 9 | f4 | 194.01 | 106.36 | 0.549 [0.533, 0.555] | 2.0% | 1.05 | pass | Some(Signature) | 8 |
| T4 | goldilocks/noon-7 | 16 | 21 | m31 | 108.07 | 105.67 | 0.972 [0.966, 0.979] | 0.6% | 1.03 | pass | Some(Signature) | 8 |
| T3 | m31/mq-random-10 | 1 | 9 | f4 | 930.69 | 454.76 | 0.487 [0.479, 0.491] | 1.3% | 1.05 | pass | Some(Signature) | 1 |
| T3 | m31/mq-random-10 | 4 | 9 | f4 | 338.34 | 337.65 | 0.995 [0.983, 1.015] | 1.6% | 1.05 | pass | Some(Shipping(WorkerCrossover)) | 4 |
| T3 | m31/mq-random-10 | 8 | 9 | f4 | 247.98 | 248.36 | 1.001 [0.993, 1.005] | 0.6% | 1.05 | pass | Some(Shipping(WorkerCrossover)) | 8 |
| T3 | m31/mq-random-10 | 16 | 9 | f4 | 228.10 | 226.89 | 0.995 [0.987, 1.002] | 0.8% | 1.05 | pass | Some(Shipping(WorkerCrossover)) | 16 |
| T5 | wide64/cyclic-7 | 1 | 9 | f4 | 277.41 | 278.45 | 1.010 [0.982, 1.030] | 2.4% | 1.05 | pass | Some(Shipping(DegreeSpread)) | 1 |
| T5 | wide64/cyclic-7 | 16 | 9 | f4 | 146.12 | 143.60 | 0.990 [0.971, 1.006] | 1.7% | 1.05 | pass | Some(Shipping(DegreeSpread)) | 16 |
| T4 | wide64/eco-12 | 16 | 9 | m31 | 1727.19 | 1740.46 | 1.007 [1.000, 1.009] | 0.5% | 1.03 | pass | Some(Signature) | 16 |
| T4 abs | wide64/eco-12 | 16 | 9 | f4 | 2372.24 | 1740.46 | 0.733 [0.731, 0.736] | 0.3% | 0.7 | FAIL | Some(Signature) | 16 |
| T4 | wide64/katsura-11 | 16 | 9 | m31 | 617.14 | 619.00 | 1.001 [0.990, 1.009] | 1.0% | 1.03 | pass | Some(Signature) | 16 |
| T4 abs | wide64/katsura-11 | 16 | 9 | f4 | 1344.11 | 619.00 | 0.461 [0.459, 0.463] | 0.4% | 0.5 | pass | Some(Signature) | 16 |
| T4 | wide64/noon-8 | 16 | 9 | m31 | 602.80 | 602.57 | 1.005 [0.989, 1.016] | 1.3% | 1.03 | pass | Some(Signature) | 8 |
| held-out | goldilocks/mq-random-10 | 1 | 9 | f4 | 5610.10 | 960.70 | 0.171 [0.168, 0.173] | 1.6% | 1.05 | pass | Some(Signature) | 1 |
| held-out (info) | goldilocks/mq-random-10 | 4 | 9 | f4 | 1817.77 | 1812.85 | 0.992 [0.966, 1.027] | 3.1% | 1.05 | pass (imprecise) | Some(Shipping(WorkerCrossover)) | 4 |
| held-out (info) | goldilocks/mq-random-10 | 8 | 9 | f4 | 1183.17 | 1185.58 | 1.002 [0.995, 1.006] | 0.5% | 1.05 | pass | Some(Shipping(WorkerCrossover)) | 8 |
| held-out | goldilocks/mq-random-10 | 16 | 9 | f4 | 910.41 | 906.23 | 1.002 [0.990, 1.011] | 1.0% | 1.05 | pass | Some(Shipping(WorkerCrossover)) | 16 |
| held-out | m31/eco-11 | 1 | 9 | f4 | 1312.03 | 405.21 | 0.313 [0.305, 0.318] | 2.2% | 1.05 | pass | Some(Signature) | 1 |
| held-out (info) | m31/eco-11 | 4 | 9 | f4 | 529.81 | 331.74 | 0.627 [0.615, 0.647] | 2.5% | 1.05 | pass (imprecise) | Some(Signature) | 4 |
| held-out (info) | m31/eco-11 | 8 | 9 | f4 | 433.11 | 320.34 | 0.737 [0.734, 0.745] | 0.7% | 1.05 | pass | Some(Signature) | 8 |
| held-out | m31/eco-11 | 16 | 9 | f4 | 425.80 | 339.41 | 0.794 [0.791, 0.799] | 0.5% | 1.05 | pass | Some(Signature) | 16 |
| held-out | m31/katsura-10 | 1 | 9 | f4 | 839.97 | 173.57 | 0.207 [0.206, 0.208] | 0.7% | 1.05 | pass | Some(Signature) | 1 |
| held-out (info) | m31/katsura-10 | 4 | 9 | f4 | 324.22 | 323.53 | 1.005 [0.987, 1.021] | 1.7% | 1.05 | pass | Some(Shipping(WorkerCrossover)) | 4 |
| held-out (info) | m31/katsura-10 | 8 | 9 | f4 | 246.25 | 246.22 | 1.000 [0.995, 1.010] | 0.7% | 1.05 | pass | Some(Shipping(WorkerCrossover)) | 8 |
| held-out | m31/katsura-10 | 16 | 9 | f4 | 241.55 | 240.03 | 1.001 [0.986, 1.011] | 1.3% | 1.05 | pass | Some(Shipping(WorkerCrossover)) | 16 |
| T5 | goldilocks/katsura-4 | 1 | 31 | f4 | 0.04 | 0.04 | 1.014 [1.008, 1.019] | 0.5% | 1.05 | pass | Some(Shipping(Small)) | 1 |
| T5 | goldilocks/katsura-4 | 16 | 31 | f4 | 0.05 | 0.05 | 1.014 [1.005, 1.027] | 1.1% | 1.05 | pass | Some(Shipping(Small)) | 16 |
| T5 | wide64/katsura-4 | 1 | 31 | f4 | 0.04 | 0.04 | 1.014 [1.009, 1.020] | 0.6% | 1.05 | pass | Some(Shipping(Small)) | 1 |
| T5 | wide64/katsura-4 | 16 | 31 | f4 | 0.05 | 0.05 | 1.016 [1.009, 1.023] | 0.7% | 1.05 | pass | Some(Shipping(Small)) | 16 |
| T4 (info) | wide64/katsura-9 | 1 | 31 | m31 | 23.12 | 24.22 | 1.047 [1.044, 1.048] | 0.2% | 1.03 | FAIL | Some(Signature) | 1 |
| T4 (info) | wide64/katsura-9 | 4 | 31 | m31 | 20.04 | 21.39 | 1.060 [1.025, 1.096] | 3.4% | 1.03 | FAIL (imprecise) | Some(Signature) | 4 |
| T4 (info) | wide64/katsura-9 | 8 | 31 | m31 | 20.70 | 22.25 | 1.075 [1.072, 1.077] | 0.2% | 1.03 | FAIL | Some(Signature) | 8 |
| T4 | wide64/katsura-9 | 16 | 31 | m31 | 23.49 | 24.41 | 1.036 [1.034, 1.040] | 0.3% | 1.03 | FAIL | Some(Signature) | 8 |

## T6 memory (median peak RSS, MiB)

| row | w | ad | f4 | ad ÷ f4 (≤ 1.25) | m31 | ad ÷ m31 (≤ 1.10) |
|---|---:|---:|---:|---:|---:|---:|
| gf32003/mq-random-10 | 1 | 31 | 38 | 0.821 | — | — |
| gf32003/mq-random-10 | 4 | 43 | 43 | 1.007 | — | — |
| gf32003/mq-random-10 | 8 | 43 | 43 | 1.002 | — | — |
| gf32003/mq-random-10 | 16 | 47 | 47 | 0.990 | — | — |
| goldilocks/cyclic-7 | 1 | 22 | 22 | 1.000 | — | — |
| goldilocks/cyclic-7 | 16 | 25 | 24 | 1.009 | — | — |
| goldilocks/katsura-11 | 16 | 117 | 153 | 0.767 | 115 | 1.018 |
| goldilocks/katsura-4 | 1 | 8 | 8 | 1.056 | — | — |
| goldilocks/katsura-4 | 16 | 8 | 8 | 1.021 | — | — |
| goldilocks/mq-random-10 | 1 | 89 | 88 | 1.018 | — | — |
| goldilocks/mq-random-10 | 4 | 97 | 97 | 1.000 | — | — |
| goldilocks/mq-random-10 | 8 | 98 | 98 | 0.998 | — | — |
| goldilocks/mq-random-10 | 16 | 107 | 115 | 0.926 | — | — |
| goldilocks/mq-random-11 | 16 | 372 | 397 | 0.938 | 370 | 1.005 |
| goldilocks/noon-7 | 1 | 23 | 26 | 0.864 | — | — |
| goldilocks/noon-7 | 16 | 24 | 28 | 0.847 | 22 | 1.060 |
| m31/eco-11 | 1 | 49 | 55 | 0.900 | — | — |
| m31/eco-11 | 4 | 51 | 59 | 0.854 | — | — |
| m31/eco-11 | 8 | 52 | 60 | 0.869 | — | — |
| m31/eco-11 | 16 | 52 | 60 | 0.871 | — | — |
| m31/katsura-10 | 1 | 32 | 33 | 0.988 | — | — |
| m31/katsura-10 | 4 | 39 | 39 | 1.009 | — | — |
| m31/katsura-10 | 8 | 40 | 41 | 0.994 | — | — |
| m31/katsura-10 | 16 | 42 | 42 | 1.000 | — | — |
| m31/mq-random-10 | 1 | 41 | 38 | 1.078 | — | — |
| m31/mq-random-10 | 4 | 44 | 44 | 1.002 | — | — |
| m31/mq-random-10 | 8 | 45 | 45 | 1.001 | — | — |
| m31/mq-random-10 | 16 | 49 | 49 | 0.999 | — | — |
| wide64/cyclic-7 | 1 | 22 | 22 | 1.008 | — | — |
| wide64/cyclic-7 | 16 | 25 | 24 | 1.018 | — | — |
| wide64/eco-12 | 16 | 174 | 203 | 0.853 | 171 | 1.014 |
| wide64/katsura-11 | 16 | 117 | 153 | 0.767 | 115 | 1.018 |
| wide64/katsura-4 | 1 | 8 | 8 | 1.013 | — | — |
| wide64/katsura-4 | 16 | 9 | 8 | 1.045 | — | — |
| wide64/katsura-9 | 1 | 15 | — | — | 14 | 1.068 |
| wide64/katsura-9 | 4 | 16 | — | — | 15 | 1.061 |
| wide64/katsura-9 | 8 | 16 | — | — | 19 | 0.853 |
| wide64/katsura-9 | 16 | 16 | 19 | 0.843 | 19 | 0.857 |
| wide64/noon-8 | 16 | 96 | 119 | 0.810 | 96 | 1.005 |

## T7 / §9.1 correctness

| row | order | digests (all arms) | ad = f4 | references agreeing | certified |
|---|---|---:|---|---|---|
| gf32003/mq-random-10 | grevlex | 1 | yes | groebner-rs =, Singular = | yes |
| gf32003/mq-random-10 | grlex | 1 | yes | groebner-rs =, Singular = | yes |
| goldilocks/cyclic-7 | grevlex | 1 | yes | groebner-rs = | yes |
| goldilocks/cyclic-7 | grlex | 1 | yes | groebner-rs = | yes |
| goldilocks/katsura-11 | grevlex | 1 | yes | groebner-rs = | yes |
| goldilocks/katsura-11 | grlex | 1 | NO | groebner-rs ≠ | NO |
| goldilocks/katsura-4 | grevlex | 1 | yes | groebner-rs = | yes |
| goldilocks/katsura-4 | grlex | 1 | yes | groebner-rs = | yes |
| goldilocks/mq-random-10 | grevlex | 1 | yes | groebner-rs = | yes |
| goldilocks/mq-random-10 | grlex | 1 | yes | groebner-rs = | yes |
| goldilocks/mq-random-11 | grevlex | 1 | yes | groebner-rs =, grobx certified (M31) = | yes |
| goldilocks/mq-random-11 | grlex | 1 | NO | groebner-rs ≠ | NO |
| goldilocks/noon-7 | grevlex | 1 | yes | groebner-rs = | yes |
| goldilocks/noon-7 | grlex | 1 | yes | groebner-rs = | yes |
| m31/eco-11 | grevlex | 1 | yes | groebner-rs =, Singular = | yes |
| m31/eco-11 | grlex | 1 | yes | groebner-rs =, Singular = | yes |
| m31/katsura-10 | grevlex | 1 | yes | groebner-rs =, Singular = | yes |
| m31/katsura-10 | grlex | 1 | yes | groebner-rs =, Singular = | yes |
| m31/mq-random-10 | grevlex | 1 | yes | groebner-rs =, Singular = | yes |
| m31/mq-random-10 | grlex | 1 | yes | groebner-rs =, Singular = | yes |
| wide64/cyclic-7 | grevlex | 1 | yes | groebner-rs =, grobx certified (M31) = | yes |
| wide64/cyclic-7 | grlex | 1 | yes | groebner-rs = | yes |
| wide64/eco-12 | grevlex | 1 | yes | groebner-rs =, grobx certified (M31) = | yes |
| wide64/eco-12 | grlex | 1 | yes | groebner-rs = | yes |
| wide64/katsura-11 | grevlex | 1 | yes | groebner-rs =, grobx certified (M31) = | yes |
| wide64/katsura-11 | grlex | 1 | NO | groebner-rs ≠ | NO |
| wide64/katsura-4 | grevlex | 1 | yes | groebner-rs = | yes |
| wide64/katsura-4 | grlex | 1 | yes | groebner-rs = | yes |
| wide64/katsura-9 | grevlex | 1 | yes | groebner-rs = | yes |
| wide64/katsura-9 | grlex | 1 | NO | groebner-rs ≠ | NO |
| wide64/noon-8 | grevlex | 1 | yes | groebner-rs = | yes |
| wide64/noon-8 | grlex | 1 | yes | groebner-rs = | yes |

## T8 behaviour

Thread high-water: 327 adaptive children; worst peak minus cap 9; over the cap: [('goldilocks/cyclic-7', 'grevlex', 2, 3), ('goldilocks/cyclic-7', 'grevlex', 4, 5), ('goldilocks/cyclic-7', 'grevlex', 9, 10), ('wide64/cyclic-7', 'grevlex', 2, 3), ('wide64/cyclic-7', 'grevlex', 3, 4), ('wide64/cyclic-7', 'grevlex', 5, 6), ('goldilocks/mq-random-10', 'grevlex', 4, 5), ('goldilocks/mq-random-10', 'grevlex', 15, 16), ('m31/katsura-10', 'grevlex', 7, 8), ('wide64/eco-12', 'grlex', 4, 5), ('goldilocks/cyclic-7', 'grlex', 8, 9), ('wide64/cyclic-7', 'grlex', 4, 5), ('wide64/cyclic-7', 'grlex', 8, 9), ('goldilocks/mq-random-10', 'grlex', 8, 9), ('m31/katsura-10', 'grlex', 8, 9), ('m31/eco-11', 'grlex', 16, 25)]
1 s wall budget, wide64/eco-12, 1 w: 'stopped: the computation did not finish within 1000 ms, and had reached degree 9 after 1046 ms', process wall 1059 ms
1 s wall budget, wide64/eco-12, 16 w: 'stopped: the computation did not finish within 1000 ms, and had reached degree 12 after 1020 ms', process wall 1036 ms
1 s wall budget, goldilocks/mq-random-11, 1 w: 'stopped: the computation did not finish within 1000 ms, and had reached degree 8 after 1351 ms', process wall 1365 ms
1 s wall budget, goldilocks/mq-random-11, 16 w: 'stopped: the computation did not finish within 1000 ms: final interreduction had reduced 0 of 767 basis elements after 1023 ms', process wall 1034 ms

## T9 dispatch cost

n = 890: max 6.9 µs (wide64/katsura-9, 1 w); median 1.0 µs; worst share of wall on rows ≥ 50 ms 0.0021%

## Children

Incomplete children: 27 [('check', 'gf32003/mq-random-10', 'ad.grlex:1', 0, 0, 'stopped: the computation did not finish within 180000 ms, and had reached degree 14 after 180246 ms'), ('check', 'm31/mq-random-10', 'ad.grlex:1', 0, 0, 'stopped: the computation did not finish within 180000 ms, and had reached degree 14 after 180385 ms'), ('check', 'wide64/eco-12', 'ad.grlex:1', 0, 0, 'stopped: the computation did not finish within 180000 ms, and had reached degree 12 after 187326 ms'), ('check', 'goldilocks/katsura-11', 'ad.grlex:1', 0, -2, None), ('check', 'goldilocks/katsura-11', 'ad.grlex:4', 0, -2, None), ('check', 'goldilocks/katsura-11', 'ad.grlex:8', 0, -2, None), ('check', 'goldilocks/katsura-11', 'ad.grlex:16', 0, -2, None), ('check', 'goldilocks/katsura-11', 'adc.grlex:16', 0, -2, None), ('check', 'wide64/katsura-11', 'ad.grlex:1', 0, -2, None), ('check', 'wide64/katsura-11', 'ad.grlex:4', 0, -2, None)]
Children started at load > 4.0: 220 [('dev', 0, 'gf32003/mq-random-10', 'f4:1', 12.1), ('dev', 0, 'gf32003/mq-random-10', 'ad:1', 12.1), ('dev', 0, 'gf32003/mq-random-10', 'f4:4', 11.3), ('dev', 0, 'gf32003/mq-random-10', 'ad:4', 10.6), ('dev', 0, 'gf32003/mq-random-10', 'f4:8', 10.6), ('dev', 0, 'gf32003/mq-random-10', 'ad:8', 9.7), ('dev', 0, 'gf32003/mq-random-10', 'f4:16', 9.3), ('dev', 0, 'gf32003/mq-random-10', 'ad:16', 9.3), ('dev', 0, 'm31/mq-random-10', 'f4:1', 8.9), ('dev', 0, 'm31/mq-random-10', 'ad:1', 8.2)]
Imprecise gated cells (extension candidates): []

## Verdicts

- T3: pass
- T4: FAIL
- T5: pass
- T6: pass
- T7: FAIL
- T8: FAIL
- T9: pass
- complete: FAIL
- held-out: pass
