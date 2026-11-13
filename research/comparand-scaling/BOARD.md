# Comparand scaling cohorts (#739)

Generated from hash-bound retained attempts; no solver is invoked by replay.
Whole-process, hot-call, certification and diagnostic observations are separate configurations.

## native-resume-v1.json.gz

# Comparand worker cohorts (#739)

**Measured at:** `2f6616261efe6b600cdcddb0e291071352acbc01`.

Full reduced-basis process wall; exact reference checks follow timing. Diagnostic hot-region ticks are separate.
Unverified completions retain raw wall observations but no timing ratios; limits/capabilities remain visible. Julia deterministic backend; Rust randomized native backend.
S(p)/E(p) also require both process walls above twice the corresponding Katsura-4 startup control.

| Field/input | Engine | Workers | Complete/planned (verified) | Wall median s | Process CPU median s | RSS max MiB | S(p) | E(p) | Status |
|---|---|---:|---:|---:|---:|---:|---:|---:|---|
| 32003/katsura-4 | msolve | 1 | 3/3 (3) | 0.0063 [0.0062,0.0065] | 0.0041 | 5.14 | — | — | verified |
| 32003/katsura-4 | msolve | 2 | 3/3 (3) | 0.0064 [0.0062,0.0065] | 0.0049 | 5.11 | — | — | verified |
| 32003/katsura-4 | msolve | 4 | 3/3 (3) | 0.0062 [0.0062,0.0065] | 0.0066 | 5.16 | — | — | verified |
| 32003/katsura-4 | msolve | 8 | 3/3 (3) | 0.0062 [0.0062,0.0065] | 0.0104 | 5.16 | — | — | verified |
| 32003/katsura-4 | msolve | 16 | 3/3 (3) | 0.0116 [0.0063,0.0125] | 0.0209 | 5.15 | — | — | verified |
| 32003/katsura-4 | msolve | 32 | 3/3 (3) | 0.0119 [0.0116,0.1302] | 0.0481 | 8.05 | — | — | verified |
| 32003/katsura-4 | groebner-rs | 1 | 3/3 (3) | 0.0065 [0.0062,0.0067] | 0.0030 | 3.05 | — | — | verified |
| 32003/katsura-4 | groebner-rs | 2 | 3/3 (3) | 0.0062 [0.0062,0.0065] | 0.0036 | 3.11 | — | — | verified |
| 32003/katsura-4 | groebner-rs | 4 | 3/3 (3) | 0.0063 [0.0062,0.0065] | 0.0041 | 3.14 | — | — | verified |
| 32003/katsura-4 | groebner-rs | 8 | 3/3 (3) | 0.0062 [0.0061,0.0065] | 0.0053 | 3.26 | — | — | verified |
| 32003/katsura-4 | groebner-rs | 16 | 3/3 (3) | 0.0062 [0.0062,0.0065] | 0.0079 | 3.44 | — | — | verified |
| 32003/katsura-4 | groebner-rs | 32 | 3/3 (3) | 0.0115 [0.0067,0.0118] | 0.0149 | 3.77 | — | — | verified |
| 32003/katsura-4 | grobx | 1 | 3/3 (3) | 0.0063 [0.0062,0.0064] | 0.0037 | 9.11 | — | — | verified |
| 32003/katsura-4 | grobx | 2 | 0/3 (0) | — | — | — | — | — | unsupported |
| 32003/katsura-4 | grobx | 4 | 0/3 (0) | — | — | — | — | — | unsupported |
| 32003/katsura-4 | grobx | 8 | 0/3 (0) | — | — | — | — | — | unsupported |
| 32003/katsura-4 | grobx | 16 | 0/3 (0) | — | — | — | — | — | unsupported |
| 32003/katsura-4 | grobx | 32 | 0/3 (0) | — | — | — | — | — | unsupported |
| 32003/katsura-4 | zeebra | 1 | 0/3 (0) | — | — | — | — | — | not-measured |
| 32003/katsura-4 | zeebra | 2 | 0/3 (0) | — | — | — | — | — | unsupported |
| 32003/katsura-4 | zeebra | 4 | 0/3 (0) | — | — | — | — | — | unsupported |
| 32003/katsura-4 | zeebra | 8 | 0/3 (0) | — | — | — | — | — | unsupported |
| 32003/katsura-4 | zeebra | 16 | 0/3 (0) | — | — | — | — | — | unsupported |
| 32003/katsura-4 | zeebra | 32 | 0/3 (0) | — | — | — | — | — | unsupported |
| 32003/mq-random-10 | msolve | 1 | 3/3 (3) | 0.2121 [0.2119,0.2211] | 0.2087 | 14.09 | 1.000 | 1.000 | verified |
| 32003/mq-random-10 | msolve | 2 | 3/3 (3) | 0.1575 [0.1503,0.1642] | 0.2671 | 14.28 | 1.347 | 0.674 | verified |
| 32003/mq-random-10 | msolve | 4 | 3/3 (3) | 0.1309 [0.1292,0.1342] | 0.3900 | 14.66 | 1.620 | 0.405 | verified |
| 32003/mq-random-10 | msolve | 8 | 3/3 (3) | 0.1168 [0.1145,0.1185] | 0.6032 | 15.06 | 1.815 | 0.227 | verified |
| 32003/mq-random-10 | msolve | 16 | 3/3 (3) | 0.6581 [0.1221,0.8797] | 8.9004 | 15.89 | 0.322 | 0.020 | verified |
| 32003/mq-random-10 | msolve | 32 | 3/3 (3) | 0.4827 [0.3773,1.3011] | 13.0936 | 17.25 | 0.439 | 0.014 | verified |
| 32003/mq-random-10 | groebner-rs | 1 | 3/3 (3) | 0.1169 [0.1168,0.1250] | 0.1135 | 23.74 | 1.000 | 1.000 | verified |
| 32003/mq-random-10 | groebner-rs | 2 | 3/3 (3) | 0.0984 [0.0948,0.1000] | 0.1344 | 25.47 | 1.188 | 0.594 | verified |
| 32003/mq-random-10 | groebner-rs | 4 | 3/3 (3) | 0.0891 [0.0881,0.0926] | 0.1675 | 27.02 | 1.312 | 0.328 | verified |
| 32003/mq-random-10 | groebner-rs | 8 | 3/3 (3) | 0.0882 [0.0873,0.0889] | 0.2172 | 30.13 | 1.325 | 0.166 | verified |
| 32003/mq-random-10 | groebner-rs | 16 | 3/3 (3) | 0.1006 [0.0987,0.1111] | 0.3021 | 31.70 | 1.162 | 0.073 | verified |
| 32003/mq-random-10 | groebner-rs | 32 | 3/3 (3) | 0.1248 [0.1164,0.1313] | 0.6047 | 35.22 | 0.937 | 0.029 | verified |
| 32003/mq-random-10 | grobx | 1 | 3/3 (3) | 0.3323 [0.3309,0.3332] | 0.3262 | 17.99 | 1.000 | 1.000 | verified |
| 32003/mq-random-10 | grobx | 2 | 0/3 (0) | — | — | — | — | — | unsupported |
| 32003/mq-random-10 | grobx | 4 | 0/3 (0) | — | — | — | — | — | unsupported |
| 32003/mq-random-10 | grobx | 8 | 0/3 (0) | — | — | — | — | — | unsupported |
| 32003/mq-random-10 | grobx | 16 | 0/3 (0) | — | — | — | — | — | unsupported |
| 32003/mq-random-10 | grobx | 32 | 0/3 (0) | — | — | — | — | — | unsupported |
| 32003/mq-random-10 | zeebra | 1 | 0/3 (0) | — | — | — | — | — | not-measured |
| 32003/mq-random-10 | zeebra | 2 | 0/3 (0) | — | — | — | — | — | unsupported |
| 32003/mq-random-10 | zeebra | 4 | 0/3 (0) | — | — | — | — | — | unsupported |
| 32003/mq-random-10 | zeebra | 8 | 0/3 (0) | — | — | — | — | — | unsupported |
| 32003/mq-random-10 | zeebra | 16 | 0/3 (0) | — | — | — | — | — | unsupported |
| 32003/mq-random-10 | zeebra | 32 | 0/3 (0) | — | — | — | — | — | unsupported |
| 32003/katsura-11 | msolve | 1 | 3/3 (0) | 1.3987 [1.3948,1.4005] | 1.3872 | 23.67 | — | — | complete |
| 32003/katsura-11 | msolve | 2 | 3/3 (0) | 0.9117 [0.9112,0.9130] | 1.5046 | 23.80 | — | — | complete |
| 32003/katsura-11 | msolve | 4 | 3/3 (0) | 0.6761 [0.6712,0.6800] | 1.7322 | 24.25 | — | — | complete |
| 32003/katsura-11 | msolve | 8 | 3/3 (0) | 0.5797 [0.5781,0.5881] | 2.2063 | 25.09 | — | — | complete |
| 32003/katsura-11 | msolve | 16 | 3/3 (0) | 1.2545 [0.6056,1.3337] | 13.1374 | 25.64 | — | — | complete |
| 32003/katsura-11 | msolve | 32 | 3/3 (0) | 0.7875 [0.7759,1.3332] | 12.5335 | 27.67 | — | — | complete |
| 32003/katsura-11 | groebner-rs | 1 | 3/3 (0) | 0.4721 [0.4665,0.4779] | 0.4664 | 75.85 | — | — | complete |
| 32003/katsura-11 | groebner-rs | 2 | 3/3 (0) | 0.3536 [0.3506,0.3563] | 0.5014 | 78.64 | — | — | complete |
| 32003/katsura-11 | groebner-rs | 4 | 3/3 (0) | 0.2955 [0.2896,0.3004] | 0.5557 | 84.25 | — | — | complete |
| 32003/katsura-11 | groebner-rs | 8 | 3/3 (0) | 0.2893 [0.2892,0.2894] | 0.7088 | 86.58 | — | — | complete |
| 32003/katsura-11 | groebner-rs | 16 | 3/3 (0) | 0.3118 [0.3092,0.3176] | 0.9005 | 92.50 | — | — | complete |
| 32003/katsura-11 | groebner-rs | 32 | 3/3 (0) | 0.3617 [0.3599,0.3636] | 1.6866 | 98.44 | — | — | complete |
| 32003/katsura-11 | grobx | 1 | 3/3 (0) | 0.1251 [0.1237,0.1286] | 0.1212 | 32.42 | — | — | complete |
| 32003/katsura-11 | grobx | 2 | 0/3 (0) | — | — | — | — | — | unsupported |
| 32003/katsura-11 | grobx | 4 | 0/3 (0) | — | — | — | — | — | unsupported |
| 32003/katsura-11 | grobx | 8 | 0/3 (0) | — | — | — | — | — | unsupported |
| 32003/katsura-11 | grobx | 16 | 0/3 (0) | — | — | — | — | — | unsupported |
| 32003/katsura-11 | grobx | 32 | 0/3 (0) | — | — | — | — | — | unsupported |
| 32003/katsura-11 | zeebra | 1 | 0/3 (0) | — | — | — | — | — | not-measured |
| 32003/katsura-11 | zeebra | 2 | 0/3 (0) | — | — | — | — | — | unsupported |
| 32003/katsura-11 | zeebra | 4 | 0/3 (0) | — | — | — | — | — | unsupported |
| 32003/katsura-11 | zeebra | 8 | 0/3 (0) | — | — | — | — | — | unsupported |
| 32003/katsura-11 | zeebra | 16 | 0/3 (0) | — | — | — | — | — | unsupported |
| 32003/katsura-11 | zeebra | 32 | 0/3 (0) | — | — | — | — | — | unsupported |
| 32003/cyclic-7 | msolve | 1 | 3/3 (3) | 0.0825 [0.0800,0.0833] | 0.0774 | 10.86 | 1.000 | 1.000 | verified |
| 32003/cyclic-7 | msolve | 2 | 3/3 (3) | 0.0717 [0.0714,0.0733] | 0.1328 | 10.87 | 1.151 | 0.575 | verified |
| 32003/cyclic-7 | msolve | 4 | 3/3 (3) | 0.0718 [0.0676,0.0722] | 0.2437 | 11.33 | 1.148 | 0.287 | verified |
| 32003/cyclic-7 | msolve | 8 | 3/3 (3) | 0.0720 [0.0718,0.0734] | 0.4885 | 11.57 | 1.146 | 0.143 | verified |
| 32003/cyclic-7 | msolve | 16 | 3/3 (3) | 0.1910 [0.0839,0.5115] | 2.7201 | 12.35 | 0.432 | 0.027 | verified |
| 32003/cyclic-7 | msolve | 32 | 3/3 (3) | 0.0843 [0.0834,0.2353] | 2.3156 | 13.28 | 0.978 | 0.031 | verified |
| 32003/cyclic-7 | groebner-rs | 1 | 3/3 (3) | 0.0554 [0.0537,0.0567] | 0.0511 | 11.90 | 1.000 | 1.000 | verified |
| 32003/cyclic-7 | groebner-rs | 2 | 3/3 (3) | 0.0457 [0.0443,0.0478] | 0.0591 | 12.10 | 1.212 | 0.606 | verified |
| 32003/cyclic-7 | groebner-rs | 4 | 3/3 (3) | 0.0455 [0.0447,0.0481] | 0.0812 | 12.48 | 1.217 | 0.304 | verified |
| 32003/cyclic-7 | groebner-rs | 8 | 3/3 (3) | 0.0453 [0.0445,0.0483] | 0.1153 | 13.00 | 1.222 | 0.153 | verified |
| 32003/cyclic-7 | groebner-rs | 16 | 3/3 (3) | 0.0568 [0.0556,0.0598] | 0.2784 | 13.73 | 0.974 | 0.061 | verified |
| 32003/cyclic-7 | groebner-rs | 32 | 3/3 (3) | 0.0721 [0.0719,0.0737] | 0.4615 | 16.34 | 0.768 | 0.024 | verified |
| 32003/cyclic-7 | grobx | 1 | 3/3 (3) | 0.0554 [0.0532,0.0565] | 0.0515 | 15.36 | 1.000 | 1.000 | verified |
| 32003/cyclic-7 | grobx | 2 | 0/3 (0) | — | — | — | — | — | unsupported |
| 32003/cyclic-7 | grobx | 4 | 0/3 (0) | — | — | — | — | — | unsupported |
| 32003/cyclic-7 | grobx | 8 | 0/3 (0) | — | — | — | — | — | unsupported |
| 32003/cyclic-7 | grobx | 16 | 0/3 (0) | — | — | — | — | — | unsupported |
| 32003/cyclic-7 | grobx | 32 | 0/3 (0) | — | — | — | — | — | unsupported |
| 32003/cyclic-7 | zeebra | 1 | 0/3 (0) | — | — | — | — | — | not-measured |
| 32003/cyclic-7 | zeebra | 2 | 0/3 (0) | — | — | — | — | — | unsupported |
| 32003/cyclic-7 | zeebra | 4 | 0/3 (0) | — | — | — | — | — | unsupported |
| 32003/cyclic-7 | zeebra | 8 | 0/3 (0) | — | — | — | — | — | unsupported |
| 32003/cyclic-7 | zeebra | 16 | 0/3 (0) | — | — | — | — | — | unsupported |
| 32003/cyclic-7 | zeebra | 32 | 0/3 (0) | — | — | — | — | — | unsupported |
| 32003/cyclic-10 | msolve | 1 | 0/3 (0) | — | — | — | — | — | skipped-by-gate, stopped-by-limit |
| 32003/cyclic-10 | msolve | 2 | 0/3 (0) | — | — | — | — | — | skipped-by-gate |
| 32003/cyclic-10 | msolve | 4 | 0/3 (0) | — | — | — | — | — | skipped-by-gate |
| 32003/cyclic-10 | msolve | 8 | 0/3 (0) | — | — | — | — | — | skipped-by-gate |
| 32003/cyclic-10 | msolve | 16 | 0/3 (0) | — | — | — | — | — | skipped-by-gate, stopped-by-limit |
| 32003/cyclic-10 | msolve | 32 | 0/3 (0) | — | — | — | — | — | skipped-by-gate |
| 32003/cyclic-10 | groebner-rs | 1 | 0/3 (0) | — | — | — | — | — | skipped-by-gate, stopped-by-limit |
| 32003/cyclic-10 | groebner-rs | 2 | 0/3 (0) | — | — | — | — | — | skipped-by-gate |
| 32003/cyclic-10 | groebner-rs | 4 | 0/3 (0) | — | — | — | — | — | skipped-by-gate |
| 32003/cyclic-10 | groebner-rs | 8 | 0/3 (0) | — | — | — | — | — | skipped-by-gate |
| 32003/cyclic-10 | groebner-rs | 16 | 0/3 (0) | — | — | — | — | — | skipped-by-gate, stopped-by-limit |
| 32003/cyclic-10 | groebner-rs | 32 | 0/3 (0) | — | — | — | — | — | skipped-by-gate |
| 32003/cyclic-10 | grobx | 1 | 0/3 (0) | — | — | — | — | — | skipped-by-gate, stopped-by-limit |
| 32003/cyclic-10 | grobx | 2 | 0/3 (0) | — | — | — | — | — | skipped-by-gate |
| 32003/cyclic-10 | grobx | 4 | 0/3 (0) | — | — | — | — | — | skipped-by-gate |
| 32003/cyclic-10 | grobx | 8 | 0/3 (0) | — | — | — | — | — | skipped-by-gate |
| 32003/cyclic-10 | grobx | 16 | 0/3 (0) | — | — | — | — | — | skipped-by-gate, unsupported |
| 32003/cyclic-10 | grobx | 32 | 0/3 (0) | — | — | — | — | — | skipped-by-gate |
| 32003/cyclic-10 | zeebra | 1 | 0/3 (0) | — | — | — | — | — | not-measured |
| 32003/cyclic-10 | zeebra | 2 | 0/3 (0) | — | — | — | — | — | unsupported |
| 32003/cyclic-10 | zeebra | 4 | 0/3 (0) | — | — | — | — | — | unsupported |
| 32003/cyclic-10 | zeebra | 8 | 0/3 (0) | — | — | — | — | — | unsupported |
| 32003/cyclic-10 | zeebra | 16 | 0/3 (0) | — | — | — | — | — | unsupported |
| 32003/cyclic-10 | zeebra | 32 | 0/3 (0) | — | — | — | — | — | unsupported |
| 2147483647/katsura-4 | msolve | 1 | 3/3 (3) | 0.0064 [0.0064,0.0066] | 0.0045 | 6.12 | — | — | verified |
| 2147483647/katsura-4 | msolve | 2 | 3/3 (3) | 0.0064 [0.0064,0.0067] | 0.0048 | 5.15 | — | — | verified |
| 2147483647/katsura-4 | msolve | 4 | 3/3 (3) | 0.0065 [0.0063,0.0067] | 0.0065 | 5.14 | — | — | verified |
| 2147483647/katsura-4 | msolve | 8 | 3/3 (3) | 0.0235 [0.0066,0.0302] | 0.1186 | 7.45 | — | — | verified |
| 2147483647/katsura-4 | msolve | 16 | 3/3 (3) | 0.0066 [0.0065,0.0341] | 0.0214 | 7.52 | — | — | verified |
| 2147483647/katsura-4 | msolve | 32 | 3/3 (3) | 0.0121 [0.0067,0.1116] | 0.0516 | 8.05 | — | — | verified |
| 2147483647/katsura-4 | groebner-rs | 1 | 3/3 (3) | 0.0064 [0.0063,0.0070] | 0.0032 | 3.08 | — | — | verified |
| 2147483647/katsura-4 | groebner-rs | 2 | 3/3 (3) | 0.0066 [0.0062,0.0067] | 0.0036 | 3.18 | — | — | verified |
| 2147483647/katsura-4 | groebner-rs | 4 | 3/3 (3) | 0.0065 [0.0063,0.0067] | 0.0041 | 3.12 | — | — | verified |
| 2147483647/katsura-4 | groebner-rs | 8 | 3/3 (3) | 0.0064 [0.0063,0.0067] | 0.0053 | 3.22 | — | — | verified |
| 2147483647/katsura-4 | groebner-rs | 16 | 3/3 (3) | 0.0064 [0.0062,0.0067] | 0.0084 | 3.41 | — | — | verified |
| 2147483647/katsura-4 | groebner-rs | 32 | 3/3 (3) | 0.0117 [0.0066,0.0120] | 0.0146 | 3.78 | — | — | verified |
| 2147483647/katsura-4 | grobx | 1 | 3/3 (3) | 0.0064 [0.0063,0.0066] | 0.0042 | 9.04 | — | — | verified |
| 2147483647/katsura-4 | grobx | 2 | 0/3 (0) | — | — | — | — | — | unsupported |
| 2147483647/katsura-4 | grobx | 4 | 0/3 (0) | — | — | — | — | — | unsupported |
| 2147483647/katsura-4 | grobx | 8 | 0/3 (0) | — | — | — | — | — | unsupported |
| 2147483647/katsura-4 | grobx | 16 | 0/3 (0) | — | — | — | — | — | unsupported |
| 2147483647/katsura-4 | grobx | 32 | 0/3 (0) | — | — | — | — | — | unsupported |
| 2147483647/katsura-4 | zeebra | 1 | 0/3 (0) | — | — | — | — | — | not-measured |
| 2147483647/katsura-4 | zeebra | 2 | 0/3 (0) | — | — | — | — | — | unsupported |
| 2147483647/katsura-4 | zeebra | 4 | 0/3 (0) | — | — | — | — | — | unsupported |
| 2147483647/katsura-4 | zeebra | 8 | 0/3 (0) | — | — | — | — | — | unsupported |
| 2147483647/katsura-4 | zeebra | 16 | 0/3 (0) | — | — | — | — | — | unsupported |
| 2147483647/katsura-4 | zeebra | 32 | 0/3 (0) | — | — | — | — | — | unsupported |
| 2147483647/mq-random-10 | msolve | 1 | 3/3 (3) | 0.2384 [0.2370,0.2389] | 0.2341 | 14.23 | 1.000 | 1.000 | verified |
| 2147483647/mq-random-10 | msolve | 2 | 3/3 (3) | 0.2129 [0.2050,0.2212] | 0.3782 | 14.40 | 1.120 | 0.560 | verified |
| 2147483647/mq-random-10 | msolve | 4 | 3/3 (3) | 0.1670 [0.1640,0.1737] | 0.5336 | 14.72 | 1.427 | 0.357 | verified |
| 2147483647/mq-random-10 | msolve | 8 | 3/3 (3) | 0.4615 [0.4611,0.4658] | 3.3536 | 15.25 | 0.517 | 0.065 | verified |
| 2147483647/mq-random-10 | msolve | 16 | 3/3 (3) | 0.4621 [0.1992,0.4900] | 6.1977 | 15.94 | 0.516 | 0.032 | verified |
| 2147483647/mq-random-10 | msolve | 32 | 3/3 (3) | 0.7044 [0.4597,1.2542] | 19.8274 | 17.47 | 0.338 | 0.011 | verified |
| 2147483647/mq-random-10 | groebner-rs | 1 | 3/3 (3) | 0.1552 [0.1539,0.1662] | 0.1486 | 24.55 | 1.000 | 1.000 | verified |
| 2147483647/mq-random-10 | groebner-rs | 2 | 3/3 (3) | 0.1193 [0.1135,0.1224] | 0.1680 | 23.61 | 1.301 | 0.650 | verified |
| 2147483647/mq-random-10 | groebner-rs | 4 | 3/3 (3) | 0.1027 [0.0959,0.1056] | 0.2026 | 24.74 | 1.512 | 0.378 | verified |
| 2147483647/mq-random-10 | groebner-rs | 8 | 3/3 (3) | 0.0970 [0.0956,0.0972] | 0.2546 | 26.40 | 1.600 | 0.200 | verified |
| 2147483647/mq-random-10 | groebner-rs | 16 | 3/3 (3) | 0.1077 [0.1066,0.1089] | 0.3259 | 27.95 | 1.441 | 0.090 | verified |
| 2147483647/mq-random-10 | groebner-rs | 32 | 3/3 (3) | 0.1415 [0.1339,0.1446] | 0.6999 | 30.08 | 1.097 | 0.034 | verified |
| 2147483647/mq-random-10 | grobx | 1 | 3/3 (3) | 0.1609 [0.1590,0.1612] | 0.1549 | 18.02 | 1.000 | 1.000 | verified |
| 2147483647/mq-random-10 | grobx | 2 | 0/3 (0) | — | — | — | — | — | unsupported |
| 2147483647/mq-random-10 | grobx | 4 | 0/3 (0) | — | — | — | — | — | unsupported |
| 2147483647/mq-random-10 | grobx | 8 | 0/3 (0) | — | — | — | — | — | unsupported |
| 2147483647/mq-random-10 | grobx | 16 | 0/3 (0) | — | — | — | — | — | unsupported |
| 2147483647/mq-random-10 | grobx | 32 | 0/3 (0) | — | — | — | — | — | unsupported |
| 2147483647/mq-random-10 | zeebra | 1 | 0/3 (0) | — | — | — | — | — | not-measured |
| 2147483647/mq-random-10 | zeebra | 2 | 0/3 (0) | — | — | — | — | — | unsupported |
| 2147483647/mq-random-10 | zeebra | 4 | 0/3 (0) | — | — | — | — | — | unsupported |
| 2147483647/mq-random-10 | zeebra | 8 | 0/3 (0) | — | — | — | — | — | unsupported |
| 2147483647/mq-random-10 | zeebra | 16 | 0/3 (0) | — | — | — | — | — | unsupported |
| 2147483647/mq-random-10 | zeebra | 32 | 0/3 (0) | — | — | — | — | — | unsupported |
| 2147483647/katsura-11 | msolve | 1 | 3/3 (3) | 1.5328 [1.5318,1.6127] | 1.5199 | 24.44 | 1.000 | 1.000 | verified |
| 2147483647/katsura-11 | msolve | 2 | 3/3 (3) | 1.0142 [0.9983,1.0468] | 1.6954 | 24.40 | 1.511 | 0.756 | verified |
| 2147483647/katsura-11 | msolve | 4 | 3/3 (3) | 0.7558 [0.7485,0.7629] | 2.0373 | 24.61 | 2.028 | 0.507 | verified |
| 2147483647/katsura-11 | msolve | 8 | 3/3 (3) | 0.7155 [0.7125,0.8029] | 3.2255 | 25.38 | 2.142 | 0.268 | verified |
| 2147483647/katsura-11 | msolve | 16 | 3/3 (3) | 2.7126 [2.6237,3.2052] | 35.4940 | 26.70 | 0.565 | 0.035 | verified |
| 2147483647/katsura-11 | msolve | 32 | 3/3 (3) | 1.2543 [1.1629,1.8048] | 26.4857 | 28.53 | 1.222 | 0.038 | verified |
| 2147483647/katsura-11 | groebner-rs | 1 | 3/3 (3) | 0.8100 [0.8045,0.8110] | 0.8012 | 84.12 | 1.000 | 1.000 | verified |
| 2147483647/katsura-11 | groebner-rs | 2 | 3/3 (3) | 0.5229 [0.5146,0.5352] | 0.8041 | 85.77 | 1.549 | 0.774 | verified |
| 2147483647/katsura-11 | groebner-rs | 4 | 3/3 (3) | 0.4134 [0.3983,0.4179] | 0.9095 | 90.68 | 1.959 | 0.490 | verified |
| 2147483647/katsura-11 | groebner-rs | 8 | 3/3 (3) | 0.3603 [0.3585,0.3616] | 1.0366 | 93.03 | 2.248 | 0.281 | verified |
| 2147483647/katsura-11 | groebner-rs | 16 | 3/3 (3) | 0.3794 [0.3755,0.3918] | 1.1476 | 96.82 | 2.135 | 0.133 | verified |
| 2147483647/katsura-11 | groebner-rs | 32 | 3/3 (3) | 0.4096 [0.4086,0.4100] | 1.9049 | 101.62 | 1.978 | 0.062 | verified |
| 2147483647/katsura-11 | grobx | 1 | 3/3 (3) | 0.1504 [0.1476,0.1567] | 0.1484 | 31.59 | 1.000 | 1.000 | verified |
| 2147483647/katsura-11 | grobx | 2 | 0/3 (0) | — | — | — | — | — | unsupported |
| 2147483647/katsura-11 | grobx | 4 | 0/3 (0) | — | — | — | — | — | unsupported |
| 2147483647/katsura-11 | grobx | 8 | 0/3 (0) | — | — | — | — | — | unsupported |
| 2147483647/katsura-11 | grobx | 16 | 0/3 (0) | — | — | — | — | — | unsupported |
| 2147483647/katsura-11 | grobx | 32 | 0/3 (0) | — | — | — | — | — | unsupported |
| 2147483647/katsura-11 | zeebra | 1 | 0/3 (0) | — | — | — | — | — | not-measured |
| 2147483647/katsura-11 | zeebra | 2 | 0/3 (0) | — | — | — | — | — | unsupported |
| 2147483647/katsura-11 | zeebra | 4 | 0/3 (0) | — | — | — | — | — | unsupported |
| 2147483647/katsura-11 | zeebra | 8 | 0/3 (0) | — | — | — | — | — | unsupported |
| 2147483647/katsura-11 | zeebra | 16 | 0/3 (0) | — | — | — | — | — | unsupported |
| 2147483647/katsura-11 | zeebra | 32 | 0/3 (0) | — | — | — | — | — | unsupported |
| 2147483647/cyclic-7 | msolve | 1 | 3/3 (0) | 0.0865 [0.0845,0.0957] | 0.0852 | 10.66 | — | — | complete |
| 2147483647/cyclic-7 | msolve | 2 | 3/3 (0) | 0.0814 [0.0732,0.0850] | 0.1437 | 11.12 | — | — | complete |
| 2147483647/cyclic-7 | msolve | 4 | 3/3 (0) | 0.0756 [0.0735,0.0786] | 0.2627 | 11.60 | — | — | complete |
| 2147483647/cyclic-7 | msolve | 8 | 3/3 (0) | 0.0749 [0.0737,0.0804] | 0.5221 | 12.05 | — | — | complete |
| 2147483647/cyclic-7 | msolve | 16 | 3/3 (0) | 0.0901 [0.0862,0.6716] | 1.2220 | 12.33 | — | — | complete |
| 2147483647/cyclic-7 | msolve | 32 | 3/3 (0) | 0.0963 [0.0920,0.5906] | 2.5631 | 12.76 | — | — | complete |
| 2147483647/cyclic-7 | groebner-rs | 1 | 3/3 (0) | 0.0901 [0.0859,0.0966] | 0.0866 | 12.59 | — | — | complete |
| 2147483647/cyclic-7 | groebner-rs | 2 | 3/3 (0) | 0.0731 [0.0730,0.0746] | 0.0991 | 12.35 | — | — | complete |
| 2147483647/cyclic-7 | groebner-rs | 4 | 3/3 (0) | 0.0579 [0.0570,0.0605] | 0.1131 | 14.01 | — | — | complete |
| 2147483647/cyclic-7 | groebner-rs | 8 | 3/3 (0) | 0.0523 [0.0510,0.0548] | 0.1459 | 12.99 | — | — | complete |
| 2147483647/cyclic-7 | groebner-rs | 16 | 3/3 (0) | 0.0625 [0.0609,0.0632] | 0.2155 | 13.34 | — | — | complete |
| 2147483647/cyclic-7 | groebner-rs | 32 | 3/3 (0) | 0.0816 [0.0792,0.0856] | 0.4980 | 15.62 | — | — | complete |
| 2147483647/cyclic-7 | grobx | 1 | 3/3 (0) | 0.0404 [0.0403,0.0430] | 0.0341 | 15.23 | — | — | complete |
| 2147483647/cyclic-7 | grobx | 2 | 0/3 (0) | — | — | — | — | — | unsupported |
| 2147483647/cyclic-7 | grobx | 4 | 0/3 (0) | — | — | — | — | — | unsupported |
| 2147483647/cyclic-7 | grobx | 8 | 0/3 (0) | — | — | — | — | — | unsupported |
| 2147483647/cyclic-7 | grobx | 16 | 0/3 (0) | — | — | — | — | — | unsupported |
| 2147483647/cyclic-7 | grobx | 32 | 0/3 (0) | — | — | — | — | — | unsupported |
| 2147483647/cyclic-7 | zeebra | 1 | 0/3 (0) | — | — | — | — | — | not-measured |
| 2147483647/cyclic-7 | zeebra | 2 | 0/3 (0) | — | — | — | — | — | unsupported |
| 2147483647/cyclic-7 | zeebra | 4 | 0/3 (0) | — | — | — | — | — | unsupported |
| 2147483647/cyclic-7 | zeebra | 8 | 0/3 (0) | — | — | — | — | — | unsupported |
| 2147483647/cyclic-7 | zeebra | 16 | 0/3 (0) | — | — | — | — | — | unsupported |
| 2147483647/cyclic-7 | zeebra | 32 | 0/3 (0) | — | — | — | — | — | unsupported |
| 2147483647/cyclic-10 | msolve | 1 | 0/3 (0) | — | — | — | — | — | skipped-by-gate, stopped-by-limit |
| 2147483647/cyclic-10 | msolve | 2 | 0/3 (0) | — | — | — | — | — | skipped-by-gate |
| 2147483647/cyclic-10 | msolve | 4 | 0/3 (0) | — | — | — | — | — | skipped-by-gate |
| 2147483647/cyclic-10 | msolve | 8 | 0/3 (0) | — | — | — | — | — | skipped-by-gate |
| 2147483647/cyclic-10 | msolve | 16 | 0/3 (0) | — | — | — | — | — | skipped-by-gate, stopped-by-limit |
| 2147483647/cyclic-10 | msolve | 32 | 0/3 (0) | — | — | — | — | — | skipped-by-gate |
| 2147483647/cyclic-10 | groebner-rs | 1 | 0/3 (0) | — | — | — | — | — | skipped-by-gate, stopped-by-limit |
| 2147483647/cyclic-10 | groebner-rs | 2 | 0/3 (0) | — | — | — | — | — | skipped-by-gate |
| 2147483647/cyclic-10 | groebner-rs | 4 | 0/3 (0) | — | — | — | — | — | skipped-by-gate |
| 2147483647/cyclic-10 | groebner-rs | 8 | 0/3 (0) | — | — | — | — | — | skipped-by-gate |
| 2147483647/cyclic-10 | groebner-rs | 16 | 0/3 (0) | — | — | — | — | — | skipped-by-gate, stopped-by-limit |
| 2147483647/cyclic-10 | groebner-rs | 32 | 0/3 (0) | — | — | — | — | — | skipped-by-gate |
| 2147483647/cyclic-10 | grobx | 1 | 0/3 (0) | — | — | — | — | — | skipped-by-gate, stopped-by-limit |
| 2147483647/cyclic-10 | grobx | 2 | 0/3 (0) | — | — | — | — | — | skipped-by-gate |
| 2147483647/cyclic-10 | grobx | 4 | 0/3 (0) | — | — | — | — | — | skipped-by-gate |
| 2147483647/cyclic-10 | grobx | 8 | 0/3 (0) | — | — | — | — | — | skipped-by-gate |
| 2147483647/cyclic-10 | grobx | 16 | 0/3 (0) | — | — | — | — | — | skipped-by-gate, unsupported |
| 2147483647/cyclic-10 | grobx | 32 | 0/3 (0) | — | — | — | — | — | skipped-by-gate |
| 2147483647/cyclic-10 | zeebra | 1 | 0/3 (0) | — | — | — | — | — | not-measured |
| 2147483647/cyclic-10 | zeebra | 2 | 0/3 (0) | — | — | — | — | — | unsupported |
| 2147483647/cyclic-10 | zeebra | 4 | 0/3 (0) | — | — | — | — | — | unsupported |
| 2147483647/cyclic-10 | zeebra | 8 | 0/3 (0) | — | — | — | — | — | unsupported |
| 2147483647/cyclic-10 | zeebra | 16 | 0/3 (0) | — | — | — | — | — | unsupported |
| 2147483647/cyclic-10 | zeebra | 32 | 0/3 (0) | — | — | — | — | — | unsupported |
| wide64/katsura-4 | msolve | 1 | 0/3 (0) | — | — | — | — | — | unsupported |
| wide64/katsura-4 | msolve | 2 | 0/3 (0) | — | — | — | — | — | unsupported |
| wide64/katsura-4 | msolve | 4 | 0/3 (0) | — | — | — | — | — | unsupported |
| wide64/katsura-4 | msolve | 8 | 0/3 (0) | — | — | — | — | — | unsupported |
| wide64/katsura-4 | msolve | 16 | 0/3 (0) | — | — | — | — | — | unsupported |
| wide64/katsura-4 | msolve | 32 | 0/3 (0) | — | — | — | — | — | unsupported |
| wide64/katsura-4 | groebner-rs | 1 | 3/3 (0) | 0.0064 [0.0062,0.0067] | 0.0034 | 3.09 | — | — | complete |
| wide64/katsura-4 | groebner-rs | 2 | 3/3 (0) | 0.0066 [0.0061,0.0067] | 0.0038 | 3.08 | — | — | complete |
| wide64/katsura-4 | groebner-rs | 4 | 3/3 (0) | 0.0064 [0.0062,0.0067] | 0.0043 | 3.12 | — | — | complete |
| wide64/katsura-4 | groebner-rs | 8 | 3/3 (0) | 0.0064 [0.0061,0.0066] | 0.0054 | 3.26 | — | — | complete |
| wide64/katsura-4 | groebner-rs | 16 | 3/3 (0) | 0.0064 [0.0061,0.0068] | 0.0087 | 3.45 | — | — | complete |
| wide64/katsura-4 | groebner-rs | 32 | 3/3 (0) | 0.0064 [0.0062,0.0067] | 0.0139 | 3.77 | — | — | complete |
| wide64/katsura-4 | grobx | 1 | 3/3 (0) | 0.0064 [0.0061,0.0068] | 0.0038 | 9.18 | — | — | complete |
| wide64/katsura-4 | grobx | 2 | 0/3 (0) | — | — | — | — | — | unsupported |
| wide64/katsura-4 | grobx | 4 | 0/3 (0) | — | — | — | — | — | unsupported |
| wide64/katsura-4 | grobx | 8 | 0/3 (0) | — | — | — | — | — | unsupported |
| wide64/katsura-4 | grobx | 16 | 0/3 (0) | — | — | — | — | — | unsupported |
| wide64/katsura-4 | grobx | 32 | 0/3 (0) | — | — | — | — | — | unsupported |
| wide64/katsura-4 | zeebra | 1 | 0/3 (0) | — | — | — | — | — | not-measured |
| wide64/katsura-4 | zeebra | 2 | 0/3 (0) | — | — | — | — | — | unsupported |
| wide64/katsura-4 | zeebra | 4 | 0/3 (0) | — | — | — | — | — | unsupported |
| wide64/katsura-4 | zeebra | 8 | 0/3 (0) | — | — | — | — | — | unsupported |
| wide64/katsura-4 | zeebra | 16 | 0/3 (0) | — | — | — | — | — | unsupported |
| wide64/katsura-4 | zeebra | 32 | 0/3 (0) | — | — | — | — | — | unsupported |
| wide64/katsura-9 | msolve | 1 | 0/3 (0) | — | — | — | — | — | unsupported |
| wide64/katsura-9 | msolve | 2 | 0/3 (0) | — | — | — | — | — | unsupported |
| wide64/katsura-9 | msolve | 4 | 0/3 (0) | — | — | — | — | — | unsupported |
| wide64/katsura-9 | msolve | 8 | 0/3 (0) | — | — | — | — | — | unsupported |
| wide64/katsura-9 | msolve | 16 | 0/3 (0) | — | — | — | — | — | unsupported |
| wide64/katsura-9 | msolve | 32 | 0/3 (0) | — | — | — | — | — | unsupported |
| wide64/katsura-9 | groebner-rs | 1 | 3/3 (0) | 0.0725 [0.0707,0.0760] | 0.0692 | 9.48 | — | — | complete |
| wide64/katsura-9 | groebner-rs | 2 | 3/3 (0) | 0.0497 [0.0492,0.0527] | 0.0738 | 9.72 | — | — | complete |
| wide64/katsura-9 | groebner-rs | 4 | 3/3 (0) | 0.0438 [0.0432,0.0466] | 0.0869 | 11.29 | — | — | complete |
| wide64/katsura-9 | groebner-rs | 8 | 3/3 (0) | 0.0387 [0.0376,0.0411] | 0.1056 | 12.14 | — | — | complete |
| wide64/katsura-9 | groebner-rs | 16 | 3/3 (0) | 0.0467 [0.0438,0.0489] | 0.1400 | 12.80 | — | — | complete |
| wide64/katsura-9 | groebner-rs | 32 | 3/3 (0) | 0.0556 [0.0545,0.0582] | 0.2985 | 13.68 | — | — | complete |
| wide64/katsura-9 | grobx | 1 | 3/3 (0) | 0.0236 [0.0224,0.0250] | 0.0187 | 12.66 | — | — | complete |
| wide64/katsura-9 | grobx | 2 | 0/3 (0) | — | — | — | — | — | unsupported |
| wide64/katsura-9 | grobx | 4 | 0/3 (0) | — | — | — | — | — | unsupported |
| wide64/katsura-9 | grobx | 8 | 0/3 (0) | — | — | — | — | — | unsupported |
| wide64/katsura-9 | grobx | 16 | 0/3 (0) | — | — | — | — | — | unsupported |
| wide64/katsura-9 | grobx | 32 | 0/3 (0) | — | — | — | — | — | unsupported |
| wide64/katsura-9 | zeebra | 1 | 0/3 (0) | — | — | — | — | — | not-measured |
| wide64/katsura-9 | zeebra | 2 | 0/3 (0) | — | — | — | — | — | unsupported |
| wide64/katsura-9 | zeebra | 4 | 0/3 (0) | — | — | — | — | — | unsupported |
| wide64/katsura-9 | zeebra | 8 | 0/3 (0) | — | — | — | — | — | unsupported |
| wide64/katsura-9 | zeebra | 16 | 0/3 (0) | — | — | — | — | — | unsupported |
| wide64/katsura-9 | zeebra | 32 | 0/3 (0) | — | — | — | — | — | unsupported |
| wide64/cyclic-7 | msolve | 1 | 0/3 (0) | — | — | — | — | — | unsupported |
| wide64/cyclic-7 | msolve | 2 | 0/3 (0) | — | — | — | — | — | unsupported |
| wide64/cyclic-7 | msolve | 4 | 0/3 (0) | — | — | — | — | — | unsupported |
| wide64/cyclic-7 | msolve | 8 | 0/3 (0) | — | — | — | — | — | unsupported |
| wide64/cyclic-7 | msolve | 16 | 0/3 (0) | — | — | — | — | — | unsupported |
| wide64/cyclic-7 | msolve | 32 | 0/3 (0) | — | — | — | — | — | unsupported |
| wide64/cyclic-7 | groebner-rs | 1 | 3/3 (0) | 0.1780 [0.1765,0.1813] | 0.1734 | 14.48 | — | — | complete |
| wide64/cyclic-7 | groebner-rs | 2 | 3/3 (0) | 0.1096 [0.1084,0.1142] | 0.1700 | 15.11 | — | — | complete |
| wide64/cyclic-7 | groebner-rs | 4 | 3/3 (0) | 0.0847 [0.0813,0.0873] | 0.1978 | 13.79 | — | — | complete |
| wide64/cyclic-7 | groebner-rs | 8 | 3/3 (0) | 0.0736 [0.0713,0.0751] | 0.2221 | 15.96 | — | — | complete |
| wide64/cyclic-7 | groebner-rs | 16 | 3/3 (0) | 0.0816 [0.0787,0.0823] | 0.2901 | 16.81 | — | — | complete |
| wide64/cyclic-7 | groebner-rs | 32 | 3/3 (0) | 0.0985 [0.0928,0.1030] | 0.5724 | 17.15 | — | — | complete |
| wide64/cyclic-7 | grobx | 1 | 3/3 (0) | 0.1193 [0.1155,0.1199] | 0.1137 | 13.46 | — | — | complete |
| wide64/cyclic-7 | grobx | 2 | 0/3 (0) | — | — | — | — | — | unsupported |
| wide64/cyclic-7 | grobx | 4 | 0/3 (0) | — | — | — | — | — | unsupported |
| wide64/cyclic-7 | grobx | 8 | 0/3 (0) | — | — | — | — | — | unsupported |
| wide64/cyclic-7 | grobx | 16 | 0/3 (0) | — | — | — | — | — | unsupported |
| wide64/cyclic-7 | grobx | 32 | 0/3 (0) | — | — | — | — | — | unsupported |
| wide64/cyclic-7 | zeebra | 1 | 0/3 (0) | — | — | — | — | — | not-measured |
| wide64/cyclic-7 | zeebra | 2 | 0/3 (0) | — | — | — | — | — | unsupported |
| wide64/cyclic-7 | zeebra | 4 | 0/3 (0) | — | — | — | — | — | unsupported |
| wide64/cyclic-7 | zeebra | 8 | 0/3 (0) | — | — | — | — | — | unsupported |
| wide64/cyclic-7 | zeebra | 16 | 0/3 (0) | — | — | — | — | — | unsupported |
| wide64/cyclic-7 | zeebra | 32 | 0/3 (0) | — | — | — | — | — | unsupported |
| wide64/mq-random-10 | msolve | 1 | 0/3 (0) | — | — | — | — | — | unsupported |
| wide64/mq-random-10 | msolve | 2 | 0/3 (0) | — | — | — | — | — | unsupported |
| wide64/mq-random-10 | msolve | 4 | 0/3 (0) | — | — | — | — | — | unsupported |
| wide64/mq-random-10 | msolve | 8 | 0/3 (0) | — | — | — | — | — | unsupported |
| wide64/mq-random-10 | msolve | 16 | 0/3 (0) | — | — | — | — | — | unsupported |
| wide64/mq-random-10 | msolve | 32 | 0/3 (0) | — | — | — | — | — | unsupported |
| wide64/mq-random-10 | groebner-rs | 1 | 3/3 (0) | 1.5881 [1.5787,1.6081] | 1.5770 | 83.14 | — | — | complete |
| wide64/mq-random-10 | groebner-rs | 2 | 3/3 (0) | 0.9257 [0.9072,0.9414] | 1.6217 | 84.75 | — | — | complete |
| wide64/mq-random-10 | groebner-rs | 4 | 3/3 (0) | 0.6297 [0.6243,0.6339] | 1.7646 | 87.37 | — | — | complete |
| wide64/mq-random-10 | groebner-rs | 8 | 3/3 (0) | 0.4778 [0.4778,0.4781] | 1.9240 | 88.98 | — | — | complete |
| wide64/mq-random-10 | groebner-rs | 16 | 3/3 (0) | 0.4903 [0.4848,0.4948] | 1.9868 | 93.65 | — | — | complete |
| wide64/mq-random-10 | groebner-rs | 32 | 3/3 (0) | 0.4612 [0.4511,0.4667] | 2.5216 | 93.80 | — | — | complete |
| wide64/mq-random-10 | grobx | 1 | 3/3 (0) | 0.4861 [0.4757,0.4864] | 0.4827 | 36.76 | — | — | complete |
| wide64/mq-random-10 | grobx | 2 | 0/3 (0) | — | — | — | — | — | unsupported |
| wide64/mq-random-10 | grobx | 4 | 0/3 (0) | — | — | — | — | — | unsupported |
| wide64/mq-random-10 | grobx | 8 | 0/3 (0) | — | — | — | — | — | unsupported |
| wide64/mq-random-10 | grobx | 16 | 0/3 (0) | — | — | — | — | — | unsupported |
| wide64/mq-random-10 | grobx | 32 | 0/3 (0) | — | — | — | — | — | unsupported |
| wide64/mq-random-10 | zeebra | 1 | 0/3 (0) | — | — | — | — | — | not-measured |
| wide64/mq-random-10 | zeebra | 2 | 0/3 (0) | — | — | — | — | — | unsupported |
| wide64/mq-random-10 | zeebra | 4 | 0/3 (0) | — | — | — | — | — | unsupported |
| wide64/mq-random-10 | zeebra | 8 | 0/3 (0) | — | — | — | — | — | unsupported |
| wide64/mq-random-10 | zeebra | 16 | 0/3 (0) | — | — | — | — | — | unsupported |
| wide64/mq-random-10 | zeebra | 32 | 0/3 (0) | — | — | — | — | — | unsupported |
| goldilocks/katsura-4 | msolve | 1 | 0/3 (0) | — | — | — | — | — | unsupported |
| goldilocks/katsura-4 | msolve | 2 | 0/3 (0) | — | — | — | — | — | unsupported |
| goldilocks/katsura-4 | msolve | 4 | 0/3 (0) | — | — | — | — | — | unsupported |
| goldilocks/katsura-4 | msolve | 8 | 0/3 (0) | — | — | — | — | — | unsupported |
| goldilocks/katsura-4 | msolve | 16 | 0/3 (0) | — | — | — | — | — | unsupported |
| goldilocks/katsura-4 | msolve | 32 | 0/3 (0) | — | — | — | — | — | unsupported |
| goldilocks/katsura-4 | groebner-rs | 1 | 3/3 (0) | 0.0064 [0.0063,0.0068] | 0.0035 | 3.12 | — | — | complete |
| goldilocks/katsura-4 | groebner-rs | 2 | 3/3 (0) | 0.0065 [0.0061,0.0068] | 0.0038 | 3.11 | — | — | complete |
| goldilocks/katsura-4 | groebner-rs | 4 | 3/3 (0) | 0.0064 [0.0063,0.0068] | 0.0043 | 3.16 | — | — | complete |
| goldilocks/katsura-4 | groebner-rs | 8 | 3/3 (0) | 0.0065 [0.0061,0.0068] | 0.0057 | 3.19 | — | — | complete |
| goldilocks/katsura-4 | groebner-rs | 16 | 3/3 (0) | 0.0066 [0.0062,0.0068] | 0.0090 | 3.43 | — | — | complete |
| goldilocks/katsura-4 | groebner-rs | 32 | 3/3 (0) | 0.0066 [0.0062,0.0123] | 0.0132 | 3.76 | — | — | complete |
| goldilocks/katsura-4 | grobx | 1 | 3/3 (0) | 0.0066 [0.0061,0.0068] | 0.0036 | 9.25 | — | — | complete |
| goldilocks/katsura-4 | grobx | 2 | 0/3 (0) | — | — | — | — | — | unsupported |
| goldilocks/katsura-4 | grobx | 4 | 0/3 (0) | — | — | — | — | — | unsupported |
| goldilocks/katsura-4 | grobx | 8 | 0/3 (0) | — | — | — | — | — | unsupported |
| goldilocks/katsura-4 | grobx | 16 | 0/3 (0) | — | — | — | — | — | unsupported |
| goldilocks/katsura-4 | grobx | 32 | 0/3 (0) | — | — | — | — | — | unsupported |
| goldilocks/katsura-4 | zeebra | 1 | 0/3 (0) | — | — | — | — | — | not-measured |
| goldilocks/katsura-4 | zeebra | 2 | 0/3 (0) | — | — | — | — | — | unsupported |
| goldilocks/katsura-4 | zeebra | 4 | 0/3 (0) | — | — | — | — | — | unsupported |
| goldilocks/katsura-4 | zeebra | 8 | 0/3 (0) | — | — | — | — | — | unsupported |
| goldilocks/katsura-4 | zeebra | 16 | 0/3 (0) | — | — | — | — | — | unsupported |
| goldilocks/katsura-4 | zeebra | 32 | 0/3 (0) | — | — | — | — | — | unsupported |
| goldilocks/katsura-9 | msolve | 1 | 0/3 (0) | — | — | — | — | — | unsupported |
| goldilocks/katsura-9 | msolve | 2 | 0/3 (0) | — | — | — | — | — | unsupported |
| goldilocks/katsura-9 | msolve | 4 | 0/3 (0) | — | — | — | — | — | unsupported |
| goldilocks/katsura-9 | msolve | 8 | 0/3 (0) | — | — | — | — | — | unsupported |
| goldilocks/katsura-9 | msolve | 16 | 0/3 (0) | — | — | — | — | — | unsupported |
| goldilocks/katsura-9 | msolve | 32 | 0/3 (0) | — | — | — | — | — | unsupported |
| goldilocks/katsura-9 | groebner-rs | 1 | 3/3 (0) | 0.0715 [0.0703,0.0784] | 0.0686 | 9.48 | — | — | complete |
| goldilocks/katsura-9 | groebner-rs | 2 | 3/3 (0) | 0.0528 [0.0494,0.0552] | 0.0733 | 11.40 | — | — | complete |
| goldilocks/katsura-9 | groebner-rs | 4 | 3/3 (0) | 0.0446 [0.0435,0.0470] | 0.0892 | 11.97 | — | — | complete |
| goldilocks/katsura-9 | groebner-rs | 8 | 3/3 (0) | 0.0391 [0.0374,0.0412] | 0.1046 | 12.29 | — | — | complete |
| goldilocks/katsura-9 | groebner-rs | 16 | 3/3 (0) | 0.0445 [0.0429,0.0469] | 0.1400 | 12.61 | — | — | complete |
| goldilocks/katsura-9 | groebner-rs | 32 | 3/3 (0) | 0.0553 [0.0550,0.0582] | 0.2863 | 14.20 | — | — | complete |
| goldilocks/katsura-9 | grobx | 1 | 3/3 (0) | 0.0240 [0.0227,0.0247] | 0.0185 | 13.27 | — | — | complete |
| goldilocks/katsura-9 | grobx | 2 | 0/3 (0) | — | — | — | — | — | unsupported |
| goldilocks/katsura-9 | grobx | 4 | 0/3 (0) | — | — | — | — | — | unsupported |
| goldilocks/katsura-9 | grobx | 8 | 0/3 (0) | — | — | — | — | — | unsupported |
| goldilocks/katsura-9 | grobx | 16 | 0/3 (0) | — | — | — | — | — | unsupported |
| goldilocks/katsura-9 | grobx | 32 | 0/3 (0) | — | — | — | — | — | unsupported |
| goldilocks/katsura-9 | zeebra | 1 | 0/3 (0) | — | — | — | — | — | not-measured |
| goldilocks/katsura-9 | zeebra | 2 | 0/3 (0) | — | — | — | — | — | unsupported |
| goldilocks/katsura-9 | zeebra | 4 | 0/3 (0) | — | — | — | — | — | unsupported |
| goldilocks/katsura-9 | zeebra | 8 | 0/3 (0) | — | — | — | — | — | unsupported |
| goldilocks/katsura-9 | zeebra | 16 | 0/3 (0) | — | — | — | — | — | unsupported |
| goldilocks/katsura-9 | zeebra | 32 | 0/3 (0) | — | — | — | — | — | unsupported |
| goldilocks/cyclic-7 | msolve | 1 | 0/3 (0) | — | — | — | — | — | unsupported |
| goldilocks/cyclic-7 | msolve | 2 | 0/3 (0) | — | — | — | — | — | unsupported |
| goldilocks/cyclic-7 | msolve | 4 | 0/3 (0) | — | — | — | — | — | unsupported |
| goldilocks/cyclic-7 | msolve | 8 | 0/3 (0) | — | — | — | — | — | unsupported |
| goldilocks/cyclic-7 | msolve | 16 | 0/3 (0) | — | — | — | — | — | unsupported |
| goldilocks/cyclic-7 | msolve | 32 | 0/3 (0) | — | — | — | — | — | unsupported |
| goldilocks/cyclic-7 | groebner-rs | 1 | 3/3 (0) | 0.1792 [0.1760,0.1808] | 0.1747 | 14.73 | — | — | complete |
| goldilocks/cyclic-7 | groebner-rs | 2 | 3/3 (0) | 0.1099 [0.1042,0.1155] | 0.1713 | 14.79 | — | — | complete |
| goldilocks/cyclic-7 | groebner-rs | 4 | 3/3 (0) | 0.0827 [0.0820,0.0847] | 0.1872 | 15.43 | — | — | complete |
| goldilocks/cyclic-7 | groebner-rs | 8 | 3/3 (0) | 0.0727 [0.0702,0.0773] | 0.2253 | 13.99 | — | — | complete |
| goldilocks/cyclic-7 | groebner-rs | 16 | 3/3 (0) | 0.0829 [0.0792,0.0877] | 0.2954 | 15.71 | — | — | complete |
| goldilocks/cyclic-7 | groebner-rs | 32 | 3/3 (0) | 0.0992 [0.0984,0.0994] | 0.5740 | 16.70 | — | — | complete |
| goldilocks/cyclic-7 | grobx | 1 | 3/3 (0) | 0.1207 [0.1165,0.1208] | 0.1148 | 13.64 | — | — | complete |
| goldilocks/cyclic-7 | grobx | 2 | 0/3 (0) | — | — | — | — | — | unsupported |
| goldilocks/cyclic-7 | grobx | 4 | 0/3 (0) | — | — | — | — | — | unsupported |
| goldilocks/cyclic-7 | grobx | 8 | 0/3 (0) | — | — | — | — | — | unsupported |
| goldilocks/cyclic-7 | grobx | 16 | 0/3 (0) | — | — | — | — | — | unsupported |
| goldilocks/cyclic-7 | grobx | 32 | 0/3 (0) | — | — | — | — | — | unsupported |
| goldilocks/cyclic-7 | zeebra | 1 | 0/3 (0) | — | — | — | — | — | not-measured |
| goldilocks/cyclic-7 | zeebra | 2 | 0/3 (0) | — | — | — | — | — | unsupported |
| goldilocks/cyclic-7 | zeebra | 4 | 0/3 (0) | — | — | — | — | — | unsupported |
| goldilocks/cyclic-7 | zeebra | 8 | 0/3 (0) | — | — | — | — | — | unsupported |
| goldilocks/cyclic-7 | zeebra | 16 | 0/3 (0) | — | — | — | — | — | unsupported |
| goldilocks/cyclic-7 | zeebra | 32 | 0/3 (0) | — | — | — | — | — | unsupported |
| goldilocks/mq-random-10 | msolve | 1 | 0/3 (0) | — | — | — | — | — | unsupported |
| goldilocks/mq-random-10 | msolve | 2 | 0/3 (0) | — | — | — | — | — | unsupported |
| goldilocks/mq-random-10 | msolve | 4 | 0/3 (0) | — | — | — | — | — | unsupported |
| goldilocks/mq-random-10 | msolve | 8 | 0/3 (0) | — | — | — | — | — | unsupported |
| goldilocks/mq-random-10 | msolve | 16 | 0/3 (0) | — | — | — | — | — | unsupported |
| goldilocks/mq-random-10 | msolve | 32 | 0/3 (0) | — | — | — | — | — | unsupported |
| goldilocks/mq-random-10 | groebner-rs | 1 | 3/3 (0) | 1.6043 [1.5837,1.6806] | 1.5912 | 81.73 | — | — | complete |
| goldilocks/mq-random-10 | groebner-rs | 2 | 3/3 (0) | 0.9276 [0.9273,0.9305] | 1.6186 | 87.64 | — | — | complete |
| goldilocks/mq-random-10 | groebner-rs | 4 | 3/3 (0) | 0.6297 [0.6172,0.6340] | 1.7657 | 88.13 | — | — | complete |
| goldilocks/mq-random-10 | groebner-rs | 8 | 3/3 (0) | 0.4778 [0.4728,0.4836] | 1.9051 | 88.05 | — | — | complete |
| goldilocks/mq-random-10 | groebner-rs | 16 | 3/3 (0) | 0.4881 [0.4703,0.4914] | 2.0016 | 96.38 | — | — | complete |
| goldilocks/mq-random-10 | groebner-rs | 32 | 3/3 (0) | 0.4650 [0.4511,0.4668] | 2.4891 | 95.94 | — | — | complete |
| goldilocks/mq-random-10 | grobx | 1 | 3/3 (0) | 0.4789 [0.4766,0.4831] | 0.4735 | 36.89 | — | — | complete |
| goldilocks/mq-random-10 | grobx | 2 | 0/3 (0) | — | — | — | — | — | unsupported |
| goldilocks/mq-random-10 | grobx | 4 | 0/3 (0) | — | — | — | — | — | unsupported |
| goldilocks/mq-random-10 | grobx | 8 | 0/3 (0) | — | — | — | — | — | unsupported |
| goldilocks/mq-random-10 | grobx | 16 | 0/3 (0) | — | — | — | — | — | unsupported |
| goldilocks/mq-random-10 | grobx | 32 | 0/3 (0) | — | — | — | — | — | unsupported |
| goldilocks/mq-random-10 | zeebra | 1 | 0/3 (0) | — | — | — | — | — | not-measured |
| goldilocks/mq-random-10 | zeebra | 2 | 0/3 (0) | — | — | — | — | — | unsupported |
| goldilocks/mq-random-10 | zeebra | 4 | 0/3 (0) | — | — | — | — | — | unsupported |
| goldilocks/mq-random-10 | zeebra | 8 | 0/3 (0) | — | — | — | — | — | unsupported |
| goldilocks/mq-random-10 | zeebra | 16 | 0/3 (0) | — | — | — | — | — | unsupported |
| goldilocks/mq-random-10 | zeebra | 32 | 0/3 (0) | — | — | — | — | — | unsupported |

## Frozen input identities

| Field/input | Complete canonical SHA-256 |
|---|---|
| 32003/katsura-4 | `c5fb073f5c9aceaab7d83d9c24de42c24eaa083777748dda50104b24347e2682` |
| 32003/mq-random-10 | `16422dafcdb6487ea541f976f7754112b811c85af2b3537ed10fe4ef9c8f3d7f` |
| 32003/katsura-11 | `c6802b0391f8394f38f2d5807f3c0d197cae6a592a875c3b65c38b41f949b378` |
| 32003/cyclic-7 | `18746449c45766c3ba73ab0417c2ea1bbe7f7842d88d8a1a55068c71e9aaa736` |
| 32003/cyclic-10 | `538964ac3a891da65bb0eaada43b7ed3a6a5aa51f1fa608a6f4119a500ff0d34` |
| 2147483647/katsura-4 | `825a3aa54e152da5f2abac4a0b863430addacb4d8920aab3dac571cc681853fd` |
| 2147483647/mq-random-10 | `72d0ad315fc25409792625465578d18329597d3ee183e75f257774d9215803b2` |
| 2147483647/katsura-11 | `03bf44d5d614a21cc8f56462aa873b7961641a2341892e3b2ef52b6cfec86a13` |
| 2147483647/cyclic-7 | `30ce3b4f54c7b30ef818a8750b4e61e51f3f8a1a6e4e49e384fbb5096c6eec17` |
| 2147483647/cyclic-10 | `df450bfc1886aa266a0f5a4ad5e0bef8d53822a079b9b7467e0b73d5a0a6ad75` |
| wide64/katsura-4 | `f2670d770ef9a866db0a407dbd1f05827563a9af3bc4485d51a99bb3eef307b6` |
| wide64/katsura-9 | `18eb9c774fc5700cc38e0724dc04af38f34803132a8c20b38f1ad88f5ff749ec` |
| wide64/cyclic-7 | `1da97cb3fe0eff34f224caaa8f029579d5f7252d910b78a3d5021baec41386bc` |
| wide64/mq-random-10 | `f6ea856abd1e8bf5e7ef04f0bae0426b8b69c12dc7e485a1ba7873eaa92a9e3a` |
| goldilocks/katsura-4 | `00f08d221047f38741f377f52893d3d561236feecf3bce5f9108d570937f35d3` |
| goldilocks/katsura-9 | `5e53d1de46cee3e490a6cf38677e28396bda682e3b4acd0854a2b02daa421e6a` |
| goldilocks/cyclic-7 | `274e9a533b788e6e440803ad61ee44d2e0c691cec045c8c3bd6607ad8c42cb11` |
| goldilocks/mq-random-10 | `f69e955f898956df18bf174d1635f4f2cef7cf3e457e101713e826b3674a7bf3` |

## Same-engine hot-call curves

These internal timers exclude process setup/input/output; Julia tiny-warmup calls can still include threaded JIT and GC and cannot be divided by another engine’s process wall.
Each S(p) uses this engine/configuration’s own one-worker control; pivot work can change.

| Field/input | Engine | Workers | Repeats | Hot median [min,max] ms | S(p) | E(p) |
|---|---|---:|---:|---:|---:|---:|
| 32003/katsura-4 | groebner-rs | 1 | 3 | 0.173 [0.159,0.189] | 1.000 | 1.000 |
| 32003/katsura-4 | grobx | 1 | 3 | 0.207 [0.194,0.211] | 1.000 | 1.000 |
| 32003/katsura-4 | groebner-rs | 2 | 3 | 0.202 [0.171,0.215] | 0.857 | 0.429 |
| 32003/katsura-4 | groebner-rs | 4 | 3 | 0.168 [0.152,0.169] | 1.030 | 0.257 |
| 32003/katsura-4 | groebner-rs | 8 | 3 | 0.203 [0.194,0.243] | 0.855 | 0.107 |
| 32003/katsura-4 | groebner-rs | 16 | 3 | 0.206 [0.203,0.219] | 0.842 | 0.053 |
| 32003/katsura-4 | groebner-rs | 32 | 3 | 0.187 [0.183,0.225] | 0.929 | 0.029 |
| 32003/mq-random-10 | groebner-rs | 1 | 3 | 94.773 [94.599,101.946] | 1.000 | 1.000 |
| 32003/mq-random-10 | grobx | 1 | 3 | 322.890 [322.523,325.234] | 1.000 | 1.000 |
| 32003/mq-random-10 | groebner-rs | 2 | 3 | 76.847 [72.321,77.186] | 1.233 | 0.617 |
| 32003/mq-random-10 | groebner-rs | 4 | 3 | 66.455 [63.145,67.192] | 1.426 | 0.357 |
| 32003/mq-random-10 | groebner-rs | 8 | 3 | 62.491 [60.771,63.620] | 1.517 | 0.190 |
| 32003/mq-random-10 | groebner-rs | 16 | 3 | 71.287 [70.350,83.270] | 1.329 | 0.083 |
| 32003/mq-random-10 | groebner-rs | 32 | 3 | 96.196 [87.250,100.699] | 0.985 | 0.031 |
| 32003/cyclic-7 | groebner-rs | 1 | 3 | 40.981 [40.702,41.706] | 1.000 | 1.000 |
| 32003/cyclic-7 | grobx | 1 | 3 | 47.907 [47.611,47.996] | 1.000 | 1.000 |
| 32003/cyclic-7 | groebner-rs | 2 | 3 | 32.512 [32.146,35.248] | 1.260 | 0.630 |
| 32003/cyclic-7 | groebner-rs | 4 | 3 | 31.215 [29.711,33.222] | 1.313 | 0.328 |
| 32003/cyclic-7 | groebner-rs | 8 | 3 | 30.129 [30.076,30.870] | 1.360 | 0.170 |
| 32003/cyclic-7 | groebner-rs | 16 | 3 | 42.369 [36.399,45.045] | 0.967 | 0.060 |
| 32003/cyclic-7 | groebner-rs | 32 | 3 | 55.639 [54.368,55.655] | 0.737 | 0.023 |
| 2147483647/katsura-4 | groebner-rs | 1 | 3 | 0.181 [0.173,0.191] | 1.000 | 1.000 |
| 2147483647/katsura-4 | grobx | 1 | 3 | 0.279 [0.279,0.280] | 1.000 | 1.000 |
| 2147483647/katsura-4 | groebner-rs | 2 | 3 | 0.182 [0.177,0.210] | 0.993 | 0.496 |
| 2147483647/katsura-4 | groebner-rs | 4 | 3 | 0.189 [0.169,0.234] | 0.956 | 0.239 |
| 2147483647/katsura-4 | groebner-rs | 8 | 3 | 0.169 [0.168,0.177] | 1.068 | 0.133 |
| 2147483647/katsura-4 | groebner-rs | 16 | 3 | 0.215 [0.213,0.238] | 0.842 | 0.053 |
| 2147483647/katsura-4 | groebner-rs | 32 | 3 | 0.184 [0.174,0.202] | 0.981 | 0.031 |
| 2147483647/mq-random-10 | groebner-rs | 1 | 3 | 127.426 [127.080,137.974] | 1.000 | 1.000 |
| 2147483647/mq-random-10 | grobx | 1 | 3 | 150.030 [149.201,151.048] | 1.000 | 1.000 |
| 2147483647/mq-random-10 | groebner-rs | 2 | 3 | 92.420 [90.608,95.570] | 1.379 | 0.689 |
| 2147483647/mq-random-10 | groebner-rs | 4 | 3 | 77.088 [71.710,77.785] | 1.653 | 0.413 |
| 2147483647/mq-random-10 | groebner-rs | 8 | 3 | 68.006 [67.876,68.101] | 1.874 | 0.234 |
| 2147483647/mq-random-10 | groebner-rs | 16 | 3 | 78.088 [76.700,78.489] | 1.632 | 0.102 |
| 2147483647/mq-random-10 | groebner-rs | 32 | 3 | 108.415 [103.949,112.509] | 1.175 | 0.037 |
| 2147483647/katsura-11 | groebner-rs | 1 | 3 | 682.027 [681.629,685.973] | 1.000 | 1.000 |
| 2147483647/katsura-11 | grobx | 1 | 3 | 128.509 [123.751,131.232] | 1.000 | 1.000 |
| 2147483647/katsura-11 | groebner-rs | 2 | 3 | 397.236 [393.416,411.397] | 1.717 | 0.858 |
| 2147483647/katsura-11 | groebner-rs | 4 | 3 | 282.124 [271.404,283.431] | 2.417 | 0.604 |
| 2147483647/katsura-11 | groebner-rs | 8 | 3 | 221.795 [219.664,224.183] | 3.075 | 0.384 |
| 2147483647/katsura-11 | groebner-rs | 16 | 3 | 240.059 [235.586,252.985] | 2.841 | 0.178 |
| 2147483647/katsura-11 | groebner-rs | 32 | 3 | 271.862 [270.177,275.252] | 2.509 | 0.078 |


## julia-ordinary.json.gz

# Comparand worker cohorts (#739)

**Measured at:** `55f513492f565f59aadd4d9b30b5f5a8b2039929`.

Full reduced-basis process wall; exact reference checks follow timing. Diagnostic hot-region ticks are separate.
Unverified completions retain raw wall observations but no timing ratios; limits/capabilities remain visible. Julia deterministic backend; Rust randomized native backend.
S(p)/E(p) also require both process walls above twice the corresponding Katsura-4 startup control.

| Field/input | Engine | Workers | Complete/planned (verified) | Wall median s | Process CPU median s | RSS max MiB | S(p) | E(p) | Status |
|---|---|---:|---:|---:|---:|---:|---:|---:|---|
| 32003/katsura-4 | groebner.jl | 1 | 3/3 (3) | 6.5293 [6.5108,6.7097] | 6.4834 | 709.55 | — | — | verified |
| 32003/katsura-4 | groebner.jl | 2 | 3/3 (3) | 6.5524 [6.5505,6.7669] | 6.5014 | 709.59 | — | — | verified |
| 32003/katsura-4 | groebner.jl | 4 | 3/3 (3) | 6.4069 [6.4048,6.4430] | 6.5485 | 713.07 | — | — | verified |
| 32003/katsura-4 | groebner.jl | 8 | 3/3 (3) | 6.3385 [6.3321,6.3389] | 6.5972 | 698.17 | — | — | verified |
| 32003/katsura-4 | groebner.jl | 16 | 3/3 (3) | 6.3579 [6.3034,6.3735] | 6.8125 | 699.27 | — | — | verified |
| 32003/katsura-4 | groebner.jl | 32 | 3/3 (3) | 6.4609 [6.4425,6.4989] | 7.5063 | 703.05 | — | — | verified |
| 32003/mq-random-10 | groebner.jl | 1 | 3/3 (3) | 8.0349 [8.0208,8.0373] | 7.9770 | 751.46 | — | — | verified |
| 32003/mq-random-10 | groebner.jl | 2 | 3/3 (3) | 8.0390 [7.9807,8.1239] | 8.3527 | 755.17 | — | — | verified |
| 32003/mq-random-10 | groebner.jl | 4 | 3/3 (3) | 7.7972 [7.7459,7.9183] | 8.8244 | 781.81 | — | — | verified |
| 32003/mq-random-10 | groebner.jl | 8 | 3/3 (3) | 7.6987 [7.6954,7.7572] | 9.6561 | 732.98 | — | — | verified |
| 32003/mq-random-10 | groebner.jl | 16 | 3/3 (3) | 7.7483 [7.7236,7.8787] | 11.6676 | 767.09 | — | — | verified |
| 32003/mq-random-10 | groebner.jl | 32 | 3/3 (3) | 7.8808 [7.8529,7.9400] | 16.0604 | 778.58 | — | — | verified |
| 32003/cyclic-7 | groebner.jl | 1 | 3/3 (3) | 6.6956 [6.6873,6.7069] | 6.6438 | 725.32 | — | — | verified |
| 32003/cyclic-7 | groebner.jl | 2 | 3/3 (3) | 6.8636 [6.8365,6.8695] | 7.0000 | 723.46 | — | — | verified |
| 32003/cyclic-7 | groebner.jl | 4 | 3/3 (3) | 6.7415 [6.7123,6.7626] | 7.4182 | 720.46 | — | — | verified |
| 32003/cyclic-7 | groebner.jl | 8 | 3/3 (3) | 6.7046 [6.7039,6.7419] | 8.3016 | 708.08 | — | — | verified |
| 32003/cyclic-7 | groebner.jl | 16 | 3/3 (3) | 6.8247 [6.7498,6.9972] | 10.2713 | 740.07 | — | — | verified |
| 32003/cyclic-7 | groebner.jl | 32 | 3/3 (3) | 6.9131 [6.7405,6.9347] | 17.0055 | 743.29 | — | — | verified |
| 2147483647/katsura-4 | groebner.jl | 1 | 3/3 (3) | 3.9764 [3.9564,3.9954] | 3.9474 | 678.20 | — | — | verified |
| 2147483647/katsura-4 | groebner.jl | 2 | 3/3 (3) | 3.9969 [3.9678,4.0099] | 3.9637 | 679.43 | — | — | verified |
| 2147483647/katsura-4 | groebner.jl | 4 | 3/3 (3) | 3.8786 [3.8237,3.8953] | 4.0225 | 680.73 | — | — | verified |
| 2147483647/katsura-4 | groebner.jl | 8 | 3/3 (3) | 3.8023 [3.8016,3.9183] | 4.0548 | 680.27 | — | — | verified |
| 2147483647/katsura-4 | groebner.jl | 16 | 3/3 (3) | 3.8257 [3.8167,3.8298] | 4.2671 | 682.63 | — | — | verified |
| 2147483647/katsura-4 | groebner.jl | 32 | 3/3 (3) | 3.8410 [3.8372,3.9322] | 4.8822 | 687.04 | — | — | verified |
| 2147483647/mq-random-10 | groebner.jl | 1 | 3/3 (3) | 6.1407 [6.1329,6.2316] | 6.0953 | 718.18 | — | — | verified |
| 2147483647/mq-random-10 | groebner.jl | 2 | 3/3 (3) | 6.1625 [6.1557,6.1758] | 6.4617 | 716.80 | — | — | verified |
| 2147483647/mq-random-10 | groebner.jl | 4 | 3/3 (3) | 5.9898 [5.9755,6.0035] | 6.9811 | 714.62 | — | — | verified |
| 2147483647/mq-random-10 | groebner.jl | 8 | 3/3 (3) | 5.9187 [5.9048,5.9259] | 7.9274 | 744.42 | — | — | verified |
| 2147483647/mq-random-10 | groebner.jl | 16 | 3/3 (3) | 6.0265 [5.9435,6.0547] | 9.9286 | 736.59 | — | — | verified |
| 2147483647/mq-random-10 | groebner.jl | 32 | 3/3 (3) | 6.0485 [6.0391,6.0629] | 13.5083 | 746.92 | — | — | verified |
| 2147483647/katsura-11 | groebner.jl | 1 | 3/3 (3) | 9.6167 [9.5943,9.6796] | 9.5533 | 767.35 | 1.000 | 1.000 | verified |
| 2147483647/katsura-11 | groebner.jl | 2 | 3/3 (3) | 8.4137 [8.4095,8.6350] | 9.9167 | 792.80 | 1.143 | 0.571 | verified |
| 2147483647/katsura-11 | groebner.jl | 4 | 3/3 (3) | 7.4708 [7.4591,7.5204] | 10.4299 | 804.22 | — | — | verified |
| 2147483647/katsura-11 | groebner.jl | 8 | 3/3 (3) | 7.1358 [7.0861,7.1401] | 11.6897 | 808.61 | — | — | verified |
| 2147483647/katsura-11 | groebner.jl | 16 | 3/3 (3) | 7.1737 [7.0258,7.2739] | 13.8044 | 832.12 | — | — | verified |
| 2147483647/katsura-11 | groebner.jl | 32 | 3/3 (3) | 7.0811 [7.0241,7.1202] | 18.5289 | 836.82 | — | — | verified |

## Frozen input identities

| Field/input | Complete canonical SHA-256 |
|---|---|
| 32003/katsura-4 | `c5fb073f5c9aceaab7d83d9c24de42c24eaa083777748dda50104b24347e2682` |
| 32003/mq-random-10 | `16422dafcdb6487ea541f976f7754112b811c85af2b3537ed10fe4ef9c8f3d7f` |
| 32003/cyclic-7 | `18746449c45766c3ba73ab0417c2ea1bbe7f7842d88d8a1a55068c71e9aaa736` |
| 2147483647/katsura-4 | `825a3aa54e152da5f2abac4a0b863430addacb4d8920aab3dac571cc681853fd` |
| 2147483647/mq-random-10 | `72d0ad315fc25409792625465578d18329597d3ee183e75f257774d9215803b2` |
| 2147483647/katsura-11 | `03bf44d5d614a21cc8f56462aa873b7961641a2341892e3b2ef52b6cfec86a13` |

## Same-engine hot-call curves

These internal timers exclude process setup/input/output; Julia tiny-warmup calls can still include threaded JIT and GC and cannot be divided by another engine’s process wall.
Each S(p) uses this engine/configuration’s own one-worker control; pivot work can change.

| Field/input | Engine | Workers | Repeats | Hot median [min,max] ms | S(p) | E(p) |
|---|---|---:|---:|---:|---:|---:|
| 32003/katsura-4 | groebner.jl | 1 | 3 | 0.856 [0.831,0.901] | 1.000 | 1.000 |
| 32003/katsura-4 | groebner.jl | 2 | 3 | 0.854 [0.850,0.871] | 1.002 | 0.501 |
| 32003/katsura-4 | groebner.jl | 4 | 3 | 0.749 [0.731,0.754] | 1.143 | 0.286 |
| 32003/katsura-4 | groebner.jl | 8 | 3 | 0.813 [0.773,0.834] | 1.053 | 0.132 |
| 32003/katsura-4 | groebner.jl | 16 | 3 | 0.822 [0.713,0.843] | 1.041 | 0.065 |
| 32003/katsura-4 | groebner.jl | 32 | 3 | 0.730 [0.727,0.814] | 1.172 | 0.037 |
| 32003/mq-random-10 | groebner.jl | 1 | 3 | 438.083 [435.030,440.575] | 1.000 | 1.000 |
| 32003/mq-random-10 | groebner.jl | 2 | 3 | 422.403 [419.617,423.468] | 1.037 | 0.519 |
| 32003/mq-random-10 | groebner.jl | 4 | 3 | 328.915 [315.143,348.145] | 1.332 | 0.333 |
| 32003/mq-random-10 | groebner.jl | 8 | 3 | 294.282 [293.657,296.849] | 1.489 | 0.186 |
| 32003/mq-random-10 | groebner.jl | 16 | 3 | 304.438 [292.711,439.954] | 1.439 | 0.090 |
| 32003/mq-random-10 | groebner.jl | 32 | 3 | 398.111 [364.405,400.480] | 1.100 | 0.034 |
| 32003/cyclic-7 | groebner.jl | 1 | 3 | 102.299 [102.269,102.437] | 1.000 | 1.000 |
| 32003/cyclic-7 | groebner.jl | 2 | 3 | 253.590 [252.604,258.696] | 0.403 | 0.202 |
| 32003/cyclic-7 | groebner.jl | 4 | 3 | 245.848 [245.267,247.871] | 0.416 | 0.104 |
| 32003/cyclic-7 | groebner.jl | 8 | 3 | 264.078 [263.952,266.132] | 0.387 | 0.048 |
| 32003/cyclic-7 | groebner.jl | 16 | 3 | 402.394 [276.631,547.062] | 0.254 | 0.016 |
| 32003/cyclic-7 | groebner.jl | 32 | 3 | 447.731 [275.680,494.090] | 0.228 | 0.007 |
| 2147483647/katsura-4 | groebner.jl | 1 | 3 | 0.792 [0.787,0.827] | 1.000 | 1.000 |
| 2147483647/katsura-4 | groebner.jl | 2 | 3 | 0.822 [0.812,0.834] | 0.964 | 0.482 |
| 2147483647/katsura-4 | groebner.jl | 4 | 3 | 0.626 [0.620,0.630] | 1.265 | 0.316 |
| 2147483647/katsura-4 | groebner.jl | 8 | 3 | 0.718 [0.639,0.764] | 1.103 | 0.138 |
| 2147483647/katsura-4 | groebner.jl | 16 | 3 | 0.707 [0.693,0.723] | 1.120 | 0.070 |
| 2147483647/katsura-4 | groebner.jl | 32 | 3 | 0.718 [0.715,0.729] | 1.103 | 0.034 |
| 2147483647/mq-random-10 | groebner.jl | 1 | 3 | 393.991 [393.459,396.407] | 1.000 | 1.000 |
| 2147483647/mq-random-10 | groebner.jl | 2 | 3 | 389.233 [388.111,389.456] | 1.012 | 0.506 |
| 2147483647/mq-random-10 | groebner.jl | 4 | 3 | 310.943 [303.194,315.759] | 1.267 | 0.317 |
| 2147483647/mq-random-10 | groebner.jl | 8 | 3 | 289.031 [286.347,296.392] | 1.363 | 0.170 |
| 2147483647/mq-random-10 | groebner.jl | 16 | 3 | 291.524 [289.961,384.852] | 1.351 | 0.084 |
| 2147483647/mq-random-10 | groebner.jl | 32 | 3 | 390.392 [371.451,406.495] | 1.009 | 0.032 |
| 2147483647/katsura-11 | groebner.jl | 1 | 3 | 2953.887 [2945.324,2959.177] | 1.000 | 1.000 |
| 2147483647/katsura-11 | groebner.jl | 2 | 3 | 1746.317 [1740.700,1748.633] | 1.691 | 0.846 |
| 2147483647/katsura-11 | groebner.jl | 4 | 3 | 1066.372 [1057.299,1098.602] | 2.770 | 0.693 |
| 2147483647/katsura-11 | groebner.jl | 8 | 3 | 806.510 [803.939,807.533] | 3.663 | 0.458 |
| 2147483647/katsura-11 | groebner.jl | 16 | 3 | 844.745 [734.072,976.862] | 3.497 | 0.219 |
| 2147483647/katsura-11 | groebner.jl | 32 | 3 | 673.739 [632.759,726.360] | 4.384 | 0.137 |


## julia-rust-diagnostic.json.gz

# Comparand worker cohorts (#739)

**Measured at:** `55f513492f565f59aadd4d9b30b5f5a8b2039929`.

Full reduced-basis process wall; exact reference checks follow timing. Diagnostic hot-region ticks are separate.
Unverified completions retain raw wall observations but no timing ratios; limits/capabilities remain visible. Julia deterministic backend; Rust randomized native backend.
S(p)/E(p) also require both process walls above twice the corresponding Katsura-4 startup control.

| Field/input | Engine | Workers | Complete/planned (verified) | Wall median s | Process CPU median s | RSS max MiB | S(p) | E(p) | Status |
|---|---|---:|---:|---:|---:|---:|---:|---:|---|

## Frozen input identities

| Field/input | Complete canonical SHA-256 |
|---|---|
| 2147483647/katsura-11 | `03bf44d5d614a21cc8f56462aa873b7961641a2341892e3b2ef52b6cfec86a13` |

## Same-engine hot-call curves

These internal timers exclude process setup/input/output; Julia tiny-warmup calls can still include threaded JIT and GC and cannot be divided by another engine’s process wall.
Each S(p) uses this engine/configuration’s own one-worker control; pivot work can change.

| Field/input | Engine | Workers | Repeats | Hot median [min,max] ms | S(p) | E(p) |
|---|---|---:|---:|---:|---:|---:|

## Separate concurrency diagnostics

CPU-active participants are tick-resolution lower bounds, not simultaneous algebra workers. Julia ticks may include JIT/GC.
Full-case-prewarmed Julia processes contain two complete solves; their process wall is not comparable to the ordinary one-solve cohort.

| Field/input | Engine | Workers | Status | Process s | Hot ms | Compile ms | Recompile ms | GC ms | CPU-active participants | Peak MiB |
|---|---|---:|---|---:|---:|---:|---:|---:|---:|---:|
| 2147483647/katsura-11 | groebner-rs | 1 | verified | 0.803 | 682.799 | — | — | — | 1 | 82.684 |
| 2147483647/katsura-11 | groebner-rs | 8 | unattempted | — | — | — | — | — | unresolved | — |
| 2147483647/katsura-11 | groebner-rs | 16 | unattempted | — | — | — | — | — | unresolved | — |

## julia-julia-diagnostic.json.gz

# Comparand worker cohorts (#739)

**Measured at:** `55f513492f565f59aadd4d9b30b5f5a8b2039929`.

Full reduced-basis process wall; exact reference checks follow timing. Diagnostic hot-region ticks are separate.
Unverified completions retain raw wall observations but no timing ratios; limits/capabilities remain visible. Julia deterministic backend; Rust randomized native backend.
S(p)/E(p) also require both process walls above twice the corresponding Katsura-4 startup control.

| Field/input | Engine | Workers | Complete/planned (verified) | Wall median s | Process CPU median s | RSS max MiB | S(p) | E(p) | Status |
|---|---|---:|---:|---:|---:|---:|---:|---:|---|

## Frozen input identities

| Field/input | Complete canonical SHA-256 |
|---|---|
| 2147483647/katsura-11 | `03bf44d5d614a21cc8f56462aa873b7961641a2341892e3b2ef52b6cfec86a13` |

## Same-engine hot-call curves

These internal timers exclude process setup/input/output; Julia tiny-warmup calls can still include threaded JIT and GC and cannot be divided by another engine’s process wall.
Each S(p) uses this engine/configuration’s own one-worker control; pivot work can change.

| Field/input | Engine | Workers | Repeats | Hot median [min,max] ms | S(p) | E(p) |
|---|---|---:|---:|---:|---:|---:|

## Separate concurrency diagnostics

CPU-active participants are tick-resolution lower bounds, not simultaneous algebra workers. Julia ticks may include JIT/GC.
Full-case-prewarmed Julia processes contain two complete solves; their process wall is not comparable to the ordinary one-solve cohort.

| Field/input | Engine | Workers | Status | Process s | Hot ms | Compile ms | Recompile ms | GC ms | CPU-active participants | Peak MiB |
|---|---|---:|---|---:|---:|---:|---:|---:|---:|---:|
| 2147483647/katsura-11 | groebner.jl | 1 | verified | 12.640 | 2927.402 | 0.000 | 0.000 | 39.613 | 1 | 788.426 |
| 2147483647/katsura-11 | groebner.jl | 8 | verified | 7.897 | 609.930 | 0.000 | 0.000 | 57.908 | 11 | 820.500 |
| 2147483647/katsura-11 | groebner.jl | 16 | verified | 7.811 | 564.185 | 0.000 | 0.000 | 25.087 | 23 | 817.555 |

## julia-wide.json.gz

# Comparand worker cohorts (#739)

**Measured at:** `55f513492f565f59aadd4d9b30b5f5a8b2039929`.

Full reduced-basis process wall; exact reference checks follow timing. Diagnostic hot-region ticks are separate.
Unverified completions retain raw wall observations but no timing ratios; limits/capabilities remain visible. Julia deterministic backend; Rust randomized native backend.
S(p)/E(p) also require both process walls above twice the corresponding Katsura-4 startup control.

| Field/input | Engine | Workers | Complete/planned (verified) | Wall median s | Process CPU median s | RSS max MiB | S(p) | E(p) | Status |
|---|---|---:|---:|---:|---:|---:|---:|---:|---|
| wide64/katsura-4 | groebner.jl | 1 | 1/1 (0) | 6.4243 [6.4243,6.4243] | 6.3766 | 705.69 | — | — | complete |
| wide64/katsura-4 | groebner.jl | 8 | 1/1 (0) | 6.2319 [6.2319,6.2319] | 6.4957 | 694.59 | — | — | complete |
| wide64/katsura-4 | groebner.jl | 16 | 1/1 (0) | 6.2275 [6.2275,6.2275] | 6.6621 | 694.90 | — | — | complete |
| wide64/cyclic-7 | groebner.jl | 1 | 1/1 (0) | 6.7479 [6.7479,6.7479] | 6.6987 | 715.27 | — | — | complete |
| wide64/cyclic-7 | groebner.jl | 8 | 1/1 (0) | 6.6451 [6.6451,6.6451] | 8.3224 | 727.64 | — | — | complete |
| wide64/cyclic-7 | groebner.jl | 16 | 1/1 (0) | 6.7119 [6.7119,6.7119] | 10.1766 | 733.45 | — | — | complete |
| wide64/mq-random-10 | groebner.jl | 1 | 1/1 (0) | 18.2180 [18.2180,18.2180] | 18.1058 | 781.69 | — | — | complete |
| wide64/mq-random-10 | groebner.jl | 8 | 1/1 (0) | 9.7869 [9.7869,9.7869] | 20.9096 | 782.20 | — | — | complete |
| wide64/mq-random-10 | groebner.jl | 16 | 0/1 (0) | — | — | — | — | — | unattempted(1) |

## Frozen input identities

| Field/input | Complete canonical SHA-256 |
|---|---|
| wide64/katsura-4 | `f2670d770ef9a866db0a407dbd1f05827563a9af3bc4485d51a99bb3eef307b6` |
| wide64/cyclic-7 | `1da97cb3fe0eff34f224caaa8f029579d5f7252d910b78a3d5021baec41386bc` |
| wide64/mq-random-10 | `f6ea856abd1e8bf5e7ef04f0bae0426b8b69c12dc7e485a1ba7873eaa92a9e3a` |

## Same-engine hot-call curves

These internal timers exclude process setup/input/output; Julia tiny-warmup calls can still include threaded JIT and GC and cannot be divided by another engine’s process wall.
Each S(p) uses this engine/configuration’s own one-worker control; pivot work can change.

| Field/input | Engine | Workers | Repeats | Hot median [min,max] ms | S(p) | E(p) |
|---|---|---:|---:|---:|---:|---:|


## Separate post-campaign exact-engine agreement

Original complete-unverified statuses remain unchanged above. This layer uses trusted deterministic Julia F4, not an ideal-membership witness/cofactor certificate.
Wide Julia observations have one repetition; this is not a robust competitive-win claim.

| Field/input | Native checked answers | Julia checked answers | Trusted reference |
|---|---:|---:|---|
| wide64/katsura-4 | 21 | 3 | Groebner.jl deterministic, p=1 |
| wide64/cyclic-7 | 21 | 3 | Groebner.jl deterministic, p=1 |
| wide64/mq-random-10 | 21 | 2 | Groebner.jl deterministic, p=1 |

Rust p=8 partial diagnostic retains eight CPU-active hot-call participants after exact known-basis checking. Its parent coefficient check was interrupted: process wall/exit metadata are unavailable, so no full-process observation or ratio is fabricated. Rust p=16 hot diagnostics were not attempted.
