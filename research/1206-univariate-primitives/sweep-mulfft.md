zeebra binary: <CARGO_TARGET_DIR>/release/examples/univariate_primitives
flint driver: flint-primitives-driver contract 1
flint driver: flint 3.6.0 (headers 3.6.0), gmp 6.3.0
flint driver: driver cflags: -O2 -std=gnu17 -mcpu=native
flint driver: flint threads: 1
ntl driver: ntl-primitives-driver contract 1
ntl driver: ntl 11.6.0
ntl driver: driver cflags: -O2 -std=c++17 -mcpu=native
affinity: unpinned
rounds: 3, cap: 2s a call

| field | primitive | n | Zeebra (ms) | FLINT (ms) | NTL (ms) | Zeebra / FLINT | Zeebra / NTL |
|---|---|--:|--:|--:|--:|--:|--:|
| koalabear | mulfft | 256 | 0.014 | 0.009 | 0.017 | 1.53 | 0.85 |
| koalabear | mulfft | 512 | 0.044 | 0.017 | 0.025 | 2.56 | 1.77 |
| koalabear | mulfft | 1024 | 0.134 | 0.034 | 0.053 | 3.97 | 2.50 |
| koalabear | mulfft | 2048 | 0.287 | 0.035 | 0.115 | 8.19 | 2.50 |
| koalabear | mulfft | 4096 | 0.601 | 0.070 | 0.237 | 8.57 | 2.54 |
| koalabear | mulfft | 8192 | 1.283 | 0.147 | 0.511 | 8.72 | 2.51 |
| koalabear | mulfft | 16384 | 2.881 | 0.307 | 1.179 | 9.38 | 2.44 |
| koalabear | mulfft | 32768 | 6.658 | 0.657 | 2.425 | 10.13 | 2.75 |
| koalabear | mulfft | 65536 | 14.255 | 1.394 | 6.230 | 10.23 | 2.29 |
| koalabear | mulfft | 131072 | 31.171 | 3.152 | 12.671 | 9.89 | 2.46 |
| koalabear | mulfft | 262144 | 66.218 | 7.231 | 27.603 | 9.16 | 2.40 |
| koalabear | mulfft | 524288 | 143.579 | 16.076 | 57.344 | 8.93 | 2.50 |
| koalabear | mulfft | 1048576 | 292.017 | 34.958 | 122.882 | 8.35 | 2.38 |
| goldilocks | mulfft | 256 | 0.039 | 0.016 | 0.033 | 2.47 | 1.19 |
| goldilocks | mulfft | 512 | 0.080 | 0.031 | 0.066 | 2.62 | 1.22 |
| goldilocks | mulfft | 1024 | 0.172 | 0.060 | 0.142 | 2.85 | 1.21 |
| goldilocks | mulfft | 2048 | 0.353 | 0.128 | 0.292 | 2.75 | 1.21 |
| goldilocks | mulfft | 4096 | 0.771 | 0.266 | 0.598 | 2.89 | 1.29 |
| goldilocks | mulfft | 8192 | 1.773 | 0.547 | 1.249 | 3.24 | 1.42 |
| goldilocks | mulfft | 16384 | 3.981 | 1.136 | 2.605 | 3.50 | 1.53 |
| goldilocks | mulfft | 32768 | 8.807 | 2.408 | 5.666 | 3.66 | 1.55 |
| goldilocks | mulfft | 65536 | 19.055 | 5.177 | 13.223 | 3.68 | 1.44 |
| goldilocks | mulfft | 131072 | 40.199 | 11.027 | 26.609 | 3.65 | 1.51 |
| goldilocks | mulfft | 262144 | 88.632 | 23.987 | 55.088 | 3.70 | 1.61 |
| goldilocks | mulfft | 524288 | 183.464 | 53.729 | 117.628 | 3.41 | 1.56 |
| goldilocks | mulfft | 1048576 | 399.317 | 108.681 | 227.663 | 3.67 | 1.75 |
| p64m59 | mulfft | 256 | 0.022 | 0.015 | 0.032 | 1.44 | 0.69 |
| p64m59 | mulfft | 512 | 0.065 | 0.030 | 0.064 | 2.17 | 1.02 |
| p64m59 | mulfft | 1024 | 0.195 | 0.060 | 0.133 | 3.27 | 1.46 |
| p64m59 | mulfft | 2048 | 0.579 | 0.127 | 0.275 | 4.57 | 2.11 |
| p64m59 | mulfft | 4096 | 1.722 | 0.256 | 0.557 | 6.73 | 3.09 |
| p64m59 | mulfft | 8192 | 5.225 | 0.524 | 1.156 | 9.97 | 4.52 |
| p64m59 | mulfft | 16384 | 15.638 | 1.118 | 2.520 | 13.98 | 6.20 |
| p64m59 | mulfft | 32768 | 47.704 | 2.384 | 5.363 | 20.01 | 8.90 |
| p64m59 | mulfft | 65536 | 139.541 | 5.874 | 12.936 | 23.75 | 10.79 |
| p64m59 | mulfft | 131072 | 422.874 | 12.059 | 27.398 | 35.07 | 15.43 |
| p64m59 | mulfft | 262144 | 1251.942 | 24.515 | 53.408 | 51.07 | 23.44 |
| p64m59 | mulfft | 524288 | 3745.471 | 50.398 | 111.679 | 74.32 | 33.54 |
| bn254fr | mulfft | 256 | 0.385 | 0.171 | 0.079 | 2.24 | 4.90 |
| bn254fr | mulfft | 512 | 0.807 | 0.354 | 0.163 | 2.28 | 4.96 |
| bn254fr | mulfft | 1024 | 1.732 | 0.713 | 0.332 | 2.43 | 5.23 |
| bn254fr | mulfft | 2048 | 3.707 | 1.492 | 0.698 | 2.48 | 5.31 |
| bn254fr | mulfft | 4096 | 7.932 | 3.037 | 1.448 | 2.61 | 5.48 |
| bn254fr | mulfft | 8192 | 16.962 | 6.299 | 3.185 | 2.69 | 5.33 |
| bn254fr | mulfft | 16384 | 36.090 | 13.133 | 6.767 | 2.75 | 5.33 |
| bn254fr | mulfft | 32768 | 77.938 | 27.584 | 14.750 | 2.83 | 5.28 |
| bn254fr | mulfft | 65536 | 168.813 | 63.484 | 33.955 | 2.66 | 4.97 |
| bn254fr | mulfft | 131072 | 343.305 | 129.720 | 69.320 | 2.65 | 4.95 |
| bn254fr | mulfft | 262144 | 724.075 | 269.270 | 143.570 | 2.69 | 5.04 |
| bn254fr | mulfft | 524288 | 1533.817 | 544.948 | 297.925 | 2.81 | 5.15 |
| bn254fr | mulfft | 1048576 | 3424.160 | 1110.497 | 616.568 | 3.08 | 5.55 |
