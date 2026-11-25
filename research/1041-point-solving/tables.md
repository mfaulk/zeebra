Rates (slower of two calibration runs, one core): GF(31) 7.93e+09 multiply-adds/s, GF(2) 1.05e+10 word operations/s.

| family | n | m | Zeebra pipeline | attempts | hybrid best (k) | crossbred (k, D, d) | XL + BW (D) | best alternative | Zeebra ÷ best |
|---|---:|---:|---|---:|---|---|---|---|---:|
| A | 6 | 12 | 563.4 µs | 1 | 8.5 ms (1) | 2.2 ms (3, 2, 1) | 74.7 µs (3) | XL + BW | 7.54 |
| A | 8 | 16 | 1.5 ms | 1 | 18.1 ms (1) | 170.8 ms (4, 2, 1) | 463.3 µs (3) | XL + BW | 3.14 |
| A | 10 | 20 | 17.1 ms | 1 | 81.8 ms (1) | 25.8 ms (7, 3, 1) | 25.0 ms (4) | XL + BW | 0.69 |
| A | 12 | 24 | 94.9 ms | 1 | 1.05 s (1) | 1.33 s (8, 3, 1) | 114.0 ms (4) | XL + BW | 0.83 |
| A | 14 | 28 | 479.0 ms | 1 | 6.14 s (1) | 418.20 s (10, 3, 2) | 424.9 ms (4) | XL + BW | 1.13 |
| A | 16 | 32 | 14.13 s | 1 | 28.02 s (1) | 2.71 s (14, 4, 2) | 23.96 s (5) | crossbred | 5.22 |
| A | 18 | 36 | 92.07 s | 1 | 125.16 s (1) | 1,055.54 s (16, 4, 3) | 81.36 s (5) | XL + BW | 1.13 |
| B | 6 | 4 | 503.5 µs | 1.5 | 6.0 ms (1) | 17.3 µs (2, 3, 1) | 142.5 µs (5) | crossbred | 29.05 |
| B | 9 | 6 | 3.7 ms | 1.5 | 13.2 ms (1) | 191.8 µs (4, 5, 1) | 49.3 ms (7) | crossbred | 19.07 |
| B | 12 | 8 | 68.2 ms | 1 | 186.9 ms (1) | 7.7 ms (5, 5, 1) | 15.91 s (9) | crossbred | 8.89 |
| B | 15 | 10 | 3.21 s | 1 | 6.28 s (1) | 502.5 ms (6, 6, 1) | 4,912.50 s (11) | crossbred | 6.40 |
| C | 8 | 16 | 653.3 µs | 1 | 812.2 µs (1) | 2.4 µs (5, 2, 1) | 1.4 µs (3) | XL + BW | 458.84 |
| C | 12 | 24 | 3.1 ms | 1 | 3.8 ms (1) | 37.3 µs (6, 2, 1) | 31.4 µs (3) | XL + BW | 98.52 |
| C | 16 | 32 | 36.7 ms | 1 | 25.9 ms (2) | 542.0 µs (7, 2, 1) | 3.9 ms (4) | crossbred | 67.74 |
| C | 20 | 40 | 249.2 ms | 1 | 236.7 ms (4) | 2.4 ms (12, 3, 1) | 36.0 ms (4) | crossbred | 101.86 |
| C | 24 | 48 | 2.47 s | 1 | 2.42 s (2) | 35.7 ms (12, 3, 1) | 224.6 ms (4) | crossbred | 69.26 |
| C | 28 | 56 | 96.89 s | 1 | 23.59 s (4) | 303.4 ms (13, 3, 1) | 27.14 s (5) | crossbred | 319.31 |
| D | 12 | 8 | 931.1 µs | 1 | 1.1 ms (1) | 1.7 µs (1, 2, 1) | 2.3 µs (3) | crossbred | 550.16 |
| D | 18 | 12 | 13.5 ms | 1.5 | 7.8 ms (3) | 29.0 µs (1, 2, 1) | 350.5 µs (4) | crossbred | 467.50 |
| D | 24 | 16 | 325.0 ms | 1.5 | 100.9 ms (3) | 560.9 µs (1, 2, 1) | 45.7 ms (5) | crossbred | 579.43 |
| D | 30 | 20 | 3.37 s | 1 | 1.28 s (4) | 11.0 ms (1, 2, 1) | 699.3 ms (5) | crossbred | 305.49 |

## Predeclared decision

At the largest size each family completes. A counted alternative is re-priced at r/4; the hybrid arm is measured and does not move with r.

| family | n | m | best alternative | Zeebra ÷ best at r | at r/4 |
|---|---:|---:|---|---:|---:|
| A | 18 | 36 | XL + BW | 1.13 | 0.28 |
| B | 15 | 10 | crossbred | 6.40 | 1.60 |
| C | 28 | 56 | crossbred | 319.31 | 79.83 |
| D | 30 | 20 | crossbred | 305.49 | 76.37 |

**Predeclared decision:** proceed: a bounded prototype proposal (families C, D).
