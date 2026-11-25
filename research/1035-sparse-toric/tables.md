## Reproduction: the paper's shapes (development)

Seeds 1–2. Where both seeds complete, the F4 extents are equal on every unperturbed shape, so one figure is shown; `—` marks a shape the example does not instantiate.

| table | n_x | n_y | m | sparse d_wit | sparse rank × columns | F4 largest | F4 step degree | advantage | control: sparse d_wit, columns | control: F4 |
|---|---:|---:|---:|---:|---|---|---:|---:|---|---|
| 1 | 2 | 29 | 40 | 2 | 2,790 × 2,790 | 10,187 × 5,897 | 3 | 7.72 | 7, 2.82e+12 | refused 2/2 (`TooManyNonzeros`) |
| 1 | 2 | 39 | 53 | 2 | 4,920 × 4,920 | — | — | — | 8, 1.34e+15 | — |
| 1 | 2 | 49 | 65 | 2 | 7,650 × 7,650 | — | — | — | 9, 5.15e+17 | — |
| 1 | 2 | 59 | 78 | 2 | 10,980 × 10,980 | — | — | — | 10, 1.75e+20 | — |
| 1 | 6 | 19 | 52 | 2 | 5,880 × 5,880 | 14,458 × 11,436 | 4 | 4.78 | 4, 4.66e+08 | refused 2/2 (`TooManyNonzeros`) |
| 1 | 6 | 21 | 56 | 2 | 7,084 × 7,084 | 18,014 × 14,686 | 4 | 5.27 | 5, 2.05e+10 | refused 2/2 (`TooManyNonzeros`) |
| 1 | 6 | 27 | 71 | 2 | 11,368 × 11,368 | — | — | — | 5, 1.61e+11 | — |
| 2 | 1 | 34 | 36 | 2 | 3,150 × 3,150 | — | — | — | 19, 1.55e+22 | — |
| 2 | 1 | 39 | 41 | 2 | 4,100 × 4,100 | — | — | — | 22, 3.27e+25 | — |
| 2 | 1 | 44 | 46 | 2 | 5,175 × 5,175 | — | — | — | 24, 1.85e+28 | — |
| 2 | 2 | 15 | 25 | 2 | 2,040 × 2,040 | 2,495 × 2,881 | 4 | 1.73 | 4, 2.21e+07 | refused 2/2 (`TooManyNonzeros`) |
| 2 | 2 | 17 | 27 | 2 | 2,565 × 2,565 | 7,616 × 5,805 | 5 | 6.72 | 5, 5.57e+08 | refused 2/2 (`TooManyNonzeros`) |
| 2 | 2 | 19 | 30 | 2 | 3,150 × 3,150 | 10,392 × 7,755 | 5 | 8.12 | 5, 1.32e+09 | refused 2/2 (`TooManyNonzeros`) |
| 2 | 3 | 10 | 24 | 2 | 2,310 × 2,310 | 2,809 × 3,035 | 5 | 1.60 | 4, 7.22e+06 | 8,516 × 8,061 |
| 2 | 10 | 4 | 50 | 2 | 15,015 × 15,015 | refused 2/2 (`TooManyNonzeros`) | 6 | — | 3, 1.68e+06 | refused 2/2 (`TooManyNonzeros`) |
| 2 | 11 | 5 | 66 | 2 | 28,665 × 28,665 | refused 2/2 (`TooManyNonzeros`) | 6 | — | 3, 5.72e+06 | refused 2/2 (`TooManyNonzeros`) |
| 2 | 12 | 6 | 86 | 2 | 50,960 × 50,960 | refused 2/2 (`TooManyNonzeros`) | 5 | — | 3, 1.72e+07 | refused 2/2 (`TooManyNonzeros`) |
| 2-source | 1 | 14 | 16 | 2 | 600 × 600 | 529 × 811 | 3 | 1.19 | 9, 8.96e+09 | refused 2/2 (`TooManyNonzeros`) |
| 2-source | 1 | 19 | 21 | 2 | 1,050 × 1,050 | 1,065 × 1,766 | 3 | 1.71 | 12, 2e+13 | refused 2/2 (`TooManyNonzeros`) |
| 2-source | 1 | 24 | 26 | 2 | 1,625 × 1,625 | 1,875 × 3,271 | 3 | 2.32 | 14, 1.24e+16 | refused 2/2 (`TooManyNonzeros`) |
| 2-source | 1 | 29 | 31 | 2 | 2,325 × 2,325 | — | — | — | 17, 2.66e+19 | — |
| 2-source | 2 | 4 | 9 | 2 | 225 × 225 | 112 × 170 | 4 | 0.38 | 3, 5,880 | 386 × 394 |
| 2-source | 2 | 7 | 13 | 2 | 540 × 540 | 404 × 484 | 4 | 0.67 | 4, 289,575 | 2,371 × 1,831 |
| 2-source | 2 | 9 | 16 | 2 | 825 × 825 | 2,040 × 1,277 | 4 | 3.83 | 4, 1.09e+06 | 4,359 × 3,890 |
| 2-source | 2 | 11 | 19 | 2 | 1,170 × 1,170 | 1,853 × 2,277 | 4 | 3.08 | 4, 3.4e+06 | refused 1/2 (`TooManyNonzeros`) |
| 2-source | 2 | 13 | 22 | 2 | 1,575 × 1,575 | 1,923 × 2,016 | 4 | 1.56 | 4, 9.16e+06 | refused 2/2 (`TooManyNonzeros`) |
| 2-source | 3 | 6 | 16 | 2 | 980 × 980 | 680 × 998 | 5 | 0.71 | 3, 77,616 | 3,328 × 1,691 |
| 2-source | 3 | 7 | 18 | 2 | 1,260 × 1,260 | 910 × 1,363 | 5 | 0.78 | 3, 144,144 | 4,678 × 2,725 |
| 2-source | 3 | 8 | 20 | 2 | 1,575 × 1,575 | 1,234 × 1,834 | 5 | 0.91 | 3, 252,252 | 6,587 × 4,012 |
| 2-source | 3 | 9 | 22 | 2 | 1,925 × 1,925 | 2,369 × 2,398 | 5 | 1.53 | 3, 420,420 | 8,058 × 5,677 |
| 2-source | 14 | 1 | 42 | 2 | 9,180 × 9,180 | 9,489 × 14,597 | 5 | 1.64 | 3, 271,320 | refused 2/2 (`TooManyNonzeros`) |
| 2-source | 8 | 2 | 25 | 2 | 2,970 × 2,970 | 4,296 × 2,798 | 5 | 1.36 | 3, 84,084 | 4,349 × 2,896 |
| 2-source | 9 | 2 | 29 | 2 | 4,290 × 4,290 | 5,857 × 4,145 | 5 | 1.32 | 3, 140,140 | 5,922 × 4,260 |
| 2-source | 10 | 2 | 33 | 2 | 6,006 × 6,006 | 7,069 × 5,408 | 5 | 1.06 | 3, 224,224 | 7,366 × 5,875 |
| 2-source | 11 | 2 | 39 | 2 | 8,190 × 8,190 | 10,817 × 7,593 | 5 | 1.22 | 3, 346,528 | 11,198 × 8,174 |
| 2-source | 12 | 2 | 44 | 2 | 10,920 × 10,920 | 14,231 × 10,448 | 5 | 1.25 | 3, 519,792 | 14,735 × 11,189 |
| 2-source | 13 | 2 | 50 | 2 | 14,280 × 14,280 | refused 2/2 (`TooManyNonzeros`) | 5 | — | 3, 759,696 | refused 2/2 (`TooManyNonzeros`) |
| 2-source | 14 | 2 | 56 | 2 | 18,360 × 18,360 | refused 2/2 (`TooManyNonzeros`) | 5 | — | 3, 1.09e+06 | refused 2/2 (`TooManyNonzeros`) |
| 2-source | 8 | 3 | 30 | 2 | 4,950 × 4,950 | 5,862 × 3,774 | 5 | 0.90 | 3, 252,252 | 3,898 × 3,961 |
| 2-source | 9 | 3 | 36 | 2 | 7,150 × 7,150 | 8,784 × 5,261 | 5 | 0.90 | 3, 420,420 | 6,093 × 5,678 |
| 2-source | 10 | 5 | 43 | 3 | 448,448 × 448,448 | refused 2/2 (`TooManyNonzeros`) | 6 | — | 3, 3.7e+06 | refused 2/2 (`TooManyNonzeros`) |

Advantage over 27 completed shapes: min 0.38, median 1.53, max 8.12; 0 at ≥ 10×, 7 below 1×.

## Public panel: the eligible problems (development)

| problem | blocks (n_j, degree) | normalized volume | affine solutions | sparse d_wit | sparse rank × columns | F4 largest | advantage |
|---|---|---:|---:|---:|---|---|---:|
| `sd-ellipsoid-4` | (4, 1), (6, 12) | — | — | — | not counted: fewer generators than variables: not zero-dimensional, Lemma 5 does not apply | — | — |
| `gen-phosphorylation-5` | (16, 1), (2, 1) | 153 | 11 | 3 | 9,537 × 9,690 | 466 × 582 | 0.0029 |
| `gen-phosphorylation-6` | (2, 1), (19, 1) | 210 | 13 | 3 | 15,190 × 15,400 | 737 × 944 | 0.003 |
| `gen-phosphorylation-7` | (2, 1), (22, 1) | 276 | 15 | 3 | 22,724 × 23,000 | 1,095 × 1,432 | 0.003 |
| `gen-phosphorylation-2-nonzero` | (5, 5), (5, 1) | 787,500 | 5 | 6 | 1.49e+08 × 1.5e+08 | 55 × 62 | 1.5e-13 |
| `gen-phosphorylation-4-nonzero` | (7, 7), (9, 1) | 9.42e+09 | 9 | 8 | 1.34e+13 × 1.35e+13 | 270 × 327 | 4.9e-22 |
| `gen-phosphorylation-6-nonzero` | (9, 9), (13, 1) | 1.93e+14 | 13 | 10 | 1.98e+18 × 1.98e+18 | 1,019 × 1,032 | 2.7e-31 |

Largest advantage on an eligible public problem: 0.003.

**Predeclared decision:** disproved: the advantage is under 3× on every eligible public problem.
