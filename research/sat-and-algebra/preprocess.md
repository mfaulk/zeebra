 16:01:09 up 3 days, 28 min,  1 user,  load average: 2.52, 2.42, 2.69
kissat: /buildcache/cargo-target/zeebra-220/prefix/bin/kissat; every model checked against the original system

Wall milliseconds, minimum of 3 (one run at n = 24), one kissat process per run; CNF cut at 4.

| instance | CNF clauses / vars | after elimination | kissat alone | eliminate + kissat | of which eliminate | ratio | F4 solve_one alone | F4 after elimination |
|---|---|---|---|---|---|---|---|---|
| n=16: 12 quadratics + 4 affine, seed 1 | 3636 / 533 | 2058 / 301 | 53.5 | 27.3 | 1.07 | 0.51 | 51.5 | 183.0 |
| n=16: 12 quadratics + 4 affine, seed 2 | 3564 / 525 | 1922 / 285 | 93.6 | 30.4 | 0.93 | 0.32 | 49.3 | 326.8 |
| n=16: 12 quadratics + 4 affine, seed 3 | 3596 / 529 | 1894 / 280 | 70.4 | 41.7 | 0.84 | 0.59 | 266.0 | 204.2 |
| n=16: 12 quadratics + 4 affine, seed 4 | 3612 / 530 | 2046 / 300 | 30.7 | 25.5 | 0.70 | 0.83 | 45.8 | 38.5 |
| n=16: 12 quadratics + 4 affine, seed 5 | 3612 / 531 | 1974 / 290 | 26.8 | 38.6 | 0.81 | 1.44 | 249.0 | 242.4 |
| n=20: 15 quadratics + 5 affine, seed 1 | 7050 / 1007 | 3775 / 542 | 561.9 | 47.2 | 2.31 | 0.08 | 35478.0 | refused: Grobner(TooManyColumns { limit: 200000 }) |
| n=20: 15 quadratics + 5 affine, seed 2 | 6946 / 993 | 3851 / 553 | 130.5 | 67.9 | 2.03 | 0.52 | 2653.2 | 2064.2 |
| n=20: 15 quadratics + 5 affine, seed 3 | 6882 / 983 | 3859 / 553 | 41.3 | 87.3 | 2.33 | 2.11 | 20416.4 | 2088.6 |
| n=20: 15 quadratics + 5 affine, seed 4 | 6974 / 994 | 3711 / 532 | 687.2 | 318.8 | 2.19 | 0.46 | 15887.7 | 14615.4 |
| n=20: 15 quadratics + 5 affine, seed 5 | 6774 / 970 | 3699 / 532 | 558.8 | 24.5 | 2.16 | 0.04 | 2737.5 | 1919.0 |
| n=24: 18 quadratics + 6 affine, seed 1 | 11864 / 1661 | 6299 / 886 | 23555.1 | 585.6 | 4.42 | 0.02 | not run | not run |
| n=24: 18 quadratics + 6 affine, seed 2 | 11816 / 1658 | 6575 / 922 | 13713.7 | 1846.3 | 4.12 | 0.13 | not run | not run |
| n=24: 18 quadratics + 6 affine, seed 3 | 11600 / 1629 | 6383 / 898 | 967.5 | 409.3 | 5.15 | 0.42 | not run | not run |
| n=24: 18 quadratics + 6 affine, seed 4 | 11628 / 1631 | 6455 / 908 | 10315.6 | 2759.1 | 4.72 | 0.27 | not run | not run |
| n=24: 18 quadratics + 6 affine, seed 5 | 11432 / 1606 | 6387 / 899 | 11687.3 | 3200.7 | 4.77 | 0.27 | not run | not run |
 16:04:08 up 3 days, 31 min,  1 user,  load average: 3.54, 3.64, 3.17
