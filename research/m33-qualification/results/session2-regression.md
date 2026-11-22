### Regression read (plan §12.2), F2 ÷ F0

| Row | Engine | Workers | Method | F0 median | n | F2 ÷ F0 wall [95%] | Peak RSS ratio | Excluded |
|---|---|---:|---|---:|---:|---|---:|---:|
| grevlex/gf32003/cyclic-7 | entry | 1 | warm calls | 4948.0 ms | 31 | 1.001 [0.998, 1.006] | 1.005 | 0 |
| grevlex/gf32003/cyclic-7 | entry | 4 | warm calls | 2533.0 ms | 54 | 1.007 [1.002, 1.016] | 1.005 | 3 |
| grevlex/gf32003/cyclic-7 | entry | 8 | warm calls | 2300.9 ms | 34 | 1.005 [1.005, 1.006] | 1.003 | 24 |
| grevlex/gf32003/cyclic-7 | entry | 16 | warm calls | 2515.5 ms | 31 | 1.006 [1.004, 1.008] | 1.003 | 0 |
| grevlex/gf32003/cyclic-7 | f4 | 1 | warm calls | 4943.5 ms | 31 | 1.002 [0.992, 1.004] | 1.002 | 0 |
| grevlex/gf32003/cyclic-7 | f4 | 4 | warm calls | 2529.7 ms | 55 | 1.013 [1.000, 1.017] | 1.005 | 2 |
| grevlex/gf32003/cyclic-7 | f4 | 8 | warm calls | 2300.3 ms | 34 | 1.006 [1.005, 1.006] | 1.011 | 24 |
| grevlex/gf32003/cyclic-7 | f4 | 16 | warm calls | 2514.8 ms | 31 | 1.007 [1.006, 1.009] | 0.995 | 0 |
| grevlex/gf32003/katsura-4 | entry | 1 | warm calls | 6.5 ms | 31 | 1.006 [0.998, 1.012] | 1.000 | 0 |
| grevlex/gf32003/katsura-4 | entry | 4 | warm calls | 6.9 ms | 31 | 0.999 [0.995, 1.003] | 0.996 | 0 |
| grevlex/gf32003/katsura-4 | entry | 8 | warm calls | 7.1 ms | 31 | 1.001 [0.992, 1.006] | 1.000 | 0 |
| grevlex/gf32003/katsura-4 | entry | 16 | warm calls | 7.1 ms | 31 | 1.003 [0.996, 1.009] | 1.000 | 0 |
| grevlex/gf32003/katsura-4 | f4 | 1 | warm calls | 6.4 ms | 31 | 1.002 [0.991, 1.004] | 1.002 | 0 |
| grevlex/gf32003/katsura-4 | f4 | 4 | warm calls | 6.8 ms | 31 | 0.998 [0.994, 1.005] | 1.000 | 0 |
| grevlex/gf32003/katsura-4 | f4 | 8 | warm calls | 7.0 ms | 31 | 1.002 [0.996, 1.007] | 1.000 | 0 |
| grevlex/gf32003/katsura-4 | f4 | 16 | warm calls | 7.0 ms | 33 | 0.997 [0.990, 1.003] | 1.004 | 3 |
| grevlex/gf32003/noon-7 | entry | 1 | warm calls | 1105.5 ms | 31 | 0.621 [0.619, 0.629] | 0.881 | 0 |
| grevlex/gf32003/noon-7 | entry | 4 | warm calls | 1129.8 ms | 32 | 0.629 [0.622, 0.633] | 0.889 | 18 |
| grevlex/gf32003/noon-7 | entry | 8 | warm calls | 1236.1 ms | 31 | 0.626 [0.624, 0.628] | 0.908 | 0 |
| grevlex/gf32003/noon-7 | entry | 16 | warm calls | 1291.5 ms | 31 | 0.640 [0.637, 0.644] | 0.894 | 0 |
| grevlex/gf32003/noon-7 | f4 | 1 | warm calls | 3314.7 ms | 31 | 1.008 [1.004, 1.018] | 0.995 | 0 |
| grevlex/gf32003/noon-7 | f4 | 4 | warm calls | 2510.0 ms | 32 | 1.007 [0.997, 1.018] | 1.014 | 20 |
| grevlex/gf32003/noon-7 | f4 | 8 | warm calls | 2556.2 ms | 31 | 1.003 [1.000, 1.005] | 1.008 | 0 |
| grevlex/gf32003/noon-7 | f4 | 16 | warm calls | 3121.2 ms | 31 | 1.005 [0.999, 1.008] | 1.016 | 0 |
| grevlex/goldilocks/katsura-11 | entry | 1 | process wall | 860.4 ms | 12 | 0.805 [0.796, 0.816] | 0.841 | 6 |
| grevlex/goldilocks/katsura-11 | entry | 16 | process wall | 547.5 ms | 15 | 0.719 [0.714, 0.727] | 0.838 | 3 |
| grevlex/goldilocks/katsura-11 | f4 | 1 | process wall | 9519.4 ms | 18 | 1.025 [1.023, 1.027] | 1.004 | 0 |
| grevlex/goldilocks/katsura-11 | f4 | 16 | process wall | 1293.4 ms | 11 | 1.006 [1.000, 1.010] | 1.009 | 15 |
| grevlex/m31/eco-11 | entry | 1 | process wall | 394.6 ms | 17 | 0.777 [0.770, 0.788] | 0.824 | 1 |
| grevlex/m31/eco-11 | entry | 4 | process wall | 312.6 ms | 18 | 0.728 [0.720, 0.734] | 0.823 | 0 |
| grevlex/m31/eco-11 | entry | 8 | process wall | 300.4 ms | 9 | 0.708 [0.705, 0.715] | 0.808 | 0 |
| grevlex/m31/eco-11 | entry | 16 | process wall | 318.4 ms | 13 | 0.728 [0.719, 0.733] | 0.818 | 5 |
| grevlex/m31/eco-11 | f4 | 1 | process wall | 1281.4 ms | 18 | 1.003 [0.990, 1.013] | 1.018 | 0 |
| grevlex/m31/eco-11 | f4 | 4 | process wall | 509.1 ms | 13 | 1.018 [0.997, 1.026] | 1.004 | 6 |
| grevlex/m31/eco-11 | f4 | 8 | process wall | 411.5 ms | 9 | 1.010 [1.008, 1.012] | 1.022 | 0 |
| grevlex/m31/eco-11 | f4 | 16 | process wall | 402.6 ms | 15 | 1.007 [0.999, 1.012] | 0.994 | 4 |
| grevlex/wide64/cyclic-7 | entry | 1 | warm calls | 5291.3 ms | 31 | 1.018 [1.016, 1.020] | 0.985 | 0 |
| grevlex/wide64/cyclic-7 | entry | 16 | warm calls | 2606.8 ms | 31 | 1.001 [1.000, 1.003] | 1.006 | 0 |
| grevlex/wide64/cyclic-7 | f4 | 1 | warm calls | 5297.3 ms | 31 | 1.018 [1.015, 1.023] | 0.980 | 0 |
| grevlex/wide64/cyclic-7 | f4 | 16 | warm calls | 2606.9 ms | 31 | 1.001 [0.999, 1.004] | 1.013 | 0 |
| grevlex/wide64/katsura-4 | entry | 1 | warm calls | 9.2 ms | 31 | 0.999 [0.997, 1.005] | 1.000 | 0 |
| grevlex/wide64/katsura-4 | entry | 16 | warm calls | 9.6 ms | 33 | 0.999 [0.994, 1.005] | 0.998 | 2 |
| grevlex/wide64/katsura-4 | f4 | 1 | warm calls | 9.2 ms | 31 | 1.004 [1.001, 1.006] | 1.000 | 0 |
| grevlex/wide64/katsura-4 | f4 | 16 | warm calls | 9.6 ms | 34 | 1.006 [1.001, 1.012] | 1.001 | 1 |
| grevlex/wide64/katsura-9 | entry | 1 | warm calls | 533.1 ms | 20 | 0.676 [0.670, 0.690] | 0.999 | 11 |
| grevlex/wide64/katsura-9 | entry | 16 | warm calls | 513.3 ms | 7 | 0.603 [0.601, 0.606] | 1.003 | 27 |
| grevlex/wide64/katsura-9 | f4 | 1 | warm calls | 3007.1 ms | 31 | 1.014 [1.011, 1.022] | 1.003 | 0 |
| grevlex/wide64/katsura-9 | f4 | 16 | warm calls | 1139.3 ms | 5 | 0.999 [0.993, 1.003] | 1.000 | 35 |
| grevlex/wide64/noon-7 | entry | 1 | warm calls | 1131.4 ms | 34 | 0.620 [0.618, 0.623] | 0.921 | 2 |
| grevlex/wide64/noon-7 | entry | 16 | warm calls | 1333.7 ms | 36 | 0.641 [0.639, 0.647] | 0.926 | 0 |
| grevlex/wide64/noon-7 | f4 | 1 | warm calls | 3448.9 ms | 34 | 1.004 [0.999, 1.008] | 0.994 | 2 |
| grevlex/wide64/noon-7 | f4 | 16 | warm calls | 3199.4 ms | 34 | 1.003 [0.999, 1.007] | 0.971 | 2 |
| grevlex/wide64/noon-8 | entry | 1 | process wall | 493.5 ms | 11 | 0.742 [0.728, 0.756] | 0.830 | 3 |
| grevlex/wide64/noon-8 | entry | 16 | process wall | 518.1 ms | 11 | 0.756 [0.739, 0.761] | 0.832 | 3 |
| grevlex/wide64/noon-8 | f4 | 1 | process wall | 1309.9 ms | 9 | 0.991 [0.987, 1.014] | 1.000 | 0 |
| grevlex/wide64/noon-8 | f4 | 16 | process wall | 894.0 ms | 9 | 1.009 [0.998, 1.026] | 0.996 | 0 |

| Row | Engine | Workers | Method | Verdict |
|---|---|---:|---|---|
| grevlex/gf32003/cyclic-7 | entry | 1 | warm calls | pass |
| grevlex/gf32003/cyclic-7 | entry | 4 | warm calls | pass |
| grevlex/gf32003/cyclic-7 | entry | 8 | warm calls | pass |
| grevlex/gf32003/cyclic-7 | entry | 16 | warm calls | pass |
| grevlex/gf32003/cyclic-7 | f4 | 1 | warm calls | pass |
| grevlex/gf32003/cyclic-7 | f4 | 4 | warm calls | pass |
| grevlex/gf32003/cyclic-7 | f4 | 8 | warm calls | pass |
| grevlex/gf32003/cyclic-7 | f4 | 16 | warm calls | pass |
| grevlex/gf32003/katsura-4 | entry | 1 | warm calls | pass |
| grevlex/gf32003/katsura-4 | entry | 4 | warm calls | pass |
| grevlex/gf32003/katsura-4 | entry | 8 | warm calls | pass |
| grevlex/gf32003/katsura-4 | entry | 16 | warm calls | pass |
| grevlex/gf32003/katsura-4 | f4 | 1 | warm calls | pass |
| grevlex/gf32003/katsura-4 | f4 | 4 | warm calls | pass |
| grevlex/gf32003/katsura-4 | f4 | 8 | warm calls | pass |
| grevlex/gf32003/katsura-4 | f4 | 16 | warm calls | pass |
| grevlex/gf32003/noon-7 | entry | 1 | warm calls | pass |
| grevlex/gf32003/noon-7 | entry | 4 | warm calls | pass |
| grevlex/gf32003/noon-7 | entry | 8 | warm calls | pass |
| grevlex/gf32003/noon-7 | entry | 16 | warm calls | pass |
| grevlex/gf32003/noon-7 | f4 | 1 | warm calls | pass |
| grevlex/gf32003/noon-7 | f4 | 4 | warm calls | pass |
| grevlex/gf32003/noon-7 | f4 | 8 | warm calls | pass |
| grevlex/gf32003/noon-7 | f4 | 16 | warm calls | pass |
| grevlex/goldilocks/katsura-11 | entry | 1 | process wall | pass |
| grevlex/goldilocks/katsura-11 | entry | 16 | process wall | pass |
| grevlex/goldilocks/katsura-11 | f4 | 1 | process wall | pass |
| grevlex/goldilocks/katsura-11 | f4 | 16 | process wall | pass |
| grevlex/m31/eco-11 | entry | 1 | process wall | pass |
| grevlex/m31/eco-11 | entry | 4 | process wall | pass |
| grevlex/m31/eco-11 | entry | 8 | process wall | pass |
| grevlex/m31/eco-11 | entry | 16 | process wall | pass |
| grevlex/m31/eco-11 | f4 | 1 | process wall | pass |
| grevlex/m31/eco-11 | f4 | 4 | process wall | pass |
| grevlex/m31/eco-11 | f4 | 8 | process wall | pass |
| grevlex/m31/eco-11 | f4 | 16 | process wall | pass |
| grevlex/wide64/cyclic-7 | entry | 1 | warm calls | pass |
| grevlex/wide64/cyclic-7 | entry | 16 | warm calls | pass |
| grevlex/wide64/cyclic-7 | f4 | 1 | warm calls | pass |
| grevlex/wide64/cyclic-7 | f4 | 16 | warm calls | pass |
| grevlex/wide64/katsura-4 | entry | 1 | warm calls | pass |
| grevlex/wide64/katsura-4 | entry | 16 | warm calls | pass |
| grevlex/wide64/katsura-4 | f4 | 1 | warm calls | pass |
| grevlex/wide64/katsura-4 | f4 | 16 | warm calls | pass |
| grevlex/wide64/katsura-9 | entry | 1 | warm calls | wall stopped: n = 20 < 31 |
| grevlex/wide64/katsura-9 | entry | 16 | warm calls | wall stopped: n = 7 < 31 |
| grevlex/wide64/katsura-9 | f4 | 1 | warm calls | pass |
| grevlex/wide64/katsura-9 | f4 | 16 | warm calls | wall stopped: n = 5 < 31 |
| grevlex/wide64/noon-7 | entry | 1 | warm calls | pass |
| grevlex/wide64/noon-7 | entry | 16 | warm calls | pass |
| grevlex/wide64/noon-7 | f4 | 1 | warm calls | pass |
| grevlex/wide64/noon-7 | f4 | 16 | warm calls | pass |
| grevlex/wide64/noon-8 | entry | 1 | process wall | pass |
| grevlex/wide64/noon-8 | entry | 16 | process wall | pass |
| grevlex/wide64/noon-8 | f4 | 1 | process wall | pass |
| grevlex/wide64/noon-8 | f4 | 16 | process wall | pass |
