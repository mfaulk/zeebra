### Regression read (plan §12.2), F2 ÷ F0

| Row | Engine | Workers | Method | F0 median | n | F2 ÷ F0 wall [95%] | Peak RSS ratio | Excluded |
|---|---|---:|---|---:|---:|---|---:|---:|
| grevlex/gf32003/cyclic-7 | entry | 1 | warm calls | 4948.0 ms | 31 | 1.001 [0.998, 1.006] | 1.005 | 0 |
| grevlex/gf32003/cyclic-7 | entry | 4 | warm calls | 2536.7 ms | 29 | 1.009 [1.002, 1.023] | 0.993 | 2 |
| grevlex/gf32003/cyclic-7 | entry | 8 | warm calls | 2300.4 ms | 14 | 1.005 [1.003, 1.006] | 0.997 | 18 |
| grevlex/gf32003/cyclic-7 | entry | 16 | warm calls | 2515.5 ms | 31 | 1.006 [1.004, 1.008] | 1.003 | 0 |
| grevlex/gf32003/cyclic-7 | f4 | 1 | warm calls | 4943.5 ms | 31 | 1.002 [0.992, 1.004] | 1.002 | 0 |
| grevlex/gf32003/cyclic-7 | f4 | 4 | warm calls | 2538.0 ms | 29 | 1.001 [0.995, 1.019] | 0.996 | 2 |
| grevlex/gf32003/cyclic-7 | f4 | 8 | warm calls | 2299.6 ms | 17 | 1.006 [1.004, 1.006] | 1.025 | 15 |
| grevlex/gf32003/cyclic-7 | f4 | 16 | warm calls | 2514.8 ms | 31 | 1.007 [1.006, 1.009] | 0.995 | 0 |
| grevlex/gf32003/katsura-4 | entry | 1 | warm calls | 6.5 ms | 31 | 1.006 [0.998, 1.012] | 1.000 | 0 |
| grevlex/gf32003/katsura-4 | entry | 4 | warm calls | 6.9 ms | 31 | 0.999 [0.995, 1.003] | 0.996 | 0 |
| grevlex/gf32003/katsura-4 | entry | 8 | warm calls | 7.1 ms | 31 | 1.001 [0.992, 1.006] | 1.000 | 0 |
| grevlex/gf32003/katsura-4 | entry | 16 | warm calls | 7.1 ms | 31 | 1.003 [0.996, 1.009] | 1.000 | 0 |
| grevlex/gf32003/katsura-4 | f4 | 1 | warm calls | 6.4 ms | 31 | 1.002 [0.991, 1.004] | 1.002 | 0 |
| grevlex/gf32003/katsura-4 | f4 | 4 | warm calls | 6.8 ms | 31 | 0.998 [0.994, 1.005] | 1.000 | 0 |
| grevlex/gf32003/katsura-4 | f4 | 8 | warm calls | 7.0 ms | 31 | 1.002 [0.996, 1.007] | 1.000 | 0 |
| grevlex/gf32003/katsura-4 | f4 | 16 | warm calls | 7.0 ms | 29 | 0.997 [0.990, 1.003] | 1.000 | 2 |
| grevlex/gf32003/noon-7 | entry | 1 | warm calls | 1105.5 ms | 31 | 0.621 [0.619, 0.629] | 0.881 | 0 |
| grevlex/gf32003/noon-7 | entry | 4 | warm calls | 1128.1 ms | 20 | 0.629 [0.621, 0.650] | 0.889 | 11 |
| grevlex/gf32003/noon-7 | entry | 8 | warm calls | 1236.1 ms | 31 | 0.626 [0.624, 0.628] | 0.908 | 0 |
| grevlex/gf32003/noon-7 | entry | 16 | warm calls | 1291.5 ms | 31 | 0.640 [0.637, 0.644] | 0.894 | 0 |
| grevlex/gf32003/noon-7 | f4 | 1 | warm calls | 3314.7 ms | 31 | 1.008 [1.004, 1.018] | 0.995 | 0 |
| grevlex/gf32003/noon-7 | f4 | 4 | warm calls | 2515.1 ms | 20 | 1.005 [0.996, 1.013] | 1.005 | 13 |
| grevlex/gf32003/noon-7 | f4 | 8 | warm calls | 2556.2 ms | 31 | 1.003 [1.000, 1.005] | 1.008 | 0 |
| grevlex/gf32003/noon-7 | f4 | 16 | warm calls | 3121.2 ms | 31 | 1.005 [0.999, 1.008] | 1.016 | 0 |
| grevlex/goldilocks/katsura-11 | entry | 1 | process wall | 854.7 ms | 6 | 0.810 [0.799, 0.831] | 0.843 | 3 |
| grevlex/goldilocks/katsura-11 | entry | 16 | process wall | 546.8 ms | 6 | 0.717 [0.707, 0.729] | 0.841 | 3 |
| grevlex/goldilocks/katsura-11 | f4 | 1 | process wall | 9496.7 ms | 9 | 1.025 [1.023, 1.027] | 1.004 | 0 |
| grevlex/goldilocks/katsura-11 | f4 | 16 | process wall | 1292.6 ms | 4 | 1.006 [1.001, 1.011] | 1.011 | 5 |
| grevlex/m31/eco-11 | entry | 1 | process wall | 394.9 ms | 8 | 0.775 [0.747, 0.794] | 0.825 | 1 |
| grevlex/m31/eco-11 | entry | 4 | process wall | 313.6 ms | 9 | 0.729 [0.717, 0.737] | 0.831 | 0 |
| grevlex/m31/eco-11 | entry | 8 | process wall | 300.4 ms | 9 | 0.708 [0.705, 0.715] | 0.808 | 0 |
| grevlex/m31/eco-11 | entry | 16 | process wall | 319.7 ms | 4 | 0.725 [0.718, 0.741] | 0.822 | 5 |
| grevlex/m31/eco-11 | f4 | 1 | process wall | 1276.4 ms | 9 | 1.010 [0.997, 1.016] | 1.017 | 0 |
| grevlex/m31/eco-11 | f4 | 4 | process wall | 509.4 ms | 4 | 1.010 [0.986, 1.046] | 1.014 | 6 |
| grevlex/m31/eco-11 | f4 | 8 | process wall | 411.5 ms | 9 | 1.010 [1.008, 1.012] | 1.022 | 0 |
| grevlex/m31/eco-11 | f4 | 16 | process wall | 403.2 ms | 6 | 1.002 [0.996, 1.017] | 1.016 | 4 |
| grevlex/wide64/cyclic-7 | entry | 1 | warm calls | 5291.3 ms | 31 | 1.018 [1.016, 1.020] | 0.985 | 0 |
| grevlex/wide64/cyclic-7 | entry | 16 | warm calls | 2606.8 ms | 31 | 1.001 [1.000, 1.003] | 1.006 | 0 |
| grevlex/wide64/cyclic-7 | f4 | 1 | warm calls | 5297.3 ms | 31 | 1.018 [1.015, 1.023] | 0.980 | 0 |
| grevlex/wide64/cyclic-7 | f4 | 16 | warm calls | 2606.9 ms | 31 | 1.001 [0.999, 1.004] | 1.013 | 0 |
| grevlex/wide64/katsura-4 | entry | 1 | warm calls | 9.2 ms | 31 | 0.999 [0.997, 1.005] | 1.000 | 0 |
| grevlex/wide64/katsura-4 | entry | 16 | warm calls | 9.6 ms | 30 | 1.000 [0.995, 1.005] | 0.999 | 1 |
| grevlex/wide64/katsura-4 | f4 | 1 | warm calls | 9.2 ms | 31 | 1.004 [1.001, 1.006] | 1.000 | 0 |
| grevlex/wide64/katsura-4 | f4 | 16 | warm calls | 9.7 ms | 30 | 1.006 [1.001, 1.009] | 0.999 | 1 |
| grevlex/wide64/katsura-9 | entry | 1 | warm calls | 533.1 ms | 20 | 0.676 [0.670, 0.690] | 0.999 | 11 |
| grevlex/wide64/katsura-9 | entry | 16 | warm calls | 513.3 ms | 7 | 0.603 [0.601, 0.606] | 1.003 | 27 |
| grevlex/wide64/katsura-9 | f4 | 1 | warm calls | 3007.1 ms | 31 | 1.014 [1.011, 1.022] | 1.003 | 0 |
| grevlex/wide64/katsura-9 | f4 | 16 | warm calls | 1139.3 ms | 5 | 0.999 [0.993, 1.003] | 1.000 | 35 |
| grevlex/wide64/noon-7 | entry | 1 | warm calls | 1130.9 ms | 29 | 0.621 [0.618, 0.623] | 0.925 | 2 |
| grevlex/wide64/noon-7 | entry | 16 | warm calls | 1333.5 ms | 31 | 0.641 [0.639, 0.645] | 0.926 | 0 |
| grevlex/wide64/noon-7 | f4 | 1 | warm calls | 3450.7 ms | 30 | 1.004 [0.999, 1.008] | 0.997 | 1 |
| grevlex/wide64/noon-7 | f4 | 16 | warm calls | 3197.6 ms | 29 | 1.004 [0.999, 1.008] | 0.971 | 2 |
| grevlex/wide64/noon-8 | entry | 1 | process wall | 492.3 ms | 8 | 0.748 [0.738, 0.757] | 0.830 | 1 |
| grevlex/wide64/noon-8 | entry | 16 | process wall | 516.2 ms | 7 | 0.757 [0.736, 0.761] | 0.836 | 2 |
| grevlex/wide64/noon-8 | f4 | 1 | process wall | 1309.9 ms | 9 | 0.991 [0.987, 1.014] | 1.000 | 0 |
| grevlex/wide64/noon-8 | f4 | 16 | process wall | 894.0 ms | 9 | 1.009 [0.998, 1.026] | 0.996 | 0 |

| Row | Engine | Workers | Method | Verdict |
|---|---|---:|---|---|
| grevlex/gf32003/cyclic-7 | entry | 1 | warm calls | pass |
| grevlex/gf32003/cyclic-7 | entry | 4 | warm calls | wall stopped: n = 29 < 31 |
| grevlex/gf32003/cyclic-7 | entry | 8 | warm calls | wall stopped: n = 14 < 31 |
| grevlex/gf32003/cyclic-7 | entry | 16 | warm calls | pass |
| grevlex/gf32003/cyclic-7 | f4 | 1 | warm calls | pass |
| grevlex/gf32003/cyclic-7 | f4 | 4 | warm calls | wall stopped: n = 29 < 31 |
| grevlex/gf32003/cyclic-7 | f4 | 8 | warm calls | wall stopped: n = 17 < 31 |
| grevlex/gf32003/cyclic-7 | f4 | 16 | warm calls | pass |
| grevlex/gf32003/katsura-4 | entry | 1 | warm calls | pass |
| grevlex/gf32003/katsura-4 | entry | 4 | warm calls | pass |
| grevlex/gf32003/katsura-4 | entry | 8 | warm calls | pass |
| grevlex/gf32003/katsura-4 | entry | 16 | warm calls | pass |
| grevlex/gf32003/katsura-4 | f4 | 1 | warm calls | pass |
| grevlex/gf32003/katsura-4 | f4 | 4 | warm calls | pass |
| grevlex/gf32003/katsura-4 | f4 | 8 | warm calls | pass |
| grevlex/gf32003/katsura-4 | f4 | 16 | warm calls | wall stopped: n = 29 < 31 |
| grevlex/gf32003/noon-7 | entry | 1 | warm calls | pass |
| grevlex/gf32003/noon-7 | entry | 4 | warm calls | wall stopped: n = 20 < 31 |
| grevlex/gf32003/noon-7 | entry | 8 | warm calls | pass |
| grevlex/gf32003/noon-7 | entry | 16 | warm calls | pass |
| grevlex/gf32003/noon-7 | f4 | 1 | warm calls | pass |
| grevlex/gf32003/noon-7 | f4 | 4 | warm calls | wall stopped: n = 20 < 31 |
| grevlex/gf32003/noon-7 | f4 | 8 | warm calls | pass |
| grevlex/gf32003/noon-7 | f4 | 16 | warm calls | pass |
| grevlex/goldilocks/katsura-11 | entry | 1 | process wall | wall stopped: n = 6 < 9 |
| grevlex/goldilocks/katsura-11 | entry | 16 | process wall | wall stopped: n = 6 < 9 |
| grevlex/goldilocks/katsura-11 | f4 | 1 | process wall | pass |
| grevlex/goldilocks/katsura-11 | f4 | 16 | process wall | wall stopped: n = 4 < 9 |
| grevlex/m31/eco-11 | entry | 1 | process wall | wall stopped: n = 8 < 9 |
| grevlex/m31/eco-11 | entry | 4 | process wall | pass |
| grevlex/m31/eco-11 | entry | 8 | process wall | pass |
| grevlex/m31/eco-11 | entry | 16 | process wall | wall stopped: n = 4 < 9 |
| grevlex/m31/eco-11 | f4 | 1 | process wall | pass |
| grevlex/m31/eco-11 | f4 | 4 | process wall | wall stopped: n = 4 < 9 |
| grevlex/m31/eco-11 | f4 | 8 | process wall | pass |
| grevlex/m31/eco-11 | f4 | 16 | process wall | wall stopped: n = 6 < 9 |
| grevlex/wide64/cyclic-7 | entry | 1 | warm calls | pass |
| grevlex/wide64/cyclic-7 | entry | 16 | warm calls | pass |
| grevlex/wide64/cyclic-7 | f4 | 1 | warm calls | pass |
| grevlex/wide64/cyclic-7 | f4 | 16 | warm calls | pass |
| grevlex/wide64/katsura-4 | entry | 1 | warm calls | pass |
| grevlex/wide64/katsura-4 | entry | 16 | warm calls | wall stopped: n = 30 < 31 |
| grevlex/wide64/katsura-4 | f4 | 1 | warm calls | pass |
| grevlex/wide64/katsura-4 | f4 | 16 | warm calls | wall stopped: n = 30 < 31 |
| grevlex/wide64/katsura-9 | entry | 1 | warm calls | wall stopped: n = 20 < 31 |
| grevlex/wide64/katsura-9 | entry | 16 | warm calls | wall stopped: n = 7 < 31 |
| grevlex/wide64/katsura-9 | f4 | 1 | warm calls | pass |
| grevlex/wide64/katsura-9 | f4 | 16 | warm calls | wall stopped: n = 5 < 31 |
| grevlex/wide64/noon-7 | entry | 1 | warm calls | wall stopped: n = 29 < 31 |
| grevlex/wide64/noon-7 | entry | 16 | warm calls | pass |
| grevlex/wide64/noon-7 | f4 | 1 | warm calls | wall stopped: n = 30 < 31 |
| grevlex/wide64/noon-7 | f4 | 16 | warm calls | wall stopped: n = 29 < 31 |
| grevlex/wide64/noon-8 | entry | 1 | process wall | wall stopped: n = 8 < 9 |
| grevlex/wide64/noon-8 | entry | 16 | process wall | wall stopped: n = 7 < 9 |
| grevlex/wide64/noon-8 | f4 | 1 | process wall | pass |
| grevlex/wide64/noon-8 | f4 | 16 | process wall | pass |
