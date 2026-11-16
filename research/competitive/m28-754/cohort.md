| problem | task | p | previous serial ms | serial ms | 16w ms | 16w speedup | serial MiB | 16w MiB | fastest comparand ms (engine, workers) |
|---|---|---|---:|---:|---:|---:|---:|---:|---|
| mq-planted-wide-10 | RGB | 2^64-353 | 0.1 | 0.1 | 0.2 | 0.78x | 6.5 | 6.6 | 0.9 (groebner.jl, 1) |
| mq-planted-wide-14 | RGB | 2^64-353 | 0.2 | 0.2 | 0.2 | 0.90x | 26.6 | 26.6 | 0.9 (groebner.jl, 1) |
| mq-planted-wide-6 | RGB | 2^64-353 | 0.1 | 0.1 | 0.1 | 0.87x | 5.9 | 6.0 | 0.8 (groebner.jl, 1) |
| cyclic-4 | lex | M31 | unsupported | unsupported | unsupported | — | 6.1 | 5.9 | — |
| cyclic-4 | RGB | M31 | 0.1 | 0.1 | 0.1 | 0.90x | 5.9 | 5.8 | 0.8 (groebner.jl, 1) |
| cyclic-5 | lex | M31 | 1.3 | 1.1 | 1.3 | 0.86x | 7.0 | 7.1 | 36.0 (singular, 1) |
| cyclic-5 | RGB | M31 | 0.8 | 0.7 | 0.8 | 0.80x | 6.7 | 6.7 | 1.0 (groebner.jl, 1) |
| cyclic-6 | lex | M31 | 9.3 | 6.4 | 6.7 | 0.97x | 8.7 | 8.6 | 51.3 (singular, 1) |
| cyclic-6 | RGB | M31 | 5.6 | 3.9 | 3.9 | 0.98x | 7.5 | 7.6 | 2.1 (groebner.jl, 1) |
| cyclic-7 | lex | M31 | 823.1 | 398.9 | 307.4 | 1.30x | 32.7 | 35.3 | 2212.8 (singular, 1) |
| cyclic-7 | RGB | M31 | 660.2 | 235.9 | 130.6 | 1.81x | 21.8 | 23.7 | 47.2 (groebner.jl, 1) |
| cyclic-8 | lex | M31 | unsupported | unsupported | unsupported | — | 146.3 | 170.1 | — |
| cyclic-8 | RGB | M31 | 27658.5 | 5121.8 | 1695.9 | 3.02x | 146.2 | 170.4 | 699.5 (groebner.jl, 1) |
| cyclic-9 | lex | M31 | stopped-by-limit | stopped-by-limit | stopped-by-limit | — | 1151.3 | 1263.0 | — |
| cyclic-9 | RGB | M31 | stopped-by-limit | stopped-by-limit | stopped-by-limit | — | 1150.1 | 1261.8 | 61534.5 (groebner.jl, 1) |
| katsura-10 | lex | M31 | 4148.3 | 1250.4 | 589.5 | 2.12x | 53.9 | 60.4 | 11106.4 (singular, 1) |
| katsura-10 | RGB | M31 | 3739.0 | 943.2 | 278.4 | 3.39x | 33.0 | 41.0 | 89.5 (groebner.jl, 1) |
| katsura-11 | lex | M31 | 40819.0 | 10724.5 | 4043.0 | 2.65x | 213.3 | 241.7 | 92033.0 (singular, 1) |
| katsura-11 | RGB | M31 | 35359.5 | 8444.0 | 1614.7 | 5.23x | 117.6 | 150.2 | 517.8 (groebner.jl, 1) |
| katsura-4 | lex | M31 | 0.2 | 0.2 | 0.2 | 0.83x | 6.5 | 6.5 | 35.9 (singular, 1) |
| katsura-4 | RGB | M31 | 0.2 | 0.1 | 0.2 | 0.81x | 6.2 | 6.0 | 0.8 (groebner.jl, 1) |
| katsura-5 | lex | M31 | 0.6 | 0.4 | 0.5 | 0.79x | 6.7 | 6.8 | 36.0 (singular, 1) |
| katsura-5 | RGB | M31 | 0.4 | 0.3 | 0.4 | 0.77x | 6.1 | 6.1 | 0.8 (groebner.jl, 1) |
| katsura-6 | lex | M31 | 1.9 | 1.3 | 1.5 | 0.88x | 7.5 | 7.9 | 36.0 (singular, 1) |
| katsura-6 | RGB | M31 | 1.4 | 0.9 | 1.1 | 0.81x | 7.3 | 7.2 | 1.1 (groebner.jl, 1) |
| katsura-7 | lex | M31 | 8.9 | 5.5 | 5.7 | 0.96x | 8.4 | 8.1 | 51.4 (singular, 1) |
| katsura-7 | RGB | M31 | 7.4 | 3.9 | 4.0 | 0.97x | 7.5 | 7.8 | 1.7 (groebner.jl, 1) |
| katsura-8 | lex | M31 | 63.9 | 25.1 | 21.0 | 1.20x | 10.4 | 11.0 | 189.2 (singular, 1) |
| katsura-8 | RGB | M31 | 54.0 | 19.9 | 13.6 | 1.47x | 9.1 | 10.1 | 4.8 (groebner.jl, 1) |
| katsura-9 | lex | M31 | 507.5 | 173.3 | 106.3 | 1.63x | 19.2 | 21.3 | 1286.4 (singular, 1) |
| katsura-9 | RGB | M31 | 445.8 | 130.6 | 59.4 | 2.20x | 13.8 | 16.5 | 45.4 (groebner.jl, 1) |
| mq-planted-10 | lex | M31 | 40.0 | 30.4 | 32.6 | 0.93x | 23.6 | 23.4 | 148.2 (singular, 1) |
| mq-planted-10 | RGB | M31 | 0.1 | 0.1 | 0.1 | 0.89x | 6.7 | 6.7 | 0.7 (groebner.jl, 1) |
| mq-planted-14 | lex | M31 | stopped-by-limit | stopped-by-limit | stopped-by-limit | — | 11.1 | 10.1 | 44270.5 (singular, 1) |
| mq-planted-14 | RGB | M31 | 0.1 | 0.2 | 0.2 | 0.81x | 27.8 | 28.4 | 0.7 (groebner.jl, 1) |
| mq-planted-6 | lex | M31 | 0.4 | 0.4 | 0.6 | 0.76x | 6.6 | 6.6 | 36.0 (singular, 1) |
| mq-planted-6 | RGB | M31 | 0.1 | 0.1 | 0.1 | 0.72x | 5.9 | 6.2 | 0.8 (groebner.jl, 1) |
| mq-random-10 | lex | M31 | 4737.0 | 1247.8 | 540.5 | 2.31x | 52.6 | 58.3 | 8234.9 (singular, 1) |
| mq-random-10 | RGB | M31 | 4379.7 | 987.0 | 279.3 | 3.53x | 37.6 | 45.2 | 81.0 (groebner.jl, 1) |
| mq-random-14 | lex | M31 | stopped-by-limit | stopped-by-limit | stopped-by-limit | — | 737.5 | 832.8 | — |
| mq-random-14 | RGB | M31 | stopped-by-limit | stopped-by-limit | stopped-by-limit | — | 737.6 | 833.1 | — |
| mq-random-6 | lex | M31 | 14.1 | 6.4 | 6.6 | 0.97x | 8.2 | 8.2 | 56.4 (singular, 1) |
| mq-random-6 | RGB | M31 | 13.7 | 4.5 | 5.2 | 0.87x | 7.4 | 7.7 | 2.4 (groebner.jl, 1) |
| cyclic-4 | lex | 32003 | unsupported | unsupported | unsupported | — | 5.6 | 5.9 | — |
| cyclic-4 | RGB | 32003 | 0.1 | 0.1 | 0.1 | 0.75x | 5.6 | 5.7 | 0.9 (groebner.jl, 1) |
| cyclic-5 | lex | 32003 | 1.3 | 1.1 | 1.2 | 0.94x | 7.3 | 7.2 | 36.0 (singular, 1) |
| cyclic-5 | RGB | 32003 | 0.8 | 0.7 | 0.8 | 0.82x | 6.5 | 6.8 | 1.0 (groebner.jl, 1) |
| cyclic-6 | lex | 32003 | 7.6 | 6.7 | 6.7 | 1.00x | 8.4 | 8.4 | 51.3 (singular, 1) |
| cyclic-6 | RGB | 32003 | 5.2 | 4.0 | 4.2 | 0.97x | 7.7 | 7.9 | 2.1 (groebner.jl, 1) |
| cyclic-7 | lex | 32003 | — | 438.5 | 332.2 | 1.32x | 25.3 | 27.5 | — |
| cyclic-7 | RGB | 32003 | — | 265.4 | 136.7 | 1.94x | 19.3 | 21.8 | — |
| cyclic-8 | lex | 32003 | — | unsupported | unsupported | — | 138.4 | 160.2 | — |
| cyclic-8 | RGB | 32003 | — | 6143.8 | 1909.8 | 3.22x | 138.5 | 160.0 | — |
| cyclic-9 | lex | 32003 | — | stopped-by-limit | stopped-by-limit | — | 865.7 | 1170.0 | — |
| cyclic-9 | RGB | 32003 | — | stopped-by-limit | stopped-by-limit | — | 866.2 | 1185.9 | — |
| katsura-10 | lex | 32003 | — | 1428.1 | 631.1 | 2.26x | 48.2 | 54.5 | — |
| katsura-10 | RGB | 32003 | — | 1146.3 | 307.0 | 3.73x | 32.1 | 39.8 | — |
| katsura-11 | lex | 32003 | — | 12671.0 | 4409.7 | 2.87x | 188.2 | 215.1 | — |
| katsura-11 | RGB | 32003 | — | 10091.3 | 1865.2 | 5.41x | 110.5 | 136.7 | — |
| katsura-4 | lex | 32003 | 0.2 | 0.2 | 0.2 | 0.79x | 6.9 | 6.3 | 41.1 (singular, 1) |
| katsura-4 | RGB | 32003 | 0.2 | 0.1 | 0.2 | 0.78x | 6.1 | 6.0 | 0.9 (groebner.jl, 1) |
| katsura-5 | lex | 32003 | 0.5 | 0.4 | 0.5 | 0.80x | 6.8 | 6.8 | 36.1 (singular, 1) |
| katsura-5 | RGB | 32003 | 0.4 | 0.3 | 0.4 | 0.77x | 5.9 | 6.0 | 1.0 (groebner.jl, 1) |
| katsura-6 | lex | 32003 | 1.6 | 1.2 | 1.4 | 0.87x | 14.2 | 7.7 | 36.0 (singular, 1) |
| katsura-6 | RGB | 32003 | 1.4 | 0.9 | 1.1 | 0.83x | 7.6 | 7.4 | 1.1 (groebner.jl, 1) |
| katsura-7 | lex | 32003 | 8.0 | 5.6 | 5.8 | 0.97x | 8.0 | 8.2 | 51.3 (singular, 1) |
| katsura-7 | RGB | 32003 | 6.6 | 4.1 | 4.2 | 0.98x | 8.0 | 7.6 | 1.8 (groebner.jl, 1) |
| katsura-8 | lex | 32003 | — | 29.6 | 20.6 | 1.44x | 9.8 | 10.9 | — |
| katsura-8 | RGB | 32003 | — | 23.1 | 14.7 | 1.58x | 9.1 | 9.8 | — |
| katsura-9 | lex | 32003 | — | 194.7 | 109.7 | 1.77x | 17.3 | 19.4 | — |
| katsura-9 | RGB | 32003 | — | 166.6 | 61.6 | 2.71x | 13.5 | 15.7 | — |
| mq-planted-10 | lex | 32003 | 25.0 | 27.4 | 29.6 | 0.92x | 15.6 | 15.3 | 158.5 (singular, 1) |
| mq-planted-10 | RGB | 32003 | 0.1 | 0.1 | 0.2 | 0.86x | 6.9 | 6.4 | 0.9 (groebner.jl, 1) |
| mq-planted-14 | lex | 32003 | stopped-by-limit | stopped-by-limit | stopped-by-limit | — | 11.1 | 11.2 | 49866.1 (singular, 1) |
| mq-planted-14 | RGB | 32003 | 0.2 | 0.2 | 0.2 | 0.81x | 28.3 | 27.1 | 0.9 (groebner.jl, 1) |
| mq-planted-6 | lex | 32003 | 0.4 | 0.4 | 0.5 | 0.79x | 6.8 | 6.7 | 36.0 (singular, 1) |
| mq-planted-6 | RGB | 32003 | 0.1 | 0.1 | 0.1 | 0.77x | 6.3 | 6.1 | 0.9 (groebner.jl, 1) |
| mq-random-10 | lex | 32003 | 4360.7 | 1450.1 | 582.1 | 2.49x | 50.7 | 62.4 | 8010.1 (singular, 1) |
| mq-random-10 | RGB | 32003 | 4326.3 | 1205.5 | 299.6 | 4.02x | 36.9 | 43.7 | 84.8 (groebner.jl, 1) |
| mq-random-14 | lex | 32003 | stopped-by-limit | stopped-by-limit | stopped-by-limit | — | 723.2 | 820.9 | — |
| mq-random-14 | RGB | 32003 | stopped-by-limit | stopped-by-limit | stopped-by-limit | — | 723.1 | 822.6 | — |
| mq-random-6 | lex | 32003 | 14.8 | 6.8 | 7.0 | 0.97x | 8.1 | 8.2 | 56.5 (singular, 1) |
| mq-random-6 | RGB | 32003 | 12.3 | 5.3 | 5.5 | 0.96x | 7.8 | 7.6 | 2.6 (groebner.jl, 1) |
