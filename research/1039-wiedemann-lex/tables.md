| Row | D | grobx route | grobx ms | adaptive ÷ grobx [95%] | best Zeebra arm | Zeebra ms | best ÷ grobx [95%] | adaptive route | regret [95%] | digests |
|---|---|---|---|---|---|---|---|---|---|---|
| wd-4-10 | 10000 | FGLM | 2,431.9 | 0.24 [0.24, 0.25] n=10/12 | zb-direct-lex | 22.4 | 0.01 [0.01, 0.01] n=12/12 | Wiedemann | 1.00 [0.99, 1.01] paired | 1 (zb-adaptive: complete) |
| wdsq-4-10 | 20000 | FGLM | 22,637.7 | 0.10 [0.10, 0.10] n=10/10 | zb-wiedemann | 2,260.6 | 0.10 [0.10, 0.10] n=11/10 | Wiedemann | 1.00 [0.99, 1.00] paired | 1 (grobx155: ok; zb-adaptive: complete; zb-wiedemann: complete; zb-direct-lex: complete) |
| wd-3-30 | 27000 | FGLM | 7,415.2 | 0.39 [0.38, 0.39] n=9/12 | zb-direct-lex | 23.4 | 0.00 [0.00, 0.00] n=12/12 | Wiedemann | 1.00 [0.99, 1.00] paired | 1 (zb-adaptive: complete; zb-wiedemann: complete) |
| wd-4-12-p31 | 20736 | FGLM | 14,562.7 | 0.13 [0.13, 0.13] n=12/12 | zb-direct-lex | 54.2 | 0.00 [0.00, 0.00] n=9/12 | Wiedemann | 1.00 [0.99, 1.02] paired | 1 (zb-wiedemann: complete; zb-direct-lex: complete) |
| wdsq-5-6 | 15552 | FGLM | 24,598.8 | 0.07 [0.07, 0.07] n=10/12 | zb-wiedemann | 1,732.7 | 0.07 [0.07, 0.07] n=11/12 | Wiedemann | 1.00 [0.99, 1.01] paired | 1 (zb-direct-lex: complete; zb-adaptive: complete; zb-wiedemann: complete) |
| wd-4-6 | 1296 | FGLM | 36.1 | 0.72 [0.71, 0.73] n=12/10 | zb-direct-lex | 7.5 | 0.21 [0.20, 0.21] n=12/10 | Wiedemann | 1.00 [0.99, 1.01] paired | 1 (grobx155: ok) |
| cyclic-7 | 924 | FGLM | 93.9 | 4.58 [4.55, 4.61] n=12/8 | zb-classical | 316.8 | 3.37 [3.34, 3.41] n=3/8 | Classical/NonCyclicProjection | 1.36 [1.34, 1.37] | 1 (grobx155: ok; zb-direct-lex: stopped; zb-wiedemann: complete) |
| katsura-11 | 1024 | FGLM | 1,212.8 | 2.77 [2.74, 2.81] n=11/11 | zb-adaptive | 3,356.7 | 2.77 [2.74, 2.81] n=11/11 | Classical/DenseOperator | 0.97 [0.97, 1.00] | 1 (zb-direct-lex: stopped; grobx155: ok; zb-adaptive: complete; zb-wiedemann: complete) |
| pquad-10-1 | 1024 | FGLM | 882.6 | 2.36 [2.33, 2.40] n=10/12 | zb-classical | 1,862.7 | 2.11 [2.09, 2.14] n=3/12 | Wiedemann | 1.12 [1.10, 1.14] | 1 (zb-direct-lex: stopped; zb-adaptive: complete) |
| wd-6-6 | 46656 | FGLM | 417,314.8 | 0.03 [0.03, 0.03] n=3/3 | zb-direct-lex | 960.6 | 0.00 [0.00, 0.00] n=3/3 | Wiedemann | 1.02 [0.99, 1.04] paired | 1 (zb-classical: refused) |
| wd-5-10 | 100000 | F4-lex | 648.1 | 60.40 [59.49, 61.30] n=3/4 | zb-wiedemann | 38,917.9 | 60.05 [59.57, 60.95] n=3/4 | Wiedemann | 1.01 [0.99, 1.01] paired | 1 (zb-direct-lex: stopped; zb-classical: refused) |
| wdns-4-10 | 20000 | FGLM | 5,210.1 | 28.43 [27.63, 28.68] n=3/3 | zb-direct-lex | 24.8 | 0.00 [0.00, 0.00] n=3/3 | Classical/NonCyclicProjection | 1.03 [1.02, 1.03] paired | 1 (grobx155: ok) |
| wdnr-4-10 | 20000 | FGLM | 5,232.2 | 28.13 [27.96, 28.99] n=3/3 | zb-direct-lex | 24.7 | 0.00 [0.00, 0.00] n=3/3 | Classical/NonCyclicProjection | 1.02 [1.02, 1.04] paired | 1 |

| Row | Arm | median ms | stages (ms, medians) | peak RSS MiB |
|---|---|---|---|---|
| wd-4-10 | grobx155 | 2,431.9 | grevlex 0.1; FGLM 2,410.5; lex F4 0.0 | 128 |
| wd-4-10 | zb-adaptive | 595.4 | F4 0.1; operators 4.9; sequence 218.4; reconstruction 295.4; certificate 65.9; classical walk 0.1; attempts 1 | 21 |
| wd-4-10 | zb-classical | 34,438.2 | F4 0.1; operators 4.5; sequence 0.0; reconstruction 0.0; certificate 0.0; classical walk 34,265.4; attempts 0 | 1,537 |
| wd-4-10 | zb-direct-lex | 22.4 | F4 15.8 | 21 |
| wd-4-10 | zb-wiedemann | 594.9 | F4 0.1; operators 4.5; sequence 215.2; reconstruction 297.3; certificate 66.1; classical walk 0.1; attempts 1 | 21 |
| wdsq-4-10 | grobx155 | 22,637.7 | grevlex 0.1; FGLM 22,891.4; lex F4 0.0 | 746 |
| wdsq-4-10 | zb-adaptive | 2,267.7 | F4 0.1; operators 9.5; sequence 898.3; reconstruction 912.5; certificate 430.5; classical walk 0.3; attempts 1 | 21 |
| wdsq-4-10 | zb-classical | 339,765.1 | F4 0.1; operators 9.9; sequence 0.0; reconstruction 0.0; certificate 0.0; classical walk 339,089.0; attempts 0 | 6,121 |
| wdsq-4-10 | zb-direct-lex | 3,553.1 | F4 3,545.0 | 94 |
| wdsq-4-10 | zb-wiedemann | 2,260.6 | F4 0.1; operators 9.8; sequence 896.2; reconstruction 913.8; certificate 432.9; classical walk 0.3; attempts 1 | 21 |
| wd-3-30 | grobx155 | 7,415.2 | grevlex 0.1; FGLM 7,505.7; lex F4 0.0 | 309 |
| wd-3-30 | zb-adaptive | 2,885.5 | F4 0.1; operators 4.9; sequence 1,203.6; reconstruction 1,248.9; certificate 417.0; classical walk 0.4; attempts 1 | 21 |
| wd-3-30 | zb-classical | 221,067.7 | F4 0.1; operators 4.9; sequence 0.0; reconstruction 0.0; certificate 0.0; classical walk 219,938.0; attempts 0 | 11,141 |
| wd-3-30 | zb-direct-lex | 23.4 | F4 16.7 | 21 |
| wd-3-30 | zb-wiedemann | 2,904.8 | F4 0.1; operators 4.9; sequence 1,218.8; reconstruction 1,251.1; certificate 419.9; classical walk 0.4; attempts 1 | 21 |
| wd-4-12-p31 | grobx155 | 14,562.7 | grevlex 0.1; FGLM 14,611.0; lex F4 0.0 | 439 |
| wd-4-12-p31 | zb-adaptive | 1,912.3 | F4 0.1; operators 9.2; sequence 811.5; reconstruction 897.3; certificate 176.8; classical walk 0.1; attempts 1 | 21 |
| wd-4-12-p31 | zb-classical | 187,298.0 | F4 0.1; operators 8.3; sequence 0.0; reconstruction 0.0; certificate 0.0; classical walk 186,543.7; attempts 0 | 6,577 |
| wd-4-12-p31 | zb-direct-lex | 54.2 | F4 47.3 | 35 |
| wd-4-12-p31 | zb-wiedemann | 1,900.0 | F4 0.1; operators 9.1; sequence 805.1; reconstruction 898.8; certificate 172.9; classical walk 0.1; attempts 1 | 21 |
| wdsq-5-6 | grobx155 | 24,598.8 | grevlex 0.1; FGLM 24,458.9; lex F4 0.0 | 752 |
| wdsq-5-6 | zb-adaptive | 1,734.2 | F4 0.1; operators 16.2; sequence 677.0; reconstruction 633.6; certificate 389.5; classical walk 0.4; attempts 1 | 21 |
| wdsq-5-6 | zb-classical | 268,532.7 | F4 0.1; operators 16.1; sequence 0.0; reconstruction 0.0; certificate 0.0; classical walk 268,103.1; attempts 0 | 3,709 |
| wdsq-5-6 | zb-direct-lex | 8,102.4 | F4 8,093.0 | 159 |
| wdsq-5-6 | zb-wiedemann | 1,732.7 | F4 0.1; operators 16.2; sequence 672.6; reconstruction 642.4; certificate 386.1; classical walk 0.4; attempts 1 | 21 |
| wd-4-6 | grobx155 | 36.1 | grevlex 0.1; FGLM 28.8; lex F4 0.0 | 21 |
| wd-4-6 | zb-adaptive | 26.0 | F4 0.1; operators 0.9; sequence 4.7; reconstruction 11.9; certificate 1.6; classical walk 0.0; attempts 1 | 21 |
| wd-4-6 | zb-classical | 152.3 | F4 0.1; operators 0.9; sequence 0.0; reconstruction 0.0; certificate 0.0; classical walk 142.1; attempts 0 | 32 |
| wd-4-6 | zb-direct-lex | 7.5 | F4 1.1 | 21 |
| wd-4-6 | zb-wiedemann | 26.0 | F4 0.1; operators 0.9; sequence 4.7; reconstruction 11.9; certificate 1.6; classical walk 0.0; attempts 1 | 21 |
| cyclic-7 | grobx155 | 93.9 | grevlex 54.5; FGLM 31.4; lex F4 0.0 | 21 |
| cyclic-7 | zb-adaptive | 430.1 | F4 231.1; operators 21.3; sequence 118.2; reconstruction 1.4; certificate 0.0; classical walk 46.6; attempts 3 | 35 |
| cyclic-7 | zb-classical | 316.8 | F4 234.9; operators 22.4; sequence 0.0; reconstruction 0.0; certificate 0.0; classical walk 48.8; attempts 0 | 32 |
| cyclic-7 | zb-wiedemann | 428.9 | F4 231.0; operators 21.2; sequence 117.7; reconstruction 1.4; certificate 0.0; classical walk 46.2; attempts 3 | 35 |
| katsura-11 | grobx155 | 1,212.8 | grevlex 238.3; FGLM 960.2; lex F4 0.0 | 66 |
| katsura-11 | zb-adaptive | 3,356.7 | F4 505.1; operators 2,195.4; sequence 0.0; reconstruction 0.0; certificate 0.0; classical walk 598.3; attempts 0 | 207 |
| katsura-11 | zb-classical | 3,444.0 | F4 514.1; operators 2,260.3; sequence 0.0; reconstruction 0.0; certificate 0.0; classical walk 616.8; attempts 0 | 204 |
| katsura-11 | zb-wiedemann | 3,766.7 | F4 504.6; operators 2,212.3; sequence 738.7; reconstruction 12.6; certificate 234.5; classical walk 0.2; attempts 1 | 207 |
| pquad-10-1 | grobx155 | 882.6 | grevlex 164.1; FGLM 709.3; lex F4 0.0 | 51 |
| pquad-10-1 | zb-adaptive | 2,079.8 | F4 566.1; operators 679.2; sequence 599.4; reconstruction 11.5; certificate 180.7; classical walk 0.2; attempts 1 | 149 |
| pquad-10-1 | zb-classical | 1,862.7 | F4 568.4; operators 695.5; sequence 0.0; reconstruction 0.0; certificate 0.0; classical walk 557.6; attempts 0 | 146 |
| pquad-10-1 | zb-wiedemann | 2,079.8 | F4 557.1; operators 682.8; sequence 598.8; reconstruction 11.4; certificate 182.7; classical walk 0.2; attempts 1 | 150 |
| wd-6-6 | grobx155 | 417,314.8 | grevlex 0.2; FGLM 415,563.8; lex F4 0.0 | 3,405 |
| wd-6-6 | zb-adaptive | 11,069.2 | F4 0.1; operators 60.7; sequence 5,107.9; reconstruction 4,145.3; certificate 1,695.5; classical walk 0.7; attempts 1 | 32 |
| wd-6-6 | zb-direct-lex | 960.6 | F4 953.2 | 493 |
| wd-6-6 | zb-wiedemann | 10,899.0 | F4 0.1; operators 60.5; sequence 5,203.1; reconstruction 3,945.7; certificate 1,656.6; classical walk 0.8; attempts 1 | 31 |
| wd-5-10 | grobx155 | 648.1 | grevlex 0.2; FGLM 33.2; lex F4 606.1 | 101 |
| wd-5-10 | zb-adaptive | 39,146.4 | F4 0.1; operators 76.2; sequence 20,095.7; reconstruction 12,226.7; certificate 6,690.2; classical walk 1.5; attempts 1 | 53 |
| wd-5-10 | zb-wiedemann | 38,917.9 | F4 0.1; operators 75.7; sequence 19,785.0; reconstruction 12,151.4; certificate 6,681.9; classical walk 1.4; attempts 1 | 53 |
| wdns-4-10 | grobx155 | 5,210.1 | grevlex 0.1; FGLM 5,185.0; lex F4 0.0 | 253 |
| wdns-4-10 | zb-adaptive | 148,105.5 | F4 0.1; operators 20.1; sequence 2,442.0; reconstruction 408.6; certificate 0.0; classical walk 144,575.2; attempts 3 | 6,121 |
| wdns-4-10 | zb-classical | 145,000.5 | F4 0.1; operators 20.1; sequence 0.0; reconstruction 0.0; certificate 0.0; classical walk 144,321.7; attempts 0 | 6,122 |
| wdns-4-10 | zb-direct-lex | 24.8 | F4 18.2 | 21 |
| wdns-4-10 | zb-wiedemann | 147,268.5 | F4 0.1; operators 20.2; sequence 2,401.5; reconstruction 403.8; certificate 0.0; classical walk 143,751.4; attempts 3 | 6,121 |
| wdnr-4-10 | grobx155 | 5,232.2 | grevlex 0.1; FGLM 5,212.9; lex F4 0.0 | 252 |
| wdnr-4-10 | zb-adaptive | 147,195.5 | F4 0.1; operators 17.0; sequence 2,399.1; reconstruction 401.4; certificate 0.0; classical walk 143,734.8; attempts 3 | 6,122 |
| wdnr-4-10 | zb-classical | 144,452.6 | F4 0.1; operators 17.1; sequence 0.0; reconstruction 0.0; certificate 0.0; classical walk 143,776.3; attempts 0 | 6,122 |
| wdnr-4-10 | zb-direct-lex | 24.7 | F4 18.2 | 21 |
| wdnr-4-10 | zb-wiedemann | 147,357.8 | F4 0.1; operators 17.0; sequence 2,412.7; reconstruction 406.2; certificate 0.0; classical walk 143,875.7; attempts 3 | 6,122 |
