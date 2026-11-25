Cell cost in ms: median over clean repetitions of process wall, a repetition that is not a verified completion counted at 2C. **pen** = the cell median is the 2C penalty, not a time.

| family | record | P1 | P3 | P4 | P6 | P7-w1 | P8-w1 | P8-w16 | cheapest | P8-w1 ÷ cheapest | P4 ÷ cheapest |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `cyclic` | `zb-cyclic-7@p31` | 239 | 140 | 462 | 568 | 476 | 239 | 142 | P3 | 1.70 | 3.30 |
| `cyclic` | `zb-cyclic-7@p64` | 285 | 152 | 475 | 574 | 516 | 285 | 152 | P3 | 1.87 | 3.12 |
| `eco` | `zb-eco-12@p31` | 10,375 | 2,094 | 1,931 | 1,250 | 34,871 | 1,921 | 1,264 | P5 | 1.57 | 1.58 |
| `eco` | `zb-eco-12@p64` | 13,007 | 2,507 | 2,170 | 1,340 | 37,689 | 2,148 | 1,338 | P5 | 1.61 | 1.62 |
| `katsura` | `zb-katsura-12@p31` | 65,509 | 7,655 | 4,135 | 2,005 | 137,206 | 4,154 | 2,012 | P6 | 2.07 | 2.06 |
| `katsura` | `zb-katsura-12@p64` | 81,884 | 9,098 | 4,661 | 2,131 | 149,536 | 4,625 | 2,147 | P6 | 2.17 | 2.19 |
| `reimer` | `zb-reimer-6@p31` | 134 | 84 | 1,061 | 1,063 | 197 | 133 | 83 | P2 | 1.66 | 13.29 |
| `reimer` | `zb-reimer-6@p64` | 156 | 90 | 1,151 | 1,069 | 210 | 156 | 90 | P8-w16 | 1.74 | 12.78 |
| `sd/ellipsoid` | `sd-ellipsoid-m2@p31` | **pen** | **pen** | 1,112 | 1,167 | **pen** | **pen** | **pen** | P4 | pen | 1.00 |
| `sd/ellipsoid` | `sd-ellipsoid-m2@p64` | **pen** | **pen** | 1,116 | 1,198 | **pen** | **pen** | **pen** | P4 | pen | 1.00 |
| `sd/four-body` | `sd-fourbodyproblem@p31` | 26 | 23 | 48 | 59 | 32 | 26 | 23 | P3 | 1.11 | 2.06 |
| `sd/four-body` | `sd-fourbodyproblem@p64` | 28 | 25 | 50 | 58 | 33 | 28 | 25 | P3 | 1.12 | 2.00 |
| `sd/runge-kutta-order-conditions` | `sd-butcher@p31` | 12 | 12 | 139 | 163 | 13 | 12 | 12 | P1 | 1.01 | 12.06 |
| `sd/runge-kutta-order-conditions` | `sd-butcher@p64` | 12 | 13 | 137 | 158 | 13 | 12 | 12 | P1 | 1.00 | 11.53 |
| `sd/runge-kutta-order-conditions` | `sd-hairer-2@p31` | 49 | 49 | 17,462 | 17,792 | 88 | 49 | 48 | P2 | 1.13 | 399.57 |
| `sd/runge-kutta-order-conditions` | `sd-hairer-2@p64` | 52 | 51 | 17,713 | 17,918 | 90 | 52 | 50 | P2 | 1.15 | 390.33 |
| `zb/graph-3colouring` | `zb-col-ktree2-12-s1@p31` | 9 | 10 | 14 | 20 | 9 | 13 | 20 | P7-w1 | 1.57 | 1.58 |
| `zb/graph-3colouring` | `zb-col-ktree2-12-s1@p64` | 9 | 10 | 14 | 20 | 9 | 13 | 20 | P7-w1 | 1.59 | 1.60 |

18 of 122 development records have P8-w1 or P4 penalized or at least 1.5x the cheapest arm. Penalized on every arm (frontier): `gen-chandrasekhar-h-13@p31`, `gen-chandrasekhar-h-13@p64`.
