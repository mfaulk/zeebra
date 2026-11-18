 15:55:37 up 3 days, 23 min,  1 user,  load average: 2.46, 2.64, 2.86
## Q1: polynomial systems

Clauses / variables after Tseitin ANDs and cutting each XOR at the given length.

| instance | equations | ANF terms | longest XOR | uncut clauses for it | cut 3 | cut 4 | cut 5 | cut 6 |
|---|---|---|---|---|---|---|---|---|
| MQ n=20 m=20 | 20 | 2094 | 115 | 2^114 | 8786 / 2244 | 8786 / 1223 | 11498 / 881 | 16878 / 712 |
| n=24: 18 quadratics + 6 affine | 24 | 2807 | 166 | 2^165 | 11864 / 3035 | 11864 / 1661 | 15512 / 1205 | 22780 / 975 |
| same, affine-eliminated (n=18) | 18 | 1496 | 98 | 2^97 | 6299 / 1613 | 6299 / 886 | 8227 / 645 | 12071 / 523 |

## Q1: Macaulay rows of a real GF(2) F4 run

| instance | matrices | rows | nonzeros | longest row | uncut clauses for it | cut-4 clauses | cut-4 clauses per nonzero |
|---|---|---|---|---|---|---|---|
| MQ n=8 m=8 | 5 | 588 | 4431 | 21 | 2^20 | 13731 | 3.1 |
| MQ n=10 m=10 | 5 | 1647 | 29949 | 42 | 2^41 | 108370 | 3.6 |
| MQ n=12 m=12 | 6 | 2964 | 88636 | 92 | 2^91 | 334827 | 3.8 |
| MQ n=14 m=14 | 6 | 9421 | 464645 | 155 | 2^154 | 1788279 | 3.8 |
