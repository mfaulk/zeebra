<!-- examples/block_density.rs at base 60e99587 plus #804 (adds mq-random-8/grevlex/gf256/default), release profile; exact counts, see docs/research/gpu-f4.md §3.3 -->

Tiles are 64x64; "dense" means at least 50.0% full.

## As built, reducers first: [A B; C D]

| entry | rows x cols | reducer rows | density | max tile | dense tiles / occupied | nz in dense tiles |
|---|---|---:|---:|---:|---:|---:|
| katsura-7/grevlex/m31/default | 350 x 369 | 263 | 7.6% | 17.7% | 0 / 30 | 0.0% |
| katsura-7/grevlex/m31/baseline | 6810 x 6862 | 6788 | 0.2% | 29.7% | 0 / 1063 | 0.0% |
| katsura-6/lex/m31/baseline | 1954 x 945 | 828 | 3.5% | 52.2% | 1 / 242 | 2.5% |
| cyclic-6/grevlex/m31/default | 146 x 175 | 57 | 23.0% | 44.8% | 0 / 9 | 0.0% |
| cyclic-6/lex/m31/default | 1026 x 1048 | 1018 | 2.8% | 40.8% | 0 / 163 | 0.0% |
| katsura-7/grevlex/p64/default | 350 x 369 | 263 | 7.6% | 17.7% | 0 / 30 | 0.0% |
| cyclic-6/grevlex/p64/default | 146 x 175 | 57 | 23.0% | 44.8% | 0 / 9 | 0.0% |
| katsura-6/lex/p64/baseline | 1954 x 945 | 828 | 3.5% | 52.2% | 1 / 242 | 2.5% |
| katsura-6/grevlex/bn254/default | 140 x 152 | 98 | 11.0% | 18.6% | 0 / 9 | 0.0% |
| cyclic-5/grevlex/bn254/baseline | 635 x 379 | 317 | 3.5% | 15.1% | 0 / 42 | 0.0% |
| mq-random-6/grevlex/p31x64/default | 745 x 756 | 659 | 2.7% | 24.9% | 0 / 97 | 0.0% |
| mq-random-6/grevlex/p31x64/baseline | 3305 x 3342 | 3269 | 0.6% | 30.4% | 0 / 601 | 0.0% |
| mq-random-10/grevlex/p31x64/default | 12391 x 12020 | 11086 | 0.5% | 35.2% | 0 / 12997 | 0.0% |
| cyclic-6/grevlex/gf2/default | 124 x 163 | 50 | 11.0% | 17.6% | 0 / 6 | 0.0% |
| cyclic-7/grevlex/gf2/default | 977 x 795 | 372 | 9.2% | 30.1% | 0 / 176 | 0.0% |
| cyclic-6/grevlex/gf256/default | 124 x 163 | 50 | 11.0% | 17.6% | 0 / 6 | 0.0% |
| cyclic-5/lex/gf256/default | 61 x 72 | 55 | 10.0% | 12.7% | 0 / 2 | 0.0% |
| mq-random-8/grevlex/gf256/default | 8114 x 8236 | 7924 | 0.5% | 43.9% | 0 / 4897 | 0.0% |

## Pair-row residual D' = D - C A^-1 B, before and after its own echelon

| entry | D' rows x cols | D' density | D' max tile | D' nz in dense tiles | rank | echelon density | echelon max tile | echelon nz in dense tiles |
|---|---|---:|---:|---:|---:|---:|---:|---:|
| katsura-7/grevlex/m31/default | 87 x 106 | 67.3% | 100.0% | 58.9% | 43 | 69.5% | 100.0% | 57.0% |
| katsura-7/grevlex/m31/baseline | 22 x 74 | 90.0% | 100.0% | 100.0% | 11 | 92.0% | 100.0% | 100.0% |
| katsura-6/lex/m31/baseline | 1126 x 117 | 40.1% | 90.3% | 93.0% | 86 | 40.1% | 81.8% | 90.8% |
| cyclic-6/grevlex/m31/default | 89 x 118 | 52.4% | 83.9% | 72.1% | 55 | 51.6% | 82.9% | 73.5% |
| cyclic-6/lex/m31/default | 8 x 30 | 62.5% | 62.5% | 100.0% | 4 | 62.5% | 62.5% | 100.0% |
| katsura-7/grevlex/p64/default | 87 x 106 | 67.3% | 100.0% | 58.9% | 43 | 69.5% | 100.0% | 57.0% |
| cyclic-6/grevlex/p64/default | 89 x 118 | 52.4% | 83.9% | 72.1% | 55 | 51.6% | 82.9% | 73.5% |
| katsura-6/lex/p64/baseline | 1126 x 117 | 40.1% | 90.3% | 93.0% | 86 | 40.1% | 81.8% | 90.8% |
| katsura-6/grevlex/bn254/default | 42 x 54 | 69.4% | 69.4% | 100.0% | 23 | 71.0% | 71.0% | 100.0% |
| cyclic-5/grevlex/bn254/baseline | 318 x 62 | 43.1% | 49.1% | 0.0% | 48 | 58.3% | 58.3% | 100.0% |
| mq-random-6/grevlex/p31x64/default | 86 x 97 | 69.6% | 100.0% | 100.0% | 39 | 75.3% | 100.0% | 100.0% |
| mq-random-6/grevlex/p31x64/baseline | 36 x 73 | 84.7% | 100.0% | 100.0% | 16 | 84.8% | 100.0% | 100.0% |
| mq-random-10/grevlex/p31x64/default | 1305 x 934 | 44.4% | 100.0% | 85.2% | 579 | 52.3% | 100.0% | 94.6% |
| cyclic-6/grevlex/gf2/default | 74 x 113 | 24.4% | 37.7% | 0.0% | 44 | 24.7% | 37.2% | 0.0% |
| cyclic-7/grevlex/gf2/default | 605 x 423 | 25.1% | 51.6% | 18.3% | 267 | 27.6% | 52.0% | 26.2% |
| cyclic-6/grevlex/gf256/default | 74 x 113 | 24.4% | 37.7% | 0.0% | 44 | 24.7% | 37.2% | 0.0% |
| cyclic-5/lex/gf256/default | 6 x 17 | 47.1% | 47.1% | 0.0% | 3 | 47.1% | 47.1% | 0.0% |
| mq-random-8/grevlex/gf256/default | 190 x 312 | 78.5% | 99.7% | 97.7% | 74 | 81.9% | 99.8% | 94.8% |

## Where the multiply-adds are: sparse C A^-1 B sweep against a dense echelon of D'

| entry | sweep multiply-adds (exact) | dense D' echelon multiply-adds | dense share | D' cells |
|---|---:|---:|---:|---:|
| katsura-7/grevlex/m31/default | 239946 | 241402 | 50.2% | 9222 |
| katsura-7/grevlex/m31/baseline | 1704029 | 12078 | 0.7% | 1628 |
| katsura-6/lex/m31/baseline | 3690919 | 6895480 | 65.1% | 131742 |
| cyclic-6/grevlex/m31/default | 54795 | 315810 | 85.2% | 10502 |
| cyclic-6/lex/m31/default | 62481 | 610 | 1.0% | 240 |
| katsura-7/grevlex/p64/default | 239946 | 241402 | 50.2% | 9222 |
| cyclic-6/grevlex/p64/default | 54795 | 315810 | 85.2% | 10502 |
| katsura-6/lex/p64/baseline | 3690919 | 6895480 | 65.1% | 131742 |
| katsura-6/grevlex/bn254/default | 26578 | 29992 | 53.0% | 2268 |
| cyclic-5/grevlex/bn254/baseline | 138612 | 537512 | 79.5% | 19716 |
| mq-random-6/grevlex/p31x64/default | 502379 | 203138 | 28.8% | 8342 |
| mq-random-6/grevlex/p31x64/baseline | 1354377 | 28720 | 2.1% | 2628 |
| mq-random-10/grevlex/p31x64/default | 239473690 | 394644470 | 62.2% | 1218870 |
| cyclic-6/grevlex/gf2/default | 7222 | 212168 | 96.7% | 8362 |
| cyclic-7/grevlex/gf2/default | 680927 | 37929931 | 98.2% | 255915 |
| cyclic-6/grevlex/gf256/default | 7222 | 212168 | 96.7% | 8362 |
| cyclic-5/lex/gf256/default | 488 | 182 | 27.2% | 102 |
| mq-random-8/grevlex/gf256/default | 25413498 | 3131495 | 11.0% | 59280 |
