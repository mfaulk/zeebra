<!-- examples/block_density.rs (#225) at base 8dbf9bcf, release profile; exact counts, see docs/research/gpu-f4.md -->

Tiles are 64x64; "dense" means at least 50.0% full.

## As built, reducers first: [A B; C D]

| entry | rows x cols | reducer rows | density | max tile | dense tiles / occupied | nz in dense tiles |
|---|---|---:|---:|---:|---:|---:|
| katsura-7/grevlex/m31/default | 361 x 369 | 263 | 7.9% | 17.7% | 0 / 30 | 0.0% |
| katsura-7/grevlex/m31/baseline | 6810 x 6862 | 6788 | 0.2% | 29.7% | 0 / 1063 | 0.0% |
| katsura-6/lex/m31/baseline | 1954 x 945 | 828 | 3.5% | 52.2% | 1 / 242 | 2.5% |
| cyclic-6/grevlex/m31/default | 159 x 175 | 57 | 23.5% | 46.7% | 0 / 9 | 0.0% |
| cyclic-6/lex/m31/default | 1026 x 1048 | 1018 | 2.8% | 40.8% | 0 / 163 | 0.0% |
| katsura-7/grevlex/p64/default | 361 x 369 | 263 | 7.9% | 17.7% | 0 / 30 | 0.0% |
| cyclic-6/grevlex/p64/default | 159 x 175 | 57 | 23.5% | 46.7% | 0 / 9 | 0.0% |
| katsura-6/lex/p64/baseline | 1954 x 945 | 828 | 3.5% | 52.2% | 1 / 242 | 2.5% |
| katsura-6/grevlex/bn254/default | 144 x 152 | 98 | 11.2% | 19.0% | 0 / 9 | 0.0% |
| cyclic-5/grevlex/bn254/baseline | 635 x 379 | 317 | 3.5% | 15.1% | 0 / 42 | 0.0% |
| mq-random-6/grevlex/p31x64/default | 757 x 756 | 659 | 2.8% | 25.1% | 0 / 97 | 0.0% |
| mq-random-6/grevlex/p31x64/baseline | 3305 x 3342 | 3269 | 0.6% | 30.4% | 0 / 601 | 0.0% |
| mq-random-10/grevlex/p31x64/default | 12554 x 12020 | 11086 | 0.5% | 35.2% | 0 / 13411 | 0.0% |
| cyclic-6/grevlex/gf2/default | 130 x 163 | 50 | 10.9% | 17.7% | 0 / 9 | 0.0% |
| cyclic-7/grevlex/gf2/default | 1146 x 795 | 372 | 9.3% | 30.4% | 0 / 197 | 0.0% |
| cyclic-6/grevlex/gf256/default | 130 x 163 | 50 | 10.9% | 17.7% | 0 / 9 | 0.0% |
| cyclic-5/lex/gf256/default | 61 x 72 | 55 | 10.0% | 12.7% | 0 / 2 | 0.0% |

## Pair-row residual D' = D - C A^-1 B, before and after its own echelon

| entry | D' rows x cols | D' density | D' max tile | D' nz in dense tiles | rank | echelon density | echelon max tile | echelon nz in dense tiles |
|---|---|---:|---:|---:|---:|---:|---:|---:|
| katsura-7/grevlex/m31/default | 98 x 106 | 67.0% | 100.0% | 59.1% | 43 | 69.5% | 100.0% | 57.0% |
| katsura-7/grevlex/m31/baseline | 22 x 74 | 90.0% | 100.0% | 100.0% | 11 | 92.0% | 100.0% | 100.0% |
| katsura-6/lex/m31/baseline | 1126 x 117 | 40.1% | 90.3% | 93.0% | 86 | 40.1% | 81.8% | 90.8% |
| cyclic-6/grevlex/m31/default | 102 x 118 | 52.4% | 84.2% | 72.7% | 55 | 51.6% | 82.9% | 73.5% |
| cyclic-6/lex/m31/default | 8 x 30 | 62.5% | 62.5% | 100.0% | 4 | 62.5% | 62.5% | 100.0% |
| katsura-7/grevlex/p64/default | 98 x 106 | 67.0% | 100.0% | 59.1% | 43 | 69.5% | 100.0% | 57.0% |
| cyclic-6/grevlex/p64/default | 102 x 118 | 52.4% | 84.2% | 72.7% | 55 | 51.6% | 82.9% | 73.5% |
| katsura-6/lex/p64/baseline | 1126 x 117 | 40.1% | 90.3% | 93.0% | 86 | 40.1% | 81.8% | 90.8% |
| katsura-6/grevlex/bn254/default | 46 x 54 | 69.2% | 69.2% | 100.0% | 23 | 71.0% | 71.0% | 100.0% |
| cyclic-5/grevlex/bn254/baseline | 318 x 62 | 43.1% | 49.1% | 0.0% | 48 | 58.3% | 58.3% | 100.0% |
| mq-random-6/grevlex/p31x64/default | 98 x 97 | 68.7% | 100.0% | 68.7% | 39 | 75.3% | 100.0% | 100.0% |
| mq-random-6/grevlex/p31x64/baseline | 36 x 73 | 84.7% | 100.0% | 100.0% | 16 | 84.8% | 100.0% | 100.0% |
| mq-random-10/grevlex/p31x64/default | 1468 x 934 | 43.9% | 100.0% | 86.1% | 579 | 52.3% | 100.0% | 94.6% |
| cyclic-6/grevlex/gf2/default | 80 x 113 | 24.2% | 37.9% | 0.0% | 44 | 24.7% | 37.2% | 0.0% |
| cyclic-7/grevlex/gf2/default | 774 x 423 | 25.1% | 51.2% | 21.8% | 267 | 27.6% | 52.0% | 26.2% |
| cyclic-6/grevlex/gf256/default | 80 x 113 | 24.2% | 37.9% | 0.0% | 44 | 24.7% | 37.2% | 0.0% |
| cyclic-5/lex/gf256/default | 6 x 17 | 47.1% | 47.1% | 0.0% | 3 | 47.1% | 47.1% | 0.0% |

## Where the multiply-adds are: sparse C A^-1 B sweep against a dense echelon of D'

| entry | sweep multiply-adds (exact) | dense D' echelon multiply-adds | dense share | D' cells |
|---|---:|---:|---:|---:|
| katsura-7/grevlex/m31/default | 272854 | 281134 | 50.7% | 10388 |
| katsura-7/grevlex/m31/baseline | 1704029 | 12078 | 0.7% | 1628 |
| katsura-6/lex/m31/baseline | 3690919 | 6895480 | 65.1% | 131742 |
| cyclic-6/grevlex/m31/default | 62527 | 380160 | 85.9% | 12036 |
| cyclic-6/lex/m31/default | 62481 | 610 | 1.0% | 240 |
| katsura-7/grevlex/p64/default | 272854 | 281134 | 50.7% | 10388 |
| cyclic-6/grevlex/p64/default | 62527 | 380160 | 85.9% | 12036 |
| katsura-6/lex/p64/baseline | 3690919 | 6895480 | 65.1% | 131742 |
| katsura-6/grevlex/bn254/default | 29095 | 33856 | 53.8% | 2484 |
| cyclic-5/grevlex/bn254/baseline | 138612 | 537512 | 79.5% | 19716 |
| mq-random-6/grevlex/p31x64/default | 576733 | 239174 | 29.3% | 9506 |
| mq-random-6/grevlex/p31x64/baseline | 1354377 | 28720 | 2.1% | 2628 |
| mq-random-10/grevlex/p31x64/default | 269509492 | 455423258 | 62.8% | 1371112 |
| cyclic-6/grevlex/gf2/default | 7598 | 236060 | 96.9% | 9040 |
| cyclic-7/grevlex/gf2/default | 865179 | 50970478 | 98.3% | 327402 |
| cyclic-6/grevlex/gf256/default | 7598 | 236060 | 96.9% | 9040 |
| cyclic-5/lex/gf256/default | 488 | 182 | 27.2% | 102 |
