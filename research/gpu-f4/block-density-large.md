<!-- examples/block_density.rs (#225) at base 8dbf9bcf, release profile; exact counts, see docs/research/gpu-f4.md -->

Tiles are 64x64; "dense" means at least 50.0% full.

## As built, reducers first: [A B; C D]

| entry | rows x cols | reducer rows | density | max tile | dense tiles / occupied | nz in dense tiles |
|---|---|---:|---:|---:|---:|---:|
| mq-random-14/grevlex/p31x64/default-64m | 75091 x 76194 | 67411 | 0.4% | 46.1% | 0 / 294157 | 0.0% |

## Pair-row residual D' = D - C A^-1 B, before and after its own echelon

| entry | D' rows x cols | D' density | D' max tile | D' nz in dense tiles | rank | echelon density | echelon max tile | echelon nz in dense tiles |
|---|---|---:|---:|---:|---:|---:|---:|---:|
| mq-random-14/grevlex/p31x64/default-64m | 7680 x 8783 | 63.1% | 100.0% | 90.8% | 3504 | 65.2% | 100.0% | 96.4% |

## Where the multiply-adds are: sparse C A^-1 B sweep against a dense echelon of D'

| entry | sweep multiply-adds (exact) | dense D' echelon multiply-adds | dense share | D' cells |
|---|---:|---:|---:|---:|
| mq-random-14/grevlex/p31x64/default-64m | 34940392155 | 149608384160 | 81.1% | 67453440 |
