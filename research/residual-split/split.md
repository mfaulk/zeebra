<!-- block_density split, stock build of ca65b34d; tools/benchlock.sh zb-803, taskset -c 8; AMD Ryzen Threadripper PRO 5995WX; load 2.08 at start, 1.35 at end, 2026-11-16 -->

5 interleaved repetitions per arm; medians [min, max] in ms.

| entry | rows x cols | backend | production batch | full RREF | forward only | reference sweep | echelon of D' | Faugère–Lachartre order | sweep multiply-adds |
|---|---|---|---:|---:|---:|---:|---:|---:|---:|
|   | candidates identical: 579 rows, coefficient for coefficient | | | | | |
| mq-random-10/grevlex/p31x64/default | 12554 x 12020 | Adaptive | 1067.2 [1057.8, 1079.4] | 1392.9 [1373.9, 1462.8] | 650.2 [640.7, 661.3] | 370.0 [355.5, 374.7] | 74.5 [74.1, 77.8] | 499.2 [485.6, 509.8] | 269509492 |
|   | ceilings over production: reference sweep 2.88x, Faugère–Lachartre order 2.14x; full RREF is 1.31x production | | | | | | | | | |

5 interleaved repetitions per arm; medians [min, max] in ms.

| entry | rows x cols | backend | production batch | full RREF | forward only | reference sweep | echelon of D' | Faugère–Lachartre order | sweep multiply-adds |
|---|---|---|---:|---:|---:|---:|---:|---:|---:|
|   | **refused** under its own 64000000 live-entry budget at 64000583 live entries; arms below run unbounded | | | | | |
|   | candidates identical: 3504 rows, coefficient for coefficient | | | | | |
| mq-random-14/grevlex/p31x64/default-64m | 75091 x 76194 | Adaptive | 251585.7 [245754.2, 253157.0] | 393487.4 [391910.9, 394779.3] | 132075.4 [131998.6, 132431.5] | 50050.6 [49951.2, 50318.1] | 41299.0 [41222.2, 43804.0] | 142557.1 [142495.1, 148102.6] | 34940392155 |
|   | ceilings over production: reference sweep 5.03x, Faugère–Lachartre order 1.76x; full RREF is 1.56x production | | | | | | | | | |
