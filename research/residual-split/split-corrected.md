<!-- block_density split, release build of 8a68368f (F4's own candidate selection); tools/benchlock.sh zb-816, taskset -c 40; AMD Ryzen Threadripper PRO 5995WX; load 10.23 at end, 2026-11-16 -->

| entry | rows x cols | backend | production batch | full RREF | forward only | reference sweep | echelon of D' | Faugère–Lachartre order | sweep multiply-adds |
|---|---|---|---:|---:|---:|---:|---:|---:|---:|
|   | candidates identical: 8 rows, coefficient for coefficient | | | | | |
| mq-random-10/grevlex/p31x64/default | 12554 x 12020 | Adaptive | 752.1 [729.9, 756.9] | 1481.6 [1459.2, 1499.7] | 746.1 [737.7, 751.2] | 393.0 [384.0, 396.0] | 87.1 [84.6, 87.5] | 548.3 [538.3, 549.5] | 269509492 |
|   | ceilings over production: reference sweep 1.91x, Faugère–Lachartre order 1.37x; full RREF is 1.97x production | | | | | | | | | |
