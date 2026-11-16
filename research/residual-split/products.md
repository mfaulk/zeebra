<!-- block_density split with --features research-work, built at 818e976b (forward pass unchanged at ca65b34d); tools/benchlock.sh zb-803, taskset -c 8. Read the coefficient-product counts only: its times carry the hook overhead and its shipped arm is the full-RREF route. -->

5 interleaved repetitions per arm; medians [min, max] in ms.

| entry | rows x cols | backend | shipped batch | forward only | reference sweep | shipped echelon of D' | sweep multiply-adds |
|---|---|---|---:|---:|---:|---:|---:|
| mq-random-10/grevlex/p31x64/default | 12554 x 12020 | Adaptive | 1389.2 [1377.1, 1497.3] | 710.2 [688.9, 743.9] | 378.8 [348.9, 395.0] | 83.1 [80.3, 85.0] | 269509492 |
|   | measured ceiling, shipped / reference sweep | 3.67x | | | | | |
|   | forward products: inherited 222124839 + discovered 217291977 (49.5%); sweep at 1.616 ns/product = 435.6 ms; estimated ceiling 3.19x | | | | | |

5 interleaved repetitions per arm; medians [min, max] in ms.

| entry | rows x cols | backend | shipped batch | forward only | reference sweep | shipped echelon of D' | sweep multiply-adds |
|---|---|---|---:|---:|---:|---:|---:|
|   | **refused** under its own 64000000 live-entry budget at 64000583 live entries; arms below run unbounded | | | | | |
| mq-random-14/grevlex/p31x64/default-64m | 75091 x 76194 | Adaptive | 383476.1 [382026.2, 399585.8] | 136416.1 [135181.3, 143278.0] | 49196.5 [48916.8, 52273.8] | 42181.9 [41904.2, 44084.2] | 34940392155 |
|   | measured ceiling, shipped / reference sweep | 7.79x | | | | | |
|   | forward products: inherited 21221997121 + discovered 67796867340 (76.2%); sweep at 1.532 ns/product = 53544.0 ms; estimated ceiling 7.16x | | | | | |
