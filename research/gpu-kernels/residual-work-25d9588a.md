Exact counts; nothing is timed. Products are coefficient multiply-adds.

| entry | backend | D' rows x cols | D' entries | rank | sweep products | dense-model echelon products | shipped echelon products | echelon dense loads | echelon scan cells | echelon gather cells | back-substitution products | cell bytes |
|---|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| mq-random-6/grevlex/p31x64/default | Adaptive | 86 x 97 | 5809 | 39 | 502379 | 203138 | 49379 | 5809 | 1707 | 3042 | 31936 | 8 |
| mq-random-6/grevlex/p31x64/baseline | Sparse | 36 x 73 | 2225 | 16 | 1354377 | 28720 | 8045 | 0 | 0 | 0 | 3654 | 8 |
| mq-random-10/grevlex/p31x64/default | Adaptive | 1305 x 934 | 541552 | 579 | 239473690 | 394644470 | 50862096 | 541552 | 312731 | 373031 | 27476045 | 8 |
| mq-random-8/grevlex/gf256/default | Adaptive | 190 x 312 | 46510 | 74 | 25413498 | 3131495 | 587881 | 46510 | 6232 | 20387 | 315667 | 8 |
Exact counts; nothing is timed. Products are coefficient multiply-adds.

| entry | backend | D' rows x cols | D' entries | rank | sweep products | dense-model echelon products | shipped echelon products | echelon dense loads | echelon scan cells | echelon gather cells | back-substitution products | cell bytes |
|---|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| mq-random-14/grevlex/p31x64/default-64m | Adaptive | 6740 x 8783 | 37112849 | 3504 | 30240883045 | 126451604480 | 26707879108 | 37112849 | 18605609 | 23229300 | 18974868056 | 8 |
