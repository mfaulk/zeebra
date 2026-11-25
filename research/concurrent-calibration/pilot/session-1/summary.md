# #1106 pilot summary (exploratory; decides nothing)

C = `5451e9f853c8f24bafed6875218a175de441e3f0`. Reservation: CCDs 1-2 (fallback, §5.3).

## Binaries

| binary | SHA-256 |
|---|---|
| `sig_f4_study` | `6ffc1e8819d82327f5c01286c0e607370b8e59827d0b2ecd26a0f52a469c0bc2` |
| `m29_cost_model` | `cb2c17ce7611a3cf8f1524336e5b1d9047f5b3c4ef20d7ccee000cc00ea04576` |
| `sweep` | `7b48f39b3b1bbe430adeea99ca203aa9ba0f9e9515ec8b3b3bd6a29912d5329f` |
| `stream` | `bc0bf4ac66866fff1511b38fa26fe9115c6898a7a7d7773694299c2b423a9682` |

## A/A on the calibration cohort (§7.2)

| cell | load | n | median a | A/A median [95% CI] | half-width |
|---|---|---:|---:|---|---:|
| C-E1 | W0 | 9 | 1.9217 | 0.9991 [0.9730, 1.0064] | 0.0261 |
| C-E1 | W4 | 9 | 2.2355 | 0.9991 [0.9832, 1.0162] | 0.0170 |
| C-M1 | W0 | 9 | 0.2812 | 1.0102 [0.9864, 1.0204] | 0.0238 |
| C-M1 | W4 | 9 | 0.3009 | 0.9982 [0.9892, 1.0084] | 0.0103 |
| C-M16 | W0 | 9 | 0.2425 | 0.9973 [0.9888, 1.0482] | 0.0509 |
| C-M16 | W4 | 9 | 0.2621 | 0.9934 [0.9588, 1.0346] | 0.0411 |
| C-P16 | W0 | 9 | 0.2619 | 1.0017 [0.9442, 1.0045] | 0.0575 |
| C-P16 | W4 | 9 | 0.2816 | 0.9794 [0.9693, 1.0065] | 0.0270 |

n per cell, `min(30, max(15, ceil(9 (h / 0.010)^2)))` with h the larger half-width: C-E1 30, C-M1 30, C-M16 30, C-P16 30. **n = 30** (the cap of 30 binds).

## Real small pair (§4.3), W0 only

| target | median every s | distinct/every [95% CI] | qualifies |
|---|---:|---|---|
| mq10-32003 | 0.2697 | 0.9683 [0.9559, 1.0099] | calibration (C-P16) |
| cyclic7-wide64 | 0.1572 | 0.9651 [0.9531, 0.9728] | yes |
| katsura11-wide64 | 1.5633 | 0.8907 [0.8789, 0.9025] | no |
| katsura11-m31 | 1.2924 | 0.8947 [0.8840, 0.9263] | no |

H-S16 = **cyclic7-wide64**.

## m5 tuning (§4.2)

| cell | threads | MiB | t_A s | t_0 s | t_1 s | passes | validation 1 | validation 2 | status |
|---|---:|---:|---:|---:|---:|---:|---|---|---|
| wide64/eco-12@1w | 1 | 32 | 1.9217 | 0.0579 | 0.0622 | 13 | 1.0357 | 1.0427 | accepted |
| gf32003/mq-random-10@1w | 1 | 32 | 0.2812 | 0.0579 | 0.0622 | 1 | 1.1990 | 1.2047 | untuned |
| wide64/cyclic-7@1w | 1 | 32 | 0.2748 | 0.0579 | 0.0622 | 1 | 1.1980 | 1.1922 | untuned |
| gf32003/mq-random-10@16w | 16 | 32 | 0.2425 | 0.2561 | 0.2730 | 1 | 2.1232 | 2.0743 | untuned |
| gf32003/katsura-11@16w | 16 | 32 | 0.3207 | 0.2561 | 0.2730 | 1 | 1.8559 | 1.8286 | untuned |
| gf31/mq-dense-15-s15@16w | 16 | 32 | 0.4679 | 0.2561 | 0.2730 | 1 | 1.5623 | 1.5507 | untuned |
