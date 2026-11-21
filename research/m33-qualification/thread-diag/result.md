Cap 16. Maxima over runs, except over_cap_samples (summed). `workers` excludes the calling thread; `total` includes it. over_cap_* describe samples with more than the cap of workers alive.

| Row | Arm | Runs | Status | max_running_workers | max_running_total | max_alive_workers | over_cap_samples | over_cap_running_workers | over_cap_from_ended_teams | largest_team | team_overlaps | sweep_us |
|---|---|---:|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| grevlex/gf32003/katsura-11 | f0-entry | 20 | complete | 15 | 16 | 15 | 0 | 0 | 0 | 15 | 2 | 19.3 |
| grevlex/gf32003/katsura-11 | f0-f4 | 20 | complete | 16 | 17 | 16 | 0 | 0 | 0 | 16 | 1 | 39.4 |
| grevlex/gf32003/katsura-11 | f2-entry | 20 | complete | 15 | 16 | 15 | 0 | 0 | 0 | 15 | 1 | 21.3 |
| grevlex/gf32003/katsura-11 | f2-f4 | 20 | complete | 16 | 17 | 16 | 0 | 0 | 0 | 16 | 2 | 39.9 |
| grevlex/gf32003/noon-7 | f0-entry | 20 | complete | 7 | 8 | 7 | 0 | 0 | 0 | 7 | 0 | 19.7 |
| grevlex/gf32003/noon-7 | f0-f4 | 20 | complete | 16 | 17 | 25 | 2 | 4 | 10 | 16 | 2 | 25.2 |
| grevlex/gf32003/noon-7 | f2-entry | 20 | complete | 7 | 8 | 8 | 0 | 0 | 0 | 8 | 1 | 18.9 |
| grevlex/gf32003/noon-7 | f2-f4 | 20 | complete | 16 | 17 | 16 | 0 | 0 | 0 | 16 | 3 | 24.6 |
| grevlex/wide64/cyclic-7 | f0-entry | 20 | complete | 20 | 20 | 21 | 3 | 20 | 5 | 16 | 3 | 23.4 |
| grevlex/wide64/cyclic-7 | f0-f4 | 20 | complete | 16 | 17 | 25 | 2 | 10 | 9 | 16 | 2 | 23.7 |
| grevlex/wide64/cyclic-7 | f2-entry | 20 | complete | 17 | 18 | 20 | 5 | 17 | 6 | 16 | 3 | 23.6 |
| grevlex/wide64/cyclic-7 | f2-f4 | 20 | complete | 17 | 18 | 17 | 4 | 17 | 1 | 16 | 4 | 24.8 |
| grevlex/wide64/noon-8 | f0-entry | 20 | complete | 8 | 9 | 11 | 0 | 0 | 0 | 11 | 3 | 17.6 |
| grevlex/wide64/noon-8 | f0-f4 | 20 | complete | 16 | 17 | 16 | 0 | 0 | 0 | 16 | 1 | 22.8 |
| grevlex/wide64/noon-8 | f2-entry | 20 | complete | 7 | 8 | 9 | 0 | 0 | 0 | 7 | 1 | 17.9 |
| grevlex/wide64/noon-8 | f2-f4 | 20 | complete | 17 | 18 | 18 | 3 | 17 | 5 | 16 | 2 | 22.5 |
| grlex/wide64/eco-12 | f0-f4 | 20 | complete | 16 | 17 | 16 | 0 | 0 | 0 | 16 | 2 | 36.3 |
| grlex/wide64/eco-12 | f2-entry | 20 | complete | 16 | 17 | 16 | 0 | 0 | 0 | 16 | 2 | 35.9 |
| grlex/wide64/eco-12 | f2-f4 | 20 | complete | 18 | 18 | 24 | 6 | 18 | 8 | 16 | 2 | 36.6 |
