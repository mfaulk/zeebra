### Gate D held-out read, F2 db181c51 ÷ F0

| Row | Engine | Workers | Method | F0 median | n | F2 ÷ F0 wall [95%] | Peak RSS ratio | Excluded |
|---|---|---:|---|---:|---:|---|---:|---:|
| grevlex/gf32003/katsura-12 | entry | 1 | process wall | 4399.1 ms | 8 | 0.855 [0.852, 0.863] | 0.740 | 1 |
| grevlex/gf32003/katsura-12 | entry | 4 | process wall | 2540.2 ms | 5 | 0.692 [0.673, 0.709] | 0.739 | 4 |
| grevlex/gf32003/katsura-12 | entry | 8 | process wall | 2285.8 ms | 4 | 0.649 [0.644, 0.654] | 0.744 | 6 |
| grevlex/gf32003/katsura-12 | entry | 16 | process wall | 2179.8 ms | 8 | 0.655 [0.645, 0.658] | 0.737 | 1 |
| grevlex/m31/mq-random-10-s1 | entry | 1 | process wall | 5313.3 ms | 8 | 0.717 [0.713, 0.719] | 1.036 | 1 |
| grevlex/m31/mq-random-10-s1 | entry | 4 | process wall | 1375.8 ms | 8 | 0.995 [0.982, 1.017] | 1.007 | 1 |
| grevlex/m31/mq-random-10-s1 | entry | 8 | process wall | 937.4 ms | 5 | 1.006 [1.002, 1.008] | 1.003 | 4 |
| grevlex/m31/mq-random-10-s1 | entry | 16 | process wall | 751.7 ms | 9 | 1.004 [0.996, 1.010] | 1.018 | 0 |
| grevlex/wide64/katsura-12 | entry | 1 | process wall | 4909.2 ms | 9 | 0.840 [0.836, 0.846] | 0.840 | 0 |
| grevlex/wide64/katsura-12 | entry | 16 | process wall | 2380.9 ms | 6 | 0.679 [0.674, 0.682] | 0.842 | 3 |
| grevlex/wide64/mq-random-10-s1 | entry | 1 | process wall | 5567.9 ms | 8 | 0.721 [0.719, 0.728] | 1.037 | 2 |
| grevlex/wide64/mq-random-10-s1 | entry | 16 | process wall | 888.0 ms | 1 | 1.009 [1.009, 1.009] | 0.960 | 11 |

| Row | Engine | Workers | Method | Verdict |
|---|---|---:|---|---|
| grevlex/gf32003/katsura-12 | entry | 1 | process wall | wall stopped: n = 8 < 9 |
| grevlex/gf32003/katsura-12 | entry | 4 | process wall | wall stopped: n = 5 < 9 |
| grevlex/gf32003/katsura-12 | entry | 8 | process wall | wall stopped: n = 4 < 9 |
| grevlex/gf32003/katsura-12 | entry | 16 | process wall | wall stopped: n = 8 < 9 |
| grevlex/m31/mq-random-10-s1 | entry | 1 | process wall | wall stopped: n = 8 < 9 |
| grevlex/m31/mq-random-10-s1 | entry | 4 | process wall | wall stopped: n = 8 < 9 |
| grevlex/m31/mq-random-10-s1 | entry | 8 | process wall | wall stopped: n = 5 < 9 |
| grevlex/m31/mq-random-10-s1 | entry | 16 | process wall | pass |
| grevlex/wide64/katsura-12 | entry | 1 | process wall | pass |
| grevlex/wide64/katsura-12 | entry | 16 | process wall | wall stopped: n = 6 < 9 |
| grevlex/wide64/mq-random-10-s1 | entry | 1 | process wall | wall stopped: n = 8 < 9 |
| grevlex/wide64/mq-random-10-s1 | entry | 16 | process wall | wall stopped: n = 1 < 9 |

**Session void:** ae1f4abb17c1, 16 of 72 attempts contaminated.
