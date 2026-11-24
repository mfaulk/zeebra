| Arm | gf32003 | m31 | w59 | wide64 | goldilocks |
|---|---|---|---|---|---|
| P1 conv-w1 | pass 13 | pass 14 | pass 7 | pass 16 | pass 11, stopped 1 |
| P2 conv-w4 | pass 13 | pass 14 | pass 7 | pass 16 | pass 11, stopped 1 |
| P3 conv-w16 | pass 13 | pass 14 | pass 7 | pass 16 | pass 11, stopped 1 |
| P4 sig-w1 | pass 13 | pass 14 | pass 7 | pass 16 | pass 12 |
| P5 sig-w8 | pass 13 | pass 14 | pass 7 | pass 16 | pass 12 |
| P6 sig-w16 | pass 13 | pass 14 | pass 7 | pass 16 | pass 12 |
| P7 conv-cap16 | pass 26 | pass 28 | pass 14 | pass 32 | pass 22, stopped 2 |
| P8 adaptive | pass 26 | pass 28 | pass 14 | pass 32 | pass 22, stopped 2 |
| #997 fewest-fl | pass 26 | pass 28 | pass 14 | pass 32 | pass 22, stopped 2 |

744 cells; not passed:
- P1 conv-w1 w=1 grlex/goldilocks/mq-random-11: stopped (TooManyNonzeros { nonzeros: 37534388, limit: 32000000 })
- P2 conv-w4 w=4 grlex/goldilocks/mq-random-11: stopped (TooManyNonzeros { nonzeros: 37534388, limit: 32000000 })
- P3 conv-w16 w=16 grlex/goldilocks/mq-random-11: stopped (TooManyNonzeros { nonzeros: 37534388, limit: 32000000 })
- P7 conv-cap16 w=1 grlex/goldilocks/mq-random-11: stopped (TimeBudgetExceeded { degree: 8, elapsed_millis: 180562, budget_millis: 180000 })
- P7 conv-cap16 w=16 grlex/goldilocks/mq-random-11: stopped (TooManyNonzeros { nonzeros: 32054067, limit: 32000000 })
- P8 adaptive w=1 grlex/goldilocks/mq-random-11: stopped (TooManyNonzeros { nonzeros: 37534388, limit: 32000000 })
- P8 adaptive w=16 grlex/goldilocks/mq-random-11: stopped (TooManyNonzeros { nonzeros: 37534388, limit: 32000000 })
- #997 fewest-fl w=1 grlex/goldilocks/mq-random-11: stopped (TooManyNonzeros { nonzeros: 32000079, limit: 32000000 })
- #997 fewest-fl w=16 grlex/goldilocks/mq-random-11: stopped (TooManyNonzeros { nonzeros: 32000025, limit: 32000000 })
