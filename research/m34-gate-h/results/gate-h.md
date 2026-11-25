# Gate H read (#1012)

**Verdict: no-go.** Contexts passing: none; single-decision arm sets passing: none.

Pilot: 127 base problems, 36 families. Development: 122 records, 64 base problems, 17 families. Disqualified arms: none.

Costs are PAR-2 penalized (2C = 600 s for every attempt that is not a verified completion), not runtimes.

| Arm set | H | 95% interval | families ≤ 0.85 | H without largest contributor | split halves | Go clauses met |
|---|---:|---|---:|---|---|---|
| W16 | 0.703 | [0.392, 0.942] | 6 | 0.895 (sd/ellipsoid) | 0.702 / 0.701 | h, families, split_half |
| W1 | 0.767 | [0.446, 0.988] | 2 | 0.981 (sd/ellipsoid) | 0.765 / 0.764 | h, split_half |
| engine@1w | 0.767 | [0.446, 0.988] | 2 | 0.981 (sd/ellipsoid) | 0.765 / 0.764 | h, split_half |
| engine@16w | 0.845 | [0.399, 0.975] | 3 | 0.953 (sd/ellipsoid) | 0.844 / 0.844 | families, split_half |
| workers@conv | 0.868 | [0.757, 0.953] | 4 | 0.926 (katsura) | 0.868 / 0.864 | families |
| workers@sig | 0.952 | [0.832, 0.998] | 2 | 0.975 (katsura) | 0.953 / 0.953 | none |
| workers@cap16 | 0.894 | [0.802, 0.998] | 5 | 0.953 (katsura) | 0.871 / 0.901 | families |
| workers@adaptive | 0.925 | [0.779, 0.985] | 4 | 0.944 (katsura) | 0.925 / 0.925 | families |

## Context W16

PAR-10 H 0.681; completed-intersection H 0.898 over 61 problems in 17 families (sensitivity views; they do not decide).

| Family | problems | LOFO best fixed | VBS⁺ ÷ BF |
|---|---:|---|---:|
| `app/chandrasekhar-h` | 10 | P8-w1 | 0.909 |
| `app/multisite-phosphorylation` | 9 | P8-w1 | 0.989 |
| `cyclic` | 2 | P8-w1 | 0.745 |
| `eco` | 2 | P8-w1 | 0.794 |
| `katsura` | 2 | P8-w1 | 0.652 |
| `noon` | 2 | P8-w1 | 0.885 |
| `reimer` | 2 | P8-w1 | 0.762 |
| `sd/classical/cassou` | 1 | P8-w1 | 0.997 |
| `sd/classical/heron` | 2 | P8-w1 | 0.994 |
| `sd/classical/raksanyi` | 1 | P8-w1 | 0.976 |
| `sd/classical/weispfenning-94` | 1 | P8-w1 | 0.982 |
| `sd/ellipsoid` | 3 | P8-w1 | 0.120 |
| `sd/four-body` | 1 | P8-w1 | 0.897 |
| `sd/runge-kutta-order-conditions` | 4 | P4 | 0.116 |
| `sd/schwarz` | 4 | P8-w1 | 0.996 |
| `zb/graph-3colouring` | 12 | P8-w1 | 0.938 |
| `zb/toric` | 6 | P8-w1 | 0.969 |

| Arm | verified cells | penalized cells | marginal (VBS⁺ without ÷ with) |
|---|---:|---:|---:|
| P1 | 116 | 6 | 1.002 |
| P2 | 116 | 6 | 1.003 |
| P3 | 116 | 6 | 1.001 |
| P4 | 120 | 2 | 1.011 |
| P5 | 120 | 2 | 1.003 |
| P6 | 120 | 2 | 1.000 |
| P7-w1 | 116 | 6 | 1.001 |
| P7-w16 | 116 | 6 | 1.000 |
| P8-w1 | 118 | 4 | 1.002 |
| P8-w16 | 118 | 4 | 1.000 |

## Context W1

PAR-10 H 0.743; completed-intersection H 0.980 over 61 problems in 17 families (sensitivity views; they do not decide).

| Family | problems | LOFO best fixed | VBS⁺ ÷ BF |
|---|---:|---|---:|
| `app/chandrasekhar-h` | 10 | P8-w1 | 0.990 |
| `app/multisite-phosphorylation` | 9 | P8-w1 | 0.989 |
| `cyclic` | 2 | P8-w1 | 0.995 |
| `eco` | 2 | P8-w1 | 1.001 |
| `katsura` | 2 | P8-w1 | 0.998 |
| `noon` | 2 | P8-w1 | 0.885 |
| `reimer` | 2 | P8-w1 | 0.993 |
| `sd/classical/cassou` | 1 | P8-w1 | 0.997 |
| `sd/classical/heron` | 2 | P8-w1 | 0.994 |
| `sd/classical/raksanyi` | 1 | P8-w1 | 0.976 |
| `sd/classical/weispfenning-94` | 1 | P8-w1 | 0.982 |
| `sd/ellipsoid` | 3 | P8-w1 | 0.120 |
| `sd/four-body` | 1 | P8-w1 | 0.996 |
| `sd/runge-kutta-order-conditions` | 4 | P4 | 0.124 |
| `sd/schwarz` | 4 | P8-w1 | 0.996 |
| `zb/graph-3colouring` | 12 | P8-w1 | 0.941 |
| `zb/toric` | 6 | P8-w1 | 0.969 |

| Arm | verified cells | penalized cells | marginal (VBS⁺ without ÷ with) |
|---|---:|---:|---:|
| P1 | 116 | 6 | 1.002 |
| P4 | 120 | 2 | 1.144 |
| P7-w1 | 116 | 6 | 1.001 |
| P8-w1 | 118 | 4 | 1.003 |

## Cheapest arm per record (W16 arms)

| Family | wins |
|---|---|
| `app/chandrasekhar-h` | P5 7, P8-w1 5, P4 3, P6 2, none 2, P7-w1 1 |
| `app/multisite-phosphorylation` | P4 9, P8-w1 5, P1 4 |
| `cyclic` | P3 2, P8-w1 1, P1 1 |
| `eco` | P5 2, P8-w1 2 |
| `katsura` | P6 2, P5 2 |
| `noon` | P4 4 |
| `reimer` | P8-w1 1, P4 1, P2 1, P8-w16 1 |
| `sd/classical/cassou` | P7-w1 1, P8-w1 1 |
| `sd/classical/heron` | P1 2, P4 2 |
| `sd/classical/raksanyi` | P8-w1 1, P4 1 |
| `sd/classical/weispfenning-94` | P4 2 |
| `sd/ellipsoid` | P4 5, P7-w1 1 |
| `sd/four-body` | P3 2 |
| `sd/runge-kutta-order-conditions` | P2 4, P1 2, P8-w1 2 |
| `sd/schwarz` | P8-w1 4, P4 4 |
| `zb/graph-3colouring` | P4 10, P7-w1 6, P1 4, P8-w1 2, P5 2 |
| `zb/toric` | P1 3, P4 2, P8-w1 1 |
