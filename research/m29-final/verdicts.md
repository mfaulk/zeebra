| Goal | Window | Target | Zeebra ms (workers, n) | Comparand ms (workers, n) | Zeebra / comparand [95%] | Bar | Verdict |
|---|---|---|---:|---:|---:|---:|---|
| A | mq10-try1 | MQ10 / 32003 | 292.8 (16, 9) | msolve (exact): 116.6 (8, 9) | **2.51×** [2.47, 2.55] | ≤1.5 | **target missed** |
| A | mq10-try1 | MQ10 / 2147483647 | 278.7 (16, 8) | msolve (exact): 165.8 (4, 8) | **1.68×** [1.64, 1.78] | ≤1.5 | **target missed** |
| B | walls+wide | eco12-wide64 | 3071.3 (16, 9) | grobx (raw, randomized): 1634.1 (1, 9) | **1.88×** [1.67, 1.89] | ≤0.9 | **target missed** |
| B | walls+wide | mq11-goldilocks | 5719.6 (16, 9) | grobx (raw, randomized): 2970.4 (1, 9) | **1.93×** [1.80, 1.94] | ≤0.9 | **target missed** |
