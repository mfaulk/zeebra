**Measured at:** `4f5784c5` (see README.md).

| Goal | Window | Target | Zeebra ms (workers, n) | Comparand ms (workers, n) | Zeebra / comparand [95%] | Bar | Verdict |
|---|---|---|---:|---:|---:|---:|---|
| A | mq10-try1 | MQ10 / 32003 | 290.0 (16, 9) | msolve (exact): 116.4 (8, 9) | **2.49×** [2.46, 2.52] | ≤1.5 | **target missed** |
| A | mq10-try1 | MQ10 / 2147483647 | 276.7 (16, 9) | msolve (exact): 157.8 (4, 9) | **1.75×** [1.62, 1.78] | ≤1.5 | **target missed** |
| B | walls+wide | eco12-wide64 | 3107.1 (16, 9) | grobx (raw, randomized): 1628.4 (1, 9) | **1.91×** [1.89, 1.95] | ≤0.9 | **target missed** |
| B | walls+wide | mq11-goldilocks | 5747.3 (16, 9) | grobx (raw, randomized): 2934.4 (1, 9) | **1.96×** [1.95, 1.99] | ≤0.9 | **target missed** |
