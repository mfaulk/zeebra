# grobx's forced F4-lex route on #1039's class rows (#1127, for #1044)

**Measured at:** `c1d7af00` (driver with `lex_route`; Zeebra `src/` as `48778879`). **Mode:**
development, on a 14-core macOS/arm64 laptop. Runs were unpinned, RSS was not recorded, and n = 3.
This record decides nothing. Its purpose is to tell #1044 whether the reversal risk that #1039 §8
names is real before a bench-host session is spent on it.

## What was run

`mac_probe.py` ran three arms per row, interleaved, with three repetitions, a 300 s cap, a 16 GiB
grobx memory ceiling and one worker:

- `grobx`: the driver's default `lex` (FGLM for D ≤ 65535);
- `grobx-f4lex`: `lex_route: "f4"`, which is `Block(vec![1; n-1])`, so F4 in an order equal to lex;
- `adaptive`: `examples/lex_pipeline --arm adaptive --budget lifted`.

Each arm's wall is the process wall. Every attempt that completed gave the same `m33-basis-v1` digest
on its row.

| Row | D | grobx auto (s) | grobx F4-lex (s) | Zeebra adaptive (s) | adaptive ÷ auto | adaptive ÷ F4-lex |
|---|---|---|---|---|---|---|
| `wd-4-10` | 10⁴ | 1.294 | 0.005 | 0.472 | 0.36 | **93** |
| `wd-3-30` | 2.7·10⁴ | 4.895 | 0.007 | 2.366 | 0.48 | **339** |
| `wd-4-12` /2³¹−1 | 2.1·10⁴ | 8.941 | 0.010 | 1.495 | 0.17 | **152** |
| `wdsq-4-10` | 2·10⁴ | 12.086 | stopped (deadline 1, memory 2) | 1.772 | 0.15 | censored |
| `wdsq-5-6` | 1.6·10⁴ | 13.094 | stopped (memory 3/3, ~60 s) | 1.382 | 0.11 | censored |
| `wd-5-10` (control) | 10⁵ | 0.298 | 0.288 | 28.746 | 97 | 100 |

## Reading

- **The reversal is real on the radical chain rows.** In lex, the chain's last generator
  `x_{N-1}^d - x_0 - 1` leads with `x_0`, so F4 in lex finishes in milliseconds. The faster grobx
  route beats the pipeline by about 90–340× on `wd-4-10`, `wd-3-30` and `wd-4-12`. #1039's
  predicate admits these rows, and one of them (`wd-4-10`) is a development row. With the comparand
  set to the faster route as §9.4 requires, the class fails §9.5's development bar.
- **The nonradical rows survive this probe.** On `wdsq-4-10` and `wdsq-5-6`, grobx's F4-lex
  exhausts 16 GiB, so the faster grobx route is FGLM, and the pipeline reads 0.11–0.15 of it. A
  class limited to these rows would be a new predicate chosen after this read. It would need its
  own declaration and untouched rows, not a re-scoring of #1039's class.
- **The block order is a faithful proxy.** On `wd-5-10`, grobx's own `lex` already runs F4 in lex.
  Its lex run took 0.2775 s, and the forced block-order run took 0.2775 s (report `ran` times, last
  repetition). Comparing exponent by exponent adds nothing measurable here. The forced route also
  skips native lex's grevlex prelude, which costs 0.2 ms on these rows.

## Reproduce

```sh
S=<private target dir>
(cd tools/external/grobx-driver && CARGO_TARGET_DIR=$S/grobx cargo build --release --locked)
CARGO_TARGET_DIR=$S/zb cargo build --release --example lex_pipeline
TMPDIR=$S python3 research/1127-grobx-f4lex/mac_probe.py $S/zb/release/examples/lex_pipeline \
  $S/grobx/release/grobx-driver $S/mac-probe.jsonl research/1039-wiedemann-lex 3
```
