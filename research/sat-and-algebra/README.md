# #220 raw outputs

Unedited stdout of `examples/sat_algebra.rs`, each with `uptime` before (and for `preprocess`,
after) the run. The analysis is [`docs/research/sat-and-algebra.md`](../../docs/research/sat-and-algebra.md).

| file | command | commit |
|---|---|---|
| `clauses.md` | `sat_algebra clauses` | `e6b04c24` |
| `replay.md` | `sat_algebra replay 3` | `e6b04c24` |
| `preprocess.md` | `sat_algebra preprocess 3` | `60c50d7a` |

Built `--release` with a private `CARGO_TARGET_DIR`, run unpinned on a shared 128-thread machine,
`ZEEBRA_EXT_PREFIX` holding kissat 4.0.4, CryptoMiniSat 5.18.0 and `cms-xor-driver` from
`tools/external/provision-sat.sh`. Instances are public: random planted quadratic systems over
`GF(2)` generated in the example from fixed seeds.
