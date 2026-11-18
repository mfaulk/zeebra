# #86 evidence: GPU-suitability kernel census

Report: [`docs/research/gpu-kernel-classification.md`](../../docs/research/gpu-kernel-classification.md).

**Measured at:** binaries built from `25d9588a` (`examples/gpu_kernel_census.rs` and the
`residual-work` mode of `examples/block_density.rs`; `src/` identical to `main` at `6a69522f`),
2026-11-18, release, fat LTO, `x86-64-v3`, `CARGO_TARGET_DIR=/buildcache/cargo-target/zeebra-86`,
`RUSTC_WRAPPER=""`. Host: Threadripper PRO 5995WX. No CCD reservation.

| File | What |
|---|---|
| [run.sh](run.sh) | `ceilings` and `stages` (timed, under `tools/benchlock.sh zb-86`, CPU 48 / CPUs 48–63), `census` and `residual` (exact counts, no lock) |
| `ceilings-25d9588a.json` | per-field step rates at L1/L2/L3/DRAM residency, plus one core's streaming read; five rotated repetitions |
| `f4-stages-25d9588a.jsonl` | stage clocks, seven system/field pairs × {1, 16} workers × five repetitions, interleaved; `load1` per child |
| `f4-census-25d9588a.jsonl` | the serial entry census (`--work`, research-work build) per pair. The `mq-9` rows are trivial systems and are not used |
| `residual-work-25d9588a.md` | exact work on `D'` for the corpus's random-MQ entries and the large `mq-random-14` capture |
| [analyze.py](analyze.py) → [tables.md](tables.md) | every table in the report; it also reads `research/m30-final/{stages,census}.jsonl.gz` (`e4826153`) |
| [benchlock.log](benchlock.log) | the two `zb-86` lock windows (load 1.90 → 2.02 and 1.94 → 2.20) |

Reproduce, with both binaries copied to `$BIN/stock` and `$BIN/work`:

```bash
COMMIT=25d9588a ONE=48 SIXTEEN=48-63 research/gpu-kernels/run.sh ceilings
COMMIT=25d9588a ONE=48 SIXTEEN=48-63 research/gpu-kernels/run.sh stages
COMMIT=25d9588a ONE=41 research/gpu-kernels/run.sh census
COMMIT=25d9588a ONE=42 research/gpu-kernels/run.sh residual
python3 research/gpu-kernels/analyze.py > research/gpu-kernels/tables.md
```

The census was taken before `run.sh`'s case list dropped `katsura-10` and `mq-9` from the timed
set. `katsura-10` over BN254 takes 120 s per serial run.
