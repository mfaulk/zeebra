# #754 Zeebra M28 cohort

**Measured at:** `0e060666` (base `4eaa07f1`, patch id `b0056c11e730…` in every row), 2026-11-16,
under `tools/benchlock.sh 754-m28`: 09:40:49–09:51:15 EST, 626 s, `end=exited`, status 0, load
1.09 → 2.78 ([benchlock.log](benchlock.log)). Host `fedora`, AMD Ryzen Threadripper PRO 5995WX,
rustc 1.99.1, release, fat LTO, one codegen unit, `x86-64-v3`. Binary SHA-256 in
[binary.sha256](binary.sha256).

Zeebra only, one row per process, 60 s wall, no RSS cap. Two cohorts over the same 83 cells:
`--workers 1` on CPU 2 and `--workers 16` on CPUs 2–17 (distinct physical cores). The adapter caps
F4's parallel forward elimination at the cohort's workers (#754), so the serial cohort really is
serial. Cells: Katsura 4–11, Cyclic 4–9, MQ random/planted 6/10/14, at GF(32003) and
GF(2147483647), reduced Gröbner basis and lex by conversion; planted-wide 6/10/14 at 2^64−353,
reduced basis only. Comparand rows were not re-measured: #813 changed no comparand.

| file | what |
|---|---|
| [run.sh](run.sh) | the campaign, exactly as run |
| [campaign.log](campaign.log) | one line per attempt: cohort, cell, harness exit status, load |
| [summarize.py](summarize.py) | pairs the cohorts per cell from `../results/history.json` |
| [cohort.md](cohort.md) | its output: `python3 research/competitive/m28-754/summarize.py 0e060666` |

166 attempts: 138 complete, 20 stopped by the 60 s wall (Cyclic-9 both tasks, MQ-random-14 both,
MQ-planted-14 lex, each field, each cohort), 8 unsupported (Cyclic-4 and Cyclic-8 lex, as in every earlier
cohort). Both cohorts reach the same outcome in every cell. Each cell is a single observation,
so sub-millisecond cells and ratios under about 1.2x are within noise. The "fastest comparand"
column is the board's fastest complete non-Sagebrush row at any recorded worker count. Its timing
boundary differs by engine (see `COMPETITIVE.md`), so ratios against it are not claims.
