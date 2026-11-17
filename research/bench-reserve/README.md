# #848 calibration: what a reserved CCD does and does not fence

**Measured at:** `faa015e6`, whose library and example sources are those of `main` at `527a105e`
(the commit adds only `tools/`). 2026-11-16 23:46 – 2026-11-17 00:11 EST, AMD Threadripper PRO
5995WX, governor `performance`, boost on, CCDs 1-2 (CPUs 8-23 + siblings 72-87) reserved with
`tools/bench-reserve.sh`. One `tools/benchlock.sh` window per campaign ([benchlock.log](benchlock.log)).
Findings and the policy they set: `docs/guide/benchmarking.md`, *Reserved CCDs*.

Subjects are fresh-process `m29_cost_model` runs on the shipping defaults: `mq10-32003` at one
worker on CPU 8 (33 MB peak RSS, just past one CCD's 32 MB L3), `mq10-32003` at 16 workers and
`eco12-wide64` at 16 workers (197 MB, DRAM-bound) on CPUs 8-23. The driver itself runs in
`zbbench.slice`, so its launch overhead is the same in every arm.

| arm | the other six CCDs | fence |
|---|---|---|
| A1, A2 | idle (A2 repeats A1 last, as the drift check) | reserved |
| B | three loops of full-clean dev builds, `-j32` each (load ~180–300) | reserved |
| D | 16 NumPy streams copying 1 GiB arrays (DRAM bandwidth, load ~13) | reserved |
| C | the same builds as B | **released**: builds may run on CCDs 1-2 |

[`aa.jsonl.gz`](aa.jsonl.gz) is a separate A/A campaign: the same binary run twice back to back,
nine pairs, idle and then under B's load. Its ratio spread is the noise an interleaved A/B on a
reserved CCD inherits.

| file | what |
|---|---|
| [run.sh](run.sh), [run-aa.sh](run-aa.sh) | the two campaigns, one benchlock window each |
| [driver.py](driver.py), [aa.py](aa.py) | the children, with `tools/cpu-context.sh` before and after each |
| [memhog.py](memhog.py) | arm D's bandwidth hog |
| [analyze.py](analyze.py) → [tables.md](tables.md) | both tables |
| `walls.jsonl.gz`, `aa.jsonl.gz` | one record per child or pair |
| [events.log](events.log) | arm boundaries with the load at each |

Every child completed with one basis digest per subject. The clock readings in the records were
taken just before and just after each child, when the core is idle; they do not show the
clock during the run, and nothing here separates a clock effect from a memory one.
