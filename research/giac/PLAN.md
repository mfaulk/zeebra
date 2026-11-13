# Giac adapter acceptance cohort (#740)

Declared before measurement, 2026-11-13. This is an adapter/provenance study;
no claim of equal compiler/ISA settings between the prebuilt Giac engine and
Zeebra, and no cross-engine speedup claim. Giac 2.0.0, upstream Debian package
2.0.0-3, SHA-256 `4986dec6c37fcc8a76e4a71c483f722666e9ebc149d84921bfbafe114aa9a451`.

Use existing `groebner_comparison`, CompetitiveBoard records, and the guarded
`run` function in `tools/external/grobx-cohort.py` (one fresh harness per row).
Select frozen `mq-random-10`, `katsura-11`, and `cyclic-5` at both GF(32003) and
GF(2147483647). Bind ordered generators and variable lists to the existing
corpus digest before each computation; retain complete bases and the raw
independent Singular answers. Every coefficient must agree before accepting
any row. The exact check and its elapsed cost are separate from Giac child
wall/CPU/RSS. Every accepted row gets its quotient dimension and leading ideal
from the exactly matched independent result.

Workers 1 and 4, five interleaved fresh processes per case/cohort (60 attempts).
CPU2 for one worker; physical cores CPU2–5 for four workers, checked against
`lscpu` rather than inferred from numbering. Alternate worker-order by repeat;
serialize the whole campaign with `tools/benchlock.sh`. Capture topology,
load, affinities, source/compiler/lockfile/binary/runtime-library fingerprints
inside the lock. Build/test before locking, release/fat LTO/one codegen unit,
x86-64-v3 for the Rust harness, empty wrapper, private target/scratch on
`/buildcache`. Engine compiler/ISA is unspecified, not borrowed from the harness.

Per child (Giac and verifier): 60 s / 2 GiB RSS. Existing parent watchdog:
185 s / 2 GiB RSS. Whole campaign: 3000 s external stop. Preserve every attempt,
including stops/failures; no ratio or completion time inferred from a limit.
After regular cases, retain capability refusals at 2^64−353 (`mq-planted-wide-6`) and
2^64−59 (`groebner-rs-wide-control`). Goldilocks is also refused in API tests. There are no wide-field arithmetic timings in this study.

The acceptance target is agreeing complete output for the three requested
families at each worker count, or a precise, reproducible blocker. Full-output
verification failures reject adapter readiness; time/memory stops stay visible.
No worker crossover or general scaling conclusion is an adoption requirement
here: startup-heavy controls cannot establish one, and #739 owns broader
comparand scaling. Report median/range/RSS per cohort without historical ratios.
