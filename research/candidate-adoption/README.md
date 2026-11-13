# Candidate-only production adoption (#749)

The production F4 route fully reduces extracted candidate rows and keeps unused echelon rows.
Public RREF remains full RREF. The private kernel reserves an upper bound for every selected
replacement's possible suffix growth plus one dense row **before** any target changes. If entry
reservation or the 64-MiB scratch/index/selection ceiling cannot be met, the original full-RREF
pass runs from the unchanged echelon matrix, preserving old admission and refusal semantics.

Mathematical `peak_nonzeros` excludes retained-original copies. `candidate_reduction` separately
reports selected targets, coefficient products, whole-pass reserved entries, sparse output/row
capacity, workspace and full-RREF fallback counts. A no-candidate batch builds no selection/dense/
index buffers. The existing research override reports zero production-contract batches.

## Bounded validation campaign

Build and test outside the benchmark lock. Use private target and scratch on `/buildcache` and
`RUSTC_WRAPPER=''`. Build a feature-absent `mq10_profile` at baseline `778e1dc9`, a feature-absent
production binary at the adoption source pin, and the same source with `research-work` enabled.
Copy each binary before changing features; retain SHA256, source, toolchain, allocator and ISA.

The existing runner's `adoption` phase schedules five alternating repetitions of stock,
feature-absent production and feature-present/counters-off production on MQ10, Cyclic-5 and
Katsura-6 at GF(32003)/GF(2^31−1): 90 attempts. `adoption-work` adds 20 separate MQ10 diagnostics
(full research control versus ordinary production with passive counters), never pooled into native
timings. Each child retains 60 seconds/2 GiB, with the existing 185-second outer watchdog.
Worst-case child budget: 6,600 seconds across 110 attempts; expected hot-region cost is under
three minutes from retained pilot evidence. A single 900-second outer campaign watchdog covers both phases; each completed attempt is checkpointed.
An aggregate timeout preserves the readable prefix and is not an accepted complete cohort.
No retries or budget extensions are preauthorized.
Output cap: 256 MiB for retained compressed records and full-basis sidecars; refuse expansion.

Predeclared adoption gates: exact full independent reference bases and pair/degree trajectories;
MQ10 at least 10% faster at both primes; no material control regression beyond 5%, assessed with
five repeated ranges and sub-millisecond control uncertainty; RSS no more than 1.25x unless an
explicit tradeoff is reviewed. Preserve every refusal, failure and environmental exclusion.
No frontier or wide-field performance claim follows from this bounded campaign.

```sh
ZEEBRA_MACHINE=5995wx ZEEBRA_AFFINITY=3 tools/benchlock.sh candidate-adoption \
  taskset -c 3 python3 tools/external/selective-backward-study.py \
  --phase adoption --stock /buildcache/candidate-adoption/stock \
  --production /buildcache/candidate-adoption/production \
  --binary /buildcache/candidate-adoption/observed \
  --baseline-commit 778e1dc9 --build-commit ADOPTION_BUILD_COMMIT \
  --scratch /buildcache/candidate-adoption/native \
  --output /buildcache/candidate-adoption/adoption.json.gz
```

Use `--phase adoption-work` with a separate scratch/output path for diagnostics. The runner rejects
research overrides presented as production, absent production metadata, mismatched complete bases,
input/trajectory drift, binary changes, dirty sources and ambient compilation. Build pins and the
final retained report replace `ADOPTION_BUILD_COMMIT` after the implementation is committed.
