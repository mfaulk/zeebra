# M30-P2: deterministic parallel monomial interning and dispatch (#860)

**Measured at:** `514cada9` (the `intern` and `live` suites; executable SHA-256 `c6e9b6d3…`), and
`bcf5af6a` for the retained first `intern` pass (`intern-seed512`). Both heads' production source
outside `research-work` is the M30 freeze `4f5784c5` plus a refactor of one call site that compiles
to the same shipping path (`ed6f5fd7`). 2026-11-17, 11:08–12:30 EST, inside the CCD 1–2 reservation
(CPUs 8–23) held by #855, one `tools/bench-reserve.sh run zb-860 8-23` window per suite, 1-minute
load up to 7.2 at child starts, at most three compilers running on other CCDs. The §5 RSS diagnosis is
a single unlocked run per arm on CPUs 96–111 and reports memory only. §9 (#871) was measured at
`7d0ac698` (executable SHA-256 `3d509058…`), 2026-11-17 17:15–17:32 EST, under `tools/benchlock.sh`
on CPUs 8–23, 1-minute load up to 4.7 at child starts.
**Host:** as [`m30-symbolic-cost-model.md`](m30-symbolic-cost-model.md).
**Evidence:** [`research/m30-symbolic/`](../../research/m30-symbolic/README.md) (`intern.jsonl.gz`,
`intern-seed512.jsonl.gz`, `live.jsonl.gz`, [`tables.md`](../../research/m30-symbolic/tables.md)).
**Reads:** #859's cost model ([`m30-symbolic-cost-model.md`](m30-symbolic-cost-model.md)).
**Plan:** [`MILESTONE-SIGNATURE-SYMBOLIC-F4.md`](../MILESTONE-SIGNATURE-SYMBOLIC-F4.md) §9.2, §9.4.

Quantities: symbolic-stage wall (replayed closure) and complete-F4 **process wall**, paired against
the shipping path in the same executable (`--merge off`), which is the #855 configuration.

## 1. Findings

1. **Both prototypes clear the stage target by a wide margin.** At a 16-worker team the replayed
   closure runs **2.2–2.4× faster on MQ10, 4.9–5.0× on Eco-12, 5.7–6.0× on MQ11 and 4.5–4.8× on
   Katsura-11**, against #859's needed 1.41–1.79×. #827's level-parallel prototype managed 1.17–2.01×
   on the same batches (#859 §5).
2. **Complete F4 moves by more than 10% on every substantial target.** Process wall at 16 workers,
   prototype ÷ shipping in the same executable, n = 5: **Eco-12 0.743 [0.722, 0.771] (serial merge) /
   0.738 [0.718, 0.748] (sharded), MQ11 0.806 / 0.803, Katsura-11 0.768 / 0.763, MQ10/2³¹−1 0.802 /
   0.825, MQ10/32003 0.817 / 0.827.** At 8 workers 0.79–0.87, at 4 workers 0.87–0.93. Every run's
   basis digest equals the shipping one.
3. **No one-worker regression.** At one worker the prototype is the shipping closure (no team is
   started); ratios 0.996–1.006 with every interval containing 1.
4. **Peak RSS grows 1.20–1.31× at 16 workers — over the 1.15× budget — and it is allocator arenas,
   not live data.** With `MALLOC_ARENA_MAX=1` the prototype's peak equals the shipping path's (Eco-12
   183 / 183 MiB, MQ11 360 / 360 MiB): glibc keeps the worker threads' freed scratch in per-thread
   arenas. A P3 implementation must allocate step scratch on the caller (or on the F4 pool's
   existing threads) and reuse it, and show RSS ≤1.15× as its first acceptance test. **Done in §9
   (#871): 1.00–1.13× with caller-owned scratch sized to what a step touches.**
5. **The two merges are close; the serial merge is simpler.** On the wide targets the sharded merge
   is 3–6% faster in the stage and under 1% faster in process wall; on MQ10 the serial merge is
   6–10% faster in the stage and 1–3% faster in process wall. The serial merge's walk costs 10–31 ms
   per F4 call; the sharded merge cuts that to 9–22 ms but adds four barriers per step and 16 shard
   tables, which MQ10's many small levels pay for. What is left serial in both is the caller's
   stitch (rows, leads, the handle append): 21–62 ms, about a quarter of the remaining stage on
   Eco-12 and MQ11.
6. **Recommendation: the serial canonical merge, for #861, conditional on the RSS fix (§8).**

## 2. The two prototypes

Both live in `src/grobner/f4/symbolic_intern.rs` behind `research-work`, share everything but the
merge, and return a `Preprocessed` equal to the serial closure's — rows, columns, `term_handles`,
`leading_monomials` and every counter — under both seed policies, at every worker count, slice
count and dispatch threshold, including the row-budget refusal
(`test_parallel_interning_matches_the_serial_closure`; live F4 through either one returns the
shipping basis, `test_live_interning_prototypes_leave_f4_unchanged`).

The closure runs as *steps*: the seed rows, then each breadth-first level (#859 §4: the levels are
the only algebraic dependency). Each step has four phases:

1. **Scan** (parallel, dynamic slices). Per frontier monomial: the lcm check, the divisor search, the
   multiple's terms. Each term is hashed once and looked up in the interner as it stood before the
   step; a hit becomes its handle, a miss is deduplicated in a slice-local table and becomes
   `LOCAL | id`, ids in first-occurrence order.
2. **Merge** — the only difference between the prototypes.
   - **Serial canonical merge (approach 1).** One thread walks the slices' new monomials in slice
     order, then local order, probing one table with the worker's precomputed hash. That order *is*
     the serial closure's first-occurrence order, so each new monomial receives exactly the serial
     handle (`arena.len()`) and the slice's translation array records it.
   - **Sharded merge (approach 2).** New monomials are routed by hash bits 32+ to one shard per
     worker. In parallel, each shard finds every monomial's first occurrence (its *owner*); a prefix
     sum of owners per slice gives slice bases; each slice numbers its owners `base + rank` in local
     order; each shard then records the handles it owns and resolves its repeats. The serial order
     is restored by arithmetic, with no serial walk over monomials.
3. **Emit** (parallel). Each slice rewrites its `LOCAL | id` references through its translation
   array into its run of `term_handles`.
4. **Stitch** (caller). Append rows, leads, handles and the arena; the next frontier is the arena's
   new tail, which is the serial FIFO queue's next level in order.

Worker-local ids map to final `MonomialHandle`s through one `u32` per candidate per slice: no
rewrite pass over the arena and no second allocation of the monomials.

### Dispatch

One scoped team per batch, started lazily at the first step whose width reaches `min_frontier`
(256, #827's measured best); narrower steps run on the caller alone with the team parked on a
barrier, so a closure that never widens never starts a thread. Each step is cut into 4 slices per
worker, claimed dynamically, which removes #827's static-chunk imbalance (its slowest slice ran ~3×
the mean). Barriers per dispatched step: 2 per parallel phase (3 phases serial merge, 5 sharded).
Slice buffers and local tables are reused across steps; nothing is spawned per level.

**A threshold on pair count does not work.** The first pass (`intern-seed512`, retained) started a
team only for batches with ≥512 seed rows; that sent 17 of 23 Eco-12 batches and 8 of 10 MQ10
batches down the serial path and capped the stage at 1.39× / 1.27×, because pair count does not
predict closure size (an 11-pair Eco-12 batch needs 11 137 rows, a 326-pair one 916). Starting the
team at the first wide frontier is the one adaptive threshold the plan asks for.

## 3. Stage speedup (replayed on every live batch, n = 5)

Serial closure ÷ prototype, both on the live batch, alternated per batch; ms are per F4 call
(sum over batches), median of 5 runs [min, max of the per-run ratio]. Team = workers in the
prototype; all arms run on CPUs 8–23. Full table (teams 4 / 8 / 16, phase clocks):
[tables.md](../../research/m30-symbolic/tables.md).

| Target | serial closure | serial merge, 16 | speedup | sharded, 16 | speedup | steps (dispatched) |
|---|---:|---:|---:|---:|---:|---:|
| MQ10 / 32003 | 96.3 | 41.6 | 2.33× [2.23, 2.44] | 43.9 | 2.20× [2.01, 2.28] | 121 (35) |
| MQ10 / 2³¹−1 | 96.0 | 40.1 | 2.40× [2.34, 2.46] | 44.3 | 2.19× [2.11, 2.28] | 121 (35) |
| Eco-12 | 1043.1 | 213.2 | 4.89× [4.80, 5.08] | 206.9 | 5.04× [4.92, 5.07] | 124 (59) |
| MQ11 | 1340.0 | 238.6 | 5.66× [5.42, 5.76] | 220.8 | 6.02× [5.95, 6.16] | 35 (18) |
| Katsura-11 | 456.4 | 100.7 | 4.53× [4.24, 4.62] | 95.1 | 4.81× [4.52, 4.92] | 84 (40) |

Teams of 4 / 8 reach 1.9–3.3× / 2.3–5.0×. Where the 16-worker prototype's time goes (ms, median run;
`scan` is parallel, `merge` serial for approach 1 and three parallel phases for approach 2, `emit`
parallel, `stitch` serial):

| Target | merge | spawn | scan | merge | emit | stitch |
|---|---|---:|---:|---:|---:|---:|
| MQ10 / 2³¹−1 | serial | 2.4 | 14.9 | 9.6 | 3.1 | 8.7 |
| MQ10 / 2³¹−1 | sharded | 2.3 | 18.1 | 10.7 | 2.4 | 8.5 |
| Eco-12 | serial | 5.8 | 98.5 | 30.3 | 14.1 | 60.6 |
| Eco-12 | sharded | 5.6 | 102.8 | 22.3 | 8.6 | 62.3 |
| MQ11 | serial | 3.6 | 121.1 | 30.6 | 19.0 | 61.1 |
| MQ11 | sharded | 3.4 | 123.9 | 17.3 | 12.6 | 59.8 |
| Katsura-11 | serial | 2.8 | 42.8 | 20.6 | 6.9 | 24.8 |
| Katsura-11 | sharded | 2.8 | 49.4 | 13.3 | 4.8 | 21.5 |

Shard balance: the worst dispatched step's largest shard holds 2.1–2.8× the mean on MQ10 and
Katsura-11, and up to 4.4× (Eco-12) and 9.0× (MQ11) on narrow steps late in a batch, where a few
hundred candidates spread over 16 shards; the totals above are dominated by wide steps, where it is
near 1. Duplicate discovery across slices is what the merge exists for: candidates exceed owners by
the slices' repeated first-occurrences (`candidates` / `owners` in the records).

The first pass with a 512-seed-row team threshold (`intern-seed512`, n = 5, retained): 1.19–1.30×
on MQ10, 1.30–1.39× on Eco-12, 2.19–3.01× on MQ11, 2.08–2.65× on Katsura-11 — the cost of a
threshold on the wrong quantity (§2).

## 4. Complete F4 (process wall, n = 5, same executable)

Prototype ÷ shipping (`--merge off`) at the same worker count; medians of 5, 95% bootstrap
intervals resampling each arm independently. The team size is the forward-worker budget.

| Target | workers | shipping ms | serial merge | ratio | sharded | ratio | basis |
|---|---:|---:|---:|---:|---:|---:|---|
| MQ10 / 32003 | 1 | 1152.3 | 1157.7 | 1.005 [0.999, 1.013] | | | identical |
| MQ10 / 32003 | 4 | 423.5 | 392.3 | 0.926 [0.883, 0.946] | | | identical |
| MQ10 / 32003 | 8 | 337.8 | 278.9 | 0.826 [0.821, 0.829] | | | identical |
| MQ10 / 32003 | 16 | 291.9 | 238.5 | 0.817 [0.809, 0.823] | 241.5 | 0.827 [0.821, 0.833] | identical |
| MQ10 / 2³¹−1 | 1 | 980.1 | 986.4 | 1.006 [0.992, 1.011] | | | identical |
| MQ10 / 2³¹−1 | 4 | 381.5 | 342.5 | 0.898 [0.841, 0.920] | | | identical |
| MQ10 / 2³¹−1 | 8 | 312.4 | 252.9 | 0.810 [0.806, 0.815] | | | identical |
| MQ10 / 2³¹−1 | 16 | 278.3 | 223.2 | 0.802 [0.794, 0.810] | 229.6 | 0.825 [0.814, 0.834] | identical |
| Eco-12 | 1 | 13403.2 | 13361.5 | 0.997 [0.960, 1.002] | | | identical |
| Eco-12 | 4 | 4885.8 | 4255.6 | 0.871 [0.859, 0.937] | | | identical |
| Eco-12 | 8 | 3806.1 | 3002.3 | 0.789 [0.773, 0.794] | | | identical |
| Eco-12 | 16 | 3140.1 | 2333.0 | **0.743** [0.722, 0.771] | 2317.7 | **0.738** [0.718, 0.748] | identical |
| MQ11 | 1 | 39887.2 | 39802.8 | 0.998 [0.992, 1.009] | | | identical |
| MQ11 | 4 | 12134.1 | 11213.8 | 0.924 [0.921, 0.934] | | | identical |
| MQ11 | 8 | 8160.6 | 7094.9 | 0.869 [0.863, 0.872] | | | identical |
| MQ11 | 16 | 5701.8 | 4595.5 | **0.806** [0.802, 0.807] | 4576.4 | **0.803** [0.798, 0.804] | identical |
| Katsura-11 | 1 | 7178.6 | 7152.8 | 0.996 [0.983, 1.002] | | | identical |
| Katsura-11 | 4 | 2426.0 | 2155.4 | 0.888 [0.876, 0.918] | | | identical |
| Katsura-11 | 8 | 1820.6 | 1493.0 | 0.820 [0.818, 0.822] | | | identical |
| Katsura-11 | 16 | 1455.1 | 1117.4 | **0.768** [0.759, 0.770] | 1110.1 | **0.763** [0.755, 0.767] | identical |

The shipping arm reproduces #859's non-`research-work` walls within 1% at 16 workers (Eco-12
3140 vs 3119 ms, MQ11 5702 vs 5747 ms), so the `research-work` build is a fair control. The
measured saving matches #859's Amdahl prediction: Eco-12's *f*<sub>wall</sub> = 0.317 and a 4.9×
stage give 0.317 × (1 − 1/4.9) = −25%, measured −26%; MQ11's 0.227 and 5.7× give −19%, measured
−19%.

## 5. Memory

Peak RSS, median of 5, from the same `live` runs (MiB):

| Target | shipping 16w | serial merge | ratio | sharded | ratio | at 1 worker |
|---|---:|---:|---:|---:|---:|---:|
| MQ10 / 32003 | 40 | 50 | 1.24 | 53 | 1.31 | 1.00 |
| MQ10 / 2³¹−1 | 42 | 50 | 1.21 | 54 | 1.28 | 1.00 |
| Eco-12 | 200 | 254 | 1.27 | 257 | 1.29 | 1.00 |
| MQ11 | 393 | 499 | 1.27 | 501 | 1.28 | 0.99 |
| Katsura-11 | 144 | 172 | 1.20 | 184 | 1.28 | 1.00 |

**Diagnosis (memory only, one unlocked run per arm on CPUs 96–111):** with `MALLOC_ARENA_MAX=1`
Eco-12 peaks at 183 MiB shipping and 183 MiB serial merge; MQ11 at 360 / 360 / 361 MiB (shipping /
serial / sharded). With one arena the prototype's live data adds nothing measurable; the default
allocator's growth comes from worker threads allocating step scratch — per-slice reference arrays
(4 B per term), candidate lists and local tables — in their own arenas, which glibc retains after
the batch. The sharded merge's extra 2–4 points are its shard tables. A single arena is not the fix
(it slowed the shipping path by 7% on Eco-12 in the same probe); caller-owned, reused scratch is.

## 6. Invariants and what P3 would have to keep

| Invariant | Depends on handle order? | Notes |
|---|---|---|
| `Preprocessed::term_handles` | yes, as an index into `monomials` | Both prototypes reproduce it exactly. A stable remap would also do, provided `monomials` is permuted with it. |
| Matrix column order | **no** | `build_measured` sorts `(monomial, handle)` pairs by monomial; `column_of` absorbs any numbering. |
| Reducer selection | no | A function of the monomial and the basis. |
| Row order | reducer rows: no; pair rows: yes | `partition_reducers_first` sorts reducers by leading column; pair rows keep pair order, which both prototypes keep (seeds are not reordered). |
| Closure order / levels | the *set* only | Least fixed point; levels are the critical path. |
| Basis output | no | Identical basis digests in every `live` run (§4). |
| Row budget | no | Checked after each step; refuses exactly when the serial closure does (tested). |
| Cancellation | — | Not wired: the prototypes are unbudgeted for wall time. A step is the natural cancellation point; partial work is slice-local and discarded with the `Step`. |
| Live-entry budget | — | Unchanged: the matrix is built from an identical `Preprocessed`. The prototypes' own scratch (per-slice references, 4 B per term; candidates and local tables) is not counted against `max_live_nonzeros` and would need to be for P3. |

Exact handle identity is therefore **not** required by anything downstream; it is kept here only so
equality can be tested with `==`; a design that numbers handles differently and remaps them is equally valid.

## 7. Dispatch overhead (the 0.64× one-worker cost of #827)

#827's 0.64× one-worker cost came from running the level machinery on one thread. Here a team
of one never runs the machinery: `workers ≤ 1` takes the shipping closure directly, and §4's
one-worker ratios are 0.996–1.006. With a team, the costs #827 named are gone or measured:

- **Per-level spawns → one lazy team per batch.** Spawning costs 2.3–5.8 ms per F4 call at 16
  workers (0.2–0.3 ms per batch).
- **Coarser, balanced tasks.** 4 dynamic slices per worker per step instead of one static chunk.
- **Scratch reuse.** Slice buffers and local tables persist across a batch's steps.
- **Fewer barriers.** 2 per parallel phase; narrow steps (below 256 monomials) run on the caller
  with no barrier at all: 35 of 121 MQ10 steps and 59 of 124 Eco-12 steps dispatch.
- **Serial path for small closures** chosen by the frontier, not the batch's pair count (§2).

Not tried: reusing `linalg::concurrent` or the forward pool's threads. Neither exposes a persistent
team a caller can hand phases to; a scoped team per batch was the smallest thing that measured.
Reusing the forward pool's threads is, however, the likely RSS fix (§5) and belongs to P3.

## 8. Recommendation for #861

**P2 → P3 gate (plan §9.4), read against these measurements:**

| Criterion | Result |
|---|---|
| ≥2× symbolic stage at 16 workers on a substantial target | **met**: 4.9× Eco-12, 5.7× MQ11 (serial merge) |
| ≥10% complete F4 process wall on a substantial public benchmark | **met**: −25.7% Eco-12 [−27.8, −22.9], −19.4% MQ11 |
| improvement on a held-out instance | **met**: Katsura-11 −23.2% [−24.1, −23.0] (not an M29 target; #827's instance) |
| ≤5% regression at one worker / on small tasks | **met at one worker** (ratios ≤1.006); small tasks below MQ10 not measured — the lazy team never starts on a closure without a 256-wide level |
| peak RSS ≤1.15× | **not met**: 1.20–1.27× (serial merge), 1.28–1.31× (sharded); diagnosed as allocator arenas (§5) |
| identical deterministic output | **met**: equality tests at 1/2/5/16 workers, every `live` basis identical |
| budget and cancellation | row budget **met** (tested); wall-time cancellation not wired |

Recommended design for #861: **the serial canonical merge**, with the lazy per-batch team and the
frontier threshold of this prototype. It is the simpler of the two (no shard tables, two barrier
pairs fewer per step), it is ahead on MQ10 and within 1% of process wall on the wide targets, and its RSS excess is
the smaller. Before any production work P3 must (1) move step scratch to caller-owned buffers
reused across batches or run the team on the F4 worker pool, and show peak RSS ≤1.15×; (2) add wall
cancellation at step boundaries and account scratch in the live-entry budget; (3) measure small
tasks (Katsura-6/7, cyclic-6) for the ≤5% criterion. Next serial targets after that are the
stitch (rows, leads and the handle append: 21–62 ms) and the merge walk (10–31 ms).

## 9. Caller-owned scratch and the RSS gate (#871, 2026-11-17, `7d0ac698`)

**Result: peak RSS is at most 1.13× shipping at 16 workers on every target, and the process-wall
savings are unchanged.** Same `live` method as §4 and §5: shipping (`--merge off`) and the serial
merge in one executable, n = 5 per arm, paired by repetition and interleaved with rotated arm order
(`scratch` suite, [`tables.md`](../../research/m30-symbolic/tables.md), `scratch.jsonl.gz`). Every
run's basis digest equals the shipping one.

| Target | shipping RSS 16w | serial merge | RSS ratio, paired [min, max] | §5 ratio | wall ratio [95% CI] | §4 ratio | 1 worker: wall / RSS |
|---|---:|---:|---:|---:|---:|---:|---:|
| MQ10 / 32003 | 40 MiB | 46 MiB | **1.130** [1.121, 1.137] | 1.24 | 0.819 [0.814, 0.827] | 0.817 | 0.997 / 1.003 |
| MQ10 / 2³¹−1 | 42 MiB | 47 MiB | **1.125** [1.117, 1.134] | 1.21 | 0.811 [0.801, 0.817] | 0.802 | 1.002 / 1.005 |
| Eco-12 | 200 MiB | 200 MiB | **1.002** [1.001, 1.006] | 1.27 | 0.740 [0.734, 0.744] | 0.743 | 1.000 / 1.001 |
| MQ11 | 393 MiB | 393 MiB | **1.000** [0.998, 1.002] | 1.27 | 0.800 [0.786, 0.803] | 0.806 | 1.004 / 0.991 |
| Katsura-11 | 144 MiB | 144 MiB | **0.998** [0.993, 1.006] | 1.20 | 0.767 [0.764, 0.792] | 0.768 | 0.998 / 1.001 |

Process-wall savings at 16 workers are Eco-12 −26.0%, MQ11 −20.0% and Katsura-11 −23.3%, against
§4's −25.7%, −19.4% and −23.2%. Each interval contains the §4 figure, so the difference is noise.

**What the fix is, and what it is not.** The issue proposed allocating the scratch once per F4 run
and clearing it instead of freeing it. That alone made peak RSS worse. The `serialrun` arm keeps
the buffers for the whole run (`--retain run`) and measures 1.16–1.25×; an earlier unlocked probe
with the #860 data layout read 1.50× on Eco-12. Instrumenting RSS at the close of each batch showed
why. On Katsura-11 the process high-water mark is set *inside the symbolic stage* of the widest
batch, not in its matrix. Any scratch still resident at that moment adds to the peak, and that
includes scratch held over from earlier batches. The arena diagnosis of §5 holds: with
`MALLOC_ARENA_MAX=1` the excess shrank but did not vanish once the scratch was no longer freed into
worker arenas. But arenas were only part of the cause. The rest was the size of the scratch itself.
Three changes closed the gap, each measured unlocked before the campaign:

1. **Workers never allocate.** Every buffer a scan writes is caller-allocated. A scan that would
   outgrow a buffer stops and records which buffer and how far it got. The caller grows that buffer
   by extrapolating from the scan's progress, then rescans the slice. Buffers are freed after each
   batch, on the caller, where the batch's matrix reuses the memory. Their capacities carry over as
   hints, so a later batch allocates what it needs up front (`Retain::Batch`, the default). Rescans
   happen while the scratch warms up, about 670–850 per F4 call. They are included in the walls
   above.
2. **Candidates name a position, not a monomial.** A pre-step miss is stored as (hash, row, term)
   in 16 bytes. Before, it was the hash plus the monomial: 56 bytes at twelve variables. The
   monomial is recomputed (a shift of one basis term) when the merge or a local probe needs it. The
   candidate list was the largest buffer, at 35 MiB of capacity on Eco-12.
3. **Both deduplication tables hold 8-byte ids.** A hash table's inserts land across its whole
   bucket array, so its full size is resident however few entries it holds. The per-slice
   `HashMap<Keyed, u32>` (64 bytes an entry, 63 MiB on Eco-12) became an open-addressing table of
   `tag | id` slots. It starts each step small and doubles in place within the caller's capacity.
   The serial merge's interner uses the same structure over the column arena. That took MQ10 from
   1.15× to 1.13×; the per-batch `HashMap<Keyed, u32>` was what kept MQ10 over budget.

The bound is `research-work`-only and applies to the serial merge. The sharded merge's shard tables
are still grown by its workers, so its RSS is not covered here. §8 already recommends the serial
merge for #861.

**Scratch-reuse invariant.** `test_interning_scratch_is_not_reallocated_after_warm_up` runs every
cyclic-6 batch twice through one `InternScratch`, under both merges and both retentions. On the
second pass no buffer grows, no slice is rescanned and no capacity changes, and every batch equals
the serial closure. The existing exact-equality tests (`test_parallel_interning_matches_the_serial_closure`,
`test_live_interning_prototypes_leave_f4_unchanged`) pass unchanged.

### Gate (plan §9.4) re-read

| Criterion | Status after #871 |
|---|---|
| ≥2× symbolic stage | met (§3; the scan is unchanged in kind) |
| ≥10% complete F4 process wall | **met**: Eco-12 −26.0%, MQ11 −20.0% |
| held-out instance | **met**: Katsura-11 −23.3% |
| ≤5% regression at one worker / small tasks | **met at one worker** (wall 0.997–1.004, RSS 0.991–1.005); small tasks below MQ10 are still unmeasured (precondition 3) |
| peak RSS ≤1.15× | **met**: 1.000–1.130× (serial merge, paired medians; worst single repetition 1.137×) |
| identical deterministic output | met: every run identical |
| budget and cancellation | row budget met; scratch charged to `max_live_nonzeros` and wall-time cancellation are #872 |

## 10. Live-entry budget and cancellation (#872, 2026-11-17)

No timing or memory figures; behaviour only.

- **Budget.** The parallel closure charges its step scratch to the configured live-entry allowance
  (`F4Options::live_entry_allowance`, entries of `F`), measured by capacity in bytes and rounded up
  to whole entries. The charge is taken before every scan and after every growth, so a step whose
  scratch would not fit is refused before it runs, with the same error a matrix over the budget
  gets (`TooManyNonzeros` or `TooManyLiveBytes`, whichever budget binds). Nothing is charged after
  the call returns. Under the default `Retain::Batch` the scratch is freed before the batch's
  matrix is built and never coexists with it, so the scratch is charged on its own, not added to
  the matrix peak. A budget between the shipping peak and the shipping peak plus the scratch
  therefore trips the parallel path exactly when the scratch alone exceeds it. The live test
  chooses a fixture where it does.
- **Cancellation.** Two stops are checked at every step boundary, before a step's scan: the
  observer's `should_stop` and `max_wall_time`. The wall-time check uses the batch loop's own
  clock, armed under the loop's rule that one batch is always reduced. A stop requested before a
  step returns after exactly the steps before it, with no partial result. The serial closure has
  no stop inside the symbolic stage; it is checked between batches and after construction.

| Criterion (plan §9.4) | Status after #872 |
|---|---|
| budget and cancellation | row budget, live-entry budget and step-boundary stops tested (`test_parallel_interning_charges_its_scratch_to_the_live_entry_budget`, `test_live_interning_trips_a_live_budget_the_shipping_path_meets`, `test_parallel_interning_stops_at_a_step_boundary`, `test_live_interning_honors_an_observer_stop_at_the_first_step`) |
