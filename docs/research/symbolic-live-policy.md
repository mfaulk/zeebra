# Live symbolic ordering and exact pair-multiple deduplication (#753)

**Measured at:** binary build `d8a322888fdc6837c32fc8c24f7ce5385ee3c849`; initial controller
`bd7b7764`, continuation controller `6c5de01f` (repair implementation `29e17521`). Later publication
changes only analysis, documentation and retained data. The sole Rust source delta from the build
is the verbatim two-line `cfg(test)` initializer correction pinned in the manifest; no measured
production code changes. [Build/provenance metadata](../../research/symbolic-live/build-metadata.json).
**Production baseline:** candidate-only serial backward reduction from #749, present in audited
`b9898c9a`; shared forward/backward stage refinements are the #751 timer-only prerequisite.
**Decision:** retain the bounded research policy and **defer production adoption**. Ordinary F4
defaults are unchanged; the complete small-control regression gate is not established.

## Controlled change and correctness

The experiment has two independent Boolean factors. Initial ordering changes only the
first-applicable reducer search: stably sort the normalized, distinct initial generator prefix
by increasing leading monomial under the actual order, then leave every appended element in
insertion order. It does not reorder basis storage, pair indices, pair seeds or public
normal-form divisors. F4 freezes the actual initial size after removing zero/proportional
inputs, rather than trusting the caller's possibly larger input length.

Deduplication retains one pair seed per exact `(basis_index, multiplier)` key. The basis stores
monic coefficients, so equal keys denote identical polynomial multiples including every tail
coefficient. A repeated row supplies no additional vector to the seed span. Every original pair's
two halves therefore remain represented, and their difference still lies in that span even when
the retained row's origin names an earlier pair. Equal leading monomials alone never imply equal
keys; distinct basis indices, including proportional original generators in a direct symbolic
call, remain distinct. F4's usual initial normalization separately removes duplicate monic inputs.

Every pair LCM is still inserted into the covered-leading set, even if a seed was retained earlier.
Removing duplicate offers cannot change the first occurrence of any support monomial. With fixed
reducer order, the same symbolic closure columns and covered leads are obtained; exact direct
fixtures assert those equalities. Changing reducer search can legitimately change closure and
subsequent work. Each newly introduced reducer multiple belongs to the original ideal, while
coverage supplies every needed reduction column. Neither factor weakens the selected-candidate
output contract or final reduced-basis verification. Final matrix interreduction always keeps its
ordinary policy; scope does not rewrite its reducer order.

Row admission checks remain at the existing push sites, on the actual retained seed/closure rows.
An unchanged allowance can admit a smaller matrix; it is not a raised budget. Matrix entry/byte
limits and candidate-pass reservations retain their existing definitions. The new seed-key table
and index permutation require extra temporary storage; their capacities are reported separately
and process RSS is measured. Capacities are logical entries, not allocator bytes or hardware
traffic. Ordering under non-first-applicable selection or a divmask replay is explicitly refused
rather than silently miscounted. Field operations remain generic.

## Protocol and retained evidence

The [predeclared plan](../../research/symbolic-live/README.md) defines one 2×2 campaign, numerical
adoption/regression/RSS gates, strict compiler/load gates and aggregate resources. Feature-absent
stock, feature-present/scope-off and active-original controls isolate feature/scope perturbation.
Every complete answer is compared coefficient-for-coefficient to the independently Singular-checked
reference for its exact field, ordered original generators and input digest. This study reuses
those retained independent answers; it does not relabel a new unverified reference as an oracle.
Verification runs outside the timed process. Mathematical reduced bases, not dimension/rank/leading
terms alone, are the comparison boundary.

Five interleaved fresh-process timing repetitions per arm are separate from one deterministic
work diagnostic per policy/cell. Five MQ10 repetitions disable stage clocks to expose observer
perturbation. No worker, backward, arithmetic or field-representation factor is bundled into the
symbolic factors. Complete F4 includes final interreduction; process wall/CPU includes input,
answer formatting and full JSON output. Self high-water before final serialization and sampled
process-tree RSS are retained separately; their maximum is reported rather than subtracting peaks.

The scope is thread-local and restores an outer scope even after panic. Symbolic preprocessing
runs on the solver thread; this study makes no worker-propagation or production parallel policy
claim. Explicit work observers remain separate from native timing.

## Results and decision

The completed [cohort](../../research/symbolic-live/results.json.gz) retains **346 exact-verified answers**:
270 native, 36 work diagnostics and 40 clocks-off controls. One earlier protocol rejection was
adjudicated from its unchanged response using exact existing polynomial normalization; no solver
was rerun. One pre-child compiler hold preserved the exact prefix. Cumulative measured/controller
active time through attempt publication was 251.354 seconds; complete lock windows including final
offline validation total 319 seconds (20 + 9 + 290), below the 900-second budget. Scratch used
125.4 MiB below 512 MiB. Every solver child stayed below 60 seconds/2 GiB, with no executed
failure, resource refusal or compiler-contaminated child accepted.

Machine: Threadripper PRO 5995WX, one worker pinned to CPU 4, rustc 1.99.1, release/fat LTO/one
codegen unit/x86-64-v3, mold and system allocator. Actual topology, environment/configuration,
Cargo fingerprints and executable hashes are retained, rather than inferred from the build label.
[The lock log](../../research/symbolic-live/benchlock.log) records all three nonoverlapping windows;
start/end loads were 1.23/1.40, 2.26/2.24 and 3.17/1.42. Unrelated compilation occurred between
windows and caused the pre-child hold. Paused time is not silently included in solver timings.

### Complete MQ10 timing and observer controls

Five-run medians with [min,max], milliseconds. RSS is the maximum accepted observed/self process
high-water across the five runs, not a matrix-entry model. No historical cohort is a denominator.

| Prime | Arm | Complete F4 ms [min,max] | Process wall ms [min,max] | Max RSS MiB |
|---:|---|---:|---:|---:|
| 32003 | stock | 1247.908 [1222.005,1257.550] | 1276.944 [1250.832,1287.013] | 35.82 |
| 32003 | feature-off | 1314.973 [1310.054,1358.693] | 1344.760 [1338.203,1390.116] | 36.98 |
| 32003 | original | 1315.385 [1310.090,1359.212] | 1345.263 [1339.975,1388.647] | 36.75 |
| 32003 | order | 1229.802 [1217.324,1300.934] | 1260.557 [1244.669,1332.812] | 34.88 |
| 32003 | dedup | 1202.921 [1179.344,1343.425] | 1234.497 [1208.092,1374.799] | 36.44 |
| 32003 | both | 1101.866 [1094.950,1246.119] | 1130.717 [1123.679,1278.484] | 34.43 |
| 2147483647 | stock | 1344.435 [1335.488,1490.413] | 1376.001 [1365.069,1524.585] | 36.96 |
| 2147483647 | feature-off | 1414.435 [1400.831,1534.527] | 1444.445 [1431.519,1568.807] | 37.66 |
| 2147483647 | original | 1452.217 [1416.195,1532.478] | 1482.250 [1447.055,1562.676] | 37.41 |
| 2147483647 | order | 1328.260 [1310.130,1365.470] | 1358.636 [1340.587,1397.922] | 35.65 |
| 2147483647 | dedup | 1282.042 [1267.821,1329.856] | 1311.760 [1298.541,1360.514] | 37.18 |
| 2147483647 | both | 1193.172 [1175.429,1211.639] | 1222.339 [1205.558,1242.532] | 35.21 |

The combined arm reduces complete-F4 medians by 11.70%/11.25% and process medians by
11.45%/11.17% versus feature-absent stock. The GF(32003) process ranges overlap:
combined max 1278.484 ms versus stock min 1250.832 ms. At Mersenne-31 the combined maximum
1242.532 ms is below the stock minimum 1365.069 ms. These are named reduced-basis results,
not confidence intervals, a whole-solving gain or a universal field-width claim.

Feature-present/scope-off costs about 5.37%/5.21% more F4 median than stock; active original
adds 0.03%/2.67% versus scope-off. Those are observed build/scope perturbations, not avoided
algebraic work. The policy comparison must therefore also use its same-binary active-original
control. The following observations pair each arm with the original in the same repetition;
they do not divide unrelated aggregate medians. Negative reductions would mean regression.

| Prime | Policy | Paired F4 reduction median [min,max] |
|---:|---|---:|
| 32003 | order | 6.36% [4.29,7.35] |
| 32003 | dedup | 8.30% [1.16,9.98] |
| 32003 | both | 16.27% [8.32,16.77] |
| 2147483647 | order | 9.28% [5.04,10.90] |
| 2147483647 | dedup | 11.72% [8.79,13.22] |
| 2147483647 | both | 17.84% [16.60,20.94] |

Clocks-off F4 original→combined medians are 1335.095→1156.136 ms and
1446.447→1226.335 ms. The sign survives disabling stage clocks. Those controls use the
scoped binary, not a missing feature-absent clocks-off arm; they cannot erase the measured
feature-present overhead. Work-on diagnostics are separate single observations, not timing repeats.

### Native stage attribution and logical work

Native stage medians below are milliseconds. Forward/backward refine elimination and are not
added to its inclusive total twice; medians of individual stages need not sum to the median call.

| Prime | Policy | Symbolic | Construction | Forward | Backward | Extraction | Final interreduction |
|---:|---|---:|---:|---:|---:|---:|---:|
| 32003 | original | 86.073 | 17.968 | 1134.192 | 44.586 | 8.523 | 12.983 |
| 32003 | order | 83.726 | 16.650 | 1050.372 | 43.079 | 8.417 | 13.095 |
| 32003 | dedup | 86.566 | 17.544 | 1019.603 | 46.530 | 8.730 | 13.342 |
| 32003 | both | 79.332 | 16.586 | 928.030 | 42.850 | 8.362 | 12.704 |
| 2147483647 | original | 88.111 | 18.757 | 1257.714 | 50.808 | 8.349 | 13.071 |
| 2147483647 | order | 84.169 | 17.108 | 1146.478 | 47.497 | 8.398 | 12.819 |
| 2147483647 | dedup | 87.206 | 18.151 | 1091.040 | 51.232 | 8.601 | 12.917 |
| 2147483647 | both | 80.694 | 16.667 | 1009.984 | 47.883 | 8.394 | 12.925 |

The deterministic work diagnostics retain actual batch trajectories, scans, loads, gathers,
applications, peak entries, sparse capacities and candidate reservations. The table sums as-built
batch dimensions/entries and actual products; it is not physical memory bandwidth or allocation
counts. Final interreduction is charged above and separately observed outside batch counters.

| Prime | Policy | Sum rows / columns | As-built entries | Forward products | Backward products |
|---:|---|---:|---:|---:|---:|
| 32003 | original | 52,779 / 53,686 | 2,622,503 | 585,166,982 | 23,566,622 |
| 32003 | order | 45,221 / 46,128 | 2,556,652 | 549,231,661 | 22,945,638 |
| 32003 | dedup | 52,440 / 53,686 | 2,523,210 | 518,277,638 | 23,566,622 |
| 32003 | both | 44,882 / 46,128 | 2,457,359 | 486,416,830 | 22,945,638 |
| 2147483647 | original | 52,779 / 53,686 | 2,622,520 | 585,195,178 | 23,567,093 |
| 2147483647 | order | 45,221 / 46,128 | 2,556,669 | 549,254,798 | 22,946,054 |
| 2147483647 | dedup | 52,440 / 53,686 | 2,523,227 | 518,303,495 | 23,567,093 |
| 2147483647 | both | 44,882 / 46,128 | 2,457,376 | 486,438,478 | 22,946,054 |

The live combined GF(32003) trajectory reproduces the frozen replay's 486,416,830 forward
products exactly; this experiment now verifies the complete live answer rather than assuming
the replay trajectory survives. Ten MQ batches offer 3554 pair seeds; dedup retains 3215, removing
339 exact identities. The peak seed-table capacity is 1792 keys; ordering retains a 260-index
permutation at its maximum. These containers are temporary and their construction is timed.
They do not change the arithmetic or turn modeled capacities into RSS. All complete MQ answers
have the independent reference's 247 reduced basis elements; pair/degree and matrix trajectories
for every public control remain in the raw work responses.

### Public controls and the adoption gate

Five-run native F4 medians [min,max] in milliseconds. Process-wall and RSS ratios compare
combined to feature-absent stock; the raw data retain all four policies and scope controls.

| Control / prime | Stock F4 ms [min,max] | Combined F4 ms [min,max] | Process median ratio | Max RSS ratio |
|---|---:|---:|---:|---:|
| cyclic-5 / 32003 | 0.609 [0.588,0.943] | 0.968 [0.640,1.012] | 0.975 | 1.063 |
| cyclic-5 / 2147483647 | 0.629 [0.621,0.637] | 1.014 [0.650,1.035] | 1.006 | 1.038 |
| katsura-6 / 32003 | 1.099 [1.028,1.178] | 1.089 [1.079,1.238] | 0.992 | 1.070 |
| katsura-6 / 2147483647 | 1.095 [1.087,1.121] | 1.100 [1.070,1.128] | 0.992 | 1.071 |
| public-eco-4 / 32003 | 0.084 [0.078,0.092] | 0.102 [0.088,0.127] | 0.986 | 1.099 |
| public-noon-3 / 32003 | 0.142 [0.128,0.146] | 0.142 [0.129,0.180] | 0.991 | 1.079 |
| public-reimer-3 / 32003 | 0.178 [0.158,0.200] | 0.197 [0.178,0.213] | 0.956 | 1.108 |

Cyclic-5 F4 medians regress about 59%/61% (roughly 0.36–0.38 ms), while process startup and
supervision largely hide that change in process-wall ratios. Public Eco/Reimer also show
above-5% relative F4 medians at tens-of-microseconds absolute differences. Many ranges overlap;
these sub-two-millisecond cases do not establish precise 5% ordering. Conversely, overlap does
not prove the no-more-than-5% regression gate passed. No threshold is silently relaxed after
measurement. The 1.25× maximum-RSS gate passes on these named cells, but the full control gate
remains unresolved/adverse. No larger fixed-budget completion is claimed.

**Retain the opt-in combined policy; defer production adoption.** Initial ordering or dedup alone
does not clear the named 10% complete-task stock gate here. The combined median gain and exact
work reduction justify retaining this research implementation, but its noisy GF(32003) range,
feature/scope perturbation, small-control regressions and incomplete repeated whole-route baseline
#751 prevent a shipping recommendation. No new campaign is launched: this closes the one bounded
pilot at a scoped decision. Reopening needs a current whole-route baseline, a measured small-case
selection/fallback rule, above-noise public controls and the same exact-answer/resource gates.
Parallel-forward/backward interactions belong to their separate owners and are not inferred by
multiplying independent gains.

### Interrupted validation and audit trail

The initial controller accepted 36 responses then rejected the exit-0 public Eco stock response
because its reference prints negative residues (e.g. −3) while Zeebra prints 32000. The
[original archive](../../research/symbolic-live/pre-repair-results.json.gz) and
[repair audit](../../research/symbolic-live/repair-audit.json) preserve the complete original failed
attempt, failure text, stdout/raw hashes and both controller commits. The existing wide-corpus
exact polynomial normalizer over the bound field/order/variables proves every coefficient equal;
canonical reference/response hashes agree. Tests reject changed coefficients, missing/duplicate
rows and genuine exit/compiler failures. The unchanged response was adjudicated, not rerun or
discarded. A subsequent pre-child compiler hold executed no new child. Ordinary continuation
then appended exactly the remaining 309 cells, retaining its refusal marker. The final cohort
contains the audit and all environmental/resumption metadata. This repair changes verification
outside child timing only; both frozen executables and every timed response remain unchanged.


## Validation and limits

Behavior tests were written first and failed because the research API was absent, then passed
with the implementation. Tests cover exact duplicate seeds, equal leads with distinct identities,
covered leads/columns, exact row refusal, empty batches, unwind/reuse, preservation of the appended
search suffix, and the normalized initial prefix while later basis elements are added. Every 2×2
policy is checked against independent Buchberger output over lex/grlex/grevlex plus weighted and
block orders, with GF(2), GF(2^8), GF(13), GF(32003), Mersenne-31, a 64-bit prime and BN254. Zero
and proportional inputs are included. This proves tested behavior, not broad performance at all
field widths. Existing mq10 profile controls and the stage-refinement aggregation regression pass.

Runner tests preceded its implementation and cover the complete interleaved plan, policy/path
metadata, exact full outputs and refusal of incomplete plans. Later Red–Green tests cover signed
residue adjudication, strict prefix continuation and exact paired repetition matching. Offline replay rechecks every
retained answer, repetition/phase coverage, native clock boundaries, per-policy trajectory
agreement across observation modes, process resources, payload hashes and pinned reference data.
README paths/commands, changed source comments and existing CI hooks are reviewed at publication.

Production adoption also depends on the separately current whole-route baseline #751. No
complete-solving or wide-field speedup can be inferred from this reduced-basis experiment.


## Acceptance disposition and reproduction

| #753 requirement | Disposition |
|---|---|
| Live 2×2, correctness/covered leads, generic fallbacks | Implemented only under research scope; six behavior tests and exact complete answers |
| MQ plus Katsura/Cyclic/Eco/Noonburg/Reimer | All nine field/input cells completed; exact identities/reference hashes in manifest |
| Five native repeats, independent answers, diagnostics/overhead | 346 retained attempts; separate feature/scope/work/clocks-off boundaries |
| Costs and resource refusals | All stages, logical products/trajectory/capacity and RSS retained; no resource-refused child; extra scratch explicit |
| Adoption/regression/RSS gate | Named combined median gain and RSS pass; small-control/default gate unresolved/adverse, so defer production |
| Publication/tests/README/CI | Source/build/controller pins, raw outputs, repair/interruption evidence and deterministic paired summaries retained |

Run the two offline checks from the [reproduction guide](../../research/symbolic-live/README.md):

```sh
python3 tools/test/symbolic-live-study-test.py
python3 tools/external/symbolic-live-study.py --replay research/symbolic-live
```

The replay launches no solver, validates the full coefficient answers and regenerates every
reported native stage/paired timing group. Publication adds only derived `stages_ms`/`paired`
analysis fields to the original controller summary schema; all underlying responses, times and
counters are unchanged. The original buildcache summary intentionally lacks these fields. Production policy remains unchanged. The current-main
publication merge includes #760/#761 documentation/CI only; the measured Rust source remains the
frozen build plus the verbatim test-only fixture correction. Shared #751 timer changes are an
explicit prerequisite, not attributed to the symbolic policy.
