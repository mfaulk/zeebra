# Passive grobx work counters for #713

This directory belongs to the parent **GPL-3.0-only** driver workspace. The recipe applies
original passive instrumentation to a private copy of upstream commit
`1854835dbc25f24dc9a9ba017024d5030e99da1c`; it never changes the normal driver or installs a
replacement into the external-engine prefix. No upstream solver implementation is copied into
the MIT crate.

Build before acquiring the benchmark lock, using a new private target:

```sh
python3 tools/external/grobx-driver/research/test_instrument.py
python3 tools/external/grobx-driver/research/provision.py \
  --source /path/to/local/grobx/git-checkout \
  --target /buildcache/cargo-target/zeebra-713-grobx --test
```

The checkout only supplies `git archive` at the exact pin; working-tree edits are not consumed.
The script checks hashes of every modified source file, then applies guarded anchors. It refuses
an existing `source` or `driver` directory and a target outside `/buildcache`. Rust/toolchain,
release/fat LTO/one codegen unit, `x86-64-v3`, upstream allocator and dependency versions follow the
normal driver. Offline dependency resolution removes git identities only for the two copied local
packages; no version upgrade is requested. The copied `Cargo.lock` is retained in the private
`driver` directory. The optional upstream unit-test command uses its separate locked workspace
and may fetch missing registry metadata for unrelated upstream workspace members; it does not
upgrade dependency versions. Build metadata includes a SHA-256 manifest of the changed upstream files and
instrumentation recipes. Each solve also returns that `research_identity`; normal adapter
admission is not used for this experimental binary.

Executable: `/buildcache/cargo-target/zeebra-713-grobx/build/release/grobx-driver`.
Requests retain the normal driver contract and add `research_work: true` to enable counters.
Omitted/false leaves `work: null` in the **same binary**. Compare stock, patched/off and patched/on
with original requests, unchanged seed zero, report enabled, no cofactors and no trace listener.
The observer never changes pivot order, field arithmetic, signature/handover choices, scans,
bands, random draws or resource limits. Capture adds CPU/allocation overhead, which must be
measured rather than presumed free. Enabled instrumentation currently refuses characteristics
at or above `2^31` because its field-kernel counters cover `Gf31` only.

`work` contains an ordered `matrices` array: zero-based `index`, rows/given/columns/initial entries,
forward/backsub/combination counters, and row-boundary capacity snapshots. Match this ordinal and
dimensions to ordered engine reports, including abandoned signature runs and final interreduction;
do not use final `Stats` alone. `outside_matrix` retains calls before/after matrix reduction.
Stopped matrices are marked `partial` when still active.

| Counter | Meaning |
|---|---|
| `row_kernel_calls` | Calls to Gf31 sparse scalar, four-lane or single-band-lane update kernels; includes combination construction. |
| `executed_lane_products` | Sparse support length times physically executed lanes; a four-lane SIMD update counts all four, including zero multipliers. |
| `nonzero_multiplier_products` | Same support weighted by nonzero multipliers; useful for separating redundant SIMD lanes. |
| `source_entries_read` | One source support traversal per kernel call, before lane weighting; logical source reads, not cache/DRAM measurements. |
| `loaded_entries` | Sparse entries scattered into dense or band accumulators. |
| `dense_take_calls` | Calls reading/resetting a dense scalar cell, including zero cells and all band lanes. |
| `direct_field_mul_calls` | Gf31 scalar `mul` calls outside the sparse update kernel, such as normalization and band relations. |
| `subtraction_budget_calls` | Calls spending subtracted entries; a band call can account for several target rows. |
| `subtracted_entry_charges` | Existing upstream budget charges, including implicit leading entries. |

The `combination` phase covers building combinations; reducing them is forward work.
Backsub only covers the explicit made-row pass, not input-echelon reduction or final basis
interreduction as a separate objective. The final interreduction has its own matrix record.

`at_capacity_peak` is one simultaneous **accounted** snapshot, not a sum of independently attained
peaks. Original column capacities cost four bytes each, with source coefficients shared from the
basis and excluded here. Made rows use separate column/coefficient vectors. Workspace capacities
include dense/band arrays, row-building vectors and marks. Transient row copies are separate.
`peak_stored_sparse_entries` counts stored lengths, including stale scratch; it is not a live
mathematical-nonzero count. Snapshots are at reducer construction, row-copy/keep boundaries and
return, so these are **row-boundary lower bounds** on accounted allocated-capacity/stored-entry high waters, not resident memory. Band/final-interreduction result collections held outside the reducer,
basis/shared coefficients, monomial tables, row
headers, pivot maps, allocator overhead and input-echelon sparse merges are excluded. Reserved
capacity is not RSS; in particular upstream's large virtual column reservation is often much
larger than resident pages. #268 owns fuller allocation attribution.

Tests cover fail-closed source guards, exact scalar/four-lane product counts, disabled collection,
and simultaneous role accounting. The ordinary driver tests still cover input binding, exact
checking and resource stops. These are correctness checks, not performance measurements.

## Independent randomization controls (#714)

Add `--randomization` to the provisioner for the isolated feature-ablation driver. Its pinned
[overlay and tests](randomization/) add independent plain-combination and signature-zero-test
controls, optional public plain-only engine selection, solver seeds and a budgeted native residual
check restricted to plain F4. This option does not change the normal provisioner path or install a
replacement stock binary. See the [experiment contract](../../../../research/grobx-randomization/README.md)
for requests, observation limits and the predeclared campaign.
