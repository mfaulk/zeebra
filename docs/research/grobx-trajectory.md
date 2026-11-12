# Grobx and Zeebra trajectory attribution (#713)

**Measured at:** not measured here yet — this initial counter contract precedes instrumentation; final native evidence will identify its frozen source and binaries below.

This study compares complete reduced grevlex bases on the two public `mq-random-10`
instances, not a solver redesign. Baseline production code is main after #717
(`ff65d2b4`), including the #712 prefix optimization. Grobx is pinned to
`1854835dbc25f24dc9a9ba017024d5030e99da1c` (0.73.3); its current default branch was
identical when this work began. The isolated GPL instrumentation is confined to
`tools/external/grobx-driver/research/` and a separate build workspace. No upstream
implementation is introduced into the MIT library.

## Counter contract and scope

The report decoder first reads the existing `grobx-683.json.gz` evidence. It retains
all signature rounds, the discarded run and original-input restart, the plain
rounds, both input echelon phases, and final basis interreduction. Grobx's public
`Stats` describes only the last run and excludes final interreduction. The full
report is the observation interface: enabling a trace listener or cofactors would
change randomization and handover and is forbidden as an instrumentation method.

| Quantity | Meaning and comparability |
|---|---|
| Pair decisions | Engine-native generated/considered/rejected/queued/processed counts, preserving criterion names. Signature reductants are not ordinary S-pairs. |
| Round degree | Plain sugar degree versus signature degree; the same integer is not proof of the same trajectory. |
| Matrix dimensions/entries/density | Initial encoded rows and columns, not peak fill or allocated capacity. |
| Rank/new pivots | Keep inherited pivots and newly discovered rows distinct. Zero combinations/tests are not individual zero rows. |
| Pivot applications | One target update by a pivot, including band lanes separately. Counts are never assumed to have equal cost. |
| Coefficient products | Entries actually multiplied in the update kernel. Include zero multiplier lanes if executed; distinguish pivot leading entries included/skipped. |
| Entry charges | Existing grobx budget `subtracted`/`added`: full row length per target/lane. A diagnostic work proxy, not exact products. |
| Sparse target work | Entries scanned/merged/rewritten by the actual post-prefix kernel. Preserved prefixes are reported separately; they are not coefficient arithmetic. |
| Dense work | Loaded entries, cells scanned/cleared/gathered and pivot scatter updates. Count actual loops, not hypothetical dense spans. |
| Live payload | Simultaneous entries by original/source-reference and newly materialized row roles, plus scratch. Mathematical live entries and duplicate physical input copies are distinguished. |
| Capacity | Allocated slots by buffer type, including scratch/dense/auxiliary arrays. Entry sizes and sharing determine logical bytes; allocator residency/RSS cannot be inferred exactly. |
| Process wall/RSS | Fresh-process spawn to reap and process high-water RSS, including full output encoding; independent answer checking is afterwards. Stage durations remain separate. |

Counters are scoped to one serial computation, opt-in, and separated into
forward reduction, back-substitution, final interreduction and per-batch metadata.
They must not reorder rows, change pivot selection, add tracing, change field
representations, or alter mathematical budgets. Known-rank hand-computable tests
establish product and row-application counts before MQ runs. Feature-absent,
feature-present/counters-off and counters-on arms distinguish compilation/layout
cost from observation overhead. Same-path checks compare dimensions, degrees,
pairs, ranks, zeros and entry charges, not clocks.

This is a bounded matrix ledger, not a replacement for #268's whole-process memory
accounting. Basis objects, monomial intern tables, queues, output strings and
allocator retention must remain explicitly unaccounted where not observed.
Logical bytes and unique pivot-entry reads are not measured physical DRAM traffic.

## Reproduction

Use the existing [external comparison protocol](external-comparison-protocol.md),
[driver contract](../../tools/external/grobx-driver/README.md), and
[study commands](../../research/grobx-trajectory/README.md). The runner reuses
`mq10-profile.py`'s full-answer checker and descendant RSS observation, the corpus
reference artifacts, and `benchlock.sh`; it does not append profiling rows to the
competitive board. Every failure/refusal remains in the retained cohort.

Exact initial identities:

- GF(32003): `16422dafcdb6487ea541f976f7754112b811c85af2b3537ed10fe4ef9c8f3d7f`.
- GF(2147483647): `72d0ad315fc25409792625465578d18329597d3ee183e75f257774d9215803b2`.

All completed answers must match the full retained independently Singular-verified
247-polynomial bases. Reusing those exact reference polynomials is independent
answer verification, not rerunning Singular within timed solver work. Tiny
hand-matrix tests supplement this check; rank or leading monomials alone never
suffice. Five interleaved fresh-process repetitions per arm, one worker, same
machine/affinity/ISA, 60 seconds and 2 GiB per child, frozen sources and binary
hashes, and explicit load gates are required. This attribution study does not
adopt a technique; larger MQ/Katsura/Cyclic validation gates any later adoption.
