# Bounded R1CS adapter decision (#725)

**Measured at:** `d7e1e130` — role-corrected importer pilot. Its base is `02b21224`, and the full
[retained source patch](../../research/r1cs-725/final-source.patch) reconstructs that importer.
The earlier `c01a9377` and `f6df75c3` cohorts and their original recovery patches are retained
separately; [cohort-provenance.json](../../research/r1cs-725/cohort-provenance.json) binds each
record to its exact source. The same ten timing instances were rerun after reviewed fixes;
no timings are pooled. Compiler, executable and source identities, all thirty attempts,
producer/reader revisions and limits are retained in
[`research/r1cs-725/`](../../research/r1cs-725/README.md).

## Gate and recommendation

**Continue with a narrow checked adapter.** Before adding the Rust implementation, the public
`iden3/r1csfile` example round-tripped byte for byte through independently decoded rows. A
Circom-produced BN254 multiplier round-tripped with section ordering normalized. The pinned
external reader reread both reconstructed files with all coefficients, counts and maps unchanged.
The existing `MultivariatePolynomial<N,F>` API admits their six- and three-variable capacities;
no core runtime-arity redesign is necessary.

The independent prototype tested all 343 assignments in GF(7)^3 against three synthetic rows
(1,029 row checks), including constants, empty combinations and linear constraints. The Rust
suite repeats an exhaustive comparison between original sparse-row residuals and expanded
polynomials. The producer's BN254 witness `[1,15,3,5]` is valid, while incrementing its public
output yields a nonzero residual in both representations.

The original sparse R1CS row evaluator is the named semantic baseline. The independent input
oracle is `r1csfile` 0.0.48 at `d82959da1f88fbd06db0407051fde94afbf8824a`, plus Circom's generated
witness calculator. None of these checks is a proof-system security result or a performance
comparison with another solver. Solving, recovery, Halo2/AIR inputs and a universal circuit IR
remain outside this adapter.

## Source and wire identity

The format source is the pinned [R1CS v1 description](https://github.com/iden3/r1csfile/blob/d82959da1f88fbd06db0407051fde94afbf8824a/doc/r1cs_bin_format.md).
The compiler is the official [Circom 2.2.3 release](https://github.com/iden3/circom/releases/tag/v2.2.3),
whose source tag is `ad44e915a12bb047b05745c2884aad9cc8326bc6`. The release binary's exact hash
is pinned directly, without claiming a reproducible build from that source tag. The circuit is
our synthetic multiplier; its entire source, binary, symbols and producer witness are retained.
The motivating [Picus project](https://github.com/chyanju/picus) is a prospective consumer;
this change introduces no Picus integration or claim about its analysis.

| Input | Wires / rows | Source SHA-256 | Canonical SHA-256 |
|---|---:|---|---|
| Public reader example | 7 / 3 | `8fdbe0d7cfd4379e36593ed9597889a3b7b750566d035c7cc805b9acaaf3d039` | same |
| Circom multiplier | 4 / 1 | `16ab9e569919f7d25f32321974db3b1803b469d4ab0c25769cc94cc3f0d324f7` | `945ef7efeda20135be64cfb8a91533cad8aba99bf1cd8f56c5d55ded1b9c4add` |

Wire zero is checked as constant one; wire `i > 0` maps to variable `i − 1`. Original row IDs,
selected wire labels, public-interface roles, declared private counts and optional symbols remain attached.
A symbol for a selected canonical label must retain that label's actual wire. Other labels may
alias a wire or remain optimized out. Polynomial capacity can include padding, but that padding
is unconstrained and must not be counted as new circuit wires. Exact capacity is appropriate
when asking a later solver about dimension.

The profile requires exactly header, constraints and wire-map sections. Unknown/custom sections
are explicit refusals, including extensions the broader format permits tools to ignore.
Prime fields of canonical 8–32-byte width are admitted only on an exact modulus match; extension
fields, noncanonical factors, inconsistent metadata and truncation are refused. This strict
profile is a stated limitation, not a claim to accept every R1CS producer or extension.

## Optimized private-input role conformance

A separate functional producer audit found that private counts do **not** establish a retained
private-wire prefix. At pinned Circom source `ad44e915a12bb047b05745c2884aad9cc8326bc6`,
[`constraint_list/src/lib.rs:132–139`](https://github.com/iden3/circom/blob/ad44e915a12bb047b05745c2884aad9cc8326bc6/constraint_list/src/lib.rs#L132-L139)
keeps original and retained private counts separately;
[`r1cs_porting.rs:37–45`](https://github.com/iden3/circom/blob/ad44e915a12bb047b05745c2884aad9cc8326bc6/constraint_list/src/r1cs_porting.rs#L37-L45)
writes the original count into the binary header. The
[`simplifier's deletion accounting`](https://github.com/iden3/circom/blob/ad44e915a12bb047b05745c2884aad9cc8326bc6/constraint_list/src/constraint_simplification.rs#L715-L729)
calculates retained counts separately. Public inputs and outputs are protected from deletion
by the producer's [`forbidden_if_main` set](https://github.com/iden3/circom/blob/ad44e915a12bb047b05745c2884aad9cc8326bc6/dag/src/lib.rs#L180-L201).

The retained `roles.circom` has one used and one unused private input plus an internal square.
Its O0 file has five wires and map `[0,1,2,3,4]`; O2 has four wires and map `[0,1,2,4]`, but both
headers declare two private inputs. The O2 symbol table marks input label 3 optimized out and
internal label 4 on wire 3. A header-only private-prefix interpretation would misclassify that
internal wire. `roles-many.circom` additionally demonstrates five declared private inputs with
only four retained wires. The external reader's complete conformance outputs, fixture hashes,
source circuits and O0/O2 binaries/symbols are retained. These are functional regression probes,
not additional instances in the timing pilot.

The generic adapter consequently preserves the private count as metadata, returns
`UnclassifiedWitness` after the public prefix when that count is nonzero, and returns `Internal`
there only when the declared count is zero. It does not infer private identities from labels or
names. Public-prefix and wire-map bounds remain checked; private declarations are not required
to fit retained wires. Exact private-wire identity requires producer information absent from this
binary header and symbol format. Both formerly failing optimized-role regressions now pass.

## Ten-case bounded pilot

The predeclared pilot used one worker on CPU 2, one fresh child for each of ten cases, a
60-second external timeout and `RLIMIT_AS=512 MiB`. The virtual-address-space ceiling is
stricter than an RSS ceiling. Library defaults separately bound 100 wires, 1,000 rows,
16 MiB of input/sidecar bytes, 10,000 symbols, 100,000 raw products and 100,000 retained terms,
with cooperative per-operation deadlines. Counts do not constitute a process-memory guarantee.

Values below are single observations, not throughput estimates or ratios. Harness wall includes
GNU `time` startup; kernel child RSS and the native self-high-water snapshot are retained as
separate fields. The native snapshots were 2.41–2.81 MiB across all ten children. There were
no timeout, memory-limit or unexpected failures; seven refusals are expected outcomes, not
missing answers.

| Case | Outcome / refusal | Raw products / retained terms | Parse / model | Original-row / polynomial check | Harness wall / kernel child RSS |
|---|---|---:|---:|---:|---:|
| Producer BN254 | complete, witness agrees | 1 / 2 | 16.9 / 3.29 µs | 0.391 / 2.99 µs | 4.39 ms / 2.09 MiB |
| Public example | complete, exact canonical round-trip | 15 / 17 | 46.3 / 7 µs | not requested | 3.65 ms / 2.04 MiB |
| Synthetic GF(7) | complete, witness agrees | 2 / 2 | 6.43 / 1.73 µs | 0.101 / 0.33 µs | 3.98 ms / 2.06 MiB |
| Capacity 2 | `Arity` | not expanded | 13.7 / 0.11 µs | not reached | 3.68 ms / 2.06 MiB |
| Wrong modulus | `FieldMismatch` | not expanded | 0.681 µs / not reached | not reached | 3.92 ms / 2.09 MiB |
| Truncated file | `Truncated` | not expanded | 1.99 µs / not reached | not reached | 3.64 ms / 2.09 MiB |
| Constant wire zero | `ConstantWire` | 1 / 2 | 13.7 / 3.72 µs | 0.03 µs refusal / not reached | 4.04 ms / 2.04 MiB |
| Declared 101 wires | wire `Limit` | not expanded | 0.711 µs / not reached | not reached | 3.97 ms / 2.05 MiB |
| Declared 1,001 rows | row `Limit` | not expanded | 0.741 µs / not reached | not reached | 3.57 ms / 2.05 MiB |
| Product budget zero | product `Limit` | refused before first product | 15.1 / 0.31 µs | not reached | 3.56 ms / 2.05 MiB |

The two declared-count cases are admission tests, not valid large-system cost measurements.
`solve_ns` and `recovery_ns` are null for every row, since those tasks were not attempted.
Read, symbols, parse, model and independent/polynomial-check durations remain separate in the
raw records. The pilot establishes that these small slices fit the existing API and declared
process budgets; it does not establish a crossover, all-producer coverage or feasibility beyond
those limits.

## Validation and integration

The initial parser test failed before implementation. The symbol-identity regression separately
failed before the stronger consistency check; a small-stack regression failed before capacity
admission was moved ahead of fixed exponent-array allocation. Twenty-two integration tests cover malformed and
every-prefix-truncated files, missing/duplicate/unsupported sections, field and coefficient
checks, roles and labels, symbols, empty/constant-only/tautological rows, const-generic padding,
structural limits, small-stack capacity refusal and zero deadlines, optimized private-role
ambiguity, plus exhaustive GF(7) and the producer's BN254 witness.
The source documentation and [user guide](../guide/r1cs.md) state the profile and arity limits.
Existing CI automatically discovers these offline integration tests, builds the example and
compiles the guide as doctests; no external producer or new CI dependency is required.
