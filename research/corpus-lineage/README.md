# #1005: retained-corpus lineage audit

This audit inspects committed definitions and identities, without running a solver or recording
new timings. The [admission and split contract](../../docs/research/corpus-lineage.md) defines the
schema, normalization, S1–S5, and the separate later M34 freeze. These artifacts are **not an M34
cohort freeze**. The example catalog/split/exposure list reuse published inputs to demonstrate the
commands; their evaluation label never means those inputs are untouched.

```sh
python3 tools/test/corpus-lineage-test.py
python3 tools/corpus_lineage.py audit > /tmp/corpus-lineage-audit.json
cmp research/corpus-lineage/audit.json /tmp/corpus-lineage-audit.json
python3 tools/corpus_lineage.py validate research/corpus-lineage/example-catalog.json
python3 tools/corpus_lineage.py check research/corpus-lineage/example-catalog.json research/corpus-lineage/example-split.json
python3 tools/corpus_lineage.py draw research/corpus-lineage/example-catalog.json --protocol S2 --salt example-only --evaluation-groups 1 --exposed research/corpus-lineage/example-exposed.json > /tmp/lineage-example-split.json
python3 tools/corpus_lineage.py check research/corpus-lineage/example-catalog.json /tmp/lineage-example-split.json
```

Run from the repository root with Python 3.9 or newer; all dependencies are standard-library.
The audit output is sorted JSON with file hashes, so CI's retained-audit test detects stale evidence.
A change to an audited source requires regenerating the artifact and reviewing the new findings.
It is a partial legacy audit, not a catalog accepted by `validate`; null support/digest fields are
explicitly unresolved, not independent instances. `audit` exits 0 when inspection succeeds even
when it finds unresolved data; `check` uses 0/1/2 for clean/leaking/invalid splits.

## Coverage and findings

[audit.json](audit.json) retains the file hashes and every row behind these counts:

| Input | Coverage |
|---|---|
| `research/wide-corpus/cases.json` | 39 exact prime-field systems, including BN254 |
| `research/public-corpus/results/public-679.json.gz` | 6 retained exact systems |
| `research/public-corpus/inventory.json` | 8 reviewed upstream candidates; original decisions and file hashes retained |
| `research/m33-baseline/candidates.json` | 152 identities, 76 per track; exclusions retained |
| `research/m33-baseline/held-out.json` | 4 original held-out identities, marked within the candidate/final rows |
| `research/m33-baseline/manifests/{G,M}-baseline.json` | 17 baseline input-file links with their original hashes, joined to final reference input digests |
| `research/m33-final/references.json` | 21 final input identities, including the 4 held-out rows |
| `research/m33-qualification/references.json` | 71 correctness reference identities over grevlex, grlex and lex |

Across the 289 occurrence rows (generator sources and qualification recipes are hash-pinned too):

- **17 repeated computed-support groups** among the exact systems and digest-linked references. Field twins share support
  where reduction did not remove terms. These are groups, not extra independent samples.
- **53 repeated formulation groups** across exact systems and M33 identities. For example,
  `eco/12` and `katsura/9` occur at several primes and in several retained corpora. The sparse MQ
  `n=10, seed=1` candidate is one conservative formulation group at every prime, even though a
  finite-field RNG draw need not preserve its support.
- **39 repeated legacy-digest groups**, representing reuse of candidate/catalog inputs in final
  and correctness qualification. They are recorded occurrences of known inputs, not fresh evaluation examples.
- **12 repeated normalized-input groups** after joining references to exact definitions by their
  legacy input digest. There are 72 equation-backed occurrences: 45 original definitions, 9
  final references and 18 qualification references. The original 45 definitions have no normalized
  duplicate group. The other 217 identity-only occurrences still lack a verified normalized input
  and support; admission must materialize their pinned equations and verify their digests.
- The wide catalog's `mq-random-N` is **dense all-nonzero MQ** (`examples/wide_corpus.rs`, seed
  `0x73800000+N`). M33's `mq-random-N-sS` is **sparse sampled MQ**
  (`corpus::random_mq_instance`, `max_terms=4*N`, seed S). An unqualified M33 name uses the frozen dense catalog when that field/name is
  registered there, and the sparse generator at seed N otherwise; the qualification recipe
  records this distinction.
  The audit gives these separate family/formulation namespaces. Their shared display prefix is
  insufficient evidence of shared support.
- The public inventory is an acquisition review, not eight admitted systems. In particular its
  excluded headerless/model-data exports are not imported or promoted to records with invented
  provenance. Retained smaller independently generated cases remain distinct from larger
  upstream exports. Original decisions stay in `upstream_decisions`.

`historical_split` examines the **21 final identities**: the four original held-out identities are
`evaluation`, the remaining 17 development/control identities are `development`. It does not
pretend the entire unmeasured candidate pool was development data.

- There are **no declared-formulation crossings under the S1 relation** in this historical split.
  Nine final input digests join to exact catalog definitions; the other 12 supports remain
  unknown, so this is not a clean S1 certification.
- **Katsura and sparse random MQ both cross the family boundary under S2.** M33's original draw
  can be reported as a within-family/family-size draw, never an unseen-family result.
- M33's published final outcomes have now been inspected. Its former held-out rows and connected
  relatives must be exposed/development exclusions when drawing a genuinely untouched M34 cohort.

## Remaining admission work

The audit does not guess missing equations, licence rights, transformations or parent chains.
The 217 unresolved occurrence records need materialized, pinned inputs before the normalized
checker can qualify them. Computed support equality is a presentation statistic, not proof of
ideal equivalence. Shared formulation IDs for deterministic named families are conservative
construction groupings supported by the current generators; arbitrary imported alternative
models require a human provenance review and explicit parent links.

The sibling schema and validator leave existing Rust `InstanceManifest` and run-journal formats
unchanged. Add new records with exact equations and a reproducible recipe rather than changing
historical digests. Freeze the actual cohorts in the later commit required by #1005, after
acquisition/admission and before fitting #1013; record that freeze on #1005 and #1043.
