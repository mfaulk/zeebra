# Corpus identity, lineage and generalization splits

Issue #1005; task vocabulary from [the contract matrix](adaptive-selection-contracts.md).
This is an admission and splitting contract, with no solver timings. It does not change
`InstanceManifest::SCHEMA` or any retained instance or measurement digest. Actual M34 development
and untouched cohorts must be frozen in a **separate later commit**, before #1013 fits a rule.
The examples below use already published inputs and are **not an untouched cohort**.

## Admission record

[corpus-lineage.schema.json](../../tools/corpus-lineage.schema.json) is a sibling JSON Schema
(Draft 2020-12), version `corpus-instance-v1`. A catalog is a JSON array of records with unique
`id`s. [corpus_lineage.py](../../tools/corpus_lineage.py) validates the schema and the semantic
constraints with Python's standard library. No Rust build, external solver or pip package is needed.
Unknown fields, duplicate JSON keys, nonfinite numbers and unknown schema constraints fail closed.

Every record requires:

- `id`, `field`, **ordered** `variables`, `order`, `task` and exact `equations`.
- `source.url`, `source.revision` and `source.license`. State data-specific terms; a repository's
  licence alone does not establish ownership of imported models. Unresolved terms preclude admission.
- `generator`: `null` for exact imported equations, or a recipe with `repository`, full 40-hex
  `revision`, `path`, argument-vector `call`, `seed` (integer or explicit `null`), and `parameters`.
  Retain generated equations too: a recipe alone cannot verify the normalized input digest.
- `transformations`: an ordered array of `{kind, description}`; use `[]` when none. Record field
  equations, elimination, slicing, denominator clearing, variable/coordinate changes, generator
  mixing, homogenization and alternate formulations. They may change the ideal or the task.
- `normalized_input_digest`, and the lineage object below.

`field` contains a decimal-string `characteristic`, integer `extension_degree=d`, and
`defining_polynomial`: `[]` for prime fields, or `d+1` decimal residues, constant coefficient first,
with leading coefficient 1. Extension coordinates use the basis `1,a,...,a^(d-1)` modulo that
polynomial. Each equation is a list of `{exponents, coefficient}` terms: `exponents` has one
nonnegative integer per ordered variable; `coefficient` has exactly `d` decimal residues in `[0,p)`.
An empty term list is zero; an empty equation list is the zero ideal. At least one variable is
required. Admission must establish primality/irreducibility separately: the shape validator checks
encoding, not that a claimed coefficient ring is a field.

`order` is an exact order specification, including weights/blocks and precedence when applicable;
it must not abbreviate two different orders to the same string. `task` is `T-GB`, `T-GB-conv`,
`T-PT1` or `T-PTALL`. Run limits, hardware and measurements belong in run manifests, not this record.

| Lineage key | Definition and assignment rule |
|---|---|
| `support_id` | One construction support: coefficient resamples share it. Use the computed `support-v1` hash for identical coordinate supports; retain a broader common ID if a resampling process can cancel terms. |
| `formulation_id` | One mathematical formulation at fixed family parameters, before prime reduction. Field twins share it. Include a random generator's seed; do not equate two different generators because their display names agree. |
| `presentation_parent` | Immediate parent instance ID, or explicit `null`. Every ancestor must occur in the catalog; cycles and unresolved parents are errors. A changed presentation stays connected to the original through this chain. |
| `family_id` | The construction mechanism/model family, independent of scale, coefficient sample and prime. Dense all-nonzero MQ and sparse sampled MQ are different mechanisms. |
| `family_parameters` | Named JSON parameters, including the numeric scale variable used by S3. Keep generator parameters too; these describe the family rather than a command. |
| `source_id` | Stable upstream collection **and model** identifier. Use a broader shared source ID when several models cannot be established as independent. |

IDs are globally comparable, not scoped by a file, field, order or split. Grouping is transitive:
sharing any protected key joins the entire connected group. Do not rename a lineage ID to obtain
an eligible holdout. New/uncertain relationships require provenance review; the checker cannot prove
that arbitrary asserted lineage labels are true.

## Two input identities

The existing `external::contract::Instance::digest` hashes `Instance::canonical`: field, order,
ordered variables, transformation text, and each **generator string in its original order**.
It does not parse polynomials. Consequently, changing term text/order or generator order changes
that legacy digest. It is **not stable** under the S4 normalizations. The wide catalog also has a
separate `wide-corpus-v1` format. Neither historical format is rewritten here.

`normalized-input-v1` hashes compact, sorted-key, ASCII JSON with the keys `format`, `field`,
`variables`, `order`, `equations` (`json.dumps(..., sort_keys=True, separators=(',', ':'),
ensure_ascii=True)`). For each polynomial: sum repeated exponent vectors componentwise modulo p,
remove zero coefficients, sort terms by the exponent tuple, and encode a term as
`[exponents, coefficient_decimal_strings]`. Sort the resulting polynomial lists by their compact
JSON bytes, preserving repeated/zero generators. This ignores term and generator enumeration,
without making generators monic. Names, task, recipe, transformation labels and source are excluded:
identical inputs submitted for different tasks still get flagged.

The normalized digest retains the field definition, variable order, coefficients and monomial
order. It is not invariant under coordinate changes, generator mixing, scalar multiplication,
homogenization or ideal equivalence. Those need lineage links, not a stronger claim about hashing.
`support-v1` similarly hashes `{format, variables, supports}`, with the normalized nonzero exponent
lists sorted by JSON bytes, excluding coefficients and field. It is coordinate dependent.

## Split checker

```sh
python3 tools/corpus_lineage.py validate research/corpus-lineage/example-catalog.json
python3 tools/corpus_lineage.py check research/corpus-lineage/example-catalog.json research/corpus-lineage/example-split.json
python3 tools/test/corpus-lineage-test.py
```

A `corpus-split-v1` record has `protocol` and `assignments`: `{id, partition}`, with partition
`development` or `evaluation`. Every catalog ID must be covered, both partitions must be nonempty,
and an instance may occur only once except for S5-hardware. Run each protocol separately; never
aggregate them under a single "held out" label.

| Protocol | Protected groups / required transfer |
|---|---|
| S1 familiar-family interpolation | Protect support ID, computed coordinate support, formulation ID, presentation root and normalized input. Families may occur on both sides. Fresh parameters/seeds must give independent protected groups; fixed-support coefficient resamples stay together. |
| S2 unseen supports and whole families/models | All S1 protections **plus** whole `family_id` and `source_id` groups. This deliberately strict combined protocol cannot qualify a new-family claim using only a fresh support of a known mechanism. |
| S3 scale transfer | S1 protections; required `scale_parameter` names a finite numeric family parameter. Every evaluated family must have development values, and every evaluation value must exceed every development value in that family. No tuning at the larger scale. |
| S4 presentation transfer | S1 protections. Keep the entire parent/transform cluster on one side; evaluate base and difficult presentations together within evaluation. This measures transfer to presentations of an unseen base, not training on a base and calling its permutation independent. |
| S5-field | Explicit exception: support/formulation twins may cross. Each evaluation formulation needs a development twin; complete field definitions must be disjoint across partitions. Normalized inputs and explicit presentation chains remain protected. Report the direction and all characteristics/degrees. |
| S5-hardware | Explicit exception: repeat the same input using assignments `{id, partition, hardware}`. Hardware IDs must be disjoint across partitions; every evaluation normalized input needs a development match. A hardware ID denotes the recorded machine/build/worker configuration, not just its host nickname. |

`validate` returns 0 for valid metadata, 2 for unreadable/invalid metadata. `check` returns 0 for
no detected leakage, 1 for leakage/draw mismatch, 2 for invalid metadata. Normalized-input
collisions are flagged across partitions even when declared lineage differs (the matched-input
S5-hardware exception is explicit). A clean check is not proof of scientific independence.

## Draw, seal, expose and replace

1. Admit the catalog and commit its exact equations, provenance, lineage, generator revisions,
   and source hashes. Resolve audit gaps before admission. Predeclare the protocol, group count,
   salt, exclusion list, eligibility checks, replacement rule and stopping rule **before drawing**.
2. Record every previously exposed ID in a JSON array. Include all inputs inspected in M29–M33
   tables, profiling, routing choices or gate decisions, including former held-out rows. Include
   their known relatives in the catalog so the checker can close the group; incomplete lineage
   cannot establish untouched status. The example exposure file is only a demonstration.
3. For S1/S2/S4 use the deterministic whole-group draw:

   ```sh
   python3 tools/corpus_lineage.py draw research/corpus-lineage/example-catalog.json --protocol S2 --salt example-only --evaluation-groups 1 --exposed research/corpus-lineage/example-exposed.json > /tmp/lineage-example-split.json
   python3 tools/corpus_lineage.py check research/corpus-lineage/example-catalog.json /tmp/lineage-example-split.json
   ```

   The tool closes all protected links, excludes every group touching an exposed ID, and sorts
   remaining groups by SHA-256 of compact JSON `["hash-groups-v1", salt, protocol, sorted_member_ids]`
   (member IDs break a hash tie). Select the first declared number of **groups**, not rows. Retain
   at least one development group. `draw` records the salt, exclusions, group count and canonical
   catalog hash; `check` recomputes and verifies both the draw metadata and assignments.
   S3 uses predeclared scale cutoffs; S5 uses predeclared field/hardware directions instead of a
   random group draw. Validate those explicit assignments with `check`.
4. Commit the catalog, exposure list, split, predeclaration and validation output in a separate
   **freeze commit** linked on #1005 and #1043, before #1013. Tag/reference its full commit and
   file SHA-256s. Seal evaluation outcomes from fitting: feature inspection, trial selection,
   thresholds, model choice and gate decisions may use only development data. A committed input
   list is an integrity seal, not an access-control mechanism; record who may perform qualification.
5. Admission/correctness checks may reject an input only by the predeclared rule. Retain every
   rejection and its reason. Select replacements by continuing the same hash ordering, never by
   speed or whether the result flatters a candidate. Commit an amendment before qualification;
   a changed catalog changes its hash and requires a new documented draw/freeze.
6. Once any evaluation result or feature inspection influences a rule, the whole connected group
   becomes development data. Keep the old seal, label it consumed, record the exposure, and draw a
   new cohort from unexposed groups with a newly predeclared salt. Do not reroll an adverse gate or
   claim that M33's now-published four rows remain untouched in M34.

## Retained-corpus audit

[The audit report and reproduction commands](../../research/corpus-lineage/README.md) cover the
wide catalog, public corpus and upstream inventory, M33 candidate/held-out lists, baseline input
manifests, final reference identities and correctness-qualification references. Partial legacy metadata is reported separately; it cannot
be passed off as an admitted `corpus-instance-v1` catalog. No actual M34 cohort is frozen here.
