# The benchmark schema, as implemented: two schemas and one set of conventions

**Measured at:** not measured here — this document takes no measurement of its own. Every figure in
it is quoted from a source doc comment or another research note and cited there; the one number that
looks like a measurement, the 4.1x between an estimated and a measured peak on katsura-7, is quoted
from `src/grobner/research/record.rs` and belongs to that figure's era, not to this document's.

Reference for **#73 (A4)**, a child of #65. The issue asked for "a common benchmark schema for
cryptanalysis instances" and said it "should be drafted after A1 has imported something real — a
schema designed in the abstract will encode the wrong things." A1 landed, the schema was built, and
**it was never written down**. This document is that write-up, and the headline is the answer to the
issue's own go/no-go rather than a design proposal:

> **Go** if one representation covers both. **If a single representation cannot cover MQ and
> cryptographic entries without special-casing, split it into two documented schemas rather than
> forcing a unified one.**

**The split happened.** There are two manifest types, they share no field set and no conversion, and
the reason is structural rather than incidental. What was missing was the second half of that
sentence — the documentation. §1 states the split and why; §2 maps #73's nine fields onto what
actually carries each; §3 is the part worth reading, the things the schema deliberately refuses; §4
is an honest account of what is unused; §5 collects the gaps other documents have already argued.

## 1. Two schemas, because a problem is not a file

`src/grobner/research/challenge.rs` states the distinction in its module doc, and it is the whole
design:

> An `InstanceManifest` says what a *file* is. A `ChallengeManifest` says what a **problem** is — the
> objective a public program stated, the parameters it stated them over, and how a claimed solution
> is checked by something that is not this crate. The two are separate because a challenge need not
> be a file: the 2026 CICO targets are a sentence and five numbers, and their round constants are
> *derived* rather than published.

That is not a profile distinction. The two have **disjoint field sets**, different identity
semantics, different completeness mechanisms, and no conversion in either direction:

| concern | `InstanceManifest` (`manifest.rs`) | `ChallengeManifest` (`challenge.rs`) |
| --- | --- | --- |
| identity | `provenance.sha256` — a hash of **bytes** | `digest()` — SHA-256 over canonical family + objective + parameters |
| storage | `String` fields, assembled at run time | `&'static str`, a compile-time frozen constant |
| variables | `Vec<String>`, an **ordered list** | a count only |
| generators | a count; the bytes are the source file | **executable** — `cico_instance()` builds them |
| monomial order | verbatim from the file's header | absent, deliberately (§3.7) |
| published results | absent | `reference_points: &[ReferencePoint]` |
| completeness | `missing()` naming absent fields | a frozen-registry test over id and digest |
| serialized | no — `Display` only | yes, 63 files under `research/scoreboard/challenges/` |

What they do share is a **convention set**, which is the part that makes "one schema" the wrong way
to describe it and "two unrelated schemas" equally wrong: both carry `schema: u32` at `SCHEMA = 1`;
both carry a `redistribution` field; both tag mathematical claims with the same `Claim` type (§3.2);
both serialize through the same float-free `Json` writer; and both derive identity by hashing
canonical lines — `external::contract::Instance::canonical` says "Follows `ChallengeManifest::canonical`
in shape", so the idiom is cross-schema by intent.

### 1.1 Identity is three layers, and they pin different things

The distinction that makes two schemas necessary is sharpest here. `MILESTONE-CRYPTANALYSIS-SCOREBOARD.md`
§4.1 tabulates it; restated because a reader of #73 needs it first:

| what is pinned | by | when it is the right reference |
| --- | --- | --- |
| **the problem** | `ChallengeManifest::digest` | a public program stated an objective over parameters; the bytes may not exist |
| **the generator** | `derived_digest` | the instance is constructed, so the construction *is* the identity |
| **the bytes** | `Provenance::sha256` | the problem *is* a file, and a regenerated file is a different one |

A name is never the reference. `ExperimentRecord` carries `instance` (a name, "human-readable, and
therefore not a reference") beside `manifest_sha256`, and the scoreboard's `RunRecord` carries
`challenge` beside `challenge_digest`, for the reason `record.rs`'s test states: "two runs can agree
on `fukuoka-mq-III-n10-seed0` and disagree on what that file is."

## 2. #73's nine fields, and what carries each

**Four types carry this schema, not one.** Two manifests, plus `ExperimentRecord`/`RunRecord` for the
measurement side, plus `cost_model::FigureBasis` for the epistemic status of a *figure*. That is the
single most useful correction this document makes to #73's framing, which assumed one.

| # | #73 asked for | carried by | state |
| ---: | --- | --- | --- |
| 1 | source, version, retrieval date, upstream commit, content hash | `Provenance{source, version, url, sha256}`; `ChallengeProgram{name, version, url}` | **partial** — retrieval date and commit are folded into free-text `version` ("whatever that source versions by"); one hash where two artifacts exist (§5) |
| 2 | characteristic, degree, modulus, concrete field type | `InstanceManifest{characteristic, extension_degree, field}` | **partial** — **no modulus field in either manifest**, which is a real ambiguity over an extension field (§5). The concrete Rust type is chosen by monomorphization at the call site; `ChallengeManifest` instead refuses a mismatched `F` by name |
| 3 | generators, or a deterministic generator plus parameters | `generators: usize` (a count); `cico_instance()` (executable); `contract::Instance::system` (embedded, for Zeebra-generated systems) | **met three ways**, and the count is deliberate (§3.1) |
| 4 | variable ordering and monomial order | `InstanceManifest{variables, monomial_order}` | **met for files**; withdrawn for problems (§3.7) |
| 5 | known witnesses, and the verification procedure | `witness`/`verification`; `verifier`; `CicoTarget::PlantedFrom`; `ExperimentRecord::verified` (three-state) | **met**, one witness per entry (§5) |
| 6 | dimension, degree, quotient dimension, shape position — known or conjectured | `quotient_dimension: Option<Claim<usize>>` | **partial** — quotient dimension only; the known/conjectured mechanism is `Claim` and it is the strong part (§3.2) |
| 7 | reference solver and published results, with citations | `reference_points: &[ReferencePoint]`, `DisclosedMethod` | **met**, and added *because* `InstanceManifest` had nowhere to put a competitor's figure |
| 8 | resource requirements, measured vs extrapolated **at the schema level** | `ExperimentRecord{estimated_peak_bytes, peak_resident_bytes}`; **`cost_model::FigureBasis`** | **met, by a type #73 did not anticipate** — see below |
| 9 | provenance and licensing, incl. a download recipe instead of embedded data | `Provenance::redistribution` (**required**), `ChallengeProgram::redistribution`, the fetch scripts | **met**; the recipe is a sentence plus a script, not a type (§5) |

**Field 8 deserves its own paragraph, because it is the one #73 was most specific about** — "measured
and extrapolated values distinguished at the schema level, not in prose" — and the answer is better
than the issue asked for. `ExperimentRecord` distinguishes *estimated* from *measured* by three
structural means: separate fields, key names a consumer cannot confuse
(`estimated_peak_bytes` against `measured_peak_resident_bytes`), and **omission rather than `null`**
for an absent measurement, because "`null` invites being coerced to zero, and 'not measured' is not
zero bytes". An ambiguous `peak_bytes` key is asserted absent by a test.

The four-way distinction lives in `cost_model::FigureBasis`: `Measured{instrument}` — because "two
instruments for peak memory measure different quantities" — `Fitted{law, worst_residual_bp,
fitted_to}`, `Predicted{model}`, and `Extrapolated{law, fitted_to, evaluated_at}`, "separated from
`Fitted` because the residual does not transfer: nothing bounds the error of a law outside its
range". And it is **enforced, not advised**: "an estimate in a measured field is a `SchemaError`, not
a caveat." The contract is written into the data file itself, because "a consumer cannot read a Rust
doc comment."

### 2.1 One correction to the existing prose

`MILESTONE-RESOURCE-AWARE-CRYPTANALYSIS.md` §7.1 is the closest thing to a specification that
existed, and it lists three fields the type does not have: a **repository commit** (folded into
`version`), a **modulus or irreducible polynomial** (absent — §5), and a **variable count** distinct
from the names (derivable from `variables.len()`). Read it as the design intent, not as the field
list; this document is the field list.

## 3. What the schema deliberately refuses, and why

This is the part a reader cannot reconstruct from the types, and the part most likely to be
re-litigated by someone who assumes an omission is an oversight. Each refusal has a written
rationale at its definition; the argument is quoted because the argument is the point.

**3.1 Generators, as data.** `generators` is a count: "the generators themselves live in the source
file, which the checksum pins; copying them here would duplicate data this manifest cannot license."
The licensing constraint is the reason and the checksum is the substitute. Contrast
`contract::Instance::system`, which *does* embed generators — those systems are generated by Zeebra
and carry no licence problem. So the rule is not "never embed generators" but "never embed generators
you may not redistribute".

**3.2 An untagged mathematical claim.** `Claim<T>` has exactly two variants, `Proved` and `Observed`,
and `Display` cannot print a value without its status. The rationale names the failure it prevents:
"a corpus that mixed the two would let an observation harden into an assumption, and M21-0 found
exactly that failure mode — `generators == variables` looks like a dimension claim and is not." The
tag is load-bearing rather than decorative: `Claim::Proved(1) != Claim::Observed(1)` is asserted,
`published_quotient_dimension` returns `Observed` at every call site "because these are measurements
from one implementation, and the designers' corresponding statement is a conjecture", and
`additional-benchmarks.md` records one instance of a tag being *upgraded* when a conjecture was
proven.

**3.3 Any timing or byte count in a manifest.** "A benchmark instance must not change when a
different workstation produces new timings." Enforced by `test_a_manifest_carries_no_measurements`,
which scans the rendered manifest for `ms`, `seconds`, `bytes`, `MB`, `elapsed` and `memory` — and
whose own doc comment concedes the limit of that: "enforced by review rather than by the type system,
so this test is a statement of intent with teeth."

**3.4 Floats, anywhere in a record.** The `Json` type has no float variant and its parser *rejects*
`0.5` and `1e3`: "a float is not a parse failure in RFC 8259; it is one *here*, because this type has
no float variant and `0.1` does not round-trip." Hence durations as integer nanoseconds and ratios as
two integers, and basis points where a percentage would be natural.

**3.5 `null` for an absent measurement — but `null` where absence means something.** Omission for
"not measured"; `null` retained for `outcome`, `verified`, `failure` and for a stage that never ran,
because "zeros would read as 'it ran and did nothing', which is a different fact". `verified:
Some(false)` is "a defect, not an absence" — three states, not two.

**3.6 Paperwork inside identity.** `ChallengeManifest::digest` excludes the program's URL, its
reward, its external status and its verifier prose, "because those are things that get corrected or
that change on the program's side, and an identity that moved when a bounty was paid would break
every historical comparison keyed on it." Two tests pin it: disclosing a method and adding a
reference point both leave the digest unchanged.

**3.7 A monomial order on a *problem*.** Withdrawn as a schema gap, and the reasoning generalizes: "a
weighted monomial order … is a property of an *attack*, not of a problem; it belongs in
`ExperimentRecord::configuration` and `transformations`. `InstanceManifest::monomial_order` describes
a file's coefficient layout, which none of these candidates has an analogue of." The order a file's
coefficients are laid out in is a fact about the file; the order a solver chooses is a fact about the
run.

**3.8 A parameter-file format.** None exists, deliberately — see `poseidon.md` §7.2. The parameters
are typed, so a malformed configuration is a compile error or a named refusal rather than a run-time
parse error, and the identity digest covers them.

**3.9 A single aggregate score.** `BenchmarkClass` exists so that a witness for a planted `t = 2`
surrogate and a verified witness for the official `t = 16` target are never summed, and "nothing here
produces a single score". `Significance` is *computed* from class and external status rather than
asserted by whoever writes the report.

**3.10 A guess where the method is unknown.** `DisclosedMethod::Unknown` is "the honest state for a
solved problem with no technical report, and not a synonym for 'brute force' or for any other guess."
And `ExternalStatus::NotAPublicProblem` is distinct from `NoneRecorded`, because "reporting a derived
instance as having no recorded solution would imply someone had looked."

**3.11 An objective the crate cannot generate, silently rebuilt as one it can.** `cico_instance`
refuses `CicoExactTrailing` by name rather than building the leading-constraint objective, because
"the result would be a different problem wearing this row's identity." The rows are registered
anyway: "a scoreboard that only lists what it can run hides the targets that are actually open."

## 4. What is unused, stated plainly

**`InstanceManifest` has no library caller.** It is constructed in exactly two places —
`examples/mq_challenge.rs`, twice — and in its own unit test. No code under `src/` builds, consumes,
validates or serializes one; `missing()` and `is_complete()` have no caller outside their own tests;
there is no `to_json` and no file on disk. The committed corpus is **100% `ChallengeManifest`**: 63
entries, emitted to `research/scoreboard/challenges/` "so the JSON cannot drift from the code".

This is worth recording rather than quietly leaving for the next reader to discover, and it is not
the same as saying the type was a mistake. It is the shape a file-identified instance takes, it is
exercised end to end by the example that imports a real Fukuoka file, and `ChallengeParameters::MqSystem`
carries the one field — `sha256` — that a file-identified problem needs inside the registry that is
actually used. What has not happened is a second file-identified family arriving to justify the
separate type. If one does, this is the type; if the registry absorbs the case instead, the honest
step is to retire `InstanceManifest` rather than keep two homes for one concern.

`#73`'s acceptance criterion "two structurally different instances load through one path" is
therefore **partly met**: `examples/scoreboard.rs` dispatches CICO and MQ rows as two constructors
over **one registry** and **one record schema**. One path for identity and for results; two for
construction.

## 5. Gaps, already argued elsewhere and collected here

None of these is new in this document; each is an argued finding in the document that hit it, and
#73 is where they belong together.

| gap | why it matters | argued in |
| --- | --- | --- |
| **no modulus / irreducible polynomial field** | an entry over a non-prime field without one "is not under-specified, it is ambiguous between two different problems" — two tools' default `GF(2^8)` need not be the same ring | `fukuoka-mq.md` §12 |
| **one content hash, two artifacts** | field 1 says "content hash", singular; a generated Fukuoka instance has both the instance file and the 200 MB π artifact | `fukuoka-mq.md` §12 |
| **one witness per entry** | 37 recorded solves each publish a full answer vector on its own URL; a schema holding one cannot express them | `fukuoka-mq.md` §12 |
| **no unit/scope/metric for a published figure** | "a measured per-subsystem CPU figure and a measured wall-clock total are both measured and are not the same kind of number" — handled today in TSV headers, not in Rust | `fukuoka-mq.md` §12, `minrank.md` |
| **no mirror URL** | a canonical URL that rots takes the fetch recipe with it | `additional-benchmarks.md` |
| **no rank objective, no `MinRank` parameters** | MinRank needs an `Objective` carrying a target rank | `minrank.md` |
| **no structured download recipe** | the recipe is a sentence in `redistribution` plus a script; it works and it is not typed | this document |
| **no offline validation in CI** | `missing()` exists and nothing calls it | this document |

## 6. Reproducing

The schema is code, so the checks are tests rather than runs:

```sh
cargo test --lib -- grobner::research::manifest     # Claim, Provenance, InstanceManifest
cargo test --lib -- grobner::research::record       # the measurement side, incl. the float refusal
cargo test --lib -- grobner::research::challenge    # the frozen registry, id and digest per row
cargo test --lib -- grobner::research::cost_model   # FigureBasis, and the measured-field refusal
cargo run --release --example mq_challenge          # the only place an InstanceManifest is built
```

`test_estimated_and_measured_memory_are_distinct_keys` is the one to cite for field 8: it asserts
both keys are present, that neither is `null`, and that no ambiguous `peak_bytes` key exists. The two
quantities differ by 4.1x on katsura-7, which is why the distinction is structural rather than
advisory.
