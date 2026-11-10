# The benchmark schema, as implemented: two schemas and one set of conventions

**Measured at:** not measured here — this document takes no measurement of its own. Every figure in
it is quoted from a source doc comment or another research note and cited there; the one number that
looks like a measurement, the 4.1x between an estimated and a measured peak on katsura-7, is quoted
from `src/grobner/record/mod.rs` and belongs to that figure's era, not to this document's.

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

*Since #668, only the file-identified half — `InstanceManifest`, `ExperimentRecord` and the `Json`
writer, now under `src/grobner/record/` and `src/util/` — is documented here. The problem-identified
half (`ChallengeManifest`, the challenge registry and the scoreboard's records) was moved out with the
cryptanalysis research; it is preserved at commit 9532a9a2.*

## 1. Two schemas, because a problem is not a file

*The `ChallengeManifest` side of this section (its module-doc rationale and its column of the
comparison table) was moved out with the cryptanalysis research in #668; it is preserved at commit
9532a9a2.*

An `InstanceManifest` says what a *file* is:

| concern | `InstanceManifest` (`src/grobner/record/manifest.rs`) |
| --- | --- |
| identity | `provenance.sha256` — a hash of **bytes** |
| storage | `String` fields, assembled at run time |
| variables | `Vec<String>`, an **ordered list** |
| generators | a count; the bytes are the source file |
| monomial order | verbatim from the file's header |
| completeness | `missing()` naming absent fields |
| serialized | no — `Display` only |

What it shares with the rest of the record layer is a **convention set**: it carries `schema: u32`
at `SCHEMA = 1`; it carries a `redistribution` field; it tags mathematical claims with the `Claim`
type (§3.2); records serialize through the float-free `Json` writer; and identity is derived by
hashing canonical lines, the idiom `external::contract::Instance::canonical` also follows.

### 1.1 Identity is three layers, and they pin different things

*The layer table (problem digest, generator digest, byte hash) belongs to the challenge registry and
was moved out in #668; it is preserved at commit 9532a9a2.*

A name is never the reference. `ExperimentRecord` carries `instance` (a name, "human-readable, and
therefore not a reference") beside `manifest_sha256`, for the reason the record tests state: "two
runs can agree on `fukuoka-mq-III-n10-seed0` and disagree on what that file is."

## 2. #73's nine fields, and what carries each

**More than one type carries this schema, not one.** The manifest, plus `ExperimentRecord` for the
measurement side. That is the single most useful correction this document makes to #73's framing,
which assumed one. *(The challenge-registry carriers — `ChallengeManifest`, `ChallengeProgram`,
`ReferencePoint`, `DisclosedMethod` and `cost_model::FigureBasis` — were moved out in #668.)*

| # | #73 asked for | carried by | state |
| ---: | --- | --- | --- |
| 1 | source, version, retrieval date, upstream commit, content hash | `Provenance{source, version, url, sha256}` | **partial** — retrieval date and commit are folded into free-text `version` ("whatever that source versions by"); one hash where two artifacts exist (§5) |
| 2 | characteristic, degree, modulus, concrete field type | `InstanceManifest{characteristic, extension_degree, field}` | **partial** — **no modulus field in the manifest**, which is a real ambiguity over an extension field (§5). The concrete Rust type is chosen by monomorphization at the call site |
| 3 | generators, or a deterministic generator plus parameters | `generators: usize` (a count); `contract::Instance::system` (embedded, for Zeebra-generated systems) | **met**, and the count is deliberate (§3.1) |
| 4 | variable ordering and monomial order | `InstanceManifest{variables, monomial_order}` | **met for files**; withdrawn for problems (§3.7) |
| 5 | known witnesses, and the verification procedure | `witness`/`verification`; `ExperimentRecord::verified` (three-state) | **met**, one witness per entry (§5) |
| 6 | dimension, degree, quotient dimension, shape position — known or conjectured | `quotient_dimension: Option<Claim<usize>>` | **partial** — quotient dimension only; the known/conjectured mechanism is `Claim` and it is the strong part (§3.2) |
| 7 | reference solver and published results, with citations | *(the challenge registry's carrier, moved out in #668)* | not carried by `InstanceManifest` |
| 8 | resource requirements, measured vs extrapolated **at the schema level** | `ExperimentRecord{estimated_peak_bytes, peak_resident_bytes}` | **met** — see below |
| 9 | provenance and licensing, incl. a download recipe instead of embedded data | `Provenance::redistribution` (**required**) | **met**; the recipe is a sentence plus a script, not a type (§5) |

**Field 8 deserves its own paragraph, because it is the one #73 was most specific about** — "measured
and extrapolated values distinguished at the schema level, not in prose" — and the answer is better
than the issue asked for. `ExperimentRecord` distinguishes *estimated* from *measured* by three
structural means: separate fields, key names a consumer cannot confuse
(`estimated_peak_bytes` against `measured_peak_resident_bytes`), and **omission rather than `null`**
for an absent measurement, because "`null` invites being coerced to zero, and 'not measured' is not
zero bytes". An ambiguous `peak_bytes` key is asserted absent by a test.

*The four-way `cost_model::FigureBasis` distinction (measured, fitted, predicted, extrapolated) was
moved out with the attack cost model in #668; it is preserved at commit 9532a9a2.*

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
tag is load-bearing rather than decorative: `Claim::Proved(1) != Claim::Observed(1)` is asserted.

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

*§3.6 (paperwork excluded from a challenge's identity digest) was moved out with the challenge
registry in #668; it is preserved at commit 9532a9a2.*

**3.7 A monomial order on a *problem*.** Withdrawn as a schema gap, and the reasoning generalizes: "a
weighted monomial order … is a property of an *attack*, not of a problem; it belongs in
`ExperimentRecord::configuration` and `transformations`. `InstanceManifest::monomial_order` describes
a file's coefficient layout, which none of these candidates has an analogue of." The order a file's
coefficients are laid out in is a fact about the file; the order a solver chooses is a fact about the
run.

*§3.8–§3.11 (the cipher parameter-file refusal, `BenchmarkClass`, `DisclosedMethod`/`ExternalStatus`,
and the refused CICO objective) describe the challenge registry and were moved out with it in #668;
they are preserved at commit 9532a9a2.*

## 4. What is unused, stated plainly

*§4 (the `InstanceManifest`/challenge-registry usage audit) was moved out with the cryptanalysis
research in #668; it is preserved at commit 9532a9a2.*

## 5. Gaps, already argued elsewhere and collected here

*§5 (the schema gaps argued in the Fukuoka MQ and MinRank notes) was moved out with those notes in
#668; it is preserved at commit 9532a9a2.*

## 6. Reproducing

The schema is code, so the checks are tests rather than runs:

```sh
cargo test --lib -- grobner::record     # Claim, Provenance, InstanceManifest, and the measurement side, incl. the float refusal
```

`test_estimated_and_measured_memory_are_distinct_keys` is the one to cite for field 8: it asserts
both keys are present, that neither is `null`, and that no ambiguous `peak_bytes` key exists. The two
quantities differ by 4.1x on katsura-7, which is why the distinction is structural rather than
advisory.
