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

## 7. The benchmark-job manifest (`bench-job-manifest-v1`, #967)

A third schema, for *runs* rather than problems or results: the input to `tools/bench-job submit`
(usage in [`docs/guide/benchmarking.md`](../guide/benchmarking.md), "Submitting a benchmark job").
The canonical JSON (sorted keys, no whitespace) is the job's identity: the job id is the first 12
hex of its SHA-256, so a changed byte is a different job and a resubmitted manifest is refused.
Validation is `validate()` in `tools/bench-job`; anything below marked *required* is refused when
missing.

| Key | Meaning |
|---|---|
| `schema` | `"bench-job-manifest-v1"`, required |
| `mode` | `"dev"` or `"publication"` (plan §11.2), required; recorded now, enforced by #968 |
| `context.issue`, `context.agent` | the owning issue and `scripts/agent/zb-claim.sh id`, required |
| `arms[].name` | unique; `[A-Za-z0-9._/-]`, the rotation unit |
| `arms[].commit` | 7–40 hex; the source the binary was built from |
| `arms[].binary`, `arms[].sha256` | absolute path at submit time and its SHA-256, which must match; the job copies it |
| `arms[].build.{profile,flags,recipe}` | strings; `recipe` must contain `git archive <commit>` |
| `arms[].build.comparand` | optional; an externally provisioned comparand's provenance (provision script, upstream pin). It stands in for the `git archive` recipe, which a Zeebra arm still needs (#966) |
| `arms[].workers` | optional subset of `run.workers`; the arm runs only at those counts (Track G's 16-worker best-supported arm beside 1-worker arms, #966) |
| `arms[].argv` | template; `{field}` placeholders take `instance.params` and `instance`, `input`, `inputs[<key>]`, `workers`, `seed`, `rep`, `cpus`, `wall_seconds`, `live_bytes` |
| `arms[].contract` | optional task contract: `T-GB`, `T-GB-conv`, `T-RAD`, `T-PT1`, `T-PTALL` or `T-ALG` (`adaptive-selection-contracts.md` §2, #1004) |
| `arms[].configuration` | optional portfolio configuration id, a plain name (default: the arm's name) |
| `instances[].name`, `.params` | unique name; template values |
| `instances[].lineage` | optional `{key: string}` lineage keys, copied to every selection record; #1005 fixes the key set |
| `instances[].path`, `.sha256` | optional input file and its digest; copied and re-hashed like a binary |
| `instances[].inputs` | optional `{key: {path, sha256}}`, one file per solver format, each copied and re-hashed like `path`; argv names one as `{inputs[key]}` (#966) |
| `run.workers` | list of worker counts; an attempt pins to the first *w* CPUs of `run.cpus` |
| `run.cpus` | cpulist handed to `bench-reserve run`; must lie inside the reservation |
| `run.repetitions`, `run.interleave`, `run.seeds` | *n* ≥ 1; `"rotate"` (the only rule); integer seeds, default `[0]` |
| `run.retries` | extra tries for a `failed`, `timeout` or `rss-limit` attempt, default 0 |
| `run.limits.wall_seconds`, `.kill_after_seconds` | the `timeout --signal=INT` cap and its `--kill-after` (default 60) |
| `run.limits.rss_bytes`, `.live_bytes` | `rss-guard` ceiling (null: unguarded); the live-bytes limit for argv templates |
| `run.limits.aggregate_wall_seconds`, `.output_bytes` | the journal's budget; defaults: every try at its cap, 1 GiB. `output_bytes` must be a positive integer: the job stops with `output-bytes` once the retained (gzipped) child output reaches it. Prefer a digest-only reply to raising it (#1020) |

The journal it writes extends `StudyJournal` without forking it. An `exit` record may carry
`try` > 0, a retry of the index recorded immediately before it; and a `resume` record may follow a
`stop`, lifting it. Journals written before #967 contain neither and replay unchanged. Every exit's
metadata carries `attempt_id` (`<job-id>:<index>:<try>`), `binary_sha256`, `cpus`, `argv`, the
`cpu-context` snapshots and `contamination` (null until #968 fills it).

From #1105 an exit also carries `rusage` (the child tree's `nvcsw`, `nivcsw`, `majflt`, `minflt`,
`inblock`, `oublock` from `wait4`), and `contamination.metrics` adds the interference telemetry
listed as `TELEMETRY_METRICS` in `tools/bench_contamination.py`: `telemetry` (its version),
placement-aware compiler and runner counts, `psi` and `psi_bench_slice` stall fractions, `vmstat`
deltas, `mbm_bytes_per_s`, `ccd_load` and `bench_running`. Each is a value, `null` (the snapshots
predate it) or `{"unavailable": "<reason>"}`. No verdict rule reads them, so the session verdict
version stays 3; sources and privileges are in `docs/guide/benchmarking.md`, *Recording the CPU
context of a multicore timing*.

The `complete` stop carries the session verdict, `{version, grouping, contaminated, total, void,
median_khz, clock_sources, flagged}`. **Version 3** (#999) reads an attempt's clock from
per-process cycle counts where `perf` could attach (`contamination.clock_source: "perf-cycles"`,
the counts in the exit's `perf`). It judges those attempts only against the arm's other cycle-count
attempts, keyed `<instance>@<w>w/<arm>/perf-cycles`. Sampled attempts keep the version 2 key, and a
journal without `clock_source` judges exactly as version 2. **Version 2** (#996) groups the clock rule per arm within a cell
(`grouping: "arm"`, `median_khz` keyed `<instance>@<w>w/<arm>`). A verdict with no `version` key
is **version 1**, grouped per cell (`<instance>@<w>w`), and is read as such: `report` names the
grouping either way, and a journal is never rewritten. The re-judged M33 sessions are in
[`research/m33-clock-rule/`](../../research/m33-clock-rule/README.md).

## 8. Selection outcomes (`selection-outcome-v1`, #1008)

A selector is fitted on a performance matrix, and the matrix compares only if every cell is
accounted for the same way (M34 plan §8.4). `bench-job`'s journaled status (`ok`, `failed`,
`timeout`, `rss-limit`, `cancelled`) is the harness's view, and it drives retries. It cannot tell a
typed refusal from a completion, because a child that refuses still exits 0. Before this schema, such
an attempt was timed as if it had finished.

`selection_outcome()` in `tools/bench-job` derives one more status per attempt, at report time,
from:

- the journaled status;
- the child's JSON report (its last stdout line);
- optionally, an independent reference digest.

Nothing new is journaled, so every journal written before this schema replays unchanged.
`report --json` carries one `selection` record per attempt and `counts.selection`.

### 8.1 Statuses

| Status | Comes from | Completion time | Timed |
|---|---|---|---|
| `completed-verified` | a completion that passed the arm's runtime check (`verified: true`, grobx `certified: true`, RunStatus `verified`) or matched the reference digest | process wall | yes |
| `completed-unverified` | a completion with neither | process wall | yes |
| `timeout` | the harness's wall cap, or an in-solver time stop | none; `censored_at_ms` = the cap | no |
| `memory-refusal` | a typed in-solver resource refusal (`StopKind::Resource`: matrix, live-entry, live-byte, batch or basis-size limits) | none | no |
| `rss-limit` | the external `rss-guard` kill | none | no |
| `unsupported` | a typed refusal before work (`Unsupported`, `refused`) | none | no |
| `process-failure` | a nonzero exit that is not a cap or guard, a child-reported failure, or a stop the classifier cannot name | none | no |
| `incorrect-output` | a rejected certificate, or a basis digest different from the reference | none | no |
| `not-run` | a cancelled attempt | none | no |

- **Censoring.** A censored attempt (`timeout`) records the cap C, never its wall. An in-solver time
  stop is censored at the job's cap too, because the comparison is at C.
- **Mismatches.** A digest mismatch overrides any runtime verdict. A missing digest convicts
  nothing: the attempt stays at the status it already had, which is `completed-unverified` unless
  its own check passed.

### 8.2 What a child reports

Every key below is optional. A child reporting none of them reads as a completion when it exits 0,
which is what every attempt was before this schema.

| Key | Values |
|---|---|
| `selection_outcome` | `complete`, `unsupported`, `memory-refusal`, `time-stop`, `incorrect-output`. Any other value is refused |
| `reason` | free text, kept on the record |
| `verified` | `true` when the arm's own runtime check passed |
| `acceptance` | `deterministic`, `certified-randomized`, `probabilistic` (the #1029 acceptance modes, `adaptive-selection-contracts.md` §8.4) |
| `costs_ns` | `{feature, inference, probe, discarded, conversion, verification, fallback}` charged to the arm, plus `audit`, which is recorded and never charged |
| `basis_sha256` | compared with `--references` |

Without `selection_outcome`, existing shapes are read as follows:

- **m33_qualify's `status` and `error`.**
  - `refused` → `unsupported`.
  - `stopped` → named from the `F4Error` or `SigF4Error` Debug variant: a resource limit, a time
    limit, `CertificationFailed` (→ `incorrect-output`) or `Unsupported`.
- **The external contract's RunStatus tags.**
  - `verified` → `completed-verified`.
  - `unsupported` → `unsupported`.
  - `failed` → `process-failure`.
  - `stopped-by-limit` → split on the Display text. A wall budget names milliseconds; any other
    limit is a resource refusal.
- **The grobx driver's `stopped`** (`deadline`, `memory` or `cancel`) and `certified` fields.

Two caveats:

- `outcome` is **not** read. `r1cs_import` and `whole_route` already use that key with their own
  vocabularies.
- The grobx driver refuses an unsupported cell with a nonzero exit, so through `bench-job` that is
  `process-failure`. Reporting it as `unsupported` needs the driver to exit 0 with
  `selection_outcome`, which is driver work (#987's scope).

### 8.3 Cost accounting

- **A policy's cost** is the process wall of every attempt it made, including discarded and
  fallback attempts. The in-process components in `costs_ns` are attribution *within* that wall,
  not additions to it:
  - feature extraction, inference, probes, discarded work, conversion and fallback;
  - runtime verification that the arm's guarantee requires.
- **The independent-reference audit** (digest comparison, normally offline) is common to every arm.
  It is recorded under `audit` and never charged.
- **Identity on every record.** The arm's `contract` and `configuration`, and the instance's
  `lineage`, come from the manifest (§7). The binary hash, commit, build, cpus and `cpu-context`
  are already on the attempt's metadata. Which lineage keys are required is #1005's decision; this
  schema carries whatever the manifest states.
