# Giac modular basis adapter and acceptance cohort (#740)

**Measured at:** `fa0790de` (Rust source), based on `55fef8d9`, 2026-11-13.
The [source recovery patch](../../research/giac/source.patch) and
[manifest](../../research/giac/manifest.json) bind the compiled code, harness and
engine binaries, compiler/flags, lockfile, loaded libraries and input digests.
The Giac engine is the pinned upstream Debian package **2.0.0-3**, reporting
Giac 2.0.0; its compiler settings/ISA are unspecified. The Rust harness's fat-LTO,
single-codegen-unit, x86-64-v3 settings must not be attributed to Giac.

## Implemented contract

`GiacSolver` is behind the existing `external-runners` feature, adds no Cargo
dependency and invokes the GPL executable as a separate supervised process.
The registered task is a complete monic reduced grevlex basis over a prime
`2 <= p < 2^31`, using the documented modular route. The adapter registers at
most fifteen variables and 16-bit input degrees; this does not describe every
algorithm Giac offers. Other tasks/orders, extension fields, larger primes and
unrepresentable interchange syntax return capability refusals before a solve.

The generated script assigns the requested thread count, uses
`proba_epsilon=0`, coerces the generator vector modulo p, echoes those parsed
polynomials back over the integers with `%0`, and calls
`gbasis(input, variables, revlex)`. Whole-identifier renaming keeps `x1` separate
from `x10` and avoids clashes with interpreter constants and adapter variables.
The parser requires unique field/worker/count markers, all generator echoes,
the entire basis and a completion marker. A zero exit code alone is insufficient.

Each accepted answer must agree with independent Singular on every coefficient
of the full reduced basis. Singular script generation and parsing are reused,
while the verifier runs through its own direct-child supervisor so both wall
and RSS ceilings apply and the complete reference output is retained. A stopped
or failed verifier cannot produce a verified Giac row. Quotient dimension and
leading ideal are taken from the exactly matched independent result, not guessed
from Giac's first printed term. Verification duration is recorded separately;
full parent wall includes probes, Giac, checking and serialization.

The [guide](../guide/external-engines.md#giac-modular-grevlex-comparand) documents
installation and `ZEEBRA_GIAC`, `ZEEBRA_GIAC_LIBRARY_PATH` and `ZEEBRA_SINGULAR`.
A child-only library-path override isolates the extracted Debian Giac runtime
from the system Singular libraries. The pinned package and its checksums are
in [external comparands](external-comparands.md#giac-200-modular-subprocess).

## Bounded experiment and interpretation

The [predeclared plan](../../research/giac/PLAN.md) selects frozen
`mq-random-10`, `katsura-11` and `cyclic-5` at both board primes, workers one
and four, with five interleaved fresh processes per case/cohort. The existing
`groebner_comparison` row runner retains board records and full outputs, with
`tools/external/grobx-cohort.py`'s existing 185-second / 2 GiB parent watchdog.
Giac and the sequential independent verifier each receive 60 seconds / 2 GiB
RSS. Whole campaign cap is 3000 seconds. CPU2 and CPU2–5 are physical-core
cohorts verified against topology; load and actual affinity are retained under
the repository's shared benchmark lock.

The completed campaign retains **62 attempts**: 40 verified MQ/Cyclic answers,
20 Katsura-11 wall-clock stops and two wide-field capability refusals. No full
basis verification failed. Every Katsura stop occurred in the Giac computation,
before independent checking. The separate failed metadata preflight ran no solver.

See the generated [result table](../../research/giac/table.md). Columns separate
Giac's child wall/RSS, independent checking time and full parent wall. No
engine-internal solve time is inferred from script chatter. The raw compressed
cohort retains CPU time and its measurement basis, child RSS basis, complete
answers, stops, startup observations and exact independent output. The offline
checker rehashes ordered input identities, checks both parsed generator systems,
compares full bases and rejects relabeled tasks/orders or missing evidence.
RSS is supervisor-sampled kernel high-water data; very late peaks may be missed.

Katsura rows that reach the declared budget remain explicit limit stops. They
cannot supply a completion time, an invariant-agreement claim or a speedup
inferred from a timeout. The issue permits a documented blocker as an alternate
acceptance result; the bounded Katsura attempts and commands make that resource
limit reproducible. MQ and Cyclic rows are accepted only after exact verification.
This engine version and resource budget do not establish universal Giac limits.

Wide-field controls retain capability refusals at 2^64−353 and 2^64−59. They do
not time wide-field arithmetic. API tests also cover the Goldilocks refusal.
These are bounds of the registered modular route; no performance ranking may
use them as failed timed solves.

There are no matched-build cross-engine ratios in this cohort. Historical
Zeebra/msolve/etc. rows differ in source/build/policy and must not become
comparison denominators. Small Cyclic controls also include a material interpreter
startup floor. These two worker counts do not establish a scaling knee or a
competitive target for Zeebra; #739 owns the broader comparand scaling study.
The costs of exact verification remain visible for any later adoption discussion.

## Reproduction and checks

The [retained README](../../research/giac/README.md) contains exact build/run
commands and source reconstruction from a main-reachable base. The first metadata
preflight failed before any solver attempt because Fedora's `Singular` command
is an `exec` wrapper; its note and lock log are retained. The capture uses the
explicit native executable and `SINGULAR_DATA_DIR=/usr/share`.

Red–Green tests preceded adapter behavior, CLI worker/memory handling, bounded
verification and artifact checking. The focused native checks include zero/unit
ideals and both board primes, missing executables, incomplete reports, changed
coefficients, unsupported syntax/fields/tasks and verifier memory refusal.
The full external-runner suite, sweep tests, no-default-feature build and
all-target/all-feature Clippy were checked. Existing CI runs Rust tests; its
artifact job now independently regenerates the Giac table without native engines.
Production F4 arithmetic and its serial defaults are unchanged. Multiworker sweep
requests for the configured serial Zeebra engine return a capability refusal.
