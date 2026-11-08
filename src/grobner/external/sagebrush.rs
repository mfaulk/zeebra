//! Sagebrush as an [`ExternalSolver`], driven through the provisioned `sagebrush-gb-driver`.
//!
//! # Maturity: run it, and do not quote it as a baseline yet
//!
//! Sagebrush is the one permissively-licensed comparand in M25 (§ Licensing below), which makes it
//! the only one whose code Zeebra could lawfully reuse — and that is exactly why its *correctness*
//! has to be settled before its *speed* is quoted. What the source supports, at
//! `86d9f1c787030752dcaab1ddb8d99cf1b7fa5e1b`:
//!
//! * The repository is five weeks old (first commit 2026-10-02), 6864 commits, and **every
//!   `engine/*` crate is `version = "0.1.0"`** with no crate-level git tag.
//! * `engine/mpoly/src/f4.rs` is 1318 lines and carries **six** `#[test]`s; `f4q.rs` (913 lines,
//!   the default route over Q) and `sigf4.rs` carry **none**.
//! * The repository's Sage and Magma oracle trees are substantial — `sage-tests/` has 267 entries
//!   — but **two** of those files mention `groebner_basis` at all and both are two-variable toys;
//!   `magma-tests/` has no Gröbner test. There is no committed oracle run on cyclic-n or
//!   katsura-n.
//! * `engine/mpoly/src/sigf4.rs:28` claims validation "against Singular"; no such test, script or
//!   recorded output exists in the tree.
//!
//! Against that, the correctness evidence this adapter establishes. `tests/external_comparands.rs`
//! checks Sagebrush against Zeebra **term for term, every coefficient included** — not merely on
//! [`Invariants`] — and it agrees on the provisioning smoke system, on katsura-3/4/5, on
//! cyclic-3/4/5 including positive-dimensional cyclic-4, and on katsura-4 at a 62-bit prime.
//! Eight instances across three families and two characteristics, where the provisioning record
//! had one.
//!
//! So: the F4 is real, literature-cited and free of stub markers, and it now agrees with an
//! independent implementation wherever it has been asked to. What has *not* changed is the
//! structural case above — five weeks of history, nothing versioned, six tests on the F4 path, no
//! committed oracle run on a system large enough to exercise matrix elimination. **A row from this
//! adapter is [`RunStatus::Complete`], never self-certified, and should carry the maturity caveat
//! into the results table.** A fast wrong answer is not a competitive result, and eight agreeing
//! instances is evidence rather than a guarantee.
//!
//! # What the driver exposes
//!
//! Sagebrush builds no Gröbner CLI: `engine/cli` depends on four crates that do not include
//! `mpoly` and exposes no entry point. The provisioned `sagebrush-gb-driver` — Zeebra's own MIT
//! code, built by `tools/external/provision.sh` against the pinned clone — reads an msolve-format
//! file and calls into `sagebrush_mpoly` on two selectable axes:
//!
//! | `--route` | `--order` | entry point | task |
//! |---|---|---|---|
//! | `f4` | `degrevlex`, `deglex`, `lex` | `f4::groebner_p` | [`Task::ReducedGrobnerBasis`], [`Task::LexBasis`] |
//! | `fglm` | `lex` | `fglm::groebner_fglm` | [`Task::LexBasisByConversion`] |
//!
//! The lex basis under `f4` is the engine's own homogenize → DegLex → dehomogenize → re-reduce
//! route (`engine/mpoly/src/f4.rs:491-547`); under `fglm` it is an order conversion from a
//! degrevlex basis (`engine/mpoly/src/fglm.rs:325`). **The two routes are separate tasks and must
//! not share a column** — that is what [`Task::LexBasisByConversion`] exists for — and Sagebrush
//! is the only comparand here that offers both, Groebner.jl 0.10.11 having no FGLM at all.
//!
//! **Sagebrush has a task-specific field ceiling, and it is eight times narrower than the basis
//! bound.** [`MAX_CHARACTERISTIC`] is the bound on `f4::groebner_p`; `fglm.rs:329` caps the FGLM
//! route at [`FGLM_MAX_CHARACTERISTIC`] = `2^31`. Declaring only the basis bound would let a sweep
//! run a worker into its wall limit and record [`LimitStop`] where the truth is [`Unsupported`] —
//! a timing-adjacent outcome for what is actually a capability gap, which is the one confusion
//! this contract exists to prevent. Worse, `fglm.rs:329` returns `Ok(None)` past the cap, the
//! *same* value it returns for an ideal that is not zero-dimensional, so above the bound "no
//! answer" stops meaning anything in particular; the driver refuses the modulus itself for that
//! reason. msolve has the same shape and worse consequences: its eliminant ceiling is
//! `p < 1515531529` and above it the sparse-FGLM failure is laundered into a retry loop with no
//! exit. Groebner.jl, measured, has **no** task-specific ceiling: its lex route is the same F4
//! under a different ordering and returns the same quotient dimension at every prime the basis
//! route accepts, up to `2^64 - 59`.
//!
//! # The quotient dimension is the driver's own, which is what makes it worth having
//!
//! `fglm_p` computes the staircase length at `fglm.rs:97` and exposes only the boolean
//! `zero_dimensional`, so there is nothing to read out of Sagebrush. The driver counts the
//! monomials no leading monomial divides and reports `#quotient dimension:`, which is the
//! definition rather than a restatement — so checking it against Zeebra's is a genuine third
//! shared invariant on top of the leading monomials and the cardinality, taking
//! [`Invariants::overlap`] against Zeebra from 2 to 3. A positive-dimensional ideal is reported as
//! `-1`, the convention Singular's `vdim` already uses, and read here as "not reported".
//!
//! # The generator echo, checked on every run
//!
//! The driver prints one `#gen` line per generator **before** it calls into Sagebrush, rendered
//! from the packed polynomials it is about to hand over — so the echo is a round trip through the
//! driver's own parser and packer rather than a copy of its input, and
//! `check_echoed_generators` compares it against [`Instance::system`] as a set of canonical term
//! multisets.
//!
//! This covers the one failure mode **cross-validation cannot catch**. Every engine is handed the
//! same bytes, so an input that is misread is misread identically everywhere, and the engines then
//! agree with each other while all of them answer a different question — and agreement is the
//! instrument this module relies on. The live instance of it is the `x1` / `x10` prefix collapse at
//! ten or more variables, which the corpus's fourteen-variable rungs reach. A [`RunStatus::Complete`]
//! on one of those is therefore *itself* the proof that the two names were read apart; before this
//! the claim rested on a single behavioural test over a single system.
//!
//! [`DRIVER_CONTRACT`] is why the check cannot quietly lapse against an older installed binary.
//!
//! # The leading-monomial trap, handled in the driver
//!
//! Sagebrush keeps a polynomial's terms in decreasing **lex** order of the packed exponent word
//! whatever the monomial order is (`engine/mpoly/src/order.rs:58-60` puts variable 0 in the
//! highest field, so a plain unsigned word compare *is* a lex compare). For degrevlex the first
//! stored term is therefore **not** the leading term: on the provisioning smoke system the second
//! basis element stores as `x*z + … + z^4 + …`, whose degrevlex leading monomial is `z^4`.
//!
//! The driver re-sorts every polynomial under the requested order and prints the leading terms in
//! a `--- leading monomials ---` section, so this adapter reads that section rather than taking a
//! first term. Taking `exps[0]` yields a plausible-looking and entirely wrong leading-monomial
//! list — the first version of the driver did exactly that, and only the four-way agreement caught
//! it.
//!
//! The ordering key is the driver's own `order_key`, over exponent vectors rather than packed
//! words, because the FGLM route's exponents do not pack (`fglm.rs:16`: a target basis can carry
//! degrees "far beyond the packed words") and packing them back would silently truncate them. That
//! makes it a *second* implementation of the engine's `Packing::key`
//! (`engine/mpoly/src/order.rs:104-125`, which builds degrevlex as degree-then-complemented-and-
//! field-reversed), so the driver asserts the two rank every pair of 625 monomials identically
//! under all four orders — this being precisely the function whose first version got degrevlex
//! wrong.
//!
//! # Above `p = 2^31` nothing can check this tool
//!
//! msolve and Singular both stop at `p <= 2^31 - 1`. Sagebrush and Groebner.jl are the only
//! comparands that accept a larger prime, so between `2^31` and this adapter's
//! [`MAX_CHARACTERISTIC`] the only available corroboration is Groebner.jl — two implementations
//! agreeing with each other and nothing else. Such a run stays [`RunStatus::Complete`]. Combined
//! with the maturity note above, a 64-bit Sagebrush row is the weakest evidence this module
//! produces and must be labelled as such.
//!
//! # Two measurement caveats that are properties of the engine
//!
//! 1. **Above `p = 2^31` the elimination is single-threaded.** `engine/mpoly/src/f4.rs:219`
//!    switches on the modulus: below 2^31 it uses the Faugère–Lachartre sparse elimination in
//!    `engine/arith/src/spelim.rs`, which is row-parallel past 32 rows (`f4.rs:317`); at or above
//!    2^31 it uses the dense accumulator in `reduce_rows` (`f4.rs:233-278`), which has no
//!    parallelism at all. A `workers = 64` figure at a 64-bit prime is therefore a serial figure,
//!    and comparing it with a `workers = 64` figure at a 31-bit prime compares two different
//!    implementations.
//! 2. **The elimination strategy is chosen by a cost model that reads `is_x86_feature_detected!
//!    ("avx2")`** (`engine/arith/src/spelim.rs:381-384`), so the same input can take a different
//!    route on different hardware. This adapter deliberately **does not** pin `SB_F4_FL`: that
//!    would measure something no user of Sagebrush gets. It records the machine instead, and
//!    refuses to run if the variable is already set — see [`PINNED_SWITCHES`].
//!
//! # Licensing
//!
//! `NOTICE.md:3` is `Copyright (c) 2026 SageMath, Inc.`, `NOTICE.md:5-9` grants Apache-2.0 **or**
//! MIT at the licensee's option, and `engine/mpoly/Cargo.toml:5` is `license = "MIT OR
//! Apache-2.0"`. `NOTICE.md:16-18` states that nothing in Sagebrush is derived from GPL software.
//! So this is the "reuse permitted" class of `docs/research/external-provenance-policy.md` §2 —
//! and **nothing is reused here**: the driver calls a public library function across a crate
//! boundary and copies no code, so §8.1's notice obligation is not engaged. See
//! `docs/research/sagebrush-implementation.md` for what reuse *would* require.

use std::time::Duration;

use super::{
    contract::{
        generators_agree, Answer, ExternalSolver, Instance, Invariants, LimitStop, Limits,
        Measurement, RunFailure, RunReport, RunStatus, Support, Task, ToolVersion, Unsupported,
    },
    process::{read_output, Invocation, Supervisor},
};
use crate::MonomialOrder;

/// The commit the provisioned driver was built against.
///
/// **Not self-reported.** The driver prints an engine name and no version, and Sagebrush has no
/// crate-level tag to report — every `engine/*` crate is `0.1.0`. This constant is the pin
/// asserted by `tools/external/provision.sh`, carried into [`ToolVersion::build`] so that a record
/// says which tree produced it, and it is the adapter's claim rather than the tool's.
pub const PROVISIONED_COMMIT: &str = "86d9f1c787030752dcaab1ddb8d99cf1b7fa5e1b";

/// The largest modulus Sagebrush's own entry point accepts.
///
/// `engine/mpoly/src/lib.rs:1552-1554` rejects anything outside `[2, 2^62)`:
///
/// ```text
/// if pm < 2 || pm >= 1 << 62 {
///     return Err("the modulus must be in [2, 2^62)".into());
/// }
/// ```
///
/// and `engine/mpoly/src/sparse.rs:5` documents `Fp` as "GF(p), p < 2^62". The gate sits on
/// `call()`, which the driver bypasses by calling `f4::groebner_p` directly — so **this adapter
/// has to enforce Sagebrush's own bound on Sagebrush's behalf**, and that is why it is a constant
/// here. Past it the failure is silent rather than reported: `ZPoly::reduce_mod`
/// (`engine/mpoly/src/lib.rs:1111`) reduces by `p as i64`, which is negative for `p >= 2^63`, and
/// `sparse.rs:57-63` adds two residues in a `u64` without a widening step.
///
/// This is wider than msolve's and Singular's shared 2^31 ceiling
/// (`docs/research/external-comparands.md` §3.3, §6.2) and narrower than Groebner.jl's
/// [`MAX_CHARACTERISTIC`](super::groebner_jl::MAX_CHARACTERISTIC).
pub const MAX_CHARACTERISTIC: u64 = 1 << 62;

/// The largest modulus the **FGLM** route accepts, which is not [`MAX_CHARACTERISTIC`].
///
/// `engine/mpoly/src/fglm.rs:329` is the gate:
///
/// ```text
/// if n == 0 || (p > 0 && p >= 1 << 31) {
///     return Ok(None);
/// }
/// ```
///
/// `Ok(None)` is also what `fglm_p` returns for an ideal that is **not zero-dimensional**, so past
/// this bound the two cases are indistinguishable in the return value — which is why the driver
/// refuses an out-of-range modulus before calling, and why this bound is declared here rather than
/// discovered. An eighth of the basis route's, and it applies only to
/// [`Task::LexBasisByConversion`].
pub const FGLM_MAX_CHARACTERISTIC: u64 = 1 << 31;

/// The most variables the packed exponent representation can carry.
///
/// Sagebrush packs every exponent into one `u64` with `bits` bits each, `ZPoly` holding the
/// invariant `n * bits <= 64` (`engine/mpoly/src/lib.rs:100-101`), and `f4::bits_range`
/// (`engine/mpoly/src/f4.rs:660-666`) caps `bits` at `64 / n`. The top bit of every field is a
/// **guard bit** used for branchless divisibility and overflow detection
/// (`engine/mpoly/src/order.rs:69-72`, and `divides` at `f4.rs:76-79`), so the usable exponent
/// range is `2^(bits - 1)`, not `2^bits`. At `n > 32` that leaves `bits = 1`, one guard bit and no
/// exponent — nothing above degree 0 can be represented.
///
/// **Useful capacity degrades well before this bound**, and that is not a capability statement: an
/// instance inside the bound whose exponents will not pack comes back as Sagebrush's own
/// `exponents too large to pack` (`f4.rs:680-682`, `:694-701`), which this adapter reports as
/// [`RunFailure::Reported`]. A bound in `supports` must describe what the tool declares, not
/// predict what a run will do.
pub const MAX_VARIABLES: usize = 32;

/// The most variables the **direct lex** route can carry, which is one fewer than
/// [`MAX_VARIABLES`].
///
/// A lex basis is computed by homogenizing, so the elimination runs in `n + 1` variables
/// (`engine/mpoly/src/f4.rs:497-499` returns `Overflow` when `(n + 1) * bits > 64`, and
/// `f4::bits_range` caps `bits` at `64 / (n + 1)` for a lex order). With the guard bit that leaves
/// `bits >= 2`, hence `n <= 31` — the same arithmetic that gives [`MAX_VARIABLES`] its 32, applied
/// to the extra homogenizing variable.
///
/// Applies to [`Task::LexBasis`] only. [`Task::LexBasisByConversion`] does **not** pay it: FGLM
/// takes its source basis in degrevlex and converts over exponent vectors rather than packed
/// words, so it stays inside [`MAX_VARIABLES`].
pub const MAX_VARIABLES_LEX: usize = 31;

/// Environment variables that change which algorithm Sagebrush runs, or what it prints.
///
/// Every one is read with `env::var(..).is_ok()` — **truthy if set, so `SB_SIGF4=0` enables the
/// signature path** — except `SB_F4_FL`, which is value-compared. [`Invocation`] can set a child's
/// variables but not clear them, so an inherited one cannot be undone from here; the adapter
/// therefore refuses to run rather than produce a figure for an engine configuration it did not
/// choose.
///
/// | variable | site | effect |
/// |---|---|---|
/// | `SB_SIGF4` | `engine/mpoly/src/f4.rs:484` | tries the experimental signature-based F4 first |
/// | `SB_SIG_NOSYZ` | `engine/mpoly/src/sigf4.rs:170` | disables syzygy-signature pruning |
/// | `SB_SIG_NOREW` | `engine/mpoly/src/sigf4.rs:171` | disables the rewrite criterion |
/// | `SB_SIG_NOZERO` | `engine/mpoly/src/sigf4.rs:327` | stops recording zero reductions as syzygies |
/// | `SB_F4_FL` | `engine/mpoly/src/f4.rs:325-329` | overrides the elimination cost model |
/// | `SB_F4_DEBUG` | 24 sites from `engine/mpoly/src/f4.rs:196` | writes a stderr trace |
/// | `SB_F4_SHAPE` | `engine/mpoly/src/f4.rs:310` | writes matrix shape statistics |
///
/// The last two are a parsing hazard as much as a measurement one: the supervisor sends both of
/// the child's streams to one file, so a trace interleaves with the basis the adapter parses.
///
/// Each entry carries its effect as well as its name, because that text becomes
/// [`RunFailure::Environment`]'s `detail` — and a refusal that says only *which* variable is set
/// tells an operator to unset it without letting them judge whether it should have been.
pub const PINNED_SWITCHES: &[(&str, &str)] = &[
    (
        "SB_SIGF4",
        "tries the experimental signature-based F4 first (engine/mpoly/src/f4.rs:484)",
    ),
    (
        "SB_SIG_NOSYZ",
        "disables syzygy-signature pruning (engine/mpoly/src/sigf4.rs:170)",
    ),
    (
        "SB_SIG_NOREW",
        "disables the rewrite criterion (engine/mpoly/src/sigf4.rs:171)",
    ),
    (
        "SB_SIG_NOZERO",
        "stops recording zero reductions as syzygies (engine/mpoly/src/sigf4.rs:327)",
    ),
    (
        "SB_F4_FL",
        "overrides the elimination cost model (engine/mpoly/src/f4.rs:325-329)",
    ),
    (
        "SB_F4_DEBUG",
        "writes a trace into the stream the basis is parsed from \
         (24 sites from engine/mpoly/src/f4.rs:196)",
    ),
    (
        "SB_F4_SHAPE",
        "writes matrix shape statistics into the stream the basis is parsed from \
         (engine/mpoly/src/f4.rs:310)",
    ),
];

/// The variable Sagebrush takes its worker count from.
///
/// `engine/mpoly/src/lib.rs:1005` parses it as an integer and falls back to
/// `available_parallelism()` — **all 128 hardware threads on the provisioning machine** — when it
/// is unset. An unflagged Sagebrush run is therefore fully parallel where an unflagged msolve run
/// is serial (`docs/research/external-comparands.md` §3.6, §5.3), so this is set on every run.
const THREADS_VARIABLE: &str = "SAGEBRUSH_THREADS";

/// The separator the driver prints between the basis and its leading monomials.
const LEADING_SEPARATOR: &str = "--- leading monomials ---";

/// The driver output format this adapter requires, which the driver prints as
/// `#driver contract:`.
///
/// # Why a version and not a tolerated absence
///
/// The driver lives in the provisioning prefix, not in this repository, so an installed binary can
/// be older than the adapter reading it. The obvious accommodation — check the generator echo only
/// when `#gen` is present — is **a check that silently stops checking**: against an older binary
/// every run would pass having verified nothing, and the one failure mode the echo exists to catch
/// is precisely the one that produces a well-formed answer to a different question. So the marker
/// is *required*, and a driver that cannot produce it fails loudly with
/// [`RunFailure::Incomplete`] telling the operator to re-run `tools/external/provision.sh`.
///
/// | contract | what it added |
/// |---|---|
/// | 1 | the degrevlex basis, its leading monomials, and the echoed characteristic, variable order and monomial order |
/// | 2 | `--order` / `--route`, `#route:`, `#quotient dimension:`, and the `#gen` generator echo |
/// | 3 | `#isa floor:`, the comparand's own compile-time ISA floor (#385) |
///
/// Contract 3 is also what stops a **stale binary** being measured against the matched build
/// configuration #385 introduced: a driver installed before that change reports no floor and is
/// refused here, rather than producing a row that reads as `x86-64-v3` because the script now says
/// so. Re-run `tools/external/provision.sh`.
pub const DRIVER_CONTRACT: u32 = 3;

/// Sagebrush's name for one of Zeebra's monomial orders, which is what the driver's `--order`
/// takes and what its `#monomial order:` header echoes.
///
/// `deglex` and Zeebra's `grlex` are the same order under two names, and conflating the *names*
/// with the orders is how a basis under the wrong order gets compared: the echo check in
/// [`SagebrushSolver::answer`] compares against this, not against Zeebra's tag.
fn sagebrush_order(order: MonomialOrder) -> &'static str {
    match order {
        MonomialOrder::Lexicographic => "lex",
        MonomialOrder::GradedLexicographic => "deglex",
        MonomialOrder::GradedReverseLexicographic => "degrevlex",
    }
}

/// The `(--order, --route)` the driver is invoked with for `task` on `instance`.
///
/// The target order is the **task's**, not always the instance's: a conversion task is a lex basis
/// however the instance declares itself, exactly as Singular's adapter computes its source basis
/// under `dp` whatever the instance says, because the conversion is what is being measured.
fn driver_arguments(instance: &Instance, task: Task) -> (&'static str, &'static str) {
    match task {
        Task::LexBasisByConversion => ("lex", "fglm"),
        Task::LexBasis => ("lex", "f4"),
        _ => (sagebrush_order(instance.order), "f4"),
    }
}

/// The first identifier in `instance`'s generators that is not a declared variable.
///
/// A generator naming a variable the ring does not declare is an **input the tool cannot
/// represent**, and it is knowable before anything runs — so it belongs in `supports` as
/// [`Unsupported::Representation`] rather than arriving as a failed run.
///
/// The check exists because of how badly the neighbouring tool handles it: msolve **silently drops
/// the factor** (`iofiles.c:57-62` has no `else`), so `x*z-1` with only `x,y` declared reads as
/// `x-1`, exits 0, and reports `#invalid equations 0` — a well-formed basis of a different ideal.
/// Measured here, neither of this module's two tools shares that behaviour: the Sagebrush driver
/// exits 1 with `not a variable or integer: "z"`, and an unbound name in the generated Julia is an
/// `UndefVarError`. Both are loud. The check is still worth making, because a capability gap
/// reported as a capability gap costs nothing and a loud failure is still a failure.
fn undeclared_identifier(instance: &Instance) -> Option<String> {
    for generator in &instance.system {
        let mut name = String::new();
        // One pass, accumulating identifier characters and flushing at every separator. An
        // identifier is matched whole, which is the same discipline that keeps `x1` and `x10`
        // apart.
        for character in generator.chars().chain(std::iter::once('+')) {
            if character.is_ascii_alphanumeric() || character == '_' {
                name.push(character);
                continue;
            }
            if !name.is_empty() {
                let token = std::mem::take(&mut name);
                // A numeric literal is a coefficient or an exponent, not a variable.
                if token.parse::<u128>().is_err() && !instance.variables.contains(&token) {
                    return Some(token);
                }
            }
        }
    }
    None
}

/// How a [`SagebrushSolver`] reads one environment variable, as a value and not a verdict.
///
/// Indirection rather than a direct `env::var_os`, so that a test can exercise the refusal path
/// without a `set_var` — which under `cargo test`'s one-process-many-threads suite races every
/// concurrent reader of the environment and leaks the value into whichever test is looking at that
/// moment (#418). The probe yields the *value* so that "truthy if set" stays decided in
/// [`SagebrushSolver::inherited_switch`], which is the code that has to get it right.
type SwitchProbe = fn(&str) -> Option<std::ffi::OsString>;

/// The real probe: the harness's own environment.
fn environment_switch(name: &str) -> Option<std::ffi::OsString> {
    std::env::var_os(name)
}

/// Sagebrush driven as a competitive solver, through the provisioned driver binary.
#[derive(Clone, Debug)]
pub struct SagebrushSolver {
    binary: String,
    work_dir: std::path::PathBuf,
    version: Option<ToolVersion>,
    runs: u64,
    switches: SwitchProbe,
}

impl SagebrushSolver {
    /// A solver over the driver at `binary`, with scratch files under `work_dir`.
    ///
    /// # Errors
    /// [`RunFailure::Io`] if the scratch directory could not be created. A *missing* driver is not
    /// reported here, because nothing has been run yet: it surfaces from
    /// [`ExternalSolver::probe_version`] or [`ExternalSolver::run`] as
    /// [`RunFailure::Unavailable`].
    pub fn new(
        binary: impl Into<String>,
        work_dir: impl Into<std::path::PathBuf>,
    ) -> Result<Self, RunFailure> {
        let work_dir = work_dir.into();
        std::fs::create_dir_all(&work_dir)?;
        Ok(Self {
            binary: binary.into(),
            work_dir,
            version: None,
            runs: 0,
            switches: environment_switch,
        })
    }

    /// The same solver reading its [`PINNED_SWITCHES`] through `probe` instead of the environment.
    #[cfg(test)]
    fn with_switch_probe(mut self, probe: SwitchProbe) -> Self {
        self.switches = probe;
        self
    }

    /// A solver configured from the environment `tools/external/env.sh` exports.
    ///
    /// `ZEEBRA_SAGEBRUSH_DRIVER` names the binary and defaults to `sagebrush-gb-driver`, which
    /// `env.sh` puts on `PATH`.
    ///
    /// # Errors
    /// As [`Self::new`].
    pub fn from_env(work_dir: impl Into<std::path::PathBuf>) -> Result<Self, RunFailure> {
        let binary = std::env::var("ZEEBRA_SAGEBRUSH_DRIVER")
            .unwrap_or_else(|_| "sagebrush-gb-driver".to_string());
        Self::new(binary, work_dir)
    }

    /// The scratch paths for the next run: the input file and the file both streams go to.
    fn scratch(&mut self, tag: &str) -> (std::path::PathBuf, std::path::PathBuf) {
        self.runs += 1;
        let stem = format!("{}-{}", tag, self.runs);
        (
            self.work_dir.join(format!("{}.ms", stem)),
            self.work_dir.join(format!("{}.out", stem)),
        )
    }

    /// The input file: msolve's three-part format, which the driver reads.
    ///
    /// Variables comma-separated on line 1 **in the instance's order**, which is what defines the
    /// monomial order and which the driver maps positionally onto exponent fields; the
    /// characteristic on line 2; then the generators comma-separated with no trailing comma
    /// (`docs/research/external-comparands.md` §3.1).
    fn input(instance: &Instance) -> String {
        format!(
            "{}\n{}\n{}\n",
            instance.variables.join(","),
            instance.field.characteristic,
            instance.system.join(",\n")
        )
    }

    /// An invocation of the driver on `input` for `task`, with the worker count set.
    ///
    /// The order and the route are passed explicitly even when they are the driver's defaults, so
    /// that the command line recorded on the report says which question was asked.
    fn invocation(
        &self,
        input: &std::path::Path,
        output: &std::path::Path,
        instance: &Instance,
        task: Task,
        limits: &Limits,
    ) -> Invocation {
        let (order, route) = driver_arguments(instance, task);
        Invocation::new(&self.binary, &self.work_dir, output)
            .arg(input)
            .arg("--order")
            .arg(order)
            .arg("--route")
            .arg(route)
            .env(THREADS_VARIABLE, limits.workers.max(1).to_string())
    }

    /// The first [`PINNED_SWITCHES`] entry `probe` reports set, with its effect.
    ///
    /// Presence and not value: every one of these but `SB_F4_FL` is read with
    /// `env::var(..).is_ok()`, so `SB_SIGF4=0` *enables* the signature path.
    fn inherited_switch(probe: SwitchProbe) -> Option<(&'static str, &'static str)> {
        PINNED_SWITCHES
            .iter()
            .copied()
            .find(|(name, _)| probe(name).is_some())
    }

    /// Parse the driver's output into an answer, checking its echoed headers against the request.
    ///
    /// The headers are the driver telling the adapter what it actually did, and checking them is
    /// what catches a mismatch that would otherwise produce a basis under the wrong order or in
    /// the wrong variables — the failure mode that does not announce itself.
    fn answer(&self, output: &str, instance: &Instance, task: Task) -> Result<Answer, RunFailure> {
        let header = |name: &'static str| -> Result<&str, RunFailure> {
            output
                .lines()
                .find_map(|line| line.strip_prefix(name))
                .map(str::trim)
                .ok_or(RunFailure::MissingMarker {
                    marker: name.to_string(),
                })
        };

        // Before anything else: a driver too old to echo its generators cannot be checked, and an
        // unchecked run is the one this adapter must not report as a result.
        let contract = header("#driver contract:")?;
        let contract: u32 = contract.parse().map_err(|_| RunFailure::Unparsable {
            marker: "#driver contract:".to_string(),
            value: contract.to_string(),
        })?;
        if contract < DRIVER_CONTRACT {
            return Err(RunFailure::Incomplete {
                detail: format!(
                    "the installed driver speaks contract {} and this adapter requires {}; \
                     re-run tools/external/provision.sh to rebuild sagebrush-gb-driver",
                    contract, DRIVER_CONTRACT
                ),
            });
        }

        let characteristic = header("#field characteristic:")?;
        if characteristic != instance.field.characteristic.to_string() {
            return Err(RunFailure::SelfInconsistent {
                detail: format!(
                    "the driver read characteristic {} where the instance declares {}",
                    characteristic, instance.field.characteristic
                ),
            });
        }
        let variables = header("#variable order:")?;
        if variables != instance.variables.join(", ") {
            return Err(RunFailure::SelfInconsistent {
                detail: format!(
                    "the driver read variables {} where the instance declares {}",
                    variables,
                    instance.variables.join(", ")
                ),
            });
        }
        let (expected_order, expected_route) = driver_arguments(instance, task);
        let order = header("#monomial order:")?;
        if !order.starts_with(expected_order) {
            return Err(RunFailure::SelfInconsistent {
                detail: format!(
                    "the driver computed a {} basis, not {}",
                    order, expected_order
                ),
            });
        }
        // The route is the difference between `LexBasis` and `LexBasisByConversion`, and the two
        // produce the *same* basis — so nothing in the output but this line distinguishes a
        // direct lex F4 from an FGLM conversion, and a column that mixed them would compare two
        // complexities under one heading.
        let route = header("#route:")?;
        if !route.starts_with(expected_route) {
            return Err(RunFailure::SelfInconsistent {
                detail: format!(
                    "the driver took the {} route where {} asks for {}",
                    route, task, expected_route
                ),
            });
        }

        Self::check_echoed_generators(output, instance)?;

        let length = header("#length of basis:")?;
        let size: usize = length
            .split_whitespace()
            .next()
            .unwrap_or_default()
            .parse()
            .map_err(|_| RunFailure::Unparsable {
                marker: "#length of basis:".to_string(),
                value: length.to_string(),
            })?;

        let (basis, leading) = Self::split_body(output, size)?;
        let mut invariants = Invariants::none().with_leading_monomials(leading);
        // Negative is "no finite dimension to report" — `-1` a positive-dimensional ideal, `-2` an
        // enumeration the driver abandoned at its own ceiling. Both read as absent, which per
        // `Invariants` means "not reported" and never zero. A missing header is absent too, so a
        // driver built before this marker existed still parses.
        if let Some(dimension) = Self::quotient_dimension(output)? {
            invariants = invariants.with_quotient_dimension(dimension);
        }
        Ok(Answer::from_invariants(invariants).with_basis(basis))
    }

    /// Check that the system the driver parsed is the one that was sent, **as a set**.
    ///
    /// # Why this is a check and not a comment
    ///
    /// The driver prints `#gen` for each generator *before* it calls into Sagebrush, rendering the
    /// packed polynomials it is about to hand over — so the echo is a round trip through the
    /// driver's own parser and packer, not a copy of its input. It has to be checked on every run
    /// because of one failure mode **cross-validation cannot catch**: every engine is handed the
    /// same bytes, so an input that is misread is misread identically everywhere, and the engines
    /// then agree with each other while all of them answer a different question.
    ///
    /// The concrete instance of it is the `x1` / `x10` prefix collapse — see
    /// [`canonical_generator`](super::contract::canonical_generator) — and the corpus has fourteen-variable rungs, so a `Complete` status
    /// on one is now *itself* the proof that the two names were read apart. Previously that was
    /// pinned by a single behavioural test covering one system; this covers every run.
    ///
    /// The driver's parser is believed clean (it splits on `*`, then `^`, then matches the base
    /// against a variable name with an exact whole-string comparison, never a longest-prefix scan).
    /// This check is what makes that a per-run assertion rather than a belief, and it also catches
    /// a dropped generator, a packing that truncated an exponent, and a renderer change on
    /// Zeebra's side.
    ///
    /// # Errors
    /// [`RunFailure::Unparsable`] if the count and the lines disagree — a run killed between two
    /// `println!`s is a failure and not a shorter system. [`RunFailure::SelfInconsistent`] if the
    /// systems differ, which is what a tool contradicting its input *is*: nothing can be concluded
    /// about any other implementation from a run whose input was not the one requested.
    fn check_echoed_generators(output: &str, instance: &Instance) -> Result<(), RunFailure> {
        let reported = output
            .lines()
            .find_map(|line| line.strip_prefix("#generators:"))
            .map(str::trim)
            .ok_or(RunFailure::MissingMarker {
                marker: "#generators:".to_string(),
            })?;
        let count: usize = reported.parse().map_err(|_| RunFailure::Unparsable {
            marker: "#generators:".to_string(),
            value: reported.to_string(),
        })?;
        let echoed: Vec<String> = output
            .lines()
            .filter_map(|line| line.trim_start().strip_prefix("#gen "))
            .map(|generator| generator.trim().to_string())
            .collect();
        if echoed.len() != count || echoed.len() != instance.system.len() {
            return Err(RunFailure::Unparsable {
                marker: "#gen".to_string(),
                value: format!(
                    "{} echoed lines for a reported {} and a sent system of {}",
                    echoed.len(),
                    count,
                    instance.system.len()
                ),
            });
        }
        generators_agree(&instance.system, &echoed, instance.field.characteristic).map_err(
            |(sent, read)| RunFailure::SelfInconsistent {
                detail: format!("the driver read a different system: sent {sent}, read {read}"),
            },
        )
    }

    /// The driver's `#quotient dimension:`, or `None` when it reported no finite one.
    ///
    /// # Errors
    /// [`RunFailure::Unparsable`] if the marker is present but not an integer. Present-and-wrong is
    /// a different thing from absent, and silently reading it as absent would turn a driver defect
    /// into one missing invariant nobody notices.
    fn quotient_dimension(output: &str) -> Result<Option<usize>, RunFailure> {
        let Some(value) = output
            .lines()
            .find_map(|line| line.strip_prefix("#quotient dimension:"))
            .map(str::trim)
        else {
            return Ok(None);
        };
        let dimension: i64 = value.parse().map_err(|_| RunFailure::Unparsable {
            marker: "#quotient dimension:".to_string(),
            value: value.to_string(),
        })?;
        Ok(usize::try_from(dimension).ok())
    }

    /// The basis lines and the leading-monomial lines, each checked against the reported count.
    ///
    /// Positional rather than marker-driven because the driver's format is positional, so the
    /// count check is the only defence against a truncated run being read as a shorter basis.
    fn split_body(output: &str, size: usize) -> Result<(Vec<String>, Vec<String>), RunFailure> {
        let body: Vec<&str> = output
            .lines()
            .map(str::trim)
            .filter(|line| !line.is_empty() && !line.starts_with('#'))
            .collect();
        let separator = body
            .iter()
            .position(|line| *line == LEADING_SEPARATOR)
            .ok_or(RunFailure::MissingMarker {
                marker: LEADING_SEPARATOR.to_string(),
            })?;
        let basis = &body[..separator];
        let leading = &body[separator + 1..];
        if basis.len() != size || leading.len() != size {
            return Err(RunFailure::Unparsable {
                marker: "#length of basis:".to_string(),
                value: format!(
                    "{} basis and {} leading lines for a reported size of {}",
                    basis.len(),
                    leading.len(),
                    size
                ),
            });
        }
        Ok((
            basis.iter().map(|line| line.to_string()).collect(),
            leading.iter().map(|line| line.to_string()).collect(),
        ))
    }

    /// The driver-reported time of the `groebner_p` call alone.
    ///
    /// Recorded as a *stage* and never as the run's wall time: unlike Groebner.jl, whose process
    /// time is its compiler's, a native binary's startup is a real and small part of the cost of
    /// asking, so `wall` stays the supervised process's and stays comparable with Singular's and
    /// msolve's.
    fn solve_stage(output: &str) -> Option<Duration> {
        output
            .lines()
            .find_map(|line| line.strip_prefix("#seconds:"))
            .and_then(|value| value.trim().parse::<f64>().ok())
            .filter(|seconds| seconds.is_finite() && *seconds >= 0.0)
            .map(Duration::from_secs_f64)
    }

    /// The finer build identifier a record carries: the pinned commit **and** the ISA floor.
    ///
    /// # Why the floor belongs in the record
    ///
    /// `docs/research/external-comparison-protocol.md` requires each side's build configuration to
    /// travel with the figure, because a comparison between a tool built for its distribution's
    /// baseline and one built for the host is not a comparison of algorithms. Until #385 the
    /// driver was built at baseline `x86-64` against Zeebra's `x86-64-v3`, and — this being the
    /// part that made it a defect rather than a documented asymmetry — **a row gave no way to tell
    /// which**: the version string was the engine name and the commit, both of which are identical
    /// across the two builds.
    ///
    /// So the floor is read from the driver's own `#isa floor:`, which is a compile-time
    /// `cfg!(target_feature = ..)` inside the binary that ran. Not inferred from
    /// `provision.sh`: the script states what it asks for, and an installed binary can predate it.
    /// Not probed from the artifact either — #385 measured that instruction censuses cannot
    /// separate a raised floor from an explicitly dispatched `#[target_feature]` kernel, and that
    /// rustc emits no GNU property note.
    ///
    /// # Errors
    /// [`RunFailure::MissingMarker`] when the driver reports no floor, which means a binary older
    /// than driver contract 3 and is the operator's cue to re-provision.
    fn build_identity(output: &str) -> Result<String, RunFailure> {
        let floor = output
            .lines()
            .find_map(|line| line.strip_prefix("#isa floor:"))
            .map(str::trim)
            .filter(|floor| !floor.is_empty())
            .ok_or(RunFailure::MissingMarker {
                marker: "#isa floor:".to_string(),
            })?;
        Ok(format!("{PROVISIONED_COMMIT}, built for {floor}"))
    }

    /// The driver's error message, if it printed one.
    ///
    /// `main` returns `Result<(), String>`, so a failure is `Error: "..."` on stderr and a
    /// non-zero exit. Sagebrush's own packing failure — `exponents too large to pack` — arrives
    /// this way.
    fn error_line(output: &str) -> Option<String> {
        output
            .lines()
            .map(str::trim_start)
            .find(|line| line.starts_with("Error:") || line.starts_with("error:"))
            .map(|line| {
                line.trim_start_matches("Error:")
                    .trim_start_matches("error:")
                    .trim()
                    .trim_matches('"')
                    .to_string()
            })
    }

    /// The error line the driver prints for a positive-dimensional ideal, as [`Unsupported`].
    ///
    /// The driver exits non-zero for it, so without this the message — which states the capability
    /// fact correctly — arrives as [`RunFailure::Reported`] and the row reads as a tool that broke.
    fn capability_refusal(output: &str, task: Task) -> Option<Unsupported> {
        let message = Self::error_line(output)?;
        message
            .contains("not zero-dimensional")
            .then_some(Unsupported::PositiveDimensional { task })
    }
}

impl ExternalSolver for SagebrushSolver {
    fn id(&self) -> &str {
        "sagebrush"
    }

    fn probe_version(&mut self) -> Result<ToolVersion, RunFailure> {
        // The driver has no `--version`: an argument it cannot open is a path error. So presence is
        // proved the only way it can be, by solving a one-variable system and reading back the
        // engine line.
        let (input_path, output_path) = self.scratch("version");
        std::fs::write(&input_path, "x\n65521\nx^2-1\n")?;
        let invocation = Invocation::new(&self.binary, &self.work_dir, &output_path)
            .arg(&input_path)
            .env(THREADS_VARIABLE, "1");
        let measurement = Supervisor::new(Duration::from_secs(60)).run(&invocation)?;
        let output = read_output(&output_path);
        if !measurement.succeeded() {
            return Err(match Self::error_line(&output) {
                Some(message) => RunFailure::Reported { message },
                None => RunFailure::NonZeroExit {
                    code: measurement.exit_code,
                },
            });
        }
        let engine = output
            .lines()
            .find_map(|line| line.strip_prefix("#engine:"))
            .map(str::trim)
            .ok_or(RunFailure::MissingMarker {
                marker: "#engine:".to_string(),
            })?;
        let version = ToolVersion::new("sagebrush", engine)
            .with_build(Self::build_identity(&output)?)
            .with_raw(output.clone());
        self.version = Some(version.clone());
        Ok(version)
    }

    fn supports(&self, instance: &Instance, task: Task) -> Support {
        // The three tasks the driver has entry points for. Everything else is refused rather than
        // approximated: answering `UnivariateEliminant` with the last element of a lex basis, or
        // `LexBasis` with a degrevlex one, is precisely the substitution the task taxonomy forbids.
        match task {
            Task::ReducedGrobnerBasis | Task::LexBasisByConversion => {}
            Task::LexBasis => {
                if instance.order != MonomialOrder::Lexicographic {
                    return Support::No(Unsupported::Order {
                        order: instance.order,
                    });
                }
            }
            Task::OneFiniteFieldSolution
            | Task::AllFiniteFieldSolutions
            | Task::UnivariateEliminant
            | Task::CryptanalyticWitness => {
                return Support::No(Unsupported::Task { task });
            }
        }

        // The FGLM route's ceiling is its own and is checked before the basis route's, because the
        // narrower bound is the one that applies and reporting the wider one would name a bound
        // that is not the one in the way.
        if task == Task::LexBasisByConversion
            && instance.field.characteristic >= FGLM_MAX_CHARACTERISTIC
        {
            return Support::No(Unsupported::Characteristic {
                characteristic: instance.field.characteristic,
                supported_below: FGLM_MAX_CHARACTERISTIC,
            });
        }
        // Homogenizing costs the direct lex route one variable's worth of packing.
        if task == Task::LexBasis && instance.variables.len() > MAX_VARIABLES_LEX {
            return Support::No(Unsupported::VariableCount {
                variables: instance.variables.len(),
                maximum: MAX_VARIABLES_LEX,
            });
        }

        if !instance.field.is_prime_field() {
            return Support::No(Unsupported::ExtensionField {
                characteristic: instance.field.characteristic,
                extension_degree: instance.field.extension_degree,
            });
        }
        if instance.field.characteristic < 2 {
            return Support::No(Unsupported::Representation {
                detail: "the driver handles prime fields only; characteristic 0 would be Q"
                    .to_string(),
            });
        }
        if instance.field.characteristic >= MAX_CHARACTERISTIC {
            return Support::No(Unsupported::Characteristic {
                characteristic: instance.field.characteristic,
                supported_below: MAX_CHARACTERISTIC,
            });
        }
        if instance.variables.is_empty() || instance.variables.len() > MAX_VARIABLES {
            return Support::No(Unsupported::VariableCount {
                variables: instance.variables.len(),
                maximum: MAX_VARIABLES,
            });
        }
        // The driver's parser splits a generator on `*` and matches each factor against a variable
        // name, so a name containing `*`, `^`, `+`, `-` or `,` cannot be told from an operator.
        if let Some(name) = instance
            .variables
            .iter()
            .find(|name| name.is_empty() || name.contains(['*', '^', '+', '-', ',', ' ']))
        {
            return Support::No(Unsupported::Representation {
                detail: format!(
                    "{:?} is not distinguishable from an operator in the driver's input syntax",
                    name
                ),
            });
        }
        if let Some(name) = undeclared_identifier(instance) {
            return Support::No(Unsupported::Representation {
                detail: format!(
                    "the generators name {:?}, which is not a declared variable",
                    name
                ),
            });
        }
        Support::Yes
    }

    fn run(&mut self, instance: &Instance, task: Task, limits: &Limits) -> RunReport {
        // Cloned before the closure so that `finish` borrows nothing of `self`: the scratch-file
        // counter needs `&mut self` between here and every use of it.
        let version = self.version.clone();
        let finish = |status: RunStatus, measurement: Measurement, command: Option<String>| {
            let mut report =
                RunReport::new("sagebrush", instance, task, limits, status, measurement);
            if let Some(version) = &version {
                report = report.with_version(version.clone());
            }
            if let Some(command) = command {
                report = report.with_command_line(command);
            }
            report
        };

        if let Support::No(reason) = self.supports(instance, task) {
            return finish(
                RunStatus::Unsupported(reason),
                Measurement::unmeasured(),
                None,
            );
        }
        if let Some((variable, effect)) = Self::inherited_switch(self.switches) {
            // Refusing beats measuring: an inherited switch selects a different algorithm or
            // interleaves a trace with the basis, and `Invocation` can set a child's variable but
            // not clear one — so the condition cannot be fixed from inside the run.
            //
            // `RunFailure::Environment` and not `Reported`: nothing ran, so the tool printed no
            // error. `was_skipped()` counts it, so the board shows the row as not attempted.
            return finish(
                RunStatus::Failed(RunFailure::Environment {
                    variable: variable.to_string(),
                    detail: format!("{} and cannot be cleared from the invocation", effect),
                }),
                Measurement::unmeasured(),
                None,
            );
        }

        let (input_path, output_path) = self.scratch(&instance.name);
        if let Err(error) = std::fs::write(&input_path, Self::input(instance)) {
            return finish(
                RunStatus::Failed(RunFailure::Io {
                    reason: error.to_string(),
                }),
                Measurement::unmeasured(),
                None,
            );
        }

        let invocation = self.invocation(&input_path, &output_path, instance, task, limits);
        let command = Some(invocation.command_line());
        let process = match Supervisor::new(limits.wall).run(&invocation) {
            Ok(process) => process,
            Err(error) => {
                return finish(
                    RunStatus::Failed(RunFailure::from(error)),
                    Measurement::unmeasured(),
                    command,
                )
            }
        };

        if process.timed_out {
            return finish(
                RunStatus::StoppedByLimit(LimitStop::WallClock {
                    limit: limits.wall,
                    elapsed: process.wall,
                }),
                Measurement {
                    wall: limits.wall,
                    cpu: process.cpu,
                    cpu_basis: process.cpu_basis,
                    peak_rss_bytes: process.peak_rss_bytes,
                    rss_basis: process.rss_basis,
                    stages: Vec::new(),
                },
                command,
            );
        }

        let output = read_output(&output_path);
        if !process.succeeded() {
            // Checked before the failure bucket, because the driver exits non-zero for a
            // positive-dimensional ideal and that is a fact about the ideal rather than about
            // Sagebrush. Measurement is deliberately dropped: a capability statement must carry
            // no timing, so it cannot be read as "slower" or enter a ratio.
            if let Some(reason) = Self::capability_refusal(&output, task) {
                return finish(
                    RunStatus::Unsupported(reason),
                    Measurement::unmeasured(),
                    command,
                )
                .with_log_path(output_path);
            }
            let failure = match Self::error_line(&output) {
                Some(message) => RunFailure::Reported { message },
                None => RunFailure::NonZeroExit {
                    code: process.exit_code,
                },
            };
            return finish(
                RunStatus::Failed(failure),
                Measurement::of_process(&process),
                command,
            );
        }

        let mut measurement = Measurement::of_process(&process);
        if let Some(solve) = Self::solve_stage(&output) {
            measurement = measurement.with_stage("solve", solve);
        }

        match self.answer(&output, instance, task) {
            // `Complete` and not `Verified`, and for Sagebrush that distinction carries more weight
            // than for any other comparand here: see the maturity note at the top of this file.
            Ok(answer) => finish(RunStatus::Complete(answer), measurement, command),
            Err(failure) => finish(RunStatus::Failed(failure), measurement, command),
        }
        .with_log_path(output_path)
    }
}

#[cfg(test)]
mod tests {
    use super::{
        SagebrushSolver, DRIVER_CONTRACT, FGLM_MAX_CHARACTERISTIC, MAX_CHARACTERISTIC,
        MAX_VARIABLES, MAX_VARIABLES_LEX, PINNED_SWITCHES, PROVISIONED_COMMIT,
    };
    use crate::{
        grobner::external::{
            ExternalSolver, FieldSpec, Instance, Limits, RunFailure, RunStatus, Support, Task,
            Unsupported,
        },
        MonomialOrder,
    };
    use std::time::Duration;

    fn instance(characteristic: u64, order: MonomialOrder) -> Instance {
        Instance::new(
            "pair",
            "smoke",
            FieldSpec::prime(characteristic),
            vec!["x1".to_string(), "x2".to_string()],
            vec!["x1^2+x2".to_string(), "x2^2-1".to_string()],
            order,
        )
    }

    /// The provisioned driver, or `None` with a loud note that the live checks did not run.
    fn installed_driver() -> Option<String> {
        let path = std::path::Path::new(env!("HOME"))
            .join(".local/opt/zeebra-ext/bin/sagebrush-gb-driver")
            .to_string_lossy()
            .into_owned();
        let found = std::path::Path::new(&path).is_file().then_some(path);
        if found.is_none() {
            eprintln!(
                "sagebrush NOT CHECKED: no driver at \
                 $HOME/.local/opt/zeebra-ext/bin/sagebrush-gb-driver"
            );
            assert!(
                std::env::var_os("ZEEBRA_REQUIRE_SAGEBRUSH").is_none(),
                "ZEEBRA_REQUIRE_SAGEBRUSH is set and the driver is absent: coverage was \
                 asserted, not obtained"
            );
        }
        found
    }

    fn solver(binary: &str, tag: &str) -> SagebrushSolver {
        let root = std::env::temp_dir().join(format!(
            "zeebra-sagebrush-{}-{}-{:?}",
            tag,
            std::process::id(),
            std::thread::current().id()
        ));
        SagebrushSolver::new(binary, root).expect("a writable scratch directory")
    }

    /// An absent driver is reported as unavailable from a run, not as a failed solve.
    #[test]
    fn test_an_absent_binary_is_reported_and_not_a_failed_solve() {
        let mut solver = solver("zeebra-no-such-sagebrush", "absent");
        let report = solver.run(
            &instance(65521, MonomialOrder::GradedReverseLexicographic),
            Task::ReducedGrobnerBasis,
            &Limits::wall(Duration::from_secs(5)),
        );
        match &report.status {
            RunStatus::Failed(RunFailure::Unavailable { binary, .. }) => {
                assert_eq!(binary, "zeebra-no-such-sagebrush");
            }
            other => panic!("expected Unavailable, got {:?}", other),
        }
        assert!(report.was_skipped(), "an absent tool is a skipped row");
        assert!(report.measurement.is_unmeasured());
    }

    /// An absent driver fails the version probe the same way.
    #[test]
    fn test_an_absent_binary_fails_the_version_probe_the_same_way() {
        let mut solver = solver("zeebra-no-such-sagebrush", "absent-probe");
        match solver.probe_version() {
            Err(RunFailure::Unavailable { binary, .. }) => {
                assert_eq!(binary, "zeebra-no-such-sagebrush")
            }
            other => panic!("expected Unavailable, got {:?}", other),
        }
    }

    /// Goldilocks is inside Sagebrush's 2^62 bound; a 2^63 prime is not.
    #[test]
    fn test_the_characteristic_bound_is_sagebrushs_own_two_to_the_sixty_second() {
        let solver = solver("sagebrush-gb-driver", "char");
        assert_eq!(MAX_CHARACTERISTIC, 1 << 62);
        // 2^61 - 1, the Mersenne prime the provisioning smoke test reached.
        assert!(solver
            .supports(
                &instance(
                    2_305_843_009_213_693_951,
                    MonomialOrder::GradedReverseLexicographic
                ),
                Task::ReducedGrobnerBasis
            )
            .is_supported());
        match solver.supports(
            &instance(
                0xFFFF_FFFF_0000_0001,
                MonomialOrder::GradedReverseLexicographic,
            ),
            Task::ReducedGrobnerBasis,
        ) {
            Support::No(Unsupported::Characteristic {
                supported_below, ..
            }) => {
                assert_eq!(supported_below, MAX_CHARACTERISTIC)
            }
            other => panic!("Goldilocks is above Sagebrush's own gate, got {:?}", other),
        }
    }

    /// More variables than the packed representation can carry is a capability gap, named.
    #[test]
    fn test_too_many_variables_is_unsupported_with_the_packing_bound() {
        let solver = solver("sagebrush-gb-driver", "vars");
        let mut wide = instance(65521, MonomialOrder::GradedReverseLexicographic);
        wide.variables = (0..MAX_VARIABLES + 1).map(|i| format!("x{}", i)).collect();
        match solver.supports(&wide, Task::ReducedGrobnerBasis) {
            Support::No(Unsupported::VariableCount { variables, maximum }) => {
                assert_eq!(variables, MAX_VARIABLES + 1);
                assert_eq!(maximum, MAX_VARIABLES);
            }
            other => panic!("expected an unsupported variable count, got {:?}", other),
        }
    }

    /// The three tasks the driver has entry points for are offered; the other four are refused.
    ///
    /// `UnivariateEliminant` is among the refusals deliberately: the eliminant is the last element
    /// of the lex basis the driver *can* compute, and returning it would be answering a cheaper
    /// question than the one asked.
    #[test]
    fn test_the_three_tasks_with_entry_points_are_offered() {
        let solver = solver("sagebrush-gb-driver", "tasks");
        let lex = instance(65521, MonomialOrder::Lexicographic);
        for task in Task::all() {
            let support = solver.supports(&lex, task);
            match task {
                Task::ReducedGrobnerBasis | Task::LexBasis | Task::LexBasisByConversion => {
                    assert!(support.is_supported(), "{}", task)
                }
                _ => assert!(
                    matches!(support, Support::No(Unsupported::Task { .. })),
                    "{}",
                    task
                ),
            }
        }
    }

    /// Every order Zeebra can express is offered for a reduced basis, each by its Sagebrush name.
    #[test]
    fn test_every_order_is_offered_for_a_reduced_basis() {
        let solver = solver("sagebrush-gb-driver", "order");
        for (order, tag) in [
            (MonomialOrder::Lexicographic, "lex"),
            (MonomialOrder::GradedLexicographic, "deglex"),
            (MonomialOrder::GradedReverseLexicographic, "degrevlex"),
        ] {
            assert!(
                solver
                    .supports(&instance(65521, order), Task::ReducedGrobnerBasis)
                    .is_supported(),
                "{:?}",
                order
            );
            assert_eq!(super::sagebrush_order(order), tag);
        }
    }

    /// `LexBasis` is refused for an instance that does not declare lex order.
    ///
    /// Computing a lex basis for an instance declaring degrevlex would answer under an order the
    /// instance did not ask for, which is the substitution the task taxonomy forbids.
    #[test]
    fn test_the_lex_basis_task_needs_an_instance_that_declares_lex() {
        let solver = solver("sagebrush-gb-driver", "lex-order");
        for order in [
            MonomialOrder::GradedReverseLexicographic,
            MonomialOrder::GradedLexicographic,
        ] {
            assert!(
                matches!(
                    solver.supports(&instance(65521, order), Task::LexBasis),
                    Support::No(Unsupported::Order { .. })
                ),
                "{:?}",
                order
            );
        }
        assert!(solver
            .supports(
                &instance(65521, MonomialOrder::Lexicographic),
                Task::LexBasis
            )
            .is_supported());
    }

    /// The conversion task carries FGLM's own 2^31 ceiling, not the basis route's 2^62.
    ///
    /// Declaring the wider bound would send a sweep into its wall limit and record a timing-shaped
    /// `LimitStop` for what is a capability gap — and past the bound Sagebrush's `Ok(None)` cannot
    /// be told from "not zero-dimensional", so there is nothing to discover it from either.
    #[test]
    fn test_the_conversion_task_carries_fglms_narrower_characteristic_bound() {
        let solver = solver("sagebrush-gb-driver", "fglm-char");
        assert_eq!(FGLM_MAX_CHARACTERISTIC, 1 << 31);
        const { assert!(FGLM_MAX_CHARACTERISTIC < MAX_CHARACTERISTIC) };
        // 2^31 - 1, the largest prime FGLM accepts.
        let inside = instance(2_147_483_647, MonomialOrder::GradedReverseLexicographic);
        assert!(solver
            .supports(&inside, Task::LexBasisByConversion)
            .is_supported());
        // 2^61 - 1 is inside the basis route's bound and outside FGLM's.
        let outside = instance(
            2_305_843_009_213_693_951,
            MonomialOrder::GradedReverseLexicographic,
        );
        assert!(solver
            .supports(&outside, Task::ReducedGrobnerBasis)
            .is_supported());
        match solver.supports(&outside, Task::LexBasisByConversion) {
            Support::No(Unsupported::Characteristic {
                supported_below, ..
            }) => assert_eq!(supported_below, FGLM_MAX_CHARACTERISTIC),
            other => panic!("expected FGLM's own bound, got {:?}", other),
        }
    }

    /// The direct lex route declares one variable fewer, because it homogenizes.
    #[test]
    fn test_the_direct_lex_route_declares_one_variable_fewer() {
        let solver = solver("sagebrush-gb-driver", "lex-vars");
        assert_eq!(MAX_VARIABLES_LEX, MAX_VARIABLES - 1);
        let mut wide = instance(65521, MonomialOrder::Lexicographic);
        wide.variables = (0..MAX_VARIABLES).map(|i| format!("x{}", i)).collect();
        wide.system = vec![wide.variables.join("*")];
        // Inside the basis route's bound.
        assert!(solver
            .supports(&wide, Task::ReducedGrobnerBasis)
            .is_supported());
        match solver.supports(&wide, Task::LexBasis) {
            Support::No(Unsupported::VariableCount { variables, maximum }) => {
                assert_eq!(variables, MAX_VARIABLES);
                assert_eq!(maximum, MAX_VARIABLES_LEX);
            }
            other => panic!("expected the lex packing bound, got {:?}", other),
        }
        // FGLM converts over exponent vectors, so it does not pay the homogenizing variable.
        assert!(solver
            .supports(&wide, Task::LexBasisByConversion)
            .is_supported());
    }

    /// An extension field is unsupported rather than silently computed over the prime subfield.
    #[test]
    fn test_an_extension_field_is_unsupported() {
        let solver = solver("sagebrush-gb-driver", "ext");
        let mut extension = instance(2, MonomialOrder::GradedReverseLexicographic);
        extension.field = FieldSpec::extension(2, 8, "t^8+t^4+t^3+t+1");
        assert!(matches!(
            solver.supports(&extension, Task::ReducedGrobnerBasis),
            Support::No(Unsupported::ExtensionField { .. })
        ));
    }

    /// The input file declares the characteristic and the instance's variable order verbatim.
    #[test]
    fn test_the_input_declares_the_instances_variable_order() {
        let input =
            SagebrushSolver::input(&instance(65521, MonomialOrder::GradedReverseLexicographic));
        let mut lines = input.lines();
        assert_eq!(lines.next(), Some("x1,x2"));
        assert_eq!(lines.next(), Some("65521"));
        assert_eq!(lines.next(), Some("x1^2+x2,"));
        assert_eq!(lines.next(), Some("x2^2-1"));
    }

    /// The worker count reaches Sagebrush through the variable it actually reads.
    ///
    /// Unset, Sagebrush uses `available_parallelism()` — every hardware thread — so an unset
    /// worker count is not a default of one.
    #[test]
    fn test_the_worker_count_is_declared_to_the_child() {
        let solver = solver("sagebrush-gb-driver", "threads");
        let command = solver
            .invocation(
                std::path::Path::new("in.ms"),
                std::path::Path::new("out"),
                &instance(65521, MonomialOrder::GradedReverseLexicographic),
                Task::ReducedGrobnerBasis,
                &Limits::wall(Duration::from_secs(5)).with_workers(8),
            )
            .command_line();
        assert!(command.starts_with("SAGEBRUSH_THREADS=8"), "{}", command);
    }

    /// Each task is asked for by the order and route the driver takes flags for.
    ///
    /// The conversion task's target is lex **whatever the instance declares**, because the
    /// conversion is what is being measured — the same convention Singular's adapter follows.
    #[test]
    fn test_each_task_selects_its_own_order_and_route() {
        let solver = solver("sagebrush-gb-driver", "route-flags");
        let grevlex = instance(65521, MonomialOrder::GradedReverseLexicographic);
        let lex = instance(65521, MonomialOrder::Lexicographic);
        let grlex = instance(65521, MonomialOrder::GradedLexicographic);
        for (instance, task, order, route) in [
            (&grevlex, Task::ReducedGrobnerBasis, "degrevlex", "f4"),
            (&grlex, Task::ReducedGrobnerBasis, "deglex", "f4"),
            (&lex, Task::ReducedGrobnerBasis, "lex", "f4"),
            (&lex, Task::LexBasis, "lex", "f4"),
            // The instance is degrevlex and the conversion target is still lex.
            (&grevlex, Task::LexBasisByConversion, "lex", "fglm"),
        ] {
            let command = solver
                .invocation(
                    std::path::Path::new("in.ms"),
                    std::path::Path::new("out"),
                    instance,
                    task,
                    &Limits::wall(Duration::from_secs(5)),
                )
                .command_line();
            assert!(
                command.contains(&format!("--order {}", order)),
                "{} wants --order {}: {}",
                task,
                order,
                command
            );
            assert!(
                command.contains(&format!("--route {}", route)),
                "{} wants --route {}: {}",
                task,
                route,
                command
            );
        }
    }

    /// A complete driver output parses into leading monomials, a cardinality and a dimension.
    #[test]
    fn test_the_driver_output_parses_into_invariants() {
        let solver = solver("sagebrush-gb-driver", "parse");
        let output = "#driver contract:      3\n\
                      #isa floor:            x86-64-v3 or better (AVX2)\n\
                      #generators:           2\n\
                      #gen 1*x1^2 + 1*x2\n#gen 1*x2^2 + 65520\n\
                      #engine:               sagebrush-mpoly f4::groebner_p\n\
                      #field characteristic: 65521\n\
                      #variable order:       x1, x2\n\
                      #monomial order:       degrevlex (Order::DegRevLex)\n\
                      #route:                f4 (direct)\n\
                      #quotient dimension:   4\n\
                      #length of basis:      2 elements sorted by increasing leading monomials\n\
                      #seconds:              0.000250\n\
                      1*x2^2 + 65520\n\
                      1*x1^2 + 1*x2\n\
                      --- leading monomials ---\n\
                      x2^2\n\
                      x1^2\n";
        let answer = solver
            .answer(
                output,
                &instance(65521, MonomialOrder::GradedReverseLexicographic),
                Task::ReducedGrobnerBasis,
            )
            .expect("a complete run parses");
        assert_eq!(answer.invariants.basis_cardinality, Some(2));
        assert_eq!(
            answer.invariants.leading_monomials.as_deref(),
            Some(&["x1^2".to_string(), "x2^2".to_string()][..]),
            "sorted, so print order does not matter"
        );
        assert_eq!(answer.basis.as_ref().map(Vec::len), Some(2));
        assert_eq!(
            SagebrushSolver::solve_stage(output),
            Some(Duration::from_secs_f64(0.000250))
        );
        // The third shared invariant, which is what takes `overlap()` against Zeebra from 2 to 3.
        assert_eq!(answer.invariants.quotient_dimension, Some(4));
    }

    /// A negative or absent quotient dimension is "not reported" and never a dimension of zero.
    ///
    /// `-1` is a positive-dimensional ideal and `-2` a staircase the driver abandoned; a missing
    /// header is a driver built before the marker existed. All three must leave the invariant
    /// absent, because `Invariants::agree` treats absent as "not reported" and a spurious `0`
    /// would be a disagreement with every correct answer.
    #[test]
    fn test_a_negative_or_absent_quotient_dimension_is_not_reported() {
        for value in ["-1", "-2"] {
            let output = format!(
                "#field characteristic: 65521\n#variable order:       x1, x2\n\
                 #monomial order:       degrevlex\n#route:                f4\n\
                 #quotient dimension:   {}\n#length of basis:      1 elements\n\
                 1*x1\n--- leading monomials ---\nx1\n",
                value
            );
            assert_eq!(
                SagebrushSolver::quotient_dimension(&output),
                Ok(None),
                "{}",
                value
            );
        }
        assert_eq!(
            SagebrushSolver::quotient_dimension("#length of basis:      1 elements\n"),
            Ok(None),
            "an absent marker parses as not reported"
        );
        assert_eq!(
            SagebrushSolver::quotient_dimension("#quotient dimension:   12\n"),
            Ok(Some(12))
        );
        // Present but not an integer is a driver defect, and reading it as absent would hide one.
        assert!(matches!(
            SagebrushSolver::quotient_dimension("#quotient dimension:   lots\n"),
            Err(RunFailure::Unparsable { .. })
        ));
    }

    /// A complete output whose echoed generators are the sent system parses.
    #[test]
    fn test_echoed_generators_matching_the_sent_system_parse() {
        let solver = solver("sagebrush-gb-driver", "gen-ok");
        let output = "#driver contract:      3\n\
                      #field characteristic: 65521\n#variable order:       x1, x2\n\
                      #monomial order:       degrevlex\n#route:                f4\n\
                      #generators:           2\n\
                      #gen 1*x1^2 + 1*x2\n#gen 1*x2^2 + 65520\n\
                      #length of basis:      1 elements\n\
                      1*x1\n--- leading monomials ---\nx1\n";
        assert!(solver
            .answer(
                output,
                &instance(65521, MonomialOrder::GradedReverseLexicographic),
                Task::ReducedGrobnerBasis
            )
            .is_ok());
    }

    /// Echoed generators that are not the sent system are self-inconsistent.
    ///
    /// The whole point of the echo: a run whose input was not the one requested says nothing about
    /// any other implementation, however well-formed its basis looks.
    #[test]
    fn test_an_echoed_generator_mismatch_is_self_inconsistent() {
        let solver = solver("sagebrush-gb-driver", "gen-mismatch");
        // The instance sends `x1^2+x2` and `x2^2-1`; the driver echoes a different constant.
        let output = "#driver contract:      3\n\
                      #field characteristic: 65521\n#variable order:       x1, x2\n\
                      #monomial order:       degrevlex\n#route:                f4\n\
                      #generators:           2\n\
                      #gen 1*x1^2 + 1*x2\n#gen 1*x2^2 + 65519\n\
                      #length of basis:      1 elements\n\
                      1*x1\n--- leading monomials ---\nx1\n";
        match solver.answer(
            output,
            &instance(65521, MonomialOrder::GradedReverseLexicographic),
            Task::ReducedGrobnerBasis,
        ) {
            Err(RunFailure::SelfInconsistent { detail }) => {
                assert!(detail.contains("different system"), "{}", detail)
            }
            other => panic!("expected SelfInconsistent, got {:?}", other),
        }
    }

    /// The `x1` / `x10` prefix collapse is caught by the echo check, on every run.
    ///
    /// The hazard cross-engine agreement structurally cannot catch: every engine is handed the same
    /// bytes, so a greedy tokenizer reading `x1*x10` as `x1*x1*0` annihilates the term identically
    /// everywhere and four engines then agree while all four answer a different question. This test
    /// is the one that must be able to fail, so it feeds the *collapsed* echo a greedy parser would
    /// produce and requires the adapter to reject it.
    #[test]
    fn test_the_prefix_collapse_is_caught_by_the_echoed_generators() {
        let solver = solver("sagebrush-gb-driver", "gen-prefix");
        let mut wide = instance(1_073_741_827, MonomialOrder::GradedReverseLexicographic);
        wide.variables = (1..=10).map(|i| format!("x{}", i)).collect();
        wide.system = vec!["x1*x10-1".to_string()];
        let header = "#driver contract:      3\n\
                      #field characteristic: 1073741827\n\
                      #variable order:       x1, x2, x3, x4, x5, x6, x7, x8, x9, x10\n\
                      #monomial order:       degrevlex\n#route:                f4\n\
                      #generators:           1\n";
        let tail = "#length of basis:      1 elements\n1*x1\n--- leading monomials ---\nx1\n";

        // What a greedy longest-prefix tokenizer produces: `x1*x10` read as `x1*x1*0`, so the
        // whole term vanishes and the generator collapses to the constant.
        let collapsed = format!("{}#gen 1073741826\n{}", header, tail);
        match solver.answer(&collapsed, &wide, Task::ReducedGrobnerBasis) {
            Err(RunFailure::SelfInconsistent { .. }) => {}
            other => panic!("a collapsed `x1*x10` must be rejected, got {:?}", other),
        }
        // And the honest echo of the same generator is accepted, so the check is not merely strict.
        let faithful = format!("{}#gen 1*x1*x10 + 1073741826\n{}", header, tail);
        assert!(
            solver
                .answer(&faithful, &wide, Task::ReducedGrobnerBasis)
                .is_ok(),
            "`x1*x10` read whole must be accepted"
        );
    }

    /// A driver too old to echo its generators fails loudly rather than skipping the check.
    ///
    /// "Check only if the marker is present" is a check that silently stops checking, which is the
    /// one outcome worse than not having it — so the contract marker is **required**.
    #[test]
    fn test_a_driver_that_cannot_echo_its_generators_is_refused() {
        let solver = solver("sagebrush-gb-driver", "gen-old");
        let output = "#field characteristic: 65521\n#variable order:       x1, x2\n\
                      #monomial order:       degrevlex\n#route:                f4\n\
                      #length of basis:      1 elements\n\
                      1*x1\n--- leading monomials ---\nx1\n";
        match solver.answer(
            output,
            &instance(65521, MonomialOrder::GradedReverseLexicographic),
            Task::ReducedGrobnerBasis,
        ) {
            Err(RunFailure::MissingMarker { marker }) => {
                assert_eq!(marker, "#driver contract:")
            }
            other => panic!("expected a missing contract marker, got {:?}", other),
        }
    }

    /// A driver whose contract is older than the adapter requires is refused, naming both.
    #[test]
    fn test_an_older_driver_contract_is_refused_and_names_the_requirement() {
        let solver = solver("sagebrush-gb-driver", "gen-older");
        let output = "#driver contract:      1\n\
                      #field characteristic: 65521\n#variable order:       x1, x2\n\
                      #monomial order:       degrevlex\n#route:                f4\n\
                      #length of basis:      1 elements\n\
                      1*x1\n--- leading monomials ---\nx1\n";
        match solver.answer(
            output,
            &instance(65521, MonomialOrder::GradedReverseLexicographic),
            Task::ReducedGrobnerBasis,
        ) {
            Err(RunFailure::Incomplete { detail }) => {
                assert!(detail.contains("provision"), "{}", detail);
                assert!(detail.contains(&DRIVER_CONTRACT.to_string()), "{}", detail);
            }
            other => panic!("expected an Incomplete contract refusal, got {:?}", other),
        }
    }

    /// The build identity carries both the pinned commit and the driver's own reported ISA floor.
    #[test]
    fn test_the_build_identity_records_the_drivers_isa_floor() {
        let output = "#driver contract:      3\n\
                      #isa floor:            x86-64-v3 or better (AVX2)\n\
                      #engine:               sagebrush-mpoly f4::groebner_p\n";
        let identity = SagebrushSolver::build_identity(output).expect("the floor is reported");
        assert!(identity.contains(PROVISIONED_COMMIT), "{}", identity);
        assert!(
            identity.contains("x86-64-v3 or better (AVX2)"),
            "{}",
            identity
        );
    }

    /// A driver that reports no ISA floor yields no build identity rather than an assumed one.
    ///
    /// The whole point of #385's marker: the script's intent is not evidence about the binary that
    /// is installed, so an absent floor is a missing marker and not "presumably the configured one".
    #[test]
    fn test_a_driver_reporting_no_isa_floor_is_a_missing_marker() {
        let output = "#driver contract:      2\n\
                      #engine:               sagebrush-mpoly f4::groebner_p\n";
        match SagebrushSolver::build_identity(output) {
            Err(RunFailure::MissingMarker { marker }) => assert_eq!(marker, "#isa floor:"),
            other => panic!("expected a missing floor marker, got {:?}", other),
        }
    }

    /// A build below the floor is still recorded, verbatim, rather than silently normalized.
    ///
    /// Refusing it here would be the wrong place: `#isa floor:` is *provenance*, and a figure taken
    /// against a baseline comparand is publishable as long as the record says so. What must never
    /// happen is the record claiming the floor the script asked for.
    #[test]
    fn test_a_baseline_build_is_recorded_rather_than_refused() {
        let output = "#driver contract:      3\n\
                      #isa floor:            baseline x86-64, NO AVX2 — this build is below \
                      Zeebra's floor; re-run provision.sh\n";
        let identity = SagebrushSolver::build_identity(output).expect("a floor is reported");
        assert!(identity.contains("NO AVX2"), "{}", identity);
    }

    /// An echoed generator count that disagrees with the lines printed is a truncated run.
    #[test]
    fn test_an_echoed_generator_count_mismatch_is_unparsable() {
        let solver = solver("sagebrush-gb-driver", "gen-count");
        let output = "#driver contract:      3\n\
                      #field characteristic: 65521\n#variable order:       x1, x2\n\
                      #monomial order:       degrevlex\n#route:                f4\n\
                      #generators:           2\n#gen 1*x1^2 + 1*x2\n\
                      #length of basis:      1 elements\n\
                      1*x1\n--- leading monomials ---\nx1\n";
        match solver.answer(
            output,
            &instance(65521, MonomialOrder::GradedReverseLexicographic),
            Task::ReducedGrobnerBasis,
        ) {
            Err(RunFailure::Unparsable { marker, .. }) => assert_eq!(marker, "#gen"),
            other => panic!("expected Unparsable, got {:?}", other),
        }
    }

    /// A driver that took the direct F4 route is not an answer to the conversion task.
    ///
    /// The two routes return the *same* lex basis, so this header is the only thing in the output
    /// that distinguishes them — and a column that mixed a direct lex F4 with an FGLM conversion
    /// would compare two different complexities under one heading.
    #[test]
    fn test_an_echoed_route_mismatch_is_self_inconsistent() {
        let solver = solver("sagebrush-gb-driver", "echo-route");
        let output = "#driver contract:      3\n\
                      #field characteristic: 65521\n#variable order:       x1, x2\n\
                      #monomial order:       lex\n#route:                f4 (direct)\n\
                      #length of basis:      1 elements\n\
                      1*x1\n--- leading monomials ---\nx1\n";
        match solver.answer(
            output,
            &instance(65521, MonomialOrder::GradedReverseLexicographic),
            Task::LexBasisByConversion,
        ) {
            Err(RunFailure::SelfInconsistent { detail }) => {
                assert!(detail.contains("fglm"), "{}", detail)
            }
            other => panic!("expected SelfInconsistent, got {:?}", other),
        }
    }

    /// An echoed order mismatch names the order that was asked for, in Sagebrush's vocabulary.
    #[test]
    fn test_an_echoed_order_mismatch_names_the_requested_order() {
        let solver = solver("sagebrush-gb-driver", "echo-order");
        let output = "#driver contract:      3\n\
                      #field characteristic: 65521\n#variable order:       x1, x2\n\
                      #monomial order:       degrevlex\n#route:                f4\n\
                      #length of basis:      1 elements\n\
                      1*x1\n--- leading monomials ---\nx1\n";
        match solver.answer(
            output,
            &instance(65521, MonomialOrder::Lexicographic),
            Task::LexBasis,
        ) {
            Err(RunFailure::SelfInconsistent { detail }) => {
                assert!(detail.contains("not lex"), "{}", detail)
            }
            other => panic!("expected SelfInconsistent, got {:?}", other),
        }
    }

    /// A driver that echoed a different variable order is self-inconsistent, not a disagreement.
    ///
    /// The single most dangerous failure mode here: a basis under a permuted variable order is not
    /// comparable, and nothing else in the output would say so.
    #[test]
    fn test_an_echoed_variable_order_mismatch_is_self_inconsistent() {
        let solver = solver("sagebrush-gb-driver", "echo");
        let output = "#driver contract:      3\n\
                      #field characteristic: 65521\n\
                      #variable order:       x2, x1\n\
                      #monomial order:       degrevlex\n\
                      #route:                f4\n\
                      #length of basis:      1 elements\n\
                      1*x1\n--- leading monomials ---\nx1\n";
        match solver.answer(
            output,
            &instance(65521, MonomialOrder::GradedReverseLexicographic),
            Task::ReducedGrobnerBasis,
        ) {
            Err(RunFailure::SelfInconsistent { detail }) => {
                assert!(detail.contains("x2, x1"), "{}", detail)
            }
            other => panic!("expected SelfInconsistent, got {:?}", other),
        }
    }

    /// An echoed characteristic mismatch is self-inconsistent too.
    #[test]
    fn test_an_echoed_characteristic_mismatch_is_self_inconsistent() {
        let solver = solver("sagebrush-gb-driver", "echo-char");
        let output = "#driver contract:      3\n\
                      #field characteristic: 65519\n#variable order:       x1, x2\n\
                      #monomial order:       degrevlex\n#route:                f4\n\
                      #length of basis:      1 elements\n\
                      1*x1\n--- leading monomials ---\nx1\n";
        assert!(matches!(
            solver.answer(
                output,
                &instance(65521, MonomialOrder::GradedReverseLexicographic),
                Task::ReducedGrobnerBasis
            ),
            Err(RunFailure::SelfInconsistent { .. })
        ));
    }

    /// A basis shorter than its reported length is unparsable, not a smaller basis.
    #[test]
    fn test_a_truncated_basis_is_unparsable_rather_than_short() {
        let solver = solver("sagebrush-gb-driver", "truncated");
        let output = "#driver contract:      3\n\
                      #field characteristic: 65521\n#variable order:       x1, x2\n\
                      #monomial order:       degrevlex\n#route:                f4\n\
                      #generators:           2\n\
                      #gen 1*x1^2 + 1*x2\n#gen 1*x2^2 + 65520\n\
                      #length of basis:      2 elements\n\
                      1*x1\n--- leading monomials ---\nx1\n";
        match solver.answer(
            output,
            &instance(65521, MonomialOrder::GradedReverseLexicographic),
            Task::ReducedGrobnerBasis,
        ) {
            Err(RunFailure::Unparsable { marker, .. }) => {
                assert_eq!(marker, "#length of basis:")
            }
            other => panic!("expected Unparsable, got {:?}", other),
        }
    }

    /// Sagebrush's own packing failure is extracted as the reported message.
    #[test]
    fn test_the_drivers_error_line_is_extracted() {
        assert_eq!(
            SagebrushSolver::error_line("Error: \"exponents too large to pack\"\n").as_deref(),
            Some("exponents too large to pack")
        );
        assert_eq!(SagebrushSolver::error_line("#engine: x\n"), None);
    }

    /// The driver's zero-dimensionality refusal is a capability statement, not a failed run.
    #[test]
    fn test_the_zero_dimensionality_refusal_is_a_capability_and_not_a_failure() {
        let output = "Error: \"the ideal is not zero-dimensional, so FGLM does not apply\"\n";
        assert_eq!(
            SagebrushSolver::capability_refusal(output, Task::LexBasisByConversion),
            Some(Unsupported::PositiveDimensional {
                task: Task::LexBasisByConversion
            })
        );
    }

    /// Against the real driver, `cyclic-4`'s conversion row is unsupported and carries no time.
    ///
    /// Skipped where the driver is absent, as CI's is. Three outcomes and not two: absence says so
    /// on stderr, and `ZEEBRA_REQUIRE_SAGEBRUSH=1` turns it into a failure for an environment that
    /// means to assert this coverage rather than hope for it.
    #[test]
    fn test_a_real_driver_reports_cyclic_fours_conversion_as_unsupported() {
        let Some(driver) = installed_driver() else {
            return;
        };
        let cyclic = crate::grobner::external::corpus::instance(
            "cyclic-4",
            crate::grobner::external::corpus::REFERENCE_CHARACTERISTIC,
            MonomialOrder::Lexicographic,
        )
        .expect("cyclic-4 builds");
        let mut solver = solver(&driver, "positive-dimensional");
        let report = solver.run(
            &cyclic,
            Task::LexBasisByConversion,
            &Limits::wall(Duration::from_secs(120)),
        );
        match &report.status {
            RunStatus::Unsupported(Unsupported::PositiveDimensional { task }) => {
                assert_eq!(*task, Task::LexBasisByConversion)
            }
            other => panic!("expected PositiveDimensional, got {:?}", other),
        }
        assert!(
            report.measurement.is_unmeasured(),
            "a capability statement must carry no timing"
        );
    }

    /// Any other error line stays in the failure bucket, where a tool that broke belongs.
    #[test]
    fn test_an_unrelated_error_line_is_not_reclassified_as_unsupported() {
        assert_eq!(
            SagebrushSolver::capability_refusal(
                "Error: \"exponents too large to pack\"\n",
                Task::LexBasisByConversion
            ),
            None
        );
        assert_eq!(
            SagebrushSolver::capability_refusal("#engine: x\n", Task::LexBasisByConversion),
            None
        );
    }

    /// An inherited engine switch is detected at the value `0`, because presence is what counts.
    #[test]
    fn test_an_inherited_engine_switch_is_detected_at_a_falsy_value() {
        let name = "SB_SIGF4";
        assert!(PINNED_SWITCHES.iter().any(|(switch, _)| *switch == name));
        let switch = SagebrushSolver::inherited_switch(|probed| {
            (probed == "SB_SIGF4").then(|| std::ffi::OsString::from("0"))
        });
        assert_eq!(
            switch.map(|(switch, _)| switch),
            Some(name),
            "a truthy-if-set switch must be detected even at the value 0"
        );
    }

    /// An environment setting none of the pinned switches leaves the run to proceed.
    #[test]
    fn test_an_unpinned_variable_is_not_an_inherited_switch() {
        assert_eq!(
            SagebrushSolver::inherited_switch(|_| Some(std::ffi::OsString::from("1")))
                .map(|(switch, _)| switch),
            Some(PINNED_SWITCHES[0].0),
            "the first pinned entry wins when several are set"
        );
        assert!(SagebrushSolver::inherited_switch(|_| None).is_none());
    }

    /// An inherited switch is reported as `Environment`, naming the variable, and skips the row.
    ///
    /// Not [`RunFailure::Reported`], which is documented as "the tool printed an error": nothing
    /// ran, so there was no tool to print anything. The distinction is the point of #316 — a board
    /// must show this row as not attempted rather than as a result, and an operator needs to be
    /// told which variable to unset.
    #[test]
    fn test_an_inherited_switch_is_an_environment_failure_naming_the_variable() {
        let name = "SB_F4_SHAPE";
        assert!(PINNED_SWITCHES.iter().any(|(switch, _)| *switch == name));
        let mut solver = solver("sagebrush-gb-driver", "env-refusal")
            .with_switch_probe(|probed| (probed == "SB_F4_SHAPE").then(std::ffi::OsString::new));
        let report = solver.run(
            &instance(65521, MonomialOrder::GradedReverseLexicographic),
            Task::ReducedGrobnerBasis,
            &Limits::wall(Duration::from_secs(5)),
        );

        match &report.status {
            RunStatus::Failed(RunFailure::Environment { variable, detail }) => {
                assert_eq!(variable, name);
                assert!(!detail.is_empty(), "the effect has to be named");
            }
            other => panic!("expected an Environment refusal, got {:?}", other),
        }
        assert!(report.was_skipped(), "nothing was attempted");
        assert!(report.measurement.is_unmeasured());
    }

    /// A generator naming an undeclared variable is a capability gap, not a failed run.
    ///
    /// msolve silently drops such a factor and returns a well-formed basis of a different ideal.
    /// Both of this module's tools fail loudly instead, but the gap is knowable before running, so
    /// it is reported as `Unsupported` rather than discovered.
    #[test]
    fn test_a_generator_naming_an_undeclared_variable_is_unsupported() {
        let solver = solver("sagebrush-gb-driver", "undeclared");
        let mut bad = instance(65521, MonomialOrder::GradedReverseLexicographic);
        bad.system = vec!["x1*z-1".to_string(), "x2-1".to_string()];
        match solver.supports(&bad, Task::ReducedGrobnerBasis) {
            Support::No(Unsupported::Representation { detail }) => {
                assert!(detail.contains("\"z\""), "{}", detail)
            }
            other => panic!("expected an unsupported representation, got {:?}", other),
        }
        // Coefficients and exponents are not identifiers, so a plain system still passes.
        let mut fine = instance(65521, MonomialOrder::GradedReverseLexicographic);
        fine.system = vec!["2*x1^3+65520*x2-1".to_string()];
        assert!(solver
            .supports(&fine, Task::ReducedGrobnerBasis)
            .is_supported());
    }
}
