//! msolve as an [`ExternalSolver`].
//!
//! msolve is the reference external comparand: it is the only tool in the M25 set that both
//! reports its F4 stage timings under Zeebra's own stage names and offers the Gröbner stage and
//! the order-conversion stage as separately invocable modes. What it does **not** offer is a lex
//! basis or an enumeration of `GF(p)` points, and [`MsolveSolver::supports`] refuses those rather
//! than approximating them.
//!
//! Licence: msolve is GPL-2.0-or-later. It is driven here as a subprocess that reads a text file
//! and writes a text file, and no msolve source is reused. See
//! `docs/research/external-provenance-policy.md`.
//!
//! # Three silent failure modes, and what each one is routed to
//!
//! ## 1. msolve substitutes a problem it can solve
//!
//! At its default `-v 0`, msolve is silent: on a system whose staircase is not generic enough it
//! prints nothing, **exits 0**, and writes a perfectly well-formed parametrization — of a
//! *different ideal*. `-c` defaults to `2`, which lets msolve permute the variables and then
//! append a fresh variable carrying a random linear form (`msolve.c:511-546` for the permutation,
//! `main.c:110-119` for the flag). msolve's own source says so at `msolve.c:144-148`:
//!
//! ```text
//! /* Print all variables:
//!  * 1. may include new variable from added linear form,
//!  * 2. variables may have a different order than in the.
//!  *    input system
//!  * Both of the above points are due to genericity handling. */
//! ```
//!
//! So the output file's variable list is the only reliable signal, and it is the one
//! [`parse_parametrization`] checks: the list must equal the instance's variables **as an ordered
//! sequence**. Any permutation or addition means msolve answered a different question, and this
//! adapter reports [`RunFailure::SelfInconsistent`] carrying msolve's own words rather than
//! [`RunStatus::Complete`]. A silent success here would be the worst outcome available to the
//! milestone, so the check does not depend on `-v 1` having been passed — though it is, always.
//!
//! One correction to the provisioning record: that advisory line goes to **stderr**, not stdout.
//! `streams.h:24-26` defines `OUTSTREAM stdout`, `VERBSTREAM stderr` and `ERRSTREAM stderr`, and
//! every genericity message is written to `VERBSTREAM`; measured, `-v 1` puts **zero** bytes on
//! stdout. It makes no difference to this adapter, because
//! [`Supervisor`](super::process::Supervisor) merges both streams into one log, but it does matter
//! to anyone driving msolve by hand with `2>/dev/null`.
//!
//! ## 2. msolve's sparse-FGLM refuses a prime and then retries forever
//!
//! Worse than the first, and not recorded in the provisioning notes.
//! msolve's own guard is `1518500213`, hard-coded in `fglm_core.c:1385`; at or above it
//! sparse-FGLM returns `NULL` with `Prime <p> is too large.` on stderr.
//! [`MAX_CHARACTERISTIC_ELIMINANT`] is lower — the kernels' *documented-safe* modulus rather than
//! msolve's guard, see its own docs for the 2 968 684-wide window between the two. The genericity handler
//! reads that `NULL` as a non-generic staircase and retries with a new random linear form, without
//! bound — 25 353 retries and 1.37 million lines in eight seconds on katsura-5 over
//! `GF(2^31 - 1)`, never exiting. [`MsolveSolver::supports`] therefore refuses the eliminant task
//! above that prime as a **capability** gap, and [`ExternalSolver::run`] additionally recognises
//! msolve's own message so that a run killed at its wall limit is still reported as a refusal
//! rather than as a lower bound on msolve's speed. The `-g 2` basis path is unaffected.
//!
//! ## 3. msolve drops a factor it does not recognise
//!
//! The caller's mistake rather than msolve's, and the cheapest of the three to prevent.
//! `store_exponent` (`iofiles.c:26-73`) splits each term on `*` and matches every factor's name
//! against the declared list with a full `strcmp`. That exactness is a *good* property — it is
//! exactly why msolve is immune to the `x1`/`x10` prefix collision that a greedy tokenizer would
//! fall into, verified here by handing it 53 distinct degree-2 monomials over fourteen variables
//! and getting the same 53 back as a set. But the matching loop (`iofiles.c:57-62`) has no `else`,
//! so a factor matching nothing is **silently dropped**: `x*z-1` with only `x,y` declared is read
//! as `x-1`, exit 0, `#invalid equations 0`, and the basis is of a different ideal.
//!
//! [`MsolveSolver::supports`] therefore checks every identifier in every generator against the
//! declared variable order before anything runs. Note that cross-engine agreement cannot catch
//! this class of bug — every engine is handed the same bytes, so a mis-tokenized generator makes
//! all of them agree on the wrong ideal.
//!
//! # Why every header line is asserted
//!
//! `-g` output states the characteristic, the variable order, the monomial order and the basis
//! length it actually used (`iofiles.c:195-221`). Those are msolve reporting what it did, not an
//! echo of the request, so they are checked against the instance instead of trusted. A mismatch
//! is [`RunFailure::SelfInconsistent`]: msolve's own echo disagreeing with msolve's own input
//! file is not a disagreement about mathematics and nothing may be concluded from the run.
//!
//! Where msolve reports an invariant twice by two routes — basis size in the output file and in
//! the verbose `COMPUTATIONAL DATA` block, quotient dimension in the parametrization and in the
//! sparse-FGLM block — both are parsed and compared, which is what
//! [`RunFailure::SelfInconsistent`] is for. The `-v 1` `INPUT DATA` block's `#variables`,
//! `#equations` and `#invalid equations` are checked the same way; the last is the only place
//! msolve admits to having discarded a generator.

use std::{path::PathBuf, time::Duration};

use super::{
    contract::{
        order_is_unsupported_externally, Answer, ExternalSolver, Instance, Invariants, LimitStop,
        Limits, Measurement, RunFailure, RunReport, RunStatus, Support, Task, ToolVersion,
        Unsupported,
    },
    process::{read_output, CpuBasis, Invocation, Supervisor},
};
use crate::MonomialOrder;

/// msolve's prime-field ceiling: the characteristic must be **strictly below** `2^31`.
///
/// `get_characteristic` in `src/msolve/iofiles.c:556-570` of the 0.11.0 tarball reads the second
/// line of the input file and rejects it outright:
///
/// ```c
/// if(tmp_mod > 2147483647){
///   fprintf(ERRSTREAM, "Warning: characteristic must be 0 or < 2^31\n");
///   ...
///   exit(1);
/// ```
///
/// Measured as well as read: `p = 2147483647` is accepted and `p = 2147483659` exits 1 with that
/// line on stderr and a zero-byte output file. Note that msolve's message says `< 2^31` while the
/// comparison is `> 2^31 - 1`; both mean `p <= 2147483647`, so this bound is exclusive.
///
/// **Narrower than Zeebra's.** Zeebra's 31-bit fields are inside it; Goldilocks, BN254 and
/// BLS12-381 scalar fields are not, and an instance over one of those is
/// [`Unsupported::Characteristic`] — a capability gap, never a row in a speedup table.
pub const MAX_CHARACTERISTIC: u64 = 1 << 31;

/// The ceiling on [`Task::UnivariateEliminant`], which is **far below** [`MAX_CHARACTERISTIC`].
///
/// msolve's sparse-FGLM refuses the prime outright, at `src/fglm/fglm_core.c:1384-1389` of the
/// 0.11.0 tarball — and again verbatim at `:1586` and `:1805`:
///
/// ```c
/// /* 1147878294 */
/// if(prime>=1518500213){
///   fprintf(ERRSTREAM, "Prime %u is too large.\n", prime);
///   fprintf(ERRSTREAM, "One needs to use updated linear algebra fglm functions\n");
///   return NULL;
/// }
/// ```
///
/// `1518500213` is `floor(sqrt(2^61)) + 1`-ish: the sparse-FGLM matrix-vector kernels accumulate
/// **eight** products of magnitude under `p^2` before folding, so they need `8p^2 < 2^64`
/// (`fglm/linalg-fglm.c:464-552` for the AVX2 kernel, with the carry fold at `:547-552`).
///
/// # Why the constant is *tighter* than msolve's own guard
///
/// `linalg-fglm.c:33-39` documents the safe modulus as **`1515531528`**, inherited from FLINT:
///
/// ```c
/// //  -> modulus <= DOT2_ACC8_MAX_MODULUS   (about 2**30.5, slightly less)
/// #define DOT2_ACC8_MAX_MODULUS UWORD(1515531528)
/// ```
///
/// Neither that constant nor its length companion is ever compared against anything in msolve's
/// tree — they are documentation. So the guard admits `p <= 1518500212` while the kernel's stated
/// precondition stops at `1515531528`, and primes in the **2 968 684-wide window** between them run
/// to completion with no accumulation guarantee. A result that may be silently wrong is worse for
/// this milestone than a row marked unsupported, so this bound is the documented-safe one and not
/// msolve's. Nothing is lost in practice: no Zeebra benchmark prime lies in the window.
///
/// # Why it is a capability bound and not a slow path
///
/// **msolve does not terminate above its own guard**, and this is provable from its source rather
/// than merely observed. The `NULL` is laundered into `success = 0` at `msolve/msolve.c:1740-1752`
/// — the *same* encoding used for a non-generic staircase — which becomes return code 1
/// ("not in generic position") at `msolve.c:2446`, which reaches the `goto restart` genericity
/// handler at `msolve.c:4513-4533`. That loop cannot exit, because
/// `add_linear_form_to_input_system` unconditionally `return 1` (`msolve.c:649`) and
/// `undo_variable_order_change` permanently returns 0 once a linear form exists
/// (`msolve.c:482-484`). Each round adds another linear form, so successive attempts get *slower*.
///
/// Measured: katsura-5 over `GF(2^31 - 1)` produced **25 353** retries and 1.37 million lines of
/// `Prime 2147483647 is too large.` in eight seconds, and never exited. `p = 1518500201` returns
/// the correct degree-2 eliminant; `p = 1518500213` loops. Without this constant every eliminant
/// row above the bound would burn its whole wall limit and be recorded as "msolve needed more than
/// the limit", which files a defect as slowness.
///
/// The `-g 2` basis path is **unaffected** and works at every `p < MAX_CHARACTERISTIC`, so the two
/// tasks genuinely have two different ceilings.
///
/// Note what this excludes: Zeebra's [`Mersenne31`](crate::fields::Mersenne31) and
/// [`Zp2147483647`](crate::fields::Zp2147483647) are both **above** this bound, so msolve is not
/// an eliminant comparand on Zeebra's most natural 31-bit field. An eliminant comparison needs a
/// prime below it — `1073741827`, the one the smoke corpus uses, is inside.
pub const MAX_CHARACTERISTIC_ELIMINANT: u64 = 1_515_531_529;

/// The stderr line msolve repeats when [`MAX_CHARACTERISTIC_ELIMINANT`] is exceeded.
///
/// Matched so that a run killed at its wall limit can still be reported as the refusal it is
/// rather than as a timing lower bound.
const FGLM_PRIME_TOO_LARGE: &str = "is too large";

/// The most stage figures kept from one run.
///
/// A runaway genericity retry loop prints a `TIMINGS` block per attempt — tens of thousands of
/// them — and a `RunReport` carrying all of them is unusable. The cap is far above any legitimate
/// run, which prints at most three blocks.
const MAX_STAGES: usize = 64;

/// The smallest characteristic msolve's input format can carry as a prime field.
///
/// `0` on line 2 of the input file means **Q**, not a field of characteristic zero that Zeebra
/// could compare against (`iofiles.c:556-562`), and `1` is not a field. Both are refused rather
/// than quietly sent to msolve's rational path, where the answer would be a real-root isolation
/// and not a basis over `GF(p)`.
pub const MIN_CHARACTERISTIC: u64 = 2;

/// The monomial order `-g` computes in, and the only one msolve offers.
///
/// `main.c:104-109` documents `-g` as printing a reduced basis "for first prime characteristic
/// **w.r.t. grevlex ordering**", and `iofiles.c:210-220` prints that order back. msolve has no lex
/// mode at all: `-e` builds a two-block *elimination* order whose blocks are each degrevlex, which
/// is not lex either, and the parametrization from `-g 0` is a rational parametrization rather
/// than a basis. So an instance posed under lex or grlex is [`Unsupported::Order`].
pub const NATIVE_ORDER: MonomialOrder = MonomialOrder::GradedReverseLexicographic;

/// The `#monomial order:` line `-g` prints for [`NATIVE_ORDER`], verbatim.
///
/// Asserted rather than skipped, because `-e` makes `iofiles.c:212-218` print "eliminating first
/// N variables, blocks: graded reverse lexicographical" instead — so this one line is what
/// separates a comparable basis from an incomparable one.
const GREVLEX_HEADER: &str = "graded reverse lexicographical";

/// msolve driven as a competitive solver.
///
/// One per worker with its own `work_dir`: the scratch filenames are numbered per solver, so two
/// solvers sharing a directory would hand the same input path to two processes.
#[derive(Clone, Debug)]
pub struct MsolveSolver {
    binary: String,
    work_dir: PathBuf,
    version: Option<ToolVersion>,
    runs: u64,
}

impl MsolveSolver {
    /// A solver over `binary`, with scratch files under `work_dir`.
    ///
    /// Neither path is touched here and a missing binary is **not** an error at this point:
    /// nothing has been run, so the absent-tool case surfaces from [`Self::probe_version`] or
    /// [`ExternalSolver::run`] as [`RunFailure::Unavailable`], which is the outcome a sweep
    /// records and continues past.
    pub fn new(binary: impl Into<String>, work_dir: impl Into<PathBuf>) -> Self {
        Self {
            binary: binary.into(),
            work_dir: work_dir.into(),
            version: None,
            runs: 0,
        }
    }

    /// The binary this solver drives.
    pub fn binary(&self) -> &str {
        &self.binary
    }

    /// The three scratch paths for the next run: input, msolve's `-o` file, and the merged log.
    ///
    /// Numbered so that a sweep's runs do not overwrite each other's evidence, which matters
    /// because a parse failure is not diagnosable without the log that produced it.
    fn paths(&mut self) -> (PathBuf, PathBuf, PathBuf) {
        self.runs += 1;
        let stem = format!("msolve-{}-{}", std::process::id(), self.runs);
        (
            self.work_dir.join(format!("{}.ms", stem)),
            self.work_dir.join(format!("{}.out", stem)),
            self.work_dir.join(format!("{}.log", stem)),
        )
    }
}

/// The instance as an msolve input file.
///
/// Three parts, from `main.c:86-92` and the `-h` text: the variables comma-separated on line 1,
/// the characteristic on line 2, then one generator per line separated by commas with **no**
/// trailing comma. The variable order on line 1 is the instance's variable order, greatest first,
/// because for msolve that line *is* the order — see [`msolve`](self) on why a permutation here is
/// the most dangerous mistake available.
pub fn input_file(instance: &Instance) -> String {
    let mut text = String::new();
    text.push_str(&instance.variables.join(","));
    text.push('\n');
    text.push_str(&instance.field.characteristic.to_string());
    text.push('\n');
    text.push_str(&instance.system.join(",\n"));
    text.push('\n');
    text
}

/// The first identifier in `generator` that is not one of `variables`, if there is one.
///
/// An identifier is a maximal run of letters, digits and underscores that **starts** with a letter
/// or underscore; a run that starts with a digit is a coefficient. That is the whole lexical
/// vocabulary of msolve's input format — the only other characters are `*`, `^`, `+` and `-` — so
/// any identifier that is not a declared variable is a factor msolve will drop on the floor.
///
/// Whole-token comparison, not a prefix test: `x1` and `x10` are different identifiers here for
/// the same reason they are different to msolve's `strcmp`, which is what makes a fourteen-variable
/// system safe to hand over.
fn unknown_identifier(generator: &str, variables: &[String]) -> Option<String> {
    let bytes = generator.as_bytes();
    let is_word = |c: u8| c.is_ascii_alphanumeric() || c == b'_';
    let mut i = 0;
    while i < bytes.len() {
        if !(bytes[i].is_ascii_alphabetic() || bytes[i] == b'_') {
            // Skip the whole run, so that the `1` of a coefficient `12` never starts a token.
            while i < bytes.len() && is_word(bytes[i]) {
                i += 1;
            }
            i += usize::from(i < bytes.len());
            continue;
        }
        let start = i;
        while i < bytes.len() && is_word(bytes[i]) {
            i += 1;
        }
        let token = &generator[start..i];
        if !variables.iter().any(|name| name == token) {
            return Some(token.to_string());
        }
    }
    None
}

/// A `#key: value` header line from `-g` output, with the value trimmed.
///
/// `iofiles.c:197-221` pads the values into a column, so the separator is a colon and everything
/// after it is whitespace to be trimmed.
fn header(output: &str, key: &str) -> Option<String> {
    let prefix = format!("#{}:", key);
    output
        .lines()
        .find(|line| line.starts_with(&prefix))
        .map(|line| line[prefix.len()..].trim().to_string())
}

/// The polynomials in a bracketed `-g` list, one per line.
///
/// `iofiles.c:268-328` writes `[` glued to the first element, `,\n` between elements and `]:`
/// glued to the last, and never wraps an element across lines. The closing `]:` is the
/// completeness marker: without it the file is a truncated write from a killed process, which must
/// not be parsed as a short basis.
fn parse_list(output: &str) -> Result<Vec<String>, RunFailure> {
    let body = match output.split_once("#---\n[") {
        // Everything after the *second* `#---`, which is the one that closes the header block.
        Some((_, rest)) => rest,
        None => match output.find('[') {
            Some(at) => &output[at + 1..],
            None => {
                return Err(RunFailure::MissingMarker {
                    marker: "the opening [ of the basis list".to_string(),
                })
            }
        },
    };
    let body = match body.split_once("]:") {
        Some((inside, _)) => inside,
        None => {
            return Err(RunFailure::MissingMarker {
                marker: "the closing ]: of the basis list".to_string(),
            })
        }
    };

    let elements: Vec<String> = body
        .lines()
        .map(|line| line.trim().trim_end_matches(',').trim().to_string())
        .filter(|line| !line.is_empty())
        .collect();
    if elements.is_empty() {
        return Err(RunFailure::MissingMarker {
            marker: "at least one basis element".to_string(),
        });
    }
    Ok(elements)
}

/// The leading monomial of a printed basis element, in Zeebra's rendering.
///
/// msolve prints the leading term first and every exponent explicitly: `1*x^1*y^1`
/// (`iofiles.c:277-301`). The leading-ideal mode prints the same monomial from the same
/// `hm[0]` without the coefficient (`iofiles.c:240-266`), which is why dropping the coefficient
/// from the first term is the leading monomial and not an approximation of it — checked against
/// `-g 1` on katsura-6, where all 22 agree.
///
/// The rendering is normalized to [`monomial_to_string`](crate::grobner::differential::text)'s
/// convention — `x*y` rather than `x^1*y^1` — so that
/// [`Invariants::leading_monomials`](super::contract::Invariants::leading_monomials) compares
/// equal to Zeebra's without either side knowing about the other's printer.
fn leading_monomial(element: &str) -> String {
    let first_term = element.split('+').next().unwrap_or(element).trim();
    let mut factors: Vec<String> = Vec::new();
    for factor in first_term.split('*') {
        let factor = factor.trim();
        if factor.is_empty() {
            continue;
        }
        match factor.split_once('^') {
            // `name^exponent`: an exponent of one is implicit in Zeebra's rendering.
            Some((name, exponent)) => {
                if exponent.trim() == "1" {
                    factors.push(name.trim().to_string());
                } else {
                    factors.push(format!("{}^{}", name.trim(), exponent.trim()));
                }
            }
            // No caret: either the leading coefficient or a bare variable name. msolve always
            // prints the coefficient of the leading term and always carets its exponents, so a
            // purely numeric factor here is the coefficient and is dropped.
            None => {
                if !factor.chars().all(|c| c.is_ascii_digit()) {
                    factors.push(factor.to_string());
                }
            }
        }
    }
    if factors.is_empty() {
        // Every exponent was zero: the element is a nonzero constant, so the ideal is the whole
        // ring and the leading monomial is 1 — the same string Zeebra's printer uses.
        return "1".to_string();
    }
    factors.join("*")
}

/// A `COMPUTATIONAL DATA` integer from the verbose log, if the log carried it.
///
/// `neogb/meta_data.c:328-340` and `fglm/fglm_core.c:88-98` pad these into a column, so the value
/// is the last whitespace-separated token. `None` rather than an error: the figure is a
/// cross-check on a value the output file already gave, and a missing cross-check is weaker
/// evidence rather than a failed run.
fn computational_datum(log: &str, label: &str) -> Option<u64> {
    log.lines()
        .find(|line| line.trim_start().starts_with(label))
        .and_then(|line| line.split_whitespace().last()?.parse().ok())
}

/// A tool-reported stage figure from a `TIMINGS` block, as `(label, seconds)`.
///
/// `neogb/meta_data.c:285-327` prints `<label><padding><%.2f> sec[ <%.1f>%]`, so the seconds are
/// the token before `sec`. The resolution is **10 ms**, which is why a stage breakdown means
/// nothing on an instance that finishes in milliseconds.
fn timing_line(line: &str) -> Option<(String, Duration)> {
    let (before, _) = line.split_once(" sec")?;
    let seconds: f64 = before.split_whitespace().last()?.parse().ok()?;
    let label = before[..before.len() - before.split_whitespace().last()?.len()]
        .trim()
        .to_string();
    if label.is_empty() || seconds.is_sign_negative() {
        return None;
    }
    Some((label, Duration::from_secs_f64(seconds)))
}

/// Which of msolve's three `TIMINGS` writers produced a block.
///
/// The blocks have to be told apart because two of them use the *same* label, `overall(elapsed)`,
/// for different quantities — F4's `st->f4_rtime` and sparse-FGLM's `st->fglm_rtime`. The
/// discriminator is grounded in the three source sites rather than in block position, because a
/// genericity retry repeats the first two blocks:
///
/// * `neogb/meta_data.c:285-327` — F4. The only block with named stage lines.
/// * `fglm/fglm_core.c:84-87` — sparse-FGLM. `overall` lines and nothing else.
/// * `msolve/msolve.c:3800-3808` — the rational parametrization. Labels itself.
fn stage_prefix(block: &str) -> &'static str {
    if block.contains("rational param(") {
        return "rational-param";
    }
    // Any named F4 stage. `convert` and `select` are printed unconditionally by that writer,
    // while `tracer`, `reduce gb` and `rht` are conditional, so the unconditional pair is the
    // reliable test.
    if block.contains("\nconvert ") || block.contains("\nselect ") {
        return "f4";
    }
    "sparse-fglm"
}

/// Every stage figure msolve printed, in the order it printed them.
///
/// Prefixed by which computation the block belongs to and suffixed with an occurrence index when
/// the same stage is reported more than once, which happens on every genericity retry. Repeats
/// are kept rather than collapsed: the retries are real work msolve did, and a board that summed
/// one of them would understate the cost of the run.
fn parse_stages(log: &str) -> Vec<(String, Duration)> {
    let mut stages: Vec<(String, Duration)> = Vec::new();
    let mut seen: std::collections::HashMap<String, u32> = std::collections::HashMap::new();

    for block in log
        .split("---------------- TIMINGS ----------------")
        .skip(1)
    {
        // The block ends at its own rule; anything after it belongs to another section.
        let block = block
            .split_once("-----------------------------------------")
            .map(|(inside, _)| inside)
            .unwrap_or(block);
        let prefix = stage_prefix(block);
        for line in block.lines() {
            if stages.len() >= MAX_STAGES {
                return stages;
            }
            if let Some((label, elapsed)) = timing_line(line) {
                // msolve's own label, verbatim — `symbolic prep.`, `linear algebra`. The
                // correspondence with Zeebra's stage names is the finding and belongs in the
                // study, so it must not be hidden by renaming here. The prefix is a
                // disambiguator, not a rename: F4 and sparse-FGLM both print `overall(elapsed)`
                // for different quantities.
                let mut name = format!("{}/{}", prefix, label);
                let count = seen.entry(name.clone()).or_insert(0);
                *count += 1;
                if *count > 1 {
                    name = format!("{}#{}", name, count);
                }
                stages.push((name, elapsed));
            }
        }
    }
    stages
}

/// `-g` output as an answer, with every header line checked against the instance.
fn parse_basis(output: &str, instance: &Instance, log: &str) -> Result<Answer, RunFailure> {
    let inconsistent = |detail: String| RunFailure::SelfInconsistent { detail };

    let characteristic = header(output, "field characteristic").ok_or({
        RunFailure::MissingMarker {
            marker: "#field characteristic".to_string(),
        }
    })?;
    if characteristic != instance.field.characteristic.to_string() {
        return Err(inconsistent(format!(
            "the input file declared characteristic {} and msolve's output reports {}",
            instance.field.characteristic, characteristic
        )));
    }

    // The check the whole workstream turns on. msolve echoes the order it used, comma-space
    // separated (`iofiles.c:202-207`); a basis under any other order is not comparable with
    // Zeebra's and is not comparable with msolve's own previous runs either.
    let variables = header(output, "variable order").ok_or({
        RunFailure::MissingMarker {
            marker: "#variable order".to_string(),
        }
    })?;
    let reported: Vec<&str> = variables.split(',').map(str::trim).collect();
    if reported != instance.variable_refs() {
        return Err(inconsistent(format!(
            "the input file declared the variable order {} and msolve's output reports {}",
            instance.variables.join(", "),
            variables
        )));
    }

    let order = header(output, "monomial order").ok_or({
        RunFailure::MissingMarker {
            marker: "#monomial order".to_string(),
        }
    })?;
    if order != GREVLEX_HEADER {
        return Err(inconsistent(format!(
            "msolve reports the monomial order as {:?}, not {:?}",
            order, GREVLEX_HEADER
        )));
    }

    // `iofiles.c:216-220` writes "1 element" without the trailing clause when the basis is a
    // single polynomial, so the count is the first token and the rest of the line is prose.
    let length = header(output, "length of basis").ok_or({
        RunFailure::MissingMarker {
            marker: "#length of basis".to_string(),
        }
    })?;
    let declared: usize = length
        .split_whitespace()
        .next()
        .and_then(|token| token.parse().ok())
        .ok_or(RunFailure::Unparsable {
            marker: "#length of basis".to_string(),
            value: length.clone(),
        })?;

    // msolve's `-v 1` INPUT DATA block echoes what it decided it read (`meta_data.c`'s
    // `print_initial_statistics`). Weaker than the `-g` header but free, and `#invalid equations`
    // is the only place msolve reports having discarded a generator.
    for (label, expected) in [
        ("#variables", instance.variables.len() as u64),
        ("#equations", instance.system.len() as u64),
        ("#invalid equations", 0),
    ] {
        if let Some(reported) = computational_datum(log, label) {
            if reported != expected {
                return Err(inconsistent(format!(
                    "msolve reports {} as {} where the input file carries {}",
                    label.trim_start_matches('#'),
                    reported,
                    expected
                )));
            }
        }
    }

    let basis = parse_list(output)?;
    if basis.len() != declared {
        return Err(inconsistent(format!(
            "msolve's header declares {} basis elements and its list carries {}",
            declared,
            basis.len()
        )));
    }
    // msolve's second, independent route to the same number. `size of basis` is computed from the
    // basis struct in `get_final_statistics`, not from the printer, so a disagreement is msolve
    // contradicting itself and nothing may be concluded from the run.
    if let Some(reported) = computational_datum(log, "size of basis") {
        if reported != basis.len() as u64 {
            return Err(inconsistent(format!(
                "msolve's verbose log reports a basis of size {} and its output file carries {}",
                reported,
                basis.len()
            )));
        }
    }

    let leading: Vec<String> = basis.iter().map(|e| leading_monomial(e)).collect();
    Ok(
        Answer::from_invariants(Invariants::none().with_leading_monomials(leading))
            .with_basis(basis),
    )
}

/// What the parametrization output file said, beyond the fields an [`Answer`] carries.
///
/// Separated from the `Answer` so that the two outcomes msolve expresses *as* a parametrization —
/// an empty variety and a positive-dimensional one — can be told from a parametrization that
/// actually parametrizes something.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Parametrization {
    /// `[-1]:` — no solution in the algebraic closure (`main.c:94`, `msolve.c:3890`).
    NoSolution,

    /// `[1, nvars, -1, []]:` — infinitely many solutions, i.e. the ideal is not
    /// zero-dimensional (`main.c:95`). Not a failure and not a timing to compare: msolve answered
    /// the question it was asked and the answer is that the eliminant does not exist.
    PositiveDimensional,

    /// A rational parametrization.
    Zero {
        /// Variables **as msolve used them**, which is the genericity signal.
        variables: Vec<String>,
        /// The linear form msolve eliminated in, one coefficient per variable.
        linear_form: Vec<i64>,
        /// `dim k[x]/I`, msolve's `dquot` (`msolve.c:158`).
        quotient_dimension: usize,
        /// The eliminant's degree and its coefficients in ascending degree
        /// (`fglm_core.c:105-118`).
        eliminant_degree: usize,
        eliminant_coefficients: Vec<String>,
    },
}

/// The bracketed group starting at `from`, and the index just past its closing bracket.
fn bracketed(text: &str, from: usize) -> Option<(&str, usize)> {
    let bytes = text.as_bytes();
    let open = (from..bytes.len()).find(|&i| bytes[i] == b'[')?;
    let mut depth = 0usize;
    for i in open..bytes.len() {
        match bytes[i] {
            b'[' => depth += 1,
            b']' => {
                depth -= 1;
                if depth == 0 {
                    return Some((&text[open + 1..i], i + 1));
                }
            }
            _ => {}
        }
    }
    None
}

/// The comma-separated items of a group, trimmed and with quotes stripped.
fn items(group: &str) -> Vec<String> {
    group
        .split(',')
        .map(|item| item.trim().trim_matches('\'').trim().to_string())
        .filter(|item| !item.is_empty())
        .collect()
}

/// The parametrization output file, as the shape `mpz_param_out_str` writes.
///
/// `msolve.c:154-210` is the writer and fixes the field order: characteristic, variable count,
/// quotient dimension, the variable list, the linear form, then `[1, <eliminant>, <denominator>,
/// <coordinates>]`. Each polynomial is `[<degree>, [<coefficients ascending>]]`
/// (`fglm_core.c:105-118`).
fn parse_parametrization(output: &str) -> Result<Parametrization, RunFailure> {
    let text = output.trim();
    if text.is_empty() {
        return Err(RunFailure::MissingMarker {
            marker: "any parametrization output".to_string(),
        });
    }
    if !text.ends_with("]:") {
        // The `]:` is written last (`msolve.c:3912`), so its absence is a truncated file rather
        // than a short answer.
        return Err(RunFailure::MissingMarker {
            marker: "the closing ]: of the parametrization".to_string(),
        });
    }

    let (outer, _) = bracketed(text, 0).ok_or(RunFailure::Unparsable {
        marker: "parametrization".to_string(),
        value: text.chars().take(80).collect(),
    })?;
    let leading: Vec<&str> = outer.split(',').map(str::trim).collect();
    match leading.first().copied() {
        Some("-1") => return Ok(Parametrization::NoSolution),
        // `[1, nvars, -1, []]`: the third field is the quotient dimension and `-1` is msolve's
        // "infinite" (`main.c:95`).
        Some("1") if leading.get(2).copied() == Some("-1") => {
            return Ok(Parametrization::PositiveDimensional)
        }
        Some("0") => {}
        _ => {
            return Err(RunFailure::Unparsable {
                marker: "the parametrization's leading tag".to_string(),
                value: leading.first().copied().unwrap_or_default().to_string(),
            })
        }
    }

    // Inside the outer group, the parametrization proper is its own bracketed group.
    let (inner, _) = bracketed(outer, 0).ok_or(RunFailure::Unparsable {
        marker: "the parametrization body".to_string(),
        value: outer.chars().take(80).collect(),
    })?;

    // The three scalars precede the variable list, which is the first bracketed group.
    let (variable_group, after_variables) = bracketed(inner, 0).ok_or(RunFailure::Unparsable {
        marker: "the parametrization's variable list".to_string(),
        value: inner.chars().take(80).collect(),
    })?;
    let head_end = inner.find('[').unwrap_or(0);
    let scalars = items(&inner[..head_end]);
    let quotient_dimension: usize =
        scalars
            .get(2)
            .and_then(|value| value.parse().ok())
            .ok_or(RunFailure::Unparsable {
                marker: "the parametrization's quotient dimension".to_string(),
                value: scalars.join(","),
            })?;
    let variables = items(variable_group);

    let (form_group, after_form) =
        bracketed(inner, after_variables).ok_or(RunFailure::Unparsable {
            marker: "the parametrization's linear form".to_string(),
            value: inner.chars().take(80).collect(),
        })?;
    let linear_form: Vec<i64> = items(form_group)
        .iter()
        .filter_map(|value| value.parse().ok())
        .collect();

    // `msolve.c:206` writes `[1,\n[` and lets the inner bracket run to the end of the record, so
    // the shape is `[1, [ <eliminant>, <denominator>, [<coordinates>] ]]` — two levels, not one,
    // and the eliminant is the first group inside the inner one.
    let (parts, _) = bracketed(inner, after_form).ok_or(RunFailure::Unparsable {
        marker: "the parametrization's polynomial block".to_string(),
        value: inner.chars().take(80).collect(),
    })?;
    let (polynomials, _) = bracketed(parts, 0).ok_or(RunFailure::Unparsable {
        marker: "the parametrization's polynomial list".to_string(),
        value: parts.chars().take(80).collect(),
    })?;
    let (eliminant, _) = bracketed(polynomials, 0).ok_or(RunFailure::Unparsable {
        marker: "the eliminant".to_string(),
        value: polynomials.chars().take(80).collect(),
    })?;
    let eliminant_degree: usize = eliminant
        .split(',')
        .next()
        .map(str::trim)
        .and_then(|value| value.parse().ok())
        .ok_or(RunFailure::Unparsable {
            marker: "the eliminant's degree".to_string(),
            value: eliminant.chars().take(80).collect(),
        })?;
    let (coefficients, _) = bracketed(eliminant, 0).ok_or(RunFailure::Unparsable {
        marker: "the eliminant's coefficients".to_string(),
        value: eliminant.chars().take(80).collect(),
    })?;

    Ok(Parametrization::Zero {
        variables,
        linear_form,
        quotient_dimension,
        eliminant_degree,
        eliminant_coefficients: items(coefficients),
    })
}

/// The eliminant as a polynomial in `variable`, terms descending.
///
/// msolve gives the coefficients ascending (`fglm_core.c:109-112`); Zeebra's printer renders
/// descending with `+` between terms and coefficients in `[0, p)`, so this renders to match and
/// the two strings can be compared directly.
fn render_eliminant(coefficients: &[String], variable: &str) -> String {
    let mut terms: Vec<String> = Vec::new();
    for (degree, coefficient) in coefficients.iter().enumerate().rev() {
        if coefficient == "0" {
            continue;
        }
        match degree {
            0 => terms.push(coefficient.clone()),
            1 if coefficient == "1" => terms.push(variable.to_string()),
            1 => terms.push(format!("{}*{}", coefficient, variable)),
            _ if coefficient == "1" => terms.push(format!("{}^{}", variable, degree)),
            _ => terms.push(format!("{}*{}^{}", coefficient, variable, degree)),
        }
    }
    if terms.is_empty() {
        return "0".to_string();
    }
    terms.join("+")
}

/// A parametrization as an answer, or the reason it is not one of the requested ideal.
fn eliminant_answer(
    parametrization: Parametrization,
    instance: &Instance,
    log: &str,
) -> Result<Answer, RunFailure> {
    let (variables, linear_form, quotient_dimension, eliminant_degree, coefficients) =
        match parametrization {
            Parametrization::NoSolution => {
                // A consistent, well-defined answer that is nonetheless not an eliminant. Nothing
                // in `Invariants` expresses "the variety is empty", so reporting it as an answer
                // with no eliminant would publish a timing against a blank.
                return Err(RunFailure::Reported {
                    message: "msolve reports no solution in the algebraic closure ([-1]), so the \
                              ideal has no univariate eliminant"
                        .to_string(),
                });
            }
            Parametrization::PositiveDimensional => {
                return Err(RunFailure::Reported {
                    message: "msolve reports infinitely many solutions ([1, nvars, -1, []]), so \
                              the ideal is not zero-dimensional and has no univariate eliminant"
                        .to_string(),
                });
            }
            Parametrization::Zero {
                variables,
                linear_form,
                quotient_dimension,
                eliminant_degree,
                eliminant_coefficients,
            } => (
                variables,
                linear_form,
                quotient_dimension,
                eliminant_degree,
                eliminant_coefficients,
            ),
        };

    // The genericity check, and the reason this adapter exists. msolve's own source
    // (`msolve.c:144-148`) names the two ways this list can differ from the input's, and both
    // mean the parametrization describes a different ideal than the one asked about.
    if variables != instance.variables {
        let added: Vec<&String> = variables
            .iter()
            .filter(|name| !instance.variables.contains(name))
            .collect();
        let detail = if added.is_empty() {
            format!(
                "msolve permuted the variables to {} looking for a generic staircase",
                variables.join(", ")
            )
        } else {
            format!(
                "msolve added the variable(s) {} carrying a random linear form, so its eliminant \
                 is of an augmented ideal",
                added
                    .iter()
                    .map(|name| name.as_str())
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        };
        // msolve's own words where `-v 1` captured them, so the record quotes the tool rather
        // than only this adapter's inference.
        let quoted = log
            .lines()
            .find(|line| line.contains("not in generic position"))
            .map(|line| format!(" msolve said: {:?}.", line.trim()))
            .unwrap_or_default();
        // `SelfInconsistent` rather than `Reported`: msolve ran, produced output, and the output
        // is internally fine — it just describes an ideal msolve substituted for the one it was
        // given. Both variants are `Failed` and so neither is timing evidence, which is the
        // property that matters; this is the variant the runner contract's owner picked for the
        // case, so an aggregator can key on it uniformly across adapters.
        return Err(RunFailure::SelfInconsistent {
            detail: format!(
                "{} (input order {}, msolve's order {}).{} Run with -c 0 to make msolve refuse \
                 instead of substituting a problem.",
                detail,
                instance.variables.join(", "),
                variables.join(", "),
                quoted
            ),
        });
    }

    // With the variable list intact, the remaining way msolve's eliminant can be of something
    // else is a linear form that is not the last variable on its own. `[0, .., 0, 1]` is the
    // identity case; anything else is the minimal polynomial of a linear combination.
    let identity_form: bool = linear_form.len() == instance.variables.len()
        && linear_form.last().copied() == Some(1)
        && linear_form[..linear_form.len() - 1].iter().all(|c| *c == 0);
    if !identity_form {
        return Err(RunFailure::SelfInconsistent {
            detail: format!(
                "msolve parametrized in the linear form [{}] rather than in {} alone, so its \
                 eliminant is the minimal polynomial of a combination and not the eliminant of \
                 the requested variable order",
                linear_form
                    .iter()
                    .map(|c| c.to_string())
                    .collect::<Vec<_>>()
                    .join(", "),
                instance.variables.last().map(String::as_str).unwrap_or("?")
            ),
        });
    }

    if eliminant_degree != coefficients.len().saturating_sub(1) {
        return Err(RunFailure::SelfInconsistent {
            detail: format!(
                "msolve declares an eliminant of degree {} and prints {} coefficients",
                eliminant_degree,
                coefficients.len()
            ),
        });
    }
    // The verbose log's sparse-FGLM block reports both figures again from the FGLM structs
    // (`fglm_core.c:88-98`), independently of the parametrization writer.
    for (label, from_file) in [
        ("degree of ideal", quotient_dimension),
        ("deg. elim. pol.", eliminant_degree),
    ] {
        if let Some(from_log) = computational_datum(log, label) {
            if from_log != from_file as u64 {
                return Err(RunFailure::SelfInconsistent {
                    detail: format!(
                        "msolve's verbose log reports {} as {} and its output file as {}",
                        label, from_log, from_file
                    ),
                });
            }
        }
    }

    let variable = instance.variables.last().map(String::as_str).unwrap_or("x");
    Ok(Answer::from_invariants(
        Invariants::none()
            .with_quotient_dimension(quotient_dimension)
            .with_eliminant_degree(eliminant_degree),
    )
    .with_eliminant(render_eliminant(&coefficients, variable)))
}

/// The failure a non-zero exit stands for, read from what msolve printed.
///
/// msolve's error lines are the evidence; the exit code alone does not distinguish "this
/// characteristic is too large" from "the staircase was not generic and `-c 0` forbade a fix".
fn failure_from_log(log: &str, code: Option<i32>) -> RunFailure {
    for (needle, message) in [
        (
            "characteristic must be 0 or < 2^31",
            "msolve refused the characteristic: it must be 0 or below 2^31",
        ),
        (
            "Computation failed",
            "msolve's computation failed: the staircase was not generic enough and -c forbade a \
             change of variables",
        ),
        (
            "Bad file format",
            "msolve rejected the generated input file as malformed",
        ),
    ] {
        if log.contains(needle) {
            return RunFailure::Reported {
                message: message.to_string(),
            };
        }
    }
    // msolve's own I/O, as msolve reported it: the tool ran and failed on a file of its own, which
    // is its row and not the harness's. `RunFailure::Io` is that side of #610's split, and it is
    // deliberately **not** counted by `was_skipped()`.
    if log.contains("Cannot open output file") {
        return RunFailure::Io {
            reason: "msolve could not open its output file".to_string(),
        };
    }
    RunFailure::NonZeroExit { code }
}

impl ExternalSolver for MsolveSolver {
    fn id(&self) -> &str {
        "msolve"
    }

    fn probe_version(&mut self) -> Result<ToolVersion, RunFailure> {
        let (_, _, log) = self.paths();
        let invocation = Invocation::new(&self.binary, &self.work_dir, &log).arg("-V");
        let measurement = Supervisor::new(Duration::from_secs(30)).run(&invocation)?;
        let output = read_output(&log);
        if !measurement.succeeded() {
            return Err(RunFailure::Incomplete {
                detail: format!(
                    "msolve -V exited {:?} rather than cleanly: {:?}",
                    measurement.exit_code,
                    output.trim()
                ),
            });
        }
        // `-V` prints the bare version and nothing else (`main.c`'s `-V` branch), so the first
        // non-empty line is it. Parsed defensively rather than taken whole, because the raw text
        // is kept and a misparse has to stay recoverable.
        let version = output
            .lines()
            .map(str::trim)
            .find(|line| !line.is_empty())
            .ok_or(RunFailure::MissingMarker {
                marker: "a version line from msolve -V".to_string(),
            })?;
        let version = ToolVersion::new("msolve", version).with_raw(output.clone());
        self.version = Some(version.clone());
        Ok(version)
    }

    fn supports(&self, instance: &Instance, task: Task) -> Support {
        // Weighted orders (#306) are refused rather than approximated: no adapter here has a
        // verified spelling for one, and substituting an unweighted order would answer a
        // different question with a basis that looks right.
        if order_is_unsupported_externally(instance.order) {
            return Support::No(Unsupported::Order {
                order: instance.order,
            });
        }
        match task {
            // `-g 2` under the instance's order, which must be the only order msolve has.
            Task::ReducedGrobnerBasis => {
                if instance.order != NATIVE_ORDER {
                    return Support::No(Unsupported::Order {
                        order: instance.order,
                    });
                }
            }
            // The default mode's rational parametrization. Its eliminant is a lex-flavoured
            // object that msolve computes from a grevlex basis, so the instance's declared order
            // is not a constraint here the way it is above.
            Task::UnivariateEliminant => {}

            // msolve has **no lex order**. `-g` is grevlex only (`main.c:104-109`); `-e` builds a
            // two-block elimination order whose blocks are each degrevlex, which is not lex; and
            // the parametrization is a rational parametrization rather than a basis. Refused
            // rather than approximated by the eliminant, because conflating the two is exactly
            // what #257's taxonomy exists to stop.
            Task::LexBasis | Task::LexBasisByConversion => {
                return Support::No(Unsupported::Task { task })
            }

            // Over a prime field msolve's answer is the parametrization; its solution path is for
            // rational input, where it isolates *real* roots ("When input coefficients are
            // rational numbers: real solutions to the input system", `main.c:96-97`). Enumerating
            // `GF(p)` points from the parametrization is root-finding the caller would have to do,
            // and attributing that work to msolve would be measuring the adapter.
            Task::OneFiniteFieldSolution | Task::AllFiniteFieldSolutions => {
                return Support::No(Unsupported::Task { task })
            }

            // A cryptanalytic witness is checked against a primitive, not against a basis, and
            // belongs to the cryptanalysis scoreboard rather than the competitive board.
            Task::CryptanalyticWitness => return Support::No(Unsupported::Task { task }),
        }

        // msolve's input format carries a single integer characteristic on line 2
        // (`iofiles.c:556-562`); there is no syntax for an extension field at all, so a tool that
        // "accepted" one would be working over the prime subfield and answering a different
        // question.
        if !instance.field.is_prime_field() {
            return Support::No(Unsupported::ExtensionField {
                characteristic: instance.field.characteristic,
                extension_degree: instance.field.extension_degree,
            });
        }
        // The basis path's bound, which applies to every task.
        if instance.field.characteristic >= MAX_CHARACTERISTIC {
            return Support::No(Unsupported::Characteristic {
                characteristic: instance.field.characteristic,
                supported_below: MAX_CHARACTERISTIC,
            });
        }
        // The eliminant path's much lower one. Checked here rather than discovered by running,
        // because what msolve does above it is loop forever — see
        // [`MAX_CHARACTERISTIC_ELIMINANT`].
        if task == Task::UnivariateEliminant
            && instance.field.characteristic >= MAX_CHARACTERISTIC_ELIMINANT
        {
            return Support::No(Unsupported::Characteristic {
                characteristic: instance.field.characteristic,
                supported_below: MAX_CHARACTERISTIC_ELIMINANT,
            });
        }
        if instance.field.characteristic < MIN_CHARACTERISTIC {
            return Support::No(Unsupported::Representation {
                detail: format!(
                    "characteristic {} is not a prime field for msolve: 0 on line 2 of its input \
                     file means Q",
                    instance.field.characteristic
                ),
            });
        }

        if instance.variables.is_empty() {
            return Support::No(Unsupported::Representation {
                detail: "msolve needs at least one variable on line 1 of its input file"
                    .to_string(),
            });
        }
        if instance.system.is_empty() {
            return Support::No(Unsupported::Representation {
                detail: "msolve needs at least one generator".to_string(),
            });
        }
        // The input format is line- and comma-delimited with no quoting, so a generator carrying
        // either delimiter would be silently split into two. Refused rather than written out and
        // hoped for.
        for generator in &instance.system {
            if generator.contains('\n') || generator.contains(',') {
                return Support::No(Unsupported::Representation {
                    detail: "msolve's input format separates generators by commas and newlines, \
                             so a generator may contain neither"
                        .to_string(),
                });
            }
        }
        for name in &instance.variables {
            if name.is_empty() || name.contains(',') || name.contains('\n') {
                return Support::No(Unsupported::Representation {
                    detail: format!("{:?} is not a usable msolve variable name", name),
                });
            }
        }
        // msolve catches this itself — `iofiles.c:1005` exits 1 with "Duplicate variable name" —
        // but an instance with a repeated name is malformed before msolve is involved, and
        // `Unsupported` is the better place to say so than a non-zero exit.
        for (i, name) in instance.variables.iter().enumerate() {
            if instance.variables[i + 1..].contains(name) {
                return Support::No(Unsupported::Representation {
                    detail: format!("{:?} appears twice in the variable order", name),
                });
            }
        }

        // The third silent failure mode, and the only one of the three that is the *caller's*
        // mistake rather than msolve's. `store_exponent` (`iofiles.c:26-73`) splits a term on `*`
        // and matches each factor's name with a full `strcmp` against the declared list — which is
        // exactly why msolve is immune to the `x1`/`x10` prefix collision. But the matching loop
        // has no else:
        //
        // ```c
        // for (k = 0; k < gens->nvars; ++k) {
        //     if (strcmp(gens->vnames[k], var) == 0) {
        //         ((gens->exps) + pos)[k] = strtol(ev, NULL, 10);
        //         break;
        //     }
        // }
        // ```
        //
        // A factor naming nothing in the list is **silently dropped**. Measured: `x*z-1` with only
        // `x,y` declared is read as `x-1`, exit 0, `#invalid equations 0`, and the basis is of a
        // different ideal with no signal anywhere. So every identifier in every generator is
        // checked against the declared names here, before anything runs.
        for generator in &instance.system {
            if let Some(unknown) = unknown_identifier(generator, &instance.variables) {
                return Support::No(Unsupported::Representation {
                    detail: format!(
                        "the generator {:?} names {:?}, which is not in the variable order {}; \
                         msolve would drop that factor silently",
                        generator,
                        unknown,
                        instance.variables.join(", ")
                    ),
                });
            }
        }

        Support::Yes
    }

    fn run(&mut self, instance: &Instance, task: Task, limits: &Limits) -> RunReport {
        // Cloned out of `self` before the closure exists, so that `paths` can still take
        // `&mut self` to number this run's scratch files.
        let known_version = self.version.clone();
        let finish = |status: RunStatus,
                      measurement: Measurement,
                      command: Option<String>,
                      log: Option<PathBuf>| {
            let mut report = RunReport::new("msolve", instance, task, limits, status, measurement);
            if let Some(version) = &known_version {
                report = report.with_version(version.clone());
            }
            if let Some(command) = command {
                report = report.with_command_line(command);
            }
            if let Some(log) = log {
                report = report.with_log_path(log);
            }
            report
        };

        // Repeated inside `run` rather than assumed of the caller: a harness that forgot
        // `supports` must still get `Unsupported` and not a number.
        if let Support::No(reason) = self.supports(instance, task) {
            return finish(
                RunStatus::Unsupported(reason),
                Measurement::unmeasured(),
                None,
                None,
            );
        }

        let (input_path, output_path, log_path) = self.paths();

        // `-v 1` is mandatory, not optional: at the default `-v 0` msolve prints nothing at all,
        // and the stage timings and the `COMPUTATIONAL DATA` cross-checks only exist above it.
        let mut invocation = Invocation::new(&self.binary, &self.work_dir, &log_path)
            .arg("-f")
            .arg(&input_path)
            .arg("-o")
            .arg(&output_path)
            .arg("-v")
            .arg("1")
            // `-t` defaults to 1 (`main.c:76-78`), so an unflagged msolve is serial. Setting it
            // from the declared limit is what makes the worker count a property of the comparison
            // rather than of each tool's defaults.
            .arg("-t")
            .arg(limits.workers.max(1).to_string());
        if task == Task::ReducedGrobnerBasis {
            // `-g 2` prints the full reduced basis **and stops** there, so it times the Gröbner
            // stage alone; `-g 0` goes on to the parametrization.
            invocation = invocation.arg("-g").arg("2");
        }
        // Tool caps are recorded in `Limits` as the flags that set them, so they are passed
        // through verbatim. A cap that changes the output format will fail the header assertions
        // and be reported as a failure, which is the safe direction.
        for cap in &limits.tool_caps {
            invocation = invocation.args(cap.split_whitespace());
        }

        let command = invocation.command_line();
        // The absent-tool path, settled before any scratch work and before the supervisor's clock:
        // an absent msolve is a row that was not attempted, and neither the wall budget nor a
        // failed write may stand between that fact and the report of it (#391). No log file is
        // named, because none was opened.
        if let Some(absent) = invocation.unavailable() {
            return finish(
                RunStatus::Failed(RunFailure::from(absent)),
                Measurement::unmeasured(),
                Some(command),
                None,
            );
        }

        // The two writes below are the harness's own, so a failure of either is a skipped row
        // rather than a failed solve: msolve was never started, and a full disk, an exhausted fd
        // table or an unwell `/tmp` says nothing about it (#610).
        if let Err(e) = std::fs::create_dir_all(&self.work_dir) {
            return finish(
                RunStatus::Failed(RunFailure::Harness {
                    detail: format!("{}: {}", self.work_dir.display(), e),
                }),
                Measurement::unmeasured(),
                None,
                None,
            );
        }
        if let Err(e) = std::fs::write(&input_path, input_file(instance)) {
            return finish(
                RunStatus::Failed(RunFailure::Harness {
                    detail: format!("{}: {}", input_path.display(), e),
                }),
                Measurement::unmeasured(),
                None,
                None,
            );
        }
        // msolve clears `-o` itself at `main.c:581-589`, but only once it has got far enough to
        // parse its arguments. Removing it here means a file from a crashed earlier run can never
        // be parsed as this run's answer.
        let _ = std::fs::remove_file(&output_path);

        let process = match Supervisor::new(limits.wall).run(&invocation) {
            Ok(process) => process,
            Err(e) => {
                // The absent-tool path. A sweep records the row as not attempted and continues;
                // nothing about Zeebra follows from it.
                return finish(
                    RunStatus::Failed(RunFailure::from(e)),
                    Measurement::unmeasured(),
                    Some(command),
                    Some(log_path),
                );
            }
        };

        let log = read_output(&log_path);
        let mut measurement = Measurement::of_process(&process);
        measurement.stages = parse_stages(&log);

        // Checked *before* the limit branch. A run we killed after msolve told us thousands of
        // times that the prime exceeds its FGLM bound is a refusal, not a lower bound on how long
        // msolve needs, and reporting it as a wall-clock stop would file a defect as slowness.
        // `supports` already rejects the characteristics that cause this, so reaching here means
        // either a caller bypassed it or msolve has a bound this adapter has not found yet —
        // which is exactly when the tool's own words are worth more than the adapter's inference.
        if log.contains(FGLM_PRIME_TOO_LARGE) {
            let quoted = log
                .lines()
                .find(|line| line.contains(FGLM_PRIME_TOO_LARGE))
                .unwrap_or(FGLM_PRIME_TOO_LARGE)
                .trim();
            return finish(
                RunStatus::Failed(RunFailure::Reported {
                    message: format!(
                        "msolve's sparse-FGLM refused the prime and its genericity handler retried \
                         without bound: {:?}. msolve's own guard is 1518500213 \
                         (fglm_core.c:1385); this adapter stops at the documented-safe {} \
                         (linalg-fglm.c:38).",
                        quoted, MAX_CHARACTERISTIC_ELIMINANT
                    ),
                }),
                measurement,
                Some(command),
                Some(log_path),
            );
        }

        if process.timed_out {
            // Not a failure and not a speed result: the wall time is the limit, so the status says
            // so and `is_timing_evidence` keeps it out of every ratio.
            return finish(
                RunStatus::StoppedByLimit(LimitStop::WallClock {
                    limit: limits.wall,
                    elapsed: measurement.wall,
                }),
                Measurement {
                    cpu: None,
                    cpu_basis: CpuBasis::Unavailable,
                    peak_rss_bytes: measurement.peak_rss_bytes,
                    rss_basis: measurement.rss_basis,
                    wall: limits.wall,
                    stages: measurement.stages,
                },
                Some(command),
                Some(log_path),
            );
        }
        if !process.succeeded() {
            return finish(
                RunStatus::Failed(failure_from_log(&log, process.exit_code)),
                measurement,
                Some(command),
                Some(log_path),
            );
        }

        let output = read_output(&output_path);
        let answer = match task {
            Task::ReducedGrobnerBasis => parse_basis(&output, instance, &log),
            Task::UnivariateEliminant => match parse_parametrization(&output) {
                Ok(parametrization) => eliminant_answer(parametrization, instance, &log),
                Err(failure) => Err(failure),
            },
            // `supports` refuses every other task, so arriving here is a harness bug.
            other => Err(RunFailure::Incomplete {
                detail: format!("this adapter has no msolve invocation for {}", other),
            }),
        };

        match answer {
            // `Complete`, never `Verified`: msolve answered and nothing independent has checked
            // it. Promotion is the harness's job against another implementation's `Invariants`,
            // and is deliberately out of an adapter's reach.
            Ok(answer) => finish(
                RunStatus::Complete(answer),
                measurement,
                Some(command),
                Some(log_path),
            ),
            Err(failure) => finish(
                RunStatus::Failed(failure),
                measurement,
                Some(command),
                Some(log_path),
            ),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{
        computational_datum, eliminant_answer, failure_from_log, input_file, leading_monomial,
        parse_basis, parse_list, parse_parametrization, parse_stages, render_eliminant,
        unknown_identifier, MsolveSolver, Parametrization, MAX_CHARACTERISTIC,
        MAX_CHARACTERISTIC_ELIMINANT, MAX_STAGES,
    };
    use crate::{
        fields::PrimeFieldElement64,
        grobner::{
            benchmark_systems::{cyclic, katsura},
            differential::monomial_to_string,
            external::{
                corpus, ExternalSolver, FieldSpec, Instance, Invariants, Limits, Measurement,
                RunFailure, RunReport, RunStatus, Support, Task, Unsupported,
                REFERENCE_CHARACTERISTIC,
            },
            f4, f4_with_options, F4Options,
        },
        FiniteField, MonomialOrder, MultivariatePolynomial,
    };
    use std::time::Duration;

    const GREVLEX: MonomialOrder = MonomialOrder::GradedReverseLexicographic;
    /// The corpus's reference field, `2^31 - 1`. Also msolve's own ceiling less one, so the basis
    /// fixtures pin that the top of the supported range works — and it is **above** the eliminant
    /// ceiling, which is why the eliminant rungs use `P30`.
    const P31: u64 = REFERENCE_CHARACTERISTIC;
    /// The corpus's reference field type, for recomputing a rung's basis in Zeebra.
    type Reference = PrimeFieldElement64<REFERENCE_CHARACTERISTIC>;
    /// The prime the recorded parametrization fixtures were taken over, `2^30 + 3`. Below
    /// [`MAX_CHARACTERISTIC_ELIMINANT`], which `P31` is not.
    ///
    /// Taken from the corpus rather than written again: the corpus generates over the prime it
    /// declares, so a rung at a prime the corpus has no compiled field for is `None` — and a
    /// literal here would make that a panic in these tests instead of a build error.
    const P30: u64 = corpus::ALTERNATE_CHARACTERISTIC;

    // ---------------------------------------------------------------------------------------
    // Fixtures. Every one is **verbatim output of msolve 0.11.0** on this machine, captured on
    // 2026-11-06 from an input file this adapter's own `input_file` generated. Recorded rather
    // than re-run so that the parse, the normalization and the agreement with Zeebra are all
    // tested in CI with no msolve installed.
    // ---------------------------------------------------------------------------------------

    /// `msolve -g 2` on **the corpus's `katsura-4`** at [`REFERENCE_CHARACTERISTIC`], the exact
    /// instance #263's sweep will run — digest `825a3aa54e15…`, matching `corpus::ladder`'s frozen
    /// value. Captured from `input_file(corpus::instance("katsura-4", ..))`.
    const KATSURA_4_BASIS: &str = "\
#Reduced Groebner basis data
#---
#field characteristic: 2147483647
#variable order:       x1, x2, x3, x4
#monomial order:       graded reverse lexicographical
#length of basis:      7 elements sorted by increasing leading monomials
#---
[1*x1^1+2*x2^1+2*x3^1+2*x4^1+2147483646,
1*x3^2+2*x2^1*x4^1+920350139*x3^1*x4^1+306783382*x4^2+306783378*x2^1+1227133512*x3^1+613566755*x4^1,
1*x2^1*x3^1+2147483645*x2^1*x4^1+613566753*x3^1*x4^1+920350131*x4^2+1994091958*x2^1+1533916891*x3^1+1840700270*x4^1,
1*x2^2+2*x2^1*x4^1+1840700270*x3^1*x4^1+613566758*x4^2+613566756*x2^1+306783378*x3^1+1227133512*x4^1,
1*x3^1*x4^2+1908874354*x4^3+119304647*x2^1*x4^1+2120971503*x3^1*x4^1+318145725*x4^2+1391887549*x2^1+888156817*x3^1+636291451*x4^1,
1*x2^1*x4^2+715827882*x4^3+238609294*x2^1*x4^1+1391887549*x3^1*x4^1+1908874353*x4^2+1133394147*x2^1+1511192196*x3^1,
1*x4^4+1349709138*x4^3+1819697142*x2^1*x4^1+1238170675*x3^1*x4^1+1345692147*x4^2+440061417*x2^1+755127449*x3^1+912660465*x4^1]:
";

    /// `msolve -g 2` on **the corpus's `cyclic-4`** at [`REFERENCE_CHARACTERISTIC`], digest
    /// `e1d8d59448b3…`.
    ///
    /// cyclic-4 is **positive-dimensional** (`benchmark_systems.rs:10-15`), which does not stop it
    /// having a perfectly good grevlex basis — it stops it having an eliminant, which is a
    /// separate fixture below.
    const CYCLIC_4_BASIS: &str = "\
#Reduced Groebner basis data
#---
#field characteristic: 2147483647
#variable order:       x1, x2, x3, x4
#monomial order:       graded reverse lexicographical
#length of basis:      7 elements sorted by increasing leading monomials
#---
[1*x1^1+1*x2^1+1*x3^1+1*x4^1,
1*x2^2+2*x2^1*x4^1+1*x4^2,
1*x2^1*x3^2+1*x3^2*x4^1+2147483646*x2^1*x4^2+2147483646*x4^3,
1*x2^1*x3^1*x4^2+1*x3^2*x4^2+2147483646*x2^1*x4^3+1*x3^1*x4^3+2147483646*x4^4+2147483646,
1*x2^1*x4^4+1*x4^5+2147483646*x2^1+2147483646*x4^1,
1*x3^3*x4^2+1*x3^2*x4^3+2147483646*x3^1+2147483646*x4^1,
1*x3^2*x4^4+1*x2^1*x3^1+2147483646*x2^1*x4^1+1*x3^1*x4^1+2147483645*x4^2]:
";

    /// `msolve -g 1` on `x^2*y+1, x*y^2+x+1` over `GF(1073741827)` with **`x,y`** on line 1.
    ///
    /// Half of the variable-order witness: the same two generators under the other order give a
    /// basis of a different *cardinality*, so no amount of coefficient normalization could
    /// reconcile them.
    const ASYMMETRIC_X_FIRST: &str = "\
#Leading ideal data
#---
#field characteristic: 1073741827
#variable order:       x, y
#monomial order:       graded reverse lexicographical
#length of basis:      3 elements sorted by increasing leading monomials
#---
[x^1*y^1,
x^2,
y^3]:
";

    /// The same two generators with **`y,x`** on line 1. Two leading monomials, not three.
    const ASYMMETRIC_Y_FIRST: &str = "\
#Reduced Groebner basis data
#---
#field characteristic: 1073741827
#variable order:       y, x
#monomial order:       graded reverse lexicographical
#length of basis:      2 elements sorted by increasing leading monomials
#---
[1*x^2+1073741826*y^1+1*x^1,
1*y^2+1073741826*y^1*x^1+1]:
";

    /// The default mode on `x^2-2, y-x-1` over `GF(1073741827)`: generic, so the variable list is
    /// untouched and the linear form is the last variable alone.
    const GENERIC_PARAMETRIZATION: &str = "\
[0, [1073741827,
2,
2,
['x', 'y'],
[0, 1],
[1,
[[2,
[1073741826, 1073741825, 1]],
[0,
[1]],
[
[[1,
[1, 1073741826]]]
]]]]]:
";

    /// The default mode on the smoke system over `GF(1073741827)`.
    ///
    /// **The silent failure.** Exit 0, a well-formed parametrization, and a fourth variable `A`
    /// that was never in the input — msolve's genericity recovery substituting a problem it could
    /// solve. Truncated after the eliminant, which is all the parser reads.
    const ADDED_VARIABLE_PARAMETRIZATION: &str = "\
[0, [1073741827,
4,
12,
['x', 'y', 'z', 'A'],
[1,2,3,1],
[1,
[[12,
[3083428, 62208, 1072369795, 17280, 321120, 432, 1073707323, 0, 2160, 0, 1073741755, 0, 1]],
[0,
[1]],
[
[[11,
[311843434, 18732829, 277220721, 227251407, 410133853, 509849746, 1013921499, 597713747, 848965636, 1013763370, 376241973, 501401011]]]
]]]]]:
";

    /// The default mode on `cyclic::<4>` over `GF(1073741827)`: `-1` in the third field.
    const POSITIVE_DIMENSIONAL: &str = "[1, 4, -1, []]:\n";

    /// The default mode on `x-1, x-2, y-1`: the variety is empty.
    const NO_SOLUTION: &str = "[-1]:\n";

    /// The verbose log of `msolve -f katsura-4.ms -g 2 -v 1`, trimmed to the two blocks the
    /// adapter reads. The figures really are `0.00`: msolve's resolution is 10 ms and katsura-4
    /// takes under a millisecond, which is itself worth pinning.
    const KATSURA_4_LOG: &str = "
---------------- TIMINGS ----------------
overall(elapsed)        0.00 sec
overall(cpu)            0.00 sec
select                  0.00 sec   4.9%
symbolic prep.          0.00 sec   5.9%
update                  0.00 sec  35.4%
convert                 0.00 sec  13.0%
linear algebra          0.00 sec   8.0%
reduce gb               0.00 sec   0.0%
-----------------------------------------

---------- COMPUTATIONAL DATA -----------
size of basis                     7
#terms in basis                  49
-----------------------------------------
";

    /// msolve's three `TIMINGS` writers in the order a parametrization run emits them, with the
    /// seconds scaled above the 10 ms resolution so the values can be asserted. The labels and the
    /// layout are byte-for-byte msolve's.
    const THREE_BLOCK_LOG: &str = "
---------------- TIMINGS ----------------
overall(elapsed)        1.50 sec
overall(cpu)            1.50 sec
select                  0.10 sec   3.8%
symbolic prep.          0.20 sec   4.1%
update                  0.30 sec  25.0%
convert                 0.40 sec  25.4%
linear algebra          0.50 sec   6.8%
reduce gb               0.00 sec   0.0%
-----------------------------------------

---------- COMPUTATIONAL DATA -----------
size of basis                    22
-----------------------------------------


---------------- TIMINGS ----------------
overall(elapsed)        2.25 sec
overall(cpu)            2.25 sec
-----------------------------------------

---------- COMPUTATIONAL DATA -----------
degree of ideal                  32
deg. elim. pol.                  32
-----------------------------------------


---------------- TIMINGS ----------------
rational param(elapsed)         0.75 sec
rational param(cpu)             0.75 sec
-----------------------------------------
";

    // ---------------------------------------------------------------------------------------
    // Helpers
    // ---------------------------------------------------------------------------------------

    fn instance(name: &str, characteristic: u64, variables: &[&str], system: &[&str]) -> Instance {
        Instance::new(
            name,
            "test",
            FieldSpec::prime(characteristic),
            variables.iter().map(|v| v.to_string()).collect(),
            system.iter().map(|s| s.to_string()).collect(),
            GREVLEX,
        )
    }

    fn pair(characteristic: u64) -> Instance {
        instance(
            "pair",
            characteristic,
            &["x1", "x2"],
            &["x1^2+x2", "x2^2-1"],
        )
    }

    /// Where one test's scratch files go, so that a test can also assert what is *not* written.
    fn scratch_root(tag: &str) -> std::path::PathBuf {
        std::env::temp_dir().join(format!(
            "zeebra-msolve-solver-{}-{}-{:?}",
            tag,
            std::process::id(),
            std::thread::current().id()
        ))
    }

    fn solver(binary: &str, tag: &str) -> MsolveSolver {
        MsolveSolver::new(binary, scratch_root(tag))
    }

    /// A corpus rung as the rendered [`Instance`] #263's sweep will hand msolve.
    ///
    /// **Digest-identical** to the sweep's, including the `x1..xN` naming — which is the naming
    /// with the `x1`/`x10` prefix hazard in it. Separate from [`corpus_pair`] so that a caller
    /// wanting only the instance does not ask for an oracle it then discards: several rungs here
    /// are built at [`P30`], where an oracle over [`Reference`] would be over the *wrong field*.
    fn corpus_instance(name: &str, characteristic: u64) -> Instance {
        corpus::instance(name, characteristic, GREVLEX)
            .unwrap_or_else(|| panic!("{} is a corpus rung", name))
    }

    /// A corpus instance, and Zeebra's own invariants for it under grevlex.
    ///
    /// Zeebra's side is computed here and now, so an agreement test is live Zeebra against
    /// recorded msolve rather than two recordings.
    ///
    /// Panics if the rung has no oracle. Every caller names its rung as a literal at [`P31`], so
    /// that is a programming error rather than a gap; the ladder-wide test uses
    /// [`has_compiled_pair`] and [`zeebra_oracle`] directly, because it needs to tell a rung with
    /// no oracle from one whose oracle ran out of budget.
    fn corpus_pair(name: &str, characteristic: u64) -> (Instance, Invariants) {
        let instance = corpus_instance(name, characteristic);
        let invariants = zeebra_oracle(&instance).unwrap_or_else(|| {
            panic!(
                "no oracle for {} at characteristic {}",
                name, characteristic
            )
        });
        (instance, invariants)
    }

    /// The variable counts Zeebra's side has a compiled instantiation for.
    ///
    /// The whole coupling this list replaces: the dispatch used to be on **family name**, so each
    /// of the twelve families #324 added needed an edit in two places before it had an oracle, and
    /// had none until someone made it. Dispatching on width means a family added at a count
    /// already here is covered with no edit at all. Only a genuinely new width needs a line — and
    /// [`zeebra_oracle`] panics rather than silently reporting "no oracle" if this list and its
    /// match ever disagree.
    const COMPILED_WIDTHS: &[usize] = &[4, 5, 6, 7, 8, 9, 10, 11, 14];

    /// Whether a rung can have an oracle at all, from its field and its width alone.
    ///
    /// Cheap by design: it runs no F4, so the ladder-wide coverage assertion can cover all
    /// twenty-six rungs without computing a fourteen-variable basis.
    ///
    /// The field check is not a formality. Parsing a rung's text into [`Reference`] reduces its
    /// coefficients modulo [`REFERENCE_CHARACTERISTIC`], so an oracle built for a rung over any
    /// other prime would be an answer to a different problem — silently.
    fn has_compiled_pair(instance: &Instance) -> bool {
        instance.field.characteristic == REFERENCE_CHARACTERISTIC
            && COMPILED_WIDTHS.contains(&instance.variables.len())
    }

    /// Zeebra's invariants for a rung, by **parsing the rung's own text**.
    ///
    /// `None` for two different reasons, which [`has_compiled_pair`] separates: the rung has no
    /// oracle (another field, or an uncompiled width), or Zeebra's own F4 crossed
    /// [`ZEEBRA_ORACLE_BUDGET`]. Neither is a disagreement, and a caller must not report them as
    /// one.
    ///
    /// # Why parse rather than re-instantiate the family
    ///
    /// Rebuilding from `katsura::<4, _>()` *assumes* that the rendered corpus text and the typed
    /// generator agree. Parsing the text instead means **the bytes checked are the bytes every
    /// engine is handed**: the corpus renders through `polynomial_to_string` and this reads back
    /// through `parse`, so a round-trip failure in either direction surfaces as a disagreement
    /// rather than as a silently different problem.
    ///
    /// That matters most for msolve. The one hazard cross-engine agreement structurally *cannot*
    /// catch is text misread identically by everything, because every engine was handed the same
    /// bytes — and `iofiles.c:57-62` has no `else`, so a factor naming a variable not on line 1 is
    /// **silently dropped**. The fourteen-variable rungs are where that is live.
    fn zeebra_oracle(instance: &Instance) -> Option<Invariants> {
        if !has_compiled_pair(instance) {
            return None;
        }
        let leading = match instance.variables.len() {
            4 => zeebra_leading_parsed::<4>(instance),
            5 => zeebra_leading_parsed::<5>(instance),
            6 => zeebra_leading_parsed::<6>(instance),
            7 => zeebra_leading_parsed::<7>(instance),
            8 => zeebra_leading_parsed::<8>(instance),
            9 => zeebra_leading_parsed::<9>(instance),
            10 => zeebra_leading_parsed::<10>(instance),
            11 => zeebra_leading_parsed::<11>(instance),
            14 => zeebra_leading_parsed::<14>(instance),
            // `has_compiled_pair` admitted this width, so a missing arm is a bug in this file and
            // not a rung without an oracle. Reporting it as the latter is how a rung quietly loses
            // its oracle, which is the recurring defect this issue exists to remove.
            other => panic!("COMPILED_WIDTHS admits {} with no dispatch arm", other),
        }?;
        Some(Invariants::none().with_leading_monomials(leading))
    }

    /// How long Zeebra's own F4 is given per rung when it is acting as the oracle.
    ///
    /// Not a measurement and not a claim about Zeebra's speed — it is the budget that keeps this
    /// test runnable. The default `F4Options` limits are *resource* bounds with `max_wall_time`
    /// unset, so a hard rung such as fourteen random quadratics in fourteen variables can grind
    /// for a long time before crossing one. An oracle slower than the tool it checks makes the
    /// test impractical to run, which is how a test stops being run and therefore stops being
    /// true. It is also symmetric with the external side, which always gets a `Limits::wall`.
    ///
    /// The same budget and the same reasoning as `tests/external_comparands.rs`.
    ///
    /// **It is not a reliable bound, which is why [`DEFAULT_ORACLE_WIDTH_CEILING`] exists too.**
    /// The check is cooperative and happens once per batch (`src/grobner/f4/mod.rs:416`), so a
    /// single long matrix reduction overruns it: measured here, `mq-random-10` ran past **ten
    /// minutes** under this 120-second budget. The budget still earns its place for rungs where a
    /// batch boundary arrives in time; it just cannot be the only guard.
    const ZEEBRA_ORACLE_BUDGET: Duration = Duration::from_secs(120);

    /// The widest rung the live ladder test builds an oracle for unless asked otherwise.
    ///
    /// **A test-runtime bound, not a capability claim.** [`zeebra_oracle`] handles every width in
    /// [`COMPILED_WIDTHS`]; this only decides what one `cargo test` pays for by default, because
    /// `test_a_real_msolve_agrees_with_zeebra_on_katsura_and_cyclic` is deliberately **not**
    /// `#[ignore]`d — it runs whenever msolve is installed.
    ///
    /// Measured on the provisioning machine: the rungs at or below seven variables built their
    /// oracles in **1.4 seconds in total**, while `mq-random-10` alone did not finish in ten
    /// minutes. A test that takes ten minutes stops being run, and a test that stops being run
    /// stops being true.
    ///
    /// **That figure is now ~29 s, and the ceiling was kept at 7 anyway.** #424 added `cyclic-7`,
    /// which is also seven variables and about fifteen times `katsura-7`'s cost — width is a crude
    /// proxy for work, and this is where that shows. The trade was taken deliberately: `cyclic-7`
    /// is the top of the *reachable* cyclic family and the rung whose `D = 924` is the one
    /// externally published count the crate can check, so an oracle for it is worth having on every
    /// `cargo test`. Twenty-nine seconds is still two orders of magnitude inside the threshold the
    /// paragraph above sets. Lowering the ceiling to 6 would buy the time back and cost both
    /// `katsura-7`'s and `cyclic-7`'s coverage, which is the worse half of the trade.
    ///
    /// `ZEEBRA_FULL_CORPUS_ORACLE=1` lifts it, for a machine that wants the eight- to
    /// fourteen-variable rungs covered. Rungs left out are **printed**, never silently dropped.
    const DEFAULT_ORACLE_WIDTH_CEILING: usize = 7;

    /// [`DEFAULT_ORACLE_WIDTH_CEILING`], or no ceiling when `ZEEBRA_FULL_CORPUS_ORACLE` is set.
    fn oracle_width_ceiling() -> usize {
        if std::env::var_os("ZEEBRA_FULL_CORPUS_ORACLE").is_some() {
            usize::MAX
        } else {
            DEFAULT_ORACLE_WIDTH_CEILING
        }
    }

    /// The leading monomials of Zeebra's grevlex basis of `instance`, parsed from its own text.
    ///
    /// `None` when Zeebra's F4 crosses one of its `F4Options` limits, including
    /// [`ZEEBRA_ORACLE_BUDGET`]. A parse failure is **not** folded into that: the corpus text is
    /// Zeebra's own rendering, so failing to read it back is a defect rather than a budget, and it
    /// panics with the offending generator.
    fn zeebra_leading_parsed<const N: usize>(instance: &Instance) -> Option<Vec<String>> {
        let names: Vec<&str> = instance.variable_refs();
        let fixed: [&str; N] = names.clone().try_into().ok()?;
        let system: Vec<MultivariatePolynomial<N, Reference>> = instance
            .system
            .iter()
            .map(|generator| {
                MultivariatePolynomial::parse(generator, fixed).unwrap_or_else(|e| {
                    panic!(
                        "Zeebra cannot parse its own corpus text {:?}: {}",
                        generator, e
                    )
                })
            })
            .collect();
        let options = F4Options {
            max_wall_time: Some(ZEEBRA_ORACLE_BUDGET),
            ..F4Options::default()
        };
        let (basis, _statistics) = f4_with_options(&system, GREVLEX, &options).ok()?;
        Some(
            basis
                .iter()
                .map(|p| monomial_to_string(&p.leading_monomial(GREVLEX), &names))
                .collect(),
        )
    }

    /// The corpus rungs that can have no Zeebra oracle, and why.
    ///
    /// **Not a coverage gap — a correct residue.** Poseidon carries KoalaBear and Anemoi
    /// `2^64 - 353`, and neither shares [`Reference`]'s type, so each needs a second *field type*
    /// rather than a second match arm. Every rung at the reference field now has an oracle
    /// whatever its family, because the dispatch is on [`COMPILED_WIDTHS`].
    ///
    /// Asserted two-sidedly, so a rung that silently *gained* coverage is caught as well as one
    /// that lost it (#338's contribution, kept).
    const WITHOUT_A_COMPILED_PAIR: &[&str] = &[
        "poseidon-t2-rf2-rp0-planted",
        "poseidon-t2-rf2-rp2-planted",
        "poseidon-t2-rf4-rp0-planted",
        "anemoi64-cico-n1-fcico",
        "anemoi64-cico-n2-fcico",
    ];

    /// Every rung at the reference field has an oracle; only the other-field ones do not.
    ///
    /// The property #345 is about. The dispatch is on **variable count**, so a family added at a
    /// width already present — 4, 5, 6, 7, 10 or 14 — is covered with no edit here, and
    /// [`WITHOUT_A_COMPILED_PAIR`] shrinks to the rungs that are genuinely out of reach. The
    /// previous dispatch was on family name, so each of the twelve families #324 added arrived
    /// with no oracle until someone wrote a match arm.
    ///
    /// Deliberately checks the *decision* and not the oracle: `has_compiled_pair` reads the
    /// instance's characteristic and width, so this covers all twenty-six rungs without running
    /// Zeebra's F4 on a fourteen-variable system.
    #[test]
    fn test_every_reference_field_rung_has_a_compiled_oracle() {
        let mut without: Vec<&str> = Vec::new();
        for entry in corpus::ladder() {
            let instance = corpus_instance(entry.name, P31);
            if !has_compiled_pair(&instance) {
                without.push(entry.name);
                continue;
            }
            assert_eq!(
                instance.field.characteristic, P31,
                "{}: an oracle at another field would parse into the wrong one",
                entry.name
            );
            assert!(
                COMPILED_WIDTHS.contains(&instance.variables.len()),
                "{}: {} variables",
                entry.name,
                instance.variables.len()
            );
        }
        without.sort_unstable();
        let mut expected = WITHOUT_A_COMPILED_PAIR.to_vec();
        expected.sort_unstable();
        assert_eq!(
            without, expected,
            "a corpus rung gained or lost a compiled Zeebra side; see #333"
        );
    }

    /// The rungs with no oracle are exactly the ones carrying their own field, not their own name.
    ///
    /// Poseidon is over KoalaBear and Anemoi over `2^64 - 353`; neither shares [`Reference`]'s
    /// type, so each needs a second field type rather than a second match arm. That residue is
    /// correct rather than a coverage gap, and this test is what says so.
    #[test]
    fn test_the_rungs_without_an_oracle_are_the_ones_at_another_field() {
        for name in WITHOUT_A_COMPILED_PAIR {
            let instance = corpus_instance(name, P31);
            assert_ne!(
                instance.field.characteristic, P31,
                "{}: it is at the reference field, so it should have an oracle",
                name
            );
        }
        assert_eq!(
            WITHOUT_A_COMPILED_PAIR.len(),
            5,
            "three Poseidon rungs and two Anemoi rungs"
        );
    }

    /// Parsing the rung's own text gives the same basis as instantiating the family in Rust.
    ///
    /// The guard on replacing the route. Rebuilding from `katsura::<4, _>()` *assumes* that the
    /// rendered corpus text and the typed generator agree; parsing the text instead makes a
    /// round-trip failure in either direction show up, because the bytes parsed are the bytes
    /// every engine is handed. This asserts the two routes coincide where both exist, so the
    /// change is a strengthening rather than a substitution.
    #[test]
    fn test_the_parsed_oracle_agrees_with_the_instantiated_one() {
        // Both sides go through `with_leading_monomials`, which sorts: the initial ideal is a
        // *set*, so comparing print order would be comparing something that carries no meaning.
        let instantiated =
            |leading: Vec<String>| Invariants::none().with_leading_monomials(leading);

        let katsura_4 = corpus_instance("katsura-4", P31);
        let refs: Vec<&str> = katsura_4.variable_refs();
        assert_eq!(
            zeebra_oracle(&katsura_4).expect("katsura-4 has an oracle"),
            instantiated(zeebra_leading(&katsura::<4, Reference>(), &refs)),
            "parsing katsura-4's text must give the basis katsura::<4> does"
        );

        let cyclic_4 = corpus_instance("cyclic-4", P31);
        let refs: Vec<&str> = cyclic_4.variable_refs();
        assert_eq!(
            zeebra_oracle(&cyclic_4).expect("cyclic-4 has an oracle"),
            instantiated(zeebra_leading(&cyclic::<4, Reference>(), &refs)),
            "parsing cyclic-4's text must give the basis cyclic::<4> does"
        );
    }

    /// The leading monomials of Zeebra's grevlex basis, rendered with `variables`.
    fn zeebra_leading<const N: usize, F: FiniteField>(
        system: &[MultivariatePolynomial<N, F>],
        variables: &[&str],
    ) -> Vec<String> {
        f4(system, GREVLEX)
            .expect("Zeebra computes a basis for a corpus rung")
            .iter()
            .map(|p| monomial_to_string(&p.leading_monomial(GREVLEX), variables))
            .collect()
    }

    /// The msolve binary, when one is installed where the M25 provisioning puts it.
    ///
    /// Returns `None` otherwise, which is how the live tests skip: CI has no msolve and must not
    /// need one, so nothing below may assert on its presence.
    fn installed_binary() -> Option<String> {
        let path = std::path::Path::new(env!("HOME"))
            .join(".local/opt/zeebra-ext/bin/msolve")
            .to_string_lossy()
            .into_owned();
        let found = std::path::Path::new(&path).is_file().then_some(path);
        if found.is_none() {
            // Three outcomes, not two. A test that returns early on an absent tool is
            // indistinguishable in the harness's output from one that ran and agreed, which is
            // how a panic on the mq/poseidon rungs reached `main` with CI green: CI has no
            // msolve, so the only machine that runs these for real is the one no automated
            // check covers (#333). The line below makes "not checked" say so, and
            // `ZEEBRA_REQUIRE_MSOLVE=1` turns absence into a failure for any environment that
            // does have the binary and wants to assert coverage rather than hope for it.
            // This is the same discipline `zb-claim.sh` applies to a board read and
            // `Outcome::instead_of_a_time` applies to a row that carries no wall time.
            eprintln!("msolve NOT CHECKED: no binary at $HOME/.local/opt/zeebra-ext/bin/msolve");
            assert!(
                std::env::var_os("ZEEBRA_REQUIRE_MSOLVE").is_none(),
                "ZEEBRA_REQUIRE_MSOLVE is set and msolve is absent: coverage was asserted, \
                 not obtained"
            );
        }
        found
    }

    // ---------------------------------------------------------------------------------------
    // Input conversion: the variable order
    // ---------------------------------------------------------------------------------------

    /// The input file is variables, characteristic, then one generator per line without a trailing
    /// comma — msolve's three-part format.
    #[test]
    fn test_the_input_file_has_msolves_three_parts() {
        let text = input_file(&pair(P30));
        assert_eq!(text, "x1,x2\n1073741827\nx1^2+x2,\nx2^2-1\n");
        assert!(
            !text.trim_end().ends_with(','),
            "msolve rejects a trailing comma after the last generator"
        );
    }

    /// Line 1 is the instance's variable order verbatim, because for msolve that line *is* the
    /// order.
    #[test]
    fn test_line_one_is_the_instances_variable_order_verbatim() {
        let forward = instance("f", P30, &["x", "y", "z"], &["x+y+z"]);
        let reversed = instance("r", P30, &["z", "y", "x"], &["x+y+z"]);
        assert_eq!(input_file(&forward).lines().next(), Some("x,y,z"));
        assert_eq!(input_file(&reversed).lines().next(), Some("z,y,x"));
        // And the two are different problems to the contract as well as to msolve.
        assert_ne!(forward.digest(), reversed.digest());
    }

    // ---------------------------------------------------------------------------------------
    // Leading monomials
    // ---------------------------------------------------------------------------------------

    /// A leading monomial drops msolve's explicit coefficient and its `^1` exponents, matching
    /// Zeebra's rendering.
    #[test]
    fn test_the_leading_monomial_is_normalized_to_zeebras_rendering() {
        assert_eq!(leading_monomial("1*x^1*y^1+1*x^1*z^1"), "x*y");
        assert_eq!(leading_monomial("920350139*u2^2+2*u1^1"), "u2^2");
        assert_eq!(leading_monomial("1*u1^1*u3^12+1*u3^1"), "u1*u3^12");
        // `-g 1` prints the same monomial with no coefficient at all.
        assert_eq!(leading_monomial("x^1*y^1"), "x*y");
        assert_eq!(leading_monomial("y^3"), "y^3");
    }

    /// A basis element that is a nonzero constant has leading monomial `1`, not the empty string.
    #[test]
    fn test_a_constant_element_has_leading_monomial_one() {
        assert_eq!(leading_monomial("1"), "1");
        assert_eq!(leading_monomial("1073741826"), "1");
    }

    // ---------------------------------------------------------------------------------------
    // The variable-order hazard, which is the whole point
    // ---------------------------------------------------------------------------------------

    /// The same two generators give bases of **different cardinality** under a permuted variable
    /// order, so a wrong order cannot be rescued by normalizing coefficients.
    ///
    /// Both sides are recorded msolve output. This is the witness the adapter's order handling is
    /// defended by: three leading monomials under `x > y`, two under `y > x`.
    #[test]
    fn test_an_asymmetric_system_has_a_different_basis_under_a_permuted_order() {
        let x_first = instance("asym", P30, &["x", "y"], &["x^2*y+1", "x*y^2+x+1"]);
        let y_first = instance("asym", P30, &["y", "x"], &["x^2*y+1", "x*y^2+x+1"]);

        let under_x = parse_basis(ASYMMETRIC_X_FIRST, &x_first, "").expect("x-first parses");
        let under_y = parse_basis(ASYMMETRIC_Y_FIRST, &y_first, "").expect("y-first parses");

        assert_eq!(
            under_x.invariants.leading_monomials,
            Some(vec![
                "x*y".to_string(),
                "x^2".to_string(),
                "y^3".to_string()
            ])
        );
        assert_eq!(
            under_y.invariants.leading_monomials,
            Some(vec!["x^2".to_string(), "y^2".to_string()])
        );
        assert_eq!(under_x.invariants.basis_cardinality, Some(3));
        assert_eq!(under_y.invariants.basis_cardinality, Some(2));

        // The invariants genuinely disagree, and on something both sides reported.
        let disagreements = under_x.invariants.agree(&under_y.invariants);
        assert!(under_x.invariants.overlap(&under_y.invariants) > 0);
        assert!(
            !disagreements.is_empty(),
            "a permuted variable order must be visible as a disagreement"
        );
    }

    /// A header reporting a variable order other than the instance's is rejected, never parsed.
    ///
    /// The structural defence: even if the input file were written wrong, msolve's echo of the
    /// order it used does not match, and the run becomes a failure rather than an incomparable
    /// basis.
    #[test]
    fn test_a_basis_whose_header_reports_another_variable_order_is_rejected() {
        // The y-first output offered against an x-first instance.
        let x_first = instance("asym", P30, &["x", "y"], &["x^2*y+1", "x*y^2+x+1"]);
        match parse_basis(ASYMMETRIC_Y_FIRST, &x_first, "") {
            Err(RunFailure::SelfInconsistent { detail }) => {
                assert!(detail.contains("variable order"), "got {:?}", detail);
                assert!(detail.contains("y, x"), "got {:?}", detail);
            }
            other => panic!("expected a rejected variable order, got {:?}", other),
        }
    }

    // ---------------------------------------------------------------------------------------
    // Agreement with Zeebra, recorded
    // ---------------------------------------------------------------------------------------

    /// msolve's recorded katsura-4 basis agrees with Zeebra's freshly computed one.
    ///
    /// The Katsura rung of the correctness check: Zeebra runs F4 here and now, msolve's answer is
    /// the recorded fixture, and `agree` compares the leading monomials and the cardinality with a
    /// non-zero overlap asserted so the agreement is not vacuous.
    #[test]
    fn test_the_recorded_katsura_4_basis_agrees_with_zeebras() {
        let (instance, ours) = corpus_pair("katsura-4", P31);
        let theirs = parse_basis(KATSURA_4_BASIS, &instance, KATSURA_4_LOG)
            .expect("the recorded katsura-4 basis parses")
            .invariants;

        assert_eq!(ours.basis_cardinality, Some(7));
        assert!(
            ours.overlap(&theirs) >= 2,
            "both sides must report the leading monomials and the cardinality"
        );
        assert_eq!(
            ours.agree(&theirs),
            vec![],
            "msolve and Zeebra must agree on katsura-4"
        );
    }

    /// msolve's recorded cyclic-4 basis agrees with Zeebra's freshly computed one.
    ///
    /// The Cyclic rung. cyclic-4 is positive-dimensional, which is a fact about its *eliminant*
    /// and not about its grevlex basis — both engines produce the same seven leading monomials.
    #[test]
    fn test_the_recorded_cyclic_4_basis_agrees_with_zeebras() {
        let (instance, ours) = corpus_pair("cyclic-4", P31);
        let theirs = parse_basis(CYCLIC_4_BASIS, &instance, "")
            .expect("the recorded cyclic-4 basis parses")
            .invariants;

        assert_eq!(ours.basis_cardinality, Some(7));
        assert!(ours.overlap(&theirs) >= 2);
        assert_eq!(
            ours.agree(&theirs),
            vec![],
            "msolve and Zeebra must agree on cyclic-4"
        );
    }

    /// msolve's katsura convention is Zeebra's: `katN` is **N variables**, not `n + 1`.
    ///
    /// Pinned because external tools differ on it and `katsura::<N, F>()` is N = n + 1 variables
    /// (`benchmark_systems.rs:54-66`). msolve's shipped `input_files/kat6-31.ms` declares
    /// `x1..x6` — six variables — and its first equation is the linear one, matching
    /// `katsura::<6, F>()` term for term under `x_{j+1} = u_j`. So the two agree on the variable
    /// count for a given label and a row named `katsura-6` means the same system to both.
    #[test]
    fn test_the_katsura_convention_is_the_variable_count() {
        assert_eq!(
            katsura::<4, Reference>().len(),
            4,
            "katsura::<4> is four equations"
        );
        let instance = corpus_instance("katsura-4", P31);
        assert_eq!(instance.variables.len(), 4);
        // And msolve's echo of that input agrees it read four variables, under the corpus's own
        // `x1..xN` naming.
        assert_eq!(
            super::header(KATSURA_4_BASIS, "variable order"),
            Some("x1, x2, x3, x4".to_string())
        );
    }

    // ---------------------------------------------------------------------------------------
    // Header and list defences
    // ---------------------------------------------------------------------------------------

    /// A header characteristic that disagrees with the input file is self-inconsistent.
    #[test]
    fn test_a_header_characteristic_that_disagrees_is_self_inconsistent() {
        let wrong = instance("katsura-4", P30, &["x1", "x2", "x3", "x4"], &["x1"]);
        match parse_basis(KATSURA_4_BASIS, &wrong, "") {
            Err(RunFailure::SelfInconsistent { detail }) => {
                assert!(detail.contains("characteristic"), "got {:?}", detail)
            }
            other => panic!("expected self-inconsistent, got {:?}", other),
        }
    }

    /// A monomial-order header that is not plain grevlex is rejected.
    ///
    /// `-e` makes msolve print an elimination-order line instead (`iofiles.c:212-218`), and a
    /// two-block order is not the order the instance declared.
    #[test]
    fn test_an_elimination_order_header_is_rejected() {
        let elimination = KATSURA_4_BASIS.replace(
            "#monomial order:       graded reverse lexicographical",
            "#monomial order:       eliminating first variable, blocks: graded reverse lexicographical",
        );
        let instance = corpus_instance("katsura-4", P31);
        match parse_basis(&elimination, &instance, "") {
            Err(RunFailure::SelfInconsistent { detail }) => {
                assert!(detail.contains("monomial order"), "got {:?}", detail)
            }
            other => panic!("expected self-inconsistent, got {:?}", other),
        }
    }

    /// A declared basis length that disagrees with the list is self-inconsistent.
    #[test]
    fn test_a_declared_length_that_disagrees_with_the_list_is_rejected() {
        let lying = KATSURA_4_BASIS.replace("7 elements", "9 elements");
        let instance = corpus_instance("katsura-4", P31);
        match parse_basis(&lying, &instance, "") {
            Err(RunFailure::SelfInconsistent { detail }) => {
                assert!(detail.contains("declares 9"), "got {:?}", detail)
            }
            other => panic!("expected self-inconsistent, got {:?}", other),
        }
    }

    /// A verbose `size of basis` that disagrees with the output file is self-inconsistent.
    ///
    /// msolve's two independent routes to the same number: the printer walks the basis, while
    /// `size of basis` comes from `get_final_statistics`. A disagreement is the tool contradicting
    /// itself and nothing may be concluded from the run.
    #[test]
    fn test_a_verbose_basis_size_that_disagrees_is_self_inconsistent() {
        let lying = KATSURA_4_LOG.replace("size of basis                     7", "size of basis 9");
        let instance = corpus_instance("katsura-4", P31);
        match parse_basis(KATSURA_4_BASIS, &instance, &lying) {
            Err(RunFailure::SelfInconsistent { detail }) => {
                assert!(detail.contains("verbose log"), "got {:?}", detail)
            }
            other => panic!("expected self-inconsistent, got {:?}", other),
        }
    }

    /// A basis list without its closing `]:` is a truncated write, not a short basis.
    #[test]
    fn test_a_truncated_basis_list_is_a_missing_marker() {
        // Drop the final element, and with it the closing `]:` — exactly what a process killed
        // mid-write leaves behind.
        let truncated = KATSURA_4_BASIS
            .rsplit_once(",\n")
            .map(|(head, _)| head.to_string())
            .expect("the fixture has more than one element");
        assert!(!truncated.contains("]:"));
        assert!(matches!(
            parse_list(&truncated),
            Err(RunFailure::MissingMarker { .. })
        ));
    }

    /// The singular `1 element` header parses, because msolve writes it without the trailing
    /// clause (`iofiles.c:216-220`).
    #[test]
    fn test_a_one_element_basis_header_parses() {
        let single = "\
#Reduced Groebner basis data
#---
#field characteristic: 1073741827
#variable order:       x1, x2
#monomial order:       graded reverse lexicographical
#length of basis:      1 element
#---
[1]:
";
        let answer = parse_basis(single, &pair(P30), "").expect("a one-element basis parses");
        assert_eq!(answer.invariants.basis_cardinality, Some(1));
        assert_eq!(
            answer.invariants.leading_monomials,
            Some(vec!["1".to_string()])
        );
    }

    // ---------------------------------------------------------------------------------------
    // The parametrization, and the silent failure
    // ---------------------------------------------------------------------------------------

    /// `[-1]:` is recognised as an empty variety rather than parsed as a basis.
    #[test]
    fn test_the_no_solution_output_is_recognised() {
        assert_eq!(
            parse_parametrization(NO_SOLUTION),
            Ok(Parametrization::NoSolution)
        );
    }

    /// `[1, nvars, -1, []]:` is recognised as positive-dimensional.
    #[test]
    fn test_the_positive_dimensional_output_is_recognised() {
        assert_eq!(
            parse_parametrization(POSITIVE_DIMENSIONAL),
            Ok(Parametrization::PositiveDimensional)
        );
    }

    /// cyclic-4's eliminant request fails with the reason, because the ideal is not
    /// zero-dimensional — recorded rather than assumed from Zeebra's classification.
    #[test]
    fn test_cyclic_4_has_no_eliminant_and_says_why() {
        let instance = corpus_instance("cyclic-4", P30);
        // The corpus agrees it is not zero-dimensional, which is why the rung is there.
        assert!(corpus::ladder()
            .iter()
            .any(|e| e.name == "cyclic-4" && !e.zero_dimensional));
        let parsed = parse_parametrization(POSITIVE_DIMENSIONAL).expect("parses");
        match eliminant_answer(parsed, &instance, "") {
            Err(RunFailure::Reported { message }) => {
                assert!(
                    message.contains("not zero-dimensional"),
                    "got {:?}",
                    message
                )
            }
            other => panic!("expected a reported failure, got {:?}", other),
        }
    }

    /// A generic parametrization yields the quotient dimension, the eliminant degree and the
    /// eliminant itself.
    #[test]
    fn test_a_generic_parametrization_yields_the_eliminant() {
        let instance = instance("gen", P30, &["x", "y"], &["x^2-2", "y-x-1"]);
        let parsed = parse_parametrization(GENERIC_PARAMETRIZATION).expect("parses");
        let answer = eliminant_answer(
            parsed,
            &instance,
            THREE_BLOCK_LOG.replace("32", "2").as_str(),
        )
        .expect("a generic parametrization is an answer");
        assert_eq!(answer.invariants.quotient_dimension, Some(2));
        assert_eq!(answer.invariants.eliminant_degree, Some(2));
        // Coefficients ascending in msolve, descending here: y^2 - 2y - 1 over GF(1073741827).
        assert_eq!(
            answer.eliminant.as_deref(),
            Some("y^2+1073741825*y+1073741826")
        );
    }

    /// **The silent failure mode.** An added variable is a failure, never a `Complete` answer.
    ///
    /// msolve exits 0 and writes a well-formed parametrization of an ideal it augmented with a
    /// random linear form in a new variable `A`. The only signal is the output's variable list,
    /// and this asserts the adapter reads it.
    #[test]
    fn test_an_added_variable_is_a_failure_and_never_an_answer() {
        let smoke = instance(
            "smoke",
            P30,
            &["x", "y", "z"],
            &["x^2+y^2+z^2-1", "x*y+y*z+z*x-1", "x*y*z-1"],
        );
        let parsed = parse_parametrization(ADDED_VARIABLE_PARAMETRIZATION).expect("parses");
        // The parse itself succeeds — the output really is well-formed, which is the hazard.
        match &parsed {
            Parametrization::Zero { variables, .. } => {
                assert_eq!(variables, &["x", "y", "z", "A"])
            }
            other => panic!("expected a parametrization, got {:?}", other),
        }
        match eliminant_answer(parsed, &smoke, "") {
            Err(RunFailure::SelfInconsistent { detail }) => {
                assert!(detail.contains("added the variable"), "got {:?}", detail);
                assert!(detail.contains('A'), "got {:?}", detail);
                assert!(detail.contains("-c 0"), "got {:?}", detail);
            }
            other => panic!("an added variable must not be an answer, got {:?}", other),
        }
    }

    /// A permutation alone — msolve's first genericity remedy — is also a failure.
    #[test]
    fn test_a_permuted_parametrization_is_a_failure() {
        let smoke = instance("gen", P30, &["x", "y"], &["x^2-2", "y-x-1"]);
        let permuted = GENERIC_PARAMETRIZATION.replace("['x', 'y']", "['y', 'x']");
        let parsed = parse_parametrization(&permuted).expect("parses");
        match eliminant_answer(parsed, &smoke, "") {
            Err(RunFailure::SelfInconsistent { detail }) => {
                assert!(detail.contains("permuted"), "got {:?}", detail)
            }
            other => panic!("expected a permutation failure, got {:?}", other),
        }
    }

    /// A linear form that is not the last variable alone is rejected: the eliminant would be the
    /// minimal polynomial of a combination, not of the requested variable.
    #[test]
    fn test_a_non_identity_linear_form_is_rejected() {
        let instance = instance("gen", P30, &["x", "y"], &["x^2-2", "y-x-1"]);
        let combined = GENERIC_PARAMETRIZATION.replace("[0, 1],", "[3, 1],");
        let parsed = parse_parametrization(&combined).expect("parses");
        match eliminant_answer(parsed, &instance, "") {
            Err(RunFailure::SelfInconsistent { detail }) => {
                assert!(detail.contains("linear form"), "got {:?}", detail)
            }
            other => panic!("expected a linear-form failure, got {:?}", other),
        }
    }

    /// A declared eliminant degree that disagrees with the coefficient count is
    /// self-inconsistent.
    #[test]
    fn test_an_eliminant_degree_that_disagrees_with_its_coefficients_is_rejected() {
        let instance = instance("gen", P30, &["x", "y"], &["x^2-2", "y-x-1"]);
        let lying = GENERIC_PARAMETRIZATION.replace("[[2,", "[[5,");
        let parsed = parse_parametrization(&lying).expect("parses");
        assert!(matches!(
            eliminant_answer(parsed, &instance, ""),
            Err(RunFailure::SelfInconsistent { .. })
        ));
    }

    /// A verbose `degree of ideal` that disagrees with the output file is self-inconsistent.
    #[test]
    fn test_a_verbose_quotient_dimension_that_disagrees_is_rejected() {
        let instance = instance("gen", P30, &["x", "y"], &["x^2-2", "y-x-1"]);
        let parsed = parse_parametrization(GENERIC_PARAMETRIZATION).expect("parses");
        // The log says 32, the output file says 2.
        match eliminant_answer(parsed, &instance, THREE_BLOCK_LOG) {
            Err(RunFailure::SelfInconsistent { detail }) => {
                assert!(detail.contains("degree of ideal"), "got {:?}", detail)
            }
            other => panic!("expected self-inconsistent, got {:?}", other),
        }
    }

    /// An empty output file is a missing marker, not an empty answer.
    #[test]
    fn test_an_empty_parametrization_file_is_a_missing_marker() {
        assert!(matches!(
            parse_parametrization(""),
            Err(RunFailure::MissingMarker { .. })
        ));
        assert!(matches!(
            parse_parametrization("[0, [1073741827,\n2,\n"),
            Err(RunFailure::MissingMarker { .. })
        ));
    }

    /// The eliminant renders descending in the last variable, matching Zeebra's printer.
    #[test]
    fn test_the_eliminant_renders_descending_with_unit_coefficients_implicit() {
        let coefficients = ["5".to_string(), "0".to_string(), "1".to_string()];
        assert_eq!(render_eliminant(&coefficients, "y"), "y^2+5");
        let linear = ["7".to_string(), "1".to_string()];
        assert_eq!(render_eliminant(&linear, "z"), "z+7");
        assert_eq!(render_eliminant(&[], "y"), "0");
    }

    // ---------------------------------------------------------------------------------------
    // Stage timings
    // ---------------------------------------------------------------------------------------

    /// The F4 stage labels are msolve's own, verbatim, and not renamed to Zeebra's spelling.
    ///
    /// The correspondence between msolve's stage names and Zeebra's is the finding; a translation
    /// layer here would hide it.
    #[test]
    fn test_the_f4_stage_labels_are_msolves_own() {
        let stages = parse_stages(KATSURA_4_LOG);
        let names: Vec<&str> = stages.iter().map(|(name, _)| name.as_str()).collect();
        assert_eq!(
            names,
            vec![
                "f4/overall(elapsed)",
                "f4/overall(cpu)",
                "f4/select",
                "f4/symbolic prep.",
                "f4/update",
                "f4/convert",
                "f4/linear algebra",
                "f4/reduce gb",
            ]
        );
        // katsura-4 finishes inside msolve's 10 ms resolution, so every figure really is zero.
        assert!(stages.iter().all(|(_, elapsed)| elapsed.is_zero()));
    }

    /// msolve's three `TIMINGS` writers are told apart, so F4's `overall(elapsed)` and
    /// sparse-FGLM's are not conflated.
    #[test]
    fn test_the_three_timings_blocks_are_distinguished() {
        let stages = parse_stages(THREE_BLOCK_LOG);
        let find = |name: &str| {
            stages
                .iter()
                .find(|(stage, _)| stage == name)
                .map(|(_, elapsed)| *elapsed)
        };
        assert_eq!(
            find("f4/overall(elapsed)"),
            Some(Duration::from_millis(1500))
        );
        assert_eq!(
            find("sparse-fglm/overall(elapsed)"),
            Some(Duration::from_millis(2250))
        );
        assert_eq!(
            find("rational-param/rational param(elapsed)"),
            Some(Duration::from_millis(750))
        );
        assert_eq!(find("f4/linear algebra"), Some(Duration::from_millis(500)));
        assert_eq!(find("f4/convert"), Some(Duration::from_millis(400)));
    }

    /// A repeated stage is suffixed rather than dropped, because a genericity retry is real work.
    #[test]
    fn test_a_repeated_stage_is_suffixed_and_not_dropped() {
        let twice = format!("{}{}", THREE_BLOCK_LOG, THREE_BLOCK_LOG);
        let stages = parse_stages(&twice);
        assert!(stages.iter().any(|(name, _)| name == "f4/select"));
        assert!(stages.iter().any(|(name, _)| name == "f4/select#2"));
    }

    /// The stage list is capped, so a runaway retry loop cannot produce an unusable report.
    #[test]
    fn test_the_stage_list_is_capped() {
        let runaway = THREE_BLOCK_LOG.repeat(40);
        assert_eq!(parse_stages(&runaway).len(), MAX_STAGES);
    }

    /// A `COMPUTATIONAL DATA` integer is read from the column msolve pads it into.
    #[test]
    fn test_a_computational_datum_is_read_from_its_padded_column() {
        assert_eq!(computational_datum(KATSURA_4_LOG, "size of basis"), Some(7));
        assert_eq!(
            computational_datum(THREE_BLOCK_LOG, "deg. elim. pol."),
            Some(32)
        );
        assert_eq!(computational_datum(KATSURA_4_LOG, "no such label"), None);
    }

    // ---------------------------------------------------------------------------------------
    // Capability: `supports`
    // ---------------------------------------------------------------------------------------

    /// A characteristic at or above msolve's own bound is unsupported, naming the bound.
    #[test]
    fn test_a_characteristic_above_msolves_bound_is_unsupported() {
        let solver = solver("msolve", "char");
        let goldilocks = 0xFFFF_FFFF_0000_0001;
        match solver.supports(&pair(goldilocks), Task::ReducedGrobnerBasis) {
            Support::No(Unsupported::Characteristic {
                characteristic,
                supported_below,
            }) => {
                assert_eq!(characteristic, goldilocks);
                assert_eq!(supported_below, MAX_CHARACTERISTIC);
            }
            other => panic!("expected an unsupported characteristic, got {:?}", other),
        }
        // And the top of the supported range is supported.
        assert!(solver
            .supports(&pair(MAX_CHARACTERISTIC - 1), Task::ReducedGrobnerBasis)
            .is_supported());
    }

    /// The eliminant task has a much lower ceiling, and it is declared rather than discovered by
    /// running into msolve's unbounded retry loop.
    ///
    /// `Mersenne31` is above it, so a basis comparison over `GF(2^31 - 1)` is possible and an
    /// eliminant comparison over the same field is not.
    #[test]
    fn test_the_eliminant_ceiling_is_lower_than_the_basis_ceiling() {
        let solver = solver("msolve", "elim-char");
        const { assert!(MAX_CHARACTERISTIC_ELIMINANT < MAX_CHARACTERISTIC) };

        // Mersenne31: fine for a basis, refused for an eliminant.
        assert!(solver
            .supports(&pair(P31), Task::ReducedGrobnerBasis)
            .is_supported());
        match solver.supports(&pair(P31), Task::UnivariateEliminant) {
            Support::No(Unsupported::Characteristic {
                characteristic,
                supported_below,
            }) => {
                assert_eq!(characteristic, P31);
                assert_eq!(supported_below, MAX_CHARACTERISTIC_ELIMINANT);
            }
            other => panic!("expected the eliminant ceiling, got {:?}", other),
        }
        // Just inside it, the eliminant is on offer.
        assert!(solver
            .supports(
                &pair(MAX_CHARACTERISTIC_ELIMINANT - 2),
                Task::UnivariateEliminant
            )
            .is_supported());
    }

    /// An extension field is unsupported: msolve's input format has no syntax for one.
    #[test]
    fn test_an_extension_field_is_unsupported() {
        let solver = solver("msolve", "ext");
        let mut extension = pair(2);
        extension.field = FieldSpec::extension(2, 8, "t^8+t^4+t^3+t+1");
        assert!(matches!(
            solver.supports(&extension, Task::ReducedGrobnerBasis),
            Support::No(Unsupported::ExtensionField {
                extension_degree: 8,
                ..
            })
        ));
    }

    /// Characteristic zero is unsupported: on line 2 of msolve's input file it means Q.
    #[test]
    fn test_characteristic_zero_is_unsupported_because_it_means_the_rationals() {
        let solver = solver("msolve", "qq");
        assert!(matches!(
            solver.supports(&pair(0), Task::ReducedGrobnerBasis),
            Support::No(Unsupported::Representation { .. })
        ));
    }

    /// A basis under lex or grlex is unsupported: `-g` only ever computes grevlex.
    #[test]
    fn test_a_non_grevlex_basis_is_an_unsupported_order() {
        let solver = solver("msolve", "order");
        for order in [
            MonomialOrder::Lexicographic,
            MonomialOrder::GradedLexicographic,
        ] {
            let mut posed = pair(P30);
            posed.order = order;
            match solver.supports(&posed, Task::ReducedGrobnerBasis) {
                Support::No(Unsupported::Order { order: reported }) => {
                    assert_eq!(reported, order)
                }
                other => panic!(
                    "expected an unsupported order for {:?}, got {:?}",
                    order, other
                ),
            }
        }
    }

    /// The tasks msolve has no mode for are refused by name, not approximated.
    ///
    /// `LexBasis` and `LexBasisByConversion`: msolve has no lex order at all — `-e` is a two-block
    /// degrevlex elimination order and the parametrization is not a basis. The two solution tasks:
    /// over `GF(p)` msolve returns a rational parametrization and its root-isolation path is for
    /// rational input, so **operation (c) is not a mode msolve has**. Confirmed independently of
    /// the provisioning survey, which found the same of all four comparands.
    #[test]
    fn test_the_tasks_msolve_has_no_mode_for_are_refused_by_name() {
        let solver = solver("msolve", "tasks");
        for task in [
            Task::LexBasis,
            Task::LexBasisByConversion,
            Task::OneFiniteFieldSolution,
            Task::AllFiniteFieldSolutions,
            Task::CryptanalyticWitness,
        ] {
            match solver.supports(&pair(P30), task) {
                Support::No(Unsupported::Task { task: reported }) => assert_eq!(reported, task),
                other => panic!("expected {} to be refused, got {:?}", task, other),
            }
        }
        // And the two it does serve are on offer.
        for task in [Task::ReducedGrobnerBasis, Task::UnivariateEliminant] {
            assert!(
                solver.supports(&pair(P30), task).is_supported(),
                "{} should be supported",
                task
            );
        }
    }

    /// A generator carrying one of msolve's delimiters is refused rather than silently split.
    #[test]
    fn test_a_generator_carrying_a_delimiter_is_unrepresentable() {
        let solver = solver("msolve", "delim");
        for bad in ["x1^2+x2,x2", "x1^2\n+x2"] {
            let broken = instance("broken", P30, &["x1", "x2"], &[bad]);
            assert!(
                matches!(
                    solver.supports(&broken, Task::ReducedGrobnerBasis),
                    Support::No(Unsupported::Representation { .. })
                ),
                "{:?} must be refused",
                bad
            );
        }
    }

    /// An instance with no variables or no generators is unrepresentable.
    #[test]
    fn test_an_empty_instance_is_unrepresentable() {
        let solver = solver("msolve", "empty");
        let no_variables = instance("empty", P30, &[], &["1"]);
        let no_generators = instance("empty", P30, &["x"], &[]);
        for bad in [no_variables, no_generators] {
            assert!(matches!(
                solver.supports(&bad, Task::ReducedGrobnerBasis),
                Support::No(Unsupported::Representation { .. })
            ));
        }
    }

    // ---------------------------------------------------------------------------------------
    // The absent-tool path, which CI must be able to exercise
    // ---------------------------------------------------------------------------------------

    /// An absent msolve is reported as unavailable from a run under a budget nothing could meet,
    /// and without writing a scratch file.
    ///
    /// Needs no msolve installed, which is the point: CI must exercise this and must never depend
    /// on the binary's presence.
    #[test]
    fn test_an_absent_binary_is_reported_and_not_a_failed_solve() {
        let mut solver = solver("zeebra-no-such-msolve", "absent");
        // `Duration::ZERO`, because the assertion is about *which* failure is reported and must not
        // depend on a wall budget the spawn-and-fail path could lose a race with under suite load
        // (#391). A clock-coupled verdict fails this every time instead of once in a while.
        let report = solver.run(
            &pair(P30),
            Task::ReducedGrobnerBasis,
            &Limits::wall(Duration::ZERO),
        );
        match &report.status {
            RunStatus::Failed(RunFailure::Unavailable { binary, .. }) => {
                assert_eq!(binary, "zeebra-no-such-msolve")
            }
            other => panic!("expected Unavailable, got {:?}", other),
        }
        assert!(report.was_skipped(), "an absent tool is a skipped row");
        assert!(!report.status.is_timing_evidence());
        assert!(report.measurement.is_unmeasured());
        assert_eq!(report.instance, "pair");
        // The command line is still recorded, so the row says what was attempted.
        assert!(report
            .command_line
            .as_deref()
            .is_some_and(|line| line.contains("zeebra-no-such-msolve")));
        // Nothing was written, so nothing about the filesystem can decide this row either.
        let root = scratch_root("absent");
        let written = std::fs::read_dir(&root).map_or(0, |dir| dir.count());
        assert_eq!(written, 0, "{} holds {} file(s)", root.display(), written);
    }

    /// A failure of the harness's **own** scratch work is a skipped row, not a failed msolve.
    ///
    /// Driven for real rather than asserted on a constructed report: the binary is present, so the
    /// absent-tool short cut does not fire, and the scratch root is named under an existing *file*
    /// so `create_dir_all` cannot succeed. Needs no msolve (#610).
    #[test]
    fn test_a_failed_scratch_write_is_a_skipped_row_and_not_a_failed_solve() {
        let blocker = scratch_root("harness-io-blocker");
        if let Some(parent) = blocker.parent() {
            std::fs::create_dir_all(parent).expect("a writable temp dir");
        }
        std::fs::write(&blocker, b"not a directory").expect("the blocking file");
        // `/bin/true` exists and is executable, so absence is not what this row reports.
        let mut solver = MsolveSolver::new("/bin/true", blocker.join("work"));
        let report = solver.run(
            &pair(P30),
            Task::ReducedGrobnerBasis,
            &Limits::wall(Duration::from_secs(30)),
        );
        let _ = std::fs::remove_file(&blocker);

        match &report.status {
            RunStatus::Failed(RunFailure::Harness { detail }) => {
                assert!(detail.contains("work"), "{}", detail)
            }
            other => panic!("expected Harness, got {:?}", other),
        }
        assert!(
            report.was_skipped(),
            "the harness's own filesystem failed, so msolve was never attempted"
        );
        assert!(!report.status.is_timing_evidence());
        assert!(report.measurement.is_unmeasured());
    }

    /// msolve's own `Cannot open output file` is the **tool's** I/O, so the row is attempted.
    ///
    /// The other half of #610's split, read off the log the way every other msolve failure is.
    #[test]
    fn test_msolves_own_output_file_error_is_the_tools_io_and_not_skipped() {
        let failure = failure_from_log("Cannot open output file\n", Some(1));
        match &failure {
            RunFailure::Io { reason } => assert!(reason.contains("output file"), "{}", reason),
            other => panic!("expected Io, got {:?}", other),
        }
        let report = RunReport::new(
            "msolve",
            &pair(P30),
            Task::ReducedGrobnerBasis,
            &Limits::wall(Duration::from_secs(30)),
            RunStatus::Failed(failure),
            Measurement::unmeasured(),
        );
        assert!(
            !report.was_skipped(),
            "msolve ran and reported a failure of its own I/O"
        );
    }

    /// An absent msolve fails the version probe the same way.
    #[test]
    fn test_an_absent_binary_fails_the_version_probe_the_same_way() {
        let mut solver = solver("zeebra-no-such-msolve", "absent-probe");
        match solver.probe_version() {
            Err(RunFailure::Unavailable { binary, .. }) => {
                assert_eq!(binary, "zeebra-no-such-msolve")
            }
            other => panic!("expected Unavailable, got {:?}", other),
        }
    }

    /// An unsupported instance yields an unsupported run with no measurement, without spawning
    /// anything.
    #[test]
    fn test_an_unsupported_instance_is_not_a_timing() {
        let mut solver = solver("zeebra-no-such-msolve", "unsupported");
        let report = solver.run(
            &pair(0xFFFF_FFFF_0000_0001),
            Task::ReducedGrobnerBasis,
            &Limits::wall(Duration::from_secs(5)),
        );
        assert!(matches!(report.status, RunStatus::Unsupported(_)));
        assert!(!report.status.is_timing_evidence());
        assert!(report.measurement.is_unmeasured());
        // Nothing was run, so there is no command to reproduce.
        assert!(report.command_line.is_none());
    }

    /// msolve's own error lines are mapped to failures, and an unrecognised non-zero exit is kept
    /// as one.
    #[test]
    fn test_msolves_error_lines_are_recognised() {
        assert!(matches!(
            failure_from_log("Warning: characteristic must be 0 or < 2^31\n", Some(1)),
            RunFailure::Reported { .. }
        ));
        assert!(matches!(
            failure_from_log("\n=====> Computation failed <=====\n", Some(1)),
            RunFailure::Reported { .. }
        ));
        match failure_from_log("something nobody has seen before", Some(7)) {
            RunFailure::NonZeroExit { code } => assert_eq!(code, Some(7)),
            other => panic!("expected a non-zero exit, got {:?}", other),
        }
        // A signal death carries no code and must not be reported as an exit status.
        match failure_from_log("", None) {
            RunFailure::NonZeroExit { code } => assert_eq!(code, None),
            other => panic!("expected a signal death, got {:?}", other),
        }
    }

    /// The run's flags are the ones the comparison depends on: `-v 1`, `-t` from the declared
    /// worker count, and `-g 2` for a basis.
    ///
    /// Checked through the recorded command line of a run against an absent binary, so no msolve
    /// is needed. `-t` matters because msolve's default is **1** thread: an unflagged msolve would
    /// be measured single-threaded against a parallel Zeebra.
    #[test]
    fn test_the_invocation_sets_verbosity_threads_and_the_basis_mode() {
        let mut solver = solver("zeebra-no-such-msolve", "flags");
        let limits = Limits::wall(Duration::from_secs(5)).with_workers(8);
        let basis = solver.run(&pair(P30), Task::ReducedGrobnerBasis, &limits);
        let line = basis.command_line.expect("a recorded command line");
        assert!(line.contains("-v 1"), "{}", line);
        assert!(line.contains("-t 8"), "{}", line);
        assert!(line.contains("-g 2"), "{}", line);

        // The eliminant uses the default mode, so it must *not* pass `-g`. Asserted over the
        // command line's **tokens**: the recorded line embeds the temporary input and output paths,
        // and a substring test for `-g` matches any checkout directory that happens to contain one
        // — which made this assertion a fact about where the repository was cloned.
        let eliminant = solver.run(&pair(P30), Task::UnivariateEliminant, &limits);
        let line = eliminant.command_line.expect("a recorded command line");
        assert!(
            !line.split_whitespace().any(|token| token == "-g"),
            "{}",
            line
        );
        assert!(line.contains("-t 8"), "{}", line);
    }

    /// The invocation is the solver itself, never a shell or a `timeout`/`taskset` wrapper.
    ///
    /// The contract's rule 2: the direct child has to be msolve, or the peak-RSS figure is a
    /// wrapper's.
    #[test]
    fn test_the_child_is_msolve_and_not_a_wrapper() {
        let mut solver = solver("zeebra-no-such-msolve", "wrapper");
        let report = solver.run(
            &pair(P30),
            Task::ReducedGrobnerBasis,
            &Limits::wall(Duration::from_secs(5)),
        );
        let line = report.command_line.expect("a recorded command line");
        assert!(line.starts_with("zeebra-no-such-msolve"), "{}", line);
        for wrapper in ["sh ", "timeout", "taskset", "/bin/sh"] {
            assert!(
                !line.contains(wrapper),
                "{} must not appear in {}",
                wrapper,
                line
            );
        }
    }

    // ---------------------------------------------------------------------------------------
    // The prefix collision, and the undeclared-variable drop
    // ---------------------------------------------------------------------------------------

    /// `x1` and `x10` are distinct identifiers, so a fourteen-variable instance is representable.
    ///
    /// The hazard this guards: a greedy tokenizer reads `x1*x10` as `x1*x1*0`. msolve is immune by
    /// construction — `store_exponent` (`iofiles.c:26-73`) splits each term on `*` and matches
    /// factor names with a full `strcmp` — and this adapter's own identifier check has to be
    /// whole-token for the same reason, or it would reject what msolve accepts.
    #[test]
    fn test_a_variable_that_is_a_prefix_of_another_is_not_confused() {
        let names: Vec<String> = (1..=14).map(|i| format!("x{}", i)).collect();
        assert_eq!(unknown_identifier("x1*x10+x10*x14-x1^2", &names), None);
        assert_eq!(unknown_identifier("x1*x10", &names), None);
        // And a genuinely absent name is still caught even though `x1` is present.
        assert_eq!(unknown_identifier("x1*x15", &names).as_deref(), Some("x15"));

        let solver = solver("msolve", "prefix");
        let wide = instance(
            "wide",
            P30,
            &names.iter().map(String::as_str).collect::<Vec<_>>(),
            &["x1*x10-1", "x2*x11+x10*x14"],
        );
        assert!(solver
            .supports(&wide, Task::ReducedGrobnerBasis)
            .is_supported());
        // Line 1 carries all fourteen in order, and `x1` is not `x10`.
        let first = input_file(&wide).lines().next().unwrap().to_string();
        assert_eq!(first, "x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14");
    }

    /// A coefficient is never mistaken for an identifier.
    #[test]
    fn test_digits_are_not_identifiers() {
        let names = vec!["x".to_string(), "y".to_string()];
        assert_eq!(unknown_identifier("1073741826*x^2+12*y+7", &names), None);
        assert_eq!(unknown_identifier("-x+2*y-1", &names), None);
    }

    /// A generator naming a variable that is not declared is unsupported, not run.
    ///
    /// **The third silent failure mode.** `store_exponent`'s matching loop (`iofiles.c:57-62`) has
    /// no `else`, so a factor matching no declared name is dropped and msolve computes a basis of a
    /// different ideal, exits 0, and reports `#invalid equations 0`. Measured: `x*z-1` with only
    /// `x,y` declared yields the leading ideal `{x, y^2}` instead of `{x*z, y^2}`.
    #[test]
    fn test_a_generator_naming_an_undeclared_variable_is_unsupported() {
        let solver = solver("msolve", "undeclared");
        let dropped = instance("dropped", P30, &["x", "y"], &["x*z-1", "y^2-1"]);
        match solver.supports(&dropped, Task::ReducedGrobnerBasis) {
            Support::No(Unsupported::Representation { detail }) => {
                assert!(detail.contains("\"z\""), "got {:?}", detail);
                assert!(detail.contains("silently"), "got {:?}", detail);
            }
            other => panic!("an undeclared variable must be refused, got {:?}", other),
        }
    }

    /// A repeated variable name is unsupported.
    #[test]
    fn test_a_repeated_variable_name_is_unsupported() {
        let solver = solver("msolve", "dup");
        let repeated = instance("dup", P30, &["x", "y", "x"], &["x+y"]);
        assert!(matches!(
            solver.supports(&repeated, Task::ReducedGrobnerBasis),
            Support::No(Unsupported::Representation { .. })
        ));
    }

    /// msolve's own `#invalid equations` echo is checked, so a discarded generator is a failure.
    #[test]
    fn test_a_discarded_generator_is_self_inconsistent() {
        let instance = corpus_instance("katsura-4", P31);
        let discarded = KATSURA_4_LOG.replace(
            "size of basis                     7",
            "#invalid equations               1\nsize of basis                     7",
        );
        match parse_basis(KATSURA_4_BASIS, &instance, &discarded) {
            Err(RunFailure::SelfInconsistent { detail }) => {
                assert!(detail.contains("invalid equations"), "got {:?}", detail)
            }
            other => panic!("expected self-inconsistent, got {:?}", other),
        }
    }

    // ---------------------------------------------------------------------------------------
    // Live, and skipped wherever msolve is not installed
    // ---------------------------------------------------------------------------------------

    /// Against a real msolve, the version probe reports a version.
    #[test]
    fn test_a_real_msolve_reports_its_version() {
        let Some(binary) = installed_binary() else {
            return;
        };
        let mut solver =
            MsolveSolver::new(&binary, std::env::temp_dir().join("zeebra-msolve-live-v"));
        let version = solver.probe_version().expect("msolve -V");
        assert_eq!(version.tool, "msolve");
        assert!(
            version.version.starts_with(char::is_numeric),
            "got {:?}",
            version.version
        );
    }

    /// Against a real msolve, the katsura and cyclic rungs agree with Zeebra's own F4.
    ///
    /// The end-to-end correctness check, through `ExternalSolver::run` rather than through a
    /// recorded fixture. Skipped where msolve is absent, so CI never needs it; the recorded
    /// fixtures above cover the same ground there.
    #[test]
    fn test_a_real_msolve_agrees_with_zeebra_on_katsura_and_cyclic() {
        let Some(binary) = installed_binary() else {
            return;
        };
        let mut solver = MsolveSolver::new(
            &binary,
            std::env::temp_dir().join(format!("zeebra-msolve-live-{}", std::process::id())),
        );
        let limits = Limits::wall(Duration::from_secs(60));

        // Every rung on the corpus ladder, so a rung added there is covered here without an edit.
        // A rung with no compiled Zeebra side is skipped, and the skipped set is asserted below
        // rather than left implicit: a loop that silently covers less than it appears to is the
        // failure this milestone keeps finding.
        //
        // Three outcomes per rung, not two, because "no oracle" has two causes that must not be
        // conflated. `skipped` is the structural one — another field — and is asserted against an
        // explicit constant. `over_budget` is Zeebra's own F4 running out of time, which varies
        // with the machine and so cannot be asserted, and is therefore **printed**: a rung that
        // quietly loses its oracle is the recurring defect of this milestone, and making it say so
        // is the fix.
        let mut skipped: Vec<&str> = Vec::new();
        let mut over_budget: Vec<&str> = Vec::new();
        for entry in corpus::ladder() {
            let instance = corpus_instance(entry.name, P31);
            // Checked for every rung, including the ones with no oracle: a row is only the problem
            // the corpus pinned if its digest is the frozen one.
            assert_eq!(
                Some(instance.digest().as_str()),
                entry.digest_at(instance.field.characteristic),
                "{}: the corpus digest must be frozen",
                entry.name
            );
            if !has_compiled_pair(&instance) {
                skipped.push(entry.name);
                continue;
            }
            if instance.variables.len() > oracle_width_ceiling() {
                eprintln!(
                    "{}: NO ORACLE — {} variables is above the default ceiling of {}; \
                     set ZEEBRA_FULL_CORPUS_ORACLE=1 to include it",
                    entry.name,
                    instance.variables.len(),
                    DEFAULT_ORACLE_WIDTH_CEILING
                );
                over_budget.push(entry.name);
                continue;
            }
            let Some(ours) = zeebra_oracle(&instance) else {
                eprintln!(
                    "{}: NO ORACLE — Zeebra's own F4 crossed its {:?} budget, so msolve's answer \
                     for this rung is unchecked",
                    entry.name, ZEEBRA_ORACLE_BUDGET
                );
                over_budget.push(entry.name);
                continue;
            };
            let report = solver.run(&instance, Task::ReducedGrobnerBasis, &limits);
            let answer = match &report.status {
                RunStatus::Complete(answer) => answer,
                other => panic!("{} did not complete: {:?}", instance.name, other),
            };
            assert!(
                ours.overlap(&answer.invariants) >= 2,
                "{}: nothing shared is not agreement",
                instance.name
            );
            assert_eq!(
                ours.agree(&answer.invariants),
                vec![],
                "{} disagreed between msolve and Zeebra",
                instance.name
            );
            // The run is timing evidence and carries msolve's own stage breakdown.
            assert!(report.status.is_timing_evidence());
            assert!(
                report
                    .measurement
                    .stages
                    .iter()
                    .any(|(name, _)| name == "f4/linear algebra"),
                "{}: msolve's stage breakdown should be captured",
                instance.name
            );
        }

        skipped.sort_unstable();
        let mut expected = WITHOUT_A_COMPILED_PAIR.to_vec();
        expected.sort_unstable();
        assert_eq!(
            skipped, expected,
            "a corpus rung gained or lost a compiled Zeebra side; see #333"
        );
        // Printed and not asserted: the width ceiling is liftable and a budget crossing depends on
        // the machine, so pinning either would make the test fail for being run somewhere slower
        // or configured differently. Saying how many rungs went unchecked is what stops the loop
        // from appearing to cover more than it did — which is the recurring defect this issue is
        // about.
        if !over_budget.is_empty() {
            eprintln!(
                "{} of {} rungs had msolve's answer left unchecked: {:?}",
                over_budget.len(),
                corpus::ladder().len(),
                over_budget
            );
        }
    }

    /// Against a real msolve, a fourteen-variable monomial ideal round-trips as a **set**.
    ///
    /// The direct test of the `x1`/`x10` prefix collision, and the reason it is a set equality
    /// rather than a basis comparison: a set of *distinct degree-2 monomials* is pairwise
    /// non-dividing, so the reduced Gröbner basis of the monomial ideal they generate **is that
    /// set**. Any tokenizer error changes the set, and nothing else can. Every single-digit index
    /// is paired with every double-digit one, in both orders of appearance.
    ///
    /// Cross-engine agreement cannot catch this class of bug — every engine is handed the same
    /// bytes, so a prefix collision makes all of them agree on the wrong ideal — which is why the
    /// check has to be against the input rather than against another tool.
    #[test]
    fn test_a_real_msolve_round_trips_fourteen_variables_as_a_set() {
        let Some(binary) = installed_binary() else {
            return;
        };
        let names: Vec<String> = (1..=14).map(|i| format!("x{}", i)).collect();
        let render = |a: usize, b: usize| {
            if a == b {
                format!("x{}^2", a)
            } else {
                let (lo, hi) = (a.min(b), a.max(b));
                format!("x{}*x{}", lo, hi)
            }
        };
        let mut monomials: Vec<String> = Vec::new();
        for i in 1..=9 {
            for j in 10..=14 {
                monomials.push(render(i, j));
                monomials.push(render(j, i));
            }
        }
        for (a, b) in [
            (10, 11),
            (11, 14),
            (12, 13),
            (1, 2),
            (9, 9),
            (10, 10),
            (14, 14),
            (1, 1),
        ] {
            monomials.push(render(a, b));
        }
        monomials.sort();
        monomials.dedup();

        let wide = Instance::new(
            "prefix-14",
            "test",
            FieldSpec::prime(P30),
            names,
            monomials.clone(),
            GREVLEX,
        );
        let mut solver = MsolveSolver::new(
            &binary,
            std::env::temp_dir().join(format!("zeebra-msolve-live-p-{}", std::process::id())),
        );
        let report = solver.run(
            &wide,
            Task::ReducedGrobnerBasis,
            &Limits::wall(Duration::from_secs(60)),
        );
        let answer = match &report.status {
            RunStatus::Complete(answer) => answer,
            other => panic!(
                "the fourteen-variable instance did not complete: {:?}",
                other
            ),
        };
        // The leading monomials msolve reports must be exactly the generators it was given.
        assert_eq!(
            answer.invariants.leading_monomials.as_ref(),
            Some(&monomials),
            "msolve did not round-trip the generators of a monomial ideal"
        );
    }

    /// Against a real msolve, cyclic-4's eliminant is refused as positive-dimensional and
    /// katsura's is produced with the quotient dimension Zeebra's FGLM also reports.
    #[test]
    fn test_a_real_msolve_handles_the_eliminant_task() {
        let Some(binary) = installed_binary() else {
            return;
        };
        let mut solver = MsolveSolver::new(
            &binary,
            std::env::temp_dir().join(format!("zeebra-msolve-live-e-{}", std::process::id())),
        );
        let limits = Limits::wall(Duration::from_secs(60));

        // `P30`, not the corpus's reference field: `P31` is above
        // `MAX_CHARACTERISTIC_ELIMINANT`, so an eliminant row over it is `Unsupported` by design.
        let katsura_5 = corpus_instance("katsura-5", P30);
        match &solver
            .run(&katsura_5, Task::UnivariateEliminant, &limits)
            .status
        {
            RunStatus::Complete(answer) => {
                assert_eq!(answer.invariants.quotient_dimension, Some(16));
                assert_eq!(answer.invariants.eliminant_degree, Some(16));
                // The eliminant is in the last variable of the corpus's order.
                assert!(answer
                    .eliminant
                    .as_deref()
                    .is_some_and(|e| e.contains("x5")));
            }
            other => panic!("katsura-5's eliminant did not complete: {:?}", other),
        }

        let cyclic_4 = corpus_instance("cyclic-4", P30);
        match &solver
            .run(&cyclic_4, Task::UnivariateEliminant, &limits)
            .status
        {
            RunStatus::Failed(RunFailure::Reported { message }) => {
                assert!(
                    message.contains("not zero-dimensional"),
                    "got {:?}",
                    message
                )
            }
            other => panic!("cyclic-4 has no eliminant; got {:?}", other),
        }
    }

    /// msolve and Zeebra return the **same eliminant** on katsura-5, polynomial not text.
    ///
    /// The corroboration gain #465 unlocked. Until Zeebra served the task, the eliminant was the
    /// only one the board defines with two external engines and no in-crate operand — the
    /// invariant could not be checked against Zeebra at all. Both renderers were already made to
    /// agree (`render_eliminant` matches Zeebra's printer), but a text comparison would pass on a
    /// coincidence of formatting and fail on a harmless one, so this parses both sides back into
    /// polynomials over the same field and compares those.
    ///
    /// `P30`, not the corpus reference prime: `P31` is above `MAX_CHARACTERISTIC_ELIMINANT`, so
    /// msolve is `Unsupported` there by design.
    #[test]
    fn test_a_real_msolve_and_zeebra_return_the_same_eliminant() {
        use crate::fields::PrimeFieldElement64;
        use crate::grobner::external::zeebra::ZeebraSolver;
        use crate::MultivariatePolynomial;

        let Some(binary) = installed_binary() else {
            return;
        };
        let katsura_5 = corpus_instance("katsura-5", P30);
        let limits = Limits::wall(Duration::from_secs(60));

        let mut msolve = MsolveSolver::new(
            &binary,
            std::env::temp_dir().join(format!("zeebra-msolve-live-agree-{}", std::process::id())),
        );
        let theirs = match msolve
            .run(&katsura_5, Task::UnivariateEliminant, &limits)
            .status
        {
            RunStatus::Complete(answer) => answer,
            other => panic!("msolve's eliminant did not complete: {:?}", other),
        };

        let mut zeebra = ZeebraSolver::new();
        let ours = match zeebra
            .run(&katsura_5, Task::UnivariateEliminant, &limits)
            .status
        {
            RunStatus::Complete(answer) => answer,
            other => panic!("zeebra's eliminant did not complete: {:?}", other),
        };

        // The invariant first, which is what a board row compares.
        assert_eq!(ours.invariants.eliminant_degree, Some(16));
        assert_eq!(
            ours.invariants.eliminant_degree,
            theirs.invariants.eliminant_degree
        );

        // Then the polynomial. Parsed rather than string-compared: equality has to be on the
        // object, since both sides are rendered by printers that could agree or differ for
        // reasons that have nothing to do with the mathematics.
        type F = PrimeFieldElement64<P30>;
        let names: Vec<&str> = katsura_5.variables.iter().map(String::as_str).collect();
        let mut compiled = [""; 5];
        compiled.copy_from_slice(&names[..5]);
        let parse = |text: &str, who: &str| {
            MultivariatePolynomial::<5, F>::parse(text, compiled)
                .unwrap_or_else(|e| panic!("{}'s eliminant does not parse: {} ({})", who, text, e))
        };
        assert_eq!(
            parse(ours.eliminant.as_deref().expect("ours"), "zeebra"),
            parse(theirs.eliminant.as_deref().expect("theirs"), "msolve"),
        );
    }

    /// Against a real msolve, the smoke system's eliminant request hits the silent failure and is
    /// reported rather than completed.
    ///
    /// The live counterpart of `test_an_added_variable_is_a_failure_and_never_an_answer`: msolve
    /// really does exit 0 here with a well-formed answer about a different ideal.
    #[test]
    fn test_a_real_msolve_does_not_pass_off_an_augmented_ideal() {
        let Some(binary) = installed_binary() else {
            return;
        };
        let mut solver = MsolveSolver::new(
            &binary,
            std::env::temp_dir().join(format!("zeebra-msolve-live-a-{}", std::process::id())),
        );
        let smoke = instance(
            "smoke",
            P30,
            &["x", "y", "z"],
            &[
                "x^2+y^2+z^2+1073741826",
                "x*y+y*z+x*z+1073741826",
                "x*y*z+1073741826",
            ],
        );
        let report = solver.run(
            &smoke,
            Task::UnivariateEliminant,
            &Limits::wall(Duration::from_secs(60)),
        );
        match &report.status {
            RunStatus::Failed(RunFailure::SelfInconsistent { detail }) => {
                assert!(detail.contains('A'), "got {:?}", detail)
            }
            other => panic!(
                "expected the genericity substitution to be caught, got {:?}",
                other
            ),
        }
        assert!(
            !report.status.is_timing_evidence(),
            "a substituted problem must never be a timing"
        );
    }
}
