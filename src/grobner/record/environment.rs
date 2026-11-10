//! Where a measurement came from: the machine, the build, and a commit stamp that stays resolvable.

use crate::util::Json;

/// `git diff <range> | git patch-id --stable`, or empty if either side of the pipe fails.
///
/// Its own function because the pipe is the whole awkwardness: `git patch-id` reads a diff on
/// stdin and there is no `git diff --patch-id`.
fn patch_id(range: &str) -> String {
    use std::io::Write;
    use std::process::{Command, Stdio};

    let diff = match Command::new("git").args(["diff", range]).output() {
        Ok(out) if out.status.success() => out.stdout,
        _ => return String::new(),
    };
    let mut child = match Command::new("git")
        .args(["patch-id", "--stable"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
    {
        Ok(child) => child,
        Err(_) => return String::new(),
    };
    if let Some(stdin) = child.stdin.as_mut() {
        // A broken pipe here is `git patch-id` having exited early, which the wait below reports.
        let _ = stdin.write_all(&diff);
    }
    drop(child.stdin.take());
    match child.wait_with_output() {
        // `<patch-id> <commit-id>`; the first field is the content hash and the one that is stable.
        Ok(out) if out.status.success() => String::from_utf8_lossy(&out.stdout)
            .split_whitespace()
            .next()
            .unwrap_or_default()
            .to_string(),
        _ => String::new(),
    }
}

/// The machine and the build a measurement came from.
///
/// Carried on every run because a runtime comparison across two of these is not a comparison.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Environment {
    /// The commit the binary was built from.
    ///
    /// **Not durable on its own.** A sweep run on a branch records that branch's commit, and a
    /// merge that rewrites history leaves the stamp dangling: reachable from nothing, so
    /// "re-measure at this commit" is an instruction no later reader can carry out (#505, where
    /// 315 of 387 competitive rows were in that state). [`Self::base_commit`] and
    /// [`Self::patch_id`] are the half that survives, and [`Self::stamp_is_resolvable`] is the
    /// check.
    pub commit: String,

    /// The commit the measured branch was cut from: `git merge-base HEAD origin/main`.
    ///
    /// Durable **by construction** — a merge base is an ancestor of `main` and nothing can make it
    /// stop being one — so this is what is still checkout-able after the branch is rebased,
    /// squashed or deleted. Equal to [`Self::commit`] when the measurement was taken on `main`.
    /// Empty in records written before the field existed, and in records whose branch commit was
    /// already gone when the field arrived.
    pub base_commit: String,

    /// `git patch-id --stable` over `base_commit..commit`: the measured delta by its content.
    ///
    /// A patch id hashes the diff, not the history, so it is unchanged by the rebase or squash that
    /// invalidated [`Self::commit`] — which is what lets a reader find the landed equivalent of a
    /// dangling branch commit, or confirm that a tree they reconstructed is the measured one.
    /// Empty when there is no delta to identify (`base_commit == commit`) and empty in records
    /// written before the field existed.
    pub patch_id: String,

    /// A machine label: hostname, or a description.
    pub machine: String,

    /// Logical CPUs, and whatever pinning policy was applied.
    pub cpu: String,

    /// Worker threads the solver was given. **1 for every uncontended figure**, which is what
    /// every record written before concurrency existed is read back as.
    ///
    /// Recorded beside [`Self::cpu`] rather than folded into it because it is the one condition the
    /// comparison path **refuses** on rather than merely caveats: a parallel wall clock and a
    /// single-threaded one are costs of different things, and a ratio between them read as a solver
    /// speedup would be false.
    pub concurrency: usize,

    /// `RUSTFLAGS` and the profile, which decide whether two timings are comparable at all.
    pub build: String,

    /// The resource policy the run was given, in its own words.
    pub policy: String,
}

impl Environment {
    /// The environment as JSON.
    pub fn to_json(&self) -> Json {
        Json::object([
            ("commit", Json::string(&self.commit)),
            ("base_commit", Json::string(&self.base_commit)),
            ("patch_id", Json::string(&self.patch_id)),
            ("machine", Json::string(&self.machine)),
            ("cpu", Json::string(&self.cpu)),
            ("concurrency", Json::size(self.concurrency)),
            ("build", Json::string(&self.build)),
            ("policy", Json::string(&self.policy)),
        ])
    }

    /// The provenance fields read from git; every other field left empty for the caller.
    ///
    /// Three reads, each degrading to **empty rather than to a guess**: the commit, the merge base
    /// against `origin/main` (then `main`, for a checkout with no remote), and the patch id of the
    /// delta between them. A writer that cannot name its base records that it cannot, which
    /// [`Self::stamp_is_resolvable`] reports — the failure #505 is about is a stamp that *looks*
    /// resolvable and is not, so inventing a base here would be worse than leaving it blank.
    ///
    /// `concurrency` comes back `0`, which is not a valid worker count: every caller sets it, and a
    /// reader coerces an absent or zero count to 1.
    pub fn from_git() -> Self {
        let git = |arguments: &[&str]| -> String {
            std::process::Command::new("git")
                .args(arguments)
                .output()
                .ok()
                .filter(|out| out.status.success())
                .and_then(|out| String::from_utf8(out.stdout).ok())
                .map(|text| text.trim().to_string())
                .unwrap_or_default()
        };
        let commit = git(&["rev-parse", "--short", "HEAD"]);
        let base = ["origin/main", "main"]
            .iter()
            .map(|reference| git(&["merge-base", "HEAD", reference]))
            .find(|base| !base.is_empty())
            .unwrap_or_default();
        let base_short = if base.is_empty() {
            String::new()
        } else {
            git(&["rev-parse", "--short", &base])
        };
        // A patch id and not a tree hash, though the tree hash is the cheaper read. A tree object
        // lives only as long as something reaches it, so a tree hash recorded on a branch dies
        // with the branch — the same failure as the commit, one indirection along. A patch id is a
        // *function of the diff*, so a later reader recomputes it over a candidate range on `main`
        // and compares; it needs no object to have survived.
        let delta = if base.is_empty() || base_short == commit {
            String::new()
        } else {
            patch_id(&format!("{}..HEAD", base))
        };
        Self {
            commit,
            base_commit: base_short,
            patch_id: delta,
            machine: String::new(),
            cpu: String::new(),
            concurrency: 0,
            build: String::new(),
            policy: String::new(),
        }
    }

    /// Whether what this figure was measured with can still be reached.
    ///
    /// Two ways to pass, and recording [`Self::commit`] alone is neither: the measurement was taken
    /// at the base itself, so there is nothing to reconstruct; or it records a base — permanently
    /// reachable — **and** the patch id of the delta from it. A branch commit with no base is the
    /// #505 state: a stamp that satisfies #335's letter and resolves to nothing.
    ///
    /// Deliberately **not** part of [`Self::comparable`]: two figures taken at the same commit are
    /// comparable whether or not a later reader can check that commit out. Resolvability is a
    /// reproducibility property, not a comparability one.
    pub fn stamp_is_resolvable(&self) -> bool {
        if self.base_commit.is_empty() {
            return false;
        }
        self.base_commit == self.commit || !self.patch_id.is_empty()
    }

    /// Whether two runs were measured under conditions a runtime may be compared across.
    ///
    /// Concurrency is deliberately **not** here: a mismatch in it is refused by
    /// a run comparison rather than carried as a caveat, so this answers the narrower question
    /// of whether the machine and the build agree.
    pub fn comparable(&self, other: &Self) -> bool {
        self.machine == other.machine && self.cpu == other.cpu && self.build == other.build
    }
}

#[cfg(test)]
mod tests {
    use super::Environment;

    fn environment() -> Environment {
        Environment {
            commit: "deadbeef".to_string(),
            base_commit: "deadbeef".to_string(),
            patch_id: String::new(),
            machine: "workstation".to_string(),
            cpu: "64 logical, taskset 0-7".to_string(),
            concurrency: 1,
            build: "release, target-cpu=x86-64-v3".to_string(),
            policy: "60k columns, 400 MB".to_string(),
        }
    }

    /// A stamp resolves when it names a base, and a bare branch commit does not.
    ///
    /// The three cases #505 turns on. The middle one is the defect: a recorded commit satisfies
    /// #335's letter and resolves to nothing once the branch it names is rewritten away.
    #[test]
    fn test_a_stamp_resolves_only_when_it_names_a_reachable_base() {
        // Taken on `main`: the commit is its own base, and there is no delta to identify.
        let on_main = Environment {
            commit: "663097a".to_string(),
            base_commit: "663097a".to_string(),
            patch_id: String::new(),
            ..environment()
        };
        assert!(on_main.stamp_is_resolvable());

        // The #505 state: a branch commit and nothing else.
        let dangling = Environment {
            commit: "7adb29e".to_string(),
            base_commit: String::new(),
            patch_id: String::new(),
            ..environment()
        };
        assert!(!dangling.stamp_is_resolvable());

        // The same measurement, stamped: the base is an ancestor of `main` and stays one, and the
        // patch id identifies the delta by content rather than by a commit name.
        let stamped = Environment {
            commit: "7adb29e".to_string(),
            base_commit: "7ab1e86".to_string(),
            patch_id: "b2b959eaed689079fb7c88ff3095dbef54a4c756".to_string(),
            ..environment()
        };
        assert!(stamped.stamp_is_resolvable());

        // A base with no patch id, where the two differ, is not enough: the base alone does not say
        // what was measured on top of it.
        let half = Environment {
            patch_id: String::new(),
            ..stamped.clone()
        };
        assert!(!half.stamp_is_resolvable());

        // Resolvability is not comparability: these two differ only in what a reader can check out.
        assert!(dangling.comparable(&stamped));
    }
}
