//! The committed per-run files, checked against the same rules as the history they mirror.
//!
//! `research/scoreboard/results/history.json` is covered by `include_str!`-based unit tests, so a
//! defect in it fails at compile-and-test time. `research/scoreboard/runs/*.json` had **no test at
//! all**, and that is how #550 half-landed: `a09a8e57` gave the four `a3e5d66` records a resolvable
//! stamp in the history and left the four run files — the per-run artifacts `CostRow::from_run`
//! cites as a figure's `source` — still naming a commit nothing can resolve. A reader who followed
//! the citation got the state the history test forbids.
//!
//! An integration test and not a unit test because the directory is walked at run time: a file
//! added to it has to be covered without anyone remembering to list it, which is the property
//! `include_str!` cannot have.

use std::{collections::BTreeMap, fs, path::PathBuf};

use zeebra::grobner::research::Json;

fn runs_directory() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("research/scoreboard/runs")
}

fn history_path() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("research/scoreboard/results/history.json")
}

/// The provenance keys of one `environment` object, as text, with absent read as empty.
///
/// Absent and empty are deliberately conflated: `Environment::stamp_is_resolvable` treats them the
/// same, and a record written before a field existed is indistinguishable from one that wrote it
/// blank — which is the fact about such records rather than something to recover.
fn stamp(environment: &Json) -> (String, String, String) {
    let field = |key: &str| {
        environment
            .get(key)
            .and_then(Json::as_str)
            .unwrap_or_default()
            .to_string()
    };
    (field("commit"), field("base_commit"), field("patch_id"))
}

/// `Environment::stamp_is_resolvable`, restated over the text so the test does not depend on the
/// record parsing against the current registry — a run file whose challenge was later redefined
/// still has to carry a stamp a reader can follow.
fn is_resolvable((commit, base, patch): &(String, String, String)) -> bool {
    !base.is_empty() && (base == commit || !patch.is_empty())
}

fn run_files() -> Vec<(String, Json)> {
    let directory = runs_directory();
    let mut files: Vec<(String, Json)> = fs::read_dir(&directory)
        .unwrap_or_else(|error| panic!("{} is readable: {error}", directory.display()))
        .map(|entry| entry.expect("a directory entry"))
        .filter(|entry| entry.path().extension().is_some_and(|ext| ext == "json"))
        .map(|entry| {
            let name = entry.file_name().to_string_lossy().to_string();
            let text = fs::read_to_string(entry.path())
                .unwrap_or_else(|error| panic!("{name} is readable: {error}"));
            let value = Json::parse(&text).unwrap_or_else(|error| panic!("{name} parses: {error}"));
            (name, value)
        })
        .collect();
    files.sort_by(|a, b| a.0.cmp(&b.0));
    assert!(
        !files.is_empty(),
        "no run files were found in {}, so this test asserts nothing",
        directory.display()
    );
    files
}

/// Every committed run file records a stamp a later reader can resolve.
#[test]
fn test_every_committed_run_file_carries_a_resolvable_stamp() {
    let unresolvable: Vec<String> = run_files()
        .into_iter()
        .filter_map(|(name, value)| {
            let environment = value.get("environment")?;
            let stamp = stamp(environment);
            (!is_resolvable(&stamp)).then(|| format!("{name} (commit {})", stamp.0))
        })
        .collect();
    assert!(
        unresolvable.is_empty(),
        "{} run files record a commit nothing can resolve: {:#?}",
        unresolvable.len(),
        unresolvable
    );
}

/// A run file and the history record it mirrors agree on the provenance stamp.
///
/// The invariant #550 broke in the half that was fixed: repairing one copy and not the other leaves
/// the board internally inconsistent, and the history test — the only one there was — passes on it.
/// Matched on the file stem, which is `RunRecord::run_file_stem`, so a stem shared by two runs is
/// satisfied by agreeing with *either*: that ambiguity is #540's subject and this test must not
/// pretend it is resolved.
#[test]
fn test_a_run_file_and_the_history_agree_on_the_stamp() {
    let text = fs::read_to_string(history_path()).expect("the committed history is readable");
    let history = Json::parse(&text).expect("the committed history parses");
    let runs = history
        .get("runs")
        .and_then(|runs| match runs {
            Json::Array(items) => Some(items),
            _ => None,
        })
        .expect("the history holds a runs array");

    // Stem -> every stamp the history records under it. A Vec because two runs legitimately share
    // a stem (#540), and collapsing them would make the comparison below depend on which came
    // last in the file.
    let mut by_stem: BTreeMap<String, Vec<(String, String, String)>> = BTreeMap::new();
    for run in runs {
        let Some(environment) = run.get("environment") else {
            continue;
        };
        let challenge = run
            .get("challenge")
            .and_then(Json::as_str)
            .expect("every record names its challenge");
        let formulation = run
            .get("formulation")
            .and_then(Json::as_str)
            .expect("every record names its formulation");
        let commit = environment
            .get("commit")
            .and_then(Json::as_str)
            .unwrap_or_default();
        by_stem
            .entry(file_stem(challenge, formulation, commit))
            .or_default()
            .push(stamp(environment));
    }

    let mut disagreements: Vec<String> = Vec::new();
    let mut matched = 0usize;
    for (name, value) in run_files() {
        let Some(environment) = value.get("environment") else {
            continue;
        };
        let stem = name.trim_end_matches(".json");
        let Some(candidates) = by_stem.get(stem) else {
            // A run file with no history entry is #540's other direction and not this test's
            // subject; `test_the_committed_run_files_have_no_collisions` is where that lives.
            continue;
        };
        matched += 1;
        let here = stamp(environment);
        if !candidates.contains(&here) {
            disagreements.push(format!(
                "{name}: file has {here:?}, history has {candidates:?}"
            ));
        }
    }

    assert!(
        matched > 0,
        "no run file matched a history stem, so the stem derivation below is wrong and this test \
         asserts nothing"
    );
    assert!(
        disagreements.is_empty(),
        "{} run files disagree with the history on their stamp: {:#?}",
        disagreements.len(),
        disagreements
    );
}

/// `RunRecord::run_file_stem`'s slugging, restated over the text.
///
/// Duplicated rather than called because the function takes a parsed `RunRecord`, which needs the
/// registry and so would make this test fail for a record whose challenge was redefined — a
/// different defect from the one being checked. Kept in step by
/// `test_a_run_file_and_the_history_agree_on_the_stamp`'s `matched > 0` assertion, which fails
/// loudly if the two ever diverge.
fn file_stem(challenge: &str, formulation: &str, commit: &str) -> String {
    format!(
        "{}--{}--{}",
        challenge,
        formulation.replace(' ', "-"),
        commit
    )
}
