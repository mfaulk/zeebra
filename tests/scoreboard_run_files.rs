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

use std::{collections::BTreeSet, fs, path::PathBuf};

use zeebra::grobner::research::{registry, Json, RunRecord, Scoreboard};

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

/// Every run file is named by the record it holds, and every retained run has one — #540.
///
/// This replaces a stamp-by-stamp comparison that had to key on
/// `challenge--formulation--commit` and therefore could not distinguish two runs of one problem.
/// It subsumes it: the stem carries a digest over the whole record, so a file whose contents
/// disagree with its history row — #550's half-landing, where the history got a resolvable stamp
/// and the file kept a dangling one — is named inconsistently with both and shows up below as an
/// orphan.
#[test]
fn test_every_run_file_is_named_by_the_record_it_holds() {
    let registry = registry();
    let mut checked = 0usize;
    for (name, value) in run_files() {
        let challenge = value
            .get("challenge")
            .and_then(Json::as_str)
            .expect("every record names its challenge");
        let manifest = registry
            .iter()
            .find(|candidate| candidate.id == challenge)
            .unwrap_or_else(|| panic!("{name} names an unregistered challenge {challenge:?}"));
        let run = RunRecord::from_json(&value, manifest)
            .unwrap_or_else(|error| panic!("{name} does not parse: {error}"));
        assert_eq!(
            name,
            format!("{}.json", run.run_file_stem()),
            "a run file must be named by the record it holds"
        );
        checked += 1;
    }
    assert!(
        checked > 0,
        "no run files were read, so this asserts nothing"
    );
}

/// The run directory is exactly the retained history: no run without a file, no file without a run.
///
/// Before #540 both sets numbered 89 and were **not the same set** — sixteen retained runs shared a
/// stem with another and so had no file of their own, while seven files carried names an earlier
/// slug rule had produced that no current stem matched. A citation that resolves to nothing is the
/// defect `CostRow::from_run`'s `source` exists not to have.
#[test]
fn test_the_run_directory_is_exactly_the_retained_history() {
    let text = fs::read_to_string(history_path()).expect("the committed history is readable");
    let history = Json::parse(&text).expect("the committed history parses");
    let board = Scoreboard::load(&history, &registry()).expect("every retained run is registered");

    let expected: BTreeSet<String> = board
        .runs()
        .iter()
        .map(|run| format!("{}.json", run.run_file_stem()))
        .collect();
    let actual: BTreeSet<String> = run_files().into_iter().map(|(name, _)| name).collect();

    let missing: Vec<&String> = expected.difference(&actual).collect();
    let orphaned: Vec<&String> = actual.difference(&expected).collect();
    assert!(
        missing.is_empty(),
        "{} retained runs have no record file: {:#?}",
        missing.len(),
        missing
    );
    assert!(
        orphaned.is_empty(),
        "{} record files are a record of nothing: {:#?}",
        orphaned.len(),
        orphaned
    );
    assert_eq!(
        actual.len(),
        board.runs().len(),
        "one file per retained run, so every run is addressable"
    );
}
