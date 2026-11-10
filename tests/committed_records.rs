//! Checks on the measurement records committed to this repository, rather than on the library.
//!
//! Excluded from the published package along with the records themselves: they are this
//! repository's history, not part of the crate.

use std::{fs, path::Path};

use zeebra::{grobner::external::CompetitiveBoard, util::Json};

/// Every committed competitive row records a stamp a later reader can still resolve.
///
/// #505: three of the four cohorts in `research/competitive/results/history.json` — 315 of 387
/// rows, including every five-library figure M27-A is organized around — record branch commits
/// from PR #435 that did not survive its merge. The letter of #335 was met and its purpose was
/// not: "re-measure at `7adb29e`" is not an instruction anyone can carry out. A merge base is
/// an ancestor of `main` and stays one, so `base_commit` plus the delta's `patch_id` is a stamp
/// that cannot dangle.
#[test]
fn test_every_committed_competitive_row_carries_a_resolvable_stamp() {
    let path =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("research/competitive/results/history.json");
    let text = fs::read_to_string(&path).expect("the committed history is readable");
    let history = Json::parse(&text).expect("committed history.json parses");
    let board = CompetitiveBoard::load(&history).expect("every committed row loads");
    assert!(
        !board.rows().is_empty(),
        "the committed history is not empty"
    );

    let unresolvable: Vec<String> = board
        .rows()
        .iter()
        .filter(|row| !row.environment.stamp_is_resolvable())
        .map(|row| {
            format!(
                "{} at {:?} (base {:?}, patch {:?})",
                row.problem,
                row.environment.commit,
                row.environment.base_commit,
                row.environment.patch_id,
            )
        })
        .collect();
    assert!(
        unresolvable.is_empty(),
        "{} of {} rows record a commit nothing can resolve: {:?}",
        unresolvable.len(),
        board.rows().len(),
        &unresolvable[..unresolvable.len().min(4)]
    );
}
