//! The guide's examples are only tested if `src/lib.rs` names the file they live in, and nothing
//! else notices an omission: a guide added without its `include_str!` line compiles nothing and
//! reports no failure.

use std::fs;
use std::path::Path;

/// Every file under `docs/guide/` is included by `src/lib.rs`, so its Rust examples are compiled.
#[test]
fn test_every_guide_document_is_compiled_as_a_doc_test() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let lib = fs::read_to_string(root.join("src/lib.rs")).expect("src/lib.rs is readable");

    let mut missing: Vec<String> = fs::read_dir(root.join("docs/guide"))
        .expect("docs/guide exists")
        .map(|entry| entry.expect("a readable directory entry").file_name())
        .map(|name| name.to_string_lossy().into_owned())
        .filter(|name| name.ends_with(".md"))
        .filter(|name| !lib.contains(&format!("include_str!(\"../docs/guide/{name}\")")))
        .collect();
    missing.sort();

    assert!(
        missing.is_empty(),
        "docs/guide files not included by src/lib.rs, so their examples are never compiled: {missing:?}"
    );
}

/// Every guide `src/lib.rs` names exists, so a renamed file fails here rather than at link time.
#[test]
fn test_every_included_guide_document_exists() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let lib = fs::read_to_string(root.join("src/lib.rs")).expect("src/lib.rs is readable");

    let mut missing: Vec<&str> = lib
        .split("include_str!(\"../docs/guide/")
        .skip(1)
        .filter_map(|tail| tail.split('"').next())
        .filter(|name| !root.join("docs/guide").join(name).exists())
        .collect();
    missing.sort_unstable();

    assert!(
        missing.is_empty(),
        "src/lib.rs includes guide files that do not exist: {missing:?}"
    );
    assert!(
        lib.contains("include_str!(\"../docs/guide/"),
        "src/lib.rs includes no guide documents at all, so this test asserts nothing"
    );
}
