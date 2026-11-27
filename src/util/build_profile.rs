//! Which cargo profile this artifact was built with, as a string a measurement record can carry.
//!
//! "release" stops naming one build once the release profile changes (#1170), so a figure that
//! says only "release" cannot be told apart from one taken under the old profile. `build.rs`
//! resolves the concrete settings — `lto`, `codegen-units`, `opt-level` — from the manifest and
//! the `CARGO_PROFILE_*` overrides at build time, the same way `isa_floor` reports what the
//! compiler was told rather than what a caller claims (#1172).
//!
//! Describes this repository's own builds. Built as a dependency, the consumer's workspace decides
//! the profile and this crate's manifest does not; the stamp then reads this crate's tables.

#[cfg(test)]
#[path = "build_profile/resolve.rs"]
mod resolve;

/// The concrete build profile, e.g.
/// `profile=release; opt-level=3; lto=fat; codegen-units=1; debug-assertions=false;
/// rustflags=-C target-cpu=x86-64-v3`.
///
/// Measurement records put this in `Environment::build`, so two figures from different profiles
/// carry different stamps and do not compare as equals.
pub fn build_profile() -> &'static str {
    env!("ZEEBRA_BUILD_PROFILE")
}

#[cfg(test)]
mod tests {
    use super::build_profile;
    use super::resolve::{profile_from_out_dir, resolve, stamp, watched_variables};
    use std::path::Path;

    const MANIFEST: &str = r#"
[package]
name = "zeebra"

[profile.release]
lto = "thin"   # the default under test
codegen-units = 16

[profile.release.package.foo]
codegen-units = 99

[profile.release-fat]
inherits = "release"
lto = "fat"
codegen-units = 1

[profile.ci-release]
inherits = "release"
opt-level = 2
lto = "off"
"#;

    fn no_env(_: &str) -> Option<String> {
        None
    }

    fn stamp_of(name: &str, env: &dyn Fn(&str) -> Option<String>) -> String {
        let settings = resolve(MANIFEST, name, env).unwrap();
        stamp(&settings, &settings.opt_level, "-C target-cpu=x86-64-v3")
    }

    /// The acceptance test of #1172: a non-default profile stamps differently from the default.
    #[test]
    fn test_a_non_default_profile_carries_a_different_stamp() {
        let release = stamp_of("release", &no_env);
        let fat = stamp_of("release-fat", &no_env);
        assert_ne!(release, fat);
        assert_eq!(
            release,
            "profile=release; opt-level=3; lto=thin; codegen-units=16; debug-assertions=false; \
             rustflags=-C target-cpu=x86-64-v3"
        );
        assert!(fat.contains("lto=fat; codegen-units=1"), "{fat}");
        // Inherited, not restated: `release-fat` takes `opt-level` from `release`'s built-in.
        assert!(fat.contains("opt-level=3"), "{fat}");
    }

    /// A per-package table is not the profile; reading it would report its `codegen-units=99`.
    #[test]
    fn test_sub_tables_are_not_the_profile() {
        assert!(stamp_of("release", &no_env).contains("codegen-units=16"));
    }

    /// CI overrides `ci-release` through the environment, and the stamp must follow it.
    #[test]
    fn test_environment_overrides_win_and_reach_children() {
        let ci = |name: &str| match name {
            "CARGO_PROFILE_CI_RELEASE_LTO" => Some("thin".to_string()),
            "CARGO_PROFILE_CI_RELEASE_OPT_LEVEL" => Some("3".to_string()),
            _ => None,
        };
        let settings = resolve(MANIFEST, "ci-release", &ci).unwrap();
        assert_eq!(
            (settings.lto.as_str(), settings.opt_level.as_str()),
            ("thin", "3")
        );

        // An override on the parent reaches a child that does not restate the key.
        let parent =
            |name: &str| (name == "CARGO_PROFILE_RELEASE_CODEGEN_UNITS").then(|| "4".to_string());
        assert_eq!(
            resolve(MANIFEST, "ci-release", &parent)
                .unwrap()
                .codegen_units,
            "4"
        );
        assert_eq!(
            resolve(MANIFEST, "release-fat", &parent)
                .unwrap()
                .codegen_units,
            "1"
        );
    }

    /// `true` and `"fat"` are one setting, so they stamp alike; the built-ins fill the rest.
    #[test]
    fn test_defaults_and_spellings() {
        let manifest = "[profile.release]\nlto = true\n";
        let settings = resolve(manifest, "release", &no_env).unwrap();
        assert_eq!(settings.lto, "fat");
        let dev = resolve(manifest, "dev", &no_env).unwrap();
        assert_eq!(
            (
                dev.opt_level.as_str(),
                dev.lto.as_str(),
                dev.debug_assertions.as_str()
            ),
            ("0", "false", "true")
        );
        assert_eq!(resolve(manifest, "bench", &no_env).unwrap().lto, "fat");
        assert!(resolve(manifest, "orphan", &no_env).is_err());
        assert!(resolve(
            "[profile.a]\ninherits = \"b\"\n[profile.b]\ninherits = \"a\"\n",
            "a",
            &no_env
        )
        .is_err());
    }

    /// An override the resolver cannot see shows up as a disagreement with cargo's own opt-level.
    #[test]
    fn test_an_unseen_override_is_reported_not_hidden() {
        let settings = resolve(MANIFEST, "release", &no_env).unwrap();
        assert!(stamp(&settings, "1", "").contains("UNSEEN OVERRIDE"));
        assert!(!stamp(&settings, "3", "").contains("UNSEEN"));
        assert!(stamp(&settings, "3", "").ends_with("rustflags=none"));
    }

    /// A build reruns when any override along the chain changes, parents included.
    #[test]
    fn test_every_override_on_the_chain_is_watched() {
        let watched = watched_variables(MANIFEST, "release-fat", &no_env);
        for variable in [
            "CARGO_PROFILE_RELEASE_FAT_LTO",
            "CARGO_PROFILE_RELEASE_CODEGEN_UNITS",
            "CARGO_PROFILE_RELEASE_OPT_LEVEL",
        ] {
            assert!(
                watched.iter().any(|w| w == variable),
                "{variable} not in {watched:?}"
            );
        }
    }

    #[test]
    fn test_the_profile_is_read_from_out_dir() {
        let at = |path: &str| profile_from_out_dir(Path::new(path));
        assert_eq!(
            at("/t/release-fat/build/zeebra-0123/out").as_deref(),
            Some("release-fat")
        );
        assert_eq!(at("/t/debug/build/zeebra-0123/out").as_deref(), Some("dev"));
        assert_eq!(
            at("/t/x86_64-unknown-linux-gnu/release/build/zeebra-0123/out").as_deref(),
            Some("release")
        );
        // The build-dir layout newer cargo uses: one more level between `build` and `out`.
        assert_eq!(
            at("/t/debug/build/zeebra/0123abcd/out").as_deref(),
            Some("dev")
        );
        assert_eq!(
            at("/t/release-fat/build/zeebra/0123abcd/out").as_deref(),
            Some("release-fat")
        );
    }

    /// The artifact running this test carries a resolved stamp, not a placeholder.
    #[test]
    fn test_this_build_is_stamped() {
        let stamp = build_profile();
        assert!(stamp.starts_with("profile="), "{stamp}");
        assert!(
            stamp.contains("; lto=") && stamp.contains("; codegen-units="),
            "{stamp}"
        );
        assert_eq!(
            stamp.contains("debug-assertions=true"),
            cfg!(debug_assertions),
            "{stamp}"
        );
    }
}
