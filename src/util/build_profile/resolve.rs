// The concrete profile settings a build used, resolved from the manifest by `build.rs`.
//
// Shared by `build.rs` (through `#[path]`) and the library's tests, which is why it uses no crate
// item and carries plain comments: it is compiled into both. Cargo gives a build script `PROFILE`
// (only `debug` or `release`) and `OPT_LEVEL`, and nothing about `lto` or `codegen-units`, so those
// are read from `Cargo.toml` the way cargo itself resolves them: built-in defaults, then the
// manifest's `[profile.*]` table, then `CARGO_PROFILE_<NAME>_<KEY>` from the environment, walking
// `inherits` until a key is set (#1172).

use std::path::Path;

/// One profile's settings, as a measurement record prints them.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Settings {
    pub profile: String,
    pub opt_level: String,
    pub lto: String,
    pub codegen_units: String,
    pub debug_assertions: String,
}

const KEYS: [&str; 4] = ["opt-level", "lto", "codegen-units", "debug-assertions"];

/// The profile a build script is running for, from the directory cargo put its `OUT_DIR` in.
///
/// `OUT_DIR` is `<target>[/<triple>]/<profile-dir>/build/<pkg>-<hash>/out`, and `<profile-dir>` is
/// the profile's name except that `dev` and `test` build into `debug` and `bench` into `release`.
/// Read back as `dev` and `release`: in this manifest `test` and `bench` restate nothing, so they
/// resolve to the same settings as the profile whose directory they share.
pub fn profile_from_out_dir(out_dir: &Path) -> Option<String> {
    let dir = out_dir
        .parent()?
        .parent()?
        .parent()?
        .file_name()?
        .to_str()?;
    Some(if dir == "debug" { "dev" } else { dir }.to_string())
}

/// The `[profile.<name>]` table's `key = value` pairs, quotes and comments stripped.
///
/// A line parser rather than a TOML dependency: the profile tables are flat scalars. Sub-tables
/// (`[profile.release.package.foo]`, `build-override`) are not this profile and are skipped.
fn manifest_table(manifest: &str, name: &str) -> Vec<(String, String)> {
    let header = format!("[profile.{name}]");
    let mut inside = false;
    let mut pairs = Vec::new();
    for raw in manifest.lines() {
        let line = raw.split('#').next().unwrap_or("").trim();
        if line.starts_with('[') {
            inside = line == header;
            continue;
        }
        if !inside {
            continue;
        }
        if let Some((key, value)) = line.split_once('=') {
            let value = value.trim().trim_matches('"').trim_matches('\'');
            pairs.push((key.trim().to_string(), value.to_string()));
        }
    }
    pairs
}

fn builtin(name: &str, key: &str) -> Option<&'static str> {
    match (name, key) {
        ("dev", "opt-level") => Some("0"),
        ("dev", "lto") => Some("false"),
        ("dev", "codegen-units") => Some("256"),
        ("dev", "debug-assertions") => Some("true"),
        ("release", "opt-level") => Some("3"),
        ("release", "lto") => Some("false"),
        ("release", "codegen-units") => Some("16"),
        ("release", "debug-assertions") => Some("false"),
        _ => None,
    }
}

/// The environment variable cargo reads to override `key` on profile `name`.
pub fn override_variable(name: &str, key: &str) -> String {
    format!("CARGO_PROFILE_{}_{}", name, key)
        .to_uppercase()
        .replace('-', "_")
}

/// The profile chain from `name` to its root, `name` first.
pub fn chain(
    manifest: &str,
    name: &str,
    env: &dyn Fn(&str) -> Option<String>,
) -> Result<Vec<String>, String> {
    let mut chain = vec![name.to_string()];
    loop {
        let current = chain.last().unwrap().clone();
        if current == "dev" || current == "release" {
            return Ok(chain);
        }
        let parent = env(&override_variable(&current, "inherits"))
            .or_else(|| {
                manifest_table(manifest, &current)
                    .into_iter()
                    .find(|(key, _)| key == "inherits")
                    .map(|(_, value)| value)
            })
            .or_else(|| match current.as_str() {
                "test" => Some("dev".to_string()),
                "bench" => Some("release".to_string()),
                _ => None,
            })
            .ok_or_else(|| format!("profile `{current}` names no `inherits`"))?;
        if chain.contains(&parent) {
            return Err(format!("profile `{name}` inherits in a cycle"));
        }
        chain.push(parent);
    }
}

/// The settings profile `name` builds with.
pub fn resolve(
    manifest: &str,
    name: &str,
    env: &dyn Fn(&str) -> Option<String>,
) -> Result<Settings, String> {
    let chain = chain(manifest, name, env)?;
    let lookup = |key: &str| -> String {
        for profile in &chain {
            if let Some(value) = env(&override_variable(profile, key)) {
                return value;
            }
            if let Some((_, value)) = manifest_table(manifest, profile)
                .into_iter()
                .find(|(k, _)| k == key)
            {
                return value;
            }
            if let Some(value) = builtin(profile, key) {
                return value.to_string();
            }
        }
        "unknown".to_string()
    };
    let lto = match lookup("lto").as_str() {
        // `true` and `"fat"` are the same setting; one spelling, so two stamps of it compare equal.
        "true" => "fat".to_string(),
        other => other.to_string(),
    };
    Ok(Settings {
        profile: name.to_string(),
        opt_level: lookup("opt-level"),
        lto,
        codegen_units: lookup("codegen-units"),
        debug_assertions: lookup("debug-assertions"),
    })
}

/// The stamp a measurement record carries: every setting that decides whether two timings compare.
///
/// `observed_opt_level` is cargo's own `OPT_LEVEL`. When it disagrees with the resolved value, an
/// override this resolver cannot see (`--config`, a `.cargo/config.toml` profile) is in effect, and
/// the stamp says so rather than reporting settings it knows to be wrong.
pub fn stamp(settings: &Settings, observed_opt_level: &str, rustflags: &str) -> String {
    let mut stamp = format!(
        "profile={}; opt-level={}; lto={}; codegen-units={}; debug-assertions={}; rustflags={}",
        settings.profile,
        settings.opt_level,
        settings.lto,
        settings.codegen_units,
        settings.debug_assertions,
        if rustflags.trim().is_empty() {
            "none"
        } else {
            rustflags.trim()
        },
    );
    if !observed_opt_level.is_empty() && observed_opt_level != settings.opt_level {
        stamp.push_str(&format!(
            "; UNSEEN OVERRIDE (cargo built at opt-level={observed_opt_level})"
        ));
    }
    stamp
}

/// Every environment variable a resolution of `name` read, for `cargo:rerun-if-env-changed`.
pub fn watched_variables(
    manifest: &str,
    name: &str,
    env: &dyn Fn(&str) -> Option<String>,
) -> Vec<String> {
    let chain = chain(manifest, name, env).unwrap_or_else(|_| vec![name.to_string()]);
    chain
        .iter()
        .flat_map(|profile| {
            KEYS.iter()
                .chain(std::iter::once(&"inherits"))
                .map(move |key| override_variable(profile, key))
        })
        .collect()
}
