//! Stamps the concrete cargo profile into the library as `ZEEBRA_BUILD_PROFILE` (#1172).
//!
//! Cargo tells a build script `PROFILE` (`debug` or `release`) and `OPT_LEVEL`, but not `lto` or
//! `codegen-units`, which are what changed meaning when the release profile did (#1170). The
//! resolver reads them from `Cargo.toml` and the `CARGO_PROFILE_*` overrides; it lives under
//! `src/` so the library's tests exercise the same code.

#[path = "src/util/build_profile/resolve.rs"]
mod resolve;

fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-changed=src/util/build_profile/resolve.rs");
    println!("cargo:rerun-if-changed=Cargo.toml");
    println!("cargo:rerun-if-env-changed=CARGO_ENCODED_RUSTFLAGS");

    let out_dir = std::env::var_os("OUT_DIR").expect("cargo sets OUT_DIR");
    let manifest_dir =
        std::env::var_os("CARGO_MANIFEST_DIR").expect("cargo sets CARGO_MANIFEST_DIR");
    let manifest = std::fs::read_to_string(std::path::Path::new(&manifest_dir).join("Cargo.toml"))
        .expect("read Cargo.toml");
    let env = |name: &str| std::env::var(name).ok();

    let observed = env("OPT_LEVEL").unwrap_or_default();
    let rustflags = env("CARGO_ENCODED_RUSTFLAGS")
        .unwrap_or_default()
        .replace('\u{1f}', " ");
    let stamp = match resolve::profile_from_out_dir(std::path::Path::new(&out_dir)) {
        Some(name) => {
            for variable in resolve::watched_variables(&manifest, &name, &env) {
                println!("cargo:rerun-if-env-changed={variable}");
            }
            match resolve::resolve(&manifest, &name, &env) {
                Ok(settings) => resolve::stamp(&settings, &observed, &rustflags),
                Err(error) => format!("profile={name}; unresolved: {error}; opt-level={observed}"),
            }
        }
        None => format!("profile=unknown; opt-level={observed}"),
    };
    println!("cargo:rustc-env=ZEEBRA_BUILD_PROFILE={stamp}");
}
