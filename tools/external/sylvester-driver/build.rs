use std::{
    io::Write,
    process::{Command, Stdio},
};
fn main() {
    let mut identity = String::new();
    for file in [
        "Cargo.toml",
        "Cargo.lock",
        "rust-toolchain.toml",
        "src/main.rs",
        "build.rs",
    ] {
        println!("cargo:rerun-if-changed={file}");
        let output = Command::new("sha256sum")
            .arg(file)
            .output()
            .expect("sha256sum");
        assert!(output.status.success(), "hash {file}");
        identity.push_str(String::from_utf8(output.stdout).unwrap().trim());
        identity.push(';');
    }
    for name in [
        "PROFILE",
        "OPT_LEVEL",
        "DEBUG",
        "TARGET",
        "CARGO_ENCODED_RUSTFLAGS",
        "CARGO_PROFILE_RELEASE_LTO",
        "CARGO_PROFILE_RELEASE_CODEGEN_UNITS",
    ] {
        println!("cargo:rerun-if-env-changed={name}");
        identity.push_str(&format!(
            "{name}={};",
            std::env::var(name)
                .unwrap_or_default()
                .replace('\u{1f}', " ")
        ));
    }
    let output = Command::new(std::env::var_os("RUSTC").unwrap())
        .arg("-Vv")
        .output()
        .unwrap();
    identity.push_str(&String::from_utf8(output.stdout).unwrap().replace('\n', ";"));
    let mut hash = Command::new("sha256sum")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .unwrap();
    hash.stdin
        .take()
        .unwrap()
        .write_all(identity.as_bytes())
        .unwrap();
    let output = hash.wait_with_output().unwrap();
    assert!(output.status.success());
    let digest = String::from_utf8(output.stdout).unwrap();
    println!(
        "cargo:rustc-env=SYLVESTER_DRIVER_ID={}",
        digest.split_whitespace().next().unwrap()
    );
    println!("cargo:rustc-env=SYLVESTER_DRIVER_BUILD={identity}");
}
