#!/usr/bin/env bash
# Tests for tools/check-archive-reproducible.sh, over a throwaway repository holding a tiny crate.
#
# The crate is built for real: what the check has to get right is whether two `git archive` builds
# in different directories come out byte-identical, and only a compiler can say that. The first
# commit reproduces #1021's cause, a path read at run time from `env!("CARGO_MANIFEST_DIR")`, which
# embeds the build directory; the second embeds the file's contents instead.
set -uo pipefail

CHECK="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)/check-archive-reproducible.sh"
pass=0 fail=0

check_rc() { # <label> <expected-rc> <actual-rc>
  if [ "$2" -eq "$3" ]; then
    pass=$((pass + 1))
  else
    fail=$((fail + 1))
    printf 'FAIL  %s\n  expected rc: %s\n  actual rc:   %s\n' "$1" "$2" "$3" >&2
  fi
}

check_has() { # <label> <needle> <haystack>
  if [[ "$3" == *"$2"* ]]; then
    pass=$((pass + 1))
  else
    fail=$((fail + 1))
    printf 'FAIL  %s\n  expected to contain: %s\n  in: %s\n' "$1" "$2" "$3" >&2
  fi
}

tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
repo="$tmp/repo"
mkdir -p "$repo/src"
git -C "$repo" init -q
git -C "$repo" config user.email test@example.invalid
git -C "$repo" config user.name test
cat > "$repo/Cargo.toml" <<'EOF'
[package]
name = "tiny"
version = "0.1.0"
edition = "2021"

[dependencies]
EOF
echo "frozen" > "$repo/data.txt"
cat > "$repo/src/main.rs" <<'EOF'
fn main() {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/data.txt");
    print!("{}", std::fs::read_to_string(path).unwrap());
}
EOF
git -C "$repo" add -A
git -C "$repo" commit -qm runtime-path
runtime="$(git -C "$repo" rev-parse HEAD)"
cat > "$repo/src/main.rs" <<'EOF'
fn main() {
    print!("{}", include_str!("../data.txt"));
}
EOF
git -C "$repo" commit -qam embedded
embedded="$(git -C "$repo" rev-parse HEAD)"

run() { # <commit> -> output, sets rc
  rc=0
  out="$(RUSTC_WRAPPER="" "$CHECK" --repo "$repo" --workdir "$tmp/work-$1" "$1" release/tiny \
    -- --release --offline 2>&1)" || rc=$?
}

# A build that embeds its directory differs between the two directories, and the check names the
# embedded path relative to the build, so the fix is findable from the report alone.
run "$runtime"
check_rc "a runtime CARGO_MANIFEST_DIR path is not reproducible" 1 "$rc"
check_has "the embedded path is named" "<src>/data.txt" "$out"

# The same program with the file embedded builds identically in both directories.
run "$embedded"
check_rc "an embedded file is reproducible" 0 "$rc"
check_has "the shared hash is reported" "reproducible" "$out"

# A build that fails is a failed check, not a verdict either way.
run 0000000000000000000000000000000000000000
check_rc "an unknown commit is an error" 2 "$rc"

# Usage errors are rc 2.
rc=0; "$CHECK" >/dev/null 2>&1 || rc=$?
check_rc "no arguments is a usage error" 2 "$rc"

printf '%d passed, %d failed\n' "$pass" "$fail"
[ "$fail" -eq 0 ]
