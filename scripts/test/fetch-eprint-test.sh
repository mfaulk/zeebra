#!/usr/bin/env bash
# Tests for scripts/fetch-eprint against a local fixture server; no live network access.
set -uo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
TOOL="$HERE/../fetch-eprint"
# shellcheck source=../fetch-eprint
. "$TOOL"
set +e

pass=0 fail=0
check() { # <label> <expected> <actual>
  if [ "$2" = "$3" ]; then
    pass=$((pass + 1))
  else
    fail=$((fail + 1))
    printf 'FAIL  %s\n  expected: %q\n  actual:   %q\n' "$1" "$2" "$3" >&2
  fi
}

WORK=$(mktemp -d "${TMPDIR:-/tmp}/fetch-eprint-test.XXXXXX")
LOG="$WORK/requests.log"
: >"$LOG"
python3 "$HERE/eprint-fixture-server.py" --port-file "$WORK/port" --log "$LOG" &
SERVER=$!
trap 'kill "$SERVER" 2>/dev/null; rm -rf -- "$WORK"' EXIT
for _ in $(seq 100); do [ -s "$WORK/port" ] && break; sleep 0.05; done
[ -s "$WORK/port" ] || { echo "fixture server did not start" >&2; exit 2; }
BASE="http://127.0.0.1:$(cat "$WORK/port")"

export EPRINT_CACHE_DIR="$WORK/cache" EPRINT_MIRROR_BASE="$BASE" EPRINT_RETRIES=3 \
  EPRINT_RETRY_DELAY=0 EPRINT_CONNECT_TIMEOUT=2 EPRINT_MAX_TIME=10
OUT="" ERR="" RC=0
run() { # runs the tool; sets OUT, ERR, RC
  OUT=$(bash "$TOOL" "$@" 2>"$WORK/stderr")
  RC=$?
  ERR=$(cat "$WORK/stderr")
}
requests() { grep -c -- "$1" "$LOG"; }
parts_left() { find "$EPRINT_CACHE_DIR" -name '*.part' 2>/dev/null | wc -l; }

# --- identifier parsing (pure) ---

# A bare id parses to year and three-digit-padded number.
check "bare id" "2025 2340" "$(parse_id 2025/2340)"
# Short numbers are zero-padded so 2021/51 and 2021/051 are one paper.
check "padding" "2021 051" "$(parse_id 2021/51)"
check "padded input" "2021 051" "$(parse_id 2021/051)"
# The original archive's abstract URL is accepted.
check "iacr.org url" "2025 2340" "$(parse_id https://eprint.iacr.org/2025/2340)"
# The .pdf suffix is optional.
check "iacr.org pdf url" "2025 2340" "$(parse_id https://eprint.iacr.org/2025/2340.pdf)"
# Mirror URLs and a trailing slash are accepted.
check "mirror url" "2025 2340" "$(parse_id https://eprint.iacr.asia/2025/2340.pdf)"
check "trailing slash" "2025 2340" "$(parse_id https://eprint.iacr.org/2025/2340/)"

# Malformed ids, traversal, foreign hosts, other schemes and shell metacharacters are all rejected.
for bad in "" "2025/" "/2025/2340" "2025/2340/" "2025-2340" "../2025/2340" "2025/2340/../../etc" \
  "2025/0" "1800/1" "2025/123456" "https://evil.example/2025/2340.pdf" \
  "https://eprint.iacr.org.evil.example/2025/2340" "https://user@eprint.iacr.org/2025/2340" \
  "file:///etc/passwd" "ftp://eprint.iacr.org/2025/2340" "https://eprint.iacr.org/2025/2340.pdf?x=1" \
  "https://eprint.iacr.org/archive/2025/2340.pdf" '2025/2340;touch /tmp/pwned' '$(id)' \
  "2025/2340 2025/2341" $'2025/2340\n'; do
  parse_id "$bad" >/dev/null 2>&1
  rc=$?
  check "rejects $(printf %q "$bad")" 1 "$rc"
done

# The CLI refuses a malformed id with status 64 and sends no request.
run "https://evil.example/2025/2340.pdf"
check "cli bad host rc" 64 "$RC"
check "cli bad host no request" 0 "$(wc -l <"$LOG")"

# A mirror base that is more than scheme://host[:port] is refused rather than used as a URL prefix.
EPRINT_MIRROR_BASE="$BASE/x?y=" run 2025/2340
check "bad mirror base rc" 64 "$RC"

# --- PDF validation (pure) ---

python3 -c 'import sys; sys.path.insert(0, sys.argv[1]); import importlib.util as u
s = u.spec_from_file_location("f", sys.argv[1] + "/eprint-fixture-server.py"); m = u.module_from_spec(s); s.loader.exec_module(m)
open(sys.argv[2], "wb").write(m.PDF); open(sys.argv[3], "wb").write(m.PDF[: len(m.PDF) // 2])' \
  "$HERE" "$WORK/good.pdf" "$WORK/trunc.pdf"
printf '<!DOCTYPE html><html></html>' >"$WORK/page.html"
: >"$WORK/empty.pdf"
# A complete PDF validates; truncated, empty and HTML files do not.
valid_pdf "$WORK/good.pdf"; check "valid pdf" 0 "$?"
valid_pdf "$WORK/trunc.pdf"; check "truncated pdf" 1 "$?"
valid_pdf "$WORK/empty.pdf"; check "empty pdf" 1 "$?"
valid_pdf "$WORK/page.html"; check "html as pdf" 1 "$?"

# --- network behaviour against the fixture server ---

# An empty cache downloads once, prints the absolute cached path, and installs a valid PDF.
run 2025/2340
check "download rc" 0 "$RC"
check "download path" "$WORK/cache/2025-2340.pdf" "$OUT"
valid_pdf "$OUT"; check "downloaded file valid" 0 "$?"
check "download one request" 1 "$(requests /2025/2340.pdf)"
check "download mode" 644 "$(stat -c %a "$OUT")"

# All three input forms resolve to the same cached file, served from cache with no new request.
for form in 2025/2340 https://eprint.iacr.org/2025/2340 https://eprint.iacr.org/2025/2340.pdf; do
  run "$form"
  check "same path for $form" "$WORK/cache/2025-2340.pdf" "$OUT"
done
check "cache hits make no request" 1 "$(requests /2025/2340.pdf)"

# A cache hit succeeds even when the mirror is unreachable.
EPRINT_MIRROR_BASE="http://127.0.0.1:9" run 2025/2340
check "offline cache hit rc" 0 "$RC"
check "offline cache hit path" "$WORK/cache/2025-2340.pdf" "$OUT"

# --refresh downloads again even though a valid copy is cached.
run --refresh 2025/2340
check "refresh rc" 0 "$RC"
check "refresh requests" 2 "$(requests /2025/2340.pdf)"

# HTTP 403 fails with status 1 after one request, leaves nothing cached, and suggests alternatives.
run 2000/403
check "403 rc" 1 "$RC"
check "403 not retried" 1 "$(requests /2000/403.pdf)"
check "403 nothing cached" no "$([ -e "$WORK/cache/2000-403.pdf" ] && echo yes || echo no)"
check "403 suggests import" yes "$(grep -q -- '--import' <<<"$ERR" && echo yes || echo no)"
check "403 stdout empty" "" "$OUT"

# HTTP 404 fails with status 1.
run 2000/404
check "404 rc" 1 "$RC"

# An HTML page served with HTTP 200 is rejected, not cached, and not retried.
run 2000/200
check "html 200 rc" 1 "$RC"
check "html 200 named" yes "$(grep -q 'HTML page' <<<"$ERR" && echo yes || echo no)"
check "html 200 not cached" no "$([ -e "$WORK/cache/2000-200.pdf" ] && echo yes || echo no)"
check "html 200 not retried" 1 "$(requests /2000/200.pdf)"

# A truncated PDF is retried up to the bound, then rejected and not cached.
run 2000/100
check "truncated rc" 1 "$RC"
check "truncated retried" 3 "$(requests /2000/100.pdf)"
check "truncated not cached" no "$([ -e "$WORK/cache/2000-100.pdf" ] && echo yes || echo no)"

# Transient 503s are retried and the third attempt succeeds.
run 2000/503
check "503 then ok rc" 0 "$RC"
check "503 attempts" 3 "$(requests /2000/503.pdf)"

# A persistent 500 stops after EPRINT_RETRIES attempts with status 2.
run 2000/500
check "500 rc" 2 "$RC"
check "500 bounded" 3 "$(requests /2000/500.pdf)"

# An unreachable mirror with an empty cache fails with status 2.
EPRINT_MIRROR_BASE="http://127.0.0.1:9" EPRINT_RETRIES=2 run 2000/1
check "unreachable rc" 2 "$RC"

# A corrupt cached file is discarded with a warning and fetched again.
printf 'garbage' >"$WORK/cache/2000-001.pdf"
run 2000/1
check "corrupt cache rc" 0 "$RC"
check "corrupt cache warned" yes "$(grep -q 'not a complete PDF' <<<"$ERR" && echo yes || echo no)"
valid_pdf "$WORK/cache/2000-001.pdf"; check "corrupt cache replaced" 0 "$?"

# The destination never exists half-written: during a slow download only a .part file exists.
bash "$TOOL" 2000/777 >"$WORK/slow.out" 2>/dev/null &
slow=$!
for _ in $(seq 40); do [ "$(parts_left)" -ge 1 ] && break; sleep 0.02; done
check "no partial at destination" no "$([ -e "$WORK/cache/2000-777.pdf" ] && echo yes || echo no)"
check "part file during download" 1 "$(parts_left)"
wait "$slow"
check "slow download rc" 0 "$?"
valid_pdf "$WORK/cache/2000-777.pdf"; check "slow download valid" 0 "$?"

# Eight concurrent fetches of one uncached paper make one request and all print the same path.
rm -f "$WORK/cache/2000-777.pdf"
before=$(requests /2000/777.pdf)
pids=()
for i in $(seq 8); do
  bash "$TOOL" https://eprint.iacr.org/2000/777.pdf >"$WORK/c$i.out" 2>"$WORK/c$i.err" &
  pids+=("$!")
done
crc=0
for p in "${pids[@]}"; do wait "$p" || crc=1; done
check "concurrent all succeed" 0 "$crc"
check "concurrent one request" $((before + 1)) "$(requests /2000/777.pdf)"
check "concurrent same path" 1 "$(cat "$WORK"/c*.out | sort -u | wc -l)"
valid_pdf "$WORK/cache/2000-777.pdf"; check "concurrent result valid" 0 "$?"

# No incomplete download is left behind by any of the above.
check "no part files left" 0 "$(parts_left)"

# --- --import ---

# A valid local PDF is installed as the paper without any request.
n=$(wc -l <"$LOG")
run --import "$WORK/good.pdf" 1999/5
check "import rc" 0 "$RC"
check "import path" "$WORK/cache/1999-005.pdf" "$OUT"
check "import no request" "$n" "$(wc -l <"$LOG")"
# A non-PDF is refused for import.
run --import "$WORK/page.html" 1999/6
check "import html rc" 1 "$RC"

# --- --text ---

# A missing extractor gives status 3 and names the cached PDF; the PDF stays cached.
EPRINT_PDFTOTEXT=no-such-pdftotext run --text 2025/2340
check "missing extractor rc" 3 "$RC"
check "missing extractor names pdf" yes "$(grep -q '2025-2340.pdf' <<<"$ERR" && echo yes || echo no)"
check "missing extractor stdout empty" "" "$OUT"

if command -v pdftotext >/dev/null 2>&1; then
  # --text prints a cached layout extraction containing the paper's text.
  run --text 2025/2340
  check "text rc" 0 "$RC"
  check "text path" "$WORK/cache/2025-2340.txt" "$OUT"
  check "text content" yes "$(grep -q 'Fixture paper' "$OUT" 2>/dev/null && echo yes || echo no)"
  # A second --text call is served from cache even with the mirror unreachable.
  EPRINT_MIRROR_BASE="http://127.0.0.1:9" EPRINT_PDFTOTEXT=no-such-pdftotext run --text 2025/2340
  check "cached text rc" 0 "$RC"
else
  echo "SKIP  --text extraction: pdftotext not installed" >&2
fi

printf 'fetch-eprint: %d passed, %d failed\n' "$pass" "$fail"
[ "$fail" -eq 0 ]
