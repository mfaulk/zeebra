#!/usr/bin/env bash
# Runs every available external comparand on the shared system in tools/external/smoke, then
# compares the bases.
#
# The comparison is on canonical leading-monomial exponent vectors, because the four tools
# spell a monomial four ways (`x^1*y^1`, `x*y`, `xy`, `1,1,0`) and a textual diff would report
# a disagreement that is purely notational. A tool that is not installed is reported absent,
# never as agreement — the same discipline as the Singular oracle
# (src/grobner/differential/singular.rs:8).

set -uo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PREFIX="${ZEEBRA_EXT_PREFIX:-$HOME/.local/opt/zeebra-ext}"
export ZEEBRA_EXT_PREFIX="$PREFIX"
# shellcheck source=../env.sh
. "$HERE/../env.sh"

SYSTEM="$HERE/system.ms"
OUT="${TMPDIR:-/tmp}/zeebra-smoke-$$"
mkdir -p "$OUT"
trap 'rm -rf "$OUT"' EXIT

VARS="$(head -1 "$SYSTEM")"
CHAR="$(sed -n 2p "$SYSTEM")"

RAN=()
ABSENT=()

# Turns one monomial per line into one exponent vector per line. Accepts `x^2*y`, `x*y`, `z`,
# `1`, and passes an already-canonical `1,1,0` through unchanged.
canon() {
  awk -v vl="$VARS" '
    BEGIN { nv = split(vl, V, ",") ; for (i=1;i<=nv;i++) gsub(/ /, "", V[i]) }
    {
      line = $0
      gsub(/[ \t]/, "", line)
      if (line == "") next
      # already an exponent vector?
      if (line ~ /^[0-9]+(,[0-9]+)*$/ && line ~ /,/) { print line; next }
      gsub(/[,:]/, "", line)
      for (i = 1; i <= nv; i++) e[i] = 0
      n = split(line, F, /\*/)
      for (k = 1; k <= n; k++) {
        f = F[k]
        if (f == "" || f == "1") continue
        p = index(f, "^")
        if (p > 0) { b = substr(f, 1, p - 1); x = substr(f, p + 1) + 0 }
        else       { b = f; x = 1 }
        for (i = 1; i <= nv; i++) if (V[i] == b) e[i] += x
      }
      s = e[1]
      for (i = 2; i <= nv; i++) s = s "," e[i]
      print s
    }'
}

# Everything after the "--- leading monomials ---" marker, or (msolve -g 1) the bracketed list.
leads_after_marker() {
  sed -n '/--- leading monomials ---/,$p' "$1" | tail -n +2
}

record() { # <name> <canonical-file>
  sort "$2" > "$OUT/$1.canon"
  RAN+=("$1")
}

echo "system:         $SYSTEM"
echo "variables:      $VARS   (first is greatest)"
echo "characteristic: $CHAR"
echo "order:          degrevlex"
echo

# --- msolve ----------------------------------------------------------------------------------
if command -v msolve > /dev/null 2>&1; then
  /usr/bin/time -f '%e %M' -o "$OUT/msolve.time" \
    msolve -f "$SYSTEM" -g 2 -o "$OUT/msolve.gb" > /dev/null 2>&1
  msolve -f "$SYSTEM" -g 1 -o "$OUT/msolve.lead" > /dev/null 2>&1
  # The leading ideal prints as a bracketed, comma-separated list after a `#` header block.
  grep -v '^#' "$OUT/msolve.lead" | tr -d '[]:' | tr ',' '\n' | canon > "$OUT/msolve.c"
  record msolve "$OUT/msolve.c"
  printf 'msolve        %s   wall %ss  maxRSS %sK  %s elements\n' \
    "$(msolve -V 2>&1 | head -1)" \
    "$(cut -d' ' -f1 "$OUT/msolve.time")" \
    "$(cut -d' ' -f2 "$OUT/msolve.time")" \
    "$(wc -l < "$OUT/msolve.canon")"
else
  ABSENT+=(msolve)
fi

# --- Groebner.jl -----------------------------------------------------------------------------
if command -v julia > /dev/null 2>&1; then
  if julia "$HERE/system.jl" > "$OUT/groebner.gb" 2>"$OUT/groebner.err"; then
    leads_after_marker "$OUT/groebner.gb" | canon > "$OUT/groebner.c"
    record groebner.jl "$OUT/groebner.c"
    printf 'Groebner.jl   %s  %s elements\n' \
      "$(grep -m1 '^#seconds:' "$OUT/groebner.gb" | sed 's/^#seconds: *//;s/^/inner /;s/$/s/')" \
      "$(wc -l < "$OUT/groebner.jl.canon")"
  else
    ABSENT+=("Groebner.jl (ran but failed; see below)")
    sed -n '1,12p' "$OUT/groebner.err"
  fi
else
  ABSENT+=("Groebner.jl (no julia on PATH)")
fi

# --- Sagebrush -------------------------------------------------------------------------------
if command -v sagebrush-gb-driver > /dev/null 2>&1; then
  if sagebrush-gb-driver "$SYSTEM" > "$OUT/sagebrush.gb" 2>"$OUT/sagebrush.err"; then
    leads_after_marker "$OUT/sagebrush.gb" | canon > "$OUT/sagebrush.c"
    record sagebrush "$OUT/sagebrush.c"
    printf 'Sagebrush     %s  %s elements  (SAGEBRUSH_THREADS=%s)\n' \
      "$(grep -m1 '^#seconds:' "$OUT/sagebrush.gb" | sed 's/^#seconds: *//;s/^/inner /;s/$/s/')" \
      "$(wc -l < "$OUT/sagebrush.canon")" \
      "${SAGEBRUSH_THREADS:-unset (all cores)}"
  else
    ABSENT+=("Sagebrush (ran but failed)")
    sed -n '1,12p' "$OUT/sagebrush.err"
  fi
else
  ABSENT+=("Sagebrush (no sagebrush-gb-driver on PATH)")
fi

# --- Singular --------------------------------------------------------------------------------
if command -v Singular > /dev/null 2>&1; then
  Singular -q "$HERE/system.sing" > "$OUT/singular.gb" 2>&1
  leads_after_marker "$OUT/singular.gb" | canon > "$OUT/singular.c"
  record singular "$OUT/singular.c"
  printf 'Singular      %s  %s elements\n' \
    "$(Singular --version 2>&1 | head -1 | sed 's/Singular for //')" \
    "$(wc -l < "$OUT/singular.canon")"
else
  ABSENT+=(Singular)
fi

echo
if [ "${#ABSENT[@]}" -gt 0 ]; then
  echo "absent (reported absent, not as agreement):"
  printf '  - %s\n' "${ABSENT[@]}"
  echo
fi

if [ "${#RAN[@]}" -lt 2 ]; then
  echo "fewer than two tools ran: no comparison possible"
  exit 1
fi

echo "canonical leading monomials (exponent vectors over $VARS, sorted):"
paste -d'|' "$OUT/${RAN[0]}.canon" | sed 's/^/  /'
echo

ref="${RAN[0]}"
status=0
for t in "${RAN[@]:1}"; do
  if cmp -s "$OUT/$ref.canon" "$OUT/$t.canon"; then
    printf '  %-14s == %s\n' "$t" "$ref"
  else
    printf '  %-14s != %s  <-- DISAGREEMENT\n' "$t" "$ref"
    diff "$OUT/$ref.canon" "$OUT/$t.canon" | sed 's/^/      /'
    status=1
  fi
done

echo
if [ "$status" -eq 0 ]; then
  echo "AGREE: ${#RAN[@]} tools, identical leading-monomial sets (${RAN[*]})"
else
  echo "DISAGREE: see above"
fi
exit "$status"
