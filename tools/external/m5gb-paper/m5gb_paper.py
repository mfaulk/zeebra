"""M5GB paper-reference adapter (#1165): input writer, output parser, canonicalizer and runner.

Polynomials are dicts {exponent tuple: coefficient mod p}, with x1 > x2 > ... > xn and variable
i written to MathicGB as the i-th letter (a, b, ..., z, A, ..., Z). `grevlex` is MathicGB's
default `revlex` base order under one all-ones grading. `lex` is its `lex` base order with no
grading, which ranks the *last* letter highest (`LexBaseOrderFromRight`), so under lex variable i
is written as letter n - 1 - i. `set_order` selects the order every function below uses.
"""

import os
import re
import signal
import subprocess
import time

LETTERS = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"


def grevlex_key(e):
    """Sort key: a larger key is a larger monomial."""
    return (sum(e), tuple(-x for x in reversed(e)))


def lex_key(e):
    return tuple(e)


KEYS = {"grevlex": grevlex_key, "lex": lex_key}
_order = ["grevlex"]


def set_order(name):
    _order[0] = name


def order_key(e):
    return KEYS[_order[0]](e)


def normalize(poly, p):
    return {e: c % p for e, c in poly.items() if c % p}


def leading(poly):
    return max(poly, key=order_key)


def monic(poly, p):
    lead = leading(poly)
    inv = pow(poly[lead], p - 2, p)
    return {e: c * inv % p for e, c in poly.items()}


def divides(a, b):
    return all(x <= y for x, y in zip(a, b))


# --- text formats -------------------------------------------------------------------------------


def parse_zeebra(text, variables, p):
    """A polynomial in Zeebra's syntax (`3*x1^2*x2 - x3 + 1`), names matched whole."""
    index = {v: i for i, v in enumerate(variables)}
    n = len(variables)
    poly = {}
    compact = re.sub(r"\s+", "", text)
    for sign, chunk in re.findall(r"([+-]?)([^+-]+)", compact):
        coef, exps = 1, [0] * n
        for factor in chunk.split("*"):
            base, _, power = factor.partition("^")
            power = int(power) if power else 1
            if base in index:
                exps[index[base]] += power
            else:
                coef *= int(base) ** power
        if sign == "-":
            coef = -coef
        e = tuple(exps)
        poly[e] = (poly.get(e, 0) + coef) % p
    return normalize(poly, p)


def format_zeebra(poly, variables):
    if not poly:
        return "0"
    terms = []
    for e in sorted(poly, key=order_key, reverse=True):
        factors = [
            v if x == 1 else f"{v}^{x}" for v, x in zip(variables, e) if x
        ]
        c = poly[e]
        terms.append("*".join([str(c)] + factors) if factors else str(c))
    return " + ".join(terms)


def parse_mathic(text, n, p):
    """A polynomial as MathicGB writes it (`-3a2b+c-1`): letters, exponents after letters."""
    poly = {}
    for sign, coef, mono in re.findall(r"([+-]?)(\d*)([a-zA-Z0-9]*?)(?=[+-]|$)", text.strip()):
        if not coef and not mono:
            continue
        exps = [0] * n
        if mono and mono != "1":
            for letter, power in re.findall(r"([a-zA-Z])(\d*)", mono):
                exps[LETTERS.index(letter)] += int(power) if power else 1
        value = int(coef) if coef else 1
        if sign == "-":
            value = -value
        e = tuple(exps)
        poly[e] = (poly.get(e, 0) + value) % p
    return normalize(poly, p)


def format_mathic(poly, n):
    if not poly:
        return "0"
    out = []
    for e in sorted(poly, key=order_key, reverse=True):
        mono = "".join(
            LETTERS[i] + (str(x) if x > 1 else "") for i, x in enumerate(e) if x
        )
        c = poly[e]
        text = mono if c == 1 and mono else f"{c}{mono}"
        out.append(text)
    return "+".join(out)


def _flip(poly):
    """Exponent tuples reversed: the letter mapping MathicGB's lex needs (see the module doc)."""
    if _order[0] != "lex":
        return poly
    return {tuple(reversed(e)): c for e, c in poly.items()}


def write_ideal(path, polys, n, p):
    """MathicGB ideal format: `<p> <n> <order>`, the generator count, one generator per line.

    `<order>` is `1 <n ones>` for grevlex (MathicGB's default `revlex` base order under one
    all-ones grading) and `lex 0` for lex.
    """
    if n > len(LETTERS):
        raise ValueError(f"MathicGB names at most {len(LETTERS)} variables")
    header = "lex 0" if _order[0] == "lex" else "1 " + " ".join(["1"] * n)
    with open(path, "w") as f:
        f.write(f"{p} {n} {header}\n{len(polys)}\n")
        for poly in polys:
            f.write(format_mathic(_flip(poly), n) + "\n")


def parse_gb_file(path, n, p):
    """The `.gb` file `-outputResult 1` writes: `-- gb: ----` then `i <sig>  <poly>` lines."""
    basis = []
    with open(path) as f:
        for line in f:
            line = line.rstrip("\n")
            if not line or line.startswith("--"):
                continue
            parts = line.split("  ", 1)
            if len(parts) != 2:
                raise ValueError(f"unparsed basis line: {line!r}")
            basis.append(_flip(parse_mathic(parts[1], n, p)))
    return basis


# --- canonical reduced basis --------------------------------------------------------------------


class Reducer:
    """Full reduction modulo a fixed list of monic polynomials."""

    def __init__(self, basis, p):
        self.p = p
        self.basis = [(leading(g), g) for g in basis]

    def divisor(self, e):
        for lead, g in self.basis:
            if divides(lead, e):
                return lead, g
        return None

    def normal_form(self, poly, skip=None):
        p = self.p
        poly = dict(poly)
        remainder = {}
        steps = 0
        while poly:
            e = leading(poly)
            c = poly.pop(e)
            found = None
            for lead, g in self.basis:
                if g is not skip and divides(lead, e):
                    found = (lead, g)
                    break
            if found is None:
                remainder[e] = c
                continue
            lead, g = found
            shift = tuple(x - y for x, y in zip(e, lead))
            for ge, gc in g.items():
                if ge == lead:
                    continue
                t = tuple(x + y for x, y in zip(ge, shift))
                v = (poly.get(t, 0) - c * gc) % p
                if v:
                    poly[t] = v
                else:
                    poly.pop(t, None)
            steps += 1
        return remainder, steps


def canonical_reduced(polys, p):
    """Minimize and interreduce a claimed Groebner basis; also check it generates the result.

    Returns (reduced basis sorted by leading monomial, every input reduced to zero, steps).
    The zero check is what makes dropping a non-minimal element safe: a set that is not a Groebner
    basis can lose generators on minimization, and then some input does not reduce to zero.
    """
    polys = [monic(normalize(g, p), p) for g in polys if normalize(g, p)]
    if not polys:
        return [], True, 0
    one = (0,) * len(leading(polys[0]))
    if any(leading(g) == one for g in polys):
        return [{one: 1}], True, 0
    polys.sort(key=lambda g: order_key(leading(g)))
    minimal = []
    for g in polys:
        lead = leading(g)
        if not any(divides(leading(h), lead) for h in minimal):
            minimal.append(g)
    steps = 0
    reduced = []
    reducer = Reducer(minimal, p)
    for g in minimal:
        lead = leading(g)
        tail = {e: c for e, c in g.items() if e != lead}
        nf, s = reducer.normal_form(tail, skip=g)
        steps += s
        nf[lead] = 1
        reduced.append(nf)
    final = Reducer(reduced, p)
    zero = True
    for g in polys:
        nf, s = final.normal_form(g)
        steps += s
        if nf:
            zero = False
            break
    reduced.sort(key=lambda g: order_key(leading(g)))
    return reduced, zero, steps


def is_reduced(polys, p):
    """Whether a list is already the reduced basis: monic, minimal, tails irreducible."""
    polys = [normalize(g, p) for g in polys]
    if any(not g for g in polys):
        return False
    leads = [leading(g) for g in polys]
    if len(set(leads)) != len(leads):
        return False
    for g, lead in zip(polys, leads):
        if g[lead] != 1:
            return False
        for e in g:
            if any(divides(other, e) for other in leads if other != lead):
                return False
    return True


def canonical_text(basis, variables):
    return [format_zeebra(g, variables) for g in basis]


# --- running the binary -------------------------------------------------------------------------

COUNTER_PATTERNS = {
    "interreduction_rounds": r"Did (\d+) iterations of interreduction",
    "regular_reducer_calls": r"Calls to regular Reducer: (\d+)",
    "skipped_elements": r"Overall skipped elements: (\d+)",
    "nonfinite_flags_terms": r"Got (\d+) non-infinity flags with terms",
    "nonfinite_flags_m": r"Got (\d+) non-infinity flags with M elements",
    "signature_hits": r"Got (\d+) signature hits",
    "reduce_invocations": r"Overall Invocations: (\d+)",
    "store_entries": r"Entry count: (\d+)",
    "store_approx_kib": r"Approximated memory consumption: (\d+) MB",
    "basis_elements": r"Basis elements:\s+([\d,]+)",
    "basis_terms": r"Terms for basis:\s+([\d,]+)",
    "minimal_syzygies": r"Minimal syzygies:\s+([\d,]+) ",
    "spairs_considered": r"S-pairs considered:\s+([\d,]+)",
    "spairs_done": r"S pairs done:\s+([\d,]+)",
    "spair_signatures_done": r"S pair sigs done:\s+([\d,]+)",
    "actual_reductions": r"Actual reductions: (\d+)",
    "koszul_queued": r"Queued Koszul syzygies:\s+([\d,]+)",
    "probe_poly_append_collisions": r"hash-probe poly-append collisions: (\d+)",
    "probe_reducer_map_collisions": r"hash-probe reducer-map collisions: (\d+)",
    "probe_reducer_map_lookups": r"hash-probe lookups: (\d+)",
}


def parse_counters(stdout):
    counters = {}
    for name, pattern in COUNTER_PATTERNS.items():
        match = re.search(pattern, stdout)
        if match:
            counters[name] = int(match.group(1).replace(",", ""))
    match = re.search(r"total compute time:\s+([\d.e+-]+) -- seconds", stdout)
    if match:
        counters["internal_compute_s"] = float(match.group(1))
    match = re.search(r"Irr Load Factor: ([\d.e+-]+)", stdout)
    if match:
        counters["irreducible_load_factor"] = float(match.group(1))
    return counters


def _rss_kib(pid):
    try:
        out = subprocess.run(
            ["ps", "-o", "rss=", "-p", str(pid)], capture_output=True, text=True, timeout=5
        ).stdout.strip()
        return int(out) if out else 0
    except (subprocess.SubprocessError, ValueError):
        return 0


def run_binary(binary, ideal_path, wall_cap_s, rss_cap_bytes, poll_s=0.05):
    """One subprocess, watched: wall cap and sampled-RSS cap, then exact peak RSS from wait4.

    Status: `ok`, `exit:<code>`, `signal:<name>`, `wall-cap` or `rss-cap`. macOS does not bind
    `ulimit -v`, so the memory cap is this watchdog killing the process group when a sample of
    `ps -o rss` passes it; a fast allocation can overshoot by up to one poll interval.
    """
    workdir = os.path.dirname(os.path.abspath(ideal_path))
    out_path = ideal_path + ".stdout"
    err_path = ideal_path + ".stderr"
    start = time.monotonic()
    with open(out_path, "w") as out, open(err_path, "w") as err:
        proc = subprocess.Popen(
            [binary, "M5GB", os.path.basename(ideal_path), "-reducer", "27", "-outputResult", "on"],
            cwd=workdir,
            stdout=out,
            stderr=err,
            start_new_session=True,
        )
        status = None
        sampled_peak = 0
        while True:
            pid, wait_status, usage = os.wait4(proc.pid, os.WNOHANG)
            if pid:
                break
            elapsed = time.monotonic() - start
            rss = _rss_kib(proc.pid) * 1024
            sampled_peak = max(sampled_peak, rss)
            if elapsed > wall_cap_s:
                status = "wall-cap"
            elif rss > rss_cap_bytes:
                status = "rss-cap"
            if status:
                os.killpg(proc.pid, signal.SIGKILL)
                pid, wait_status, usage = os.wait4(proc.pid, 0)
                break
            time.sleep(poll_s)
    wall = time.monotonic() - start
    if status is None:
        if os.WIFSIGNALED(wait_status):
            status = "signal:" + signal.Signals(os.WTERMSIG(wait_status)).name
        elif os.WEXITSTATUS(wait_status) != 0:
            status = f"exit:{os.WEXITSTATUS(wait_status)}"
        else:
            status = "ok"
    with open(out_path) as f:
        stdout = f.read()
    with open(err_path) as f:
        stderr = f.read()
    return {
        "status": status,
        "wall_s": wall,
        # macOS reports ru_maxrss in bytes.
        "peak_rss_bytes": usage.ru_maxrss if usage else None,
        "sampled_peak_rss_bytes": sampled_peak,
        "stdout": stdout,
        "stderr": stderr,
    }
