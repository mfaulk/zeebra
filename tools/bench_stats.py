"""Benchmark ratio intervals and verdicts for M33 gates (plan §§8.4, 11.6, 12.2).

The bootstraps reproduce the copies in research/m29-final/verdicts.py and
research/m31-baseline/summarize.py draw for draw: `random.Random(seed)`, `choices` with
replacement, and the percentile indices [⌊0.025·D⌋, ⌊0.975·D⌋ − 1] of the sorted draws. Changing
any of those changes published digits; tools/test/bench-stats-test.py replays them.
"""
import random
import statistics
import zlib
from collections import namedtuple

DRAWS = 20_000
BASE_N = 9
EXTENSION_N = 12
ANOMALY_TOLERANCE = 1.10
VOID_FRACTION = 0.20
OUTCOMES = ("win", "loss", "inconclusive", "regression", "no-regression", "stopped", "anomaly")

# `n` counts the numerator's samples and `n_ref` the denominator's; they are equal when paired.
Interval = namedtuple("Interval", "median lo hi n n_ref")
# `extend` asks for the single predeclared extension; it is never set on an extended read.
Verdict = namedtuple("Verdict", "outcome extend reason")


def _seed(seed):
    """An int is used as given; a str is its CRC-32, as the M31 summaries keyed theirs by cell."""
    return zlib.crc32(seed.encode()) if isinstance(seed, str) else seed


def _percentiles(draws):
    draws.sort()
    return draws[int(0.025 * len(draws))], draws[int(0.975 * len(draws)) - 1]


def paired_ratios(a, b):
    """Per-repetition a[rep] / b[rep] over the repetitions both mappings hold, in repetition order."""
    return [a[k] / b[k] for k in sorted(set(a) & set(b))]


def paired_ratio(ratios, *, seed, draws=DRAWS):
    """Median of per-repetition ratios with a percentile bootstrap over repetitions (Zeebra ÷ Zeebra)."""
    if not ratios:
        raise ValueError("no paired repetitions")
    rng = random.Random(_seed(seed))
    k = len(ratios)
    lo, hi = _percentiles([statistics.median(rng.choices(ratios, k=k)) for _ in range(draws)])
    return Interval(statistics.median(ratios), lo, hi, k, k)


def independent_ratio(a, b, *, seed, draws=DRAWS):
    """median(a) ÷ median(b), each side resampled independently (Zeebra ÷ competitor)."""
    if not a or not b:
        raise ValueError("an arm has no samples")
    rng = random.Random(_seed(seed))
    na, nb = len(a), len(b)
    lo, hi = _percentiles([statistics.median(rng.choices(a, k=na)) / statistics.median(rng.choices(b, k=nb))
                           for _ in range(draws)])
    return Interval(statistics.median(a) / statistics.median(b), lo, hi, na, nb)


def relative_half_width(ci):
    return (ci.hi - ci.lo) / 2 / ci.median


def precise(ci, threshold, *, relative=True):
    """Half-width ≤ half the distance from the threshold to 1.0.

    The M32 copies (qualification, final, adaptive-dispatch) measured the half-width relative to the
    median; research/m32-gate-s measured it in ratio units (`relative=False`).
    """
    half = relative_half_width(ci) if relative else (ci.hi - ci.lo) / 2
    return half <= abs(threshold - 1.0) / 2


def _short(ci, min_n):
    return Verdict("stopped", False, f"n = {min(ci.n, ci.n_ref)} < {min_n}") if min(ci.n, ci.n_ref) < min_n else None


def regression_verdict(ci, bound, *, extended=False, min_n=BASE_N, relative=True):
    """§12.2: no-regression when the upper bound is ≤ `bound`; unreadable unless precise."""
    stopped = _short(ci, min_n)
    if stopped:
        return stopped
    if not precise(ci, bound, relative=relative):
        return Verdict("inconclusive", not extended, "imprecise")
    if ci.hi <= bound:
        return Verdict("no-regression", False, f"upper {ci.hi:.3f} ≤ {bound}")
    return Verdict("regression", False, f"upper {ci.hi:.3f} > {bound}")


def win_verdict(ci, *, extended=False, anomaly=False, small=False, min_n=BASE_N):
    """§8.4 on an independent Zeebra ÷ competitor interval: win iff median < 1 and upper < 1.

    `anomaly` marks a count where msolve was anomalously slow (see `msolve_anomaly`); `small` marks a
    row under the 300 ms floor (§11.6). Neither can score a win.
    """
    stopped = _short(ci, min_n)
    if stopped:
        return stopped
    if ci.median < 1 and ci.hi < 1:
        if anomaly:
            return Verdict("anomaly", False, "win against an msolve scaling anomaly")
        if small:
            return Verdict("inconclusive", False, "row under the 300 ms floor cannot win")
        return Verdict("win", False, f"upper {ci.hi:.3f} < 1")
    if ci.lo > 1:
        return Verdict("loss", False, f"lower {ci.lo:.3f} > 1")
    return Verdict("inconclusive", not extended, "interval spans 1")


def msolve_anomaly(walls_by_workers, workers, *, tolerance=ANOMALY_TOLERANCE):
    """True when the median at `workers` exceeds `tolerance` × the best median over the session's counts."""
    medians = {w: statistics.median(v) for w, v in walls_by_workers.items() if v}
    return medians[workers] > tolerance * min(medians.values())


def partition_contaminated(attempts, key="contaminated"):
    """(clean, contaminated) attempts by the journal's per-attempt flag; report both counts."""
    clean = [a for a in attempts if not a.get(key)]
    return clean, [a for a in attempts if a.get(key)]


def session_void(clean, contaminated, *, limit=VOID_FRACTION):
    """A session with more than `limit` of its attempts contaminated is void (#968)."""
    total = clean + contaminated
    return total > 0 and contaminated / total > limit


def warm_median(calls):
    """Median of the warm in-process calls: every call after the first."""
    return statistics.median(calls[1:])
