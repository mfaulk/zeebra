"""#1180: idle-vs-idle false-failure rates of candidate replacements for #1107's H1 width clause.

Usage: python3 -I analyze.py [--sims S] [--draws D] [--perms P] [--jobs J] --json results.json --out tables.md

Two checks, both on #1107's retained records and both for sense only (#1180: these data do not decide):

- **observed**: each session's closing W0 judged as if it were a loaded block, against its opening W0.
  This is #1107's §5 control, extended to every candidate it can be applied to.
- **resampled**: per cell and session, the two W0 A/A series are pooled (60 ratios) and treated as
  one idle distribution. Each trial draws an opening W0, a closing W0 and seven "loaded" blocks of
  n = 30 from it, with replacement, and judges every candidate on them. No block differs from idle
  in distribution, so every failure is a false failure. Units are aggregated as #1107's gates are:
  a workload fails when any of its 14 held-out units (7 cells x 2 sessions) fails, and the campaign
  is a false no-go when all seven workloads fail.
"""
import argparse
import json
import math
import random
import statistics
import sys
from collections import defaultdict
from multiprocessing import Pool
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
CAL = REPO / 'research' / 'concurrent-calibration'
sys.path.insert(0, str(CAL))
sys.path.insert(0, str(REPO / 'tools'))
import bench_stats as bs  # noqa: E402
import calib  # noqa: E402
from extract import read  # noqa: E402

K = 1.5  # #1107's multiple
HALF_BOUND = 0.010  # §7.2's design half-width: a 2% effect is then `precise` (tools/bench_stats.py)
HALF_SENSITIVITY = (0.0100, 0.0125, 0.0150, 0.0200)
WORKLOAD_ALPHA = 0.05
HELD_OUT_UNITS = 14  # per workload: 7 held-out cells x 2 sessions
UNIT_ALPHA = 1 - (1 - WORKLOAD_ALPHA) ** (1 / HELD_OUT_UNITS)  # Šidák: 0.00366
LOADED_BLOCKS = 7  # W1, W2, W3, W4-8, W4-16, W4-32, W5
INFLATION = (1.5, 2.0, 3.0)  # synthetic dispersion multiples for the power check
CANDIDATES = ('A0', 'A1', 'A2', 'B', 'C')
NAMES = {
    'A0': 'loaded width ≤ 1.5 × opening W0 width (#1107 as run)',
    'A1': 'loaded width ≤ 1.5 × pooled-W0 width (both W0s, resampled at the loaded n)',
    'A2': 'loaded width ≤ 1.5 × the wider of the two W0 widths',
    'B': f'one-sided permutation scale test vs both W0s, fail at p ≤ {UNIT_ALPHA:.5f}',
    'C': f'loaded half-width ≤ {HALF_BOUND}',
}


# Statistics -------------------------------------------------------------------------------------
def boot_width(xs, *, seed, draws=bs.DRAWS, k=None):
    """Width of the percentile-bootstrap CI of the median of k resampled values (k = len(xs): as
    bs.paired_ratio, draw for draw)."""
    rng = random.Random(bs._seed(seed))
    k = len(xs) if k is None else k
    lo, hi = bs._percentiles([statistics.median(rng.choices(xs, k=k)) for _ in range(draws)])
    return hi - lo


def _abs_median(xs):
    return statistics.median(abs(x) for x in xs)


def _centered_logs(xs):
    logs = [math.log(x) for x in xs]
    m = statistics.median(logs)
    return [v - m for v in logs]


def scale_pvalue(loaded, idle, *, perms, seed):
    """One-sided permutation test that the loaded A/A series is more dispersed than the idle one.

    Each series is log-transformed and centred on its own median, so a shift in location (which the
    median clause judges) does not count. The statistic is the ratio of median absolute deviations;
    labels are permuted over the pooled centred values. Returns (1 + #{T* ≥ T}) / (1 + perms)."""
    lc, ic = _centered_logs(loaded), _centered_logs(idle)
    nl = len(lc)
    t = _abs_median(lc) / _abs_median(ic)
    pool = lc + ic
    rng = random.Random(bs._seed(seed))
    hits = 0
    for _ in range(perms):
        rng.shuffle(pool)
        if _abs_median(pool[:nl]) / _abs_median(pool[nl:]) >= t:
            hits += 1
    return (1 + hits) / (1 + perms)


def judge(loaded, opening, closing, *, seed, draws, perms):
    """{candidate: failed} for one loaded A/A series against the session's two idle series."""
    wl = boot_width(loaded, seed=f'{seed} L', draws=draws)
    wo = boot_width(opening, seed=f'{seed} O', draws=draws)
    wc = boot_width(closing, seed=f'{seed} C', draws=draws)
    wp = boot_width(opening + closing, seed=f'{seed} P', draws=draws, k=len(loaded))
    p = scale_pvalue(loaded, opening + closing, perms=perms, seed=f'{seed} B')
    return dict(A0=wl > K * wo, A1=wl > K * wp, A2=wl > K * max(wo, wc), B=p <= UNIT_ALPHA,
                C=wl / 2 > HALF_BOUND), dict(wl=wl, wo=wo, wp=wp)


# Data -------------------------------------------------------------------------------------------
def idle_series(recs):
    """{(session, cell, num, den): {'open': (slot, [...]), 'close': (slot, [...])}} for every W0 pair
    series, the A/A pair and the A/B pairs.

    The ratios keep calib.pairs' order (repetitions sorted as strings), which is the order #1107's
    summarizer bootstrapped them in; a bootstrap's draws depend on it."""
    refs = json.loads((CAL / 'references.json').read_text())
    by = defaultdict(list)
    for p in calib.pairs(calib.select(recs, 'raw', refs)):
        if p['workload'] == 'W0':
            by[(p['session'], p['slot'], p['cell'], p['num'], p['den'])].append(p['ratio'])
    out = defaultdict(dict)
    for (s, slot, cell, num, den), v in by.items():
        out[(s, cell, num, den)]['open' if slot == 0 else 'close'] = (slot, v)
    return dict(out)


def is_aa(num):
    return num in calib.AA.values()


def is_held_out(cell):
    return next(c.cohort for c in calib.CELLS if c.name == cell) == 'held-out'


def workers(cell):
    return next(c.workers for c in calib.CELLS if c.name == cell)


def observed(series, *, perms):
    """Closing W0 judged as loaded against the opening W0, with #1107's own seeds for the widths."""
    rows = []
    for (s, cell, num, den), v in sorted(series.items()):
        (_, op), (cslot, cl) = v['open'], v['close']
        wo = boot_width(op, seed=f'{s} idle {cell} {num}/{den}')
        wc = boot_width(cl, seed=f'{s} W0 {cslot} {cell} {num}/{den}')
        p = scale_pvalue(cl, op, perms=perms, seed=f'{s} {cell} {num}/{den} observed')
        rows.append(dict(session=s, cell=cell, pair=f'{num}/{den}', aa=is_aa(num), held_out=is_held_out(cell),
                         workers=workers(cell), w_open=wo, w_close=wc, ratio=wc / wo, p=p,
                         A0=wc > K * wo, A0_reversed=wo > K * wc, B=p <= UNIT_ALPHA, B05=p <= 0.05,
                         C_open=wo / 2 > HALF_BOUND, C_close=wc / 2 > HALF_BOUND))
    return rows


def inflate(xs, centre, g):
    """xs with its log-dispersion about `centre` (a log) multiplied by g: a synthetic load that widens the A/A
    distribution without moving its centre. Used only to measure the candidates' power."""
    return [math.exp(centre + g * (math.log(x) - centre)) for x in xs]


def _simulate_unit(args):
    key, pool, sims, draws, perms = args
    s, cell, num, den = key
    rng = random.Random(bs._seed(f'1180 {s} {cell} {num}/{den}'))
    n = len(pool) // 2
    centre = statistics.median(math.log(x) for x in pool)
    fails, ratios, power = [], [], {f: [] for f in INFLATION}
    for t in range(sims):
        op, cl = rng.choices(pool, k=n), rng.choices(pool, k=n)
        trial = []
        for w in range(LOADED_BLOCKS):
            f, wd = judge(rng.choices(pool, k=n), op, cl, seed=f'{s} {cell} {t} {w}', draws=draws, perms=perms)
            trial.append(f)
            ratios.append((wd['wl'] / wd['wo'], wd['wl'] / wd['wp'], wd['wl'] / 2))
        fails.append(trial)
        for g in INFLATION:
            loaded = inflate(rng.choices(pool, k=n), centre, g)
            power[g].append(judge(loaded, op, cl, seed=f'{s} {cell} {t} x{g}', draws=draws, perms=perms)[0])
    return key, fails, ratios, power


def simulate(series, *, sims, draws, perms, jobs):
    """Resampled idle-vs-idle trials on every A/A cell-session; see the module docstring."""
    tasks = [(k, v['open'][1] + v['close'][1], sims, draws, perms) for k, v in sorted(series.items()) if is_aa(k[2])]
    if jobs > 1:
        with Pool(jobs) as p:
            res = p.map(_simulate_unit, tasks)
    else:
        res = [_simulate_unit(t) for t in tasks]
    return {k: dict(fails=f, ratios=r, power=pw) for k, f, r, pw in res}


def aggregate(fails_by_unit, candidates=CANDIDATES):
    """Per-unit, per-workload and false-no-go rates from {unit: [trial][block]{cand: failed}}.

    Units are independent given the null, so trial t of every unit is one simulated campaign: block w
    of trial t is workload w, which fails when any unit fails it."""
    units = list(fails_by_unit)
    sims = len(next(iter(fails_by_unit.values())))
    out = {}
    for c in candidates:
        unit = sum(f[t][w][c] for u in units for f in [fails_by_unit[u]] for t in range(sims)
                   for w in range(LOADED_BLOCKS)) / (len(units) * sims * LOADED_BLOCKS)
        wl_fail = [[any(fails_by_unit[u][t][w][c] for u in units) for w in range(LOADED_BLOCKS)] for t in range(sims)]
        out[c] = dict(unit=unit,
                      workload=sum(map(sum, wl_fail)) / (sims * LOADED_BLOCKS),
                      no_go=sum(all(row) for row in wl_fail) / sims)
    return out


def quantile(xs, q):
    xs = sorted(xs)
    return xs[min(len(xs) - 1, int(q * len(xs)))]


def summarize(raw, sims):
    """The resampled figures from simulate()'s output: rates, the multiple k a ratio rule would need,
    the half-width bound's sensitivity, and power against synthetic inflation (held-out units)."""
    ho = {k: v for k, v in raw.items() if is_held_out(k[1])}
    ratios = [r for v in ho.values() for r in v['ratios']]
    qs = (1 - UNIT_ALPHA, 0.95, 0.99)
    half = {}
    for b in HALF_SENSITIVITY:
        per = {k: [[{'C': r[2] > b} for r in v['ratios'][t * LOADED_BLOCKS:(t + 1) * LOADED_BLOCKS]]
                   for t in range(sims)] for k, v in ho.items()}
        agg = aggregate(per, ('C',))['C']
        half[f'{b:.4f}'] = [agg['unit'], agg['workload']]
    power = {f'{g}': {c: sum(f[c] for v in ho.values() for f in v['power'][g]) / (len(ho) * sims) for c in CANDIDATES}
             for g in INFLATION}
    return dict(held_out=aggregate({k: v['fails'] for k, v in ho.items()}),
                all=aggregate({k: v['fails'] for k, v in raw.items()}),
                k=dict(open=[quantile([r[0] for r in ratios], q) for q in qs],
                       pooled=[quantile([r[1] for r in ratios], q) for q in qs]),
                half=half, power=power)


# Report -----------------------------------------------------------------------------------------
def tables(obs, sim, meta):
    aa = [r for r in obs if r['aa']]
    ho = [r for r in aa if r['held_out']]
    allp = obs

    def cnt(rows, k):
        return f"{sum(r[k] for r in rows)} / {len(rows)}"

    lines = [
        '# #1180: idle-vs-idle false failures of A/A width criteria',
        '',
        f"Generated by `research/1180-aa-width/analyze.py` from #1107's retained records "
        f"(`research/concurrent-calibration/data/`, binaries at `C` = `{calib.C}`). "
        f"Resampling: {meta['sims']} trials per cell-session, {meta['draws']} bootstrap draws, "
        f"{meta['perms']} permutations. Šidák per-unit α = {UNIT_ALPHA:.5f} "
        f"(5% per workload over {HELD_OUT_UNITS} units). Sense check only: these data do not decide (#1180).",
        '',
        '## Observed: closing W0 judged against opening W0',
        '',
        '| Candidate | Held-out A/A (14) | All A/A (22) | All idle pair series, A/A and A/B |',
        '|---|---|---|---|',
        f"| A0 closing ≤ 1.5 × opening | {cnt(ho, 'A0')} | {cnt(aa, 'A0')} | {cnt(allp, 'A0')} |",
        f"| A0 reversed (opening ≤ 1.5 × closing) | {cnt(ho, 'A0_reversed')} | {cnt(aa, 'A0_reversed')} | {cnt(allp, 'A0_reversed')} |",
        f"| B scale permutation, p ≤ {UNIT_ALPHA:.4f} | {cnt(ho, 'B')} | {cnt(aa, 'B')} | {cnt(allp, 'B')} |",
        f"| B at p ≤ 0.05 (calibration of the test) | {cnt(ho, 'B05')} | {cnt(aa, 'B05')} | {cnt(allp, 'B05')} |",
        f"| C half-width ≤ {HALF_BOUND}, closing W0 | {cnt(ho, 'C_close')} | {cnt(aa, 'C_close')} | {cnt(allp, 'C_close')} |",
        f"| C half-width ≤ {HALF_BOUND}, opening W0 | {cnt(ho, 'C_open')} | {cnt(aa, 'C_open')} | {cnt(allp, 'C_open')} |",
        '',
        'A1 and A2 need both W0s as the reference, so they leave no idle block to judge here; they are',
        'checked only by resampling.',
        '',
        '| Session | Cell | Workers | Pair | Opening width | Closing width | Ratio | B p | A0 fails |',
        '|---|---|---|---|---|---|---|---|---|',
    ]
    for r in aa:
        lines.append(f"| {r['session']} | {r['cell']} | {r['workers']} | {r['pair']} | {r['w_open']:.4f} | "
                     f"{r['w_close']:.4f} | {r['ratio']:.2f} | {r['p']:.4f} | {'**yes**' if r['A0'] else 'no'} |")
    lines += [
        '',
        '## Resampled: false-failure rates under an idle null',
        '',
        '| Candidate | Per unit | Per workload (any of 14 units) | False no-go (all 7 workloads fail) |',
        '|---|---|---|---|',
    ]
    for c in CANDIDATES:
        a = sim['held_out'][c]
        lines.append(f"| {c}: {NAMES[c]} | {a['unit']:.3f} | {a['workload']:.3f} | {a['no_go']:.3f} |")
    lines += [
        '',
        f"Per unit over all 22 A/A cell-sessions (calibration included): "
        + ', '.join(f"{c} {sim['all'][c]['unit']:.3f}" for c in CANDIDATES) + '.',
        '',
        '### What a fixed multiple would have to be',
        '',
        f"The multiple k at which a width-ratio rule fails one held-out unit in {1 / UNIT_ALPHA:.0f} "
        f"(per-unit α = {UNIT_ALPHA:.5f}), from the resampled ratios pooled over the held-out units:",
        '',
        '| Reference | k at 1 − α | k at 0.95 | k at 0.99 |',
        '|---|---|---|---|',
        f"| opening W0 (A0) | {sim['k']['open'][0]:.2f} | {sim['k']['open'][1]:.2f} | {sim['k']['open'][2]:.2f} |",
        f"| pooled W0s (A1) | {sim['k']['pooled'][0]:.2f} | {sim['k']['pooled'][1]:.2f} | {sim['k']['pooled'][2]:.2f} |",
        '',
        '### Absolute half-width bound: sensitivity',
        '',
        '| Bound | Per unit, held-out | Per workload |',
        '|---|---|---|',
    ]
    for b, (u, w) in sim['half'].items():
        lines.append(f"| {b} | {u:.4f} | {w:.3f} |")
    lines += [
        '',
        '### Power against synthetic inflation',
        '',
        'Per held-out unit, the fraction of trials in which a loaded block whose log-dispersion is g times',
        "idle's (centre unchanged) fails the candidate. Synthetic: #1107's loaded blocks are not used.",
        '',
        '| Candidate | ' + ' | '.join(f'g = {g}' for g in sim['power']) + ' |',
        '|---|' + '---|' * len(sim['power']),
    ]
    for c in CANDIDATES:
        lines.append(f'| {c} | ' + ' | '.join(f"{sim['power'][g][c]:.3f}" for g in sim['power']) + ' |')
    return '\n'.join(lines) + '\n'


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument('--sims', type=int, default=200)
    ap.add_argument('--draws', type=int, default=2000)
    ap.add_argument('--perms', type=int, default=1000)
    ap.add_argument('--observed-perms', type=int, default=20000)
    ap.add_argument('--jobs', type=int, default=1)
    ap.add_argument('--json', type=Path, required=True)
    ap.add_argument('--out', type=Path, required=True)
    a = ap.parse_args(argv)
    if 1 / (1 + min(a.perms, a.observed_perms)) > UNIT_ALPHA:
        ap.error(f'with fewer than {math.ceil(1 / UNIT_ALPHA) - 1} permutations no p-value can reach α = {UNIT_ALPHA:.5f}')
    recs =read(sorted((CAL / 'data').glob('s*/records-*.jsonl.gz')))
    series = idle_series(recs)
    obs = observed(series, perms=a.observed_perms)
    raw = simulate(series, sims=a.sims, draws=a.draws, perms=a.perms, jobs=a.jobs)
    sim = summarize(raw, a.sims)
    meta = dict(sims=a.sims, draws=a.draws, perms=a.perms, observed_perms=a.observed_perms, unit_alpha=UNIT_ALPHA,
                C=calib.C, records=sorted(p.name for p in (CAL / 'data').glob('s*/records-*.jsonl.gz')))
    a.json.write_text(json.dumps(dict(meta=meta, observed=obs, simulated=sim), indent=1, sort_keys=True) + '\n')
    a.out.write_text(tables(obs, sim, meta))
    print(a.out)


if __name__ == '__main__':
    main()
