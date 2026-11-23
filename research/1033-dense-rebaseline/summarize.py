#!/usr/bin/env python3
"""#1033's gate from committed files: records-<job>.jsonl.gz and density-*.json -> tables.md.

    summarize.py            # writes tables.md beside this script and prints the verdict

The metrics and rule are the pre-declaration's as amended by owner decisions 1 and 2 (#1033):
best configuration = lowest-median Zeebra arm over {entry, f4} x {1, 4, 16} w (sigf4 arms mirror
entry and are attribution only); F = elimination share of process wall on it; D = span-density
>= 50% product share on its engine; R = median Zeebra-best(1 w) / median grobx(1 w), each side
resampled independently (`tools/bench_stats.independent_ratio`, the Zeebra-vs-competitor rule).
Censored attempts count as `> cap` and are never medians of times.
"""
import gzip
import json
import statistics
import sys
from collections import defaultdict
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[1] / 'tools'))
import bench_stats  # noqa: E402

ROWS = {'n18': ('mq-dense-18-s18', 180), 'n20': ('mq-dense-20-s20', 900)}
# Attribution only (dev mode; decides nothing): (field, name, cap s).
ATTRIBUTION = [('gf31', 'mq-dense-12-s12', 180), ('gf31', 'mq-dense-15-s15', 180),
               ('gf31', 'mq-dense-unplanted-15-s15', 180), ('gf32003', 'mq-dense-12-s12', 180),
               ('gf32003', 'mq-dense-15-s15', 180), ('gf32003', 'mq-dense-18-s18', 180),
               ('gf32003', 'mq-dense-20-s20', 900), ('gf31', 'mq-random-10-s10', 180),
               ('gf31', 'mq-random-11-s11', 180), ('m31', 'mq-random-10', 180), ('wide64', 'mq-random-10-s10', 180)]
DECIDING_ARMS = ('entry', 'f4')
OPEN_F, OPEN_D, OPEN_R = 0.60, 0.50, 1.5
DEFER_F, DEFER_R = 0.40, 1.2


def load_records():
    """Attempts from every job whose session is not void; a void session (bench_stats.session_void,
    over 20% contaminated) is discarded whole, and its re-run replaces it."""
    recs, void = [], []
    for path in sorted(HERE.glob('records-*.jsonl.gz')):
        meta = json.loads(Path(str(path).replace('.jsonl.gz', '.session.json')).read_text())
        if (meta['stop'].get('contamination') or {}).get('void'):
            void.append(f'{meta["job"]["context"]["track"]} ({meta["job"]["job_id"]})')
            continue
        recs += [json.loads(line) for line in gzip.decompress(path.read_bytes()).decode().splitlines()]
    return recs, void


def complete(r):
    """A clean attempt that returned a complete basis."""
    if r['status'] != 'ok' or r['contaminated']:
        return False
    if r['arm'].startswith('grobx'):
        return r.get('basis_m33') is not None
    return r.get('zeebra_status') == 'complete' and r.get('basis_m33') is not None


def cells(recs, row, field='gf31'):
    out = defaultdict(list)
    name = ROWS[row][0] if row in ROWS else row
    for r in recs:
        if r['name'] == name and r['field'] == field:
            out[r['arm'], r['workers']].append(r)
    return out


def summary(attempts, cap):
    """Contaminated attempts are excluded, not censored; a clean attempt that did not finish is censored."""
    clean = [a for a in attempts if not a['contaminated']]
    done = [a for a in clean if complete(a)]
    walls = [a['wall_ns'] / 1e9 for a in done]
    censored = len(clean) - len(done)
    return dict(n=len(clean), complete=len(done), censored=censored, excluded=len(attempts) - len(clean),
                median=statistics.median(walls) if walls and censored == 0 else None,
                text=(f'{statistics.median(walls):.2f} s' if walls and censored == 0
                      else f"> {cap} s ({censored} of {len(clean)} not complete)"))


def elimination_share(attempt, mirror):
    """F for one attempt: f4 stages, or the signature mirror's elimination over its own wall."""
    if attempt['arm'] == 'f4':
        return attempt['forward_ns'] / attempt['wall_ns']
    if mirror:
        return statistics.median(m['elimination_ns'] / m['wall_ns'] for m in mirror)
    return None


def density_share(row, engine):
    path = HERE / f'density-{engine}-{row}.json'
    if not path.exists():
        return None, 'not measured'
    d = json.loads(path.read_text())
    work = d['work']
    total = d['statistics'].get('coefficient_products') if engine == 'sigf4' else work['forward_products']
    coverage = work['traced_products'] / total if total else 0
    if coverage < 0.99:
        return None, f'trace covers {coverage:.3f} of products'
    return float(work['summary']['span_share_at_least'][1]), f'coverage {coverage:.4f}'


def attribution(recs):
    """Median wall per arm and worker count, with F4's forward share; dev mode, decides nothing."""
    lines = ['## Attribution rows (dev mode; decide nothing)', '',
             'Median process wall. f4 cells add the forward share of wall in brackets. A censored cell reads '
             '`> cap`; `x/y` counts clean complete attempts of clean attempts where they differ.', '',
             '| Row | grobx 1 w | entry 1 w | entry 4 w | entry 16 w | f4 1 w | f4 4 w | f4 16 w | entry 1 w / grobx | Digests agree |',
             '|---|---|---|---|---|---|---|---|---|---|']
    for field, name, cap in ATTRIBUTION:
        c = cells(recs, name, field)
        row = [f'{field}/{name}']
        meds = {}
        for arm, w in [('grobx155', 1), ('entry', 1), ('entry', 4), ('entry', 16), ('f4', 1), ('f4', 4), ('f4', 16)]:
            s = summary(c.get((arm, w), []), cap)
            meds[arm, w] = s['median']
            text = s['text'].split(' (')[0]
            if s['median'] is not None and arm == 'f4':
                done = [a for a in c[arm, w] if complete(a) and not a['contaminated']]
                text += f' [{statistics.median(a["forward_ns"] / a["wall_ns"] for a in done):.2f}]'
            if s['complete'] != s['n']:
                text += f' ({s["complete"]}/{s["n"]})'
            row.append(text)
        e, g = meds['entry', 1], meds['grobx155', 1]
        row.append(f'{e / g:.1f}' if e and g else '—')
        digests = {a.get('basis_m33') for att in c.values() for a in att if complete(a)}
        row.append('yes' if len(digests) == 1 else f'NO ({len(digests)})')
        lines.append('| ' + ' | '.join(row) + ' |')
    return lines + ['']


def main():
    recs, void = load_records()
    lines = ['# #1033 deciding read: generated by summarize.py from committed records', '']
    if void:
        lines += [f'Void sessions, excluded whole: {", ".join(void)}.', '']
    verdicts = {}
    for row, (name, cap) in ROWS.items():
        c = cells(recs, row)
        lines += [f'## {row}: gf31/{name} (cap {cap} s)', '',
                  '| Arm | Workers | Clean attempts | Excluded (contaminated) | Complete | Median wall | Max RSS MiB | Digests |', '|---|---|---|---|---|---|---|---|']
        for (arm, w), attempts in sorted(c.items()):
            s = summary(attempts, cap)
            rss = max(a['peak_rss_bytes'] or 0 for a in attempts) / 2**20
            digests = sorted({(a.get('basis_m33') or 'none')[:12] for a in attempts})
            lines.append(f'| {arm} | {w} | {s["n"]} | {s["excluded"]} | {s["complete"]} | {s["text"]} | {rss:.0f} | {", ".join(digests)} |')
        grobx = [a['wall_ns'] / 1e9 for a in c.get(('grobx155', 1), []) if complete(a)]
        candidates = {(arm, w): summary(att, cap) for (arm, w), att in c.items() if arm in DECIDING_ARMS}
        timed = {k: v['median'] for k, v in candidates.items() if v['median'] is not None}
        best = min(timed, key=timed.get) if timed else None
        best1 = min((k for k in timed if k[1] == 1), key=timed.get, default=None)
        mirror_arm = ('sig' if best and best[1] == 1 else 'sigclaim')
        mirror = [m for m in c.get((mirror_arm, best[1]), []) if complete(m)] if best else []
        best_done = [a for a in c.get(best, []) if complete(a)] if best else []
        f = None
        if best and best_done:
            shares = [elimination_share(a, mirror) for a in best_done]
            if all(s is not None for s in shares):
                f = statistics.median(shares)
            if best[0] == 'entry' and mirror:
                gap = statistics.median(m['wall_ns'] for m in mirror) / statistics.median(a['wall_ns'] for a in best_done)
                if not 0.9 <= gap <= 1.1:
                    f = None  # the mirror is not entry's route within 10% (amendment)
        engine = 'f4' if best and best[0] == 'f4' else 'sigf4'
        d, d_note = density_share(row, engine)
        d_f4, d_f4_note = density_share(row, 'f4')
        r = None
        if best1 and grobx:
            z = [a['wall_ns'] / 1e9 for a in c[best1] if complete(a)]
            r = bench_stats.independent_ratio(z, grobx, seed=f'1033-{row}')
        verdicts[row] = dict(best=best, best1=best1, f=f, d=d, r=r)
        fmt = lambda x: 'not measured' if x is None else f'{x:.3f}'
        lines += ['', f'- **Best configuration:** {best} ({timed.get(best, 0):.2f} s); best at 1 w: {best1}',
                  f'- **F** (elimination share of process wall, best configuration): {fmt(f)}',
                  f'- **D** (span ≥ 50% product share, {engine}): {fmt(d)} ({d_note}); F4 alongside: '
                  f'{fmt(d_f4)} ({d_f4_note})',
                  f'- **R** (best 1 w / grobx 1 w): ' + (f'{r.median:.2f} [{r.lo:.2f}, {r.hi:.2f}] (n = {r.n}, {r.n_ref})'
                                                         if r else 'not measured'), '']
    lines += attribution(recs)
    opens = all(v['f'] is not None and v['f'] >= OPEN_F and v['d'] is not None and v['d'] >= OPEN_D
                and v['r'] is not None and v['r'].median >= OPEN_R for v in verdicts.values())
    defers = any((v['f'] is not None and v['f'] < DEFER_F) or (v['r'] is not None and v['r'].median <= DEFER_R)
                 for v in verdicts.values())
    missing = [row for row, v in verdicts.items() if v['f'] is None or v['d'] is None or v['r'] is None]
    if defers:
        decision = 'DEFER #945'
    elif missing:
        decision = f'INCOMPLETE (no verdict: {", ".join(missing)} lacks F, D or R)'
    else:
        decision = 'OPEN #945' if opens else 'DEFER #945'
    lines += ['## Decision (Gate D-0)', '', f'**{decision}.** Open needs F >= {OPEN_F}, D >= {OPEN_D}, R >= {OPEN_R} '
              f'on both rows; defer on F < {DEFER_F} or R <= {DEFER_R} on either; anything between defers.', '']
    (HERE / 'tables.md').write_text('\n'.join(lines))
    print('\n'.join(lines))


if __name__ == '__main__':
    main()
