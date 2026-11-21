#!/usr/bin/env python3
"""#972: every table of `docs/research/m33-msolve-attribution.md`, from the committed records alone.

    summarize.py            # writes tables.md
    summarize.py --check    # exits 1 if tables.md is stale

Statistics are `tools/bench_stats.py`'s: Zeebra ÷ msolve is the independent bootstrap of §8.4, a
Zeebra ÷ Zeebra ratio (an instrument's overhead, a candidate's effect) is paired per repetition.
Every table uses all ok attempts; the session table gives the clock rule's verdict beside them.
"""
import argparse
import gzip
import json
import statistics
import sys
from collections import defaultdict
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import bench_contamination as bc  # noqa: E402
import bench_stats as bs  # noqa: E402

MS = 1e6
ROWS = [('m31', 'mq-random-10'), ('gf32003', 'mq-random-10'), ('m31', 'katsura-11')]
FIELD = {'m31': 'GF(2³¹−1)', 'gf32003': 'GF(32003)'}
WORKERS = [1, 4, 8, 16]
MQ, RD = '1df3100aa22a', 'b35504942e78'  # session job ids


def load():
    recs, sessions = [], []
    for path in sorted(HERE.glob('records-*.jsonl.gz')):
        recs += [json.loads(x) for x in gzip.decompress(path.read_bytes()).decode().splitlines()]
        sessions.append(json.loads(Path(str(path).replace('.jsonl.gz', '.session.json')).read_text()))
    counts = json.loads((HERE / 'msolve-counts.json').read_text())
    return recs, sessions, counts


def sel(recs, field, name, arm, w, job=None):
    return [r for r in recs if (r['field'], r['name'], r['arm'], r['workers']) == (field, name, arm, w)
            and r['status'] == 'ok' and (job is None or r['job'].startswith(job))]


def walls(rs, clean=False):
    return [r['wall_ns'] / MS for r in rs if not (clean and r['contaminated'])]


def med(v):
    return statistics.median(v) if v else None


def f(x, d=1):
    return '—' if x is None else f'{x:,.{d}f}'


def ci(c):
    return '—' if c is None else f'{c.median:.3f} [{c.lo:.3f}, {c.hi:.3f}]'


def stat(rs, key, sub='stages'):
    """Median of a Zeebra statistic over attempts (ns figures returned in ms)."""
    v = []
    for r in rs:
        s = (r.get('zeebra') or {}).get('statistics') or {}
        s = s.get(sub) if sub else s
        if s and s.get(key) is not None:
            v.append(s[key])
    if not v:
        return None
    m = statistics.median(v)
    return m / MS if key.endswith('_ns') else m


def ms_stat(rs, key, part='timings'):
    v = [r['msolve'][part][key] for r in rs if r.get('msolve') and key in r['msolve'][part]]
    return med(v)


def zeebra_route_arm(name, w):
    """The arm whose statistics describe what `entry` ran in this cell."""
    if w == 1:
        return 'sigf4'
    return 'f4stages' if name.startswith('mq') else 'sigf4claim'


def session_table(recs, sessions):
    out = ['## Sessions and the clock rule', '',
           '| Job | Session | Attempts | ok | bench-job (per cell) | one session median | per worker group | '
           'per arm and cell | Reasons |', '|---|---|---:|---:|---|---|---|---|---|']
    for s in sessions:
        job = s['job']['job_id']
        mine = [r for r in recs if r['job'] == job]
        judged = [r for r in mine if r.get('metrics')]
        c = (s['stop'] or {}).get('contamination') or {}
        alt = []
        for groups in (None, [r['workers'] for r in judged],
                       [f"{r['field']}/{r['name']}@{r['workers']}@{r['arm']}" for r in judged]):
            v = bc.session_verdict([r['metrics'] for r in judged], 'dev', groups)
            alt.append(f"{v['contaminated']}/{v['total']}{' void' if v['void'] else ''}")
        why = defaultdict(int)
        for r in mine:
            for x in r['reasons']:
                why[' '.join(x.split(' ')[:2])] += 1
        out.append(f"| `{job}` | {s['job']['context'].get('session')} | {len(mine)} | "
                   f"{sum(r['status'] == 'ok' for r in mine)} | {c.get('contaminated')}/{c.get('total')}"
                   f"{' **void**' if c.get('void') else ''} | {alt[0]} | {alt[1]} | {alt[2]} | "
                   f"{', '.join(f'{k} {v}' for k, v in sorted(why.items())) or '—'} |")
    return out + ['']


def scoreboard(recs):
    out = ['## Zeebra (entry, F0) ÷ msolve 0.11.0, this session', '',
           '| Row | w | msolve | entry | **entry ÷ msolve** | rule-clean only (n) | msolve anomalous | Verdict |',
           '|---|---:|---:|---:|---:|---|---|---|']
    for field, name in ROWS:
        by_w = {w: walls(sel(recs, field, name, 'msolve', w)) for w in WORKERS}
        for w in WORKERS:
            z, m = walls(sel(recs, field, name, 'entry', w)), by_w[w]
            if not z or not m:
                continue
            c = bs.independent_ratio(z, m, seed=f'{field}/{name}@{w}')
            zc, mc = walls(sel(recs, field, name, 'entry', w), True), walls(sel(recs, field, name, 'msolve', w), True)
            cc = bs.independent_ratio(zc, mc, seed=f'{field}/{name}@{w}') if zc and mc else None
            anom = bs.msolve_anomaly(by_w, w)
            v = bs.win_verdict(c, anomaly=anom, small=med(m) < 300)
            out.append(f'| {name} / {FIELD[field]} | {w} | {f(med(m))} | {f(med(z))} | **{ci(c)}** | '
                       f'{ci(cc)} ({len(zc)}, {len(mc)}) | {"yes" if anom else "no"} | {v.outcome} |')
    return out + ['']


def stage_table(recs):
    out = ['## Where the time goes, per stage (medians, ms)', '',
           'Zeebra from the arm that runs `entry`\'s route with stage clocks (`sigf4`/`sigf4claim` from the F0 '
           'binary; `f4stages` from this branch). msolve from `-v 2` (10 ms resolution). Overhead is the '
           'instrumented arm ÷ `entry`, paired per repetition.', '',
           '| Row | w | Zeebra arm | symbolic | construction | forward | backward | other elimination | '
           'interreduction | bookkeeping+rest | call | overhead ÷ entry |',
           '|---|---:|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|']
    msl = ['', '| Row | w | msolve select | symbolic prep. | update | convert | linear algebra | reduce gb | '
           'elapsed (-v 2) | process wall (plain arm) |', '|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|']
    for field, name in ROWS:
        for w in WORKERS:
            arm = zeebra_route_arm(name, w)
            rs = sel(recs, field, name, arm, w)
            if not rs:
                continue
            call = med([r['zeebra']['call_ns'] / MS for r in rs])
            ent = {r['rep']: r['wall_ns'] for r in sel(recs, field, name, 'entry', w)}
            mine = {r['rep']: r['wall_ns'] for r in rs}
            ov = bs.paired_ratio(bs.paired_ratios(mine, ent), seed=f'ov{field}{name}{w}') if ent else None
            if arm == 'f4stages':
                g = lambda k: stat(rs, k)  # noqa: E731
                rest = call - sum(g(k) or 0 for k in ('symbolic_ns', 'construction_ns', 'elimination_ns',
                                                      'extraction_ns', 'interreduction_ns'))
                out.append(f'| {name} / {FIELD[field]} | {w} | {arm} | {f(g("symbolic_ns"))} | '
                           f'{f(g("construction_ns"))} | {f(g("forward_ns"))} | {f(g("backward_ns"))} | '
                           f'{f(g("extraction_ns"))} (extraction) | {f(g("interreduction_ns"))} | {f(rest)} | '
                           f'{f(call)} | {ci(ov)} |')
            else:
                g = lambda k: stat(rs, k, None)  # noqa: E731
                out.append(f'| {name} / {FIELD[field]} | {w} | {arm} | {f(g("symbolic_ns"))} | — | '
                           f'{f(g("elimination_ns"))} (all elimination) | — | — | {f(g("interreduction_ns"))} | '
                           f'{f(g("bookkeeping_ns"))} | {f(call)} | {ci(ov)} |')
            v2 = sel(recs, field, name, 'msolve-v2', w)
            t = lambda k: (ms_stat(v2, k) or 0) * 1000  # noqa: E731
            msl.append(f'| {name} / {FIELD[field]} | {w} | {f(t("select"), 0)} | {f(t("symbolic prep."), 0)} | '
                       f'{f(t("update"), 0)} | {f(t("convert"), 0)} | {f(t("linear algebra"), 0)} | '
                       f'{f(t("reduce gb"), 0)} | {f(t("overall(elapsed)"), 0)} | '
                       f'{f(med(walls(sel(recs, field, name, "msolve", w))))} |')
    return out + msl + ['']


def work_table(recs, counts):
    out = ['## Work: coefficient products, row applications and matrices', '',
           'msolve counts are its exact sparse linear algebra (`msolve-count.py`): lower rows against pivots, '
           'new-pivot interreduction and the final basis reduction. Zeebra\'s conventional route counts its '
           'concurrent forward pass (`parallel_products`) and candidate finishing (`backward_products`); the '
           'signature route counts `coefficient_products` over all its batches.', '',
           '| Row | w | Zeebra route | Zeebra forward products | backward | row operations | products ÷ row op | '
           'msolve forward | msolve new-pivot + final | msolve applications | products ÷ app | '
           '**Zeebra ÷ msolve products** |', '|---|---:|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|']
    for field, name in ROWS:
        for w in WORKERS:
            arm = zeebra_route_arm(name, w)
            rs = sel(recs, field, name, arm, w)
            c = counts.get(f'{field}/{name}@{w}')
            if not rs or not c:
                continue
            mfwd, mrest = c['forward_products'], c['newpiv_products'] + c['final_products']
            mapps = c['forward_apps'] + c['newpiv_apps'] + c['final_apps']
            if arm.startswith('f4'):
                fwd, bwd, ops = stat(rs, 'parallel_products'), stat(rs, 'backward_products'), stat(rs, 'row_operations')
                tot = fwd + bwd
            else:
                fwd, bwd, ops = stat(rs, 'coefficient_products', None), None, None
                tot = fwd
            out.append(f'| {name} / {FIELD[field]} | {w} | {arm} | {f(fwd / 1e6)} M | '
                       f'{"—" if bwd is None else f(bwd / 1e6) + " M"} | {"—" if ops is None else f(ops / 1e6, 2) + " M"} | '
                       f'{"—" if ops is None else f(fwd / ops)} | {f(mfwd / 1e6)} M | {f(mrest / 1e6, 2)} M | '
                       f'{f(mapps / 1e6, 2)} M | {f(mfwd / c["forward_apps"])} | **{tot / (mfwd + mrest):.2f}** |')
    out += ['', '| Row | Zeebra largest matrix | Zeebra reducer rows (sum) | Zeebra zero rows | msolve largest matrix | '
            'msolve rows (sum) | msolve zero reductions | rounds (Zeebra, msolve) |', '|---|---|---:|---:|---|---:|---:|---|']
    for field, name in ROWS:
        if not name.startswith('mq'):
            continue
        rs = sel(recs, field, name, 'f4stages', 4)
        v2 = sel(recs, field, name, 'msolve-v2', 4)
        if not rs or not v2:
            continue
        st = rs[0]['zeebra']['statistics']
        rounds = v2[0]['msolve']['rounds']
        big = max(rounds, key=lambda r: r['rows'] * r['columns'])
        out.append(f'| {name} / {FIELD[field]} | {st["max_matrix_rows"]:,} × {st["max_matrix_columns"]:,} | '
                   f'{st["stages"]["reducer_rows"]:,} | {st["zero_rows"]:,} | {big["rows"]:,} × {big["columns"]:,} | '
                   f'{sum(r["rows"] for r in rounds):,} | {sum(r["zero"] for r in rounds):,} | '
                   f'{st["batches"]}, {len(rounds)} |')
    return out + ['']


def throughput_table(recs, counts):
    out = ['## Arithmetic throughput and scaling of the conventional route (MQ10, 4-16 workers)', '',
           'Per-thread cost is worker time ÷ products. msolve\'s is its linear-algebra elapsed × workers ÷ its '
           'products, an upper bound because it assumes every thread busy. Imbalance is the slowest worker ÷ the '
           'mean worker; utilization is busy time ÷ (workers × forward wall).', '',
           '| Row | w | forward | critical path | mean worker | imbalance | utilization | lock + publish | '
           'retry share | Zeebra ns/product/thread | msolve ns/product/thread (bound) | serial stages |',
           '|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|']
    for field, name in ROWS:
        if not name.startswith('mq'):
            continue
        for w in WORKERS[1:]:
            rs = sel(recs, field, name, 'f4stages', w)
            v2 = sel(recs, field, name, 'msolve-v2', w)
            c = counts.get(f'{field}/{name}@{w}')
            if not rs:
                continue
            g = lambda k: stat(rs, k)  # noqa: E731
            fwd, crit, busy, slots = g('forward_ns'), g('critical_ns'), g('busy_ns'), g('worker_slots')
            mean = busy / (slots / g('passes'))
            prods = g('parallel_products')
            la = ms_stat(v2, 'linear algebra')
            mprod = c['forward_products'] + c['newpiv_products'] + c['final_products']
            serial = sum(g(k) or 0 for k in ('symbolic_ns', 'construction_ns', 'extraction_ns', 'interreduction_ns'))
            out.append(f'| {name} / {FIELD[field]} | {w} | {f(fwd)} | {f(crit)} | {f(mean)} | {crit / mean:.2f} | '
                       f'{busy / (slots / g("passes") * fwd):.0%} | {f(g("scheduling_ns") + g("publication_ns"), 2)} | '
                       f'{g("retry_products") / prods:.1%} | {busy * MS / prods:.2f} | '
                       f'{"—" if not la else f"{la * 1e9 * w / mprod:.2f}"} | {f(serial)} |')
    return out + ['']


def candidate_table(recs, job, arms, title):
    out = [f'## {title}', '',
           'Each arm ÷ `f4stages` from the same session on this branch\'s binary, paired per repetition. The '
           'projection scales the `mq` session\'s `entry` attempts by that median and divides by its msolve.', '',
           '| Row | w | arm | f4stages | arm | **arm ÷ f4stages** | forward products (÷ f4stages) | backward products '
           '(÷) | symbolic (ms) | forward + backward (ms) | projected entry ÷ msolve |',
           '|---|---:|---|---:|---:|---:|---:|---:|---:|---:|---:|']
    for field, name in ROWS:
        if not name.startswith('mq'):
            continue
        for w in WORKERS[1:]:
            a = sel(recs, field, name, 'f4stages', w, job)
            for arm in arms:
                b = sel(recs, field, name, arm, w, job)
                if not a or not b:
                    continue
                ra = {r['rep']: r['wall_ns'] for r in a}
                rb = {r['rep']: r['wall_ns'] for r in b}
                c = bs.paired_ratio(bs.paired_ratios(rb, ra), seed=f'{arm}{field}{name}{w}')
                z = walls(sel(recs, field, name, 'entry', w, MQ))
                m = walls(sel(recs, field, name, 'msolve', w, MQ))
                proj = bs.independent_ratio([x * c.median for x in z], m, seed=f'p{arm}{field}{name}{w}')
                fb = (stat(b, 'forward_ns') or 0) + (stat(b, 'backward_ns') or 0)
                out.append(f'| {name} / {FIELD[field]} | {w} | {arm} | {f(med(walls(a)))} | {f(med(walls(b)))} | '
                           f'**{ci(c)}** | {stat(b, "parallel_products") / stat(a, "parallel_products"):.3f} | '
                           f'{stat(b, "backward_products") / stat(a, "backward_products"):.3f} | '
                           f'{f(stat(b, "symbolic_ns"))} | {f(fb)} | {ci(proj)} |')
    return out + ['']


def fl918_table(recs):
    out = ['## #918: the FL sweep against the D′ echelon, 16 workers, GF(32003)', '',
           '| Row | forward order wall | FL wall | FL ÷ forward | FL forward clock | sweep | D′ (renumber + echelon) | '
           '**D′ share of forward** | D′ share of call |', '|---|---:|---:|---:|---:|---:|---:|---:|---:|']
    for field, name in [('gf32003', 'katsura-11'), ('gf32003', 'mq-random-10'), ('gf32003', 'cyclic-8')]:
        a, b = sel(recs, field, name, 'forward', 16), sel(recs, field, name, 'fl', 16)
        if not a or not b:
            continue
        ra = {r['rep']: r['wall_ns'] for r in a}
        rb = {r['rep']: r['wall_ns'] for r in b}
        c = bs.paired_ratio(bs.paired_ratios(rb, ra), seed=f'918{name}')
        shares = [r['zeebra']['statistics']['stages']['fl_echelon_ns'] / r['zeebra']['statistics']['stages']['forward_ns']
                  for r in b]
        calls = [r['zeebra']['statistics']['stages']['fl_echelon_ns'] / r['zeebra']['call_ns'] for r in b]
        out.append(f'| {name} | {f(med(walls(a)))} | {f(med(walls(b)))} | {ci(c)} | {f(stat(b, "forward_ns"))} | '
                   f'{f(stat(b, "fl_sweep_ns"))} | {f(stat(b, "fl_echelon_ns"))} | **{med(shares):.1%}** '
                   f'[{min(shares):.1%}, {max(shares):.1%}] | {med(calls):.1%} |')
    return out + ['']


def render():
    recs, sessions, counts = load()
    lines = ['# #972 M33-M1 tables', '', 'Generated by `summarize.py` from `records-*.jsonl.gz` and '
             '`msolve-counts.json`; do not edit by hand.', '']
    for part in (session_table(recs, sessions), scoreboard(recs), stage_table(recs), work_table(recs, counts),
                 throughput_table(recs, counts),
                 candidate_table(recs, MQ, ['f4fl'], 'Candidate: the Faugère–Lachartre order (session `mq`)'),
                 candidate_table(recs, RD, ['f4fl', 'f4few', 'f4fewfl'],
                                 'Candidates: FL and the fewest-terms reducer rule (session `rd`)'),
                 fl918_table(recs)):
        lines += part
    return '\n'.join(lines)


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--check', action='store_true')
    args = p.parse_args()
    text = render()
    path = HERE / 'tables.md'
    if args.check:
        sys.exit(0 if path.exists() and path.read_text() == text else 1)
    path.write_text(text)
    print(path)


if __name__ == '__main__':
    main()
