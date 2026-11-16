#!/usr/bin/env python3
"""#834: tables for docs/research/m29-baseline-cost-model.md from the retained campaign files.

    python3 research/m29-baseline/summarize.py research/m29-baseline > research/m29-baseline/tables.md

Medians with [min, max]. Ratios are formed per repetition from runs adjacent in the same rotation
and then their median is taken, so a load drift between repetitions cancels (ratios survive load,
absolutes do not). Nothing is clock-normalized.
"""
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path
import statistics
import sys

ROOT = Path(__file__).resolve().parents[2]
TARGETS = ('mq10-32003', 'mq10-m31', 'eco12-wide64', 'mq11-goldilocks')
WORKERS = (1, 4, 8, 16)
WIDE = {'eco12-wide64': ('wide64', 'eco-12'), 'mq11-goldilocks': ('goldilocks', 'mq-random-11')}
MQ10 = {'mq10-32003': '32003', 'mq10-m31': '2147483647'}


def jsonl(path):
    return [json.loads(l) for l in path.read_text().splitlines() if l.strip()] if path.exists() else []


def med(xs):
    xs = [x for x in xs if x is not None]
    return statistics.median(xs) if xs else None


def rng(xs, scale=1e6, fmt='{:.1f}'):
    xs = [x for x in xs if x is not None]
    if not xs:
        return '—'
    return f"{fmt.format(statistics.median(xs) / scale)} [{fmt.format(min(xs) / scale)}, {fmt.format(max(xs) / scale)}]"


def ok(r):
    return r['report'] is not None and r['report']['status'] == 'complete'


def by(records, **keys):
    return [r for r in records if all(r[k] == v for k, v in keys.items())]


def stat(r, key):
    s = r['report']['statistics']
    for part in key.split('.'):
        s = s[part]
    return s


def curve(walls, out):
    out.append('## Worker curves (process wall, stage clocks off)\n')
    out.append('| Target | 1 worker ms | 4 workers ms | 8 workers ms | 16 workers ms | 16w speedup | 16w clock MHz | load at start |')
    out.append('|---|---:|---:|---:|---:|---:|---:|---|')
    for t in TARGETS:
        cells, speed = [], []
        for w in WORKERS:
            rows = by(walls, target=t, workers=w)
            done = [r['process_wall_ns'] for r in rows if ok(r)]
            stopped = [r for r in rows if not ok(r)]
            cell = rng(done) if done else '—'
            if stopped:
                cell += f" ({len(stopped)} stopped: {stopped[0]['report']['status'] if stopped[0]['report'] else stopped[0]['rc']})"
            cells.append(cell)
        for rep in sorted({r['rep'] for r in walls}):
            one = [r for r in by(walls, target=t, workers=1, rep=rep) if ok(r)]
            six = [r for r in by(walls, target=t, workers=16, rep=rep) if ok(r)]
            if one and six:
                speed.append(one[0]['process_wall_ns'] / six[0]['process_wall_ns'])
        clocks = [r['freq']['mean_khz'] for r in by(walls, target=t, workers=16) if r.get('freq')]
        loads = [r['before'].get('load1') for r in by(walls, target=t)]
        loads = [l for l in loads if l is not None]
        out.append(f"| {t} | {' | '.join(cells)} | {f'{med(speed):.2f}x' if speed else '—'} | "
                   f"{f'{med(clocks) / 1e3:.0f}' if clocks else '—'} | {min(loads):.2f}–{max(loads):.2f} |")
    out.append('')


STAGES = ('symbolic_ns', 'construction_ns', 'forward_ns', 'backward_ns', 'extraction_ns', 'interreduction_ns', 'other_ns')


def stages(records, out):
    out.append('## Stage attribution (stage clocks on; ms, median of the repetitions; share of the F4 total)\n')
    for t in TARGETS:
        out.append(f'### {t}\n')
        out.append('| Workers | F4 total | symbolic | construction | forward elim | backward/finishing | extraction | interreduction | other | serial share | process wall |')
        out.append('|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|')
        for w in WORKERS:
            rows = [r for r in by(records, target=t, workers=w) if ok(r)]
            if not rows:
                out.append(f'| {w} | ' + ' | '.join(['—'] * 10) + ' |')
                continue
            total = med([stat(r, 'total_ns') for r in rows])
            cells = []
            for s in STAGES:
                v = med([stat(r, s) for r in rows])
                cells.append(f'{v / 1e6:.1f} ({100 * v / total:.0f}%)')
            serial = med([1 - stat(r, 'forward_ns') / stat(r, 'total_ns') for r in rows])
            out.append(f"| {w} | {total / 1e6:.1f} | {' | '.join(cells)} | {100 * serial:.0f}% | "
                       f"{med([r['process_wall_ns'] for r in rows]) / 1e6:.1f} |")
        out.append('')


COUNTERS = ('batches', 'pairs_reduced', 'pair_multiples_removed', 'reducer_rows', 'max_matrix_rows',
            'max_matrix_columns', 'total_initial_nonzeros', 'total_final_nonzeros', 'max_live_nonzeros',
            'live_entry_requirement', 'max_estimated_bytes', 'row_operations', 'candidate_reduction.targets',
            'candidate_reduction.coefficient_products', 'candidate_reduction.reserved_entries',
            'parallel_forward.batches', 'parallel_forward.max_workers', 'parallel_forward.lost_publications',
            'parallel_forward.reserved_entries', 'parallel_forward.workspace_bytes', 'interreduction_elements')


def counters(records, out):
    out.append('## Work and memory counters (one stage-clocked run per cell; counters are deterministic at one worker)\n')
    head = '| Counter | ' + ' | '.join(f'{t} 1w | {t} 16w' for t in TARGETS) + ' |'
    out.append(head)
    out.append('|---|' + '---:|' * (2 * len(TARGETS)))
    pick = {}
    for t in TARGETS:
        for w in (1, 16):
            rows = [r for r in by(records, target=t, workers=w) if ok(r)]
            pick[(t, w)] = rows[0] if rows else None
    for c in COUNTERS:
        cells = []
        for t in TARGETS:
            for w in (1, 16):
                r = pick[(t, w)]
                cells.append(f'{stat(r, c):,}' if r else '—')
        out.append(f"| {c} | {' | '.join(cells)} |")
    cells = []
    for t in TARGETS:
        for w in (1, 16):
            rows = [r for r in by(records, target=t, workers=w) if ok(r)]
            cells.append(f"{med([r['report']['peak_rss_bytes'] for r in rows]) / 2**20:.0f}" if rows else '—')
    out.append(f"| peak RSS MiB (median) | {' | '.join(cells)} |")
    out.append('')


def census(records, out):
    out.append('## Serial entry-operation census (`research-work`, one worker)\n')
    out.append('| Target | batches | matrix rows (sum / max) | columns max | fill (entries / rows×cols, weighted) | forward products | inherited-pivot products | discovered-pivot products | discovered share | backward products | reducer-target ops | pair-target ops |')
    out.append('|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|')
    for t in TARGETS:
        work = [r for r in by(records, target=t, arm='work') if ok(r)]
        disc = [r for r in by(records, target=t, arm='discovery') if ok(r)]
        if not work:
            out.append(f'| {t} | ' + ' | '.join(['—'] * 11) + ' |')
            continue
        w = work[0]['report']['work']
        b = w['batches']
        rows = sum(x['rows'] for x in b)
        cells_area = sum(x['rows'] * x['columns'] for x in b)
        entries = sum(x['initial_entries'] for x in b)
        d = disc[0]['report']['work'] if disc else None
        inh = d['inherited_products'] if d else None
        dis = d['discovered_products'] if d else None
        share = f'{100 * dis / (inh + dis):.1f}%' if d and inh + dis else '—'
        out.append(f"| {t} | {len(b)} | {rows:,} / {max(x['rows'] for x in b):,} | {max(x['columns'] for x in b):,} | "
                   f"{100 * entries / cells_area:.2f}% | {w['forward']['coefficient_products']:,} | "
                   f"{f'{inh:,}' if d else '—'} | {f'{dis:,}' if d else '—'} | {share} | "
                   f"{w['backward']['coefficient_products']:,} | "
                   f"{w['forward']['reducer_target_operations'] + w['backward']['reducer_target_operations']:,} | "
                   f"{w['forward']['pair_target_operations'] + w['backward']['pair_target_operations']:,} |")
    out.append('')


def ab831(records, out):
    out.append('## #831 pair-multiple dedup, measured at this commit (process wall; Distinct is the default)\n')
    out.append('| Target | Workers | Every ms | Distinct ms | Distinct / Every (paired median) | pair halves removed | peak RSS Distinct / Every |')
    out.append('|---|---:|---:|---:|---:|---:|---:|')
    for t in TARGETS:
        for w in (1, 16):
            rows = by(records, target=t, workers=w)
            e = [r for r in rows if r['arm'] == 'every' and ok(r)]
            d = [r for r in rows if r['arm'] == 'distinct' and ok(r)]
            ratios = []
            for rep in sorted({r['rep'] for r in rows}):
                er = [r for r in e if r['rep'] == rep]
                dr = [r for r in d if r['rep'] == rep]
                if er and dr:
                    ratios.append(dr[0]['process_wall_ns'] / er[0]['process_wall_ns'])
            removed = stat(d[0], 'pair_multiples_removed') if d else None
            rss = (med([r['report']['peak_rss_bytes'] for r in d]) / med([r['report']['peak_rss_bytes'] for r in e])
                   if d and e else None)
            out.append(f"| {t} | {w} | {rng([r['process_wall_ns'] for r in e])} | {rng([r['process_wall_ns'] for r in d])} | "
                       f"{f'{med(ratios):.3f}x (n={len(ratios)})' if ratios else '—'} | "
                       f"{f'{removed:,}' if removed is not None else '—'} | {f'{rss:.3f}x' if rss else '—'} |")
    out.append('')


def scaling_module():
    spec = importlib.util.spec_from_file_location('scaling', ROOT / 'tools/external/comparand-scaling.py')
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m


def mq10(directory, walls, out):
    path = directory / 'mq10.json.gz'
    if not path.exists():
        out.append('## MQ10 comparands\n\nnot measured\n')
        return
    cohort = scaling_module().load_cohort(path)
    out.append('## MQ10 against the comparands (comparand-scaling.py, fresh process, I/O included)\n')
    out.append('| Field | Engine | 1 worker ms | 4 workers ms | 8 workers ms | 16 workers ms | statuses |')
    out.append('|---|---|---:|---:|---:|---:|---|')
    groups = {}
    for a in cohort['attempts']:
        groups.setdefault((str(a['field']), a['engine'], a['workers']), []).append(a)
    for field in ('32003', '2147483647'):
        for engine in ('zeebra', 'msolve', 'groebner-rs', 'grobx'):
            cells, statuses = [], set()
            for w in WORKERS:
                rows = groups.get((field, engine, w), [])
                statuses |= {a['status'] for a in rows}
                done = [a['process_wall_ns'] for a in rows if a['status'] in ('verified', 'complete') and a.get('process_wall_ns')]
                cells.append(rng(done) + (f' n={len(done)}' if done else ''))
            out.append(f"| {field} | {engine} | {' | '.join(cells)} | {', '.join(sorted(statuses))} |")
    out.append('')
    out.append('| Field | Zeebra 16w ms | best exact msolve ≤16 ms (workers) | Zeebra / msolve | Zeebra time needed for ≤1.5x |')
    out.append('|---|---:|---:|---:|---:|')
    for field in ('32003', '2147483647'):
        z = med([a['process_wall_ns'] for a in groups.get((field, 'zeebra', 16), []) if a['status'] in ('verified', 'complete')])
        best = min(((med([a['process_wall_ns'] for a in groups.get((field, 'msolve', w), []) if a['status'] in ('verified', 'complete')]), w)
                     for w in WORKERS if groups.get((field, 'msolve', w))), key=lambda x: x[0] or 1e30, default=(None, None))
        if z and best[0]:
            out.append(f'| {field} | {z / 1e6:.1f} | {best[0] / 1e6:.1f} ({best[1]}) | {z / best[0]:.2f}x | ≤{1.5 * best[0] / 1e6:.1f} |')
    out.append('')


def wide(directory, walls, out):
    out.append('## Wide-field targets against grobx and groebner-rs (wide-corpus.py, one worker, three passes)\n')
    out.append('| Target | engine | process wall ms (n) | basis agrees with Zeebra |')
    out.append('|---|---|---:|---|')
    best = {}
    for t, (field, name) in WIDE.items():
        zsha = {r['report']['basis_sha256'] for r in by(walls, target=t) if ok(r)}
        for engine in ('grobx', 'groebner-rs'):
            walls_e, agree = [], set()
            for path in sorted(directory.glob(f'wide-{field}-{name}-pass*.json.gz')):
                cohort = json.loads(gzip.decompress(path.read_bytes()))
                for a in cohort['attempts']:
                    rep = a.get('report') or {}
                    if a['engine'] == engine and rep.get('status') == 'complete':
                        walls_e.append(rep['solver_process_wall_ns'])
                        basis = rep.get('basis')
                        if isinstance(basis, list):
                            agree.add(hashlib.sha256('\n'.join(sorted(basis)).encode()).hexdigest() in zsha)
            if walls_e:
                best.setdefault(t, []).append((med(walls_e), engine))
            out.append(f"| {t} | {engine} | {rng(walls_e)} (n={len(walls_e)}) | "
                       f"{'yes' if agree == {True} else 'no' if False in agree else 'unchecked'} |")
    out.append('')
    out.append('| Target | Zeebra 16w ms | best comparand ms (engine) | Zeebra / best | Zeebra time needed for a 10% lead |')
    out.append('|---|---:|---:|---:|---:|')
    for t in WIDE:
        z = med([r['process_wall_ns'] for r in by(walls, target=t, workers=16) if ok(r)])
        if z and t in best:
            b, e = min(best[t])
            out.append(f'| {t} | {z / 1e6:.0f} | {b / 1e6:.0f} ({e}) | {z / b:.2f}x | ≤{0.9 * b / 1e6:.0f} |')
    out.append('')


def agreement(all_records, out):
    out.append('## Basis identity across every Zeebra run\n')
    out.append('| Target | complete runs | distinct basis SHA-256 | basis elements |')
    out.append('|---|---:|---:|---:|')
    for t in TARGETS:
        rows = [r for r in all_records if r['target'] == t and ok(r)]
        shas = {r['report']['basis_sha256'] for r in rows}
        elems = {r['report']['basis_elements'] for r in rows}
        out.append(f"| {t} | {len(rows)} | {len(shas)} | {', '.join(map(str, sorted(elems)))} |")
    out.append('')


def main():
    directory = Path(sys.argv[1])
    walls, stg, ab, cen = (jsonl(directory / f'{s}.jsonl') for s in ('walls', 'stages', 'ab831', 'census'))
    out = [f'<!-- generated by research/m29-baseline/summarize.py; do not edit -->\n']
    curve(walls, out)
    mq10(directory, walls, out)
    wide(directory, walls, out)
    stages(stg, out)
    counters(stg, out)
    census(cen, out)
    ab831(ab, out)
    agreement(walls + stg + ab + cen, out)
    print('\n'.join(out))


if __name__ == '__main__':
    main()
