#!/usr/bin/env python3
"""#974 M33-Q verdicts from `tools/bench-job` job directories (plan §§8.4, 11.6, 12, 13).

    summarize.py correctness JOB...                     # §12.1: digests, typed outcomes, threads
    summarize.py regression JOB... [--small JOB...]     # §12.2: paired F2 ÷ F0 wall and peak RSS
    summarize.py gate-d --gate-d --f2 SHA JOB...        # §13 Gate D: the held-out read, once

Each prints a Markdown table and exits 1 if any row fails. `gate-d` refuses unless both `--gate-d`
and `--f2` are given and match the jobs' manifests, and refuses a second read: it writes
`gate-d.md` beside this file and will not overwrite it. The raw table comes before any verdict, so
it can be posted on #965 before it is interpreted.
"""
import argparse
import importlib.machinery
import importlib.util
import json
import statistics
import sys
from collections import defaultdict
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
sys.path.insert(0, str(ROOT / 'tools/external'))
import attempt_journal as aj  # noqa: E402
import bench_stats as bs  # noqa: E402

WALL_BOUND, RSS_BOUND, RSS_EXPLAIN, FLOOR_NS = 1.05, 1.25, 1.10, 300 * 10**6
GATE_D = HERE / 'gate-d.md'


def _bench_job():
    loader = importlib.machinery.SourceFileLoader('bench_job', str(ROOT / 'tools/bench-job'))
    module = importlib.util.module_from_spec(importlib.util.spec_from_loader('bench_job', loader))
    loader.exec_module(module)
    return module


def attempts(job):
    """One record per attempt: the cell, the job status, contamination and the harness's report."""
    job = Path(job)
    state = aj.load(job / 'journal')
    manifest = json.loads((job / 'manifest.json').read_text())
    flagged = _bench_job()._flagged(state)
    out = []
    for a in state['attempts']:
        try:
            report = json.loads(a['stdout']) if a['status'] == 'ok' else {}
        except ValueError:
            report = {}
        version, _, engine = a['cell']['arm'].partition('-')
        out.append(dict(a['cell'], job=job.name, version=version, engine=engine, status=a['status'], report=report,
                        wall_ns=a['metadata']['process_wall_ns'],
                        rss=a['metadata'].get('observed_peak_rss_bytes'),
                        contaminated=a['metadata']['attempt_id'] in flagged, context=manifest['context']))
    return out


def correctness_failures(instance, records, reference):
    """Why one correctness row fails (plan §12.1), or [] when it passes."""
    order = instance.split('/')[0]
    why = []
    if not records:
        return ['no attempts']
    bad = sorted({r['status'] for r in records if r['status'] != 'ok'})
    if bad:
        why.append('attempts ' + ', '.join(bad))
    reports = [r for r in records if r['report']]
    inputs = {r['report'].get('digest') for r in reports}
    if len(inputs) > 1 or (reference and reference.get('input_digest') not in inputs | {None}):
        why.append('input digests differ')
    digests = {r['report']['basis_m33'] for r in reports if r['report'].get('status') == 'complete'}
    if len(digests) > 1:
        why.append(f'{len(digests)} basis digests')
    expected = (reference or {}).get('basis_m33')
    if digests and expected is None:
        why.append('no reference digest')
    elif digests and digests != {expected}:
        why.append('differs from the reference')
    outcome = defaultdict(set)
    for r in reports:
        status, engine = r['report'].get('status'), r['engine']
        if order == 'lex' and engine == 'entry' and status != 'refused':
            why.append(f'{r["version"]} entry under lex: {status}, not a typed refusal')
        # Owner decision 12 (#965): graded-lex entry may ship to F4 for any reason.
        if order == 'grlex' and engine == 'entry' and r['version'] == 'f2' \
                and not (r['report'].get('route') or '').startswith('Shipping('):
            why.append(f'f2 entry under graded-lex took {r["report"].get("route")}, not a Shipping route')
        team = r['report'].get('team_running_peak')
        if team is not None and team > r['workers']:
            why.append(f'{r["arm"]} at {r["workers"]} w: {team} threads running in one team')
        kind = status if status != 'stopped' else 'stopped ' + (r['report'].get('error') or '').split(' ')[0]
        outcome[r['engine'], r['workers']].add((r['version'], kind))
    why += thread_parity_failures(reports)
    for (engine, workers), seen in sorted(outcome.items()):
        kinds = {k for _, k in seen}
        if len(kinds) > 1:
            why.append(f'{engine} at {workers} w: outcomes {sorted(seen)}')
    return sorted(set(why))


def thread_parity_failures(reports):
    """Owner decision 11 (#965): threads over the cap at F2 may not exceed F0's on a path whose thread
    lifecycle is unchanged. The F4 teardown race (#1002) lets a finished team's threads outlive their
    join on both versions, so F0 sets the allowance. With per-thread states sampled (`running_peak`)
    the excess is running threads, judged on the shipping F4 and on entry calls that ship at both
    versions by the same route; without them it is listed threads, on every path."""
    why, groups = [], defaultdict(lambda: defaultdict(list))
    for r in reports:
        groups[r['engine'], r['workers']][r['version']].append(r)
    for (engine, workers), by in sorted(groups.items()):
        states = all(r['report'].get('running_peak') is not None for v in by.values() for r in v)
        if states and engine == 'entry':
            routes = {v: {r['report'].get('route') for r in rs} for v, rs in by.items()}
            same = routes.get('f0') == routes.get('f2') and all((x or '').startswith('Shipping(') for x in routes.get('f2', ()))
            if not same:
                continue
        field, what = ('running_peak', 'running') if states else ('threads_peak', 'listed')

        def excess(version):
            return max((max(0, (r['report'].get(field) or 0) - workers) for r in by.get(version, ())), default=0)
        if excess('f2') > excess('f0'):
            why.append(f'{engine} at {workers} w: {what} threads over the cap, F2 {excess("f2")} > F0 {excess("f0")}')
    return why


def correctness(args):
    refs = json.loads(Path(args.references).read_text()) if Path(args.references).exists() else {}
    rows = defaultdict(list)
    for job in args.jobs:
        for r in attempts(job):
            rows[r['instance']].append(r)
    lines = ['| Row | Attempts | `m33-basis-v1` | Reference | Verdict |', '|---|---:|---|---|---|']
    failed = 0
    for instance, records in sorted(rows.items()):
        ref = refs.get(instance)
        why = correctness_failures(instance, records, ref)
        failed += bool(why)
        digests = sorted({r['report']['basis_m33'][:12] for r in records if r['report'].get('basis_m33')})
        lines.append(f'| {instance} | {len(records)} | {", ".join(digests) or "—"} | '
                     f'{(ref or {}).get("reference", "—")} | {"; ".join(why) or "pass"} |')
    print('\n'.join(lines))
    print(f'\n{len(rows) - failed} of {len(rows)} rows pass.')
    return 1 if failed else 0


def paired(records, small):
    """(wall interval, peak RSS ratio) of F2 ÷ F0 per repetition, over clean complete attempts; a
    small row's wall is each process's median warm call (`bench_stats.warm_median`)."""
    def sample(r):
        return bs.warm_median(r['report']['calls_ns']) if small else r['wall_ns']
    clean = [r for r in records if r['status'] == 'ok' and not r['contaminated']
             and r['report'].get('status') == 'complete']
    # Keyed by job too, so an extension job's repetitions pool with the first job's instead of replacing them.
    by = {v: {(r.get('job'), r['rep']): r for r in clean if r['version'] == v} for v in ('f0', 'f2')}
    walls = bs.paired_ratios({k: sample(r) for k, r in by['f2'].items()}, {k: sample(r) for k, r in by['f0'].items()})
    rss = [r['rss'] for r in by['f2'].values() if r['rss']], [r['rss'] for r in by['f0'].values() if r['rss']]
    ratio = statistics.median(rss[0]) / statistics.median(rss[1]) if all(rss) else None
    f0_median = statistics.median(r['wall_ns'] for r in by['f0'].values()) if by['f0'] else None
    return walls, ratio, f0_median, len(records) - len(clean)


def ratio_table(jobs, small_jobs, title):
    cells, void = defaultdict(list), []
    for job, small in [(j, False) for j in jobs] + [(j, True) for j in small_jobs]:
        records = attempts(job)
        dirty = sum(r['contaminated'] for r in records)
        if bs.session_void(len(records) - dirty, dirty):  # §11.2: > 20% contaminated, re-run whole
            void.append(f'**Session void:** {Path(job).name}, {dirty} of {len(records)} attempts contaminated.')
        for r in records:
            cells[r['instance'], r['engine'], r['workers'], small].append(r)
    raw, verdicts, failed = [f'### {title}', '', '| Row | Engine | Workers | Method | F0 median | n | '
                                                 'F2 ÷ F0 wall [95%] | Peak RSS ratio | Excluded |',
                             '|---|---|---:|---|---:|---:|---|---:|---:|'], [], 0
    for (instance, engine, workers, small), records in sorted(cells.items()):
        ratios, rss, f0, excluded = paired(records, small)
        seed = f'{instance}|{engine}|{workers}|{small}'
        ci = bs.paired_ratio(ratios, seed=seed) if ratios else None
        method = 'warm calls' if small else 'process wall'
        interval = f'{ci.median:.3f} [{ci.lo:.3f}, {ci.hi:.3f}]' if ci else '—'
        raw.append(f'| {instance} | {engine} | {workers} | {method} | {f"{f0 / 1e6:.1f} ms" if f0 else "—"} | '
                   f'{ci.n if ci else 0} | {interval} | {f"{rss:.3f}" if rss else "—"} | {excluded} |')
        why = []
        if ci is None:
            why.append('no paired repetitions')
        else:
            v = bs.regression_verdict(ci, WALL_BOUND, min_n=31 if small else bs.BASE_N)
            if v.outcome != 'no-regression':
                why.append(f'wall {v.outcome}: {v.reason}')
        if not small and f0 is not None and f0 < FLOOR_NS:
            why.append('under 300 ms: read by warm calls (the small suite), not process wall')
        if rss is not None and rss > RSS_BOUND:
            why.append(f'peak RSS {rss:.3f} > {RSS_BOUND}')
        elif rss is not None and rss > RSS_EXPLAIN:
            why.append(f'peak RSS {rss:.3f} > {RSS_EXPLAIN}: explain in the PR')
        hard = [w for w in why if 'explain' not in w and 'under 300' not in w]
        failed += bool(hard)
        verdicts.append(f'| {instance} | {engine} | {workers} | {method} | {"; ".join(why) or "pass"} |')
    out = raw + ['', '| Row | Engine | Workers | Method | Verdict |', '|---|---|---:|---|---|'] + verdicts
    return '\n'.join(out + [''] + void if void else out), failed + len(void)


def regression(args):
    text, failed = ratio_table(args.jobs, args.small or [], 'Regression read (plan §12.2), F2 ÷ F0')
    print(text)
    return 1 if failed else 0


def gate_d(args):
    if not (args.gate_d and args.f2):
        print('refused: Gate D is read once, at F2 (plan §13); pass --gate-d --f2 <commit>', file=sys.stderr)
        return 2
    for job in args.jobs:
        ctx = json.loads((Path(job) / 'manifest.json').read_text())['context']
        pinned = ctx.get('f2') or ''
        same = len(min(pinned, args.f2, key=len)) >= 7 and (pinned.startswith(args.f2) or args.f2.startswith(pinned))
        if not (ctx.get('suite', '').startswith('gate-d-') and same):
            print(f'refused: {job} is not a Gate D job at F2 {args.f2}', file=sys.stderr)
            return 2
    if GATE_D.exists():
        print(f'refused: {GATE_D.name} exists; the held-out set has been read', file=sys.stderr)
        return 2
    text, failed = ratio_table(args.jobs, [], f'Gate D held-out read, F2 {args.f2} ÷ F0')
    GATE_D.write_text(text + '\n')
    print(text)
    return 1 if failed else 0


def main(argv=None):
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('command', choices=('correctness', 'regression', 'gate-d'))
    p.add_argument('jobs', nargs='*')
    p.add_argument('--small', nargs='*')
    p.add_argument('--references', default=str(HERE / 'references.json'))
    p.add_argument('--gate-d', action='store_true')
    p.add_argument('--f2')
    args = p.parse_args(argv)
    return dict(correctness=correctness, regression=regression, **{'gate-d': gate_d})[args.command](args)


if __name__ == '__main__':
    sys.exit(main())
