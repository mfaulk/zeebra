#!/usr/bin/env python3
"""Re-judge the retained M33 sessions under bench-job's session verdict v2 (#996).

Reads each attempt's journaled contamination metrics, from the retained journal where the study kept
one and from its extracted records otherwise, and judges them through `tools/bench-job`'s own
`session_verdict_of` twice: per cell (v1, which must reproduce the verdict on record) and per arm.

    python3 research/m33-clock-rule/reverdict.py [--write]    prints, or writes verdicts.md
"""

import gzip
import importlib.machinery
import importlib.util
import json
import sys
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
_loader = importlib.machinery.SourceFileLoader('bench_job', str(ROOT / 'tools' / 'bench-job'))
bj = importlib.util.module_from_spec(importlib.util.spec_from_loader('bench_job', _loader))
_loader.exec_module(bj)

JOURNALS = [('M33-0 baseline', ROOT / 'research/m33-baseline/journals' / j)
            for j in ('00881e3bf16c', '8a0630174500', '2fb61582468a', '5d986752d34a')]
JOURNALS.append(('M33-G1 (#992)', ROOT / 'research/m33-grobx-attribution/journals/4004a790e353'))
RECORDS = [('M33-M1 (#993)', ROOT / f'research/m33-msolve-attribution/records-{j}')
           for j in ('0ec6dad86c92', '1df3100aa22a', '9de09467ead1', 'b35504942e78')]


def from_journal(directory):
    """(job, mode, context, recorded stop verdict, rows) from a retained journal's exit records."""
    job = json.loads((directory / 'header.json').read_text())['header']['bench_job']
    rows, stop = {}, None
    for line in gzip.decompress((directory / 'journal.jsonl.gz').read_bytes()).splitlines():
        r = json.loads(line)
        if r['kind'] == 'exit':
            md = r['metadata']
            rows[md['attempt_id']] = (md['attempt_id'], r['cell'], md.get('contamination') or {})
        elif r['kind'] == 'stop':
            stop = r['values']
    return job, stop, list(rows.values())


def from_records(stem):
    """The same from a study's extracted records, for a session whose journal was not retained."""
    session = json.loads(stem.with_name(stem.name + '.session.json').read_text())
    rows = [(r['attempt'], dict(instance=f"{r['field']}/{r['name']}", workers=r['workers'], arm=r['arm']),
             dict(metrics=r['metrics']))
            for r in map(json.loads, gzip.decompress(stem.with_name(stem.name + '.jsonl.gz').read_bytes()).splitlines())]
    return session['job'], session['stop'], rows


def reasons(verdict):
    return Counter(' '.join(x.split(' ')[:2]) for rs in verdict['flagged'].values() for x in rs)


def judge():
    out = []
    for study, src in JOURNALS + RECORDS:
        job, stop, rows = (from_journal if src.is_dir() else from_records)(src)
        owner = bj.lock_owner(job['job_id'])
        v1, v2 = (bj.session_verdict_of(rows, job['mode'], owner, grouping=g) for g in ('cell', 'arm'))
        recorded = (stop or {}).get('contamination') or {}
        if (v1['contaminated'], v1['void']) != (recorded.get('contaminated'), recorded.get('void')):
            raise SystemExit(f"{job['job_id']}: the v1 replay {v1['contaminated']} does not reproduce "
                             f"the recorded {recorded.get('contaminated')}")
        out.append(dict(study=study, job=job['job_id'], track=job['context'].get('track'),
                        session=job['context'].get('session'), v1=v1, v2=v2))
    return out


def table(results):
    lines = ['| Study | Job | Track / session | v1 per cell (on record) | v2 per arm | v2 reasons |',
             '|---|---|---|---|---|---|']
    for r in results:
        v1, v2 = r['v1'], r['v2']
        cell = lambda v: f"{v['contaminated']}/{v['total']} {'**void**' if v['void'] else 'valid'}"  # noqa: E731
        why = ', '.join(f'{k} {n}' for k, n in sorted(reasons(v2).items())) or '—'
        lines.append(f"| {r['study']} | `{r['job']}` | {r['track']} / {r['session']} | {cell(v1)} | {cell(v2)} | {why} |")
    return '\n'.join(lines) + '\n'


def main(argv):
    text = table(judge())
    if '--write' in argv:
        (HERE / 'verdicts.md').write_text(text)
    print(text, end='')
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
