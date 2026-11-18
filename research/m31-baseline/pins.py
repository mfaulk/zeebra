#!/usr/bin/env python3
"""Writes pins.json: the #901 freeze and the canonical SHA-256 of every corpus row, re-hashed from
`research/wide-corpus/cases.json` so a drifted catalog fails here rather than in a timing.

The held-out rows are committed before any S2/S3 timing (plan §10.3) and are never used to choose a
design or threshold.

    python3 research/m31-baseline/pins.py > research/m31-baseline/pins.json
"""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
CATALOG = ROOT / 'research/wide-corpus/cases.json'
FREEZE = 'acbaf12c840d5ccea52b10388cc850ed6e8a5236'
# (field, name, role) — plan §10.3.
CORPUS = [
    ('wide64', 'eco-12', 'primary (gating)'),
    ('goldilocks', 'katsura-11', 'second family (gating)'),
    ('wide64', 'katsura-11', 'competitive (reported)'),
    ('goldilocks', 'mq-random-11', 'reported'),
    ('goldilocks', 'cyclic-7', 'unfavourable control (gating via entry point)'),
    ('wide64', 'cyclic-7', 'unfavourable control (reported)'),
    ('goldilocks', 'katsura-4', 'small control (gating)'),
    ('wide64', 'katsura-4', 'small control (gating)'),
    ('goldilocks', 'noon-7', 'small control (gating)'),
]
HELD_OUT = [('wide64', 'katsura-9'), ('wide64', 'noon-8'), ('wide64', 'eco-14')]


def row(cases, field, name):
    case = next(c for c in cases if c['field'] == field and c['name'] == name)
    digest = hashlib.sha256(case['canonical'].encode()).hexdigest()
    assert digest == case['digest'], f'{field}/{name}: catalog digest does not match its text'
    return dict(field=field, name=name, variables=len(case['variables']), sha256=digest)


def pins():
    raw = CATALOG.read_bytes()
    cases = json.loads(raw)
    return dict(
        issue=901,
        freeze=dict(commit=FREEZE, includes={'#896': '9f904d08', '#897': '4d8ea30c', '#898': '64363ab0'}),
        catalog=str(CATALOG.relative_to(ROOT)),
        catalog_sha256=hashlib.sha256(raw).hexdigest(),
        corpus=[dict(row(cases, f, n), role=r) for f, n, r in CORPUS],
        held_out=[dict(row(cases, f, n), role='held out (reported; never used for tuning)')
                  for f, n in HELD_OUT],
        mq10=[dict(target=t, source='examples/m29_cost_model.rs (generated in-process, pinned there)')
              for t in ('mq10-32003', 'mq10-m31')],
    )


if __name__ == '__main__':
    print(json.dumps(pins(), indent=1))
