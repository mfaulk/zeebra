#!/usr/bin/env python3
"""Writes pins.json: #939's freeze and the canonical SHA-256 of every M32 corpus row (plan §10.1),
with the held-out admission read applied by the plan's fixed rule.

Catalog rows are re-hashed from `research/wide-corpus/cases.json`; rows pinned in code (the
published ladder's, and the held-out candidates `sig_f4_study` generates) must appear verbatim in
that code, whose own tests rebuild them, so a drifted generator fails there or here before a timing.

    python3 research/m32-baseline/pins.py > research/m32-baseline/pins.json
"""
import gzip
import hashlib
import json
import statistics
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
CATALOG = ROOT / 'research/wide-corpus/cases.json'
LADDER = ROOT / 'src/grobner/external/corpus.rs'
STUDY = ROOT / 'examples/sig_f4_study.rs'
ADMISSION = HERE / 'admission.jsonl.gz'

FREEZE = dict(
    reference=dict(commit='8715c8edb5ed5ab17e9d71331c48e07cb87b7754', what='M31 final main (#926)'),
    baseline=dict(commit='7b25a1ee56c348fb68fd5671a94fe19d1e6aafec',
                  what='M32 baseline main (#943); timed src/ equals e59a90a1 and differs from the '
                       'reference only in documentation (identities.json)'),
)
# (field, name, role): M31's §10.3 corpus plus its held-out katsura-9 and noon-8, demoted.
DEVELOPMENT = [
    ('wide64', 'eco-12', 'M31 primary'),
    ('goldilocks', 'katsura-11', 'M31 second family'),
    ('wide64', 'katsura-11', 'M31 competitive'),
    ('goldilocks', 'mq-random-11', 'M31 reported'),
    ('gf32003', 'mq-random-10', 'M31 MQ10'),
    ('m31', 'mq-random-10', 'M31 MQ10'),
    ('goldilocks', 'cyclic-7', 'M31 unfavourable control'),
    ('wide64', 'cyclic-7', 'M31 unfavourable control'),
    ('goldilocks', 'katsura-4', 'M31 small control'),
    ('wide64', 'katsura-4', 'M31 small control'),
    ('goldilocks', 'noon-7', 'M31 small control'),
    ('wide64', 'katsura-9', 'M31 held out, demoted'),
    ('wide64', 'noon-8', 'M31 held out, demoted'),
]
# (field, name, why) in plan §10.1's order; the source is resolved below.
HELD_OUT = [
    ('goldilocks', 'mq-random-10', "MQ10's family and size at another field width"),
    ('wide64', 'mq-random-12', 'larger dense MQ, the other side of the crossover'),
    ('gf32003', 'mq-random-9', 'smaller dense MQ'),
    ('m31', 'katsura-10', 'favourable family, unseen size and field'),
    ('m31', 'eco-11', 'favourable family, unseen size and field'),
    ('goldilocks', 'cyclic-6', 'degree-spread control'),
]
MODULUS = dict(goldilocks='18446744069414584321', wide64='18446744073709551263', gf32003='32003',
               m31='2147483647')
# Pinned in code, with the generator that builds each (both checked by `sig_f4_study`'s tests).
CODE = {
    ('gf32003', 'mq-random-10'): ('16422dafcdb6487ea541f976f7754112b811c85af2b3537ed10fe4ef9c8f3d7f', LADDER,
                                  'grobner::external::corpus::random_mq_instance(10, seed 10) (ladder)'),
    ('m31', 'mq-random-10'): ('72d0ad315fc25409792625465578d18329597d3ee183e75f257774d9215803b2', LADDER,
                              'grobner::external::corpus::random_mq_instance(10, seed 10) (ladder)'),
    ('m31', 'katsura-10'): ('67d6a96fadd21cc7a295c7100c93d84d2d7be37d9b7927377e57f973ebbbc8b0', LADDER,
                            'grobner::benchmark_systems::katsura::<10> (ladder katsura_instance)'),
    ('gf32003', 'mq-random-9'): ('4e4ddcb645c8f6eddb73d21a1532437643f7a2a2a6faf6643886d1c4a5076b21', STUDY,
                                 'grobner::external::corpus::random_mq_instance(9, seed 9)'),
    ('m31', 'eco-11'): ('3bdb17005b060d861412758860684229498a54906f610b9854b6bd09d8d11951', STUDY,
                        'grobner::benchmark_systems::eco::<11>'),
    ('goldilocks', 'cyclic-6'): ('2867c8eb39e07bec37ecb907e5b6971146a479594b0a9fc5ba20b64650a0c918', STUDY,
                                 'grobner::benchmark_systems::cyclic::<6>'),
}
# Plan §10.1's admission rule, fixed before the read.
ADMIT_NS = (20 * 10**6, 60 * 10**9)
# Both engines are generic over `FiniteField`; the signature engine's only refusal is a non-graded
# order (`SigF4Error::Unsupported`), and `sig_f4_study` instantiates both for each row's field.
FIELD_ACCEPTANCE = 'both engines generic over FiniteField; no field refusal (sigf4/dispatch.rs)'


def row(cases, sources, field, name):
    if (field, name) in CODE:
        digest, path, generator = CODE[(field, name)]
        assert f'"{digest}"' in sources[path], f'{field}/{name}: pin not found in {path.name}'
        canonical = 'external contract (Instance::canonical)'
        variables = int(name.rsplit('-', 1)[1])
    else:
        case = next(c for c in cases if c['field'] == field and c['name'] == name)
        digest = hashlib.sha256(case['canonical'].encode()).hexdigest()
        assert digest == case['digest'], f'{field}/{name}: catalog digest does not match its text'
        generator = case['canonical'].splitlines()[4].removeprefix('transformation ')
        generator = f"research/wide-corpus/cases.json ({generator})"
        canonical = 'wide-corpus-v1'
        variables = len(case['variables'])
    return dict(field=field, modulus=MODULUS[field], name=name, variables=variables, order='grevlex',
                generator=generator, canonical=canonical, sha256=digest)


def admission(records):
    """Per held-out row: every repetition's walls and the rule's verdict on their median."""
    out = {}
    for field, name, _ in HELD_OUT:
        key = f'{field}/{name}'
        mine = [r for r in records if r['row'] == key]
        if not mine:
            out[key] = dict(verdict='not read')
            continue
        reports = [r['report'] or {} for r in mine]
        complete = all(r.get('status') == 'complete' for r in reports)
        walls = sorted(r['process_wall_ns'] for r in mine)
        median = statistics.median(walls)
        if not complete:
            verdict, reason = 'dropped', 'conventional F4 did not complete under the budgets'
        elif not ADMIT_NS[0] <= median <= ADMIT_NS[1]:
            verdict, reason = 'dropped', f'median process wall {median / 1e6:.1f} ms outside 20 ms-60 s'
        else:
            verdict, reason = 'kept', 'completes inside 20 ms-60 s; both engines accept the field'
        out[key] = dict(
            verdict=verdict, reason=reason, arm='f4:16', n=len(mine),
            statuses=sorted({r.get('status', 'no report') for r in reports}),
            process_wall_ms=[round(w / 1e6, 1) for w in walls], median_process_wall_ms=round(median / 1e6, 1),
            call_ms=sorted(round(r['call_ns'] / 1e6, 1) for r in reports if 'call_ns' in r),
            peak_rss_mib=max((round(r['peak_rss_bytes'] / 2**20) for r in reports if r.get('peak_rss_bytes')),
                             default=None),
            basis_elements=sorted({r.get('basis_elements') for r in reports if 'basis_elements' in r}),
            basis_sha256=sorted({r.get('basis_sha256') for r in reports if r.get('basis_sha256')}),
            input_digests=sorted({r.get('digest') for r in reports if r.get('digest')}),
            field_acceptance=FIELD_ACCEPTANCE)
    return out


def pins():
    raw = CATALOG.read_bytes()
    cases = json.loads(raw)
    sources = {LADDER: LADDER.read_text(), STUDY: STUDY.read_text()}
    records = []
    if ADMISSION.exists():
        with gzip.open(ADMISSION, 'rt') as f:
            records = [json.loads(line) for line in f]
    admitted = admission(records)
    held_out = []
    for field, name, why in HELD_OUT:
        pinned = row(cases, sources, field, name)
        read = admitted[f'{field}/{name}']
        for digest in read.get('input_digests', []):
            assert digest == pinned['sha256'], f'{field}/{name}: timed input differs from the pin'
        held_out.append(dict(pinned, why=why, admission=read))
    return dict(
        issue=939,
        freeze=FREEZE,
        catalog=str(CATALOG.relative_to(ROOT)),
        catalog_sha256=hashlib.sha256(raw).hexdigest(),
        development=[dict(row(cases, sources, f, n), role=r) for f, n, r in DEVELOPMENT],
        held_out=held_out,
        admission_rule='kept iff conventional F4 at 16 workers completes in 20 ms-60 s (median process '
                       'wall) under 180 s / 8 GiB and both engines accept the field; otherwise dropped '
                       'with the reason and not replaced',
    )


if __name__ == '__main__':
    print(json.dumps(pins(), indent=1))
