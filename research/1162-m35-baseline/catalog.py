#!/usr/bin/env python3
"""#1162: the declared M35 panel as `corpus-instance-v1` records, so Zeebra (`m34_matrix --catalog`)
and grobx solve byte-identical inputs.

    catalog.py build --qualify BIN --study BIN [--out catalog.json]

M34 rows are copied from the M34 catalogs by id; at BabyBear and KoalaBear (#1200) the M34 public
problems are reduced by `m34_public_corpus.reduce_record` instead. Ladder, MQ and GF(2) rows come from the Z0
generators through `--input-only`: `m33_qualify` for katsura/eco/cyclic/noon and `mq-random-N-sS`,
`sig_f4_study --generate` for `mq-dense-N-sS`, which `m33_qualify` cannot generate.
"""
import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import corpus_lineage  # noqa: E402
import m34_public_corpus as public  # noqa: E402

M34_CATALOGS = [ROOT / 'research/m34-public-corpus/catalog.json',
                ROOT / 'research/m34-structural-corpus/catalog.json']
M34_FIELDS = {'p31', 'p64'}
# #1200 (Amendment 1, #1189 item 1): M34 public rows re-keyed at these primes by the M34 reduction.
REKEYED_PRIMES = {'babybear': 2013265921, 'koalabear': 2130706433}


def panel_rows(panel):
    for family in panel['families']:
        for row in family['rows'] + family.get('frontier', []):
            for field in family['fields']:
                yield family, row, field
        ladder = family.get('ladder')
        if ladder:
            for field in ladder['fields']:
                if field not in family['fields']:
                    yield family, ladder['row'], field


def m34_records():
    records = {}
    for path in M34_CATALOGS:
        for record in json.loads(path.read_text()):
            records[record['id']] = record
    return records


def rekeyed(row, field):
    """An M34 public problem reduced at a prime the M34 catalogs do not carry, exactly as
    `m34_public_corpus.py` reduces it at p31 and p64."""
    panel = json.loads(public.PANEL.read_text())
    problem = next(p for p in panel['problems'] if p['id'] == row)
    entry = public.problem_entry(problem, panel, json.loads(public.INPUTS.read_text()))
    return public.reduce_record(problem, entry, field, REKEYED_PRIMES[field])


def generated(family, row, field, qualify, study):
    if row.startswith('mq-dense-'):
        argv = [study, '--field', field, '--name', row, '--generate', '--engine', 'f4', '--input-only']
    else:
        argv = [qualify, '--field', field, '--name', row, '--input-only']
    case = json.loads(subprocess.check_output(argv, text=True))
    p = int(case['modulus'])
    names = case['variables']
    equations = []
    for text in case['generators']:
        terms = {k: c % p for k, c in public.parse_integer_polynomial(text, names).items() if c % p}
        equations.append([{'exponents': list(k), 'coefficient': [str(c)]} for k, c in sorted(terms.items())])
    rec = {
        'schema': 'corpus-instance-v1',
        'id': f'{row}@{field}',
        'field': {'characteristic': str(p), 'extension_degree': 1, 'defining_polynomial': []},
        'variables': names,
        'order': 'grevlex',
        'task': 'T-GB',
        'equations': equations,
        'generator': {'call': [Path(argv[0]).name, *argv[1:]], 'z0': 'measured/1162-z0',
                      'zeebra_input_digest': case['digest']},
        'lineage': {'family_id': family['lineage'], 'formulation_id': f'{family["lineage"]}/{row}',
                    'split': family['split'], 'role': family['role']},
    }
    rec['lineage']['support_id'] = corpus_lineage.support_digest(rec)
    rec['normalized_input_digest'] = corpus_lineage.input_digest(rec)
    return rec


def build(args):
    panel = json.loads((HERE / 'panel.json').read_text())
    m34 = m34_records()
    out = []
    for family, row, field in panel_rows(panel):
        if field in M34_FIELDS or (field in REKEYED_PRIMES and f'{row}@p31' in m34):
            rec = m34[f'{row}@{field}'] if field in M34_FIELDS else rekeyed(row, field)
            rec = dict(rec, lineage=dict(rec['lineage'], split=family['split'], role=family['role']))
        else:
            rec = generated(family, row, field, args.qualify, args.study)
        out.append(rec)
        print(rec['id'], len(rec['variables']), len(rec['equations']), file=sys.stderr)
    ids = [r['id'] for r in out]
    assert len(ids) == len(set(ids)), 'duplicate record ids'
    # The M34 catalogs' layout: a JSON array, one record per line.
    text = '[\n' + ',\n'.join(json.dumps(r, sort_keys=True) for r in out) + '\n]\n'
    Path(args.out).write_text(text)
    # The catalog (about 3 MB) is rebuilt, not committed; its digests are, so a rebuild is checkable.
    digests = {'catalog_sha256': hashlib.sha256(text.encode()).hexdigest(),
               'records': {r['id']: r['normalized_input_digest'] for r in out}}
    (HERE / 'catalog-digests.json').write_text(json.dumps(digests, indent=1, sort_keys=True) + '\n')


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('command', choices=['build'])
    p.add_argument('--qualify', required=True)
    p.add_argument('--study', required=True)
    p.add_argument('--out', default='/buildcache/cargo-target/zeebra-1162/catalog.json')
    build(p.parse_args())


if __name__ == '__main__':
    main()
