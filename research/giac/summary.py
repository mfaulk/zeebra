"""A successful cohort row must retain both complete bases and the pinned input identity."""
import collections
import gzip
import hashlib
import json
from pathlib import Path
import re
import statistics


def canonical_basis(polynomials, p):
    basis = []
    for polynomial in polynomials:
        text = ''.join(polynomial.split())
        chunks = re.findall(r'[+-]?[^+-]+', text)
        if not text or ''.join(chunks) != text:
            raise ValueError('malformed polynomial')
        terms = collections.defaultdict(int)
        for chunk in chunks:
            sign = -1 if chunk.startswith('-') else 1
            coefficient = sign
            powers = collections.Counter()
            for factor in chunk.lstrip('+-').split('*'):
                pieces = factor.split('^')
                base = pieces[0]
                exponent = int(pieces[1]) if len(pieces) == 2 else 1
                if len(pieces) > 2 or exponent < 0:
                    raise ValueError('invalid factor')
                if base.isdigit():
                    coefficient = coefficient * pow(int(base), exponent, p) % p
                elif re.fullmatch('[A-Za-z][A-Za-z_0-9]*', base):
                    powers[base] += exponent
                else:
                    raise ValueError('unsupported polynomial syntax')
            monomial = tuple(sorted((v, e) for v, e in powers.items() if e))
            terms[monomial] = (terms[monomial] + coefficient) % p
        basis.append(tuple(sorted((m, c) for m, c in terms.items() if c)))
    return sorted(basis)


def instance_digest(artifacts):
    text = f'characteristic {artifacts["modulus"]}\nextension-degree 1\norder grevlex\n'
    text += 'variables ' + ','.join(artifacts['variables']) + '\n'
    if artifacts.get('transformation') is not None:
        text += 'transformation ' + artifacts['transformation'] + '\n'
    text += ''.join('generator ' + p + '\n' for p in artifacts['generators'])
    return hashlib.sha256(text.encode()).hexdigest()


def verify_attempt(attempt):
    row = attempt['rows'][0]
    artifacts = attempt['artifacts']
    if instance_digest(artifacts) != row['problem_digest']:
        raise ValueError('input identity mismatch')
    if row['outcome'] != 'verified':
        return False
    if row.get('order') != 'grevlex' or row.get('task') != 'reduced-grobner-basis':
        raise ValueError('wrong task or monomial order')
    if artifacts['status_detail'] != 'full-basis-verified':
        raise ValueError('missing exact verification')
    outputs = artifacts['independent_outputs']
    if len(outputs) != 1:
        raise ValueError('missing complete independent output')
    raw = outputs[0]
    if '@done' not in raw.splitlines() or any(line.lstrip().startswith('?') for line in raw.splitlines()):
        raise ValueError('incomplete independent computation')
    reference = [line[len('@gb '):] for line in raw.splitlines() if line.startswith('@gb ')]
    sizes = [int(line[len('@gbsize '):]) for line in raw.splitlines() if line.startswith('@gbsize ')]
    if sizes != [len(reference)]:
        raise ValueError('truncated independent basis')
    basis = artifacts['basis']
    p = artifacts['modulus']
    generators = [line[len('@gen '):] for line in raw.splitlines() if line.startswith('@gen ')]
    if canonical_basis(generators, p) != canonical_basis(artifacts['generators'], p):
        raise ValueError('independent engine parsed a different input')
    if p != row['field']['characteristic'] or canonical_basis(basis, p) != canonical_basis(reference, p):
        raise ValueError('full reduced bases disagree')
    if len(basis) != row['invariants']['basis_cardinality']:
        raise ValueError('basis cardinality differs')
    return True


def main():
    root = Path(__file__).resolve().parent
    with gzip.open(root / 'cohort.json.gz', 'rt') as stream:
        cohort = json.load(stream)
    groups = collections.defaultdict(list)
    for attempt in cohort['attempts']:
        verify_attempt(attempt)
        row = attempt['rows'][0]
        groups[(row['problem'], row['field']['characteristic'], row['limits']['workers'])].append((row, attempt['artifacts']))
    print('| instance | p | workers | verified / attempts | child wall s median [min, max] | verification s median | parent wall s median | max RSS MiB |')
    print('|---|---:|---:|---:|---|---:|---:|---:|')
    for (name, p, workers), entries in sorted(groups.items()):
        rows = [row for row, _ in entries]
        completed = [row for row in rows if row['outcome'] == 'verified']
        if not completed:
            outcomes = ', '.join(sorted({row['outcome'] for row in rows}))
            print(f'| {name} | {p} | {workers} | 0 / {len(rows)} | {outcomes}; no timing | — | — | — |')
            continue
        if len(rows) != 5:
            raise ValueError('five fresh-process repetitions required')
        if len(completed) != len(rows):
            print(f'| {name} | {p} | {workers} | {len(completed)} / {len(rows)} | partial cohort; no timing median | — | — | — |')
            continue
        seconds = [row['wall_nanos']/1e9 for row in completed]
        rss = [row['peak_rss_bytes']/(1024**2) for row in completed if row.get('peak_rss_bytes') is not None]
        verification = [sum(stage['elapsed_nanos'] for stage in row['stages']
                            if stage['name'] == 'independent-verification') / 1e9
                        for row in completed]
        parents = [artifacts['parent_guard_wall_ns'] / 1e9 for _, artifacts in entries]
        print(f'| {name} | {p} | {workers} | {len(completed)} / {len(rows)} | '
              f'{statistics.median(seconds):.6f} [{min(seconds):.6f}, {max(seconds):.6f}] | '
              f'{statistics.median(verification):.6f} | {statistics.median(parents):.6f} | {max(rss):.2f} |')


if __name__ == '__main__':
    main()
