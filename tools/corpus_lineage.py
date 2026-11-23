#!/usr/bin/env python3
import argparse
from collections import defaultdict
import gzip
import hashlib
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
SCHEMA = json.loads(Path(__file__).with_name('corpus-lineage.schema.json').read_text())


def encoded(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'), ensure_ascii=True, allow_nan=False).encode('ascii')


def sha(value):
    return hashlib.sha256(encoded(value)).hexdigest()


def validate_shape(value, schema, path='$'):
    # Fail closed if the published schema grows beyond this dependency-free subset.
    supported = {'$ref', '$schema', '$id', '$defs', 'anyOf', 'type', 'const', 'enum', 'required',
                 'properties', 'additionalProperties', 'minItems', 'uniqueItems', 'items',
                 'minLength', 'pattern', 'minimum'}
    if set(schema) - supported:
        raise ValueError(f'unsupported schema keyword: {sorted(set(schema) - supported)}')
    if '$ref' in schema:
        return validate_shape(value, SCHEMA['$defs'][schema['$ref'].split('/')[-1]], path)
    if 'anyOf' in schema:
        for option in schema['anyOf']:
            try:
                validate_shape(value, option, path)
                return
            except ValueError:
                pass
        raise ValueError(f'{path}: no allowed shape matched')
    types = dict(object=dict, array=list, string=str, integer=int, null=type(None))
    if 'type' in schema and (not isinstance(value, types[schema['type']]) or
                             schema['type'] == 'integer' and isinstance(value, bool)):
        raise ValueError(f'{path}: expected {schema["type"]}')
    if 'const' in schema and value != schema['const']:
        raise ValueError(f'{path}: expected {schema["const"]}')
    if 'enum' in schema and value not in schema['enum']:
        raise ValueError(f'{path}: unrecognized value {value!r}')
    if isinstance(value, dict):
        for key in schema.get('required', []):
            if key not in value:
                raise ValueError(f'{path}.{key}: required')
        for key, item in value.items():
            if key in schema.get('properties', {}):
                validate_shape(item, schema['properties'][key], f'{path}.{key}')
            elif schema.get('additionalProperties') is False:
                raise ValueError(f'{path}.{key}: unknown property')
    if isinstance(value, list):
        if len(value) < schema.get('minItems', 0):
            raise ValueError(f'{path}: too few entries')
        if schema.get('uniqueItems') and len({encoded(x) for x in value}) != len(value):
            raise ValueError(f'{path}: duplicate entries')
        for i, item in enumerate(value):
            validate_shape(item, schema.get('items', {}), f'{path}[{i}]')
    if isinstance(value, str):
        if len(value.strip()) < schema.get('minLength', 0):
            raise ValueError(f'{path}: empty text')
        if 'pattern' in schema and not re.fullmatch(schema['pattern'], value):
            raise ValueError(f'{path}: invalid text')
    if 'minimum' in schema and value < schema['minimum']:
        raise ValueError(f'{path}: below minimum')


def normalized_equations(record):
    p = int(record['field']['characteristic'])
    degree = record['field']['extension_degree']
    polynomials = []
    for polynomial in record['equations']:
        terms = {}
        for term in polynomial:
            key = tuple(term['exponents'])
            coefficient = terms.setdefault(key, [0] * degree)
            for i, c in enumerate(term['coefficient']):
                coefficient[i] = (coefficient[i] + int(c)) % p
        polynomials.append([[list(m), [str(c) for c in cs]] for m, cs in sorted(terms.items()) if any(cs)])
    return sorted(polynomials, key=encoded)


def input_digest(record):
    return sha(dict(format='normalized-input-v1', field=record['field'], variables=record['variables'],
                    order=record['order'], equations=normalized_equations(record)))


def support_digest(record):
    # Field-independent but coordinate-dependent: reductions that remove terms change this digest.
    return sha(dict(format='support-v1', variables=record['variables'],
                    supports=sorted([[term[0] for term in p] for p in normalized_equations(record)], key=encoded)))


def validate_record(record):
    validate_shape(record, SCHEMA)
    field = record['field']
    p, d = int(field['characteristic']), field['extension_degree']
    if p < 2:
        raise ValueError('field.characteristic must be at least 2')
    defining = [int(c) for c in field['defining_polynomial']]
    if (d == 1 and defining) or (d > 1 and (len(defining) != d + 1 or defining[-1] != 1)):
        raise ValueError('field.defining_polynomial must be empty for prime fields or monic of degree d')
    if any(c >= p for c in defining):
        raise ValueError('field.defining_polynomial coefficient outside characteristic')
    for polynomial in record['equations']:
        for term in polynomial:
            if len(term['exponents']) != len(record['variables']):
                raise ValueError('exponent vector does not match ordered variables')
            if len(term['coefficient']) != d or any(int(c) >= p for c in term['coefficient']):
                raise ValueError('coefficient must have d residues in [0,p)')
    if record['normalized_input_digest'] != input_digest(record):
        raise ValueError(f'{record["id"]}: normalized input digest mismatch')


def presentation_roots(records):
    by_id = {r['id']: r for r in records}
    if len(by_id) != len(records):
        raise ValueError('duplicate instance id')
    roots = {}
    for name in by_id:
        seen, current = set(), name
        while current not in roots:
            if current in seen:
                raise ValueError('presentation parent cycle')
            seen.add(current)
            if current not in by_id:
                raise ValueError(f'unresolved presentation parent {current}')
            parent = by_id[current]['lineage']['presentation_parent']
            if parent is None:
                roots[current] = current
                break
            current = parent
        for member in seen:
            roots[member] = roots[current]
    return roots


def group_dimensions(r, protocol, roots):
    dimensions = {}
    if not protocol.startswith('S5-'):
        dimensions.update({k: r['lineage'][k] for k in ('support_id', 'formulation_id')})
        dimensions['presentation'] = roots[r['id']]
        dimensions['normalized-input'] = r['normalized_input_digest']
        dimensions['computed-support'] = support_digest(r)
    if protocol == 'S2':
        dimensions.update({k: r['lineage'][k] for k in ('family_id', 'source_id')})
    if protocol == 'S5-field':
        dimensions['field'] = sha(r['field'])
        dimensions['normalized-input'] = r['normalized_input_digest']
        dimensions['presentation'] = roots[r['id']]
    return dimensions


def draw_split(records, protocol, salt, evaluation_groups, exposed_ids):
    if not isinstance(records, list) or not records:
        raise ValueError('catalog must be a nonempty array')
    for record in records:
        validate_record(record)
    roots = presentation_roots(records)
    if protocol not in ('S1', 'S2', 'S4') or not isinstance(salt, str) or not salt.strip():
        raise ValueError('draw requires S1, S2 or S4 and a nonempty salt')
    if type(evaluation_groups) is not int or evaluation_groups < 1:
        raise ValueError('evaluation_groups must be positive')
    parents = {r['id']: r['id'] for r in records}
    if (not isinstance(exposed_ids, list) or any(not isinstance(x, str) for x in exposed_ids)
            or not set(exposed_ids) <= set(parents) or len(set(exposed_ids)) != len(exposed_ids)):
        raise ValueError('exposed_ids must be distinct catalog ids')

    def find(name):
        while name != parents[name]:
            parents[name] = parents[parents[name]]
            name = parents[name]
        return name

    owners = {}
    for r in sorted(records, key=lambda r: r['id']):
        for key, value in group_dimensions(r, protocol, roots).items():
            owner = owners.setdefault((key, value), r['id'])
            parents[find(r['id'])] = find(owner)
    groups = defaultdict(list)
    for name in sorted(parents):
        groups[find(name)].append(name)
    eligible = [g for g in groups.values() if not set(g).intersection(exposed_ids)]
    eligible.sort(key=lambda group: (sha(['hash-groups-v1', salt, protocol, group]), group))
    if evaluation_groups > len(eligible) or evaluation_groups >= len(groups):
        raise ValueError('not enough unexposed groups while retaining development data')
    selected = {name for group in eligible[:evaluation_groups] for name in group}
    result = dict(schema='corpus-split-v1', protocol=protocol, assignments=[
        dict(id=name, partition='evaluation' if name in selected else 'development') for name in sorted(parents)])
    result['draw'] = dict(algorithm='hash-groups-v1', salt=salt,
                          catalog_sha256=sha(sorted(records, key=lambda r: r['id'])),
                          evaluation_groups=evaluation_groups, exposed_ids=sorted(exposed_ids))
    return result


def check_split(records, split):
    if not isinstance(records, list) or not records:
        raise ValueError('catalog must be a nonempty array')
    for record in records:
        validate_record(record)
    validate_shape(split, SCHEMA['$defs']['split'])
    roots = presentation_roots(records)
    by_id = {r['id']: r for r in records}
    protocol = split['protocol']
    hardware = protocol == 'S5-hardware'
    assignments = split['assignments']
    if {a['id'] for a in assignments} != set(by_id):
        raise ValueError('assignments must cover exactly the catalog ids')
    keys = [(a['id'], a.get('hardware')) if hardware else a['id'] for a in assignments]
    if len(set(keys)) != len(keys):
        raise ValueError('duplicate assignment')
    if hardware and any('hardware' not in a for a in assignments):
        raise ValueError('S5-hardware requires hardware for every assignment')
    if not hardware and any('hardware' in a for a in assignments):
        raise ValueError('hardware is only defined for S5-hardware')
    if {a['partition'] for a in assignments} != {'development', 'evaluation'}:
        raise ValueError('split must contain development and evaluation')
    if (protocol == 'S3') != ('scale_parameter' in split):
        raise ValueError('only S3 requires scale_parameter')

    groups = defaultdict(lambda: defaultdict(set))
    for a in assignments:
        r, partition = by_id[a['id']], a['partition']
        dimensions = group_dimensions(r, protocol, roots)
        if hardware:
            dimensions['hardware'] = a['hardware']
        for key, value in dimensions.items():
            groups[key][value].add(partition)
    errors = [f'{key}: {value} crosses development/evaluation'
              for key, values in sorted(groups.items()) for value, partitions in sorted(values.items())
              if len(partitions) > 1]
    if protocol in ('S5-field', 'S5-hardware'):
        key = 'formulation_id' if protocol == 'S5-field' else 'normalized_input_digest'
        paired = defaultdict(set)
        for a in assignments:
            r = by_id[a['id']]
            paired[a['partition']].add(r['lineage'][key] if key == 'formulation_id' else r[key])
        missing = paired['evaluation'] - paired['development']
        if missing:
            label = 'formulation twin' if protocol == 'S5-field' else 'matched inputs'
            errors.append(f'{label}: no development match for {sorted(missing)}')
    if protocol == 'S3':
        parameter = split['scale_parameter']
        sizes = defaultdict(lambda: defaultdict(list))
        for a in assignments:
            r = by_id[a['id']]
            value = r['lineage']['family_parameters'].get(parameter)
            if type(value) not in (int, float) or not (-float('inf') < value < float('inf')):
                raise ValueError(f'{r["id"]}: scale parameter must be a finite number')
            sizes[r['lineage']['family_id']][a['partition']].append(value)
        for family, parts in sorted(sizes.items()):
            if parts['evaluation'] and (not parts['development'] or min(parts['evaluation']) <= max(parts['development'])):
                errors.append(f'scale: {family} evaluation must exceed all development {parameter}')
    if 'draw' in split:
        draw = split['draw']
        expected = draw_split(records, protocol, draw['salt'], draw['evaluation_groups'], draw['exposed_ids'])
        actual_assignments = sorted(assignments, key=lambda a: a['id'])
        if actual_assignments != expected['assignments'] or draw != expected['draw']:
            errors.append('draw: metadata or assignments do not match the declared hash draw')
    return errors


def parse_prime(text, p, variables):
    compact = ''.join(text.split())
    if not re.fullmatch(r'-?[^+\-]+(?:[+\-][^+\-]+)*', compact):
        raise ValueError(f'invalid expanded polynomial: {text!r}')
    result = []
    for term in compact.replace('-', '+-').split('+'):
        if not term:
            continue
        coefficient = -1 if term.startswith('-') else 1
        exponents = [0] * len(variables)
        for factor in term.lstrip('-').split('*'):
            m = re.fullmatch(r'([A-Za-z][A-Za-z0-9_]*|[0-9]+)(?:\^([0-9]+))?', factor)
            if not m:
                raise ValueError(f'invalid polynomial factor {factor!r}')
            base, power = m[1], int(m[2] or 1)
            if base.isdigit():
                coefficient = coefficient * pow(int(base), power, p) % p
            elif base in variables:
                exponents[variables.index(base)] += power
            else:
                raise ValueError(f'unknown variable {base}')
        result.append(dict(exponents=exponents, coefficient=[str(coefficient % p)]))
    return result


def legacy_input(case):
    canonical = case['canonical']
    lines = canonical.splitlines()
    expected = [f'order grevlex', 'variables ' + ','.join(case['variables'])]
    field_lines = {f'prime {case["modulus"]}', f'characteristic {case["modulus"]}'}
    if (hashlib.sha256(canonical.encode()).hexdigest() != case['digest']
            or not field_lines.intersection(lines) or any(line not in lines for line in expected)
            or [line.removeprefix('generator ') for line in lines if line.startswith('generator ')] != case['generators']):
        raise ValueError(f'{case["name"]}: legacy canonical text or digest disagrees with equation echoes')
    return dict(field=dict(characteristic=str(case['modulus']), extension_degree=1, defining_polynomial=[]),
                variables=case['variables'], order='grevlex',
                equations=[parse_prime(g, int(case['modulus']), case['variables']) for g in case['generators']])


def audit(root):
    paths = ['research/wide-corpus/cases.json', 'research/public-corpus/inventory.json',
             'research/public-corpus/results/public-679.json.gz', 'research/m33-baseline/candidates.json',
             'research/m33-baseline/held-out.json', 'research/m33-baseline/manifests/G-baseline.json',
             'research/m33-baseline/manifests/M-baseline.json',
             'research/m33-final/references.json', 'examples/wide_corpus.rs',
             'src/grobner/external/corpus.rs', 'research/m33-baseline/admission.py',
             'research/m33-qualification/references.json', 'research/m33-qualification/campaign.py']
    sources = {p: hashlib.sha256((root / p).read_bytes()).hexdigest() for p in paths}
    wide = json.loads((root / paths[0]).read_text())
    inventory = json.loads((root / paths[1]).read_text())['candidates']
    public = json.loads(gzip.decompress((root / paths[2]).read_bytes()))['cases']
    candidates = json.loads((root / paths[3]).read_text())['tracks']
    held = json.loads((root / paths[4]).read_text())
    rows, unresolved = [], []
    for catalog, cases in [('wide', wide), ('public', public)]:
        for c in cases:
            r = legacy_input(c)
            name = re.sub(r'^public-', '', c['name'])
            family, n = name.rsplit('-', 1)
            # Dense MQ in the wide catalog is NOT the sparse random generator used by M33.
            mechanism = 'wide-dense-mq' if family == 'mq-random' else family
            rows.append(dict(id=f'{catalog}/{c["modulus"]}/{c["name"]}', legacy_digest=c['digest'],
                             normalized_input_digest=input_digest(r), support_id=support_digest(r),
                             formulation_id=f'{mechanism}/{n}', family_id=mechanism,
                             source_id=f'zeebra/{mechanism}', presentation_parent=None))
    for track, cases in sorted(candidates.items()):
        for c in cases:
            name = re.sub(r'-s[0-9]+$', '', c['name'])
            family, n = name.rsplit('-', 1)
            seed = c['name'].removeprefix(name + '-s') if c['name'] != name else None
            mechanism = 'sparse-random-mq' if family == 'mq-random' else family
            ident = f'm33/{track}/{c["field"]}/{c["name"]}'
            # A seeded finite-field draw may change support across primes: never infer equality.
            formulation = f'{mechanism}/{n}' + (f'/seed-{seed}' if seed else '')
            rows.append(dict(id=ident, legacy_digest=c['digest'], normalized_input_digest=None,
                             support_id=None, formulation_id=formulation, family_id=mechanism,
                             source_id=f'zeebra/{mechanism}', presentation_parent=None,
                             m33_excluded=c['excluded'],
                             m33_held_out=any(x['field'] == c['field'] and x['name'] == c['name'] for x in held[track])))
            unresolved.append(dict(id=ident, reason='candidate retains legacy digest and generator identity, not exact equations; normalized digest and support unverified'))
    refs = json.loads((root / paths[7]).read_text())
    held_keys = {(c['field'], c['name']) for cases in held.values() for c in cases}
    exact_by_digest = {r['legacy_digest']: r for r in rows if r['normalized_input_digest']}
    wide_keys = {(c['field'], c['name']) for c in wide}

    def reference_row(ident, field, name, ref, order):
        stem = re.sub(r'-s[0-9]+$', '', name)
        family, n = stem.rsplit('-', 1)
        dense = (field, name) in wide_keys and family == 'mq-random'
        mechanism = ('wide-dense-mq' if dense else 'sparse-random-mq') if family == 'mq-random' else family
        seed = name.removeprefix(stem + '-s') if name != stem else n
        formulation = f'{mechanism}/{n}' + (f'/seed-{seed}' if mechanism == 'sparse-random-mq' else '')
        # A matching legacy input digest binds the exact retained equations, not just the name.
        exact = exact_by_digest.get(ref['input_digest'])
        if exact is None:
            unresolved.append(dict(id=ident, reason='reference pins input digest but has no matching materialized input; normalized digest and support unverified'))
        return dict(id=ident, legacy_digest=ref['input_digest'],
                    normalized_input_digest=exact['normalized_input_digest'] if exact else None,
                    support_id=exact['support_id'] if exact else None,
                    formulation_id=formulation, family_id=mechanism,
                    source_id=f'zeebra/{mechanism}', presentation_parent=None, order=order)

    for key, ref in sorted(refs.items()):
        field, name = key.split('__', 1)
        r = reference_row(f'm33-final/{field}/{name}', field, name, ref, 'grevlex')
        r['partition'] = 'evaluation' if (field, name) in held_keys else 'development'
        rows.append(r)
    qualification = json.loads((root / 'research/m33-qualification/references.json').read_text())
    for key, ref in sorted(qualification.items()):
        order, field, name = key.split('/', 2)
        rows.append(reference_row(f'm33-qualification/{key}', field, name, ref, order))
    baseline_links = []
    for path in paths[5:7]:
        manifest = json.loads((root / path).read_text())
        for c in manifest['instances']:
            params = c['params']
            key = f'{params["field"]}__{params["name"]}'
            reference = refs.get(key)
            baseline_links.append(dict(manifest=path, name=c['name'],
                                       final_input_digest=reference['input_digest'] if reference else None,
                                       input_files=c['inputs']))
            if reference is None:
                unresolved.append(dict(id=f'{path}:{c["name"]}', reason='no final reference for baseline row'))
    final_rows = [r for r in rows if r['id'].startswith('m33-final/')]
    historical = dict(protocol='M33 original family-size/seed draw; not an M34 freeze',
                      unknown_support_ids=[r['id'] for r in final_rows if r['support_id'] is None])
    for label, key in [('S1_formulation_crossings', 'formulation_id'), ('S2_family_crossings', 'family_id')]:
        members = defaultdict(list)
        for r in final_rows:
            members[r[key]].append(r)
        historical[label] = {k: [dict(id=r['id'], partition=r['partition']) for r in v]
                             for k, v in sorted(members.items()) if len({r['partition'] for r in v}) > 1}
    groups = {}
    for key in ('support_id', 'formulation_id', 'family_id', 'source_id', 'normalized_input_digest', 'legacy_digest'):
        members = defaultdict(list)
        for r in rows:
            if r[key] is not None:
                members[r[key]].append(r['id'])
        groups[key] = {k: sorted(v) for k, v in sorted(members.items()) if len(v) > 1}
    return dict(schema='legacy-corpus-audit-v1', sources=sources, counts=dict(wide=len(wide), public=len(public),
                upstream_candidates=len(inventory), m33_candidates=sum(map(len, candidates.values())),
                m33_held_out=sum(map(len, held.values())), m33_final_reference_entries=len(refs),
                m33_qualification_entries=len(qualification)),
                rows=sorted(rows, key=lambda r: r['id']), groups=groups, unresolved=unresolved,
                baseline_links=baseline_links, historical_split=historical,
                upstream_decisions=[dict(path=c['path'], sha256=c['sha256'], decision=c['decision']) for c in inventory])


def load(path):
    def unique(pairs):
        value = {}
        for key, item in pairs:
            if key in value:
                raise ValueError(f'duplicate JSON property {key}')
            value[key] = item
        return value
    value = json.loads(Path(path).read_text(), object_pairs_hook=unique,
                       parse_constant=lambda value: (_ for _ in ()).throw(ValueError(f'nonfinite JSON value {value}')))
    encoded(value)  # Also reject overflowed numeric literals such as 1e9999.
    return value


def main():
    parser = argparse.ArgumentParser(description='Validate instance lineage and check declared corpus splits; never runs a solver.')
    commands = parser.add_subparsers(dest='command', required=True)
    for name in ('validate', 'check'):
        p = commands.add_parser(name)
        p.add_argument('catalog')
        if name == 'check':
            p.add_argument('split')
    p = commands.add_parser('draw')
    p.add_argument('catalog')
    p.add_argument('--protocol', choices=['S1', 'S2', 'S4'], required=True)
    p.add_argument('--salt', required=True)
    p.add_argument('--evaluation-groups', type=int, required=True)
    p.add_argument('--exposed', required=True, help='JSON array of previously exposed instance ids')
    p = commands.add_parser('audit')
    p.add_argument('--root', type=Path, default=ROOT)
    args = parser.parse_args()
    try:
        if args.command == 'audit':
            print(json.dumps(audit(args.root), indent=2, sort_keys=True))
            return 0
        records = load(args.catalog)
        if not isinstance(records, list) or not records:
            raise ValueError('catalog must be a nonempty array')
        for r in records:
            validate_record(r)
        presentation_roots(records)
        if args.command == 'draw':
            result = draw_split(records, args.protocol, args.salt, args.evaluation_groups, load(args.exposed))
            errors = check_split(records, result)
            if errors:
                raise ValueError('; '.join(errors))
            print(json.dumps(result, indent=2, sort_keys=True))
            return 0
        errors = check_split(records, load(args.split)) if args.command == 'check' else []
        print(json.dumps(dict(valid=not errors, instances=len(records), errors=errors), indent=2))
        return 1 if errors else 0
    except (OSError, ValueError, KeyError, TypeError, IndexError) as error:
        print(f'error: {error}', file=sys.stderr)
        return 2


if __name__ == '__main__':
    sys.exit(main())
