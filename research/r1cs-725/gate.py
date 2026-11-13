#!/usr/bin/env python3
"""Reconstruct the independent reader's rows before choosing the Rust adapter boundary."""
import argparse
import hashlib
import itertools
import json
import math
import pathlib
import struct
import subprocess


def section(kind, payload):
    return struct.pack('<IQ', kind, len(payload)) + payload


def encode(model):
    n8 = model['n8']
    header = struct.pack('<I', n8) + int(model['prime']).to_bytes(n8, 'little')
    header += struct.pack('<IIIIQI', model['nWires'], model['nPublicOutputs'],
                          model['nPublicInputs'], model['nPrivateInputs'],
                          model['nLabels'], model['nConstraints'])
    rows = bytearray()
    for row in model['constraints']:
        for lc in row:
            rows += struct.pack('<I', len(lc))
            for wire, coefficient in sorted(lc.items(), key=lambda pair: int(pair[0])):
                rows += struct.pack('<I', int(wire)) + int(coefficient).to_bytes(n8, 'little')
    mapping = b''.join(struct.pack('<Q', label) for label in model['map'])
    return b'r1cs' + struct.pack('<II', 1, 3) + section(1, header) + section(2, rows) + section(3, mapping)


def expand(row, n):
    terms = {}
    def add(wires, value):
        powers = [0] * n
        for wire in wires:
            if wire:
                powers[wire - 1] += 1
        key = tuple(powers)
        terms[key] = terms.get(key, 0) + value
    for i, a in row[0].items():
        for j, b in row[1].items():
            add([int(i), int(j)], int(a) * int(b))
    for i, c in row[2].items():
        add([int(i)], -int(c))
    return terms


def sparse_residual(row, wires, p):
    dots = [sum(int(value) * wires[int(wire)] for wire, value in lc.items()) % p for lc in row]
    return (dots[0] * dots[1] - dots[2]) % p


def polynomial_residual(terms, point, p):
    return sum(c * math.prod(pow(x, e, p) for x, e in zip(point, powers))
               for powers, c in terms.items()) % p


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--reader-repo', type=pathlib.Path, required=True)
    parser.add_argument('--output', type=pathlib.Path, required=True)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    root = pathlib.Path(__file__).resolve().parents[2]
    reference = args.reader_repo / 'test/testutils/example.r1cs'
    own = root / 'tests/fixtures/r1cs/multiplier.r1cs'
    script = root / 'research/r1cs-725/reader-oracle.mjs'
    revision = subprocess.check_output(['git', '-C', str(args.reader_repo), 'rev-parse', 'HEAD'], text=True).strip()
    assert revision == 'd82959da1f88fbd06db0407051fde94afbf8824a'
    def read(*files):
        output = subprocess.check_output(['node', str(script), str(args.reader_repo), *map(str, files)], text=True)
        return json.loads(output)
    models = read(reference, own)
    (args.output / 'oracle.json').write_text(json.dumps(models, indent=2) + '\n')
    report = []
    for number, model in enumerate(models):
        raw = pathlib.Path(model['file']).read_bytes()
        canonical = encode(model)
        destination = args.output / f'canonical-{number}.r1cs'
        destination.write_bytes(canonical)
        n = model['nWires'] - 1
        assert n <= 99
        polynomials = [expand(row, n) for row in model['constraints']]
        report.append({'input': model['file'], 'input_sha256': hashlib.sha256(raw).hexdigest(),
                       'canonical_sha256': hashlib.sha256(canonical).hexdigest(),
                       'wire_count': model['nWires'], 'constraint_count': model['nConstraints'],
                       'capacity': n, 'expanded_terms_before_field_cancellation': [len(t) for t in polynomials],
                       'canonical_file': str(destination)})
    reconstructed = read(*(args.output / f'canonical-{i}.r1cs' for i in range(len(models))))
    assert [{k:v for k,v in row.items() if k != 'file'} for row in models] == [{k:v for k,v in row.items() if k != 'file'} for row in reconstructed]
    rows = [[{'0':'3','1':'1','2':'2'}, {'2':'1','3':'4'}, {'0':'6','3':'1'}],
            [{'0':'1'}, {'1':'1'}, {'3':'1'}], [{}, {'2':'1'}, {}]]
    polys = [expand(row, 3) for row in rows]
    checks = 0
    for point in itertools.product(range(7), repeat=3):
        for row, polynomial in zip(rows, polys):
            assert sparse_residual(row, [1, *point], 7) == polynomial_residual(polynomial, point, 7)
            checks += 1
    witness = list(map(int, json.loads((root / 'research/r1cs-725/producer-witness.json').read_text())['witness']))
    producer = models[1]
    p = int(producer['prime'])
    assert all(sparse_residual(row, witness, p) == 0 for row in producer['constraints'])
    witness[1] += 1
    assert any(sparse_residual(row, witness, p) != 0 for row in producer['constraints'])
    print(json.dumps({'decision':'continue', 'scope':'bounded const-generic adapter; no solver integration',
                      'fixtures':report, 'gf7_assignments':343, 'gf7_row_checks':checks,
                      'independent_reader_roundtrip':'all header counts, coefficients and wire-label mappings agree',
                      'producer_witness_and_perturbation':'agree with original rows'}, indent=2))


if __name__ == '__main__':
    main()
