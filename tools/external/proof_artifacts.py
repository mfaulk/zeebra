"""Lossless, content-addressed storage for large repeated subprocess proof responses."""
import gzip
import hashlib
import json
import re
from pathlib import Path
import sys


def pack_attempts(attempts, output):
    output = Path(output)
    proof_dir = output.parent / (output.name.removesuffix('.gz').removesuffix('.json') + '-proofs')
    decoder = json.JSONDecoder()
    for attempt in attempts:
        artifacts = attempt['artifacts']
        raw = artifacts.get('raw_output')
        if not raw:
            continue
        decoded = json.loads(raw)
        for key in ('cofactors', 'certificate'):
            if not isinstance(decoded.get(key), str):
                continue
            for match in re.finditer(r'"' + key + r'"\s*:\s*', raw):
                value, end = decoder.raw_decode(raw, match.end())
                if value != decoded[key]:
                    continue
                literal = raw[match.end():end].encode('utf-8')
                digest = hashlib.sha256(literal).hexdigest()
                proof_dir.mkdir(parents=True, exist_ok=True)
                payload = proof_dir / (digest + '.json-string.gz')
                if not payload.exists():
                    with payload.open('wb') as destination:
                        with gzip.GzipFile(filename='', mode='wb', fileobj=destination, mtime=0) as compressed:
                            compressed.write(literal)
                parts = {'prefix': raw[:match.end()], 'payload': str(payload.relative_to(output.parent)),
                         'suffix': raw[end:], 'sha256': digest, 'uncompressed_bytes': len(literal)}
                artifacts['raw_output_parts'] = parts
                del artifacts['raw_output']
                if restore_response(artifacts, output.parent) != raw:
                    raise ValueError('proof packing changed the original response')
                break
            else:
                raise ValueError('could not locate the proof literal')
            break


def restore_response(artifacts, parent):
    if 'raw_output_parts' not in artifacts:
        return artifacts.get('raw_output')
    parts = artifacts['raw_output_parts']
    with gzip.open(Path(parent) / parts['payload'], 'rb') as compressed:
        literal = compressed.read()
    if hashlib.sha256(literal).hexdigest() != parts['sha256']:
        raise ValueError('compressed proof does not match its SHA-256')
    return parts['prefix'] + literal.decode('utf-8') + parts['suffix']


def load_cohort(path):
    path = Path(path)
    opener = gzip.open if path.suffix == '.gz' else open
    with opener(path, 'rt', encoding='utf-8') as source:
        return json.load(source)


def write_cohort(path, value):
    path = Path(path)
    data = (json.dumps(value, indent=2, ensure_ascii=False) + '\n').encode('utf-8')
    if path.suffix == '.gz':
        with path.open('wb') as destination:
            with gzip.GzipFile(filename='', mode='wb', fileobj=destination, mtime=0) as compressed:
                compressed.write(data)
    else:
        path.write_bytes(data)


if __name__ == '__main__':
    cohort_path = Path(sys.argv[1])
    cohort = load_cohort(cohort_path)
    print(restore_response(cohort['attempts'][int(sys.argv[2])]['artifacts'], cohort_path.parent), end='')
