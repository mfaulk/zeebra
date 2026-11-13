"""Pack repeated basis literals while preserving a study's exact stdout and metadata."""
import copy
import importlib.util
import json
from pathlib import Path

_SPEC = importlib.util.spec_from_file_location('proof_artifacts', Path(__file__).with_name('proof_artifacts.py'))
_PROOFS = importlib.util.module_from_spec(_SPEC)
_SPEC.loader.exec_module(_PROOFS)
_MARKER = '_study_artifact_storage'


def pack_attempt(attempt, output, keys=('basis',)):
    """Pack one complete response without retaining earlier response literals in memory."""
    packed = copy.deepcopy(attempt)
    if _MARKER in packed:
        raise ValueError('study storage marker already present')
    stdout = packed.get('stdout')
    if not isinstance(stdout, str) or json.loads(stdout) != packed.get('raw'):
        raise ValueError('stdout differs from parsed raw response')
    had_artifacts = 'artifacts' in packed
    artifacts = packed.setdefault('artifacts', {})
    if not isinstance(artifacts, dict) or any(k in artifacts for k in ('raw_output', 'raw_output_parts')):
        raise ValueError('existing response artifacts conflict with study packing')
    artifacts['raw_output'] = packed.pop('stdout')
    del packed['raw']
    packed[_MARKER] = {'had_artifacts': had_artifacts}
    _PROOFS.pack_attempts([packed], output, keys=keys)
    return packed


def pack_study(cohort, output):
    """Write a losslessly packed copy, leaving the caller's cohort unchanged."""
    output = Path(output)
    packed = copy.deepcopy(cohort)
    packed['attempts'] = [pack_attempt(a, output) if a.get('status') == 'verified' else a
                          for a in packed['attempts']]
    _PROOFS.write_cohort(output, packed)
    if load_study(output) != cohort:
        raise ValueError('study packing changed metadata or response bytes')
    return packed


def _restore(attempt, parent):
    attempt = copy.deepcopy(attempt)
    marker = attempt.pop(_MARKER, None)
    if marker is not None:
        artifacts = attempt['artifacts']
        stdout = _PROOFS.restore_response(artifacts, parent)
        attempt['stdout'] = stdout
        attempt['raw'] = json.loads(stdout)
        artifacts.pop('raw_output', None)
        artifacts.pop('raw_output_parts', None)
        if not marker['had_artifacts']:
            if artifacts:
                raise ValueError('unexpected metadata in generated study artifacts')
            del attempt['artifacts']
    return attempt


def iter_attempts(path):
    """Restore and hash-check one response at a time for large certificate cohorts."""
    path = Path(path)
    for attempt in _PROOFS.load_cohort(path)['attempts']:
        yield _restore(attempt, path.parent)


def load_study(path):
    path = Path(path)
    cohort = _PROOFS.load_cohort(path)
    cohort['attempts'] = [_restore(a, path.parent) for a in cohort['attempts']]
    return cohort


if __name__ == '__main__':
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input', type=Path, help='unpacked native cohort JSON or JSON.gz')
    parser.add_argument('output', type=Path, help='packed cohort JSON.gz and adjacent payload directory')
    args = parser.parse_args()
    pack_study(_PROOFS.load_cohort(args.input), args.output)
