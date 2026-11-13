"""Pack repeated basis literals while preserving a study's exact stdout and metadata."""
import copy
import importlib.util
import json
from pathlib import Path

_SPEC = importlib.util.spec_from_file_location('proof_artifacts', Path(__file__).with_name('proof_artifacts.py'))
_PROOFS = importlib.util.module_from_spec(_SPEC)
_SPEC.loader.exec_module(_PROOFS)
_MARKER = '_study_artifact_storage'


def pack_study(cohort, output):
    """Write a losslessly packed copy, leaving the caller's cohort unchanged."""
    output = Path(output)
    packed = copy.deepcopy(cohort)
    for attempt in packed['attempts']:
        if attempt.get('status') != 'verified':
            continue
        if _MARKER in attempt:
            raise ValueError('study storage marker already present')
        stdout = attempt.get('stdout')
        if not isinstance(stdout, str) or json.loads(stdout) != attempt.get('raw'):
            raise ValueError('stdout differs from parsed raw response')
        had_artifacts = 'artifacts' in attempt
        artifacts = attempt.setdefault('artifacts', {})
        if not isinstance(artifacts, dict) or any(k in artifacts for k in ('raw_output', 'raw_output_parts')):
            raise ValueError('existing response artifacts conflict with study packing')
        artifacts['raw_output'] = attempt.pop('stdout')
        del attempt['raw']
        attempt[_MARKER] = {'had_artifacts': had_artifacts}
        _PROOFS.pack_attempts([attempt], output, keys=('basis',))
    _PROOFS.write_cohort(output, packed)
    if load_study(output) != cohort:
        raise ValueError('study packing changed metadata or response bytes')
    return packed


def load_study(path):
    """Restore the original study representation from its content-addressed payloads."""
    path = Path(path)
    cohort = _PROOFS.load_cohort(path)
    for attempt in cohort['attempts']:
        marker = attempt.pop(_MARKER, None)
        if marker is None:
            continue
        artifacts = attempt['artifacts']
        stdout = _PROOFS.restore_response(artifacts, path.parent)
        attempt['stdout'] = stdout
        attempt['raw'] = json.loads(stdout)
        artifacts.pop('raw_output', None)
        artifacts.pop('raw_output_parts', None)
        if not marker['had_artifacts']:
            if artifacts:
                raise ValueError('unexpected metadata in generated study artifacts')
            del attempt['artifacts']
    return cohort


if __name__ == '__main__':
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input', type=Path, help='unpacked native cohort JSON or JSON.gz')
    parser.add_argument('output', type=Path, help='packed cohort JSON.gz and adjacent payload directory')
    args = parser.parse_args()
    pack_study(_PROOFS.load_cohort(args.input), args.output)
