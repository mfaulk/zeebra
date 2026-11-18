#!/usr/bin/env python3
"""#901 freeze identities: #834's `identities.py` fields for the executables #901 measures.

No comparand runs in #901; the comparand identities are M30-0's (`research/m30-baseline/identities.json`),
reused unchanged as plan §7.1 allows, and recorded here by that file's SHA-256.

    python3 research/m31-baseline/identities.py --bin TIMED_EXAMPLES --split-bin SPLIT_EXAMPLES > identities.json
"""
import argparse
import hashlib
import importlib.util
import json
import platform
from pathlib import Path

HERE = Path(__file__).resolve().parent
_spec = importlib.util.spec_from_file_location('m29_identities', HERE.parent / 'm29-baseline' / 'identities.py')
m29 = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(m29)
ROOT = m29.ROOT


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--bin', type=Path, required=True)
    p.add_argument('--split-bin', type=Path, required=True)
    a = p.parse_args()
    m30 = ROOT / 'research/m30-baseline/identities.json'
    doc = dict(
        schema=1,
        zeebra=dict(
            head=m29.sh('git', 'rev-parse', 'HEAD'),
            freeze=json.loads((HERE / 'pins.json').read_text())['freeze'],
            origin_main=m29.sh('git', 'rev-parse', 'origin/main'),
            # Library changes are feature-gated (research-sigf4-split), absent from the timed binary.
            src_diff_vs_freeze=m29.sh('git', 'diff', '--stat', 'acbaf12c840d5ccea52b10388cc850ed6e8a5236',
                                      'HEAD', '--', 'src', 'Cargo.lock'),
            rustc=m29.sh('rustc', '-vV'),
            build='release; fat LTO; codegen-units=1; x86-64-v3 (.cargo/config.toml); RUSTC_WRAPPER=""',
            features=dict(timed='research-sigf4 (+ default external-runners)',
                          split='research-sigf4-split'),
            executables={name: m29.identity(a.bin / name) for name in
                         ('sig_f4_study', 'm29_cost_model', 'zeebra_driver', 'wide_corpus')},
            split_executable=m29.identity(a.split_bin / 'sig_f4_study'),
            options=dict(
                f4='F4Options::default() with parallel_forward and parallel_symbolic Serial at 1 worker, '
                   'Auto { max_workers: w } otherwise (sig_f4_study::f4_options; m29_cost_model likewise)',
                sigf4='SigF4Options::default() with workers = 1 (design 1) or 16 (design 2: parallel '
                      'pre-reduction against the reducer block; symbolic and the cascade serial)',
                symbolic_team='F4: ParallelSymbolic::Auto { max_workers: w }, clamped to available '
                              'parallelism (#895); signature engine: serial symbolic',
                wall_cap_s=180, rss_cap_kib=8 * 2**20, placement='taskset CPUs 8..8+w-1 inside '
                'bench-reserve CCDs 1-2'),
        ),
        comparands=dict(reused_from='research/m30-baseline/identities.json',
                        sha256=hashlib.sha256(m30.read_bytes()).hexdigest() if m30.exists() else None),
        host=dict(
            machine='5995wx',
            cpu=next((l.split(':', 1)[1].strip() for l in Path('/proc/cpuinfo').read_text().splitlines()
                      if l.startswith('model name')), 'unknown'),
            kernel=platform.release(),
            governor=Path('/sys/devices/system/cpu/cpu8/cpufreq/scaling_governor').read_text().strip(),
            boost=Path('/sys/devices/system/cpu/cpufreq/boost').read_text().strip(),
        ),
    )
    print(json.dumps(doc, indent=1, sort_keys=True))


if __name__ == '__main__':
    main()
