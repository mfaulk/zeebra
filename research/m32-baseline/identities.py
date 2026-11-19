#!/usr/bin/env python3
"""#939 freeze identities (plan §8.3, F0): the M31 reference, the M32 baseline and the held-out pin
build, each from a `git archive` of its commit, with the timed `src/` diffs that tie them together.

Comparands are not run by the freeze; M32 reuses M30-0's by digest, recorded here by that file's
SHA-256 (#935 re-measures groebner-rs at 1/4/8/16 workers).

    python3 research/m32-baseline/identities.py --bins BINDIR --pin COMMIT > identities.json
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
FREEZE = json.loads((HERE / 'pins.json').read_text())['freeze']
TIMED = ['src', 'Cargo.toml', 'Cargo.lock', '.cargo']
EXAMPLES = ('sig_f4_study', 'm29_cost_model', 'zeebra_driver', 'wide_corpus')


def code_lines(a, b):
    """Changed lines in the timed tree that are neither comments nor doc attributes."""
    diff = m29.sh('git', 'diff', '-U0', a, b, '--', *TIMED).splitlines()
    return [l for l in diff if l[:1] in '+-' and not l.startswith(('+++', '---'))
            and l[1:].strip() and not l[1:].strip().startswith(('//', '#[doc'))]


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--bins', type=Path, required=True, help='BINDIR/{ref,base,pin}/<example>')
    p.add_argument('--pin', required=True, help='the commit the pin build was archived from')
    a = p.parse_args()
    ref, base = FREEZE['reference']['commit'], FREEZE['baseline']['commit']
    pin = m29.sh('git', 'rev-parse', a.pin)
    m30 = ROOT / 'research/m30-baseline/identities.json'
    doc = dict(
        schema=1,
        freeze=FREEZE,
        pin_build=dict(commit=pin, what='baseline + #939 held-out inputs in examples/sig_f4_study.rs; '
                                         'used only for the admission read'),
        timed_diffs={
            'reference..baseline': m29.sh('git', 'diff', '--stat', ref, base, '--', *TIMED),
            'reference..baseline code lines (not // or #[doc])': code_lines(ref, base),
            'e59a90a1..baseline': m29.sh('git', 'diff', '--stat', 'e59a90a1', base, '--', *TIMED) or 'identical',
            'baseline..pin': m29.sh('git', 'diff', '--stat', base, pin, '--', *TIMED, 'examples') or 'identical',
        },
        rustc=m29.sh('rustc', '-vV'),
        build='git archive of each commit; cargo build --release --locked --features research-sigf4; '
              'fat LTO, codegen-units=1 (Cargo.toml), x86-64-v3 (.cargo/config.toml); RUSTC_WRAPPER="", '
              'CARGO_INCREMENTAL=0; private CARGO_TARGET_DIR under /buildcache/cargo-target/zeebra-939',
        executables={label: {name: m29.identity(a.bins / label / name) for name in EXAMPLES
                             if (a.bins / label / name).exists()} for label in ('ref', 'base', 'pin')},
        options=dict(
            f4='F4Options::default() with parallel_forward and parallel_symbolic Serial at 1 worker, '
               'Auto { max_workers: w } otherwise (sig_f4_study::f4_options)',
            entry='grobner::f4_signature under the same options, pre-solve dispatch included',
            wall_cap_s=180, rss_cap_kib=8 * 2**20,
            placement='taskset CPUs 8..8+w-1 inside bench-reserve CCDs 1-2'),
        fields=dict(goldilocks='PrimeFieldElement64<2^64-2^32+1>', wide64='PrimeFieldElement64<2^64-353>',
                    gf32003='Zp32003', m31='Zp2147483647'),
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
