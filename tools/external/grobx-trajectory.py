#!/usr/bin/env python3
"""Decode complete grobx reports without losing work discarded by a handover."""
import argparse
import gzip
import json
from pathlib import Path
import re

INTEGER = re.compile(r'^\d+$')
DECIMAL = re.compile(r'^\d+\.\d+$')
STAGES = ('select', 'symbolic', 'encode', 'reduce', 'backsub', 'record', 'decode', 'update')
ROUND_REQUIRED = ('number', 'degree', 'pairs', 'rows', 'given', 'columns', 'entries',
                  'pivots', 'zero', 'reductions', 'subtracted', 'added', 'bands')


def _require(condition, message):
    if not condition:
        raise ValueError(message)


def _fields(tokens, line):
    result = {}
    for token in tokens:
        _require('=' in token, f'malformed report token at line {line}: {token}')
        key, value = token.split('=', 1)
        _require(key and value and key not in result, f'duplicate or empty field at line {line}')
        if INTEGER.fullmatch(value):
            value = int(value)
        elif DECIMAL.fullmatch(value):
            value = float(value)
        elif value in ('yes', 'no'):
            value = value == 'yes'
        result[key] = value
    return result


def _counts(fields, names, context):
    for name in names:
        _require(type(fields.get(name)) is int and fields[name] >= 0,
                 f'{context}: missing or invalid nonnegative count {name}')


def _totals(rounds):
    return {
        'rounds': len(rounds),
        'reductions': sum(r['reductions'] for r in rounds),
        'zero_reductions': sum(r['zero'] for r in rounds),
        'subtracted_entry_charges': sum(r['subtracted'] for r in rounds),
        'added_entry_charges': sum(r['added'] for r in rounds),
        'input_matrix_entries_sum': sum(r['entries'] for r in rounds),
        'max_input_matrix_entries': max((r['entries'] for r in rounds), default=0),
        'new_pivots': sum(r['pivots'] for r in rounds),
    }


def parse_report(report):
    """Return typed events and checked per-run statistics for a completed basis report."""
    result = {'schema': 1, 'runs': [], 'events': []}
    active = None
    previous_clock = -1.0
    ended = False
    for line_number, line in enumerate(report.splitlines(), 1):
        if not line.strip():
            continue
        parts = line.split()
        _require(len(parts) >= 2 and DECIMAL.fullmatch(parts[0]),
                 f'malformed report line {line_number}')
        clock, kind = float(parts[0]), parts[1]
        _require(not ended, f'event after terminal end at line {line_number}')
        _require(clock >= previous_clock, f'report clock decreases at line {line_number}')
        previous_clock = clock
        fields = _fields(parts[2:], line_number)
        event = {'elapsed_seconds': clock, 'kind': kind, 'fields': fields}
        result['events'].append(event)
        if kind in ('call', 'read'):
            _require(kind not in result and active is None, f'duplicate or misplaced {kind}')
            result[kind] = fields
        elif kind == 'run':
            _require('call' in result and 'read' in result, 'run lacks call/read metadata')
            _require(active is None or 'summary' in active, 'new run before previous ran summary')
            _require(fields.get('number') == len(result['runs']) + 1, 'nonsequential run number')
            if active is not None:
                _require(active['summary']['outcome'] == 'handover' and
                         fields.get('engine-by') == 'handover' and fields.get('why') == 'handover',
                         'restart lacks matching handover')
            active = {'config': fields, 'rounds': [], 'handovers': [], 'events': []}
            result['runs'].append(active)
        elif kind in ('inputs', 'echelon', 'round', 'handover', 'inter', 'ran'):
            _require(active is not None and 'summary' not in active, f'misplaced {kind}')
            if kind == 'inputs':
                _require('inputs' not in active and not active['rounds'], 'duplicate or late inputs')
                _counts(fields, ('generators', 'nonzero', 'terms'), 'inputs')
                active['inputs'] = fields
            elif kind == 'echelon':
                _require('inputs' in active and 'echelon' not in active and not active['rounds'],
                         'duplicate or misplaced input echelon')
                _counts(fields, ('generators', 'rows', 'columns', 'subtracted'), 'echelon')
                active['echelon'] = fields
            elif kind == 'round':
                _require('inputs' in active and 'inter' not in active, 'round lacks inputs or follows inter')
                _counts(fields, tuple(k for k in ROUND_REQUIRED if k != 'bands'), 'round')
                _require(type(fields.get('bands')) is bool, 'round lacks bands mode')
                _require(fields['number'] == len(active['rounds']) + 1, 'nonsequential round number')
                _require(fields['given'] <= fields['rows'] and fields['pivots'] <= fields['rows'],
                         'round row counts are inconsistent')
                cells = fields['rows'] * fields['columns']
                _require(fields['entries'] <= cells, 'round entries exceed matrix size')
                for stage in STAGES:
                    _require(type(fields.get(stage)) in (int, float), f'round lacks stage {stage}')
                fields = dict(fields, elapsed_seconds=clock,
                              density=fields['entries'] / cells if cells else 0.0,
                              stages_seconds={k: fields[k] for k in STAGES})
                active['rounds'].append(fields)
            elif kind == 'handover':
                _require(fields.get('round') == len(active['rounds']), 'handover refers to absent round')
                active['handovers'].append(dict(fields, elapsed_seconds=clock))
            elif kind == 'inter':
                _require('inter' not in active, 'duplicate final interreduction')
                _counts(fields, ('rows', 'given', 'columns', 'entries', 'subtracted', 'elements'), 'inter')
                active['inter'] = dict(fields, elapsed_seconds=clock)
            elif kind == 'ran':
                _counts(fields, ('number', 'rounds', 'reduced', 'zero'), 'ran')
                _require(fields['number'] == active['config']['number'], 'ran number differs from run')
                total = _totals(active['rounds'])
                for key, total_key in [('rounds', 'rounds'), ('reduced', 'reductions'), ('zero', 'zero_reductions')]:
                    _require(fields[key] == total[total_key], f'ran {key} disagrees with round sum')
                _require('inputs' in active, 'run lacks original inputs')
                if result['call'].get('echelon') == 'on' and active['config'].get('cofactors') != 'on':
                    _require('echelon' in active, 'run lacks enabled input echelon')
                _require(fields.get('outcome') in ('basis', 'handover'), 'run did not complete or hand over')
                if fields['outcome'] == 'handover':
                    _require('inter' not in active and active['handovers'] and
                             active['handovers'][-1].get('verdict') == 'hand-over',
                             'handover outcome lacks handover decision')
                else:
                    _require('inter' in active, 'completed run lacks final interreduction')
                    _require(fields.get('elements') == active['inter']['elements'],
                             'final basis size differs from interreduction')
                active['summary'] = dict(fields, elapsed_seconds=clock)
                active['totals'] = total
        elif kind == 'end':
            _require(active is not None and active.get('summary', {}).get('outcome') == 'basis',
                     'end lacks completed basis run')
            _require(fields.get('result') == 'basis', 'report did not return a basis')
            result['end'] = fields
            ended = True
        elif active is not None:
            # Passive diagnostics are retained even when emitted after the run summary.
            active['events'].append(event)
    _require(ended, 'incomplete report: terminal end missing')
    runs = result['runs']
    original = {k: runs[0]['inputs'][k] for k in ('generators', 'nonzero', 'terms')}
    for run in runs[1:]:
        _require({k: run['inputs'][k] for k in original} == original, 'restart input shape changed')
    rounds = [r for run in runs for r in run['rounds']]
    result['totals'] = _totals(rounds)
    result['totals'].update({
        'input_echelon_subtracted_entry_charges': sum(r.get('echelon', {}).get('subtracted', 0) for r in runs),
        'interreduction_subtracted_entry_charges': sum(r.get('inter', {}).get('subtracted', 0) for r in runs),
    })
    result['limitations'] = [
        'Subtracted/added entries are upstream budget charges, not exact scalar products or physical memory traffic.',
        'Input matrix entries and their maximum do not measure simultaneous live entries or buffer capacities.',
        'Pair and pivot meanings depend on signature/plain mode; zero counts include combination tests.',
        'Restart input shape is checked, but full input identity and basis verification belong to the caller.',
        'Public Stats after handover omits abandoned runs and final interreduction; this report retains them.',
    ]
    return result


def parse_cohort(cohort):
    """Decode every verified raw MQ10 attempt in an existing comparison cohort."""
    attempts = []
    for index, attempt in enumerate(cohort['attempts']):
        _require(len(attempt.get('rows', [])) == 1, f'attempt {index} must contain exactly one row')
        row = attempt['rows'][0]
        if (row['problem'], row['library'], row['outcome']) != ('mq-random-10', 'grobx', 'verified'):
            continue
        artifacts = attempt['artifacts']
        _require(row['problem_digest'] == artifacts['digest'], f'attempt {index}: input digest mismatch')
        raw = json.loads(artifacts['raw_output'])
        trajectory = parse_report(raw['report'])
        _require(trajectory['read']['characteristic'] == artifacts['modulus'] == row['field']['characteristic'],
                 f'attempt {index}: characteristic mismatch')
        attempts.append({
            'attempt_index': index, 'digest': row['problem_digest'],
            'input': {k: artifacts[k] for k in ('digest', 'variables', 'modulus', 'generators')},
            'row': row, 'trajectory': trajectory,
        })
    _require(attempts, 'cohort contains no verified raw MQ10 attempts')
    return {'schema': 1, 'attempts': attempts}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input', type=Path, help='retained comparison JSON/JSON.gz, or text with --report')
    parser.add_argument('--report', action='store_true', help='parse a single complete engine report')
    parser.add_argument('--output', type=Path, help='write JSON here instead of stdout')
    args = parser.parse_args()
    if args.report:
        result = parse_report(args.input.read_text())
    else:
        opener = gzip.open if args.input.suffix == '.gz' else open
        with opener(args.input, 'rt') as stream:
            result = parse_cohort(json.load(stream))
    payload = json.dumps(result, indent=2, sort_keys=True) + '\n'
    if args.output:
        args.output.write_text(payload)
    else:
        print(payload, end='')


if __name__ == '__main__':
    main()
