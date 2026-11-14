#!/usr/bin/env python3
"""Crash-safe, append-only attempt journal for bounded study controllers (#764).

A controller records each child's raw output and exit metadata once, durably, before it parses or
checks anything, then appends the verdict as a separate record. Nothing is rewritten while the
controller's budget is running; `render` repacks the cohort offline. Entries are self-digested and
hash-chained, payloads are content-addressed, and a torn tail is quarantined only on request.
Lost metadata is never reconstructed: an exit that did not become durable is not an attempt.
"""
import argparse
import base64
import gzip
import hashlib
import json
import os
from pathlib import Path

HEADER = 'header.json'
JOURNAL = 'journal.jsonl'
BLOBS = 'blobs'
REQUIRED_METADATA = ('process_wall_ns', 'wall_seconds', 'cpu_seconds', 'observed_peak_rss_bytes',
                     'exit', 'stop', 'guard')
_RESERVED = {'plan', 'limits', 'attempts', 'stop', 'quarantined', 'journal_sha256', 'storage'}


def _canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'), ensure_ascii=False).encode()


def _sha(data):
    return hashlib.sha256(data).hexdigest()


def _fsync_dir(path):
    fd = os.open(path, os.O_RDONLY)
    try:
        os.fsync(fd)
    finally:
        os.close(fd)


def _atomic_write(path, data):
    tmp = path.with_name(path.name + '.tmp')
    with open(tmp, 'wb') as f:
        f.write(data)
        f.flush()
        os.fsync(f.fileno())
    tmp.replace(path)
    _fsync_dir(path.parent)


def _plain(value):
    return json.loads(_canonical(value))


def _read_header(directory):
    header = json.loads((directory / HEADER).read_bytes())
    return header, _sha((directory / HEADER).read_bytes())


def _blob(directory, digest):
    path = directory / BLOBS / (digest + '.gz')
    try:
        data = gzip.decompress(path.read_bytes())
    except (OSError, EOFError) as error:
        raise ValueError(f'payload {digest} missing or unreadable: {error}') from None
    if _sha(data) != digest:
        raise ValueError(f'payload {digest} content changed')
    return data


def _entries(directory, header_sha):
    """Parse and chain-check every complete journal line; refuse a torn tail."""
    raw = (directory / JOURNAL).read_bytes()
    if raw and not raw.endswith(b'\n'):
        raise ValueError('torn journal record; reopen with quarantine_torn=True to set it aside')
    prev = header_sha
    entries = []
    for line in raw.splitlines(keepends=True):
        entry = json.loads(line)
        digest = entry.pop('digest', None)
        if digest != _sha(_canonical(entry)) or entry.get('prev') != prev:
            raise ValueError(f'journal chain broken at record {len(entries)}')
        prev = _sha(line)
        entries.append(dict(entry, digest=digest))
    return entries, prev


def _replay(directory, header, entries):
    plan = header['plan']
    attempts, quarantined, stop = [], [], None
    for entry in entries:
        kind = entry['kind']
        if stop is not None:
            raise ValueError('journal continues after its stop record')
        if kind == 'exit':
            index = entry['index']
            if index != len(attempts) or index >= len(plan) or entry['cell'] != plan[index]:
                raise ValueError(f'exit record {index} out of plan order')
            attempts.append(dict(index=index, cell=entry['cell'], metadata=entry['metadata'],
                                 stdout_sha256=entry['stdout'], stderr_sha256=entry['stderr'],
                                 status='unverified', verdict=None, exit_digest=entry['digest']))
        elif kind == 'verdict':
            index = entry['index']
            if index >= len(attempts) or attempts[index]['verdict'] is not None \
                    or attempts[index]['exit_digest'] != entry['exit_digest']:
                raise ValueError(f'verdict record for {index} has no unique exit record')
            attempts[index].update(status=entry['status'], verdict=entry['details'])
        elif kind == 'quarantine':
            path = directory / entry['file']
            if not path.exists() or _sha(path.read_bytes()) != entry['sha256']:
                raise ValueError(f'quarantined payload {entry["file"]} changed')
            quarantined.append(entry['file'])
        elif kind == 'stop':
            stop = entry['values']
        else:
            raise ValueError(f'unknown journal record kind {kind!r}')
    return attempts, quarantined, stop


class StudyJournal:
    """Writer side. `create` once per campaign; `open` to resume after an interruption."""

    def __init__(self, directory, header, limits, entries, tail):
        self.directory = directory
        self.header = header
        self.limits = limits
        self._tail = tail
        self.bytes_written = 0
        self.attempts, _, stop = _replay(directory, header, entries)
        self.stopped = stop is not None
        self.next_index = len(self.attempts)
        self.child_wall_seconds = sum(a['metadata']['wall_seconds'] for a in self.attempts)
        referenced = {d for a in self.attempts for d in (a['stdout_sha256'], a['stderr_sha256'])}
        self._blobs = set(referenced)
        self.retained_bytes = sum(p.stat().st_size for p in (directory / HEADER, directory / JOURNAL)) + \
            sum((directory / BLOBS / (d + '.gz')).stat().st_size for d in referenced)

    @classmethod
    def create(cls, directory, header, plan, limits):
        directory = Path(directory)
        if _RESERVED & set(header):
            raise ValueError(f'header uses reserved keys {sorted(_RESERVED & set(header))}')
        directory.mkdir(parents=True, exist_ok=False)
        (directory / BLOBS).mkdir()
        document = _plain(dict(header=header, plan=plan, limits=limits))
        _atomic_write(directory / HEADER, _canonical(document) + b'\n')
        _atomic_write(directory / JOURNAL, b'')
        _, header_sha = _read_header(directory)
        return cls(directory, document, document['limits'], [], header_sha)

    @classmethod
    def open(cls, directory, header, plan, limits, quarantine_torn=False):
        directory = Path(directory)
        document, header_sha = _read_header(directory)
        if document != _plain(dict(header=header, plan=plan, limits=limits)):
            raise ValueError('frozen identity, plan or limits differ from the journal header')
        journal = directory / JOURNAL
        raw = journal.read_bytes()
        torn = b''
        if raw and not raw.endswith(b'\n'):
            if not quarantine_torn:
                raise ValueError('torn journal record; reopen with quarantine_torn=True to set it aside')
            keep = raw.rfind(b'\n') + 1
            torn = raw[keep:]
            name = f'torn-{keep}.partial'
            _atomic_write(directory / name, torn)
            with open(journal, 'r+b') as f:
                f.truncate(keep)
                f.flush()
                os.fsync(f.fileno())
        entries, tail = _entries(directory, header_sha)
        journal_ = cls(directory, document, document['limits'], entries, tail)
        if torn:
            journal_._append(dict(kind='quarantine', file=name, sha256=_sha(torn), bytes=len(torn)))
        return journal_

    def _append(self, entry):
        entry = dict(entry, prev=self._tail)
        entry['digest'] = _sha(_canonical(entry))
        line = _canonical(entry) + b'\n'
        with open(self.directory / JOURNAL, 'ab') as f:
            f.write(line)
            f.flush()
            os.fsync(f.fileno())
        self._tail = _sha(line)
        self.bytes_written += len(line)
        self.retained_bytes += len(line)
        return entry

    def _store(self, data):
        digest = _sha(data)
        if digest in self._blobs:
            return digest
        path = self.directory / BLOBS / (digest + '.gz')
        if path.exists():
            _blob(self.directory, digest)
        else:
            packed = gzip.compress(data, compresslevel=6, mtime=0)
            _atomic_write(path, packed)
            self.bytes_written += len(packed)
            self.retained_bytes += len(packed)
        self._blobs.add(digest)
        return digest

    def record_exit(self, index, cell, stdout, stderr, metadata):
        """Persist one finished child before any parsing; returns the exit record's digest."""
        if self.stopped:
            raise ValueError('journal is stopped; start a new campaign to measure more')
        if index != self.next_index:
            raise ValueError(f'exit index {index} is not the next plan index {self.next_index}')
        plan = self.header['plan']
        if index >= len(plan) or _plain(cell) != plan[index]:
            raise ValueError(f'cell {cell!r} is not plan entry {index}')
        missing = [k for k in REQUIRED_METADATA if k not in metadata]
        if missing:
            raise ValueError(f'exit metadata lacks {", ".join(missing)}; lost metadata is never inferred')
        entry = self._append(dict(kind='exit', index=index, cell=_plain(cell), metadata=_plain(metadata),
                                  stdout=self._store(bytes(stdout)), stderr=self._store(bytes(stderr))))
        self.attempts.append(dict(index=index, exit_digest=entry['digest'], verdict=None))
        self.next_index += 1
        self.child_wall_seconds += metadata['wall_seconds']
        return entry['digest']

    def record_verdict(self, index, status, details):
        if status == 'unverified':
            raise ValueError('unverified is the absence of a verdict, not a verdict')
        if index >= len(self.attempts) or self.attempts[index]['verdict'] is not None:
            raise ValueError(f'attempt {index} has no exit record or already has a verdict')
        self._append(dict(kind='verdict', index=index, exit_digest=self.attempts[index]['exit_digest'],
                          status=status, details=_plain(details)))
        self.attempts[index]['verdict'] = status

    def refusal(self, next_child_wall_seconds):
        """The budget refusal the controller must record instead of launching, or None."""
        wall = self.limits['aggregate_wall_seconds']
        if self.child_wall_seconds + next_child_wall_seconds > wall:
            return dict(reason='aggregate-wall', child_wall_seconds=self.child_wall_seconds,
                        next_child_wall_seconds=next_child_wall_seconds, limit=wall)
        if self.retained_bytes >= self.limits['output_bytes']:
            return dict(reason='output-bytes', retained_bytes=self.retained_bytes,
                        limit=self.limits['output_bytes'])
        return None

    def record_stop(self, reason, **values):
        if self.stopped:
            raise ValueError('journal is already stopped')
        self._append(dict(kind='stop', values=_plain(dict(values, reason=reason))))
        self.stopped = True


def load(directory):
    """Verify every record and payload; return the cohort with raw bytes restored."""
    directory = Path(directory)
    document, header_sha = _read_header(directory)
    entries, _ = _entries(directory, header_sha)
    attempts, quarantined, stop = _replay(directory, document, entries)
    for attempt in attempts:
        attempt['stdout'] = _blob(directory, attempt.pop('stdout_sha256'))
        attempt['stderr'] = _blob(directory, attempt.pop('stderr_sha256'))
        attempt.pop('exit_digest')
    return dict(header=document['header'], plan=document['plan'], limits=document['limits'],
                attempts=attempts, quarantined=quarantined, stop=stop,
                journal_sha256=_sha((directory / JOURNAL).read_bytes()))


def _text(data, key):
    try:
        return {key: data.decode()}
    except UnicodeDecodeError:
        return {key + '_base64': base64.b64encode(data).decode()}


def render(directory, output):
    """Deterministic offline repack into one cohort document, verified after it is written."""
    state = load(directory)
    attempts = []
    for a in state['attempts']:
        row = dict(index=a['index'], cell=a['cell'], metadata=a['metadata'], status=a['status'],
                   verdict=a['verdict'])
        row.update(_text(a['stdout'], 'stdout'))
        row.update(_text(a['stderr'], 'stderr'))
        attempts.append(row)
    cohort = dict(state['header'], storage='study-journal-render-v1', plan=state['plan'],
                  limits=state['limits'], attempts=attempts, stop=state['stop'],
                  quarantined=state['quarantined'], journal_sha256=state['journal_sha256'])
    output = Path(output)
    payload = json.dumps(cohort, sort_keys=True, indent=1, ensure_ascii=False).encode() + b'\n'
    data = gzip.compress(payload, compresslevel=9, mtime=0) if output.suffix == '.gz' else payload
    _atomic_write(output, data)
    written = output.read_bytes()
    if (gzip.decompress(written) if output.suffix == '.gz' else written) != payload:
        raise ValueError('rendered cohort did not round-trip')
    return cohort


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = parser.add_subparsers(dest='command', required=True)
    verify = sub.add_parser('verify', help='check every record and payload of a journal')
    verify.add_argument('journal', type=Path)
    publish = sub.add_parser('render', help='repack a journal into one deterministic cohort file')
    publish.add_argument('journal', type=Path)
    publish.add_argument('output', type=Path)
    args = parser.parse_args()
    if args.command == 'verify':
        state = load(args.journal)
        counts = {}
        for a in state['attempts']:
            counts[a['status']] = counts.get(a['status'], 0) + 1
        print(json.dumps(dict(attempts=len(state['attempts']), statuses=counts, stop=state['stop'],
                              quarantined=state['quarantined'], journal_sha256=state['journal_sha256'])))
    else:
        render(args.journal, args.output)


if __name__ == '__main__':
    main()
