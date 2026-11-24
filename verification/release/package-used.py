#!/usr/bin/env python3
"""Build or stage the reviewed Lean source release without runtime caches."""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import shutil
import stat
import zipfile

EXCLUDED_PARTS = {'.lake', '.git', '__pycache__', 'tmp'}
EXCLUDED_SUFFIXES = {'.olean', '.ilean', '.olean.private', '.olean.server',
                     '.pyc', '.ndjson', '.o', '.so', '.a', '.trace'}
EXCLUDED_NAMES = {'SHA256SUMS', 'RELEASE_INVENTORY.json', 'CHECKPOINT_STATUS.md',
                  'CHECKPOINT_STATUS.txt'}


def selected_files(root: Path):
    for path in sorted(root.rglob('*')):
        rel = path.relative_to(root)
        if EXCLUDED_PARTS.intersection(rel.parts) or path.name in EXCLUDED_NAMES:
            continue
        if path.is_symlink():
            raise ValueError(f'Refusing source symlink: {rel}')
        if not path.is_file():
            continue
        if path.suffix in EXCLUDED_SUFFIXES or path.name.endswith(('.olean.private', '.olean.server')):
            continue
        if path.stat().st_size > 20_000_000:
            raise ValueError(f'Unexpected large release file: {rel}')
        yield rel, path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source', type=Path)
    parser.add_argument('destination', type=Path)
    parser.add_argument('--stage', action='store_true')
    parser.add_argument('--checkpoint', action='store_true')
    args = parser.parse_args()
    root = args.source.resolve()
    pairs = list(selected_files(root))
    if args.stage:
        if args.destination.exists():
            raise ValueError('Stage must be absent; refusing to overwrite an existing checkout')
        args.destination.mkdir(parents=True)
        for rel, source in pairs:
            destination = args.destination / rel
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(source, destination)
        print(json.dumps({'staged_files': len(pairs), 'destination': str(args.destination.resolve())}))
        return

    payload = {rel.as_posix(): path.read_bytes() for rel, path in pairs}
    project_sources = {name: data for name, data in payload.items()
                       if name.endswith('.lean') and not name.startswith(('verification/', 'tests/'))}
    lean_inventory = []
    for name, data in payload.items():
        if not name.endswith('.lean'):
            continue
        source = data.decode('utf-8')
        line_count = len(source.splitlines())
        if source.splitlines()[0].strip() != 'module':
            raise ValueError(f'Missing module header: {name}')
        if line_count > 10_000:
            raise ValueError(f'Oversize Lean source: {name}')
        lean_inventory.append({'path': name, 'lines': line_count, 'bytes': len(data),
                               'sha256': hashlib.sha256(data).hexdigest()})
    if len(payload['Challenge.lean']) > 102400 or len(payload['Challenge.lean'].splitlines()) > 1000:
        raise ValueError('Challenge exceeds Palomar source-size limits')
    if args.checkpoint:
        payload['CHECKPOINT_STATUS.md'] = (
            '# Working checkpoint\n\n'
            'The new mathematical modules compile individually. The final integrated\n'
            'build, audit, and certificate checks may still be running.\n'
            'The unconditional theorem for d > 17 is NOT proved. The source\n'
            'contains a conditional reduction with RequiredRelativeLifting.\n'
        ).encode()
    report = {
        'created_utc': datetime.now(timezone.utc).isoformat(),
        'release_scope': 'A and B for d >= 36; conditional reduction for d > 17',
        'unconditional_dimension_18_proved': False,
        'checkpoint': args.checkpoint,
        'project_source_modules': len(project_sources),
        'proof_source_modules': len(project_sources) - 1,
        'all_regular_lean_files': lean_inventory,
        'input_archive_sha256': '7537d4233d74c40aa3eddad5fd4912287810f6a78c6543dbf75cf2fe364e119b',
        'excluded_runtime_artifacts': sorted(EXCLUDED_PARTS | EXCLUDED_SUFFIXES),
        'file_sha256': {name: hashlib.sha256(data).hexdigest() for name, data in payload.items()},
    }
    payload['RELEASE_INVENTORY.json'] = (json.dumps(report, indent=2) + '\n').encode()
    sums = '\n'.join(f'{hashlib.sha256(data).hexdigest()}  {name}'
                      for name, data in sorted(payload.items())) + '\n'
    payload['SHA256SUMS'] = sums.encode()
    prefix = 'akopyan_formalization_updated'
    args.destination.parent.mkdir(parents=True, exist_ok=True)
    with zipfile.ZipFile(args.destination, 'w', compression=zipfile.ZIP_DEFLATED,
                         compresslevel=9) as archive:
        for name, data in sorted(payload.items()):
            info = zipfile.ZipInfo(f'{prefix}/{name}', date_time=(2026, 11, 24, 0, 0, 0))
            info.compress_type = zipfile.ZIP_DEFLATED
            source = root / name
            mode = stat.S_IMODE(source.stat().st_mode) if source.is_file() else 0o644
            info.external_attr = (stat.S_IFREG | mode) << 16
            archive.writestr(info, data, compress_type=zipfile.ZIP_DEFLATED, compresslevel=9)
    with zipfile.ZipFile(args.destination) as archive:
        assert archive.testzip() is None
        for name, data in payload.items():
            assert archive.read(f'{prefix}/{name}') == data
    print(json.dumps({'archive': str(args.destination.resolve()), 'files': len(payload),
                      'project_sources': len(project_sources),
                      'bytes': args.destination.stat().st_size,
                      'sha256': hashlib.sha256(args.destination.read_bytes()).hexdigest()}))


if __name__ == '__main__':
    main()
