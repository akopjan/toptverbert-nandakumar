#!/usr/bin/env python3
"""Validate the source patch or final source ZIP without rebuilding proofs."""
from __future__ import annotations
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path, PurePosixPath
import shutil
import stat
import subprocess
import zipfile

SKIP = {'.git', '.lake', '__pycache__', 'verification'}
SKIP_NAMES = {'SHA256SUMS', 'RELEASE_INVENTORY.json'}


def digest(data):
    return hashlib.sha256(data).hexdigest()


def source_inventory(root):
    entries = {}
    for p in root.rglob('*'):
        rel = p.relative_to(root)
        if SKIP.intersection(rel.parts) or p.name in SKIP_NAMES:
            continue
        if p.is_symlink():
            raise ValueError(f'Unexpected source symlink: {rel}')
        if p.is_file():
            entries[rel.as_posix()] = {'sha256': digest(p.read_bytes()),
                'executable': bool(p.stat().st_mode & stat.S_IXUSR)}
    return entries


def validate_patch(args):
    old, current = source_inventory(args.original), source_inventory(args.source)
    if args.checkout.exists():
        raise ValueError('Patch-check checkout must be absent')
    args.checkout.mkdir(parents=True)
    for name in old:
        dest = args.checkout / name
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(args.original / name, dest)
    runs = []
    for extra in [['--check'], []]:
        cmd = ['git', 'apply', '--whitespace=nowarn', *extra, str(args.patch.resolve())]
        run = subprocess.run(cmd, cwd=args.checkout, text=True, capture_output=True)
        runs.append({'command': cmd, 'exit_code': run.returncode,
                     'stdout': run.stdout, 'stderr': run.stderr})
        if run.returncode:
            raise RuntimeError(json.dumps(runs, indent=2))
    patched = source_inventory(args.checkout)
    missing = sorted(current.keys() - patched.keys())
    extra = sorted(patched.keys() - current.keys())
    different = sorted(k for k in current.keys() & patched.keys() if current[k] != patched[k])
    if missing or extra or different:
        raise RuntimeError(json.dumps({'missing': missing, 'extra': extra, 'different': different}))
    return {'scope': 'All source/configuration/scripts/tests/docs files; verification evidence is distributed in ZIP',
        'patch_sha256': digest(args.patch.read_bytes()), 'patch_bytes': args.patch.stat().st_size,
        'original_files': len(old), 'final_files': len(current),
        'source_bytes_and_executable_modes_match': True,
        'challenge_bytes_unchanged': (args.original/'Challenge.lean').read_bytes() == (args.source/'Challenge.lean').read_bytes(),
        'solution_bytes_unchanged': (args.original/'Solution.lean').read_bytes() == (args.source/'Solution.lean').read_bytes(),
        'commands': runs, 'final_core_files': current}


def validate_archive(args):
    prefix = 'akopyan_formalization_updated/'
    with zipfile.ZipFile(args.archive) as z:
        if z.testzip() is not None:
            raise RuntimeError('ZIP CRC verification failed')
        infos = z.infolist()
        names = [p.filename for p in infos]
        if len(names) != len(set(names)):
            raise RuntimeError('Duplicate archive member')
        for info in infos:
            name = info.filename
            if not name.startswith(prefix) or '..' in PurePosixPath(name).parts:
                raise ValueError(f'Invalid member path: {name}')
            if not stat.S_ISREG(info.external_attr >> 16):
                raise ValueError(f'Nonregular archive member: {name}')
        payload = {n[len(prefix):]: z.read(n) for n in names}
        sums = {}
        for line in payload['SHA256SUMS'].decode().splitlines():
            value, name = line.split('  ', 1)
            sums[name] = value
        if set(sums) != set(payload) - {'SHA256SUMS'}:
            raise ValueError('Checksum inventory differs from archive members')
        for name, value in sums.items():
            if digest(payload[name]) != value:
                raise ValueError(f'Checksum mismatch: {name}')
        inventory = json.loads(payload['RELEASE_INVENTORY.json'])
        if inventory['checkpoint']:
            raise ValueError('Final delivery must not be a working checkpoint')
        for name, value in inventory['file_sha256'].items():
            if digest(payload[name]) != value:
                raise ValueError(f'Release inventory mismatch: {name}')
            path = args.source / name
            if not path.is_file() or path.read_bytes() != payload[name]:
                raise ValueError(f'ZIP differs from final working source: {name}')
        if {'CHECKPOINT_STATUS.md', 'CHECKPOINT_STATUS.txt'} & payload.keys():
            raise ValueError('Working-checkpoint marker in final ZIP')
        core = source_inventory(args.source)
        for name, entry in core.items():
            if name not in payload or digest(payload[name]) != entry['sha256']:
                raise ValueError(f'Missing or stale final core file: {name}')
        return {'scope': 'Final ZIP CRC, exact member inventory, all embedded checksums, exact final source bytes',
            'zip_sha256': digest(args.archive.read_bytes()), 'zip_bytes': args.archive.stat().st_size,
            'members': len(payload), 'core_files_verified': len(core),
            'project_source_modules': inventory['project_source_modules'],
            'all_regular_lean_files': len(inventory['all_regular_lean_files']),
            'unconditional_dimension_18_proved': inventory['unconditional_dimension_18_proved'],
            'matches_final_working_tree': True, 'checkpoint': False}


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('mode', choices=['patch', 'archive'])
    p.add_argument('--source', type=Path, required=True)
    p.add_argument('--original', type=Path)
    p.add_argument('--patch', type=Path)
    p.add_argument('--checkout', type=Path)
    p.add_argument('--archive', type=Path)
    p.add_argument('--output', type=Path, required=True)
    args=p.parse_args()
    if args.mode == 'patch' and not all([args.original,args.patch,args.checkout]):
        p.error('Patch mode requires --original, --patch, --checkout')
    if args.mode == 'archive' and not args.archive:
        p.error('Archive mode requires --archive')
    report=(validate_patch if args.mode == 'patch' else validate_archive)(args)
    report['verified_at_utc']=datetime.now(timezone.utc).isoformat()
    report['passed']=True
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in {'final_core_files','commands'}},indent=2))

if __name__ == '__main__':
    main()
