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
# Palomar's compiled-artifact list, plus large/runtime-only local outputs.
EXCLUDED_SUFFIXES = {'.a', '.bc', '.dll', '.dylib', '.ilean', '.ir', '.o', '.obj',
                     '.olean', '.so', '.trace', '.pyc', '.ndjson'}
EXCLUDED_NAME_SUFFIXES = ('.olean.private', '.olean.server', '.ir.sig')
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
        if path.suffix.lower() in EXCLUDED_SUFFIXES or path.name.lower().endswith(EXCLUDED_NAME_SUFFIXES):
            continue
        if path.stat().st_size > 20_000_000:
            raise ValueError(f'Unexpected large release file: {rel}')
        yield rel, path


def verified_dimension_eighteen(root: Path) -> tuple[dict, dict, set[str]]:
    """Bind a release claim to successful, unchanged proof-verification inputs."""
    report_hashes = {}

    def read(name):
        path = root / 'verification' / name / 'results.json'
        if not path.is_file():
            raise ValueError(f'Missing required release evidence: {path}')
        data = path.read_bytes()
        digest = hashlib.sha256(data).hexdigest()
        report_hashes[path.relative_to(root).as_posix()] = digest
        return json.loads(data), digest

    evidence = {}
    snapshots = []
    for name in ('d18-final-retry', 'd18-clean-final'):
        result, digest = read(name)
        if (result.get('outcome') != 'build-and-project-owner-audit-passed'
                or not result.get('sources_unchanged')
                or set(result.get('stage_exit_codes', {}).values()) != {0}
                or set(result.get('stage_exit_codes', {})) !=
                   {'structure', 'provenance', 'unit-tests', 'build', 'statement-audit', 'audit'}):
            raise ValueError(f'Incomplete or unsuccessful build evidence: {name}')
        snapshots.append(result['input_sha256'])
        evidence[name] = {'sha256': digest, 'outcome': result['outcome'],
                          'audit_summary': result['audit_summary']}
    if snapshots[0] != snapshots[1]:
        raise ValueError('Main and clean build do not bind exactly the same release inputs')
    expected_sources = {name.replace('.', '/') + '.lean' for name in result['source_modules']}
    if not expected_sources or not expected_sources.issubset(snapshots[0]):
        raise ValueError('Verified source-module inventory is empty or unbound')

    kernels, digest = read('d18-kernels')
    required = {'AkopyanSixfold.tverberg_counterexample',
                'AkopyanSixfold.almostSix_ninety',
                'AkopyanSixfold.convex_partition_counterexample_gt_17',
                'AkopyanResearch.ConcreteComparisonLifting.requiredRelativeLifting'}
    if (kernels.get('outcome') != 'all-components-accepted'
            or kernels.get('driver_exit_code') != 0
            or not kernels.get('proof_inputs_unchanged')
            or not kernels.get('export_unchanged_during_kernel_checks')
            or not required.issubset(kernels.get('declarations', []))):
        raise ValueError('Required final proof exports have not passed all bundled checkers')
    checker_steps = {step['label']: step['exit_code'] for step in kernels.get('steps', [])
                     if step['label'] in {'leanchecker', 'nanoda', 'con-ron'}}
    if checker_steps != {'leanchecker': 0, 'nanoda': 0, 'con-ron': 0}:
        raise ValueError('The three genuine checker commands have not all succeeded')
    records = kernels.get('export_structure', {}).get('target_records', {})
    if any(records.get(name, {}).get('kind') != 'thm'
           or not records.get(name, {}).get('has_value') for name in required):
        raise ValueError('A required exported target lacks its actual theorem body')
    snapshots.append(kernels['input_sha256'])
    evidence['d18-kernels'] = {'sha256': digest, 'outcome': kernels['outcome'],
                               'export_sha256': kernels['export_sha256']}

    interface, digest = read('d18-compiled-interface')
    if (interface.get('outcome') != 'compiled-interfaces-identical'
            or interface.get('differences') != []
            or not interface.get('input_bytes_unchanged')
            or interface.get('solution_imports_challenge')
            or interface.get('types_compared') != 9
            or interface.get('definition_values_compared') != 7
            or interface.get('challenge_project_imports') != ['Challenge']
            or 'Challenge' in interface.get('proof_project_imports', [])
            or not interface.get('input_sha256_before')
            or interface['input_sha256_before'] != interface.get('input_sha256_after')):
        raise ValueError('The independent compiled A+B18 interface check is incomplete')
    snapshots.append(interface['input_sha256_before'])
    evidence['d18-compiled-interface'] = {'sha256': digest, 'outcome': interface['outcome']}

    checked_hashes = dict(report_hashes)
    for snapshot in snapshots:
        for name, digest in snapshot.items():
            path = root / name
            if not path.resolve().is_relative_to(root):
                raise ValueError(f'Verification input escapes the project: {name}')
            if name in checked_hashes and checked_hashes[name] != digest:
                raise ValueError(f'Verification records disagree about input: {name}')
            if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != digest:
                raise ValueError(f'Release input changed after verification: {name}')
            checked_hashes[name] = digest
    return evidence, checked_hashes, expected_sources


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source', type=Path)
    parser.add_argument('destination', type=Path)
    parser.add_argument('--stage', action='store_true')
    release_mode = parser.add_mutually_exclusive_group()
    release_mode.add_argument('--checkpoint', action='store_true')
    release_mode.add_argument('--verified-d18', action='store_true',
                              help='Require the complete, unchanged A+B18 release evidence')
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

    if not args.checkpoint and not args.verified_d18:
        parser.error('Select --checkpoint or --verified-d18; an unverified final release is forbidden')
    evidence, checked_hashes, expected_sources = (
        verified_dimension_eighteen(root) if args.verified_d18 else ({}, {}, set()))

    payload = {rel.as_posix(): path.read_bytes() for rel, path in pairs}
    project_sources = {name: data for name, data in payload.items()
                       if name.endswith('.lean') and not name.startswith(('verification/', 'tests/'))}
    if args.verified_d18 and set(project_sources) != expected_sources:
        raise ValueError('Packaged proof-module inventory differs from the verified source inventory')
    for name, digest in checked_hashes.items():
        if name in payload and hashlib.sha256(payload[name]).hexdigest() != digest:
            raise ValueError(f'Actual ZIP payload changed after verification: {name}')
        if '.lake' not in Path(name).parts and name not in payload:
            raise ValueError(f'A bound verification input is missing from the source ZIP: {name}')
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
            'This is a source checkpoint, not a certified final release.\n'
            'Inspect FORMALIZATION_STATUS.md and the recorded verification\n'
            'outcomes for its exact mathematical and checking status.\n'
            'No final-release verification claim is made by this archive.\n'
        ).encode()
    report = {
        'created_utc': datetime.now(timezone.utc).isoformat(),
        'release_scope': ('A, the ninety-vertex construction, and unconditional B for d > 17'
                          if args.verified_d18 else 'Source checkpoint; see recorded status'),
        'unconditional_dimension_18_proved': args.verified_d18,
        'checkpoint': args.checkpoint,
        'verified_release_evidence': evidence,
        'project_source_modules': len(project_sources),
        'proof_source_modules': len(project_sources) - 1,
        'all_regular_lean_files': lean_inventory,
        'input_archive_sha256': '7537d4233d74c40aa3eddad5fd4912287810f6a78c6543dbf75cf2fe364e119b',
        'excluded_runtime_artifacts': sorted(EXCLUDED_PARTS | EXCLUDED_SUFFIXES
                                             | set(EXCLUDED_NAME_SUFFIXES)),
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
