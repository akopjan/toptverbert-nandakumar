#!/usr/bin/env python3
"""Check the exact source inventory and licences of vendored topology modules.

This is an integrity check, not a proof checker. Lean's all-owner audit
independently checks the mathematical declarations in the same files.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
import sys


ROOT = Path(__file__).resolve().parent.parent
VENDOR_PREFIXES = ('Submission', 'Hatcher')


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    inventory: dict[str, tuple[str, Path]] = {}
    errors: list[str] = []
    manifests = sorted((ROOT / 'docs/third_party').glob('**/*PROVENANCE.json'))
    if not manifests:
        raise ValueError('No vendor provenance manifests found')
    for manifest in manifests:
        record = json.loads(manifest.read_text())
        if record.get('license') != 'Apache-2.0':
            errors.append(f'{manifest.relative_to(ROOT)}: unrecognized vendor licence')
        if not (manifest.parent / 'LICENSE').is_file():
            errors.append(f'{manifest.relative_to(ROOT)}: missing preserved licence text')
        if not re.fullmatch(r'[0-9a-f]{40}', record.get('revision', '')):
            errors.append(f'{manifest.relative_to(ROOT)}: upstream revision is not a full commit')
        for entry in record.get('files', []):
            name = entry.get('module', '')
            if name.split('.')[0] not in VENDOR_PREFIXES:
                continue
            if not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9.]*(?<!\.)', name):
                errors.append(f'{manifest.relative_to(ROOT)}: invalid module name {name!r}')
                continue
            expected = entry.get('port_sha256', entry.get('ported_sha256', ''))
            if not re.fullmatch(r'[0-9a-f]{64}', expected):
                errors.append(f'{name}: missing exact port SHA-256')
                continue
            if name in inventory and inventory[name][0] != expected:
                errors.append(f'{name}: conflicting source hashes in provenance manifests')
                continue
            inventory[name] = expected, manifest

    actual: dict[str, Path] = {}
    for prefix in VENDOR_PREFIXES:
        for path in (ROOT / prefix).rglob('*.lean'):
            name = '.'.join(path.relative_to(ROOT).with_suffix('').parts)
            actual[name] = path
    for name, path in sorted(actual.items()):
        if name not in inventory:
            errors.append(f'{name}: vendored source is absent from the provenance inventory')
        elif digest(path) != inventory[name][0]:
            errors.append(f'{name}: source differs from its recorded port SHA-256')
    for name in sorted(set(inventory) - set(actual)):
        errors.append(f'{name}: provenance inventory refers to an absent vendored source')
    if errors:
        for error in errors:
            print(f'ERROR: {error}', file=sys.stderr)
        return 1
    print(f'PASS: {len(actual)} vendored topology modules match exact provenance hashes; '
          f'{len(manifests)} manifests retain pinned upstream revisions and licence texts')
    return 0


if __name__ == '__main__':
    try:
        sys.exit(main())
    except (OSError, ValueError, TypeError, KeyError) as error:
        print(f'ERROR: {error}', file=sys.stderr)
        sys.exit(1)
