#!/usr/bin/env python3
"""Produce the reviewable source/documentation patch, excluding verification logs."""
from __future__ import annotations
import argparse
import difflib
import hashlib
import json
from pathlib import Path
import stat

SKIP_PARTS = {'.git', '.lake', '__pycache__', 'verification'}


def inventory(root):
    result = {}
    for path in root.rglob('*'):
        rel = path.relative_to(root)
        if SKIP_PARTS.intersection(rel.parts) or not path.is_file():
            continue
        if path.is_symlink():
            raise ValueError(f'Refusing symlink: {rel}')
        if path.name in {'SHA256SUMS', 'RELEASE_INVENTORY.json'}:
            continue
        data = path.read_bytes()
        data.decode('utf-8')
        if data and not data.endswith(b'\n'):
            raise ValueError(f'No final newline: {rel}')
        executable = bool(path.stat().st_mode & stat.S_IXUSR)
        result[rel.as_posix()] = (data, '100755' if executable else '100644')
    return result


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('original', type=Path)
    p.add_argument('updated', type=Path)
    p.add_argument('output', type=Path)
    args = p.parse_args()
    old, new = inventory(args.original), inventory(args.updated)
    output = []
    changed = []
    for name in sorted(old.keys() | new.keys()):
        if old.get(name) == new.get(name):
            continue
        changed.append(name)
        output.append(f'diff --git a/{name} b/{name}\n')
        if name not in old:
            output.append(f'new file mode {new[name][1]}\n')
        elif name not in new:
            output.append(f'deleted file mode {old[name][1]}\n')
        elif old[name][1] != new[name][1]:
            output.extend([f'old mode {old[name][1]}\n', f'new mode {new[name][1]}\n'])
        before = old.get(name, (b'', ''))[0].decode('utf-8').splitlines(keepends=True)
        after = new.get(name, (b'', ''))[0].decode('utf-8').splitlines(keepends=True)
        output.extend(difflib.unified_diff(before, after,
            fromfile=f'a/{name}' if name in old else '/dev/null',
            tofile=f'b/{name}' if name in new else '/dev/null'))
    args.output.write_text(''.join(output), encoding='utf-8')
    print(json.dumps({'patch': str(args.output.resolve()), 'changed_files': changed,
                      'excluded_directory': 'verification', 'bytes': args.output.stat().st_size,
                      'sha256': hashlib.sha256(args.output.read_bytes()).hexdigest()}, indent=2))


if __name__ == '__main__':
    main()
