#!/usr/bin/env python3
"""Read two separately compiled environments and compare their literal kernel interfaces.

This diagnostic is neither the official Comparator nor a proof-body checker.
It compares the actual nine compiled types and seven definition values without
importing Solution into the Challenge inspection process.
"""
from __future__ import annotations

from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
PROJECT = HERE.parent.parent
NAMES = ['simplex', 'DisjointSupports', 'IsAlmostSixEmbedding', 'Ambient',
         'Body', 'unitBall', 'IsSixPartition', 'tverberg_counterexample',
         'convex_partition_counterexample']


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def bound_inputs():
    paths = [PROJECT / name for name in
             ['Challenge.lean', 'Solution.lean', 'lean-toolchain', 'lake-manifest.json']]
    paths += [HERE / 'serializer.lean.txt', Path(__file__).resolve()]
    for module in ['Challenge', 'Solution']:
        for suffix in ['.olean', '.olean.private']:
            p = PROJECT / '.lake/build/lib/lean' / (module + suffix)
            if not p.is_file():
                raise RuntimeError(f'Build the genuine module first: missing {p}')
            paths.append(p)
    return {str(p.relative_to(PROJECT)): sha(p) for p in paths}


def main():
    started = datetime.now(timezone.utc).isoformat()
    initial = bound_inputs()
    result = {'outcome': 'verification-in-progress', 'started_utc': started,
              'input_sha256': initial, 'official_comparator': False}
    (HERE / 'results.json').write_text(json.dumps(result, indent=2) + '\n')
    template = (HERE / 'serializer.lean.txt').read_text()
    stages = []
    for module in ['Challenge', 'Solution']:
        source = HERE / ('Inspect' + module + '.lean')
        output = HERE / (module + '.json')
        source.write_text('module\npublic import Lean\nimport all ' + module + '\n' +
                          template.replace('__OUTPUT__', output.as_posix()))
        output.unlink(missing_ok=True)
        command = ['lake', 'env', 'lean', '-j', '1', str(source.relative_to(PROJECT))]
        before = time.monotonic()
        with (HERE / (module + '.log')).open('w') as log:
            process = subprocess.run(command, cwd=PROJECT, stdout=log, stderr=subprocess.STDOUT)
        stage = {'module': module, 'command': command, 'exit_code': process.returncode,
                 'seconds': round(time.monotonic() - before, 3),
                 'inspector_sha256': sha(source)}
        stages.append(stage)
        (HERE / (module + '.exit')).write_text(str(process.returncode) + '\n')
        if process.returncode != 0 or not output.is_file():
            result.update(outcome='inspection-failed', stages=stages)
            (HERE / 'results.json').write_text(json.dumps(result, indent=2) + '\n')
            raise RuntimeError(f'{module} inspection failed; see its log')
    challenge = json.loads((HERE / 'Challenge.json').read_text())
    solution = json.loads((HERE / 'Solution.json').read_text())
    wanted = ['AkopyanSixfold.' + name for name in NAMES]
    for snapshot in [challenge, solution]:
        assert [d['name'] for d in snapshot['declarations']] == wanted
        assert [d['kind'] for d in snapshot['declarations']] == ['definition'] * 7 + ['theorem'] * 2
    project_modules = {'.'.join(p.relative_to(PROJECT).with_suffix('').parts)
                       for p in PROJECT.rglob('*.lean')
                       if not {'.lake', '.git', 'verification', 'tests'}.intersection(
                           p.relative_to(PROJECT).parts[:-1])}
    actual_challenge_project_imports = sorted(set(challenge['imports']) & project_modules)
    assert actual_challenge_project_imports == ['Challenge']
    assert 'Solution' not in challenge['imports']
    assert 'Challenge' not in solution['imports']
    differences = [name for name, a, b in zip(wanted, challenge['declarations'],
                                            solution['declarations']) if a != b]
    final = bound_inputs()
    assert final == initial, 'An inspected source, module, pin, or serializer changed'
    result.update(
        outcome='compiled-interfaces-identical' if not differences else 'interfaces-differ',
        finished_utc=datetime.now(timezone.utc).isoformat(), stages=stages,
        types_compared=9, definition_values_compared=7, differences=differences,
        challenge_project_imports=actual_challenge_project_imports,
        solution_imports_challenge=False,
        excluded_expression_fields=['metadata', 'binder display names'],
        theorem_proof_bodies_compared=False,
        input_bytes_unchanged=True,
        serialized_sha256={m:sha(HERE / (m + '.json')) for m in ['Challenge', 'Solution']},
    )
    (HERE / 'results.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: result[k] for k in ['outcome', 'types_compared',
          'definition_values_compared', 'differences', 'input_bytes_unchanged']}, indent=2))
    return 1 if differences else 0


if __name__ == '__main__':
    sys.exit(main())
