#!/usr/bin/env python3
"""Reproduce the isolated A+B18 compiled-interface diagnostic portably.

Requires an already-built project and its pinned `lake` available on PATH.
Writes only to a new directory below verification/. No build, kernel replay,
historical-result replacement, or official Comparator run is performed.
"""
from __future__ import annotations

import argparse
import ast
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

PROJECT = Path(__file__).resolve().parents[2]
HISTORICAL = PROJECT / 'verification/d18-compiled-interface'
SERIALIZER = HISTORICAL / 'serializer.lean.txt'
HISTORICAL_DRIVER = HISTORICAL / 'compare_compiled_interfaces.py.txt'
MODULES = ['Challenge', 'PalomarSolution']
OWNER_IMPORTS = {
    'Challenge': ['Challenge'],
    'PalomarSolution': ['PalomarSolution', 'Solution',
                        'AkopyanResearch.Completion.DimensionEighteen'],
}
NAMES = ['simplex', 'DisjointSupports', 'IsAlmostSixEmbedding', 'Ambient',
         'Body', 'unitBall', 'IsSixPartition', 'tverberg_counterexample',
         'convex_partition_counterexample_gt_17']


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def json_sha(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True,
        separators=(',', ':')).encode()).hexdigest()


def save_result(output_dir, result):
    (output_dir / 'results.json').write_text(json.dumps(result, indent=2) + '\n')


def discover_project_sources():
    return {'.'.join(p.relative_to(PROJECT).with_suffix('').parts): p
            for p in PROJECT.rglob('*.lean')
            if not {'.lake', '.git', 'verification', 'tests'}.intersection(
                p.relative_to(PROJECT).parts[:-1])}


def project_import_closure(sources):
    pending = list(MODULES)
    found = set()
    while pending:
        module = pending.pop()
        if module in found:
            continue
        found.add(module)
        for line in sources[module].read_text().splitlines():
            match = re.match(r'^\s*(?:public\s+)?import\s+(?:all\s+)?(.+)$', line)
            if match:
                imports = match.group(1).split('--', 1)[0].split()
                pending.extend(m for m in imports if m in sources and m not in found)
    return sorted(found)


def bound_inputs(sources, closure):
    paths = [sources[m] for m in closure]
    paths += [PROJECT / name for name in
              ['lean-toolchain', 'lake-manifest.json', 'lakefile.toml']]
    paths += [SERIALIZER, HISTORICAL_DRIVER, HISTORICAL / 'results.json',
              Path(__file__).resolve()]
    for module in closure:
        stem = PROJECT / '.lake/build/lib/lean' / module.replace('.', '/')
        ordinary = Path(str(stem) + '.olean')
        require(ordinary.is_file(), f'Build the genuine module first: missing {ordinary}')
        paths.append(ordinary)
        for suffix in ['.olean.private', '.olean.server']:
            path = Path(str(stem) + suffix)
            if path.is_file():
                paths.append(path)
    return {str(p.relative_to(PROJECT)): sha(p) for p in sorted(set(paths))}


def historical_evidence_hashes():
    # Narrative reproduction instructions may be updated independently. All
    # original drivers, inspectors, serializer, snapshots and logs are bound.
    return {p.relative_to(PROJECT).as_posix(): sha(p)
            for p in sorted(HISTORICAL.rglob('*'))
            if p.is_file() and p.suffix != '.md'}


def check_historical_logic_inputs():
    original = json.loads((HISTORICAL / 'results.json').read_text())
    for path in [SERIALIZER, HISTORICAL_DRIVER]:
        name = path.relative_to(PROJECT).as_posix()
        require(original['input_sha256_before'].get(name) == sha(path),
                f'Historical logic input no longer matches its successful record: {name}')
    constants = {}
    for node in ast.parse(HISTORICAL_DRIVER.read_text()).body:
        if isinstance(node, ast.Assign) and len(node.targets) == 1:
            target = node.targets[0]
            if isinstance(target, ast.Name) and target.id in {'MODULES', 'OWNER_IMPORTS', 'NAMES'}:
                constants[target.id] = ast.literal_eval(node.value)
    require(constants == {'MODULES': MODULES, 'OWNER_IMPORTS': OWNER_IMPORTS, 'NAMES': NAMES},
            'The historical declaration or owner-import selection differs')
    require(SERIALIZER.read_text().count('"__OUTPUT__"') == 1,
            'Expected exactly one serializer output-path placeholder')


def tool_command(command, timeout, output_dir, label):
    started = time.monotonic()
    process = subprocess.run(command, cwd=PROJECT, capture_output=True,
                             text=True, timeout=timeout, check=False)
    (output_dir / (label + '.log')).write_text(process.stdout + process.stderr)
    record = {'label': label, 'command': command, 'exit_code': process.returncode,
              'seconds': round(time.monotonic() - started, 3)}
    require(process.returncode == 0, f'{label} failed; see {label}.log')
    return process.stdout.strip(), record


def resolve_tools(output_dir, timeout):
    launcher = shutil.which('lake')
    require(launcher is not None, 'lake is not on PATH; install/select the pinned toolchain first')
    lake = str(Path(launcher).absolute())
    pin = (PROJECT / 'lean-toolchain').read_text().strip()
    match = re.fullmatch(r'leanprover/lean4:v([0-9]+\.[0-9]+\.[0-9]+(?:-[A-Za-z0-9.-]+)?)', pin)
    require(match is not None, 'Expected a pinned official Lean version in lean-toolchain')
    expected = match.group(1)
    version, version_record = tool_command([lake, 'env', 'lean', '--version'],
                                           timeout, output_dir, 'lean-version')
    actual = re.search(r'Lean \(version ([^,]+),', version)
    require(actual is not None and actual.group(1) == expected,
            f'Lake selected a Lean version different from {pin}')
    prefix, prefix_record = tool_command([lake, 'env', 'lean', '--print-prefix'],
                                         timeout, output_dir, 'lean-prefix')
    lake_version, lake_record = tool_command([lake, '--version'],
                                            timeout, output_dir, 'lake-version')
    require(f'(Lean version {expected})' in lake_version,
            'The Lake executable does not report the pinned Lean version')
    lean_binary = Path(prefix) / 'bin' / ('lean.exe' if os.name == 'nt' else 'lean')
    require(lean_binary.is_file(), 'Lake-selected Lean prefix has no compiler binary')
    paths = [Path(lake), Path(lake).resolve(), lean_binary.resolve()]
    distributed_lake = Path(prefix) / 'bin' / ('lake.exe' if os.name == 'nt' else 'lake')
    if distributed_lake.is_file():
        paths.append(distributed_lake.resolve())
    hashes = {str(p): sha(p) for p in sorted(set(paths))}
    return lake, hashes, {
        'pinned_toolchain': pin, 'lean_version': version, 'lake_version': lake_version,
        'lake_path_from_PATH': lake, 'lean_prefix_selected_by_lake': prefix,
        'tool_resolution_commands': [version_record, prefix_record, lake_record],
    }


def compare_snapshots(snapshots, sources, closure):
    # Same canonical records, kind guards, isolation guards and equality test
    # as the preserved successful driver; explicit checks remain active with -O.
    wanted = ['AkopyanSixfold.' + name for name in NAMES]
    for snapshot in snapshots.values():
        require([d['name'] for d in snapshot['declarations']] == wanted,
                'Unexpected declaration selection or order')
        require([d['kind'] for d in snapshot['declarations']] ==
                ['definition'] * 7 + ['theorem'] * 2, 'Unexpected genuine declaration kind')
    challenge = snapshots['Challenge']
    solution = snapshots['PalomarSolution']
    challenge_project_imports = sorted(set(challenge['imports']) & set(sources))
    solution_project_imports = sorted(set(solution['imports']) & set(sources))
    require(challenge_project_imports == ['Challenge'], 'Challenge imports project proof modules')
    require('Solution' not in challenge['imports'], 'Challenge imports Solution')
    require('PalomarSolution' not in challenge['imports'], 'Challenge imports PalomarSolution')
    require('Challenge' not in solution['imports'], 'Proof environment imports Challenge')
    require('Solution' in solution['imports'], 'Theorem A owner is missing')
    require('AkopyanResearch.Completion.DimensionEighteen' in solution['imports'],
            'Theorem B18 owner is missing')
    require(set(challenge_project_imports + solution_project_imports) == set(closure),
            'Static bound closure and actual imported project environments differ')
    differences = [name for name, a, b in zip(wanted, challenge['declarations'],
                                            solution['declarations']) if a != b]
    return {
        'types_compared': 9, 'definition_values_compared': 7, 'differences': differences,
        'challenge_project_imports': challenge_project_imports,
        'proof_project_imports': solution_project_imports,
        'solution_imports_challenge': False,
        'excluded_expression_fields': ['metadata', 'binder display names'],
        'retained_expression_fields': ['bound-variable indices', 'universe levels',
            'universe parameters', 'constant names', 'all applications',
            'instance arguments', 'binder types', 'binder implicitness',
            'let types and values', 'projections', 'literals'],
        'declarations_sha256': {m: json_sha(snapshots[m]['declarations']) for m in MODULES},
        'declaration_comparisons': [{
            'name': name,
            'type_identical': a['type'] == b['type'],
            'universe_parameters_identical': a['level_params'] == b['level_params'],
            'definition_value_identical': a['value'] == b['value']
                if a['kind'] == 'definition' else None,
            'compiled_kind': a['kind'],
        } for name, a, b in zip(wanted, challenge['declarations'], solution['declarations'])],
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', required=True, type=Path,
                        help='A NEW directory beneath this project\'s verification directory')
    parser.add_argument('--timeout-seconds', type=int, default=300,
                        help='Maximum seconds for each Lean inspection or tool query')
    args = parser.parse_args()
    if args.timeout_seconds <= 0:
        parser.error('--timeout-seconds must be positive')
    raw_output = args.output_dir if args.output_dir.is_absolute() else PROJECT / args.output_dir
    output_dir = raw_output.resolve()
    verification = (PROJECT / 'verification').resolve()
    if output_dir == verification or not output_dir.is_relative_to(verification):
        parser.error('--output-dir must be a new directory strictly below verification/')
    if output_dir == HISTORICAL or output_dir.is_relative_to(HISTORICAL):
        parser.error('--output-dir must be separate from the historical evidence directory')
    if raw_output.exists() or raw_output.is_symlink() or output_dir.exists():
        parser.error('Refusing to overwrite an existing output path')
    if any(ord(c) < 32 for c in str(output_dir)):
        parser.error('Control characters are not allowed in the output path')
    output_dir.mkdir(parents=True, exist_ok=False)
    result = {
        'outcome': 'verification-in-progress',
        'started_utc': datetime.now(timezone.utc).isoformat(),
        'official_comparator': False, 'official_sandbox_workflow': False,
        'theorem_proof_bodies_compared': False, 'build_commands_run': False,
        'kernel_replay_run': False,
        'driver_command': [sys.executable, str(Path(__file__).resolve()), *sys.argv[1:]],
        'working_directory': str(PROJECT), 'output_directory': str(output_dir),
        'environment_overrides': {},
        'serializer_source': SERIALIZER.relative_to(PROJECT).as_posix(),
        'historical_driver_executed': False,
        'direct_import_all_modules': OWNER_IMPORTS,
        'stages': [],
    }
    save_result(output_dir, result)
    sources = closure = initial = tools_before = historical_before = None
    try:
        check_historical_logic_inputs()
        sources = discover_project_sources()
        closure = project_import_closure(sources)
        initial = bound_inputs(sources, closure)
        historical_before = historical_evidence_hashes()
        result.update(input_sha256_before=initial,
                      source_module_count=len(closure), bound_project_import_closure=closure,
                      historical_evidence_sha256_before=historical_before)
        lake, tools_before, tool_details = resolve_tools(output_dir, args.timeout_seconds)
        result.update(tool_details, tool_sha256_before=tools_before)
        save_result(output_dir, result)
        template = SERIALIZER.read_text()
        for module in MODULES:
            source = output_dir / ('Inspect' + module + '.lean')
            output = output_dir / (module + '.json')
            header = 'module\npublic import Lean\n' + ''.join(
                'import all ' + owner + '\n' for owner in OWNER_IMPORTS[module])
            # Only the output literal changes; the historical serializer is exact.
            output_literal = json.dumps(output.relative_to(PROJECT).as_posix(), ensure_ascii=False)
            source.write_text(header + template.replace('"__OUTPUT__"', output_literal))
            command = [lake, 'env', 'lean', '-j', '1', str(source.relative_to(PROJECT))]
            started = time.monotonic()
            with (output_dir / (module + '.log')).open('w') as log:
                process = subprocess.run(command, cwd=PROJECT, stdout=log,
                                         stderr=subprocess.STDOUT, timeout=args.timeout_seconds)
            stage = {'module': module, 'command': command, 'working_directory': str(PROJECT),
                     'exit_code': process.returncode,
                     'seconds': round(time.monotonic() - started, 3),
                     'inspector_sha256': sha(source)}
            result['stages'].append(stage)
            (output_dir / (module + '.exit')).write_text(str(process.returncode) + '\n')
            save_result(output_dir, result)
            require(process.returncode == 0 and output.is_file(),
                    f'{module} inspection failed; see its log')
        snapshots = {m: json.loads((output_dir / (m + '.json')).read_text()) for m in MODULES}
        result.update(compare_snapshots(snapshots, sources, closure))
        result['serialized_sha256'] = {m: sha(output_dir / (m + '.json')) for m in MODULES}
        result['outcome'] = 'interfaces-differ' if result['differences'] else 'compiled-interfaces-identical'
    except Exception as error:
        result.update(outcome='diagnostic-failed', error_type=type(error).__name__, error=str(error))
    finally:
        try:
            if initial is not None:
                final = bound_inputs(sources, closure)
                result.update(input_sha256_after=final, input_bytes_unchanged=final == initial)
            if tools_before is not None:
                tools_after = {name: sha(Path(name)) for name in tools_before}
                result.update(tool_sha256_after=tools_after, tool_bytes_unchanged=tools_after == tools_before)
            if historical_before is not None:
                historical_after = historical_evidence_hashes()
                result.update(historical_evidence_sha256_after=historical_after,
                              historical_evidence_unchanged=historical_after == historical_before)
            if any(result.get(key) is False for key in
                   ['input_bytes_unchanged', 'tool_bytes_unchanged', 'historical_evidence_unchanged']):
                result['outcome'] = 'input-changed'
        except Exception as error:
            result.update(outcome='input-recheck-failed', recheck_error=str(error))
        result['finished_utc'] = datetime.now(timezone.utc).isoformat()
        result['driver_exit_code'] = 0 if result['outcome'] == 'compiled-interfaces-identical' else 1
        (output_dir / 'driver.exit').write_text(str(result['driver_exit_code']) + '\n')
        save_result(output_dir, result)
    print(json.dumps({key: result.get(key) for key in [
        'outcome', 'types_compared', 'definition_values_compared', 'differences',
        'input_bytes_unchanged', 'tool_bytes_unchanged', 'historical_evidence_unchanged',
        'source_module_count', 'declarations_sha256', 'driver_exit_code']}, indent=2))
    if result['driver_exit_code']:
        print(f'Diagnostic failed; inspect {output_dir / "results.json"}', file=sys.stderr)
    return result['driver_exit_code']


if __name__ == '__main__':
    sys.exit(main())
