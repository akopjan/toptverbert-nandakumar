#!/usr/bin/env python3
"""Offline structural checks for TopTverberg.

This is deliberately NOT a theorem prover. The definitive test is
`lake build Audit`, which invokes Lean's kernel and collects the axioms
of the two exported theorems.
"""

from __future__ import annotations

import json
import re
import sys
import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SOURCE_FILES = sorted(
    p for p in ROOT.rglob('*.lean')
    if '.lake' not in p.relative_to(ROOT).parts
)
PROJECT_MODULES = {'.'.join(p.relative_to(ROOT).with_suffix('').parts): p for p in SOURCE_FILES}


def strip_comments_and_strings(source: str) -> str:
    """Blank nested Lean block comments, line comments, and quoted strings.

    Preserve newlines so diagnostics can use the original line numbers.
    """
    out: list[str] = []
    index, nesting, quoted, escaped = 0, 0, False, False
    while index < len(source):
        char = source[index]
        next_char = source[index + 1] if index + 1 < len(source) else ''
        if nesting:
            if char == '/' and next_char == '-':
                nesting += 1
                out.extend((' ', ' '))
                index += 2
            elif char == '-' and next_char == '/':
                nesting -= 1
                out.extend((' ', ' '))
                index += 2
            else:
                out.append('\n' if char == '\n' else ' ')
                index += 1
        elif quoted:
            if char == '\\' and not escaped:
                escaped = True
                out.append(' ')
            elif char == '"' and not escaped:
                quoted = False
                out.append(' ')
            else:
                out.append('\n' if char == '\n' else ' ')
                escaped = False
            index += 1
        elif char == '/' and next_char == '-':
            nesting = 1
            out.extend((' ', ' '))
            index += 2
        elif char == '-' and next_char == '-':
            # '--' Lean line comments; block-comment delimiters inside are inert.
            eol = source.find('\n', index)
            if eol < 0:
                out.extend(' ' * (len(source) - index))
                index = len(source)
            else:
                out.extend(' ' * (eol - index))
                index = eol
        elif char == '"':
            quoted = True
            out.append(' ')
            index += 1
        else:
            out.append(char)
            index += 1
    if nesting:
        raise ValueError('Unterminated Lean block comment')
    if quoted:
        raise ValueError('Unterminated Lean quoted string')
    return ''.join(out)


def check_delimiters(source: str) -> None:
    """Check balanced Lean parentheses, braces, and brackets after lexing."""
    src = strip_comments_and_strings(source)
    opening, closing = '([{', ')]}'
    partners = dict(zip(closing, opening))
    stack: list[tuple[str, int]] = []
    for index, char in enumerate(src):
        if char in opening:
            stack.append((char, index))
        elif char in closing:
            if not stack or stack[-1][0] != partners[char]:
                line = src.count('\n', 0, index) + 1
                raise ValueError(f'Unmatched {char!r} at line {line}')
            stack.pop()
    if stack:
        char, index = stack[-1]
        line = src.count('\n', 0, index) + 1
        raise ValueError(f'Unclosed {char!r} at line {line}')


def theorem_signature(source: str, theorem: str) -> str:
    match = re.search(
        rf'(?m)^theorem\s+{re.escape(theorem)}\b([\s\S]*?):=\s*by\b',
        strip_comments_and_strings(source),
    )
    if not match:
        raise ValueError(f'Could not locate signature of theorem {theorem}')
    return re.sub(r'\s+', '', match.group(1))



def public_definition(source: str, name: str) -> str:
    """Extract one simple top-level `def` or `abbrev` from a comparator file.

    The comparator's seven interface definitions have indentation-based bodies.
    The leading (unindented) declaration ends at the next unindented nonblank
    source line. Comparing these as well as the theorem signatures catches a
    silent change in the meaning of a named proposition or its underlying type.
    """
    cleaned = strip_comments_and_strings(source)
    match = re.search(rf'(?m)^(?:def|abbrev)\s+{re.escape(name)}\b', cleaned)
    if not match:
        raise ValueError(f'Could not locate interface definition {name}')
    tail = cleaned[match.end():]
    next_decl = re.search(r'(?m)^\S', tail)
    end = match.end() + next_decl.start() if next_decl else len(cleaned)
    declaration = cleaned[match.start():end]
    if ':=' not in declaration:
        raise ValueError(f'Interface definition has no body: {name}')
    return re.sub(r'\s+', '', declaration)

def imports(source: str) -> set[str]:
    return set(
        re.findall(r'(?m)^\s*(?:public\s+|private\s+)?import(?:\s+all)?\s+([A-Za-z_][\w.]*)',
                   strip_comments_and_strings(source))
    )


def check_imports(sources: dict[str, str]) -> tuple[dict[str, set[str]], int]:
    graph: dict[str, set[str]] = {}
    n_local = 0
    for name, source in sources.items():
        deps: set[str] = set()
        for dep in imports(source):
            if dep.startswith('RequestProject') or dep.startswith('AkopyanResearch') or dep in ('Solution', 'Challenge', 'Audit'):
                if dep not in PROJECT_MODULES:
                    raise ValueError(f'{name}: imported project module {dep} does not exist')
                deps.add(dep)
                n_local += 1
        graph[name] = deps

    done: set[str] = set()
    visiting: set[str] = set()

    def dfs(name: str) -> None:
        if name in visiting:
            raise ValueError(f'Cyclic import involving {name}')
        if name not in done:
            visiting.add(name)
            for dep in graph[name]:
                dfs(dep)
            visiting.remove(name)
            done.add(name)

    for mod in sorted(graph):
        dfs(mod)
    return graph, n_local


def main() -> int:
    errors: list[str] = []
    config = json.loads((ROOT / 'comparator.json').read_text())
    source_paths = {name: path.relative_to(ROOT).as_posix() for name, path in PROJECT_MODULES.items()}
    sources = {name: p.read_text(encoding='utf-8') for name, p in PROJECT_MODULES.items()}
    stripped: dict[str, str] = {}
    for name, source in sources.items():
        try:
            stripped[name] = strip_comments_and_strings(source)
            check_delimiters(source)
        except ValueError as exc:
            errors.append(f'{name}: {exc}')

    lakefile = tomllib.loads((ROOT / 'lakefile.toml').read_text())
    libraries = [entry['name'] for entry in lakefile.get('lean_lib', [])]
    if len(libraries) != len(set(libraries)):
        errors.append('Duplicate Lake library targets')
    if 'Audit' not in libraries or 'Audit' not in lakefile.get('defaultTargets', []):
        errors.append('Axiom audit is not in default Lake targets')
    if lakefile.get('require', [{}])[0].get('rev') != 'v4.35.0':
        errors.append('Mathlib version differs from the pinned Lean toolchain')
    if (ROOT / 'lean-toolchain').read_text().strip() != 'leanprover/lean4:v4.35.0':
        errors.append('Lean toolchain version differs from 4.35.0')
    for entry in lakefile.get('lean_lib', []):
        for root in entry.get('roots', []):
            if root not in PROJECT_MODULES:
                errors.append(f'Lake target {entry["name"]} references absent root {root}')

    if config['challenge_module'] != 'Challenge' or config['solution_module'] != 'Solution':
        errors.append('Unexpected comparator source modules')
    if set(config['permitted_axioms']) != {'propext', 'Quot.sound', 'Classical.choice'}:
        errors.append('Unexpected permitted axioms')

    interface_names = ('simplex', 'DisjointSupports', 'IsAlmostSixEmbedding',
                       'Ambient', 'Body', 'unitBall', 'IsSixPartition')
    for name in interface_names:
        try:
            if public_definition(sources['Challenge'], name) != public_definition(sources['Solution'], name):
                errors.append(f'Interface definition mismatch: {name}')
        except ValueError as exc:
            errors.append(str(exc))

    for full_name in config['theorem_names']:
        thm = full_name.rsplit('.', 1)[-1]
        try:
            baseline = theorem_signature(sources['Challenge'], thm)
            solution = theorem_signature(sources['Solution'], thm)
            if solution != baseline:
                errors.append(f'Signature mismatch: {full_name}')
        except ValueError as exc:
            errors.append(str(exc))

    milestones = {
        'RequestProject.Construction.Assembly': ('exists_height',),
        'RequestProject.Solution': ('heightExtension',),
        'Solution': ('tverberg_counterexample', 'fivefold_tverberg_join',
                     'exists_isBlocking_5d', 'convex_partition_counterexample_ge_36',
                     'convex_partition_counterexample'),
    }
    for module, names in milestones.items():
        for name in names:
            if not re.search(rf'(?m)^theorem\s+{name}\b', stripped[module]):
                errors.append(f'Proof milestone {name} absent from {source_paths[module]}')

    challenge_sorries = list(re.finditer(r'\bsorry\b', stripped['Challenge']))
    if len(challenge_sorries) != len(config['theorem_names']):
        errors.append(f'Expected {len(config["theorem_names"])} template sorries in Challenge, found {len(challenge_sorries)}')

    bad_tokens = re.compile(r'\b(sorry|admit|axiom|constant|opaque|unsafe|native_decide|run_tac)\b')
    for module, source in stripped.items():
        for match in bad_tokens.finditer(source):
            if module == 'Challenge' and match.group(1) == 'sorry':
                continue  # The comparator's separate specification is a template.
            line = source.count('\n', 0, match.start()) + 1
            errors.append(f'{source_paths[module]}:{line}: unexpected token {match.group(1)}')

    try:
        graph, edge_count = check_imports(sources)
    except ValueError as exc:
        errors.append(str(exc))
        graph, edge_count = {}, 0
    if graph:
        if 'Challenge' in graph['Solution']:
            errors.append('Solution must not import the comparator Challenge module')
        if 'Solution' in graph['Challenge']:
            errors.append('Challenge must remain an independent specification')

    if not errors:
        seen, stack = set(), ['Solution']
        while stack:
            module = stack.pop()
            if module in seen:
                continue
            seen.add(module)
            stack.extend(graph[module])
        print(f'PASS: {len(sources)} Lean modules; balanced delimiters; {edge_count} resolved project imports; no cycles')
        print(f'PASS: {len(config["theorem_names"])} comparator signatures and {len(interface_names)} interface definitions match Solution exactly')
        print('PASS: 7 proof milestones present; no sorry/admit/axiom/constant/opaque/unsafe/native_decide/run_tac tokens in proof modules')
        print(f'INFO: Solution depends on {len(seen)-1} project modules')
        print('INFO: Challenge.lean is the original independent specification with two sorry placeholders')
        print('NEXT: lake build Audit (kernel elaboration and transitive axiom audit)')
        return 0

    for error in errors:
        print(f'ERROR: {error}', file=sys.stderr)
    return 1


if __name__ == '__main__':
    sys.exit(main())
