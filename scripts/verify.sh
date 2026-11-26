#!/usr/bin/env bash
# Verify pinned dependencies, all project modules, and the complete owner audit.
# Requirements: Bash, Python 3.11+, and Lean/Lake 4.36.0-rc2 on PATH.
set -euo pipefail

project_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd -P)"
cd "$project_dir"
if (( $# > 1 )); then
  echo 'Usage: scripts/verify.sh [log-directory]' >&2
  exit 2
fi
log_dir="${1:-verification/project}"
case "$log_dir" in
  /*) ;;
  *) log_dir="$project_dir/$log_dir" ;;
esac
mkdir -p -- "$log_dir/tmp"
export TMPDIR="$log_dir/tmp"
printf '%s\n' '{"outcome":"verification-in-progress"}' > "$log_dir/results.json"
rm -f -- "$log_dir/PASS"

fail_notice() {
  code=$?
  if (( code != 0 )); then
    printf 'Verification failed (exit %s); inspect %s\n' "$code" "$log_dir" >&2
  fi
}
trap fail_notice EXIT

command -v python3 >/dev/null
command -v lake >/dev/null
command -v lean >/dev/null
lake env lean --version > "$log_dir/toolchain.log"
lake --version >> "$log_dir/toolchain.log"
expected="$(tr -d '\r\n' < lean-toolchain)"
expected="${expected##*:}"
expected="${expected#v}"
actual="$(head -n 1 "$log_dir/toolchain.log")"
case "$actual" in
  "Lean (version $expected,"*) ;;
  *) printf 'Toolchain mismatch: expected %s; got %s\n' "$expected" "$actual" >&2; exit 1 ;;
esac
if [[ ! -f lake-manifest.json ]]; then
  echo 'Missing pinned lake-manifest.json; dependency resolution is not a verification step.' >&2
  exit 1
fi

snapshot() {
  python3 - "$project_dir" "$1" <<'PY'
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
project, output = map(Path, sys.argv[1:])
spec = importlib.util.spec_from_file_location('project_structure', project / 'scripts/check_structure.py')
assert spec and spec.loader
structure = importlib.util.module_from_spec(spec)
spec.loader.exec_module(structure)
sources = structure.PROJECT_MODULES
paths = list(sources.values())
paths += [project / name for name in ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json', 'comparator.json']]
paths += sorted(p for folder in ['scripts', 'tests'] for p in (project / folder).glob('*')
                if p.is_file() and p.suffix in {'.sh', '.py'})
paths += sorted((project / '.github/workflows').glob('*.yml'))
paths += sorted((project / 'docs/third_party').glob('**/*PROVENANCE.json'))
paths += sorted((project / 'docs/third_party').glob('**/LICENSE'))
paths += sorted(p for p in (project / 'verification/original-specification').glob('*')
                if p.is_file())
report = {
    'recorded_utc': datetime.now(timezone.utc).isoformat(),
    'source_modules': sorted(sources),
    'proof_modules': sorted(set(sources) - {'Challenge'}),
    'input_sha256': {str(path.relative_to(project)): hashlib.sha256(path.read_bytes()).hexdigest()
                     for path in sorted(set(paths))},
}
output.write_text(json.dumps(report, indent=2) + '\n')
PY
}

run_logged() {
  label="$1"
  shift
  printf 'Running %s\n' "$label"
  if "$@" > "$log_dir/$label.log" 2>&1; then
    printf '0\n' > "$log_dir/$label.exit"
    printf '%s: exit 0\n' "$label"
  else
    code=$?
    printf '%s\n' "$code" > "$log_dir/$label.exit"
    tail -n 80 "$log_dir/$label.log" >&2
    return "$code"
  fi
}

snapshot "$log_dir/source-before.json"
run_logged structure python3 scripts/check_structure.py
run_logged provenance python3 scripts/check-provenance.py
run_logged unit-tests python3 -m unittest discover -s tests -q

# Use the committed manifest; do not refresh transitive dependency revisions.
# The optional cache only supplies artifacts for the already selected inputs.
if [[ "${SKIP_MATHLIB_CACHE:-0}" != 1 ]]; then
  if lake exe cache get > "$log_dir/mathlib-cache.log" 2>&1; then
    printf '0\n' > "$log_dir/mathlib-cache.exit"
  else
    code=$?
    printf '%s\n' "$code" > "$log_dir/mathlib-cache.exit"
    echo 'Mathlib cache unavailable; the build will compile missing dependency artifacts.' >&2
  fi
fi

run_logged build lake build
run_logged statement-audit python3 scripts/check-statements.py --output-dir "$log_dir/statements"
# Run afresh even when Lake reuses a previously compiled Audit artifact.
run_logged audit lake env lean -j 1 Audit.lean
snapshot "$log_dir/source-after.json"

python3 - "$log_dir" <<'PY'
from datetime import datetime, timezone
import json
from pathlib import Path
import re
import sys
out = Path(sys.argv[1])
before = json.loads((out / 'source-before.json').read_text())
after = json.loads((out / 'source-after.json').read_text())
if before['input_sha256'] != after['input_sha256']:
    first, last = before['input_sha256'], after['input_sha256']
    changed = sorted(name for name in first.keys() | last.keys() if first.get(name) != last.get(name))
    raise SystemExit(f'Project inputs changed during verification: {changed}')
log = (out / 'audit.log').read_text()
summary = re.search(r'PROJECT AUDIT OK: [^\n]+', log)
if summary is None:
    raise SystemExit('Fresh Lean audit produced no all-owner success marker')
statements = json.loads((out / 'statements/results.json').read_text())
if (statements['outcome'] != 'literal-statements-accepted'
        or not statements['exact_reverse_transformation_matched']
        or statements['changed_inputs_during_verification']):
    raise SystemExit('Literal independent Challenge statement gate did not pass')
results = {
    **before,
    'outcome': 'build-and-project-owner-audit-passed',
    'finished_utc': datetime.now(timezone.utc).isoformat(),
    'sources_unchanged': True,
    'stage_exit_codes': {stage: int((out / (stage + '.exit')).read_text())
                         for stage in ['structure', 'provenance', 'unit-tests', 'build', 'statement-audit', 'audit']},
    'audit_summary': summary.group(0),
    'key_theorem_count': log.count('KEY THEOREM OK '),
    'key_definition_count': log.count('KEY DEFINITION OK '),
    'warning_counts': {stage: len(re.findall(r'(?m)(?:^|\s)warning:', (out / (stage + '.log')).read_text()))
                       for stage in ['build', 'audit']},
    'toolchain': (out / 'toolchain.log').read_text().splitlines(),
    'independent_challenge_comparison': False,
    'literal_challenge_statements_checked': True,
    'comparator_invoked': False,
    'full_palomar_workflow': False,
}
if any(code != 0 for code in results['stage_exit_codes'].values()):
    raise SystemExit('A required stage did not return exit 0')
(out / 'results.json').write_text(json.dumps(results, indent=2) + '\n')
(out / 'PASS').write_text(results['finished_utc'] + '\n')
print(summary.group(0))
PY
cp -- scripts/verify.sh "$log_dir/verifier-used.sh"
printf 'Verification passed; logs: %s\n' "$log_dir"
