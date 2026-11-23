#!/bin/sh
# Run the independent static check and then the Lean kernel/axiom check.
set -eu
cd "$(dirname "$0")/.."
python3 scripts/check_structure.py
python3 -m unittest discover -s tests -q
if ! command -v lake >/dev/null 2>&1; then
  printf '%s\n' 'Lean/Lake not installed: cannot perform kernel verification.' >&2
  exit 127
fi
lake update
if [ "${SKIP_MATHLIB_CACHE:-0}" != "1" ]; then
  if ! lake exe cache get; then
    printf '%s\n' 'Mathlib cache unavailable: building dependencies from sources.' >&2
  fi
fi
lake build Solution
lake build Audit
lake build
