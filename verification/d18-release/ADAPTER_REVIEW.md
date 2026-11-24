# Review of the portable interface and semantic adapters

24 November 2026. Both owners confirmed that the adapters and their successful
run evidence were frozen before this review. The review read the current
Python code, archived diagnostic code, generated sources and existing JSON
results. **No Lean process, project build or proof export was launched.**

**Finding:** neither adapter weakens its original diagnostic. The successful
runs use separate new evidence directories, preserve their mathematical
inputs, and leave the historical results unchanged. Their current source
hashes match the hashes bound by those runs.

## Compiled interfaces

`reproduce_compiled_interfaces.py` reuses the exact archived serializer and
checks its hash against the successful historical report. Its declaration
names and owner imports are checked against the original driver. The nine
types, seven definition bodies, declaration kinds, universe parameters and
import-isolation predicates are unchanged. Explicit `require` checks replace
removable Python assertions.

The two Lean environments remain separate: Challenge imports only its
specification among project modules; the proof environment imports the
actual A and B18 owners and excludes Challenge. The comparison retains the
same canonical expression fields. Binder display names and metadata remain
excluded, and theorem proof bodies are not compared by this diagnostic.

The fresh report in `d18-portable-interface/` has no differences. Both
canonical declaration digests equal the historical digest:
`0da75f6ec67460498e6f5a13890e8d06a76dd9dad1739c7f433af31e0b51c3d2`.
Its 419-module closure, 1,683 bound inputs, tools and 24 historical evidence
files have equal recorded before/after hashes.

## Semantic scope

`reproduce_semantic_scope.py` copies both archived Lean diagnostics exactly;
their current copies match the fixed source hashes. The reference still
imports only Mathlib, and its search path now explicitly excludes the
project-object directory. The second diagnostic checks the same five
statements against that reference, including B18 and A with its target
transported to Euclidean space. It retains the three concrete nonvacuity
witnesses.

The adapter additionally requires exactly five printed transitive axiom
records, each contained in `propext`, `Classical.choice` and `Quot.sound`.
The fresh `d18-portable-semantic/` report records PASS, 472 matching frozen
release inputs, the 418-module/1,254-object proof closure, and unchanged
source/object/tool hashes. These are the existing successful results, not
a new execution performed by this review.

## Portability and output isolation

Both adapters derive the project from their installed location and obtain
Lean through `lake` on PATH. Neither contains the old fixed scratch or
runtime directory. Their subprocess arguments use argument arrays, and
their writes target the new output directory; no project proof source or
existing object is an output target.

Both reject an existing output path and destinations outside
`verification/`. The compiled-interface adapter also rejects destinations
beneath its historical directory. The semantic adapter does **not** reject
every unused subdirectory nested within historical evidence. This is a
non-blocking placement limitation for future invocations: choose a fresh
sibling such as `verification/reproduction-semantic`. Its actual validated
output is separate. The release owner chose to preserve the already
validated adapter rather than change its hash for this additional guard.
The reproduction README accurately promises rejection of existing output
paths, without claiming that stronger subtree restriction.

## Frozen hashes

| File | SHA-256 |
| --- | --- |
| `reproduce_compiled_interfaces.py` | `e4e740e199b1cbf91bb12bd90c7ea031e70af91818d6ebb6e2c144048e0d0790` |
| `reproduce_semantic_scope.py` | `d45edd77b12184aac81902de9a27148a41f0b3fbfb311adbe12a9eb4133e761c` |
| `d18-portable-interface/results.json` | `a37c32c6a0787b00ff48f3bc06aa620570b68883e34d2f9f559596b6c05abd18` |
| `d18-portable-semantic/results.json` | `7bc1246ed3025749701890d6d31dcb44269b48ec85664831c9b98c829d94ae2f` |

The only file written by this review is this Markdown report.
