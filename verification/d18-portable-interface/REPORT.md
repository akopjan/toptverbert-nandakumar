# Portable compiled-interface reproduction

**PASS:** one run of the new portable reproducer returned
`compiled-interfaces-identical`, exit 0, on 24 November 2026.
Started `2026-11-24T09:48:19.959554+00:00`; finished `2026-11-24T09:48:57.310936+00:00`.
Both separate Lean inspections returned 0 (27.618 and 5.482 seconds).
Nine types and seven definition bodies match, with no differences.

## Defect and correction

The original successful runner under `d18-compiled-interface` hardcodes
its workspace's sibling `tools-runtime` directory and binary path. It is
retained as historical evidence, with its original bytes and bound hash.
It is no longer presented as a command that works in an arbitrary checkout.

The new [reproducer](../d18-release/reproduce_compiled_interfaces.py)
locates this project relative to its own file, selects `lake` from inherited
`PATH`, resolves Lean through that Lake, checks the version against
`lean-toolchain`, and hashes the actual Lean/Lake executables. It contains
no hardcoded workspace runtime or binary path. The validation shell made
the installed toolchain available through this workspace's environment
setup; that setup is not a dependency of the reproducer.

Run from a checkout with the pinned toolchain available and the genuine
project modules already built:

```sh
python3 verification/d18-release/reproduce_compiled_interfaces.py \
  --output-dir verification/reproduction-compiled-interface
```

Choose a new output directory for each run. The command refuses an existing
path, a destination outside `verification/`, and any destination inside the
historical evidence directory. All three CLI guards were exercised without
running Lean or modifying historical files; see `CLI_GUARD_CHECKS.json`.

## Identical diagnostic logic

The exact historical `serializer.lean.txt` is reused; only its output-path
literal is replaced safely. Its SHA-256 remains
`5592f69119576462fbd83893f8d83214122786942844809403956fa44f8bc115`.
The selection of nine declarations and direct `import all` owners is checked
against the saved historical runner. The comparison retains the same
canonical record equality, genuine-kind guards and separate-environment
isolation rules. Explicit Python checks remain active under `python -O`.

Challenge imports only its own project module. The proof environment imports
both real theorem owners and no Challenge. Expression metadata and binder
display names are the only omitted fields; instance applications and universe
information remain in the serialization. This is an interface diagnostic,
not a theorem-proof-body replay or the official Comparator.

The new canonical declaration digest exactly reproduces the successful
historical value for both environments:

`0da75f6ec67460498e6f5a13890e8d06a76dd9dad1739c7f433af31e0b51c3d2`.

## Integrity and evidence

The run binds 419 project sources and
1,257 compiled objects. Including configuration,
serializer, old/new driver and the historical result, all
1,683 bound inputs remained unchanged. The
24 historical evidence files and the
hashed tool executables remained unchanged. The original successful
`results.json`, serializer and runner were not edited. Only the historical
Markdown reproduction instructions were corrected separately.

A further rehash of all **472** frozen main-gate inputs found no changes.
The run issued no project build or independent-kernel command. No prior
verification result was replaced or reclassified.

Exact commands, tool paths/versions/hashes, pre/post source and object hashes,
inspector hashes, timings and result comparisons are in `results.json`.
Both generated inspectors, JSON snapshots, exit records and actual logs
are retained beside it. `PORTABILITY_REVIEW.json` records the checked link
back to the historical digest and the frozen main-gate snapshot.

Portable reproducer SHA-256:
`e4e740e199b1cbf91bb12bd90c7ea031e70af91818d6ebb6e2c144048e0d0790`.
This validation was performed on the current Linux checkout; it is not a
claim to have tested every operating system or installed toolchain manager.
