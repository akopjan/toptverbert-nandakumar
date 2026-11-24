# Portable replay of the compiled-object comparison

**PASS**, 24 November 2026, 09:48:25–09:48:34 UTC. The portable adapter
completed one read-only comparison of the existing main and clean checkouts.
It performed no project rebuild, proof export, or copy of compiled objects
between checkouts. The original comparison records and runner were preserved.

The inventory contains 438 proof-module owners and all three stored module
parts, hence 1,314 object pairs. Of these, 1,185 are byte-identical and 129
differ: one exported part, 64 server parts and 64 private parts, involving
64 modules. These are exactly the counts in the original comparison.

For every differing module the unchanged fixed inspector compared all
stored declarations, types, values, recursor right-hand sides, name arrays,
module flags and imports. Its strict comparisons covered 2,480 exported,
2,480 server and 3,672 private declaration records. All compared fields
agree. Environment-extension payloads were not compared for equality;
their names and entry counts are recorded.

All 472 frozen source/configuration inputs match the successful gate
snapshots in both trees. All 1,314 main objects match the final kernel
export's recorded inputs. Source/object hashes, historical evidence,
tool/adapter hashes and diagnostic-input hashes remained unchanged.

Use the command documented in [the reproduction guide](../README.md).
The adapter is
[reproduce_object_comparison.py](../d18-release/reproduce_object_comparison.py);
its SHA-256 for this run is
`f5498b044db2227e463c762a5b11f4adf632dcb2823bedb8c52df7e2d76007cf`.
It resolved Lean through `lake env lean --print-prefix` and checked the
release's pinned Lean 4.35.0 version. The fixed inspector SHA-256 is
`1b5338df8f1789b2d2bc2f070b649e381d4007c238ef8a01592466550d120d21`.

The complete outcome and invocation are in [results.json](results.json).
Pre/post snapshots, raw object hashes, the inspector's exact source,
per-part JSON and log are retained alongside it. This replay establishes
stored declaration equality; it is not another kernel run or a Palomar
registry workflow.
