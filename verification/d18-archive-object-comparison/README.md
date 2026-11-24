# Final archive-source objects versus the checked main objects

The configurable adapter compared the main tree with the independent
`release-source-build` checkout, after its completed six-stage gate. Both
source snapshots match the same 472 frozen release inputs.

**PASS:** all 1,314 object files for 438 proof-module owners were compared.
1,236 were byte-identical; the remaining 78 files belonged to 64 modules.
The unchanged inspector proved strict equality of all stored declaration
records, types, proof/definition bodies, recursor right-hand sides, names,
module flags and imports for those differing modules. It did not compare
opaque environment-extension payloads.

Every main object matches the input hash retained by the successful final
proof-export and three-checker report. Thus the new clean compilation of
the immutable source ZIP is linked to those previously checked proof bodies.
This comparison did not run a new export or kernel replay.

All source and object inputs, tools, copied diagnostics and historical
evidence remained unchanged. The exact command, selected gate reports,
timestamps and hashes are in `results.json` and its adjacent records.

The first archive-build driver and the later completed gate are documented
in `../d18-archive-build/README.md` and `../d18-archive-final/`. The original
output-path refusal remains recorded; it is not treated as a passed gate.
