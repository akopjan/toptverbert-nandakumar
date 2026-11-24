# Explicit-report object comparison

The single validation run on 24 November 2026, 09:58:01–09:58:13 UTC,
passed. It used `compare_rebuilt_objects.py` with the existing main gate,
independent clean gate and kernel report supplied explicitly. No build,
proof export or kernel checker was launched.

The adapter compared all 1,314 object files for 438 proof owners. Of these,
1,185 files were byte-identical. The remaining 129 files belonged to 64
modules. The unchanged module-data inspector established strict equality
of their stored declaration records, types, proof/definition bodies and
imports. All main objects matched the selected kernel report's input
hashes. Source files, objects, tools, diagnostic inputs and preserved
historical evidence remained unchanged.

`results.json` records the exact selected paths, commands, outcomes and
input bindings. `ADAPTER_REVIEW.json` records the adapter hashes and the
read-only comparison with its frozen predecessor: all 26 `require` calls
have identical Python ASTs. The only implementation changes select the
three reports from mandatory command-line arguments, record their paths
and use the new adapter's name for its preserved copy. The CLI description
was updated accordingly.

The earlier `reproduce_object_comparison.py` and its results remain
unchanged. That adapter binds main objects to the archived release reports.
The new adapter accepts newly produced reports while retaining exactly the
same checks. To compare independently rebuilt trees, follow the build,
kernel and comparison commands in [the verification guide](../README.md).

The output directory must be new and below the main project's
`verification/` directory. Relative report paths are interpreted from the
main project. Opaque environment-extension payloads are outside the stored
declaration comparison, as in the original inspector.

| File | SHA-256 |
| --- | --- |
| `compare_rebuilt_objects.py` | `5e06d69e4142d9c323426d524ffd8c1d1ab1e8fafcae2ac4520597d0d2e1779a` |
| Frozen `reproduce_object_comparison.py` | `f5498b044db2227e463c762a5b11f4adf632dcb2823bedb8c52df7e2d76007cf` |
| `results.json` | `f0c475932c91e604245dffc091a95f082cb88591b916de77b3e5d458ec3940b8` |
