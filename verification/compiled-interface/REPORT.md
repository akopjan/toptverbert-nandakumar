# Separately compiled interface comparison

**Passed:** the actual compiled Challenge and Solution have identical kernel
expressions for all nine interface types and all seven definition bodies.
The driver returned exit 0 at `2026-11-24T05:30:23.841426+00:00`. No theorem proof body
was compared by this diagnostic.

## What was compared

The two inspector processes each import exactly one compiled project module:
`Challenge` or `Solution`. In particular, the Challenge inspection does not
import Solution and does not re-elaborate the Challenge in the Solution's
context. Its only project import, including transitive imports, is `Challenge`.
The Solution process does not import Challenge.

The inspected private environment requires seven genuine definition records
and two genuine theorem records. A recursive structural serializer records
every expression constructor, application, de Bruijn index, constant name,
universe level, binder annotation, literal, projection, and let-expression.
Only elaborator metadata and the display names of bound variables are omitted.
Names are represented by their exact recursive constructors, not by a possibly
ambiguous pretty-printed string. All serialized types and definition values
are required to be closed.

The compared definitions are `simplex`, `DisjointSupports`,
`IsAlmostSixEmbedding`, `Ambient`, `Body`, `unitBall`, and `IsSixPartition`,
all in namespace `AkopyanSixfold`. The theorem types are
`tverberg_counterexample` and `convex_partition_counterexample`.
The latter retains the original hypothesis **36 ≤ d**.

The structural JSON records agree exactly. Thus this check also detects
changes in inserted typeclass arguments and constant names that a textual
restatement might not expose. It does not rely on pretty-printing equality.

## Observed execution

| Imported module | Exit | Seconds |
| --- | ---: | ---: |
| Challenge | 0 | 6.377 |
| Solution | 0 | 11.423 |

The inspected source files, `lean-toolchain`, `lake-manifest.json`, compiled
`.olean` and `.olean.private` files, serializer, and driver were hashed before
and after. Every recorded input remained byte-for-byte unchanged. The exact
hashes and commands are in `results.json`; `Challenge.json` and `Solution.json`
contain the independently obtained records and import lists.

To reproduce after building the pinned project:

```sh
python3 verification/compiled-interface/compare_compiled_interfaces.py
```

The driver generates the two small inspection modules in this directory and
runs them sequentially with `lake env lean -j 1`.

## Scope

This is an additional structural diagnostic. It is **not** the official
sandboxed Palomar Comparator and does not establish registry acceptance.
It verifies neither theorem proofs nor a strengthened dimension bound.
The original theorem proof bodies were checked separately by Lean checker,
NanoDa, and con-ron; the new project declarations have a separate all-owner
axiom audit. These distinct checks are not relabelled as a successful run
of the official Comparator.
