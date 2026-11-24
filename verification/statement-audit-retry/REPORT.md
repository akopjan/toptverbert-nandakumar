# Literal independent statement check

Lean accepted both original Challenge statements using the actual Solution
proofs. This check is generated from the independent `Challenge.lean` itself,
not from a manually restated pair of examples.

- Completed: `2026-11-24T04:52:11.287622+00:00`.
- Lean exit code: **0**.
- Runtime: 32.673 seconds.
- Original Challenge SHA-256: `cfd2f4648eee325094309614e72c032d7822cb1c23f09e941b86c36c667cff05`.
- Solution source SHA-256: `41225428eeac553dc40649334f81dbdf25414cdebf141cb1618ddcd014544d23`.
- Generated source SHA-256: `ac75050a52d78b81906b2d11f777be63d75b1098a75a036ad2c452e9030d7d86`.
- Input changes during the run: none.

The generator adds `public import Solution`, changes the opening and closing
namespace to `AkopyanChallengeAudit`, and replaces the two proof placeholders
with `exact AkopyanSixfold.tverberg_counterexample` and
`exact AkopyanSixfold.convex_partition_counterexample d hd`. Reversing exactly
these five changes reconstructs the original Challenge bytes. All seven
interface definitions, both full statements, and the bound `36 ≤ d` are
therefore preserved. Lean's successful `exact` checks establish definitional
equality of these literal independent statements with the proved Solution
types.

The checked claims are the original simplex theorem A and the unconditional
convex-partition theorem for **d ≥ 36**. This does not check or assert the
stronger d > 17 conclusion. It is a kernel-level statement gate and was not a
run of the sandboxed Palomar Comparator. Independent proof-body checks are
reported separately in the original-kernels result.

The earlier attempt lost its execution session and remained incomplete;
`../statement-audit/interruption.json` records that event. This report relies
only on the completed retry. The exact generator, input hashes, command and
return code are retained in `generator-used.py` and `results.json`.
