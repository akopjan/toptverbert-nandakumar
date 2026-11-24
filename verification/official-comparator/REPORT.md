# Official Comparator attempt

The unmodified official `scripts/verify-comparator.sh` was invoked against the
actual project and its submitted comparator configuration. The configured
claims were the original A theorem and the unconditional B theorem for d ≥ 36.
The command returned **exit 1** after **9.828 seconds** at
`2026-11-24T05:31:49.969361+00:00`.

The Mathlib cache step succeeded: no downloads were needed and all **9031**
artifacts were already decompressed. The subsequent Comparator sandbox startup
failed with the exact message:

```text
bwrap: Failed to mount tmpfs: No such file or directory
error: Child exited with 1
```

This is the observed bubblewrap startup failure. The log does not identify a
missing mount path or establish a permission-denial cause. The configured
workspace and `TMPDIR` directory exist; creating and reading the generated
Comparator configuration succeeded before this failure. A later read-only inspection of the pinned `Lake/CLI/Check.lean` found that
the sandbox explicitly masks `/home`, `/root`, `/run/user`, and `/tmp`. In
this managed filesystem `/root`, `/run`, `/run/user`, and `/tmp` are absent.
These are outside the permitted workspace write roots, so no host-directory
creation or sandbox alteration was attempted. This observation is consistent
with the reported ENOENT; it does not identify which mount failed. See
`mount-target-observations.json`.

No isolation flag was disabled, no modified sandbox command was substituted,
and no privilege escalation was requested. The original sources, scripts and
configuration remained unchanged. The official script SHA-256 is
`4fefa0e6c779448143b3164f56e96c3b6f719de67da335fa445127ab55f9b1e2`; bubblewrap reported `bubblewrap 0.12.0`.

**The full sandboxed Comparator has not accepted this project in this
environment.** The successful independent component kernels, all-owner audit,
and literal statement checks are recorded separately and do not turn this
failed workflow attempt into a successful Comparator run. The supplied CI
workflow invokes this same official script in its Linux runner.

Exact command, input hashes, exit code, timestamps, and read-only directory
observations are in `results.json`; the complete output is in `run.log`.
