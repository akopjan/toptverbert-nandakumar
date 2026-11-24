# Compilation of the immutable final proof snapshot from ZIP

The source ZIP recorded in `preparation.json` was extracted into a new
directory on 24 November 2026 at 09:55:42 UTC. It contained the exact final
472 frozen proof/build inputs. No project object directory was present.
Only the nine already verified, pinned dependency caches were linked.

The unchanged `scripts/verify.sh` passed structure, provenance and all
37 infrastructure tests, and its full `lake build` successfully compiled
the project from this single immutable source snapshot. The build log ends
with `Build completed successfully (9491 jobs).` Project sources were not
edited or resynchronized during this compilation, and no existing project
objects were copied into the checkout.

The first verifier invocation selected a log directory in the main project,
outside the extracted checkout. After the successful build, the statement
checker correctly rejected that output location. The first overall driver
therefore exited **2**, as recorded in `DRIVER_RESULT.json`. The original
verifier's initial `results.json` marker is retained verbatim; it is not a
claim that this first invocation is still running or passed.

The output path was corrected to a new directory inside the extracted
checkout. The same unchanged verifier then completed all six stages at
**10:23:29 UTC**, including the literal statement audit and a fresh
all-owner axiom audit. It reused the completed project objects: the second
build log contains zero newly built module messages. All 472 input hashes
match the main gate and remained unchanged.

The successful report and logs are preserved byte for byte in
[`../d18-archive-final/`](../d18-archive-final/), with their copy record.
This is one clean compilation of the final frozen proof snapshot and a
completed subsequent gate after correcting its output location. It is
separate from the earlier cumulative source build, which allowed
source-only finalization before its successful gate.

The input ZIP predates these new verification records and some final
documentation packaging. Its proof/build inputs are exactly the same as
those in the final delivery; the final archive validator binds that
delivered payload separately. The input ZIP's hash is recorded for
traceability, not substituted for the final delivery ZIP hash.
