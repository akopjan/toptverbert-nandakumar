# Review of root publication wording

Reviewed on 2026-11-24 against the current A+B18 specification and the new
release evidence. This review did not edit `README.md`,
`FORMALIZATION_STATUS.md` or `CHANGES.md`.

## Finding requiring synchronization

In `FORMALIZATION_STATUS.md`, the paragraph inside **Completed verifications**
still groups the separate source rebuild, compiled-interface comparison and
independent kernels as continuing. The first two now have completed evidence:

- compiled-interface comparison: PASS at `08:59:09 UTC`, nine types and
  seven definition bodies identical, 1,681 unchanged bound inputs;
- cumulative source rebuild: PASS at `09:01:10 UTC`, all six stages zero,
  the same 16,765-declaration/438-owner audit and the same 472 input hashes
  as the main release gate.

The kernel replay is still pending, and the new local Comparator attempt
remains blocked at sandbox setup. This synchronization finding was sent to
the root document owner. It concerns status wording, not the mathematical
statement or proof.

## No other substantive contradiction found

The three root documents consistently identify the unconditional theorem
with `17 < d`, retain theorem A, and distinguish an almost-six embedding
from an injective map. They describe the actual body topology and absolutely
continuous measure, preserve the original `Solution.lean`, and keep the
standard-axiom audit separate from Challenge's deliberate placeholders.

They do not claim Palomar acceptance, an executed remote workflow, identified
human maintainers, a project licence, or a published paper proving the exact
result. They preserve the archive attribution without asserting priority.
The stated 472 final-gate inputs agree with `d18-final-retry/results.json`.
All local Markdown links in these three documents resolve, and the historical
documentation directory named in `CHANGES.md` exists.

Different source counts refer to different scopes: the full owner audit
contains 438 proof-module owners; the publication proof closure has 418
local modules; the independent compiled-interface diagnostic additionally
includes Challenge, giving 419 source modules. The publication header scan
also includes diagnostic Lean files. These counts are not contradictory.

## Reviewed snapshots

| File | SHA-256 |
|---|---|
| `README.md` | `585e4f05adbe29195b8c130ea051bdfd175785e6625f0d8ecd4a7025abcf4247` |
| `FORMALIZATION_STATUS.md` | `740293eb3b275a8e1d9b551f696d51785e6c0e681f0bad01d735336be1479703` |
| `CHANGES.md` | `f18e8e14c0d65d329b0df01a903eb34346e2ca11847921550e9687009d493b62` |

Later updates to the final verification status are expected. This report
records the inspected snapshots rather than asserting that the stale
paragraph remains in a subsequent release.

## Resolution

The root document owner corrected the status paragraph at **09:03 UTC**.
A subsequent read confirms that `FORMALIZATION_STATUS.md` now records both
compiled-interface PASS and cumulative source-build PASS, while retaining
pending independent replay and the blocked local Comparator accurately.
The initial finding and its original snapshot hashes above are preserved
as the review history; the finding is **resolved**.

Resolved status-document SHA-256: `9a78d3e70175659f982d3dda5278434b35024e6226f440e99405283b344a9f5e`.

## Later final-evidence review

The preceding pending-replay language records the state at **09:03 UTC**,
not the final release status. The selected-proof replay subsequently passed
all three bundled components at **09:15:21 UTC**, and approved con-ron
accepted the same export at **09:18:19 UTC**. The local Comparator remains
blocked at sandbox setup. The current documentation review is recorded in
[PUBLICATION_DOCUMENTATION_REVIEW.md](../d18-release/PUBLICATION_DOCUMENTATION_REVIEW.md);
the original finding and snapshot hashes above remain historical evidence.
