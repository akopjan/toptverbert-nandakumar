# Source-publication payload privacy review

**Recorded:** 2026-11-24T09:38:59.823481+00:00.
**Result:** no credential or presigned-download payload was identified in
the selected source-release snapshot. This is a bounded payload check,
not a general security audit or a certificate of the future final ZIP.

## Selection and scope

The review imported the actual `selected_files(root)` function from
`/workspace/scratch/9db1b532943d/release_package.py`, with source root
`akopyan-completion`. It scanned only that function's selected files:
**1,087 files, 26,102,561 bytes**, including
**173 log files**. Runtime caches, excluded
large exports and other workspace files were not scanned.

Selector SHA-256:
`f4d8d07af52d0ff4ef251549aa3fd6c658871a0da2310e117376a4490522ed0e`.
Canonical selected path/size/hash inventory SHA-256:
`7f4059bb83cc1da73a2c06dc9dbaef5f6ebbd82139a6d6405effb860bf774209`.
The complete inventory and machine-readable findings are in
[PAYLOAD_PRIVACY_REVIEW.json](PAYLOAD_PRIVACY_REVIEW.json).

## Checks and findings

The byte/text scan covered authorization and bearer patterns, GitHub-token
formats, AWS access-key formats, AWS signed-query fields, Azure-style SAS
signature fields, OAuth/API-key query fields, JWT-shaped values, private-key
block headers, common credential assignments and credentials embedded in
HTTP URLs. Common URL/JSON separator encodings were decoded locally.
No external request or live credential test was made. No candidate secret
value was printed or retained in the review report.

The only candidates were two matches of class `authorization-header` in
`verification/d18-publication/palomar-workflow-reference/verify_submission.py.txt`.
Safe AST inspection, with all literal values removed from its output,
showed a submission-relationship dictionary and its insertion into a report.
They are ordinary source-code references to `authorization_relationship`,
not HTTP authentication headers, literal credentials or signed URLs.
All other scanned pattern classes had zero candidates.

The review changed no selected source, historical log or bound verification
evidence. A post-scan rehash found **0** changes among the
scanned snapshot inputs. No exclusion or redaction was needed.

## Limits

The release selection was still open while PDF and supplementary materials
were being prepared. This review binds the recorded snapshot only; its own
new report files were created afterward. The final archive inventory must
be distinguished from this snapshot. Pattern scanning does not prove the
absence of arbitrary encrypted, obfuscated or previously unknown secrets.
