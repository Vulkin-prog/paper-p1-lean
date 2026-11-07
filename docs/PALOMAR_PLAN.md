# Palomar preparation

The mathematical correspondence is complete for the separate version 1.7 draft:
**167 proved statements**, comprising all 73 article and all 94 companion
results. Current mathematical checkpoint: P1-MATH-0985. The original version
1.6 retains its exact bytes and its two false-original statuses; its 165 other
statements are proved. Both revised PDFs and their visual checks are preserved.

## Completed local qualification

[Nine selected families](../palomar/v1/README.md), with **37 declarations**,
have passed actual statement comparison, Lean and bundled NanoDa, with the
bubblewrap boundary enabled. Every family has its own immutable source commit,
configuration, standalone Mathlib-only Challenge, complete Solution, metadata,
qualification receipt and compressed original logs. The latest complete build
passed **18,555 jobs** and the direct source-discovered audit checked **19,402
theorems**, allowing only `propext`, `Classical.choice` and `Quot.sound`.

All nine families also passed supplementary verified con-ron, Lean and NanoDa
replays. Their [source-bound records](../palomar/v1/supplementary/README.md)
preserve binary identities, original logs, six positive/ill-typed controls,
metadata shape checks and a historical source-layout scan. These local checks
do not replace the complete workflow. The additional interfaces introduce no
new mathematical-change entry.

The [evidence checker](../scripts/check_registry_evidence.py) verifies every
receipt against its original commit and inventory, its preserved log hashes,
actual successful exports and kernels, and the unchanged current statement,
Solution, imported project proofs, compiler and dependency pins. Historical
receipts do not silently acquire the later audit's larger selection. Missing
output, repeated declarations, forbidden axioms and changed imported proofs
are rejected. The original first receipt's build/audit counts were added from
its unchanged preserved logs and checked source inventory.

Run the local preparation checks with:

```sh
python3 scripts/check_disk.py
python3 scripts/check_sources.py
python3 scripts/check_revised_sources.py --require-proved
python3 scripts/update_audit.py --check
python3 scripts/check_registry_candidates.py
python3 scripts/check_palomar_sources.py
python3 scripts/check_registry_evidence.py --require-all
```

These checks establish their stated local scope. They do not replace the
complete reusable Palomar workflow or its canonical Challenge provenance audit.

## Exact compiler and verifier

Lean is fixed to **v4.36.0-rc2**, and Mathlib to
9d581dfff2e41de989072ea63abf3daf69311520. Comparator, exporter and kernels are
those supplied by that toolchain. The Paper C Lean 4.34 binaries are not used.
The invocation is `lake env lake comparator --config <configuration>` so the
matching bundled NanoDa is on the executable search path.

Official tooling was checked on 7 November 2026 at:

- [PalomarSubmission 14aa8d6b3c2f14a8540605e37144560b9a00e7e7](https://github.com/PalomarRegistry/PalomarSubmission/tree/14aa8d6b3c2f14a8540605e37144560b9a00e7e7).
- [PalomarPolicy 28bd48b9b71bbb2a82c718ce761d5a4220ef8e60](https://github.com/PalomarRegistry/PalomarPolicy/tree/28bd48b9b71bbb2a82c718ce761d5a4220ef8e60).
- [Current intake protocol](https://submit.palomar-registry.org/llms.txt).

Every committed Lean file has a module header and at most 10,000 lines. Each
Challenge has at most 1,000 lines and 100 KiB and imports only canonical
Mathlib surfaces. The audit uses a compact Lean command over its separate JSON
inventory. The full project snapshot stays below the 500 MiB source limit.

## Complete reusable workflow

The [original workflow caller](../.github/workflows/palomar-preflight.yml) selects
exactly seven families; the [additional caller](../.github/workflows/palomar-preflight-additional.yml)
selects factorial cumulants and the moment obstruction. Both are prepared.
Both its `uses` revision and `pipeline_commit` are fixed to the exact same
PalomarSubmission SHA above. It uses `mode: full`, the required external
`palomar-standard-v1` profile, read-only repository permissions and one family
at a time. Each family has a 12-character lowercase alphanumeric request id
and its explicit configuration and metadata paths. No Palomar state or
credential is supplied to this predictive preflight.

Dispatch requires a full immutable source commit and the confirmed supported
human relationship. The full workflow has not yet been run. Its report must
actually say `status: pass` for each exact target before intake. Preparation
errors should be corrected in the indicated inputs, rather than misreported
as mathematical failures. Authenticated capacity failures need their actual
reported resolution; local sandbox settings must not be weakened.

## Intake and registration

Registrations follow the completed formalization, as the user requested. No
submission, editorial decision or permanent identifier is currently asserted.
The protocol requires confirmation of the human relationship before dispatch.
Before ordinary HTTPS intake, present the exact repository, 40-character source
SHA, configuration paths and relationship declaration for human agreement.
The authenticated GitHub CLI path may then prove repository write access using
the prescribed temporary tag and secret gist, deleting both afterwards. Never
automate the Palomar browser sign-in or recovery flow.

Intake, mechanical verification, editorial review and registration remain
distinct. Before permanent registration, show the actual private review to the
user and obtain their decision about publishing that exact review. Preserve
its digest and record a registry identifier only after actual issuance. Do not
invent a DOI or publication identifier for the working manuscript.
