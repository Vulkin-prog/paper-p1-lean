# P1 candidate registration interfaces

These interfaces are being prepared after the complete revised 167-result
proof correspondence. They select independently meaningful mathematical
families; a selected declaration count is not the manuscript coverage count.

| Family | Selected declarations | Comparator configuration | Metadata and local evidence |
|---|---:|---|---|
| Ordinary smooth integers in logarithmic intervals | 3 | [configuration](../../comparator/p1_smooth_windows.json) | [metadata](smooth_windows/formalization.yaml), [passed local comparison and both kernels](smooth_windows/qualification.json) |
| Prescribed squarefree kernels of shifted split products | 4 | [configuration](../../comparator/p1_quadratic_kernels.json) | [metadata](quadratic_kernels/formalization.yaml), [passed local comparison and both kernels](quadratic_kernels/qualification.json) |
| Asymmetric parity-space profiles | 3 | [configuration](../../comparator/p1_asymmetric_profiles.json) | [metadata](asymmetric_profiles/formalization.yaml); local comparison pending |
| Optimal quadratic Poisson--Charlier approximation | 4 | [configuration](../../comparator/p1_quadratic_approximation.json) | [metadata](quadratic_approximation/formalization.yaml); local comparison pending |

Each standalone Challenge imports only Mathlib. Its deliberate statement holes
are the exact declarations selected by its Comparator configuration. Each
matched Solution contains the proved implementations and imports the substantive development.
Neither PaperP1 nor the proof audit imports a Challenge.

The pinned Lean 4.36.0-rc2 toolchain includes Comparator, its exporter and
independent kernels. Local compilation, statement comparison, kernel replay,
the complete Palomar reusable workflow, editorial review and permanent
registration are distinct stages. Qualification receipts are added only after
the relevant commands have actually succeeded. No registry entry is claimed.

The first family passed Comparator, Lean's kernel and bundled NanoDa with
bubblewrap isolation enabled at source commit
eb3039966bdeeb0b4e5e895bc3bbecfe4222342a. The complete project build passed
18,537 jobs, and the audit covers 19,291 theorems: the 19,288 substantive
theorems plus three registry Solution wrappers. The compressed original logs
and their hashes are preserved under evidence. The complete reusable Palomar
workflow remains a separate required stage before intake.

The prescribed-kernel family passed the same isolated statement comparison
and Lean/NanoDa checks at source commit
c85100fb3371cfe2869cf98e2fb8e54eed9a231c. The complete project build passed
18,541 jobs and its extended audit checked 19,299 theorems. Its metadata and
the smooth-window metadata also pass the current community v0.4 schema;
author names use that schema's string representation, with GitHub and ORCID
identifiers retained explicitly in author_identifiers. Both families record
the exact Paper C source reuse in their related-formalization metadata.

The Paper C layout was inspected at commit
b9fa9ba490f201b408a302a86f1594ee620b228b as a workflow reference. Its Lean 4.34
verification tools were not copied into this project. Current Palomar tool
revisions and requirements are recorded in [the preparation plan](../../docs/PALOMAR_PLAN.md).
