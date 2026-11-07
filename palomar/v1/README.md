# P1 candidate registration interfaces

These interfaces are being prepared after the complete revised 167-result
proof correspondence. They select independently meaningful mathematical
families; a selected declaration count is not the manuscript coverage count.

| Family | Selected declarations | Comparator configuration | Metadata and local evidence |
|---|---:|---|---|
| Ordinary smooth integers in logarithmic intervals | 3 | [configuration](../../comparator/p1_smooth_windows.json) | [metadata](smooth_windows/formalization.yaml), [passed local comparison and both kernels](smooth_windows/qualification.json) |
| Prescribed squarefree kernels of shifted split products | 4 | [configuration](../../comparator/p1_quadratic_kernels.json) | [metadata](quadratic_kernels/formalization.yaml), [passed local comparison and both kernels](quadratic_kernels/qualification.json) |
| Universal arithmetic anchor obstructions | 4 | [configuration](../../comparator/p1_private_obstruction.json) | [metadata](private_obstruction/formalization.yaml), [passed local comparison and both kernels](private_obstruction/qualification.json) |
| Asymmetric parity-space profiles | 3 | [configuration](../../comparator/p1_asymmetric_profiles.json) | [metadata](asymmetric_profiles/formalization.yaml), [passed local comparison and both kernels](asymmetric_profiles/qualification.json) |
| Exact Poisson scales and quantized mean bias | 5 | [configuration](../../comparator/p1_poisson_scales.json) | [metadata](poisson_scales/formalization.yaml), [passed local comparison and both kernels](poisson_scales/qualification.json) |
| Optimal quadratic Poisson--Charlier approximation | 4 | [configuration](../../comparator/p1_quadratic_approximation.json) | [metadata](quadratic_approximation/formalization.yaml), [passed local comparison and both kernels](quadratic_approximation/qualification.json) |

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

The asymmetric-profile and optimal-quadratic families passed the same isolated
statement comparison and both kernels at source commit
3b777fec1dc58fb209b48c4e8e15d0de1fcd51c3. Together the four families select 14
statements. Their complete build passed 18,545 jobs and the extended source
audit checked 19,317 theorems. All four metadata files pass the community v0.4
schema. The reusable workflow and registration remain separate pending stages.

The exact Poisson-scale family passed the isolated comparison and both kernels
at 03f27990 (see its receipt for the full immutable source SHA). Its five
selections bring the locally checked total to 19 in five families. The full
build passed 18,547 jobs and the extended audit checked 19,341 theorems. Its
conditional nominal-mean lower comparison asserts no infinitude of biased
scales. The literal moving residue coefficient and both Poisson means are
retained.

The universal private-forcing family passed the isolated comparison and both
kernels at b606e132 (full source SHA in its receipt), retaining both exact
T19.17 coefficients and every independent auxiliary probability law. Its
construction and full-observable conditional law are separate checked
selections. The six locally checked families select 23 declarations. The full
build passed 18,549 jobs and the extended audit checked 19,360 theorems.
