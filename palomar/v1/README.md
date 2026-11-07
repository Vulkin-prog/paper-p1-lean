# P1 candidate registration interfaces

All seven independently meaningful families below have passed local statement
comparison and both Lean and NanoDa with bubblewrap isolation enabled. They
select **27 declarations**, separately from the complete **167-result revised
manuscript correspondence**. Their immutable local receipts and original
compressed logs preserve exactly what was checked.

| Family | Selected declarations | Comparator configuration | Metadata and local evidence |
|---|---:|---|---|
| Ordinary smooth integers in logarithmic intervals | 3 | [configuration](../../comparator/p1_smooth_windows.json) | [metadata](smooth_windows/formalization.yaml), [passed local comparison and both kernels](smooth_windows/qualification.json) |
| Prescribed squarefree kernels of shifted split products | 4 | [configuration](../../comparator/p1_quadratic_kernels.json) | [metadata](quadratic_kernels/formalization.yaml), [passed local comparison and both kernels](quadratic_kernels/qualification.json) |
| Asymmetric parity-space profiles | 3 | [configuration](../../comparator/p1_asymmetric_profiles.json) | [metadata](asymmetric_profiles/formalization.yaml), [passed local comparison and both kernels](asymmetric_profiles/qualification.json) |
| Optimal quadratic Poisson–Charlier approximation | 4 | [configuration](../../comparator/p1_quadratic_approximation.json) | [metadata](quadratic_approximation/formalization.yaml), [passed local comparison and both kernels](quadratic_approximation/qualification.json) |
| Exact Poisson scales and quantized mean bias | 5 | [configuration](../../comparator/p1_poisson_scales.json) | [metadata](poisson_scales/formalization.yaml), [passed local comparison and both kernels](poisson_scales/qualification.json) |
| Universal arithmetic anchor obstructions | 4 | [configuration](../../comparator/p1_private_obstruction.json) | [metadata](private_obstruction/formalization.yaml), [passed local comparison and both kernels](private_obstruction/qualification.json) |
| Actual conditioning and colored replica target sums | 4 | [configuration](../../comparator/p1_conditioning.json) | [metadata](conditioning/formalization.yaml), [passed local comparison and both kernels](conditioning/qualification.json) |

Each configuration names its standalone Mathlib-only Challenge and complete
Solution. Only the exact selected Challenge statements have deliberate proof
holes. No substantive proof, Solution or axiom audit imports a Challenge. The
current community v0.4 metadata schema is checked separately.

The latest whole-project replay passed **18,551 build jobs** and **19,373 theorem
axiom checks**. Earlier receipts retain their own historical source inventories.
The local [evidence checker](../../scripts/check_registry_evidence.py) validates
their hashes, exact source files, imported project proofs, actual export and
kernel success markers, full-build counts and complete audit selections. It
rejects incomplete, duplicate and forbidden-axiom audits.

The [pinned full reusable workflow](../../.github/workflows/palomar-preflight.yml)
is prepared at PalomarSubmission commit
14aa8d6b3c2f14a8540605e37144560b9a00e7e7, using `mode: full` and
`execution_profile: palomar-standard-v1`. It requires an immutable source
commit and the confirmed human relationship, runs one family at a time and
preserves one mechanical report per family. It has not yet been dispatched.
Local qualification, full mechanical preflight, editorial review and permanent
registration are separate stages. No submission or registry entry is claimed.

The Paper C workflow reference is commit
b9fa9ba490f201b408a302a86f1594ee620b228b. Its Lean 4.34 tools are not reused.
Model ports retain their precise licence and source attribution. See the
[preparation plan](../../docs/PALOMAR_PLAN.md) for the current procedure.
