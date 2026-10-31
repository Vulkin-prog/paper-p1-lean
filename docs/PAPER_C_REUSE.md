# Paper C reuse record

Reference repository: https://github.com/Vulkin-prog/paper-c-lean

Inspected main snapshot: `b9fa9ba490f201b408a302a86f1594ee620b228b`.
That snapshot uses Lean **4.34.0** and Mathlib **v4.34.0**; the new project uses
Lean **4.36.0-rc2** and Mathlib's matching immutable revision.

No Lean code has been copied yet. The following are candidates for a dependency
and statement audit, not a claim that their results have been ported.

| Candidate area | Paper C paths | Required comparison |
|---|---|---|
| Prime-sign model | `PaperC/Model/` | Finite/infinite model, complete multiplicativity, cylinders |
| Affine events | `PaperC/Affine/System.lean`, `PaperC/Affine/StartSystem.lean` | Boundary, both signs, local kernels and effective spaces |
| Rational pair structure | `PaperC/Affine/RationalChannelCode.lean` | Exact length convention, canonical code and rank |
| Finite probabilities and factorial moments | `PaperC/Probability/` | Actual marginals, incompatible pairs, repeated indices |
| Arithmetic bounds | `PaperC/Arithmetic/` and related later modules | Required exponents, degree/parameter uniformity and all explicit inputs |
| Submission organization | `docs/PALOMAR_SUBMISSIONS.md`, `comparator/`, `palomar/` | New targets, new toolchain and current verification compatibility |

Before accepting a port, record the exact path and blob/commit, retain Apache-2.0
notices, compare all hypotheses and conclusions to P1, rebuild its transitive
dependency closure and audit the resulting axioms. Never copy `.olean` files
across Lean versions. An organizational example or an old registered entry is
not a certification of this project or of the new arithmetic estimates.
