# Paper C reuse record

Reference repository: https://github.com/Vulkin-prog/paper-c-lean

Inspected main snapshot: `b9fa9ba490f201b408a302a86f1594ee620b228b`.
That snapshot uses Lean **4.34.0** and Mathlib **v4.34.0**; the new project uses
Lean **4.36.0-rc2** and Mathlib's matching immutable revision.

The parity-vector module and selected finite-model definitions/proofs have now
been ported and rebuilt under Lean 4.36.0-rc2. The remaining areas below are
candidates for a dependency and statement audit.

## Validated ports

All source files below come from the exact snapshot named above, under its
Apache-2.0 licence. Attribution is retained in the new module headers. No old
compiled artifacts were copied.

| Upstream path and Git blob | Target and scope | Adaptation |
|---|---|---|
| `PaperC/Arithmetic/ParityVector.lean`, `9277d0dc8d7291c9a2c26d590c4db2aa4fae00c8` | `PaperP1/Arithmetic/ParityVector.lean`, full parity-vector development | New module/public declarations, namespace and explicit product import; deprecated `Nat.prod_pow_factorization_eq_self` replaced by `Nat.factorization_prod_pow_eq_self` |
| `PaperC/Model/FiniteRademacher.lean`, `8616aff14971892844ce097e3a4e2c1ef55868d5` | `PaperP1/Model/FiniteRademacher.lean`, prime coordinates, value/linear map, phase, multiplicativity, dyadic cutoff/block | New probability representation using normalized nonnegative real weights; additional sign interpretation, boundary cutoff and exact-marginal count-law results |
| `PaperC/Runs/Starts.lean`, `b0a1dc84afbeccee3888f8d914c206c00eb03cbd` | `StartEvent` definition in the new finite-model module | Boundary and constancy convention retained; the rest of the old local-geometry module has not been ported |

All ported statements recompile with warnings as errors and are included in the
generated kernel-axiom audit. This port does not import the old arithmetic
estimates or any literature assumptions. Identification with the unrestricted
infinite prime-sign measure remains an explicit obligation.

## Further candidates

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
