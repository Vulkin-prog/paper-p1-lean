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
| `PaperC/Affine/System.lean`, `2744f75ed26de5014d35c48fad5aab8471724294` | `PaperP1/Affine/System.lean`, affine compatibility, fiber/kernel equivalence and exact counts | Module/public declarations and namespace; `if_pos`/`if_neg` replaced by `ite_eq_left`/`ite_eq_right` |
| `PaperC/Affine/Fourier.lean`, `d11d2472de69e4740591abd96a6161502cf55669` | `PaperP1/Affine/Fourier.lean`, character orthogonality and division-free affine Fourier identity | Module/public declarations, namespace, ite rename and unused simp argument removal; helper theorem made public for direct axiom auditing |
| `PaperC/Affine/Probability.lean`, `40d959c053dc27bfb197db83bff1e673fed55644` | `PaperP1/Affine/Probability.lean`, rational uniform affine probability formulas | Module/public declarations, namespace and ite lemma renames |
| `PaperC/Affine/StartSystem.lean`, `097a8645a5622d6b7541cc52beac2e3129392b11` | `PaperP1/Affine/StartSystem.lean`, full run-start affine encoding | Module/public declarations, opened namespaces and ite lemma renames; the finite-model `startAt` alias retains the original event |
| `PaperCPrel8/CenteredAffineBlocks.lean`, `8f021697109464c4ed6adf8c4e59d7aa83b13854` | Proof patterns for finite sum splitting and character-product induction in `PaperP1/Affine/CenteredFourier.lean` | New effective subspace indices, heterogeneous actual marginal rates, one uniform sign space and direct full-support relation kernel; the old nominal-row reference rate is not reused |
| `PaperC/Model/InfiniteRademacher.lean`, `24341f93a3b6b509bf542919b3a1cd38c6db54f6` | `PaperP1/Model/InfiniteRademacher.lean`, full infinite prime-sign construction and no-constant-tail proof | Module/public declarations and namespaces; obsolete PMF uniform law replaced with `Measure.uniformOfFinset univ`, its normalization and singleton law checked directly; renamed set lemmas; probability instance exported |
| `PaperC/Probability/InfiniteCylinderTransfer.lean`, `8347a9daff87f8ae8964764fb41aa6c7d3080247` | `PaperP1/Probability/InfiniteCylinderTransfer.lean`, full restriction/value/product-measure bridge | Module/public declarations and namespaces; exact prime enumeration and cutoff conventions retained |
| `PaperC/Probability/InfiniteStartProbabilityTransfer.lean`, `54691ea29aa646390423c179c18695ceb03c45da` | Start/count restriction proof patterns in `PaperP1/Model/InfiniteStarts.lean` | P1 Boolean indicators, actual real finite weights and full measure-valued count law; no old asymptotic imports; Bochner centered-moment transport added |
| `PaperC/Affine/TwoStartSystem.lean`, `94e01496f72b742b4f85e6c2630de078e3cddb41` | One-start complete-boundary section in `PaperP1/Affine/StartBoundary.lean` | Extracted from two-start material; public helper for auditing; unused simp arguments removed; module declarations, namespaces and ring tactic updated |
| `PaperC/Affine/StartBoundaryRange.lean`, `6ea852e5f1071357beae725b34510dc8ec69e357` | `PaperP1/Affine/StartBoundaryRange.lean`, full even-boundary range and equivalence | One-start dependency; module declarations, namespaces and redundant simp arguments updated |
| `PaperC/Affine/RelationBoundaryIff.lean`, `28382a2759144a100cd851af5a8f576cd91de5d8` | Two one-start incidence/sum helpers in `PaperP1/Affine/StartCharacterSpace.lean` | Helpers public and renamed, module declarations and namespaces updated; remaining square-class/character equivalence is new |

All ported statements recompile with warnings as errors and are included in the
generated kernel-axiom audit. This port does not import the old arithmetic
estimates or any literature assumptions. The unrestricted infinite prime-sign
measure is constructed, and the finite-cylinder consistency is now proved.

The generic affine Fourier identity is a checked precursor to P1's full-support
centered formula. The latter is now complete using additional proofs of the
effective-space identification and actual infinite-measure transport. The
ported generic identity alone does not establish P1 coverage. Upstream lemma
numbers in the ported docstrings refer to Paper C.

`Affine/RealProbability.lean` now connects cardinality ratios to the actual
normalized real uniform weights and proves that a compatible system has mass
`2⁻ʳ` for its effective rank. `Model/StartProbability.lean` applies this formula
to every positive-length start, preserving incompatible windows. These are new
bridges, rather than an identification of nominal row count with effective rank.
`Affine/Characters.lean` proves character expansions and actual marginals on
arbitrary effective dual subspaces, using evaluations at a local solution.
`CenteredFourier.lean`, `RelativeNullity.lean` and `FourierBound.lean` give the
full-support identity, dimension deficit, sharper bound and relation existence
on those effective spaces. `Model/StartFourier.lean` identifies the actual run
events with effective affine row spaces and applies these results to their
actual centered moments, including finite-set reindexing. The new
`Probability/CylinderExpectations.lean` identifies finite product-measure
weights with P1's actual real weights and transports all finite-cylinder
expectations. `Model/InfiniteStarts.lean` and `InfiniteStartFourier.lean`
transport actual marginals, centered moments, the full count law and the
full-support formula to the infinite prime-sign probability measure.

`Arithmetic/EvenSquareClasses.lean`, `Model/ParityCharacters.lean` and the new
parts of `Affine/StartCharacterSpace.lean` construct the image of even window
selections, prove its exact rational-square criterion, and identify it with
actual row characters. `SquareClassRelations.lean` transports the entire
relative-relation kernel, preserving its dimension. `SquareClassFourier.lean`
reindexes the full-support formula and proves every conclusion of P1 Lemma 4.2
on these spaces under the actual infinite measure. See
[statement alignment](FOURIER_ALIGNMENT.md).

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
