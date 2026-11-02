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

The following additional algebraic ports support companion T1.1:

| Upstream path and Git blob | Target and scope | Adaptation |
|---|---|---|
| `PaperC/Algebra/IntegerPolynomialRootBound.lean`, `6f30ccf82dcc27834babee1cb2a1a0cdbf73a5f7` | `PaperP1/Algebra/IntegerPolynomialRootBound.lean`, full module | Module/public declarations, namespace and public helpers for complete axiom auditing |
| `PaperC/Algebra/RungeSplitProduct.lean`, `85ecd7bca6da10b0d0b319e08f1d20ba271a0886` | `PaperP1/Algebra/RungeSplitProduct.lean`, full module | Module/public declarations, namespace and public helpers for complete axiom auditing |
| `PaperC/Arithmetic/DyadicGap.lean`, `541350ece22215b85008168918832bfa1498d2aa` | `PaperP1/Arithmetic/DyadicGap.lean`, full module | Module/public declarations, namespace and public helpers for complete axiom auditing |
| `PaperC/Combinatorics/RungeCoefficients.lean`, `ca9d6adab19fb09971b7f1048fe9ee59602ea64c` | `PaperP1/Combinatorics/RungeCoefficients.lean`, full module | Module/public declarations, namespace and public helpers for complete axiom auditing |
| `PaperC/Algebra/RungeTruncation.lean`, `8c8e27f660ac6a9b017059265cde6267d6eb0537` | `PaperP1/Algebra/RungeTruncation.lean`, full module | Module/public declarations, namespace, public audit helpers; dependent-ite lemma renamed |
| `PaperC/Analysis/RungePowerSeries.lean`, `7a6ba6e18ad89ab4d7e343876b5b1c11d3111994` | `PaperP1/Analysis/RungePowerSeries.lean`, full module | Module/public declarations, namespace and public helpers for complete axiom auditing |
| `PaperC/Algebra/RungeQPolynomial.lean`, `4763c81ac2a5dce00982c5a06f6c5326b6b2cab0` | `PaperP1/Algebra/RungeQPolynomial.lean`, through the exact coefficient formula, including high-degree cancellation and nonvanishing; later coarse height/equality estimates excluded | Selected dependency closure; module/public declarations, public helpers, renamed absolute-value import, proposition-local instance style; unused-argument linter suppression removed |

The following ports supply the unconditional polynomial-height route used in
companion T1.2:

| Upstream path and Git blob | Target | Selected scope |
|---|---|---|
| `PaperC/Diophantine/PellInput.lean`, `99025d6105dc01e60fb722a94a81e6e8d96c65aa` | `PaperP1/Diophantine/PellInput.lean` | Only finite counting predicates and exact equation/height definitions |
| `PaperC/Diophantine/QuadraticIdealDivisors.lean`, `91b0b26c5257b95eff99ad2dae57a57e92bd9927` | `PaperP1/Diophantine/QuadraticIdealDivisors.lean` | Full module |
| `PaperC/Diophantine/GeneralizedPell.lean`, `19a257299fe1f2d0223a16fa3cdc938fbf0e142b` | `PaperP1/Diophantine/GeneralizedPell.lean` | Finite ideal, unit-orbit, height and squarefree-reduction proofs; old final conditional estimate excluded |
| `PaperC/Asymptotics/Uniform.lean`, `b81bb994526978962be94312f51e7692ee708b13` | `PaperP1/Asymptotics/Uniform.lean` | Full module |
| `PaperC/Asymptotics/ExpSqrtLog.lean`, `070005b53f66870383fe5ba849c915efe9a8301c` | `PaperP1/Asymptotics/ExpSqrtLog.lean` | Full module |
| `PaperCV282/LogarithmicWordPowers.lean`, `560b73bebb36aeff4d910f0590578d17bafc01a0` | `PaperP1/Asymptotics/LogarithmicWordPowers.lean` | Full module |
| `PaperCV282/DivisorSubpolynomial.lean`, `62d6247c8858194df4fc1fbae80ef75a91fbb7b1` | `PaperP1/Arithmetic/DivisorSubpolynomial.lean` | Full module |
| `PaperCV282/PolynomialPellCount.lean`, `7db829dab1d9e9b89dd22c84b3dca761973b65b7` | `PaperP1/Diophantine/PolynomialPellCount.lean` | Full module |
| `PaperCV282/HostRealPowers.lean`, `d00caddc1443822afe08f449437da5cf1bc67545` | `PaperP1/Asymptotics/RealPowerRoot.lean` | Only the positive integer-root inequality |
| `PaperC/Diophantine/HalterKochConductorDescent.lean`, `6b970b5d96de14a796c4f0ec8fcd30cf3ebe2d11` | `PaperP1/Diophantine/QuadraticOrderConductor.lean` and `PaperP1/Diophantine/HalterKochConductorDescent.lean` | Concrete residue/conductor construction and its public discharge; historical stronger interface excluded |

These counting ports use module/public declarations and P1 namespaces. Historical
submission metadata and unrelated literature interfaces are omitted. Helpers
are public for the generated audit. Deprecated imports and ite/prime lemmas
are updated; a redundant cancellation instance is removed. The concrete
conductor construction is separated from its public discharge into two files,
with distinct named local number-field instances. The logarithmic and
integer-root helpers are extracted without importing the old host-counting
development. No old compiled files are used.

The new P1 square-coefficient divisor injection, combination of branches,
actual positive-solution finite set and real-exponent transport complete the
statement comparison in [QUADRATIC_COUNT_ALIGNMENT.md](QUADRATIC_COUNT_ALIGNMENT.md).
The old stronger exp(log N/log log N) endpoint and its Nicolas--Robin premise
are not imported. The elementary divisor proof is sufficient for P1's stated
subpolynomial rate.

The following generic arithmetic/coding ports prepare companion T1.3:

| Upstream path and Git blob | Target | Scope |
|---|---|---|
| `PaperC/Coding/DefectCodeProposition.lean`, `5380940cae4af4d7ceefcbbc56328e63e26f3f2e` | `PaperP1/Coding/DefectCodeProposition.lean` | Full generic module |
| `PaperC/Arithmetic/DefectivePredicate.lean`, `8ef2a76317383e4830fa9ae3866f171494bccf75` | `PaperP1/Arithmetic/DefectivePredicate.lean` | Full generic module |
| `PaperC/Coding/DefectCodeDistance.lean`, `8ce524b12c64fbd8ed8c9bb1791d4549d110fbc4` | `PaperP1/Coding/DefectCodeDistance.lean` | Full generic module |
| `PaperC/Coding/DefectCodeHamming.lean`, `f8cf3188595a220c196881fa109411f40be3e3a0` | `PaperP1/Coding/DefectCodeHamming.lean` | Full generic module |
| `PaperC/Arithmetic/DefectCounting.lean`, `6cfe401b3062c7bee7285b5a317354f2f5aa1c59` | `PaperP1/Arithmetic/DefectCounting.lean` | Full generic module |
| `PaperC/Arithmetic/DefectParitySupport.lean`, `a3d879a87a1ca539a5bb2d4363465621ce865cc2` | `PaperP1/Arithmetic/DefectParitySupport.lean` | Full generic module |
| `PaperC/Coding/DefectCodeRepresentation.lean`, `c8d938d45b4206d422744e39b9fa01ebadc90074` | `PaperP1/Coding/DefectCodeRepresentation.lean` | Full generic module |
| `PaperC/Coding/DefectCodeRank.lean`, `c177d86eacf5f09650c3e06131d63381b75826b4` | `PaperP1/Coding/DefectCodeRank.lean` | Full generic module |
| `PaperC/Coding/HammingDefectBound.lean`, `c5f03addde8291f6f28cd300981e644fb58be8e5` | `PaperP1/Coding/HammingDefectBound.lean` | Full generic module |
| `PaperC/Coding/DefectCodeRunge.lean`, `7466a01e8d5ab684b7db8f52ce47be4fec5f6d80` | `PaperP1/Coding/DefectCodeRunge.lean` | Full generic module |
| `PaperC/Coding/HammingBound.lean`, `fa57902f4ecda8b61d4b90d6aa50399462a0041b` | `PaperP1/Coding/HammingBound.lean` | Full generic module |
| `PaperC/Arithmetic/RungeTranslation.lean`, `d2db508c4669ba92e9fe0243a53ba5bdafcfa46b` | `PaperP1/Arithmetic/RungeTranslation.lean` | Full generic module |
| `PaperC/Coding/RungeDefectApplication.lean`, `dc51734b5e3f44d17979f5c6e0f2aa15a0ec1a8b` | `PaperP1/Coding/RungeDefectApplication.lean` | Application adapted to the stronger P1 (64R)^d bound, including endpoint monotonicity |
| `PaperC/Coding/IntervalDefectBound.lean`, `dbb7fa8dd13e986eb396d88a883ba011d338752b` | `PaperP1/Coding/LocalDefectBound.lean` | Finite-enumeration and small-cardinality proof patterns only; new intrinsic defective set with separate cutoff and width |

These ports use P1 namespaces and the already ported parity-vector module.
Local prime-two instances are named explicitly. Deprecated ite lemmas and
unused simp arguments are updated; a variable-headed simp attribute on the
representation identity is removed. Public helpers participate in the audit.
P1's new large-odd-kernel dictionary and actual local set complete the finite
statement comparison in [DEFECT_COUNTS_ALIGNMENT.md](DEFECT_COUNTS_ALIGNMENT.md).
No old asymptotic defect bound is imported. Additional new P1 proofs now
complete T1.3, including uniform parameter budgets and affine interval changes.

Additional elementary estimates for the T1.3 local/global rates:

| Upstream path and Git blob | Target | Scope |
|---|---|---|
| `PaperC/Arithmetic/ChebyshevPrimeCount.lean`, `740b2ca02f9ccb3dbdd16ead42294890c653017b` | `PaperP1/Arithmetic/ChebyshevPrimeCount.lean` | Full module; P1 module/public declarations and updated library names |
| `PaperC/Arithmetic/WeightedDefectCounting.lean`, `41f987ccd292fdd51778e53e33ad1cf28951e829` | `PaperP1/Arithmetic/WeightedDefectCounting.lean` | Full module; P1 module/public declarations and updated library names |
| `PaperC/Analysis/ReciprocalSqrtSum.lean`, `a83ea59a265b61fe86f8d27cd8564aeb351b423d` | `PaperP1/Analysis/ReciprocalSqrtSum.lean` | Full module; P1 module/public declarations and updated library names |
| `PaperC/Analysis/SmoothEulerProduct.lean`, `485be317256a3a95021422cd0a28746414264192` | `PaperP1/Analysis/SmoothEulerProduct.lean` | Full module; P1 module/public declarations and updated library names |

Chebyshev counts are expressed directly as the cardinality of the small-prime
finset, avoiding an extra enumeration dependency. The deprecated product
monotonicity name and redundant simp arguments are updated. The new
`Asymptotics/UniformReal.lean` generalizes the reciprocal-power conversion
pattern in `PaperCV282/LogarithmicWordPowers.lean`, blob
`560b73bebb36aeff4d910f0590578d17bafc01a0` at the same snapshot.
`Coding/LocalDefectRate.lean` adapts the finite ratio-budget argument from
the already recorded `IntervalDefectBound.lean` and introduces P1's direct
radius. `Arithmetic/GlobalDefectCount.lean` proves equality with the actual
intrinsic defective set and the uniform real-exponent global bound. The full
T1.3 statement is now complete. The new P1 modules prove the uniform prime
budget, convert to the literal B/log B scale, handle positive integer points
in real affine intervals and preserve the affine vertex boundary. No further
Paper C source file is copied for that completion.

All ported statements recompile with warnings as errors and are included in the
generated kernel-axiom audit. The old final Runge bound
`U ≤ (128 d R)^(2d)` and its analytic tail proof are not imported. New P1
weighted-height and integer-square-gap proofs yield the exact stronger
companion T1.1 bound `U ≤ (64R)^d`; see
[alignment](SPLIT_PRODUCT_ALIGNMENT.md). None of these algebraic ports imports
an unproved literature assumption. The unrestricted infinite prime-sign
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

## Large-prime graph ports for T9.3

All rows use the same exact Paper C commit and Apache-2.0 attribution above.
The graph foundations below are completed by new P1 relation and rank-cost proofs.

| Upstream path and Git blob | Target and scope | Adaptation |
|---|---|---|
| `PaperC/Affine/TwoStartSystem.lean`, `94e01496f72b742b4f85e6c2630de078e3cddb41` | `PaperP1/Affine/TwoWindowLabels.lean`, only the two-copy complete vertex label definition | Uses the existing checked one-window labels; a new P1 private-prime proof replaces the old relational-assignment dependency; no normalization or probability interface is imported |
| `PaperC/Combinatorics/PinnedGraphResolution.lean`, `d7a9b2eac6a49d7969ae9b07cd2f45e72b28e998` | `PaperP1/Combinatorics/PinnedGraphResolution.lean`, full module | One public namespace, named characteristic-two instance, dependent-ite API updates and removal of unused section assumptions on generic lemmas; equivalence, exact dimension and vertex budgets retained |
| `PaperC/Combinatorics/LargePrimeOccurrences.lean`, `087f6299d0c811996e2dfad8c7417f2fa052b446` | `PaperP1/Combinatorics/LargePrimeOccurrences.lean`, full module | Imports only P1 two-window labels and the new private-prime uniqueness bridge; no old relational-assignment module is imported; formal copies retained even for overlapping windows |
| `PaperC/Combinatorics/LargePrimeGraph.lean`, `df0af992c1966fe70befdad84bb0c39f10607e7f` | `PaperP1/Combinatorics/LargePrimeGraph.lean`, full module | Cutoff raised from L+1 to the exact P1 10(L+1); explicit helper and fixed-L arguments preserve the correct occurrence set in all three cardinality calls; ite API updates |
| `PaperC/Combinatorics/LargePrimeGraphResolution.lean`, `93e1f00df97b64c98f664d6e1866eae9cd312c2e` | `PaperP1/Combinatorics/LargePrimeGraphResolution.lean`, full module | Uses the new cutoff graph and generic pinned resolution; removes the unused LargePrimeComponents import; retains D+c, defective-vertex identification and D+2c≤2(L+1); unused base arguments renamed |

## Local rigidity provenance

For the finite local-rigidity proof, the single elementary lemma
`not_dvd_of_dvd_and_dist_lt` is adapted from
`PaperC/LinearAlgebra/PrivatePivots.lean`, Git blob
`899c4303e63e4f631b7aa9a1d8acb96b01792249`, at the reference commit above.
The target is `PaperP1/Arithmetic/PrivateWindowPrimes.lean`. Its hypotheses and
conclusion are unchanged; only P1 module/public declarations and the namespace
are adapted. That PrivatePivots selection imports no graph or large-prime
exponent-one hypothesis. The remaining private-coordinate, residual-code, Griesmer, window-code
and effective-rank bridges are new P1 proofs.

`PaperC/Arithmetic/PrimeNumberTheoremInput.lean`, blob
`a18c4679f329ef81e3311f1c249128330811c054`, was inspected at the same commit.
It defines an explicit unproved PNT proposition. It is not a proof of PNT and
has not been imported or counted as a discharged arithmetic input in P1.
The PNT input has instead been proved by adapting a selected proof from
`AlexKontorovich/PrimeNumberTheoremAnd`, with separate
[provenance and validation](PRIME_NUMBER_THEOREM_ALIGNMENT.md).
`PaperCV282/MicroscopicPrivatePrimes.lean` was also inspected but not ported;
its quadratic-window exponent-one argument is not needed here.

The full P1 Lemma 2.1 is now completed by new proofs of the uniform PNT
specialization, extension of actual window relations, critical regimes,
actual infinite relative-sign independence and critical-band marginals.
These use the checked P1 foundations above and introduce no further Paper C
port. The weaker base hypothesis is recorded as `P1-MATH-0004`.

The completion of main Proposition 3.1 uses new P1 proofs of the two-defect
obstruction, exact arbitrary-target affine deviations, finite coupling and
moment truncation. It reuses the already checked foundations, not additional
Paper C source. Both count laws are identified with the actual infinite model.

Companion T9.1 and T9.2 add no Paper C port. Their finite-set reindexing,
critical-band scale comparison and exact kernel-one count specialization are
new P1 proofs built on the checked T1.1 and T1.3 developments.

Companion T22.2 uses new P1 proofs of missing-block kernel coverage,
heterogeneous probability comparison, ordered tuple deletion and exact
falling-factorial moments. No additional Paper C source or old artifact is
imported for these steps.

Companion T19.1 adds no Paper C port. Its deterministic run separation,
exact finite-interval packing, affine mass lattice and unordered factorial
expansion are new P1 proofs using the checked model and affine foundations.

New `LargePrimeComponentArithmetic` proofs identify these graph defects with
P1's literal odd-prime kernel above 10B, prove the actual critical defect
bound, prove that nontrivial free components meet both blocks and prove the
all-or-nothing selection property. Those new P1 proofs are not copied from
Paper C. All graph ports and bridges passed the full Lean 4.36.0-rc2 build
and the actual 1,416-declaration kernel audit at the graph checkpoint. The
complete comparison with d_xy is now proved by new P1 `PairRelationDimension`,
`TwoWindowRelations`, `SmallPrimePairConstraints`, `ComponentPrimeBudget` and
`FreeComponentRank` proofs, with no additional Paper C port. The full project
passes its 1,435-declaration audit at the complete T9.3 checkpoint.

## Further candidates

Additional read-only inspections at the T19.7 checkpoint used the same
snapshot `b9fa9ba490f201b408a302a86f1594ee620b228b` (Apache-2.0,
Lean 4.34.0):

- `PaperCV282/ScalarSteinInput.lean`, blob
  `13df39419770ba57ec9255e5eab3d003b7f97ffe`, leaves the positive-rate
  scalar Stein-factor statement as an explicit input. Its zero-rate
  proof does not discharge P1's positive-rate Stein estimates.
- `PaperCV282/PoissonReverseImmigration.lean`, blob
  `7269c6d5622aa8c349b22dc275ac4a507a4652dd`, constructs a reverse
  increment process; it does not by itself prove that scalar estimate.
- `PaperCV282/DirectionalSteinIntegration.lean`, blob
  `f77178c0bd58b6e4627f0ac4d3f370f80bc6144e`, proves a comparison from
  supplied derivative bounds, rather than closing those bounds.

None of these files is ported, and no unproved Stein-factor input is
introduced. P1's weighted recurrence theorem and its unweighted scalar
Stein estimates retain their distinct statement scopes. The arithmetic
cylinder proof is new P1 code using the previously validated model and PNT.

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

## Bivariate factor height: inspected, not reused

At the T9.4 checkpoint, `PaperC/Algebra/PolynomialHeightOperations.lean`
was inspected at the same pinned Paper C commit
`b9fa9ba490f201b408a302a86f1594ee620b228b`, blob
`cf1b2f63d52164c109bf7be8f7c149475ffab13a`. Its univariate height operations
do not provide the required bivariate factor estimate. No declarations from
that module were copied. P1's new proof uses exact partial degrees,
univariate Mathlib Mahler inequalities, specialization and Parseval.
See [factor-height alignment](BIVARIATE_FACTOR_HEIGHT_ALIGNMENT.md).

## Finite Rankin comparison for P1 article Lemma 7.1

Source: `PaperCV11/RankinTilt.lean`, exact Git blob
`0e160cd09e337d5b6142c75524a2da9da7ec5584`, snapshot
`b9fa9ba490f201b408a302a86f1594ee620b228b`, Apache-2.0, Lean 4.34.0.
Target: `PaperP1/Analysis/RankinComparison.lean`, Lean v4.36.0-rc2.

The source real square-root comparison, natural square-root comparison and
finite-product real-power rewrite are adapted. The new exponent sigma is
1 minus the old zeta; sigma>=1/2 corresponds exactly to zeta<=1/2. The
natural comparison is extended to every positive support product: products
above X give an empty natural fibre and need no admissibility hypothesis.
The finite-product rewrite uses exponent -sigma. Namespaces, imports and
public module declarations are updated. Attribution is in the target header.

The old kernel-one theorem, its truncated-support modules and its harmonic
prime estimate are not ported here. P1's small-kernel cover, variable-k sum,
real cutoff transport, explicit power-sum envelope and complete source
specialization are new proofs in this project. The full build passed
(8,805 jobs), and all 1,914 project theorem/lemma declarations passed the
actual axiom audit. No old compiled artifacts were copied. See
[statement alignment](RANKIN_SMALL_KERNEL_ALIGNMENT.md).

## Closure of the P1 scalar Stein estimates

The T19.11 implementation closes the positive-intensity Poisson Stein
factor bounds using new P1 cumulative/tail proofs. The three modules
inspected at the T19.7 checkpoint remain inspected, not ported. Their
exact blobs and snapshot above remain the provenance of the inspection;
no source declaration or unresolved Stein-factor input is imported.
The new proofs are compiled under Lean v4.36.0-rc2 and included in the
full audit of 2,875 declarations. See
[statement alignment](SCALAR_RECURRENCE_ALIGNMENT.md).


## Exact two-window normalization and finite channel counts

All four ports below use `b9fa9ba490f201b408a302a86f1594ee620b228b`,
Apache-2.0, originally Lean 4.34.0. Their complete source proofs have
been recompiled under Lean v4.36.0-rc2, with no old compiled artifacts.
The source and target both use offsets {-1,...,L-1}, hence B=L+1.
P1's normalized coincidence b*(x+i)=a*(y+j) uses the old channel-count
interface with coefficients (b,a), explicitly swapped at the call site.

| Upstream path and Git blob | Target and scope | Adaptation |
|---|---|---|
| `PaperC/Arithmetic/ChannelGeometry.lean`, `a63745d3e50cafa3387d50b9570c0b68e5158cb4` | `PaperP1/Arithmetic/ChannelGeometry.lean`, full module | Public 4.36 declarations, `PaperP1.Channels` namespace; positive coprime primitive direction and exact offset box retained |
| `PaperC/Arithmetic/IntervalCongruence.lean`, `f55ba828c9613a5202c5e1ae3fc3ae0f4332e54e` | `PaperP1/Arithmetic/IntervalCongruence.lean`, full module | Public 4.36 declarations and channel namespace; exact integer ceiling, rational interval bounds and natural/product wrappers retained |
| `PaperC/Arithmetic/ChannelCount.lean`, `58e46fa13533ee3cc4c0c48558be6db2ca3ce6bb` | `PaperP1/Arithmetic/ChannelCount.lean`, full module | Public declarations, dependency paths and namespace; first, second and maximum step counts retained |
| `PaperC/Arithmetic/ChannelEnumeration.lean`, `a0bebc0b4b36c3ee1274a381cd386ee200d4f4c4` | `PaperP1/Arithmetic/ChannelEnumeration.lean`, full module | Public declarations, dependency path and namespace; finite ratio/height bounds and empty-channel convention retained |

`PaperC/Affine/RationalChannelCode.lean`, blob
`491cfb0ab916209e068673206f37a48d7ab8eb74`, was read for statement
comparison. It remains unported. P1 instead proves the finite even-image
union, dilation, private-coordinate injectivity, exact normalized set
and anchor/motif assertions in new modules. This avoids importing its
separate two-start representation. The actual P1 good-edge definition
retains infinite-model positive joint probability and dependence.
See [alignment](GOOD_EDGE_COMPRESSION_ALIGNMENT.md).

Validated implementation of article Lemma 3.5 and P1-MATH-0035:
[37c99c7ea71d70271902fd12d1b52494646ec919](https://github.com/Vulkin-prog/paper-p1-lean/commit/37c99c7ea71d70271902fd12d1b52494646ec919).

## Weighted canonical support fibres for companion T1.6

`PaperC/Arithmetic/LargeKernelWeightedCounting.lean`, exact commit
`b9fa9ba490f201b408a302a86f1594ee620b228b`, Git blob
`0a767c88c4899fbb1fc4996c6a5188a5c19af103`, Apache-2.0, originally Lean 4.34,
supplies the selected canonical small-support/large-support/square-part
reindexing argument. `PaperP1/Arithmetic/KernelSupportFibres.lean` adapts
that argument to the existing P1 odd-support definitions and generalizes
the weight to an arbitrary nonnegative function of both supports.
Candidate square fibres and canonical injection are proved under Lean
v4.36.0-rc2, with no old compiled artifacts.

The other inspected modules, `PaperC/Arithmetic/TerminalKernelCount.lean`
(blob `94289ea41c663424d1109e802b15cdabfc21151b`),
`PaperCPrel8/RoughKernelStrongCount.lean`
(blob `b23149170bdf30dd0b93a291209992114a8b271a`) and
`PaperCV282/SmallKernelAnchors.lean`
(blob `58cd4b4d32eac9e8c4055e1785390fdc82759d9a`), were compared and remain
unported. P1 already has the needed square-root small-kernel count. Its
new finite weighted tail, actual parity witnesses, prime-assignment
count and source-family bridges are proved separately.

The full 9,427-job build and actual audit of 3,626 declarations passed.
See [statement comparison](LARGE_SELECTED_KERNEL_ALIGNMENT.md).

Validated complete companion T1.6 checkpoint (9,427 build jobs;
3,626 audited declarations; 1,341 directly checked coverage/finding names):
[3be7415366bd3d27aa016bf9690b0f93d7304fd9](https://github.com/Vulkin-prog/paper-p1-lean/commit/3be7415366bd3d27aa016bf9690b0f93d7304fd9).


## Selected odd-valuation pivot port forT19.15

The exact source is `PaperCPrel8/OddPrimePivot.lean`, Git blob `1139eb6c2e9978bfe7c6cb8a33a7648fa340bced`, at commit `b9fa9ba490f201b408a302a86f1594ee620b228b`, Apache-2.0 by Vulkin-prog. The target `PaperP1/Arithmetic/OddPrimePivot.lean` retains the definition `max1(sup oddPrimeSupport)`, its positive lower bound, the cutoff equivalence and the positive pivot population definition. Module/public declarations, namespaces and exposed helpers use Lean4.36.0-rc2. The remaining old Rankin/PNT/saddle imports and analytic propositions are excluded. New P1 comparison, squarefree interpretation, canonical injection, square tail and dyadic transfer proofs use already checked P1 foundations. All selected fragments were rebuilt under the pinned compiler; no old binary artifacts were copied. See [alignment](RECIPROCAL_PIVOT_ALIGNMENT.md).
