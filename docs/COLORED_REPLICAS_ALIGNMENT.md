# Colored replica systems: current T22.7 alignment

Source: companion Proposition T22.7, `p1:uniform:replicas`, page 92,
`companion_sections/uniform_appendix.tex:351`, statement SHA-256
`cee349c607e43eada20a10105ca13a96aba5dbd24c8c491a6857a75064ff04d9`.
Status: **in progress**, not counted as a completed numbered result.

## Actual model and replica identity

`ColoredPrimeSamples.Sample κ M` has one common finite prime-sign sample
and one independent finite sample per color. `select` uses the common
sample at primes at most Y and the specified color at larger primes.
Unused coordinates are harmless independent fair bits; Y is unrestricted.
The linear diagonal sets every sample equal and merges colors exactly.
The relation-map factorization is proved, rather than assumed.

`ColoredReplicaMass.blockProbability` averages the actual prescribed
window intersection over the private sample with the common sample
fixed. A color indexes a part of the occurrence partition; an unused
color contributes one. The occurrence index is retained independently
of its center, so repeated centers remain separate coordinates.
`replica_identity` proves that the average product of all block
probabilities is the actual joint event in the colored space. Finite
Fubini and the product law use the constructed normalized uniform
weights, not an abstract independence premise.

`exact_nominal_formula` gives the exact right side with denominator
2^(rL), compatibility indicator, and 2 to the dimension of the full
nominal-row relation kernel. Every local row relation is included.
`ColoredRelativeFormula.exact_relative_formula` separately proves the
effective relative-kernel version with the exact heterogeneous original
uncolored marginal of each occurrence. Surjectivity of `select`, proved
from its diagonal right inverse, preserves every local affine law.
`regular_formula` gives the printed p^r specialization from local full
rank. No nominal marginal is silently substituted at an irregular window.

## Complete finite colored conditional target sum

`SourceFamilyEvent` identifies observation of the actual old row span
with the literal intersection of all source prescriptions.
`CompatibleSourcePrescriptions` defines the actual ratio of finite
event probabilities and proves that its denominator is positive exactly
when a source witness exists. The conditional ratio is then exactly
`FamilyConditionalMass.mass` for that witness.

`FactorConditionalKernel.conditional_kernel_le` proves the actual
inverse-image submodule inclusion under any fixed linear merging of
relation maps. The merged homogeneous prescription always has a
witness, so its conditional mass is the full inverse-image-kernel
ratio. `mass_le_merged_homogeneous` proves pointwise domination for
every finite system and every colored affine atom, including an
incompatible target atom. No regularity, separation or critical-band
assumption is required at this step. Domination by the merged affine
atom with the original right-hand sides is **not** asserted: that atom
can be incompatible. This improvement is P1-MATH-0070.

`ColoredWindowConditional.infinite_homogeneous_domination` identifies
the dominating finite atom with the actual infinite-model homogeneous
conditional probability, once the finite cutoff contains the windows.
`ColoredConditionalSum.uniform_sum` and `prescribed_sum` then apply the
complete main 6.3 homogeneous sum. For every fixed positive source order,
critical-band bound and positive epsilon, the threshold precedes N, L,
all sources, the color type and coloring, Y, the finite cutoff, compatible
source prescriptions and center-dependent target prescriptions. The sum
includes repeated source centers and all target centers in the dyadic
block, including the source centers.

The common small signs are still averaged in these probabilities.
There is no assertion of a bound for every fixed realization of the
common signs, which would be a different statement.

## Actual small-prime conditional expectations and the infinite formula

`UniformFubini.condition_first` and `CoordinateConditioning` identify
fixing finite coordinates with the actual ratio of event probabilities
and private-coordinate averaging. `FiniteObservationConditional` proves
the ordinary measure-theoretic conditional-expectation identification
from the uniform joint observation law, using its defining set-integral
property. This input law is instantiated by the already proved exact
infinite-to-finite cylinder transport.

`SmallPrimeConditioning.block_condExp` identifies each private-sample
block average with the actual infinite-model conditional expectation.
`SmallPrimeFiltration.filtration_eq` proves that observing the small
coordinates in a cylinder M gives precisely the sigma algebra generated
by the prime signs up to Y whenever Y <= M. The observed sigma algebra
is therefore independent of the larger cutoff; no abstract conditional
probability interpretation is assumed.

`InfiniteReplicaFormula.exact_relative_formula` proves the full actual
infinite-measure replica identity with exact heterogeneous marginals,
affine compatibility and the effective relative kernel. Its regular
specialization is the printed p^r identity. Repeated centers remain
separate formal occurrence coordinates. The index of colors can be the
actual partition parts, and unused colors are permitted.

## Actual weighted colored extension propagation

`ColoredTupleMass` defines actual colored tuple event probabilities.
Appending an occurrence has an exact conditional factorization, including
zero-probability seeds. Colors and prescribed words can depend on the
occurrence position; words may also depend on the center.

`ColoredMassStep` gives a single threshold before every bounded source
order, color type, coloring, Y, cutoff and prescription.
`ColoredWeightedIteration` keeps an arbitrary nonnegative weight of the
initial seed exactly through finite iteration. The weight need not be
bounded. `ColoredMassPropagation.weighted_extensions` and
`weighted_subfamilies` prove an arbitrary subpower propagation factor
for literal finite extension populations and every subfamily. Repeated
centers are retained. `ReplicaColorEmbedding.joint_mass_eq` proves that
adding unused independent colors leaves the actual seed probability
unchanged.

## Remaining obligation

The full positive weighted random-sum moment assertion still requires
its actual replica expansion, ordered-occurrence reindexing and final
logarithmic-weight absorption. The exact replica identity and weighted
extension propagation are now proved, but this last assembly has not
yet been checked. T22.7 remains in progress and main 6.4 remains open.
No new unproved literature assumption, axiom, Paper C port or Palomar
submission is used.
