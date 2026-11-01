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
The identification of this kernel with the source effective relative
kernel in its regular-window convention is still an alignment task.
No nominal marginal is silently substituted for an irregular window's
actual marginal.

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

## Remaining obligations

- Identify the fixed-common-sign block average with the conditional
  probability given the actual small-prime sigma algebra, including the
  infinite prime-sign interpretation.
- Align the effective relative kernel and exact heterogeneous local
  rates with the nominal-row version, then recover the printed p^r
  specialization in its regular-window scope.
- Prove the full positive weighted random-sum moment estimate from
  actual replica expansions and iterated colored conditional sums,
  including repeated centers, arbitrary ordered-tuple subfamilies and
  deterministic weights bounded by a fixed logarithmic power.

These are separate mathematical tasks. The finite replica formula and
conditional sum alone do not complete T22.7 or main 6.4. No new unproved
literature assumption, axiom, Paper C port or Palomar submission is used.
