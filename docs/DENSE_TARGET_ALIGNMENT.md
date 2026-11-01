# Main 6.2 — Actual projection and regularized support inputs

Target: Proposition 6.2, page 22, `p1:fixed:targets`,
`main_sections/fixed_moments.tex:89`, statement SHA-256
`4b7903db8bfa5e1ce630499b700b2defbc2505400342a6d0a769238bd2dc771f`.
This numbered result is **in progress**. No dense-target population count
is counted complete or supplied as an assumption.

## The effective increment and the actual physical code

`RelationProjection.kernelEquiv` identifies the old relation kernel with
the kernel of the new-block projection from the full effective relation
kernel. Rank-nullity proves the exact identity

    delta_z = rho(old,new)-rho(old) = rank(new-block projection).

No finite-dimensional ambient square-class space is required; each
actual effective block is finite. All local kernels have already been
quotiented in this effective definition.

`PhysicalWindowRelations.code` is the literal code on the disjoint
physical copies of every complete window vertex. Each block has even
selection parity and the full sum of prime-parity vectors is zero.
`toEffective_surjective` lifts every actual effective relation to this
code, using the defining even-square-class image maps. The physical
target projection has rank at least the effective target projection.
Overlapping or dependent sources are included, with their physical
copies kept distinct. No compatibility or local regularity is assumed.

## Projection loss and distinct nonzero labels

`ProjectionRestrictionBudget.rank_loss_le_codimension` proves that
restriction to any subspace M loses at most codim(M) in every projection.
`ProjectionLabelBudget.labelMap_kernel` identifies the kernel of an
actual coordinate map with the kernel of evaluation on its distinct
nonzero coordinate forms. Rank-nullity therefore bounds the projection
rank by the actual finite label set's cardinality.

`SmallRecoveryParameter.power_order` gives the exact recovery parameter
at t=k^s. It constructs one integer t, before every length and every
start family, with

    2*(s+1)*(L+1)*t^(-1/s) <= eta*L/4,  L>=1.

`DenseTargetRegularization.uniform_regularization` instantiates the
complete disjoint-recovery theorem with the actual physical code. It
constructs M and proves that the target retains at least

    delta_z-eta*L/4

distinct nonzero labels. In particular delta_z>=eta*L gives at least
3eta*L/4 labels. The target labels are proved to belong to the global
regularized coordinate-label set. The original no-disjoint-recovery
property, multiplicity bound and independent-representation conclusion
are retained.

## Actual finite pools of short physical supports

`BinaryLabelRepresentations` cancels repeated binary labels and selects
a minimal zero-sum-free representation of each nonzero sum. Its labels
are actual labels from the original physical support. There is no zero
label and its cardinality cannot exceed that support's cardinality.
`PhysicalLabelSupportCount.injective_lift` chooses distinct physical
representatives and proves image, subset and cardinality identities.

`RegularizedSupportPools.support_pool_contains` constructs an actual
physical sub-support of every short nonzero representation. It belongs
to a literal finite support pool. For nonzero alpha, after recovery
regularization its cardinality is at most the fixed constant

    Dstar(s,t,K) = sum_{j=1}^s j!*(t-1)^(j-1)*2^(j*K),  K=t-1.

The proof uses the complete zero-sum-free representation count and an
actual finite cover by physical label fibres. It permits all subsets of
each fibre, giving a larger constant than the source injective-choice
bound K^j. No sharper constant is claimed. All these constants are fixed
before N, which is the scope needed for the later counting argument.

## Actual prime-group classification and residual bound

`WindowPrimeIncidence` proves every actual prime row equation and the
uniqueness of a large-prime occurrence within each window.
`PrimeCircuitSupports` chooses an actual short source support with
nonzero target sum. Its insertion gives a physical relation support
containing precisely one target vertex and at least one source vertex.

`PrimeCircuitGroups` assigns every active prime to one chosen support.
`AssignedPrimeGroups` proves that the resulting actual products are
squarefree, pairwise coprime, greater than one, and divide every value
at their assigned physical support. Each group therefore divides an
actual source value and an actual target value.

`PrimeGroupIncidence` bounds actual groups through a nonzero class by
K*Dstar, where K=t-1. It proves that discarding the target labels of
at most k selected groups removes at most k classes.
`TopProductSelection` proves the finite maximal-product dichotomy.
`PrimeGroupDichotomy.selected_certificate` constructs the actual strict
T4.2 source certificate in the large-product branch. Otherwise every
remaining incident group has kth power at most N.

`ClassPrimeResidual.residual_covered` proves that each odd prime in the
actual class product above H and not dividing the actual old product
belongs to an incident group. The resulting residual product e has

    e^k <= N^(K*Dstar),  e <= N^(K*Dstar/k).

`RelativeSquarefreeParts` supplies an exact canonical decomposition of
the class squarefree kernel into a divisor of primorial H, a divisor
of the actual source product, and this residual product. It proves
the actual square equation. No relation-space enumeration or second
restriction of the regularized code is used.

## Remaining arithmetic count

The completed T4.1 now supplies the final two-disjoint-square-equation
input without a curve-count assumption. The completed T4.2 supplies
the product-certificate count. Still required for full main 6.2:

- retain two actual disjoint target label classes after discarding
  selected-group classes;
- enumerate their physical positions and actual small-prime, source-divisor
  and residual coefficients, then apply the two-equation count to the
  literal target population.

Coverage stays 69/167 and confirmed improvements stay 69. This checkpoint
formalizes source inputs rather than introducing a new independent
correction. No new external assumption, Paper C port, manuscript edit
or Palomar registration is introduced.

Dense-target input verification: Lean v4.36.0-rc2 full build passed (9943 jobs); actual axiom audit passed for all 4775 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 2490 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records are intact. Ubuntu available space: 16.66 GiB. Actual physical/effective relation projections, their fixed-order recovery regularization and finite support pools are proved. Main 6.2 remains in progress for the prime-group classification and actual target count. Coverage and confirmed improvements stay 69/167 and 69. No target-count premise, external assumption, Paper C port, manuscript-byte change or Palomar registration.

Validated preparatory proof checkpoint: [b83bdedd5e12fc31c3f964c454392afcf9121988](https://github.com/Vulkin-prog/paper-p1-lean/commit/b83bdedd5e12fc31c3f964c454392afcf9121988).

Prime-group checkpoint verification: Lean v4.36.0-rc2 full build passed (9961 jobs); actual axiom audit passed for all 4833 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 2548 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records remain intact. Ubuntu available space: 16.63 GiB. Actual circuit groups, the strict-certificate dichotomy and the residual-kernel exponent are proved. Main 6.2 remains in progress for the final two-class selection and population count. Coverage and confirmed improvements remain 69/167 and 69. No output-count premise, external assumption, new Paper C port, manuscript-byte change or Palomar registration.

Validated prime-group proof checkpoint: [23a3ac440d22d350cd37676144185ebb20bfd14e](https://github.com/Vulkin-prog/paper-p1-lean/commit/23a3ac440d22d350cd37676144185ebb20bfd14e).
