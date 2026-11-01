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

## Remaining arithmetic count

The completed T4.1 now supplies the final two-disjoint-square-equation
input without a curve-count assumption. The completed T4.2 supplies
the product-certificate count. Still required for full main 6.2:

- construct the actual large-prime circuit groups from these physical
  relations and prove their divisibility and pairwise coprimality;
- prove the product-certificate or small-group dichotomy and retain two
  disjoint target label classes;
- enumerate their actual small-prime, source-divisor and residual-kernel
  coefficients, then apply the two-equation count to the actual targets.

Coverage stays 69/167 and confirmed improvements stay 69. This checkpoint
formalizes source inputs rather than introducing a new independent
correction. No new external assumption, Paper C port, manuscript edit
or Palomar registration is introduced.

Dense-target input verification: Lean v4.36.0-rc2 full build passed (9943 jobs); actual axiom audit passed for all 4775 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 2490 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records are intact. Ubuntu available space: 16.66 GiB. Actual physical/effective relation projections, their fixed-order recovery regularization and finite support pools are proved. Main 6.2 remains in progress for the prime-group classification and actual target count. Coverage and confirmed improvements stay 69/167 and 69. No target-count premise, external assumption, Paper C port, manuscript-byte change or Palomar registration.
