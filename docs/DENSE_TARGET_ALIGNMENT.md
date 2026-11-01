# Main 6.2 — Complete actual dense-target count

Target: Proposition 6.2, page 22, `p1:fixed:targets`,
`main_sections/fixed_moments.tex:89`, statement SHA-256
`4b7903db8bfa5e1ce630499b700b2defbc2505400342a6d0a769238bd2dc771f`.
This numbered result is **proved**. The actual source-excluding target
population is counted. No count or classification is an assumption.

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

## Two actual disjoint classes and a literal finite code

`SelectedTargetClasses.exists_two` chooses two different surviving
target labels once the target has at least k+2 labels. Their physical
classes are disjoint. Both meet the target, have at most K coordinates
and yield nonempty simple disjoint offset lists.
`PhysicalClassData` extracts their actual source and target positions,
identifies the original class products, proves positivity and transfers
the target products to the literal integer split polynomials.

`ClassCoefficientValues.values` is a finite set of actual coefficients

    D=d0*d1*e*M, d0|primorial H, d1|M, 1<=e<=floor(N^theta).

It has at most tau(primorial H)*tau(M)*floor(N^theta) elements. Every
class yields a member and an actual integer square equation.
`CodedClassTargets` forms the literal finite cover by two bounded
physical classes and two such coefficients. No spaces or regularization
choices enter this enumeration.

`BoundedSubsets` bounds the number of classes by
(K+1)*(((s+1)*(L+1)+1)^K). `ClassCodeBudget` absorbs this position
budget, proves primorial(2*(L+1))<=N^A0, and applies the complete
uniform divisor bound to both primorial H and M<=N^(2K). Coefficients
cost at most N^(theta+epsilon) per class. `ClassCodeFibres` applies
the complete two-equation theorem with arbitrary nonzero coefficients.
`CodedClassCount.uniform_count` counts the actual cover by
N^(2theta+epsilon), including every code and coefficient choice.

## The full rank-loss population and quantifier order

`DenseTargetCover.uniform_cover` constructs one recovery order t before
every k, then one minimum length before all N and source tuples. It
regularizes the actual code and uses delta>=eta*L to ensure at least
k+2 target labels. The actual population is covered by strict T4.2
certificate targets and the finite two-class cover.

`DenseTargetCount.uniform_count` first fixes t, then chooses k so
theta=K*Dstar/k<=epsilon/8. The complete T4.2 and two-class count,
with explicit error margins and constant absorption, prove

    # {z in I_N : delta_z >= eta*L} <= N^epsilon

for every N after one threshold, every critical-band L and every
source tuple in I_N. Sources may repeat, overlap or be dependent;
there is no separation, compatibility or local regularity premise.
`mem_freshTargets` identifies the literal source-excluding population.
`DenseTargetCount.main_6_2` gives its count by subset monotonicity.
It supplies the full printed bound, with eventual constant one.

For a future manuscript revision, use the explicit proved Dstar for
physical supports; its j=1 term includes one-source representations.
Use two final classes and remove the final coefficient-height obligation,
as already justified by P1-MATH-0069. The repeated-source and source-
inclusive scope can be mentioned as a strengthening. No failure of
the printed dense-target conclusion is asserted.

Coverage is 70/167 (main 24/73, companion 46/94); confirmed independent
findings stay 69. Main 6.3 propagation and main 6.4 moment expansion
remain open. No external assumption, new Paper C port, manuscript edit
or Palomar registration is introduced.

## Earlier preparatory verification history

Dense-target input verification: Lean v4.36.0-rc2 full build passed (9943 jobs); actual axiom audit passed for all 4775 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 2490 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records are intact. Ubuntu available space: 16.66 GiB. Actual physical/effective relation projections, their fixed-order recovery regularization and finite support pools are proved. Main 6.2 remains in progress for the prime-group classification and actual target count. Coverage and confirmed improvements stay 69/167 and 69. No target-count premise, external assumption, Paper C port, manuscript-byte change or Palomar registration.

Validated preparatory proof checkpoint: [b83bdedd5e12fc31c3f964c454392afcf9121988](https://github.com/Vulkin-prog/paper-p1-lean/commit/b83bdedd5e12fc31c3f964c454392afcf9121988).

Prime-group checkpoint verification: Lean v4.36.0-rc2 full build passed (9961 jobs); actual axiom audit passed for all 4833 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 2548 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records remain intact. Ubuntu available space: 16.63 GiB. Actual circuit groups, the strict-certificate dichotomy and the residual-kernel exponent are proved. Main 6.2 remains in progress for the final two-class selection and population count. Coverage and confirmed improvements remain 69/167 and 69. No output-count premise, external assumption, new Paper C port, manuscript-byte change or Palomar registration.

Validated prime-group proof checkpoint: [23a3ac440d22d350cd37676144185ebb20bfd14e](https://github.com/Vulkin-prog/paper-p1-lean/commit/23a3ac440d22d350cd37676144185ebb20bfd14e).

Complete dense-target verification: Lean v4.36.0-rc2 full build passed (9985 jobs); actual axiom audit passed for all 4880 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 2595 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records are intact. Ubuntu available space: 16.59 GiB. Main 6.2 is complete for its literal source-excluding effective-rank-loss population, with a stronger repeated-source and source-inclusive count. Coverage is 70/167 (main 24/73, companion 46/94); confirmed independent findings stay 69. Main 6.3 and 6.4 remain open. No target-count premise, external assumption, new Paper C port, manuscript-byte change or Palomar registration.

Validated complete proof checkpoint: [0c3ce93793ad137d1673e8261985b1b6b548f86a](https://github.com/Vulkin-prog/paper-p1-lean/commit/0c3ce93793ad137d1673e8261985b1b6b548f86a).
