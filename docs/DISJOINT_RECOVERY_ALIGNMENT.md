# Disjoint recovery — article Lemma 6.1

**Status: proved in full.** Source: article V1.6, page 21,
`main_sections/fixed_moments.tex:30`, label `p1:fixed:recovery`.
Exact statement SHA-256:
`18db139a0bd9ab77f064acb65b950ad41adfc0ba3ee9dba623584d8600e83131`.

## Complete statement and its binary specialization

`DisjointRecoveryTheorem.main_6_1` specializes the complete construction to
an actual subspace R of F_2^V and its coordinate forms. For d>=1 and t>=2
it constructs an actual M inside R with all source conclusions:

- codim(M)<=2*card(V)*t^(-1/d);
- no nonzero form on M has t pairwise disjoint nonempty coordinate recovery
  sets, each of size at most d;
- every nonzero coordinate form has multiplicity at most t-1;
- for 1<=j<=d, each nonzero form has at most j!*t^(j-1) representations by
  j distinct linearly independent nonzero coordinate labels.

Representations are unordered sets of labels, matching the source proof's
label supports. They are not physical coordinate supports with multiplicity.
An ordered-tuple convention would multiply the support count by j!.

`disjoint_recovery` proves the entire statement over an arbitrary field K
for any finite family L:V→Dual K U on a finite-dimensional U. The family
need not separate points. This complete extension is `P1-MATH-0013`.
`disjoint_recovery_sharp` retains the stronger representation constant
j!*(t-1)^(j-1), recorded separately as `P1-MATH-0014`.

## Constructed history and deterministic rank certificate

`DisjointRecoveryHistory.exists_maximal_history` constructs a finite history
of independent new directions. Each step records actual t disjoint recovery
sets and equalities modulo earlier directions. Prefix span dimension equals
history length, which is bounded by dim U. A finite maximum gives a history
with no remaining bad recovery. No assumed greedy output or stopping-space
existence is an input.

For each coordinate selection, a successful step lies in the span of its
selected labels plus earlier directions. Induction puts all history directions
in the selected-label span plus the failed directions. The resulting pointwise
inequality is

`history length <= card(selected coordinates) + number of failed steps`.

`RecoveryRankCertificate.pointwise_rank_certificate` derives this from the
recorded algebraic recoveries. Thus the deterministic premise of the separate
sampling interface is discharged before the subspace is constructed.

## Exact finite sampling and the stopping subspace

`FiniteBernoulliSubset` constructs the actual product weights on Boolean
selections, proves total mass one and positivity, and proves the inclusion
probability u^card for every fixed subset. Expected selected size is card(V)u.
For disjoint recovery sets, finite product expansion proves the exact failure
probability `prod_j (1-u^card(A_j))`, at most `(1-u^d)^t`.

The literal parameter u=t^(-1/d) is proved positive and below one, with
u^d=1/t. Bernoulli's inequality proves `(1-1/t)^t<=1/2`. Averaging the
pointwise rank inequality gives the original constant two. Independence
between different history steps is unnecessary. The annihilator of the
stopped dual span has the exact codimension, and dual restriction transports
the stopping property to every nonzero form on M.

`DisjointRecoverySubspace.coordinate_multiplicity_le` uses singleton recovery
sets to bound each nonzero coordinate-label fiber by t-1.

## Independent-label representations and the stronger count

`RecoveryLabelSupports.noDisjointSums_of_recovery_exclusion` chooses one
physical coordinate representative for each distinct nonzero restricted
label. The representative map is injective on those labels. Thus disjoint
label supports lift to actual disjoint coordinate supports, preserving their
cardinalities and sums. The proved recovery exclusion applies to them.

For a family of j-element supports with the same nonzero sum, a maximal
pairwise disjoint subfamily has at most t-1 elements. Its union is a
transversal H of size at most j*(t-1). `UniformTransversal.exists_transversal`
constructs H from a finite maximum; no hitting-set bound is assumed.

`ZeroSumFreeRepresentations.representations_card_le` works in any abelian
group. It counts supports with no nonempty zero-sum subset. Marking a label
in H and erasing it leaves a smaller support of nonzero residual sum. The
proved recurrence gives j!*(t-1)^(j-1). Linear independence implies the
zero-sum-free property; `IndependentRepresentations` obtains both the stronger
bound and the original j!*t^(j-1). This completes the last source clause.

## Inputs and validation

All probability weights, recovery probabilities, rank budgets, history
maximality, the stopping subspace, physical-coordinate lifting and the
representation recurrence are proved internally. Mathlib at
`9d581dfff2e41de989072ea63abf3daf69311520` supplies finite sum/product
identities, Bernoulli's inequality, finite-dimensional rank and dual
annihilator identities. No literature proposition, target codimension bound,
pointwise rank certificate or representation estimate is assumed in the
complete theorem. No additional Paper C proof is ported.

The full Lean v4.36.0-rc2 build passed (8,797 jobs), followed by the actual
axiom audit of all 1,891 project theorem/lemma declarations. Only `propext`,
`Classical.choice` and `Quot.sound` occur. Completed coverage is 26 / 167:
10 main results and 16 companion results. No Palomar registration is made.

The earlier partial validation (subspace, recovery exclusion and multiplicity
only; 1,874 audited declarations) remains recorded at
[749cc57a47466ee65501e37ed5f5dfcfca6a24ea](https://github.com/Vulkin-prog/paper-p1-lean/commit/749cc57a47466ee65501e37ed5f5dfcfca6a24ea).
It is historical evidence for that partial scope, rather than validation of
the later representation proof.

All 239 distinct coverage/finding declaration names were checked directly by Lean.

Validated implementation of complete Lemma 6.1 and P1-MATH-0013/0014:
[9dcb13772d8b7dbef31571adca039223a50ec120](https://github.com/Vulkin-prog/paper-p1-lean/commit/9dcb13772d8b7dbef31571adca039223a50ec120).
