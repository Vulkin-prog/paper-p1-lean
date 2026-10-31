# Article Lemma 4.3: statement alignment

Baseline: P1 V1.6, main article page 18, label `p1:alg:compatible`,
`main_sections/affine_algebra.tex:101`. The original statement hash and source
locator are preserved in `manuscript-results.json`.

The complete checked conclusion is
`PaperP1.Model.InfiniteStarts.compatible_nullity_majorant`. It proves the
centered bound, the comparison of nullities, and the asserted equality case.

## Objects and hypotheses

| Manuscript object | Lean object |
|---|---|
| Effective local square-class space `S_x` | `squareClassSpace x L`, identified with actual characters as recorded in the [Fourier alignment](FOURIER_ALIGNMENT.md) |
| Relative nullity `ρ_rel(I)` | `runRelativeNullity L I`: kernel dimension of addition from the effective spaces, equal to the dimension deficit |
| Joint mass `q(I)` | `infiniteJointMoment L I`, the actual infinite-measure Bochner expectation of the product of indicators |
| Centered coefficient `c(I)` | `infiniteCenteredCoefficient L I`, the actual Bochner expectation of the centered product with every individual marginal retained |
| Compatible maximum `ρ_*(I)` | `runCompatibleNullity L I`; `runCompatibleNullity_eq_maximum` identifies it with the supremum over positive-mass subfamilies |

The hypotheses are positive run length and positivity of each actual marginal
in `I`, exactly the admissible-family condition. The result applies to every
finite such family, including the empty family. No asymptotic condition,
regular-window restriction, equal marginal or independent-block assumption is
used. In particular it applies to the manuscript's admissible dyadic families.

## Exact joint masses are proved

`familyStartSystem` collects the actual rows of every start in a finite family.
Its solution event is proved to be exactly the simultaneous start event. Its
effective row space is the sum of the local effective row spaces.

Uniform affine counting gives zero mass for an incompatible joint system.
For a compatible system the mass is the inverse power of two at its effective
total rank. `relative_weight_eq_total_rank` uses rank-nullity to identify this
with `2^ρ` times the product of the individual actual marginal rates.
The square-class/row-space relation-kernel equivalence preserves this `ρ`.
Finite-cylinder expectation transport then proves
`infiniteJointMoment_exact_of_pos` for the actual infinite-model joint mass.

Consequently the exact-joint-mass premise of the preparatory algebraic lemma
`centeredCoefficient_compatibleNullity_bound` is discharged by model proofs in
the final theorem. It is neither an axiom nor the desired centered bound taken
as a hypothesis.

## Inclusion-exclusion and the maximum

`infiniteCenteredCoefficient_eq_transform` proves the heterogeneous
inclusion-exclusion formula with the actual joint moments. A zero joint mass
contributes zero. For a positive joint mass, the exact formula and product
partition give the absolute term
`(∏_{x∈I} p_x) 2^{ρ_rel(A)}`. Maximizing only over these positive-mass
subfamilies and counting the `2^{|I|}` subsets gives the displayed bound.

Extension by zero embeds the relation kernel of a subfamily into that of a
larger family. `relativeNullityOn_mono` therefore proves monotonicity without
counting local relations again. This bounds the compatible maximum by the
whole-family nullity. If the whole joint mass is positive, that whole family
is itself among the candidates, proving equality.

The maximum is not a default value standing in for an empty candidate set:
`infiniteJointMoment_empty` proves `q(∅)=1`,
`runRelativeNullity_empty` proves `ρ_rel(∅)=0`, and
`runCompatibleNullity_attained` supplies an actual positive-mass maximizing
subfamily. All empty-family conclusions are included.

## Remaining scope

This establishes Lemma 4.3 without an unproved literature premise. It provides
no arithmetic upper estimate for nullity, connected-family estimate, or
asymptotic reconstruction theorem. These remain separate obligations. The
canonical direct decomposition and factorization are now proved separately;
see the [Lemma 4.4 alignment](DIRECT_COMPONENT_ALIGNMENT.md).
