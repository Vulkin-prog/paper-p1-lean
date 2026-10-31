# Coordinate regularisation — companion T2.2

**Status: proved.** Source: companion V1.6, page 20,
`companion_sections/supplemental_arithmetic.tex:51`, label
`p1:arith:coordinate-regularisation`. Exact statement SHA-256:
`a3941b762829af79b101153ae7f08368d8363545b175a014dae74742adb8f16b`.

## Literal coordinates and an actual restricted subspace

The source input is an arbitrary binary subspace `R≤(V→F₂)`, with V finite.
`coordinateFamily R v` is its actual coordinate functional. `originalForms`
is the finite set of distinct nonzero coordinate forms, so its cardinality
is the source s. `multiplicity` counts coordinate positions, rather than
distinct labels.

`zeroCoordinates` imposes exactly the selected coordinate equations inside R.
`ambientRestriction R D` embeds that space into the original function space.
`mem_ambientRestriction` proves the literal description

`x∈R' iff x∈R and x(v)=0 for every v∈D`.

The main theorem proves `dim(R)-dim(R')=card(D)`, not just an inequality.
Thus no selected equation is redundant. The cardinal bound is

`card(D)≤n/(K+1)+(s-r)/(d+1)`.

## Both regularity properties

`Regular` gives both properties for every nonzero coordinate form present
on the final space. Each has multiplicity at most K. For a present form α,
`PairDecompositions.pairs S α` consists of two-element subsets of S whose
sum is α. This is precisely an unordered decomposition into distinct
nonzero labels; neither ordered assignments nor zero labels are counted.
Its cardinality is at most d.

`activeEncoding` is the actual projection onto coordinates whose forms do
not vanish. It is proved injective. The dimension of its image is the
dimension of R', proving that deleting zero coordinates costs no further
dimension. The result imposes no claim that these properties survive a
later arbitrary restriction.

## A finite terminating construction with proved budgets

Each unordered pair summing to a fixed α is disjoint from every other such
pair. When α is killed, each pair has equal image. `MatchingCollapse`
chooses one representative to remove from each pair and proves the exact
finite cardinal loss needed for the inequality. This is an internal finite
count, rather than an assumed collision budget.

`stepKernelEquiv` identifies the next space with the actual kernel of a
nonzero coordinate form; its dimension drops by exactly one. At least all
coordinates carrying that form disappear. The number of distinct nonzero
forms drops by at least one plus the unordered decomposition count.

The potential is

`card(D)+active(D)/(K+1)+(distinct(D)-dim(R_D))/(d+1)`.

It cannot increase at a step violating either desired bound. A finite
maximal candidate D therefore admits no such step. Separating coordinate
evaluation proves `dim(R_D)≤distinct(D)`, making the last potential term
nonnegative. This proves the output bound and both stopping properties.
No assumed algorithmic output, rank-loss estimate or existence claim is
passed as a premise.

## The stronger budget

`companion_T2_2_active_budget` replaces n by the number n₊ of initially
nonzero coordinate forms, counted with multiplicity. Both conclusions hold
for all natural K and d, including zero. The source domain K,d≥1 and its
original n bound follow immediately. These finite improvements are recorded
as `P1-MATH-0011`; their denominators and the exact codimension are unchanged.

## Inputs and validation

The development uses only proved finite linear algebra and finite-set facts
from Mathlib at `9d581dfff2e41de989072ea63abf3daf69311520`, in particular
`Module.Dual.finrank_ker_add_one_of_ne_zero`,
`LinearMap.finrank_le_finrank_of_injective`, and finite maxima. All pair
collision counts, restriction identities and potential inequalities are
proved here. No additional Paper C code is ported.

The full Lean v4.36.0-rc2 build passed (8,765 jobs), followed by the actual
axiom audit of all 1,814 project theorem/lemma declarations. Only `propext`,
`Classical.choice` and `Quot.sound` occur. Coverage is 24 / 167 numbered
results: 9 main and 15 companion. No Palomar registration is made.
