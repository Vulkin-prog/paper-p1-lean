# Deleting large private ranks — companion T19.8

**Status: proved, including the original affine moments and dense component.**
Source: companion V1.6, page 71,
`companion_sections/limits_appendix.tex:427`, label
`p1:limits:peeling`. Original statement SHA-256:
`724e0fa15a6355ba86b04ad63a21b98824bea0113f27d9255431e39fdf51fc0e`.

## Actual ranks and deletion traces

`SubspaceFamilyRank.span`, `rank` and `privateRank` are the actual sum
space, its dimension and the dimension decrease after deleting one index.
The total rank is monotone, and a private rank is at most the local
dimension. Reindexing by a finite subtype preserves all these quantities.

`PrivateRankPeeling.Trace` records a finite sequence of actual deletions,
each justified by current private rank at least t. `trace_rank_budget`
proves for **every** such trace

`t*(card(A)-card(B)) + rank(B) <= rank(A)`.

It therefore proves the source size and rank bounds for any deletion
order. Strong induction constructs a terminal trace with every remaining
private rank less than t. No terminal family or rank budget is assumed.
The linear deletion construction works over any division ring; the
affine probability arguments below use the source binary field.

## Exact missing-coordinate counts and compatible affine probabilities

Extension by zero identifies the relations missing one block with the
relation kernel after deleting it. The proved dimension identity is

`rho(A) + privateRank(A,i) = rho(A erase i) + dim(S_i)`.

Consequently the exact fraction of the relation kernel whose i-th
coordinate is zero is

`2^privateRank(A,i) / 2^dim(S_i)`.

A finite union bound gives the lower count of relations meeting every
block. These are actual kernel cardinalities, not assumed loss factors.

For a compatible affine family, all local prescriptions can use a
common solution. `CommonAffineWitness` proves that this replacement
preserves each original event indicator and both joint and centered
moments. The exact Fourier formulas give the actual centered moment as
the product of exact marginals times the full-support relation count;
the joint moment is the same product times 2^rho. Common-witness phases
are proved equal to one.

Thus the centered coefficient is at least the joint probability times
one minus the sum of the exact missing-coordinate fractions. This
retains heterogeneous local dimensions and all individual private ranks.
When every local dimension is L and all private ranks are less than t,
it gives the stronger factor

`1-card(C)*p*2^(t-1)`.

The source factors with 2^t and with the original family size m follow.
The inequality holds even when its displayed lower factor is negative;
no additional positivity hypothesis is silently imposed.

## Every canonical component and the dense component

The canonical partition is the already constructed unique finest direct
partition. `PartitionRank.rank_partition_inter` proves rank additivity
after restricting the family to **any** subset. In particular the private
rank of an index inside its direct component equals its private rank in
the full remaining family. All components therefore inherit the terminal
private-rank bound and the original affine-mass inequalities.

If m-R/t>0, the remaining family is nonempty. Rank additivity and a finite
size-weighted average construct an actual canonical component of rank
density at most D=R/(m-R/t). Its rank is at least L. The proved rank-nullity
identity gives card(C)>=L/D and rho(C)>=L^2/D-L. The proof treats D>=L
separately, when the last asserted lower bound is nonpositive. No dense
component, density or nullity estimate is an input.

## Scope, improvement and validation

`PrivateRankPeelingTheorem.companion_T19_8` bundles every source
conclusion for arbitrary compatible affine prescriptions on actual finite
binary uniform probability spaces. Its moments are the defined original
event expectations. Compatibility is the source hypothesis of a common
solution, not a probability estimate passed to the theorem.

P1-MATH-0028 records the factor-two improvement from 2^t to 2^(t-1) and
the sharper heterogeneous private-rank profile. The exact remaining-rank
charge above is also retained. These are finite statements; no arithmetic
large-component construction or later asymptotic consequence is claimed.

Every deletion, kernel cardinality, compatible Fourier phase, moment
comparison and component average is proved internally. No new Paper C
source or unproved literature input is added. Mathlib at the pinned
revision supplies finite-dimensional linear algebra and finite sums.

The full Lean v4.36.0-rc2 build passed (9,013 jobs), followed by the
actual axiom audit of all 2,542 theorem/lemma declarations. Only `propext`,
`Classical.choice` and `Quot.sound` occur. Numbered coverage is 39 / 167:
main 15 / 73, companion 24 / 94. Original manuscript bytes are preserved.
No Palomar registration is made.

All 557 distinct coverage/finding declaration names were checked directly by Lean.
