# Triple activity: qualitative structure and exact cancellation

Sources: main Theorem 11.2 (`p13:activity:incompatible`) and Proposition
11.3 (`p13:activity:kappa3`), `main_sections/triple_activities.tex`.
All three numbered results 11.1, 11.2 and 11.3 are **in progress**, not counted complete.
Coverage remains 72/167 (main 25/73, companion 47/94).

## Positivity holds at every finite order

`FamilyCenteredMass` defines the actual centered coefficient of arbitrary
finite binary affine events, centered at each event's exact uniform
probability. For a common affine witness, its exact value is the product
of those actual local probabilities times the cardinality of the full-
support effective relation set. The common witness makes every relation
character equal to one. Hence every compatible coefficient is nonnegative.
The result covers every finite order, repeated formal event coordinates,
zero-dimensional local spaces and empty families. It does not require
arithmetic, regularity, separation or a fixed-order asymptotic regime.

`CompatibleRunCentered` identifies the finite coefficient with the actual
original infinite-model centered run coefficient. Positive joint mass
supplies one actual common cylinder witness. The full-support relation
count is transported by the proved equivalence from row spaces to the
physical effective square-class spaces. Thus every compatible original
run family has the same exact nonnegative count formula with its actual
heterogeneous marginals, including irregular windows and repeated
formal centers. `coefficient_nonneg` gives the literal finite-set version.
This strengthens and simplifies the compatible-triple sign assertion
of main 11.3; it is recorded as P1-MATH-0071.

## Exact triple cancellation and connectedness

`TripleCentering` proves the complete heterogeneous three-site expansion
for arbitrary normalized joint data. When the triple joint mass is zero,
the centered coefficient is exactly minus the independent product minus
its three pair centered coefficients weighted by the remaining marginal.
`TripleCancellationBound` takes absolute values while retaining both signs
of each pair coefficient. `InfiniteTripleCancellation` identifies all
terms with actual original infinite-measure joint moments and marginal
probabilities. No compatibility or sign is silently discarded.

`SmallFinpartition` proves that a partition of at most three elements
without singleton parts is indiscrete. A full-support relation cannot
have a singleton part in a relation-direct partition. Consequently
`TripleActivityConnected` proves that an admissible nonzero triple
coefficient has one canonical direct component. A disconnected triple
therefore has coefficient zero. The admissibility premise is precisely
positivity of the three actual local marginals, as in the manuscript's
set I_N of possible starts.

## Exact finite activity comparison

`CompatibleActivitySplit` partitions an arbitrary finite population by
positive joint mass versus zero joint mass. Positivity gives the exact
identity

    absolute activity - compatible centered activity
      = incompatible absolute activity >= 0.

The absolute signed-sum error is bounded by the same incompatible
absolute activity. These statements hold at every finite order and for
mixed finite populations. At order three, disconnected coefficients
vanish, so `TripleActivityConnected.positive_eq_connected` identifies the
full compatible sum with the source connected compatible activity K3+.
Its `absolute_comparison` and `signed_comparison` are the corresponding
literal finite identities for the source triple populations.

## Actual independent incompatible-triple mass

`IncompatibleTripleSeed.families` is the actual finite population of
zero-joint-mass triples with nonzero centered coefficient. Removing the
zero coefficients preserves the incompatible absolute activity exactly.
The population is a subset of the actual connected triples. The complete
main 10.2 heterogeneous independent-mass bound then proves that the sum
of its independent products is at most N^(-3/2+epsilon), after a uniform
threshold before the length and admissible dyadic center set.

This is the first term in the main 11.2 proof. It is an independent
weight estimate, not the full incompatible activity estimate.

## Exact pair/target deficit and incidence reduction

`IndependentTargetDeficit.deficit` is the literal source D_(2,1), using
actual infinite pair coefficients, actual heterogeneous target marginals
and the physical effective square-class spaces. `pair_rank` identifies
the pair nullity with dim(S_x intersection S_y); `target_pair` identifies
the target condition with S_z intersection (S_x+S_y) nonzero.

`CenteredDependenceSupport` proves that at every finite order, a nonzero
admissible centered coefficient supplies a full-support effective relation.
Every coordinate lies in the span of the others, so every target meets
that span nontrivially. A nonempty nonzero coefficient also forces positive
effective relative nullity. No assumption on connectedness is needed for
these stronger support statements.

`TriplePairIncidence.erased_sum` proves, for arbitrary r and additive
commutative target, the exact sum identity between an (r+1)-element set
with a distinguished member and its r-element complement with that member.
Its restricted nonnegative form retains the actual dependence predicates.
`IncompatibleTripleReduction.pair_cost` consequently bounds all pair terms
of the actual active incompatible population by ONE copy of D_(2,1).
`finite_bound` gives incompatible absolute activity <= independent active
triple mass + D_(2,1). `reduced_bound` supplies the complete independent
N^(-3/2+epsilon) term with a threshold before L and the admissible dyadic set.
The improved finite constant and its incidence justification are recorded
as P1-MATH-0072.

## Remaining obligations

The actual pair-activity/independent-target deficit D_(2,1) from main
11.1 still needs its arithmetic proof; the exact incidence summation is now proved.
It is necessary to bound the remaining terms in the incompatible triple
cancellation. The final N^(-3/2+epsilon) incompatible activity estimate
is therefore open. Main 11.3 also needs the exact third factorial-
cumulant/repeated-index assembly and its quantitative correction bounds.
Neither numbered result is marked proved. No deficit or target activity
estimate is introduced as an axiom or used to inflate coverage.
No new external theorem, Paper C source or Palomar submission is used.
