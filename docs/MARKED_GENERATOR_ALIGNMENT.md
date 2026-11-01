# Marked-isolate generating function — article Lemma 7.4

**Status: proved, including the exact source rational bound.** Source:
article V1.6, page 24, `main_sections/cores.tex:111`,
label `p1:core:generator`. Exact statement SHA-256:
`156f5d4177e2fa6660c40fe7ba33639bf2880208535ce72dc4cfe7494cd9eb61`.

## Exact family, graph and marked vertices

`GraphStarWeights.families G marks` consists of actual vertex subsets of
the finite simple graph. `admissible_iff_isolated_marked` proves that its
membership predicate is exactly that every induced isolated vertex is
marked. `MarkedGraphGenerator.total` is the actual finite sum z^card(D).
The numbers n, M and Delta are the actual vertex count, marked-set count
and Mathlib maximum degree. The empty graph and empty set are included.

## Constructed disjoint star partitions

Every admissible set is covered by graph edges and marked singletons
contained in that set. `MinimalFiniteCover.exists_private_cover` chooses
a cover with least cardinality and proves that every member contains a
private vertex belonging to no other member.

Use each edge's private vertex as its leaf and its other endpoint as
center. Edges can intersect only at equal centers: a private leaf cannot
occur in another member. Grouping equal centers therefore gives disjoint
stars; singleton members remain marked singleton blocks. `PrivateStarCover`
proves exact covering, pairwise disjointness and every required graph
incidence. `GraphStarPartition.exists_partition` supplies the partition
for every actual admissible vertex set. No partition is an input premise.

## Exact finite weight comparison

`FinitePolymerBound` proves that disjoint partitions into an allowed block
family give a generating sum at most the product over all allowed blocks
of (1+blockWeight), hence at most the exponential of their weight sum.
A chosen partition determines its vertex union, so the finite reindexing
is injective. Non-disjoint extra block collections add nonnegative terms.

For center v and nonempty leaves L contained in its actual neighbor set,
the block weight is w_v times the product of the leaf weights. The exact
powerset identity sums these to

`w_v*(prod_{u adjacent v}(1+w_u)-1)`.

Thus `GraphStarWeights.heterogeneous_generating_bound` proves

`sum_admissible D prod_{v in D} w_v
 <= exp(sum_marked w_v + sum_v w_v*(prod_{u adjacent v}(1+w_u)-1))`

for arbitrary nonnegative vertex weights. Every sum and product is finite.

## Scalar specialization and the source conclusion

For w_v=z>=0 the bound becomes

`exp(M*z + sum_v z*((1+z)^degree(v)-1))`.

Replacing the degrees by Delta and using 1+z<=exp(z) gives respectively

`exp(M*z+n*z*((1+z)^Delta-1))`,
`exp(M*z+n*z*(exp(Delta*z)-1))`.

These hold for every z>=0. The proved elementary exponential inequality
gives the further rational bound

`exp(M*z+2*n*Delta*z^2/(2-Delta*z))`

whenever Delta*z<2. Under the original 4*Delta*z<1 condition, the source
rational exponent follows directly from the exponential star bound.
`MarkedGraphGenerator.main_7_4` states that exact original conclusion.
The broader and sharper bounds are recorded in P1-MATH-0022.

## Inputs and validation

No connected-set count, spanning-tree enumeration or cluster expansion
is assumed. Mathlib at `9d581dfff2e41de989072ea63abf3daf69311520` supplies
finite sets, products, graph definitions and elementary exponential
inequalities. No additional Paper C source is ported.

The full Lean v4.36.0-rc2 build passed (8,905 jobs), followed by the actual
axiom audit of all 2,207 project theorem/lemma declarations. Only `propext`,
`Classical.choice` and `Quot.sound` occur. Completed numbered coverage is
34 / 167: main 14 / 73, companion 20 / 94. No Palomar registration is made.

All 393 distinct coverage/finding declaration names were checked directly by Lean.
