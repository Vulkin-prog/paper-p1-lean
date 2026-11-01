# Exact local blocks — companion T19.2

**Status: proved, including the actual Bernoulli laws and endpoint corrections.**
Source: companion V1.6, page 67,
`companion_sections/limits_appendix.tex:63`, label
`p1:limits:local-blocks`. Original statement SHA-256:
`705bac9d7b5aee059315ab720c16e5ef0539a99b2c1f2bce57b32cab6b2bb79e`.

## The exact physical relation population

`LocalRelationBlocks.relations` enumerates the nonempty even physical sets
of integers with zero total parity vector, contained in at least one
dyadic window. `mem_relations_iff_square_product` proves that this is
exactly the manuscript population of nonempty even sets with square
product. Positivity is derived from the containing window and N>=2.
The finite enclosing interval adds no arithmetic restriction.

`LocalRelationSets.word` and `physicalSupport` give mutually inverse
encodings between physical sets in a window and binary selections.
They preserve cardinality, evenness and the full square-class sum.
Membership in the actual local relation code is proved explicitly.
A binary vector space of dimension at most one has at most one nonzero
vector, so distinct physical relation sets cannot occur in one window.

## Intervals, disjointness and all deficient starts

The block of S is defined by actual containment S subset V_x. The proved
interval identity is

`block N L S = [last(S)-L+1, first(S)+1] intersect I_N`.

Every enumerated block is nonempty. The proved local rank-one theorem
makes the blocks pairwise disjoint. Rank-nullity proves that their union
is **exactly** `RegularStarts.irregularStarts`, not a larger exceptional
set. The source endpoints a_S, b_S and diameter d_S are `first`, `last`
and their natural difference. A full block has L-d_S+1 starts and at
most L starts. Its diameter is less than L.

## The predecessor phase and original probability laws

The complete boundary map identifies row relations with local physical
relations. The dot product of the start right-hand side with a relation
is its predecessor coordinate. The exact two-term finite Fourier sum
then gives marginal zero when x-1 belongs to S, and 2p otherwise.
For a containing window, x-1 belongs to S exactly when x=a_S+1.
Outside all blocks, full local rank gives marginal p.

Deterministic start separation implies that at most one start is active
in each block. `BernoulliCount.countLaw_eq_bernoulli` proves the exact
Bernoulli law of any such finite indicator count. It is instantiated
with the original finite prime cylinder and transported to the actual
infinite prime-sign measure by `LocalBlockMass.block_law_realizes`.
The parameter is proved to lie in [0,1] and to equal the source value
2p*(card(block)-e_S), with the natural subtraction also checked.
No independence between different block counts is asserted.

## Mean, absolute discrepancy and boundary terms

Summation over the disjoint blocks gives exactly

`E Z - Np = p * sum_S (card(block_S)-2e_S)`

and

`sum_x |P(J_x=1)-p| = p * sum_S card(block_S)`.

The expectation and marginals here are the actual infinite-model
Bochner integrals. Every full block contributes p*(L-d_S-1). A truncated
block contains either the left or right endpoint of I_N. Disjointness
allows at most one of each, hence at most two in total. The full source
boundary error 2Lp follows for the original mean.

P1-MATH-0027 sharpens this: a nonempty clipped block retains at least one
of its full starts, so its correction is at most
p*(card(fullBlock)-1). Summing only the actual truncated blocks gives a
length-dependent bound, and then the uniform simpler bound 2*(L-1)*p.
This improves the finite constant only; no sign of the entire mean bias
or optimality is claimed.

## Quantifiers, inputs and validation

`LocalBlocksTheorem.finite_conclusion` proves every conclusion from
finite rank-one data. `companion_T19_2` constructs that data from the
already proved critical local-rigidity theorem. One threshold precedes
every L in the fixed band and every physical relation set, block and
sample. `boundary_improvement_uniform` supplies the sharper correction
with the same order of quantifiers.

No local relation is assumed to exist. No count, Fourier phase,
probability or literature estimate is an unproved premise. No new
Paper C source is ported; the already attributed foundations are reused.
Mathlib at the pinned revision supplies finite sums, dimensions, interval
cardinalities and the elementary real arithmetic.

The full Lean v4.36.0-rc2 build passed (8,989 jobs), followed by the
actual axiom audit of all 2,487 project theorem/lemma declarations.
Only `propext`, `Classical.choice` and `Quot.sound` occur. Numbered
coverage is 38 / 167: main 15 / 73, companion 23 / 94. The original
manuscripts remain unchanged. No Palomar registration is made.

All 523 distinct coverage/finding declaration names were checked directly by Lean.
