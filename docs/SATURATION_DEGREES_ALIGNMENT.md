# Saturation degrees — article Lemma 7.3

**Status: proved, all three source degree bounds.** Source: article V1.6,
page 24, `main_sections/cores.tex:92`, label `p1:core:degrees`.
Exact statement SHA-256:
`c75c4927a6ff796073b8aa42a2e034b84529436494cc2b060e89b93c4e02bed4`.

## The actual directed relation and graph

`SaturationPrimes.Edge` requires distinct centers, two distinct physical
anchor offsets and an integer divisor D>6*N*B of their actual truncated
kernel product. Every prime of D must divide an actual value in the
receiving window. The receiver need not have odd valuation or be regular.
Incoming and outgoing populations are filters of the original interval
[N,2*N). Their membership theorems identify these exact conditions.

`SaturationGraph.graph` is the actual finite simple graph on that interval,
with adjacency given by either directed edge. `neighbors_image` identifies
its neighbors with the union of incoming/outgoing centers. Its degree and
maximum degree are actual Mathlib finite graph quantities.

## Outgoing certificates

For each of at most B^2 anchor offset pairs, the actual squarefree kernel
product has at most m prime factors, where m is the source ceiling
`ceil(2*log(3*N)/logY)`. A prime is unused or assigned to one of B offsets
in the receiving window. Thus there are at most (B+1)^m codes.
Only qualifying codes are used to count centers: their prime product is
at least N, and their congruences fix at most one center. The resulting
finite outgoing bound is `B^2*(B+1)^m`.

## Incoming certificates

For a fixed receiver, `receiverPrimes` is the actual union of primes above
Y dividing its values. Each value is positive and at most 3*N, so its
large prime support has at most m elements. The union has at most B*m
primes. A code selects at most m of these and assigns each to one of two
anchor offsets. The anchor congruences, with qualifying product at least
N, again determine at most one center. No receiver offset is chosen.

`BoundedSubsetWeights` proves the exact powerset generating identity and
its positive weighted comparison. For any pool P with card(P)<=B*m,

`sum_{S subset P, card(S)<=m} 2^card(S) <= (2*exp(1)*B)^m`.

This finite inequality holds without a condition m<=card(P)/2 and includes
m=0. Counting all anchor offset pairs gives the explicit incoming bound
`B^2*(2*exp(1)*B)^m`. The symmetrized maximum degree is at most twice this
quantity. Every arithmetic cover and code count is proved internally.

## Uniformity and growing order

`SaturationDegreeBudget` uses the exact scaled ceiling limit
`m*loglogN/logN -> 2/A`, already proved in `ModerateOrder`. For every fixed
positive constants J,K, D>=1 and epsilon>0,

`J*B^2*(K*B)^m <= N^(2/A+epsilon)`

holds eventually for every 1<=B<=D*logN, with the threshold before B.
`SaturationDegrees.main_7_3` gives both directed degree bounds and the
actual graph maximum-degree bound, uniformly over every critical-band
length and every vertex. Its threshold depends only on the fixed A>1,
critical-band constant and epsilon. No regularity or primitive-family
hypothesis is introduced.

## The separately proved lower threshold

`RelaxedSaturation.Edge` changes only the divisor requirement to D>=N.
The source relation is proved a subset. Its actual neighborhoods admit
the same congruence covers and explicit finite bounds; the union obeys
the same uniform power estimate in
`RelaxedSaturationDegrees.relaxed_neighborhood_bounds`.
P1-MATH-0021 records this extension only for these degree estimates. The
6*N*B threshold is retained in the source relation and in other core tools.

## Inputs and validation

All arithmetic and finite counting inputs are proved internally. Mathlib
at `9d581dfff2e41de989072ea63abf3daf69311520` supplies powersets, products,
exponentials, filters and finite graph definitions. No additional Paper C
source is ported.

The full Lean v4.36.0-rc2 build passed (8,893 jobs), followed by the actual
axiom audit of all 2,170 project theorem/lemma declarations. Only `propext`,
`Classical.choice` and `Quot.sound` occur. Numbered coverage is 33 / 167:
main 13 / 73, companion 20 / 94. No Palomar registration is made.

All 374 distinct coverage/finding declaration names were checked directly by Lean.
