# Actual homogeneous seed probabilities and fixed extensions

The homogeneous zero-target window event is now defined under the
actual infinite prime-sign measure. For positive L, its relative bit
prescription is proved equivalent to equality of the value signs at
x-1, x, ..., x+L-1. For any finite family I, its joint probability is
exactly 2^(-rank of the sum of its actual square-class spaces), and is
strictly positive. Tuple support transport includes repetitions and the
empty family. The probability is antitone under adding windows.

For every I contained in the regular dyadic set, this actual homogeneous
probability equals the source weight

    W(I) = p^|I| 2^(rho(I)), p=2^(-L).

The exact rank-nullity identity proves this equality. It is not asserted
with nominal marginals on irregular sites. The actual original run joint
probability is at most the homogeneous probability for every finite I
and every positive L, including irregular and incompatible families.

In a raw private good channel a:b, every pair has homogeneous mass
p^2 2^(u-1), where u is its exact-unit count. This has no affine
compatibility restriction. For each fixed coprime 0<a<b, its total
unordered homogeneous mass is at most K_(C,a,b) L N^(-1+1/b), uniformly
over the private-prime cutoff H and all sufficiently large critical N,L.
The raw principal family is the union of the 2:3 and 3:4 raw good pairs.
Its W mass is bounded above by K_C L N^(-2/3) for every H and below by
c_(C,D) L N^(-2/3) when 8(L+1)<=H<=D(L+1). The lower bound follows from
the actual compatible principal beta mass, which is at most this raw
homogeneous mass. No cancellation or compatibility filter is used in
the upper bound. This proves the principal raw seed scale stated in
the moreover clause of the first part of T1.12.

For fixed positive seed size s and fixed extension size k, the sum of
actual homogeneous probabilities over any unordered family of size
s+k containing a seed is bounded by (s+k)! N^epsilon times the sum of
the seed probabilities. All seed and target populations vary after
the same threshold. On regular populations this transports exactly
to W mass. Consequently, for every fixed r, the sum of W over all
r-subsets of any regular dyadic subfamily is at most N^epsilon.
These statements are unconditional and concern fixed orders only.

The sharp outside-principal residual, dependent-target gains and
two-good-edge bounds of T1.12 remain open. T1.12 is now in progress,
not proved. Main 6.3 stays proved and its homogeneous specialization
is recorded here. Coverage stays 77/167 (main 28/73, companion 49/94)
and confirmed improvements stay 94. No external premise, new axiom,
dependency download, manuscript-byte edit or Palomar registration
is introduced.

Verified under Lean v4.36.0-rc2: full lake build (11037 jobs), source and ledger checks, actual axiom audit of 7046 declarations (only propext, Classical.choice and Quot.sound), and 4763 direct ledger/evidence declaration checks; Ubuntu root free space 15.01 GiB. Original manuscript bytes and all 167 statement hashes preserved.


## The first T1.12 clause under explicit geometric properties

The outside-principal residual in the first numbered clause of
companion T1.12 is now proved under the already identified
geometric properties. HomogeneousPairResidualUnderInputs.
companion_T1_12_pair_residual gives the literal W-mass bound
N^(-4/5+epsilon) on all dependent, strictly separated pairs of
any regular dyadic subfamily, outside the actual raw principal
family. The affine-compatibility condition is absent. The exact
same bound is proved for the sum of the actual homogeneous
zero-target probabilities over that actual population. The
private cutoff satisfies 8(L+1)<=H<=D(L+1), with D fixed and
all subfamilies varying after the common threshold.

The new unconditional probability bridge uses the full source
pairLoss, including local kernels. The actual homogeneous pair
probability is exactly p^2*2^pairLoss even on irregular windows.
The full pair-span dimension plus pairLoss is proved equal to
2L. On regular distinct pairs, pairLoss equals the actual
effective relative nullity, by the exact two-space dimension
identity and the actual local ranks. The source W weight can
therefore be used on the regular set without silently asserting
a nominal relative-nullity formula on irregular windows.
For positive source loss, the elementary bound
2^rho<=2*(2^rho-1) is proved, with its full scaling.

The finite off-principal positive mass is bounded by the actual
positive profile error and the two actual private-channel errors,
using the exact ordered multiplicity and disjoint private
principal families. Combining the proved literal positive
profile with the unconditional private-channel errors gives
RawPairResidualUnderInputs.uniform_bound:
sum_(separated outside raw principal)(2^sourceLoss-1)
<=N^(6/5+epsilon), uniformly over the admissible private cutoffs.
No supplied off-principal count or mass is an input. The public
geometric component cap is sizeCap(epsilon/128), and all other
finite caps precede the explicit geometric arguments.

The actual regular dependent-pair population is defined and
proved to lie in that original separated off-principal family.
Its W weight is at most twice p^2 times the positive source
weight. The proved critical nominal-square upper bound and
constant absorption yield the printed N^(-4/5+epsilon) rate.
The final public component cap is sizeCap(epsilon/384), with
the exact normalized curve and ordinary/chosen-source cover
properties as explicit unproved arguments. This is a geometric
conditional proof, not an unconditional certification or a
postulate of the target residual bound.

Together with the previously proved unconditional raw principal
seed upper/lower scale, this closes clause (1) of T1.12 under
those geometric properties. Clauses (2) and (3), involving
dependent targets and two distinct good edges, remain open;
T1.12 stays in_progress. The asymmetric large-prime profile
T1.10 is not asserted proved by these pair results. Main 3.3
remains conditional with all five conclusions aligned. Coverage
stays 79/167 and confirmed improvements stay 113. These are
proof-composition advances without a new correction identifier.
Original manuscript bytes, dependencies, compiler and Palomar
state are unchanged.

Validation and the exact proof commit are recorded in the T1.12 JSON ledger entry.
