# The actual two-channel beta and its source positive phase

The actual principal edge family is now the union of the compatible,
private, dependent unordered populations in channels 2:3 and 3:4.
An exact displacement argument proves their disjointness once
29(L+1)<N: simultaneous channel alignments force the first center
below 29(L+1), contradicting its dyadic location. Its cardinality is at
most 26(L+1)N. Its joint mass beta is exactly half the sum of the two
ordered channel masses; probability-zero pairs were removed without
changing these masses.

For every fixed C,D there are positive c,k and one threshold such that,
for every critical L and 8(L+1)<=H<=D(L+1),

    c*L*N^(-2/3) <= beta <= k*L*N^(-2/3).

This is the source positive phase for the literal two-channel beta,
unconditionally. The correction from beta to its own absolute centered
activity is nonnegative and at most N^(-1+epsilon), uniformly in H.
Combining this exact subfamily with the already checked full
absolute-activity/cumulant gap also proves the one-sided comparison

    2*beta - actual_alpha <= N^(-1+epsilon),

without BCN or a complete pair profile. This is only one side of the
source absolute residual estimate. The reverse inequality at exponent
4/5, the full bad-pair activity and the complete signed pair profile
remain open. Main 3.4 stays in progress. Coverage stays 77/167 (main
28/73, companion 49/94), confirmed improvements 91. No new correction,
external input, axiom, dependency download, original-source change or
Palomar registration is introduced.

Verified under Lean v4.36.0-rc2: full lake build (10947 jobs), source and ledger checks, actual axiom audit of 6902 declarations (only propext, Classical.choice and Quot.sound), and 4619 direct ledger/evidence declaration checks; Ubuntu root free space 15.20 GiB. Original manuscript bytes and all 167 statement hashes preserved.


## Actual principal-edge activation and improvement P1-MATH-0092

The literal positive count Xi of active edges in any deterministic finite
pair family is now constructed on the original infinite prime-sign model.
Its value is the number of edges all of whose sites are active. Exact
finite-cylinder transport proves its first moment is the sum of actual
joint masses and its positivity event is precisely the union of the edge
events. A finite combinatorial estimate bounds Xi by Z_G^2. For every
R>0 and fixed m>=2 the actual truncation inequality is

    sum_(e in F)q(e) <= R^2*P(Xi>0)+E[Z_G^m]/R^(m-2).

The first Bonferroni correction is proved for every integer-valued finite
count, then transported to the actual original edge count:

    0 <= E[Xi]-P(Xi>0) <= E[Xi*(Xi-1)]/2.

For the literal principal channels 2:3 and 3:4, E[Xi]=beta exactly.
Their already proved positive beta phase and the unconditional subpower
fixed count moments imply, for every fixed epsilon>0 and C,D, one uniform
threshold for all critical lengths and 8(L+1)<=H<=D(L+1),

    N^(-2/3-epsilon) <= P(Xi>0) <= N^(-2/3+epsilon).

The proof chooses delta=epsilon/4, one fixed higher moment m=2+k with
delta*k>=2, and R=N^delta. The tail is bounded by N^(-3/2), which is
absorbed into half the positive beta lower bound. This needs neither BCN,
a complete signed pair profile, uniformly bounded fixed moments nor the
sharp second-factorial-moment estimate. The logarithmic rare-event exponent
is recorded as improvement P1-MATH-0092 for later manuscript integration.
It does not imply P(Xi>0)~beta or E[(Xi)_2]~beta^2; those sharp assertions
of T1.17 remain open. T1.17 moves from not_started to in_progress; main
3.4 stays in progress. Coverage remains 77/167 (main 28/73, companion 49/94),
confirmed improvements 92. No new external input, axiom, download,
original-source change or Palomar registration is introduced.

Verified under Lean v4.36.0-rc2: full lake build (10957 jobs), source and ledger checks, actual axiom audit of 6923 declarations (only propext, Classical.choice and Quot.sound), and 4640 direct ledger/evidence declaration checks; Ubuntu root free space 15.18 GiB. Original manuscript bytes and all 167 statement hashes preserved.


## Complete aligned principal profile

The entire original enlarged aligned unordered pair family is now
constructed using CompressedTargetAlignment.Aligned 1, with logarithmic
height at most (L+1)^3. Uniform dyadic geometry orients every representing
reduced channel as a <= b <= 2a. Its positive activity is covered by the
height-one and height-two boundary classes, private good 2:3 and 3:4
pairs, their normalized defects, zero-unit alignments, and the full
height-at-least-five tail. No disjointness of that cover is presumed.
Private one-unit pairs have zero actual centered coefficient, including
their affine prescription. All original irregular sites and zero exact
marginals are included.

Let beta be the actual joint mass of the compatible private principal
2:3 and 3:4 edges. For every fixed C, epsilon>0 and natural D, eventually
uniformly in the critical window and 8(L+1) <= H <= D(L+1), both the
absolute activity and the signed centered sum of ALL aligned pairs
differ from beta by at most N^(-4/5+epsilon). This is unconditional: no
BCN assumption is used. Separately, every pair subfamily F of the dyadic
block satisfies 0 <= A_F - C_F <= N^(-1+epsilon), uniformly over F.

An exact original-model identity splits alpha-2 beta into twice the
signed nonaligned sum, twice the aligned error, and the negative
single-site square diagonal. Consequently

    |alpha - 2 beta| <= 2 A_dense + N^(-4/5+epsilon).

Here dense is a literal finite residual family, not a presumed bound:
it consists only of regular, compatible nonaligned unordered pairs with
actual relative nullity greater than L/10. The weak, incompatible,
irregular and zero-coefficient classes have been removed using checked
estimates and an exact finite cover. The nonaligned complement retains
the full dyadic population before those removals.

The same bound holds with 2 beta replaced by the explicit sum
ChannelMainTermBounds.mainTerm N L 2 3 + mainTerm N L 3 4, using both
checked fixed-channel mass errors. These main terms retain the exact
signed finite channel sums, their source translation coefficients and
the nominal single-site scale; no phase limit is assumed.

This completes the aligned part of the actual second-cumulant profile.
It DOES NOT bound A_dense, prove the hard dense nonaligned weighted
estimate T1.8, or complete the unweighted positive/signed profile,
main 3.3 or T7.1. Both numbered results stay in progress and T1.8 stays
not started. Coverage stays 77/167 (main 28/73, companion 49/94), with
94 confirmed improvements. No new correction, external premise, axiom,
dependency download, original manuscript edit or Palomar registration
is introduced.

Verified under Lean v4.36.0-rc2: full lake build (11023 jobs), source and ledger checks, actual axiom audit of 7015 declarations (only propext, Classical.choice and Quot.sound), and 4732 direct ledger/evidence declaration checks; Ubuntu root free space 15.04 GiB. Original manuscript bytes and all 167 statement hashes preserved.


## Homogeneous seed probabilities and their principal mass

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
