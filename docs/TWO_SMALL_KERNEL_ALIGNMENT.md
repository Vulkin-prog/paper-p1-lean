# Complete two-small-kernel count — companion T6.1

Companion Lemma T6.1 is proved for actual centres and actual large odd-prime
kernels. Coverage is 60/167 (main 19/73, companion 41/94). The declarations
`TwoSmallKernelCount.companion_T6_1` and `critical_block_count` give the source
power bound and the literal critical B=L+1 formulation. The stronger core
is `real_bounds_count`, with cap Q and threshold independent of Q.

## Actual objects and coefficient heights

For an integer offset a, value(n,a)=|n+a| as a natural number, and
largeKernel(H,n,a)=K_H(value(n,a)). The source declarations prove uniformly
that n+a is positive and that the natural value casts back to n+a. Distinct
offsets therefore give distinct actual values. The HasPair predicate asks
for two distinct bounded offsets with the actual product of these kernels
at most Q. The theorem counts any finite set all of whose centres have
such a witness; neither a fibre count nor the desired bound is a premise.

The canonical factorization is

    sf(value(n,a)) = smallOddPart(H,value(n,a))*K_H(value(n,a)).

The small part is the product of its actual prime support, a subset of the
primes at most H. The two full squarefree linear coefficients are therefore
fixed by two small-prime supports and the two large kernels. On a dyadic
cell, every actual value is at most 3N, so its full kernel and large kernel
are at most N^3 for N>=2. Their product is at most N^6. These polynomial
heights are derived from actual values, regardless of the product cap Q.

## Every finite enumeration is proved

`PositiveProductPairs.uniform_count` groups actual positive pairs by their
product. There are at most Q positive integer product values at most Q,
including the empty case Q<1. At a fixed nonzero product m, first-coordinate
projection injects its factor pairs into m.divisors. The proved uniform
divisor estimate at m<=N^6 therefore bounds the number of pairs by Q*N^eta,
with a threshold independent of Q.

The proved logarithmic prime-support count bounds each small-prime support
family by N^eta. At fixed distinct offsets and fixed supports/kernel pair,
`LinearKernelFibres.fixed_linear_kernels_count` gives N^eta actual centres.
Its positive quadratic equation handles both the nonsquare and factorizable
cases, and derives all coefficient and solution heights from actual values.
The finite cover multiplies these four costs. A further actual finite cover
counts all distinct bounded offset pairs; every fixed polylogarithmic
width contributes only a subpolynomial cost.

## Comparable ranges, source blocks and stronger scope

A fixed finite dyadic cover proves the estimate on every fixed positive
comparable interval aN<=n<=bN. The same Q is retained on each cell: there is
no scale-dependent exponent q or factor depending on q. Cutoff and width
bounds are transferred by proved logarithmic comparisons and all fixed
cover constants are absorbed uniformly.

The full core conclusion is

    #S <= Q*N^epsilon,

for Q>=0, H<=D*logN and W<=E*(logN)^A0, with one threshold before H,W,Q,S.
Consequently #S<=N^(q+epsilon) holds with the same threshold for every real
q, including q varying with N. The critical-block version transfers
H<=D*(L+1), W<=E*(L+1) through the actual critical-band scale. No lower cutoff
or requirement H>block diameter is used. This is improvement P1-MATH-0061.

No new unproved literature input, Paper C port, manuscript-byte change or
Palomar registration is introduced. The smooth-modulus and private-prime
certificate lemmas, and the later conditional half-count theorem, remain
separate open work.

Verification checkpoint: Lean v4.36.0-rc2 full build passed (9,713 jobs); actual axiom audit passed for all 4,282 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 1,997 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records remain intact. Ubuntu available space: 17.38 GiB. No unproved centre/fibre count, new literature input, new Paper C port, manuscript-byte change or Palomar registration.
