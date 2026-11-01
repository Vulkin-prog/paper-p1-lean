# Complete actual companion T5.2 counts

Both T5.2 counts are proved on every fixed comparable positive interval.
Numbered coverage is 57/167 (main 17/73, companion 40/94).
P1-MATH-0057 records the stronger cumulative count. P1-MATH-0055 records
the broader width scope and the odd-degree fixed-kernel extension.

## Literal source families and common threshold

For fixed c>=0, D,A0 and epsilon>0, one N0 precedes every N>=N0,
positive natural W, natural e, finite integer offset set A and real beta
with

    2 <= d=card(A) <= c loglogN,    d even,
    W <= D(log N)^A0,    |a|<=W for every a in A.

The original critical logarithmic window is included in this more general
fixed polylogarithmic width regime. The actual integer range is a*N<=n<=b*N for fixed real a>0 and b.
The literal standard-block family `values A N e beta`
has N^beta<=sf(P_A(n))<2N^beta and e dividing that actual kernel.

`ComparableSplitProductCount.companion_T5_2` proves both bounds on
N<=C*n and n<=C*N for every fixed natural C>=1. With delta=log(e)/log(N),

    #values <= N^(1/2+beta/(2d)-delta/d+c log2+epsilon),
    #fixedKernel(q) <= N^(2c log2+epsilon)  for every q.

The real-bounds theorem `companion_T5_2_real_bounds` covers every fixed
real a>0,b and also proves positivity and equality with the literal signed
integer product. Its prescribed bound accepts sf(P_A(n))<=F*N^beta for
every fixed real F. The threshold also precedes q and the varying degree
and offset set; a,b,F remain fixed outside it.
Squarefreeness of e is unnecessary as an extra premise. On every
nonempty admissible family it follows from divisibility into the actual
squarefree kernel. Impossible e=0 or q=0 families are harmless empty
cases; no representative is assumed for an empty family.

## Exact finite arithmetic already checked

The proof constructs one pair partition P of A and fixes it for the whole
count. The actual unordered difference resultant D_A is positive. Its
exact grouped-kernel decomposition is M=q*R^2 with R|D_A. The actual
e'=e/gcd(e,rad(D_A)) is allocated explicitly into pairwise coprime
divisors e_B of the block kernels. Their product is e'.

The actual height bounds prove the prime/divisor budgets, including
tau(e')<=N^(c log2+eta) at the varying degree d<=c loglogN. The uniform
selected-block inequality, for this same fixed partition, is

    (log(q_B)-2log(e_B))/logN
      <= (log(q)/logN-2delta)/(d/2)+eta.

The finite resultant error is explicitly 4log(D_A)/(d/2) and has already
been absorbed uniformly. These are proved arithmetic inputs to the
enumeration, not assumed solution-count bounds.

## The final actual finite cover

Each solution is covered by a triple consisting of

- a block B of the fixed partition P;
- an actual divisor of the fixed e';
- the dyadic index j=log2(q_B).

Every actual block kernel is positive and at most N^6, with that height
derived from its two actual linear factors. Thus j lies in the actual
range 0..log2(N^6). Its cardinality and the number of blocks are each
at most N^eta after a common threshold. The divisor count has the bound
above. No count of all partitions or all factorizations of e' is introduced.

Cells are literal filtered subsets of the actual solution set. Equal
divisor and dyadic coordinates give a fixed shifted quadratic kernel
window. The proved injective integer shift and uniform actual quadratic
theorem count every cell. For a nonempty cell, its selected-block
predicate bounds the constant affine exponent; empty cells contribute
zero. The finite cover inequality sums these proved cell cardinalities.
All subpolynomial losses are absorbed before the varying data.

## Transfer to the full source interval convention

The arithmetic cover above first proves the count on each standard block
M<=n<=2M. Arbitrary fixed comparable positive intervals are then covered
by a constructed constant number of such integer blocks, with
N<=T*M and M<=T*N for a fixed distortion T. The floor in the smallest
base, actual block coverage and both comparisons are proved.

The bound is first rewritten exactly as

    M^(1/2+c*log2+eta) * Q^(1/(2d)) / e^(1/d).

The last factor is independent of the block scale M. This avoids a
constant raised to a varying beta, which would destroy uniformity.
The degree transfers to d<=(c+zeta)*loglogM; the polylogarithmic width
transfers with an explicit fixed factor 2^|A0|. Constant covering and
height prefactors and the arbitrarily small zeta losses are absorbed
into epsilon. The final c coefficient is therefore unchanged.

The fixed-kernel count transfers by the same actual cover and degree
budget, including odd d>=2. A natural comparison constant is constructed
from every fixed real interval a*N<=n<=b*N with a>0. Uniform positivity
also identifies the absolute-value product with the literal positive
integer product in the source. No interval count or height transfer is
assumed as an external premise.

## A cumulative strengthening

The core proof only needs the upper condition sf(P_A(n))<=N^beta.
It proves the same exponent for that entire cumulative family, without
a lower kernel-size condition. `constant_upper_count` also allows any
fixed comparison factor F in sf(P_A(n))<=F*N^beta. The source dyadic
family follows by absorbing the fixed 2 into an arbitrary positive
exponent. All these bounds hold on every fixed comparable positive
interval. This is P1-MATH-0057.

Both conclusions permit fixed polylogarithmic widths. The independent
fixed-kernel theorem additionally holds for odd degrees >=2. The
prescribed-divisor proof still uses even degree and two-element blocks;
the general-block algebraic identity alone is not asserted to give
a corresponding arbitrary-block counting exponent.

## Dependence on the qualified T5.1 ingredient

T5.1's actual affine count is proved using the universally valid capped
exponent comparison. Its printed uncapped exact comparison remains
unclaimed without a domain qualification, so that numbered row stays
in progress for manuscript wording alignment. This T5.2 proof uses the
proved actual count directly and does not assume the unqualified display.

No new unproved literature input, Paper C port, original manuscript-byte
change or Palomar registration is introduced.

Verification: Lean v4.36.0-rc2 full build passed (9,629 jobs); actual axiom audit passed for all 4,092 theorem/lemma declarations using only propext, Classical.choice and Quot.sound. All 1,807 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 result records remain intact. Ubuntu available space: 17.52 GiB. No unproved count, new literature input, new Paper C port or Palomar registration.
