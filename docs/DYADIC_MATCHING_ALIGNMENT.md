# Dyadic bounded-affine matching core — partial T2.6 and T1.11

Primary source: companion T2.6, page 22, `p1:arith:fixed-channel-rank`,
`companion_sections/supplemental_arithmetic.tex:209`, statement hash
`8dd614c19e50df20ed1eb9f3ab37c07386f1ce3665c3499e26d83211ceab60b9`.
The same argument occurs in T1.11, page 15, `p1:arith:palmrank`,
`companion_sections/arithmetic_appendix.tex:861`, statement hash
`f5c10336a982eb463bd69da026b36971a8d8bbede48fd0ad27463a97cfe6a307`.
Both numbered rank statements remain **in progress**.

## Actual finite data and integer separation

Set B=L+1. The actual source labels at fixed indices i,j equal a*t,b*t,
and the target satisfies d*z=c*t+h. All three centres are in [N,2N).
Let d<=H, |h|<=H and d>0. The source labels give the literal dyadic
parameter inequalities; no asymptotic rational-separation input is used.

`DyadicTargetInterior.weak_ratio_bounds` proves that

    t > 2H(B+1)

forces b*d<=2c and c<=2a*d. This follows from the integer gap of at
least one in any strict violation. Equalities force

    |a*t-N| <= B+H,       |b*t-2N| <= B+2H,

respectively. Therefore both inequalities are strict away from the two
strips of radius B+2H. The entirely finite scale condition

    N > a*2H*(B+1)+B

implies the needed lower bound on t, using an actual source label.
`ActualDyadicInterior.ratio_interior` then gives b/2<c/d<2a.

## Literal source exception family

For each of the B^2 pairs of actual source indices, `sourcePairs` is
the actual dyadic source-pair set satisfying the normalized unit
identity. The first endpoint subset filters by distance of the first
actual label from N, and the second by distance of the second label
from 2N. Their union over index placements is
`DyadicEndpointPairs.exceptional`. It is independent of c,d,h,z.

For strip radius R, the first subset has at most 2bR+1 pairs, the
second at most 2aR+1. The actual normalized anchor is injective for
fixed placements. Counting its integer interval gives

    card(exceptional) <= B^2*(2(a+b)R+2).

For R=B+2H, H<=B^J and fixed integer J>=1, this becomes the literal
bound

    card(exceptional) <= (6(a+b)+2)*B^(J+2).

The family may include pairs outside the geometric good-edge class;
this is a proved finite upper bound for a containing exception family.
Every actual source witness in either endpoint strip belongs to it.

## Literal target pool for one fixed source parameter

The weak upper fraction bound gives c<=2a*d<=2aH, so a separate
numerator-height hypothesis is unnecessary. `DyadicTargetCount.codes`
is the product of the c,d ranges and the integer displacement interval.
Its decoding is the literal natural target value (c*t+h)/d when the
target equation holds. Every actual bounded-affine target belongs to
this pool, which has cardinality at most

    2aH^2*(2H+1) <= 6aH^3        (H>=1).

For H<=B^J, the bound is 6aB^(3J). It is a target pool for one fixed
actual source parameter t. No curve-counting statement or external
Diophantine estimate is a premise.

## Actual matching count and common threshold

`SeparatedTargetMatches.match_bound` proves B*gamma+3 using only
deterministic separation from each source. It includes both physical
fractions, which still satisfy B/b+2. The existing compatible-match
theorem now derives separation from the actual positive joint event
and invokes this more general result.

`DyadicMatchBound.separated_bound` combines the literal endpoint
exception with this actual-value count. Its compatible wrapper derives
the separation premises from positive actual triple mass.

`CriticalPolynomialScale.source_size_eventually` supplies the finite
scale inequality uniformly for all critical lengths and all H<=B^J.
`DyadicMatchingArithmetic.uniform_core` packages the source exception
count, the target-pool count and the actual separated matching bound
with **one threshold before every source and target choice**. The
source channel a,b, the exponent J and the critical-band width are
fixed before that threshold. These explicit bounds are P1-MATH-0040.

## Remaining bridges

These results assume the displayed bounded affine representation of
the target. The construction of such data from the paper's geometric
alignment predicate remains separate unfinished work. The actual
target/old quotient-rank bridge and the extension by old prime
information are also unfinished. The generic residual arithmetic and
complete T1.9 are available, but the actual position count is not
asserted to equal a rank loss. Neither T1.11 nor T2.6 is counted complete.

No optimality of the finite constants is claimed. No new Paper C port,
external mathematical hypothesis, manuscript revision or Palomar
registration is introduced; original source bytes are preserved.
