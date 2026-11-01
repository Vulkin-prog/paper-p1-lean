# The actual shifted quadratic-block count

This extends the checked actual counts of P1-MATH-0054 and closes the
shifted quadratic counting ingredient in T5.2. The final enumeration is
still open. The unqualified uncapped exponent comparison in T5.1 remains
unclaimed. Coverage stays 56/167, with 56 confirmed improvements.

## A wider actual interval

For N/2<=x<=3N and 0<h<=N, the actual product obeys

    N^2 <= 4*x(x+h),    x(x+h)<=12N^2.

If Q<=sf(x(x+h))<2Q, Q>0, the actual square part v satisfies

    N/(4sqrt(Q))<=v<=4N/sqrt(Q).

The actual modulus e*v^2 divides x(x+h), hence is at most N^6 for N>=2.
The proved polynomial-modulus congruence estimate gives the v-fibre;
its finite sum is at most

    N^(epsilon/2)*(192sqrt(Q)/e+4N/sqrt(Q)).

Absorb the fixed 192 uniformly. The general first branch and the trivial
positive-integer count on x<=3N then give the same three exponent bounds.
Their capped minimum is universally at most the affine expression,
without an exact beta<=2 condition. One common threshold precedes
h,e,beta and the actual finite set; h has fixed polylogarithmic height.

## Exact integer-offset transport

For an actual block {a,b}, a<b, |a|,|b|<=W, N<=n<=2N and 2W<=N,
all linear values are positive. Set x=|n+a| and h=|b-a| as naturals.
The checked integer identities give

    x+h=|n+b|,
    N<=2x,    x<=3N,    0<h<=2W,
    sf(P_{a,b}(n))=sf(x(x+h)).

The map n to x is injective on the actual positive range. These are
proved equalities of the literal natural absolute values and kernels;
no replacement polynomial or transport assumption is used.

Every two-element integer block has an ordered pair representation.
For fixed D,A0,epsilon>0 in the width W<=D(log N)^A0, one threshold
therefore gives the actual two-factor count

    #S <= N^(1/2+beta/4-delta/2+epsilon),
    delta=log(e)/log(N),

for N<=n<=2N, N^beta<=sf(P_B(n))<2N^beta and e dividing that kernel.
The threshold precedes W,e,B,beta and the finite set S. Squarefreeness
of the prescribed divisor is unnecessary. Factorizable fixed-kernel
quadratic equations remain included through the proved first branch.

This supplies the uniform actual quadratic bound needed for a selected
block in T5.2. The final finite enumeration over a fixed pair partition,
divisors of e' and dyadic block kernels is not yet claimed.

The subsequent [complete T5.2 checkpoint](PRESCRIBED_SPLIT_PRODUCT_ALIGNMENT.md)
closes that final enumeration and both numbered conclusions, including a
stronger cumulative prescribed-kernel count.

No new unproved literature input, Paper C port, source-byte change or
Palomar registration is introduced.

The [complete T5.2 alignment](PRESCRIBED_SPLIT_PRODUCT_ALIGNMENT.md) now
closes the final selected count and all fixed comparable positive intervals.
