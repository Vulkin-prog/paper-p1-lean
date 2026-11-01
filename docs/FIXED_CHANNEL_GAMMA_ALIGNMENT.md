# Companion T2.6 — The exact finite coefficient, partial checkpoint

Source: Lemma T2.6, page 22, `p1:arith:fixed-channel-rank`,
`companion_sections/supplemental_arithmetic.tex:209`. Original statement
SHA-256:
`8dd614c19e50df20ed1eb9f3ab37c07386f1ce3665c3499e26d83211ceab60b9`.
Original source bytes are preserved.

T2.6 remains **in progress** and is not counted complete. This checkpoint
proves its finite coefficient bound and exact examples. The aligned-target
rank estimate, endpoint exceptional sources and inclusion of the prime
signs of a,b remain open.

## Exact definition

`FixedChannelGamma` uses natural positive a,b,c,d and the actual source
numerator bound c<=b*(a+b-1). The ratio restrictions are exactly
b/2<c/d<2a, with gcd(c,d)=1 and c dividing neither a nor b.
`ratio_conditions` proves their equivalence with the two strict integer
inequalities b*d<2*c and c<2*a*d.

The first inequality bounds d by 2*b*(a+b-1) whenever b>=1.
`mem_candidates` proves that this extra finite cutoff removes no source
fraction. `mem_values_iff_source` identifies the complete set in the
source display, including 1/b. Its rational maximum is `gamma`;
`isGreatest_real_values` proves that its real coercion `gammaReal` is
the literal real maximum of precisely that finite set.

## Proved values and sharpness

`ChannelMatchDensity` proves the coprime-divisor inequality
3*(g+h-1)<=2*c for positive proper divisors g,h of c with gcd(g,h)=1.
Applying it to g=gcd(c,a), h=gcd(c,b) proves the universal bound
gamma<=2/3 for coprime a,b and b>=3.

The exact checked values are:

| Channel | gamma |
|---|---|
| 2:3 | 1/3 |
| 3:4 | 1/2 |
| 8:9 | 2/3 |

The first two upper bounds are finite arithmetic proofs covering every
eligible numerator and denominator, with the source strict endpoints
retained. No numerical search is assumed. In the last channel, the
eligible fraction 6/1 has gcd(6,8)=2 and gcd(6,9)=3, hence density
(2+3-1)/6=2/3. Together with the universal bound this proves the
coefficient is sharp across admissible fixed channels. This is
P1-MATH-0036.

This is sharpness of the displayed finite **coefficient**. It gives no
construction of a target whose actual rank loss attains that value,
and no optimality claim for a Palm-mean exponent. Those questions are
separate from the finite maximum.

No external mathematical input, new Paper C port, manuscript revision
or Palomar registration is used at this checkpoint.

Validated coefficient checkpoint for T2.6 and P1-MATH-0036:
[b9ff1b2874b76ba8fe97e314db236980b2fe6e13](https://github.com/Vulkin-prog/paper-p1-lean/commit/b9ff1b2874b76ba8fe97e314db236980b2fe6e13).
