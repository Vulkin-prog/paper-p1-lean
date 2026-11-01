# Actual T5.1 counts and the range of the exponent comparison

Source: `p13:short:quadratic`, companion T5.1, page 31,
`companion_sections/short_supports.tex:9`; statement hash
`98eb59430167ea84a4dd75c36b107f990646c6c2f47783b8292f95e2659899bb`.

All actual counting conclusions are proved. The numbered ledger remains
**in progress** because its literal printed unqualified algebraic comparison
needs a range qualification. No proof of that unqualified comparison is
claimed. Coverage stays 56/167. P1-MATH-0054 records the distinction and a
stronger capped alternative. No failure of the paper's asymptotic count
is established.

## Actual family and quantifiers

`PrescribedQuadraticKernelTheorem.values` is the literal finite family

    N <= n <= 2N,
    N^beta <= sf(n(n+h)) < 2N^beta,
    e | sf(n(n+h)).

For every fixed real D,A0 and epsilon>0, one N0 precedes every N>=N0,
positive natural h,e and real beta with h<=D(log N)^A0. No squarefreeness
premise on e is needed. The actual canonical kernel and square part,
including q=1, are those in the first-branch checkpoint. All powers of N
in these statements use real exponents where appropriate.

## The second branch

The actual identity q*v^2=n(n+h), positivity, h<=N and the dyadic ranges
give N/(2 sqrt(Q)) <= v <= 3N/sqrt(Q). The number of actual positive
part values is at most the real upper endpoint, without an extra one.
Divisibility gives e*v^2 | n(n+h). A representative of each nonempty
part fibre proves its actual modulus is at most N^5; no separate height
assumption is imposed.

The proved gcd-group congruence count bounds the v-fibre by
N^(epsilon/2)*(2N/(e*v^2)+1). The actual lower part endpoint and actual
number of part values then give

    #S <= N^(epsilon/2)*(24 sqrt(Q)/e + 3N/sqrt(Q))
       <= 24 N^(epsilon/2)*(sqrt(Q)/e + N/sqrt(Q)).

The fixed 24 is absorbed uniformly. Both branches now accept real Q.
The first has actual kernel budget at most 2Q/e. Substitution Q=N^beta
and delta=log(e)/log(N) is checked with exact real-power identities.

## Minimum, capped and affine counts

The actual branches prove #S<=N^(c2(beta,delta)+epsilon), where

    c2 = min(beta-delta, max(beta/2-delta, 1-beta/2)).

The trivial positive-integer count adds a third branch and proves the
stronger #S<=N^(min(1,c2)+epsilon). All fixed factors are absorbed before
the varying parameters. The algebraic theorem `capped_le_affine` proves
for ALL real beta,delta that

    min(1,c2(beta,delta)) <= 1/2+beta/4-delta/2.

This proves the advertised affine actual count directly, including kernel
scales just above exponent 2, without an exact beta<=2 hypothesis.

## Qualification of the printed comparison

The uncapped exact comparison is proved under beta-2delta<=2, in
particular beta<=2 and delta>=0. Without a domain condition it fails at
beta=5/2, delta=0: c2=5/4 while the affine expression is 9/8.

That abstract example is not asserted to belong to the paper's
asymptotically admissible families. The source proof already uses
beta<=2+o(1). The formal proof derives N^beta<=6N^2 from every actual
nonempty family and hence beta<=2+eta eventually, uniformly for any
fixed eta>0. Since e>=1 gives delta>=0, `eventual_source_comparison`
proves c2<=affine+epsilon uniformly for those actual families.
The more general finite margin is eta/4 when beta-2delta<=2+eta, eta>=0.

For the next manuscript version, either print the capped exponent and
its exact universal comparison, qualify the uncapped comparison, or
display the o(1) margin already used by the proof. Until that wording is
aligned, the unchanged original result is not labelled fully proved.
`companion_T5_1_counts` packages the actual count conclusions, the stronger
capped count and the qualified comparison with explicit quantifier order.

No new unproved literature input, Paper C port, manuscript-byte change
or Palomar registration is introduced.
