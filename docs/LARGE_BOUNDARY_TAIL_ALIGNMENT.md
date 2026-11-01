# Companion T12.2 and a stronger large-boundary estimate

The full numbered lemma is proved on the actual regular-window boundary,
with the least integer cutoff defined in the manuscript. The same cutoff
in fact gives O(N^(-5/3)), improving the stated O(N^(-3/2)). This is
P1-MATH-0052; numbered coverage is 56/167.

Source: `p1:stop:tail`, companion T12.2, page 50,
`companion_sections/stopped.tex:120`; original statement hash
`58419af8ab6f89d036eca8383642d845b56d29aec345513766e926272b6359ce`.

## Exact least cutoff

`BoundaryCutoff.Condition` is the literal pair of requirements

    K >= max(4,ceil(4*exp(1)*Lambda)),
    K*log(K/(2*exp(1)*Lambda)) >= 3*log N.

For every positive real Lambda and every natural N, an explicit large
integer proves this condition nonempty. `cutoff` is its least natural
member, and its condition and minimality are proved. It is positive
and at least 2*Lambda as a real number. The source cutoff is therefore
constructed, rather than assumed to exist or replaced by a different
convenient order.

## A finite exponential tilt

`LargeSubsetWeights` proves, for any finite ground set P, p>=0,
#P*p<=Lambda and t>=1,

    sum_{I subset P, |I|>K} (2p)^|I|
      <= exp(#P*(2p)*t)/t^K.

Multiplication by t^K is compared term by term to t^|I|. The complete
finite powerset polynomial equals (1+2pt)^#P and is bounded by its
exponential majorant. Set t=K/(2*Lambda). The cutoff's logarithmic
budget yields a bound <=N^(-3), without the factor 2 in the source
factorial-tail argument. No independence assumption, infinite series,
Stirling input or assumed moment/tail estimate is used here.

## Actual affine probabilities and positive boundary mass

`LargeBoundaryMass.families` is the literal finite family of subsets
of the actual regular set, in the ordered boundary of the actual
retained class, with size greater than K. `mass` is exactly

    sum_I 2^|I| * infiniteJointMoment(L,I).

Actual joint affine probabilities are bounded by p^|I|*2^rho(I), with
p=2^(-L). The positive-probability branch uses the already proved
exact identity and actual regular marginals. The zero-probability
branch is retained, so incompatible families are covered. A general
finite nullity-budget theorem bounds the actual mass by 2^R times
the finite powerset tail whenever the actual boundary losses are <=R.

The proved T12.1 bounds give both R=3L/2 and the more precise
R=4L/3+1. The cutoff therefore gives the two finite bounds

    mass <= 2^(3L/2) * N^(-3),
    mass <= 2^(4L/3+1) * N^(-3).

## Full source theorem and the improved exponent

`LargeBoundaryTail` proves the actual regular mean is <=2^C in the
fixed critical band |L-log(N)/log(2)|<=C. Thus Lambda=2^C is an
explicit admissible source upper mean. There is also a theorem for
any fixed positive Lambda satisfying the actual upper-mean condition.

One threshold before all critical lengths, real prime cutoffs and
boundary families proves the source estimate with explicit constant

    mass <= 2^(3C/2) * N^(-3/2).

Retaining the precise nullity estimate gives, with the same least
cutoff and no additional hypotheses,

    mass <= 2*2^(4C/3) * N^(-5/3).

`companion_T12_2` proves the full source conclusion;
`improved_source_tail` proves the stronger one. These are actual
positive probability sums; no centered-to-positive conversion or
arithmetic counting assertion is assumed.

The separately displayed unnumbered cutoff asymptotic
K~3*log(N)/loglog(N), and its eventual K<=L/4 range, are not yet
proved by this checkpoint and remain for their later uses. They are
not required in this numbered large-boundary estimate. Neither
original manuscript is edited, and no new unproved literature input,
Paper C port or Palomar registration is introduced.

The full build passed (9,545 jobs), the actual axiom audit passed for
all 3,855 declarations, and Lean checked all 1,570 distinct
coverage/finding names. Only propext, Classical.choice and Quot.sound
occur; original manuscript bytes are unchanged.

Validated full T12.2 and improved-tail checkpoint (9,545 build jobs;
3,855 audited declarations; 1,570 directly checked names):
[e2a0e935344ae4c6ae3fc666de9e050d61fecaa5](https://github.com/Vulkin-prog/paper-p1-lean/commit/e2a0e935344ae4c6ae3fc666de9e050d61fecaa5).
