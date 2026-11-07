# Prime support of the retained cylinder

Checkpoint P1-MATH-0987 strengthens the finite bound from companion T19.7.
All original and revised numbered statement blocks are preserved.

For a prime q<=N, let m=floor(N/q), L=q-1, and M=2*q*m. The retained starts
are x=q*u+1 with m+1<=u<2*m and q not dividing u. Their preceding value is
negative and their next L values are positive. Every integer they use is
at most M; in particular x+L=q*(u+1)<=M<=2*N.

The event prescribing the one-negative-prime sample only through M has
probability 2^(-primeCount(M)). All later prime signs remain unrestricted.
The retained positive count is determined by this cylinder, has at least
N/q-N/q^2-3 starts, and is pointwise bounded by the full positive count.
The latter remains bounded by the full total count. Integrability of all
the exponential observables is proved for every real t. For t>=0 the
actual moments therefore satisfy

```text
positiveMGF(N,q-1,t), totalMGF(N,q-1,t)
  >= exp(t*(N/q-N/q^2-3) - primeCount(2*q*floor(N/q))*log(2)).
```

Replacing the charge by primeCount(2*N) also gives a valid lower bound.
The full count is never treated as an observable on the smaller cylinder.
The restricted count is integrated first and then compared monotonically.

At the original scale q=7 and N=2^(q-1)=64, the supported, dyadic and old
sufficient cutoffs are 126, 128 and 134. Their inclusive prime counts are
30, 31 and 32. Lean kernel computation verifies these exact counts, and
an additional theorem proves the factor-four increase of the exponential
lower bound with the same count contribution. This is a finite improvement;
the original odd-prime t>2 asymptotic statement and coefficient are preserved.

Canonical bounds: SupportedPrimeCylinder.positive_exponential_lower and
SupportedPrimeCylinder.total_exponential_lower. The optional dyadic-cutoff
corollaries and exact-gain example are in the same module.

Direct Lean v4.36.0-rc2 verification and exact 17-theorem axiom audit passed, with proof warnings as errors and only propext, Classical.choice and Quot.sound. The prime-count example uses kernel computation. Whole-project build and declaration-reference replay are pending.
