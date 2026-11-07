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

Full Lean v4.36.0-rc2 replay passed at source 68164c4abb37b8679c9c3f1f4e78dc52667a285b: 18,567 build jobs, 19,485 source-discovered theorem axiom checks and 19,643 distinct declaration-reference checks, all actual process exits 0. Proof warnings are errors; only propext, Classical.choice and Quot.sound occur.

The full replay and original compressed logs are preserved in [the validation record](validation/checkpoint-0987/validation.json).

The refinement and exact gain example are integrated in the unnumbered version 1.7 companion appendix. Both PDFs were rebuilt and reviewed; all 167 numbered statement blocks are unchanged. See [the manuscript validation](manuscript-v1.7-validation.json).
