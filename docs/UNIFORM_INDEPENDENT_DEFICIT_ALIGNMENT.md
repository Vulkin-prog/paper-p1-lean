# All-cardinality independent deficit: uniform Euler-average foundations

Source: `main_sections/exact_transfer.tex:323`. The final independent deficit remains open.

Preparation of the all-cardinality independent deficit15.6:
the rough-prime WINDOW AVERAGE in its proof is now established
unconditionally, with an explicit constant and without treating
the number of exposed sources as fixed. Main15.6 moves from
not_started to in_progress. Its final deficit estimate is NOT
yet proved. Coverage remains84/167 proved and16 conditional,
with128 confirmed mathematical improvements. This checkpoint
adds arithmetic foundations and no new numbered completion.

FiniteEulerAverage proves the exact finite divisor expansion
of an arbitrary nonnegative local Euler product over a finite
set of distinct primes. For every natural X, the average over
1<=n<=X is at most
X*product_p(1+h(p)/p).
The exact expansion uses the actual count floor(X/d) of positive
multiples of the product d of the selected distinct primes.
Primality supplies the actual coprimality implication d|n iff
every selected prime divides n. In particular there is no
spurious +1 term for each modulus in this first-moment bound.

InverseSqrtTail proves the finite elementary bound
sum_{Y<n<=X} n^(-3/2) <= 2/sqrt(Y), for every Y>=1.
It telescopes reciprocal square roots and does not invoke an
analytic tail premise or any prime-distribution estimate.
RoughEulerMoments uses the cutoff Y=64*B^2 and the actual
factor p^(-1/2). For p>Y the moment increment
h_B(p)=(1+p^(-1/2))^B-1 is at most8*B*p^(-1/2).
The already proved elementary exponential remainder gives
this bound since B/sqrt(p)<1/8. The finite tail bound gives
sum_p h_B(p)/p<=2 for EVERY finite prime set above this cutoff.
Consequently the actual B-th moment of the local rough-prime
Euler product, summed over1<=n<=X, is at most X*exp(2),
uniformly in B and in the actual finite prime set.

FiniteProductPowerMean proves the pointwise AM-GM inequality
product_i f_i <= average_i f_i^B for B positive positions,
and the finite first-moment consequence after interchanging
the actual sums. This suffices in place of the printed Holder
step. WindowEulerAverage.first_moment applies it to every true
position x-1+i of an actual complete dyadic window. Each fixed
position maps the actual starts injectively into1..3N.
For N>=2 and1<=B<=N+1 it proves
sum_{N<=x<2N} product_{i<B} product_{p in P,p|(x-1+i)}
  (1+p^(-1/2)) <= 3*N*exp(2),
for EVERY finite prime set P above64*B^2. This product counts
a prime once for every position it divides and therefore also
majorizes the single-occurrence union-of-primes product in
the manuscript. The explicit bound is independent of B.

The constant enlargement from the printed cutoff B^2 to64*B^2
is internal to these new lemmas; no preserved manuscript is
changed. The old-source Euler factor, the actual relative
exceptional exposure count and its entire cardinality sum
remain to be connected before15.6 can be completed. No desired
deficit bound or growing-order arithmetic constant is assumed.
There is no new geometric or literature input, PaperC port,
dependency download, original-source edit or Palomar registration.

The JSON result row records full validation and its exact proof commit.
