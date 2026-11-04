# Independent short-interval input implies the literal ordinary source census

Companion T19.17, limits_appendix.tex:1313 and1329-1340. Primary source: [Matomäki–Radziwiłł2016, Corollary6, p.1019](https://annals.math.princeton.edu/wp-content/uploads/annals-v183-n3-p06-p.pdf). The analytic result itself remains an explicit unformalized input.

The independent ordinary smooth source census in companion T19.17
is now derived from an explicit fixed-parameter analytic input, with
all interval, exponent, density and moving-critical-width comparisons
proved in Lean. The analytic input itself is NOT proved or installed
as an axiom. T19.17 remains in progress pending its final printed
parameter and nominal-scale specialization.

Published source: K. Matomaki and M. Radziwill, Multiplicative functions
in short intervals, Annals of Mathematics 183 (2016), 1015-1056, Corollary 6,
p. 1019, DOI 10.4007/annals.2016.183.3.6. The primary published PDF was
checked on 4 November 2026:
https://annals.math.princeton.edu/wp-content/uploads/annals-v183-n3-p06-p.pdf
For a fixed positive smoothness parameter, that result gives a
positive-density relative smooth-number count in almost all intervals
whose length tends to infinity. We use only its fixed u=2/a logarithmic
specialization and the positivity of the associated limiting density.

OrdinaryShortIntervalCensusInput makes the needed weakening explicit.
RelativeDensityInput(psi,a,rho) says that for every delta>0, the number
of j<X whose actual ordinary smooth-candidate count in indices
0,...,psi(j), at threshold j^(a/2), differs from rho*psi(j) by more
than delta*psi(j), is at most delta*X for sufficiently large X.
The interval is inclusive and its actual candidate set is the
previously defined ordinaryIndices, with no odd-kernel substitution.

For EVERY natural psi tending to infinity and every rho>0, Lean
proves that this input implies TwoCandidateDensity: the number of
j<X with fewer than two actual candidates is o(X). The proof removes
a finite initial segment where psi is small, compares the remaining
failure to the relative-error set and absorbs the finite initial
count at the specified density tolerance. All these losses and
threshold quantifiers are explicit.

LogarithmicOrdinaryCensusBridge uses

  psi(j)=floor(log(j)/(4*log(2))),

proves psi tends to infinity, and defines CorollarySixLogInput(a) as
the existence of a positive rho with that relative-density input.
The smaller logarithmic interval is permitted by the published
corollary and suffices for the actual word.

Uniformly for every L with |L-log(N)/log(2)|<=C, every original dyadic
boundary j and sufficiently large N, psi(j)<=L. The threshold precedes
L and j. OrdinaryCandidateMonotonicity proves exact finite candidate
cardinality monotonicity in BOTH word width and smoothness cutoff.
It also proves j^(a/2)<=N^a for j<=2N and N>=2, using j<=N^2.
Thus every short-interval candidate pair is an actual candidate pair
in either unsigned source word K=L+i, i=0,1.

Every missing-candidate ORIGINAL boundary lies in the literal bad
prefix set below 2N. Its cardinality is bounded by that entire prefix
set. Applying the natural-density estimate at 2N with tolerance tau/2
gives exactly tau*N. There is no endpoint or unrecorded translation
loss. Consequently CorollarySixLogInput(a) implies the independent
OrdinaryCensusDensity(C,a) for every fixed C and a>0, with no forcing,
anchor, probability, cost or reciprocal sum in either analytic input.

P1-MATH-0196 records this complete analytic-input-to-actual-census
bridge. The Matomaki--Radziwill analytic assertion and positivity of
its density remain explicit unformalized literature dependencies;
all downstream census deductions are internal proofs. Coverage stays
88 proved and 69 conditional out of 167, with ten incomplete results.
There are 195 improvements and one statement-scope correction.
Original manuscripts and compiler settings are preserved. No new
kernel axiom or software dependency is introduced. Palomar is deferred.
