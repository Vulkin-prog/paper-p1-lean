# Actual macroscopic source geometry and one-unit residual rank

Companion T21.1, arithmetic_consequences.tex:26 and its proof, particularly the uniform Runge extension down to x,y>=M^delta. The original statement and source hashes are preserved.

Companion T21.1 is now in progress, with the actual one-exact-unit
macroscopic residual-rank extension proved internally. The literal
macroscopic domain is constructed and its source-size geometry is
proved uniformly. No positive or signed profile equivalent is yet
claimed, and numbered coverage is unchanged.

NormalizedPairResidualCriterion extracts the actual base-sensitive
criterion from the existing P1 two-progression argument. For every
c>0 and epsilon>0, once B=L+1 is large, source bases satisfying

  8B<=x,  2log(2)<=log(x),  cB<=log(x)/2

have normalized residual rank at most epsilon*B, uniformly over
all positive reduced-height parameters a<=b<=B^3 and actual unit
witnesses b*(x-1+i)=a*(y-1+j), with y>0. The deduplicated normalized
union, actual prime-row budget and actual residual value kernel
are retained. The omitted-prime budget and the complete quantitative
Runge rank bound are the already proved P1 theorems, with no new
external geometric or analytic premise.

MacroscopicIntervalGeometry defines the EXACT source population

  starts(M,delta)=[ceil(M^delta),M) intersect the natural integers.

It proves the real/natural endpoint equivalence, positivity of every
source for M>=2 and delta>0, and log(x)>=delta*log(M).
For every fixed critical band C, delta>0 and fixed height threshold T,
it supplies one threshold before M,L,x for which every actual source
and every critical L satisfy B>=T, 8B<=x, log(x)>=2log(2), and

  [delta/(2*upperScale)]*B<=log(x)/2.

The proof uses the already checked positive logarithmic scales and
log(M)/M^delta tending to zero. No comparability of x with M and no
bounded ratio of the interval endpoints is assumed.

MacroscopicNormalizedPairResidual applies the finite criterion with
c=delta/(2*upperScale). It proves the actual normalized residual
rank is o(B), uniformly over all actual sources down to M^delta,
all critical L, every height up to B^3 and every exact-unit witness.
The second source need only be positive in this intermediate result.

MacroscopicAlignedPairRank then proves three actual pair conclusions
when both sources lie in the original macroscopic interval and
there is at least one exact unit: pair loss is bounded by the exact
rational-unit dimension plus epsilon*B; at coprime height b it is
at most L/b+epsilon*B; and the actual full intersection rank obeys
the same L/b bound. Actual normalized units and full raw-value rank
are connected by the existing finite rank-loss identities.

This proves the one-unit part of the uniform macroscopic Runge
extension used in the proof of T21.1. The no-unit enlarged alignment
case, fixed-height residual counts, actual rational/positive/signed
channel sums and their leading equivalents are still required.
The formalization does not infer any profile sum merely from this
local rank statement. The interval-dependent leading 1:2 channel
and its distinct B-mod-2 and L-mod-2 conventions remain to be aligned.

P1-MATH-0198 records this internal extension. Coverage stays 88 proved
and 70 conditional out of 167, with nine incomplete numbered results.
T21.1 changes from not_started to in_progress. There are 197 confirmed
improvements and one statement-scope correction. The inspected Paper C
macroscopic modules informed the comparison, but no new Paper C source
code or external theorem is imported in this checkpoint: these proofs
extend the existing P1 development. Original manuscripts, software
dependencies, kernel axioms and compiler settings are unchanged.
Palomar remains deferred.
