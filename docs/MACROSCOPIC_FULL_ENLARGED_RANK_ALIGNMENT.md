# Uniform macroscopic rank for the full enlarged alignment including zero units

Companion T21.1, arithmetic_consequences.tex:26 and its proof, particularly the uniform enlarged aligned-rank extension to x,y>=M^delta. All original source hashes are preserved.

Companion T21.1 now has the COMPLETE uniform macroscopic enlarged-
alignment rank extension used in its proof, including pairs with
NO exact unit. The interval-dependent profile sums are still open,
so the numbered result remains in progress and coverage is unchanged.

MacroscopicPolynomialScale proves that every fixed polynomial in
the actual critical width is eventually smaller than every source
in the literal interval [ceil(M^delta),M), uniformly over all critical
L. It uses the proved log-power/M^delta limit and retains the exact
real-to-natural endpoint. The threshold precedes every source and
moving critical width.

EnlargedAlignedResidualCriterion is a base-sensitive finite criterion
for the LITERAL geometric alignment

  |b*x-a*y| <= (a+b)*(L+1).

For any c>0 and epsilon>0, sufficiently large B=L+1, source bases
with 32B^4<x, log(x)>=2log(2) and cB<=log(x)/2 have actual residual
row rank at most epsilon*B. All heights a<=b<=B^3 are included.
There is no exact-unit hypothesis. The normalized union is put in
its actual arithmetic interval with base b*x-3bB and radius 6bB.
The omitted-prime budget, row-system construction and Runge bound
are the existing checked P1 two-progression theorems.

MacroscopicEnlargedAlignedResidual discharges this finite criterion
on EVERY actual macroscopic source with c=delta/(2*upperScale),
using the exact interval geometry and the proved 32B^4 source bound.
It proves both the complete residual row-rank bound and the actual
full residual value-kernel rank bound, uniformly in the critical band,
all source positions and all height parameters up to B^3. The second
source need only be positive in these intermediate results.

MacroscopicEnlargedAlignedRank proves the corresponding actual pair
conclusions when both sources lie in the original macroscopic interval:

  pairLoss <= max(#exactUnits-1,0) + epsilon*B,
  pairLoss <= L/b + epsilon*B,
  actualIntersectionRank <= L/b + epsilon*B.

The second and third bounds require the actual reduced coprime height,
as in the manuscript. The first rational-unit expression uses natural
subtraction exactly, so its zero-unit case is explicitly included.
No artificial exact-unit witness is inserted and no density or rank
bound is an external assumption.

This completes the uniform Runge/rank extension down to x,y>=M^delta
under the full enlarged geometric alignment convention, rather than
only its one-unit subcase. It is proved internally from the existing
P1 development and adds no new literature or geometric input. The
remaining work for T21.1 is the actual fixed-height residual-host
count and the ordered positive/signed rational channel sums, their
comparison with full aligned masses, the distinct parity formulas
and final leading equivalents. None of these sums is asserted merely
from the local rank extension.

P1-MATH-0199 records this progress. Coverage stays 88 proved and
70 conditional out of 167, with nine incomplete results. There are
198 improvements and one statement-scope correction. Original
manuscripts, compiler settings, dependencies and permitted axioms
are unchanged. Palomar remains deferred.
