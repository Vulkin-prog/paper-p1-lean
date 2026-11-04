# Actual square-root normalized-defect pair hosts for the full enlarged alignment

Companion T21.1, arithmetic_consequences.tex:26 and the fixed-height normalized defective-host argument in its proof. Original source and statement hashes are preserved.

Companion T21.1 now has an actual square-root host count for every
fixed-height enlarged aligned pair containing a defective normalized
integer. The bound includes zero exact units and is uniform over every
positive macroscopic lower-endpoint exponent AFTER the common threshold.
The complete profile sums remain open and coverage is unchanged.

BoundedNormalizedDefectPairs works first on the entire bounded source
interval [2,M). Its ordered pair set uses the literal enlarged geometric
alignment and the actual existence of an H-defective integer in the
deduplicated normalized union. No private-prime or residual-rank value
is a theorem premise, and there is no exact-unit hypothesis.

For each actual source-word position k and side, encode a pair by

  (b*x-a*y, normalizedDefectiveValue).

The defective value fixes the corresponding source coordinate by
multiplicative cancellation and its actual vertex label. The integer
geometric residual fixes the other coordinate. This is an injection
on the original bounded pair population. Its residual lies in the
literal integer interval with radius (a+b)*B, and its positive defective
value is at most b*(M+L).

Taking the exact finite union over the B positions and two sides gives

  #defectPairs <= 2B*(2(a+b)B+1)*#positiveDefectsBelow(H,b(M+L)).

All pairs keep their original ordered source and target labels. The
prefactor is proved at most (8Q+2)*B^2 whenever a<=b<=Q. The proof
uses no exact-unit choice, coprimality assumption or cutoff lower bound.

BoundedNormalizedDefectPairCount combines this exact injection with
the already proved global defect count and logarithmic polynomial
absorption. For every fixed critical band C, height cap Q, cutoff
constant D>=0 and epsilon>0, one threshold precedes every critical L,
actual cutoff H<=D*B and moving positive a<=b<=Q. It proves

  #actual bounded defectPairs <= M^(1/2+epsilon).

The global counting height is at most 2Q*M and the cutoff is at most
D*upperScale*log(M). The exact quadratic prefactor and all constants
are absorbed in the supplied epsilon margin. This is the literal
finite exceptional population, rather than a bound assumed of it.

MacroscopicNormalizedDefectHosts defines the same actual defective
pair population on [ceil(M^delta),M). It injects by inclusion into
the bounded population, using the exact natural endpoints and source
positivity. Its square-root host bound therefore has a threshold
chosen BEFORE every delta>0, as well as before all moving pair and
cutoff data. This strengthens the fixed-delta form needed by T21.1.
No profile sum or weighted residual conclusion is inferred solely
from this unweighted count.

P1-MATH-0201 records this actual exceptional-host count. The next
steps are its precise connection with nonprivate normalized pairs
and extra kernel relations, the weighted fixed/high-height residual
sums and the rational positive/signed channel translation profiles.
T21.1 remains in progress. Coverage stays 88 proved and 70 conditional
out of 167, with nine incomplete results. There are 200 improvements
and one statement-scope correction. No new external input, kernel
axiom, software dependency or compiler change is introduced. Original
manuscripts remain byte-identical and Palomar remains deferred.
