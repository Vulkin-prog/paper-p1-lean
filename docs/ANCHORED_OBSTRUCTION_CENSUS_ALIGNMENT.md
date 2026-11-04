# Uniform deterministic anchored obstruction under the ordinary census

Sources: companion T19.16 and T19.17, limits_appendix.tex:1214 and1313, including the clean-pair constructions in their proofs. All original source hashes are preserved in the numbered ledger.

The deterministic-anchor part of companion T19.17 is now proved
under ONE explicit, independent ordinary source census. Every cutoff,
power error, finite field identity, actual forcing cost, source selection,
and arithmetic deletion is discharged. The census itself and the
randomized-orientation extension remain open, so T19.17 stays in progress.

LogFifthPivotCutoff keeps Z=floor(log(N)^5) exactly. For every fixed D
and t>0, one threshold before all B<=D*log N gives B^2+2<=t*Z.
For t<=1 this proves 2B<=Z, positive Z, and for K+1<=B the literal
collision coefficient c=K*(K+1)+1 satisfies c<=Z and c/Z<=t.
The floor and all quantifier orders are explicit; no fixed critical
length offset is used in this cutoff estimate.

PowerGap converts every strict exponent gap into an arbitrarily small
prescribed multiple. With epsilon=(1/10-a)/2 for 0<a<1/10,
AnchoredCostErrorScale proves, uniformly over every logarithmic word,

  N^(9/10+epsilon) <= (t/2)*N,
  (c+1)*N + N^(19/10+epsilon) + N^(3/2+epsilon)
       <= t*N^(2-a).

The polynomial collision endpoint cost is absorbed using the proved
uniform word-polynomial bound. The exact exponent 9/10 is kept separate
from the source/target-pair exponents 19/10 and 3/2.

AnchoredCostNormalization gives the finite comparison. If the retained
ordinary-candidate source fraction is at least 1-t, c/Z<=t, and the
three total errors cost at most t*N^2/Q, then the factored arithmetic
minorant is at least (1-3t)*N^2/Q. The exact squared source fraction
loses at most 2t. The source upper bound |J|<=N controls the negative
endpoint term in the correct direction.

AnchoredObstructionFromCensus applies this in the ORIGINAL unsigned
anchored field at Q=N^a and the exact natural Z. The sole additional
finite condition is that the literal sources missing two ordinary
candidates number at most (t/2)*N. The proved bad-pivot count controls
the other source loss. Thus one threshold, before every width, cutoff,
anchor rule, actual field and template, gives

  actual offsite cost >= (1-3t)*2^(-2K)*N^(2-a).

No forcing-cost bound, Palm law, independent-word law, small-pivot
choice, source reciprocal lower bound, cutoff limit or exceptional-set
estimate is an argument of this theorem.

AnchoredObstructionUnderOrdinaryCensus states the remaining arithmetic
input separately as OrdinaryCensusDensity(C,a): for every tau>0,
eventually UNIFORMLY for |L-log_2 N|<=C and i in {0,1}, the actual
sources whose unsigned word of length L+i+1 lacks two ordinary
N^a-smooth candidates number at most tau*N. This input refers only
to actual integer boundaries and ordinary largest prime factors; it
contains no anchors, random samples, probabilities, couplings or costs.
Its deduction from the Matomaki--Radziwill short-interval theorem is
NOT asserted proved.

Under this explicit independent arithmetic input, the theorem
 deterministic_under_census
proves the entire deterministic-anchor lower conclusion, uniformly
over both i=0,1, all original retained-population arithmetic anchor
rules and all maximal widths B*=L+E+2<=D*log N. For every eta>0 the
actual offsite cost is at least

  (1-eta)*2^(-2(L+i))*N^(2-a).

The proved nominal_scale_identity identifies the scale exactly with
2^(-2i)*(N*2^(-L))^2*N^(-a), the manuscript's ambient lambda scale.
The actual retained mean remains the separate already proved quantity.
The actual start and unsigned exact-zero templates are both included.
No external theorem is introduced as an axiom and none is declared
proved merely because it is a theorem argument.

P1-MATH-0188 records the exact natural cutoff, all uniform asymptotic
error comparisons and the deterministic obstruction conditional solely
on its genuine ordinary census. The full numbered result remains
in progress because that census and the randomized-orientation part
are unproved. Coverage remains 88 proved and 69 conditional out of
167, with ten incomplete results. Original manuscripts, dependency
versions and the compiler are unchanged. Palomar stays deferred.
