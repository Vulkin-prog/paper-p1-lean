# Ordinary smooth source selection and the actual anchored cost

Sources: companion T19.16 and T19.17, limits_appendix.tex:1214 and1313, including the clean-pair constructions in their proofs. All original source hashes are preserved in the numbered ledger.

Companion T19.17 now has a constructive arithmetic small-pivot
selection for every anchor and an actual offsite cost minorant in terms
of the LITERAL ordinary-smooth source census. No short-interval abundance
or desired forcing-cost rate is assumed proved. The result stays in progress.

NonanchorPivotSelection defines ordinary candidate indices by the actual
largest prime factor of j+i, rather than the squarefree kernel or the
largest prime with odd valuation. The actual odd-valuation pivot is no
larger than that ordinary largest prime factor. If a source word has two
ordinary candidates at level Q, one lies outside EVERY prescribed anchor.
A simultaneous selector is constructed across the entire retained source
field, fixed before any random signs, and it selects a pivot <=Q at each
good source. At other sites it selects an arbitrary nonanchor index.

OrdinarySmoothSourcePopulation defines the actual good source set J:
dyadic boundaries with two ordinary candidates in the ACTUAL unsigned
word and with no pivot<=Z anywhere in the MAXIMAL support. It separately
defines the literal set H of sources missing the two ordinary candidates.
The exact finite deletion ledger gives

  N <= |J| + |H| + #badBoundaries(N,B,Z).

The last term already has its proved N^(9/10+epsilon) uniform bound.
The count |H| is left as the actual unresolved ordinary smooth short-
interval census, without calling it small or substituting a kernel census.

AnchoredSmallPivotSelection proves J is contained in the original
at-most-one-small-pivot retained field for Y<=Z. It constructs the chosen
small nonanchor ACTUAL private prime in each source for every admissible
arithmetic anchor rule. The exact source reciprocal sum then satisfies

  S_q >= |J|/Q.

Neither this reciprocal lower bound nor a small-pivot selector is a
premise in the final cost estimate: both are proved from the literal
ordinary candidates. All actual selected primes are positive.

CleanPairReciprocalLower factors the main reciprocal term together with
its collision loss before substitution:

  N*S_q - |J| - c*((N/Z)*S_q+|J|)
     = (1-c/Z)*N*S_q - (c+1)*|J|.

When c<=Z this coefficient is nonnegative, so S_q>=|J|/Q can be used
without reversing an inequality or bounding a negative reciprocal term
separately. This step keeps the small-pivot main scale.

AnchoredSmallPivotCostLower gives one threshold before all widths,
cutoffs, candidate levels Q, anchor rules, actual fields and templates.
Writing c=K*(K+1)+1 for an actual unsigned word of length K+1, if
K+1<=B<=D*log N, B<=Y<=Z<=log(N)^5, M>=2N+B and c<=Z, then

 actual offsite cost >= 2^(-2K) *
   [ (1-c/Z)*N*|J|/Q - (c+1)*|J|
       - N^(19/10+epsilon) - N^(3/2+epsilon) ].

This is an inequality for the actual prescribed anchored field. The
small-pivot choice is performed internally; clean-pair independence,
Palm laws, target flip costs, exceptional bounds and reciprocal lower
bounds are not theorem premises. The field forcing does not depend on
which pivot is chosen to count its contribution. For Q=N^a the only
remaining source-population input is the genuine ordinary-candidate
census, followed by the final uniform asymptotic error comparison and
the separate randomized-orientation extension.

P1-MATH-0187 records the ordinary-vs-kernel distinction, arithmetic
selection outside every anchor, exact source census and the factored
actual cost lower bound. Coverage remains 88 proved and 69 conditional
out of 167, with ten incomplete results. No new external mathematical
input, PaperC port, dependency, compiler change, axiom or original source
edit is introduced. Palomar remains deferred.
