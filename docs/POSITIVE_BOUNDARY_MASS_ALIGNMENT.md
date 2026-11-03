# Positive boundary mass in companion T17.3

Source: companion_sections/closure.tex:209. Both the exact finite inequality and the uniform arithmetic rate are proved.

Companion T17.3 is now COMPLETE CONDITIONALLY, including BOTH its exact
finite positive-boundary inequality and its uniform rate4/5 over the literal
linear range4K<=L. For H=8*(L+1), G=regularStarts(N,L), mu=E Z_G and the
literal actual nonretained low-nullity sum R_K, the checked statements are

  R_K <= F + Gdef + exp(2mu) * [ exp(A_good+A_bad+B_K)-1-A_good ],
  R_K <= N^(-4/5+epsilon), uniformly over every4K<=L.

F and Gdef are the previously constructed literal independent deficits,
with their exact cardinality grouping. A_good=4 sum_good c(e),
A_bad=4 sum_(all regular nongood pairs) |c(e)|, and B_K is the actual
weighted connected centered sum at sizes3..K with compatible nullity<=3L/2.
The finite family defining R_K is EXACTLY the actual subsets I of G with
rho(I)<=3L/2, I nonretained and |I|<=K. The original source's added terms
B/N and a_N^2 are absorbed by the proved uniform N^epsilon slack; the final
rate is therefore stated in the stronger unit-power form without those
additional nonnegative terms.

FinitePolymerRemainder proves an exact finite subset-generator remainder:
remove the empty component collection and exactly one distinguished good
component BEFORE the exponential majorant. Actual union-recoverable
component collections inject into the remaining powerset, so arbitrary
nonnegative component activities have bound exp(sum_all)-1-sum_good.
The exponential Taylor remainder is proved separately, with its explicit
quadratic budget. No independence of canonical components as random
choices, partition count heuristic, or target remainder is assumed.

CanonicalComponentWeights proves actual canonical blocks pairwise disjoint,
their cardinalities sum to |I|, and the EXACT weighted factorization
u^|I|*|c(I)|=product_C(u^|C|*|c(C)|). ActualComponentRemainder handles zero
coefficients by an exact finite filter. Nonzero coefficients have no
singleton canonical part. Every remaining part is connected, has at least
two sites, and inherits its actual nullity cap by monotonicity. Thus the
component remainder includes affine incompatibility and zero marginals;
no cancelling centered expression is replaced by a joint probability.

CenteredSourcePairBound proves 0<=c(e) and |c(e)|<=q(e) for every actual
positive-joint source pair, from the exact heterogeneous joint rank formula
and the pair covariance identity. NonretainedPositiveMass.pointwise_bound
uses the exact inverse centering expansion and separates the empty term,
source-pair terms and residual terms. Source pairs remain distinguished.
For a nonretained I and a source e subset I, the complement I minus e is
PROVED to fail directness after compression; otherwise I would be retained.
RestrictedSeedComplements.fiber_bound therefore charges that source term
to its actual source-relative independent deficit. No factorization of a
failed extension's arithmetic joint probability is assumed.

SeedComplementSum bounds the sum of EVERY contained residual seed, with
its own nonnegative centered activity and independently weighted free
complement. The exact complement map is injective in each source fiber;
its full finite generator is bounded by exp(sum_x u*p_x). Independent
nonretained terms belong to the actual ordinary independent deficit.
NonretainedPositiveMass.finite_bound combines these comparisons with the
nonlinear actual canonical-component remainder on ANY finite actual ground
G, with exact heterogeneous marginals, ANY fixed u>=0 and ANY size cap K.
Source pairs only need positive actual joint probability and membership
in G.powersetCard2. No equal-marginal assumption, regularity premise or
linear size restriction is used in this finite theorem.

RetainedBoundaryPositiveMass.finite_bound specializes this stronger finite
lemma to the actual regular ground, goodEdges and u=2. Exact marginal
identities identify F and Gdef with firstMass and secondMass; the exact
pair split identifies A_good+A_bad. It proves the source finite inequality
for EVERY K, even when4K>L. The linear restriction is needed only by the
arithmetic rate estimates, not by the finite probability/combinatorics.
Finding P1-MATH-0145 records this separation and heterogeneous extension.

RetainedBadPairActivityUnderInputs keeps every nongood centered pair,
including incompatible sources. Direct nongood pairs have zero coefficient;
the actual dependent ones lie in the height-five tail or finite exceptional
sector at Q=4. Their rates4/5 and1 give A_bad rate4/5. The only input is the
existing finite pair bundle at cap sizeCap(epsilon/128).
RetainedComponentActivityUnderInputs supplies ONE common threshold over
ALL4K<=L: A_bad has rate4/5, B_K rate1, A_good+A_bad rate2/3. B_K uses the
completed literal linear connected theorem at t=4, eta=3/2 and weight2;
the whole pair rate uses the existing fixed-cap pair bundle. These are
proved constituent estimates, not desired-bound premises.

PositiveBoundaryMassUnderInputs uses the fixed internal margin
delta=min(epsilon/4,1/12), selected before N. The total component activity
is at most2*N^(-7/12), hence eventually at most1. Its squared exponential
remainder costs N^(-7/6), while A_bad supplies rate4/5 and B_K rate1.
The actual mean is bounded uniformly; the already completed independent
deficits have stronger rates1 and7/6. A final fixed-factor absorption gives
the literal4/5 rate after one threshold, uniformly in K and L.
The final Hypotheses are a finite union of the SAME three previously
recorded geometric properties: three coarse bundles at margins delta/128,
delta/512, delta/128; their pair caps sizeCap(delta/524288) and
sizeCap(delta/1024); the whole-pair cap sizeCap(1/100); and the nongood-pair
cap sizeCap(delta/128). No BCN or new unproved property is introduced.

This checkpoint adds10 modules,27 theorems,10 definitions and2 finite
parameter structures. Coverage is87/167 unconditional and29 conditional,
with145 confirmed mathematical improvements. The complete-law quadratic
approximation still requires combining this result with the stopped
identity, large-boundary tail and reference conversion; no such completion
is claimed here. The sharp4/3 complete-law rate and T15.1 separated clauses
remain open. No original manuscript bytes, Paper C port, dependency download,
hidden axiom or Palomar registration is added.

The JSON T17.3 row and finding145 record full validation and its exact proof commit.
