# A coarse connected-triple branch toward main15.10 and15.12

This branch is preparatory. It proves a rate1 joint bound for the full actual isolated-vertex class, not the source's sharp41/30 triple proposition or the entire connected tail.

The actual connected-triple branch with an isolated vertex in its
PAIR-dependence graph is now proved at joint-mass rate1, conditionally
on the SAME explicit finite geometric properties. This includes every
primitive triple and every triple with exactly one dependent pair.
An isolated vertex is direct from each of the two other windows taken
separately; it need not be direct from their combined span. No desired
triple-mass estimate is supplied as a theorem input.

ConnectedTripleLowCrossing proves the finite pointwise bound
q(T)<=K*(sum_{x in T}|c(T erase x)|*p_x+prod_{x in T}p_x)
whenever SOME vertex/complement crossing has binary dimension factor
at most K. The exact pair reconstruction, heterogeneous marginals
and positive one-term enlargement are retained, including zero actual
marginals and incompatible systems. Its finite sum is at most
K*(D1+M3_independent_connected), using the proved pair-incidence cost
without any representation multiplicity. The asymptotic version
allows any fixed a>=0 and yields N^(-3/2+a+epsilon) when some actual
crossing dimension is at most a*L. Its pair-geometry source cap is
epsilon/2048. No isolated-vertex assumption is needed for this low
crossing theorem.

RestrictedSingletonPairCover defines the ACTUAL source-specific
fibers F.filter(T=>x in T and R(x,T)). Its weighted positive cover
sums only actual two-target extensions belonging to that fiber.
It does not replace R(x,T) by the weaker existence of another suitable
source. Membership, the cover and exact source erasure are proved.
ProperPairCrossing proves that directness from each target implies
directness from EVERY proper subfamily of that target pair, without
assuming the target pair is internally direct.

IsolatedVertexDenseTripleMassUnderInputs uses those literal fibers
with an actual isolated vertex and crossing dimension>=eta*L. The
completed full dense minimal-pair cost applies above its singleton
source, even when the other two targets are internally dependent.
Summing the actual source marginals uses the proved bounded mean;
a single common threshold precedes all critical lengths, subgrounds,
triples, vertex choices and pair representations. The resulting
actual joint sum is N^(-1+epsilon). IsolatedVertexTripleMassUnderInputs
partitions the whole isolated-vertex triple population at crossing
threshold L/4. The low branch is stronger than rate1; the dense branch
has rate1. Their sum retains rate1 after error absorption. Both finite
parameter bundles and the pair source capepsilon/4096 are explicit.

This is a proved BRANCH, not a bound for all connected triples.
Triples containing at least two dependent pairs remain to be covered.
The printed sharp exponent41/30 of main14.3 is not claimed for this
larger population. Main15.10 remains in_progress, including its
separate sharp primitive-four and full connected-family requirements;
main15.12's connected tail remains open. Coverage87/167 unconditional,
20 conditional and135 confirmed improvements are unchanged. No new
literature property, axiom, dependency download, Paper C port,
manuscript-byte edit or Palomar action is added.

The JSON result row records full validation and its exact proof commit.
