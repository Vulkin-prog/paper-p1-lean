# T19.14: literal all-pair graph and actual original law costs

Source: companion_sections/limits_appendix.tex:1047-1124. The last asymptotic criterion equivalences remain open.

CompanionT19.14 is now IN PROGRESS with its literal all-pair graph,
actual original count laws, positive residual mass, pointwise retained
geometry and every numerical comparison assertion checked. Its final
little-o equivalence to erased-background and original Hermite
approximation remains separate. No numbered completion is added.
Coverage stays87/167 unconditional and45 conditional, with157 confirmed
improvements. This checkpoint adds no mathematical correction.

PositionalAllPairCost proves deterministic restriction, support,
active-edge and vertex identities for arbitrary finite simple graphs.
For nested E subset F on the retained ground G and ANY binary counting
configuration, the all-pair isolated count is at most the good-isolated
count and their difference is at most

 2*numberOfActiveEdges(F\E) + originalCountOutside(G).

Their disagreement indicator is bounded by the same expression with
coefficient1 on the bad-edge count. No degree bound is used.

AllPairDependencyGraph constructs the EXACT source graph: pairs on G
which are contacts at distance exactly L, or strictly separated pairs
with positive relative nullity. All actual good edges are included by
their original affine compatibility and deterministic separation.
Its nongood edges are covered by the actual close-pair population and
the actual nongood dependent-pair population. Their positive joint mass
is at most the close-pair joint mass plus twice the corresponding
absolute centered nongood-pair mass; incompatible pairs are included.

AllPairResidualMass defines the true bad edges, bad joint mass, locally
deficient marginal mass and tau as their sum. Its finite inequality is

 tau <= closePairJointMass + badCenteredActivity/2 + localMarginalMass.

AllPairResidualMassUnderInputs proves UNCONDITIONALLY the local mass
rate1, and CONDITIONALLY tau<=N^(-4/5+epsilon), under the existing explicit
finite pair geometric bundle. The close-pair joint bound is already
unconditional. No new external geometric property is introduced.

AllPairRetainedGeometry proves for EVERY original prime-sign realization
that two distinct positive coordinates left by the all-pair filter have
strictly separated starts and disjoint ORIGINAL square-class spaces.
Run separation handles strict close incompatibility; the actual graph
excludes contact and positive pair nullity. This does not assert that
the filtered indicators are independent, nor exclude higher-order
primitive dependencies.

FiniteAllPairCost transports the literal pointwise bounds through ANY
finite probability space and arbitrary dependent Boolean field. It
proves actual probability-measure total variation, nonnegative mean
loss, and the quantitative bad-joint/local-marginal costs. All changes
of finite expectation order are checked.

PositionalObservationLaw constructs genuine probability laws of arbitrary
natural observations of the original finite field. Every singleton mass
is EXACTLY its event probability under the original infinite prime-sign
measure, and every real test integral is EXACTLY the original Bochner
expectation. Total-count observations after a deterministic field push
have exactly the previously defined count projection coefficients.

AllPairOriginalLaws specializes these constructions to the literal
good-isolated and all-pair counts on the full original dyadic field.
Its good-isolated probability law has exactly the coefficients of the
existing isolatedLaw count projection. Under only the finite original
model assumptions N>=2,L>0, it proves

 TV(goodIsolatedLaw,allPairLaw)<=tau,
 0<=goodIsolatedMean-allPairMean<=2*tau.

AllPairCountMeans identifies the actual means, their nonnegativity and
the unconditional upper bound by the original full count mean.
AllPairOriginalCostsUnderInputs proves weighted recurrence stability at
the RESPECTIVE ACTUAL MEANS. If goodMean<=M, its finite error is
<=(4+2*M)*tau. The original critical mean is unconditionally bounded by
M=2*2^C. The SUM of the actual total-variation cost, absolute mean loss
and absolute weighted-norm change is therefore <=N^(-4/5+epsilon),
conditionally on the same finite pair geometry.

These are actual original-model assertions, with no assumed distance,
intensity or covariance premise. The final asymptotic criterion
equivalences, including the exact original Hermite parameters, have not
yet been inferred or counted as complete. No axiom, Paper C port,
dependency download or original manuscript edit is introduced. Palomar
remains a later milestone.

The JSON row records exact verification and proof commits.
