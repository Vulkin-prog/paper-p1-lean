# Complete conditional six-vertex budget for all covers

Source: companion_sections/offset_geometry.tex:309-360, with the actual covered relation space from lines264-306.

Companion T20.8 is now COMPLETE CONDITIONALLY on the already recorded
ordinary surface-cover and normalized curve-count properties. The missing
small-component exclusion is proved from actual original motifs and a
common fixed-third-window coefficient list. The source six-vertex budget,
unrestricted primitive count and prescribed-plane count/mass assertions
are all assembled in SixVertexBudgetUnderInputs.companion_T20_8.
Numbered coverage becomes87/167 unconditional and47 conditional.

The cover is NEVER enumerated. Its actual free three-block components
supply pairwise disjoint transverse square products. Filtering those
of size at most five gives the literal smallCount from the previously
proved finite packing theorem. Every such motif has a singleton block.
SmallTransverseSelection uses just24 permutation/left-degree choices to
select k motifs of one degree-one orientation from a population of24*k.
All selections preserve the exact original vertices and small-prime code.

SmallMotifCoefficients fixes the third centre z and constructs one common
finite coefficient pool. Each motif coefficient is its ACTUAL third-block
product times its ACTUAL small-prime odd-support product. Membership in
the source-supported pool is proved by divisibility, and the literal
integer square equation is verified. No coefficient or cover is a new
free counting parameter. SmallMotifCoefficientBounds proves unconditional
subpower cardinality and polynomial coefficient height for the entire
pool, uniformly before either variable centre is chosen.

SelectedWindowAdmissibility proves monotonicity of even square-class
spaces and inheritance of even independence by arbitrary selected grids.
Actual regular full windows with disjoint relative spaces give EXACTLY
the complete geometric admissibility needed by the existing selected
degree-one root count. No nonalignment assumption is added. In particular,
aligned pairs that still have direct actual spaces are not discarded.

SmallMotifSystems constructs the actual bounded integer offset pattern,
its pairwise disjoint left and right supports, its positive common left
degree and singleton right degree, and its genuine square roots. The
selected two-block total degree is at most4. Its admissibility follows
from the actual full windows, including the coordinate parity conditions.
SmallTransverseHostData turns any actual cover with many small components
into one of these systems, and then forgets the cover completely.

SmallTransverseHostCount fixes only a permutation and the third centre.
Projection to the two remaining centres is injective on that fibre.
The existing coefficient-selected degree-one theorem gives subpower
many actual pairs, using only UniformCover k4 and the normalized curve
property at ambient parameter k+3. Summing the six permutations and N
possible third centres gives N^(1+epsilon) hosts, with all constants
absorbed after choosing the accuracy. No source host bound is passed as
an external argument; only the ordinary geometric properties are inputs.

SmallTransverseMassUnderInputs multiplies this count by the original
affine joint bound p^2 and proves mass <=N^(-1+epsilon). In fact its
uniform_bound applies to EVERY family of distinct regular triples with
pairwise direct actual spaces, BEFORE primitive filtering. This stronger
scope is improvement P1-MATH-0160. The actual exceptional set used in the
source theorem is explicitly filtered by the literal primitive predicate.

Outside that set, EVERY cover has smallCount<24*k simultaneously.
SixVertexBudgetUnderInputs.uniform_budget combines the exact finite
packing inequality with the actual prime-count bound. Its explicit
residual error is
CoverRankPrimeBudget.constant(C0)*B/log(B)+12*k,
with B=L+1, real cutoff C0*B represented exactly by its natural floor,
and C0>=1. Thus the B/log(B) coefficient is independent of epsilon and
the constant12*k is chosen before every host, width and cover. The source
C0>1 is included. Shared-prime vertex covers are converted to the exact
row cover by the already proved equivalence, rather than assumed equal.

The final companion_T20_8 also includes the already proved unrestricted
N^(3/2+epsilon) primitive host count and the prescribed-plane
N^(1+epsilon) host and N^(-1+epsilon) actual mass bounds, with one common
critical threshold. Those latter assertions remain unconditional.
Only the small-component exceptional-set and resulting simultaneous
six-vertex assertion require the two existing ordinary geometric inputs.
No chosen-source surface cover, BCN property, target estimate or new
external property is introduced.

No Paper C port, dependency download or original manuscript edit occurs.
Palomar remains a later milestone.

The JSON row and mathematical finding record exact verification and proof commits.
