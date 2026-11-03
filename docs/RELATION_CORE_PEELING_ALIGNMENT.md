# Actual core construction and probability steps in main15.12

Source: main_sections/exact_transfer.tex:746-775 (projection dimensions and ratio) and the core peeling argument at:817-870. These are preparations for the connected clause, not its completion.

The actual core construction, exact centered peeling bound,
small-core probability ratio and large-core mass in main15.12
are now formalized UNCONDITIONALLY. These are preparatory
parts of its connected assertion. Main15.12 remains
in_progress: its separate primitive clause is already proved
with stronger power7/5, while the final connected summation
and the required fixed connected activity step remain OPEN.
Numbered coverage87/167, conditional results20 and confirmed
improvements133 are unchanged. No new finding is added for
proving the manuscript's existing core steps.

RelationProjectionRank.loss is the ACTUAL deletion nullity
rho(I)-rho(I erase x). kernel_finrank proves that the kernel
of coordinate projection has exactly the erased nullity:
the finite kernel cardinality is the already exact
missedRelations count, and binary cardinality identifies
its dimension. Rank-nullity then proves
dim(projection_x K(I))+rho(I erase x)=rho(I).
The loss equals the actual effective projection rank.
No ambient finite-dimensionality of the full prime vector
space is required, and no kernel dimension is assumed.

RelationCorePeeling constructs a terminal finite deletion
trace, deleting only blocks of relation projection rank
at most k. Its exact budget is
rho(A)<=rho(D)+k*(card(A)-card(D)).
At termination every remaining projection rank is greater
than k. This differs from the older private-rank peeling:
the new construction deletes SMALL RELATION projections,
which is the direction needed by15.12.
RelationCoreWitnesses.Core t L D uses these exact losses.
exists_ten_core constructs a true ten-core with k=8 and
the exact nullity budget. The previously proved heavy even
word theorem converts each effective projection into an
actual physical relation with ten selected values at that
block; different blocks may use different witnesses.

RelationCoreIndependentBudget.uniform_ten applies the
proved t-anchor budgets to every actual ten-core of
cardinality at least256, giving independent mass
N^(-7/2+epsilon), at ALL cardinalities. The exact parameters
are t=10,A=12,b=31/60,sigma=23/25.
LargeTenCoreMass.uniform_rank includes the ACTUAL nullity
amplification for cores with rho<=2L: it costs at most
2^(2L)=O_C(N^2). Their full rank-weight mass is therefore
N^(-3/2+epsilon). uniform_actual proves the larger actual
q(D)+|c(D)| mass has this same power, including incompatible
and zero-marginal systems. The proof does not assume
primitiveness, separated windows, local regularity or
positive compatibility. It directly supplies the large
ten-core branch needed in15.12.

RelationCoreCounting.full_support_lower proves
(1-card(D)/2^k)*2^rho(D)<=number of full-support relations
whenever each actual projection rank is at least k.
It uses the exact erased-kernel cardinalities and a finite
union bound. half_full_support gives
2^rho(D)<=2*number of full-support relations for every
ten-core of size at most256.
RelationCoreMomentRatio.centered_count transports the
actual compatible infinite-model centered coefficient
to this exact square-class relation count. Together with
the actual joint rank formula, ten_core_ratio proves
q(D)<=2*c(D) for every compatible actual ten-core with
at most256 blocks. There is no common nominal marginal
or hypothetical affine sign prescription.

RelationCoreActivityPeeling.compatible_majorant extends
the actual compatible-nullity centered majorant to every
marginal pattern, including zeros. peeling_bound proves
the literal pointwise activity inequality
|c(I)|<=2^card(I)*2^(k*(card(I)-card(D)))*
        product_{I minus D}(p_x)*q(D)
for any actual compatible maximizing source A and a
constructed k-peeling trace from A to D.
The larger I may be incompatible; every factor is an
ACTUAL marginal or joint probability. The proof uses the
actual maximizing-compatible-nullity equality, the exact
trace budget and the finite product decomposition.
No deletion-order enumeration occurs.
exists_ten_core_bound INTERNALLY chooses the maximizing
compatible A, constructs D, proves q(D)>0, and supplies
the ten-core property, exact rank budget and activity
inequality simultaneously. Neither this core nor its
probability estimate is an external premise.

The remaining connected proof must sum the freely
weighted complements, handle the growing-cardinality
rank retention, and bound the finitely many small cores
using the still-open fixed connected activity estimate.
These verified pieces alone do not establish that final
4/3 bound, T16.2 at all sizes, or the complete stopped law.
No geometric input, new axiom, dependency download,
Paper C port, manuscript byte or Palomar action changes.

The JSON result row records full validation and its exact proof commit.
