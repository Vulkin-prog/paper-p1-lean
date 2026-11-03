# Two completed connected branches of main15.12

Source: main_sections/exact_transfer.tex:803-841, including the low-compatible-rank estimate and summation above large cores. The small-core branch remains open.

Two complete branches of the CONNECTED argument in main15.12
are now proved UNCONDITIONALLY: arbitrary-cardinality closure
above a large chosen ten-core has mass N^(-3/2+epsilon), and
every connected family of size at least256 with compatible
nullity at most L/60 has mass N^(-83/60+epsilon).
Main15.12 remains in_progress because its small chosen-core
branch still needs the fixed connected activity and pair
deficit assembly. Its separate primitive clause is already
unconditionally proved with stronger power7/5.
Coverage87/167, conditional results20 and confirmed
improvements133 are unchanged.

SeedComplementMass proves the exact finite identity
sum_{D subset I subset G} product_{I minus D}(w_x)
  =product_{G minus D}(1+w_x).
No seed marginal is divided out, so zero weights are allowed.
Its general positive cover theorem allows an ARBITRARY
nonnegative activity c(D) on each seed. If each family
activity is bounded by one seed's activity times its true
independent complement product, the entire family sum is
bounded by exp(sum_G w_x)*sum_D c(D). The finite sum
interchange and actual cover are proved, with no factorial
or deletion-order factor and no family-size cutoff.

ChosenRelationCore.core uses the previously proved existence
theorem to choose an ACTUAL compatible ten-core for every
nonzero length and every original family, including an
incompatible original family. properties supplies its
containment, actual positive joint probability, projection
conditions, exact rank budget and actual activity inequality.
weighted_bound absorbs all fixed powers from peeling into
the single fixed weight512*u. The inequality is
u^card(I)*|c(I)| <= (512u)^card(D)*q(D)*
                   product_{I minus D}(512u*p_x).
All true marginal and joint factors are retained.

LargeCoreFamilyCover.cores is the literal finite population
of actual ten-cores inside G, of size at least256 and raw
nullity at most2L. If the chosen core D of I is large and
rho_*(I)<=2L, its positive probability and containment imply
rho(D)<=rho_*(I), so D really belongs to that population.
finite_bound uses the general complement cover, and
source_mass_le_actual compares its q-weighted seed sum to
the already proved actual core mass q+|c|.
LargeCoreClosureMass.uniform_bound therefore proves
sum_I u^card(I)*|c(I)|<=N^(-3/2+epsilon)
for EVERY actual family population with those chosen-core
properties, at ALL cardinalities. No connectedness or
growing-order cutoff is required for this larger population.
The exact marginal cap bounds the free-complement mean by
a constant before N; its exponential is absorbed only as
a fixed constant. This fully sums the large-core branch,
rather than assuming a propagation or complement estimate.

OriginalTwoAnchorWitnesses proves actual coordinatewise
participation implies projection rank at least one at
EVERY block. The supplied effective relation gives a
nonzero vector in the actual projection image; the exact
projection-rank identity and the physical heavy-word
theorem give the literal two-anchor witness.
Every connected original family of size at least two is
proved to have that property via an actual coordinate
relation. No single relation nonzero at all blocks is
assumed. No coefficient-nonzero or positive-marginal
premise is needed for this connected participation fact.

ConnectedIndependent256Budget.uniform_bound applies the
retuned t=2,A=14,b=59/70,sigma=93/100 certificate budgets.
It proves the ACTUAL independent product mass of every
connected dyadic population of sizes at least256 is
N^(-7/5+epsilon), uniformly at all cardinalities.
LowCompatibleNullityTail.uniform_bound combines that with
the actual compatible-nullity centered majorant, using
weights2*u*p_x. The full maximum rho_* is kept, even for
incompatible I and zero marginal patterns. Under
rho_*(I)<=L/60, the binary rank amplification costs at most
N^(1/60+epsilon). The resulting power is83/60, stronger
than the27/20 low-rank branch in the source proof and
stronger than the required final4/3. This refinement uses
the same two-anchor parameter retuning already recorded
in finding133; no new overall connected theorem is claimed.

The remaining case has a small chosen compatible ten-core.
Its nonempty-rank retention on the growing range,
connectedness forcing a non-direct complement, finite
small-core activity and pair-deficit summation still have
to be assembled. None of those desired arithmetic bounds
is substituted as an external hypothesis here.
No geometric input, axiom, dependency download, Paper C
port, original manuscript byte or Palomar action changes.

The JSON result row records full validation and its exact proof commit.
