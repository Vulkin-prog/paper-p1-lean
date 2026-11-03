# Dense nonaligned actual pair confinement

Source: companion_sections/confinement.tex:149, T8.3. T8.2 remains in progress.

Companion T8.3 is complete CONDITIONALLY on the existing explicit
P1-GEO-BCN-PLANE-UNIFORM input, PlaneCurvePointCount.UniformBound c kappa
with c>0. For every fixed eta,epsilon>0, one threshold before every
critical L and every finite ordered dyadic pair family gives #F<=N^epsilon
when the actual intersection dimension d_xy is at least eta*(L+1)
and the pair is not CompressedTargetAlignment.Aligned 1 x y L.
The stronger version with density eta*L is also proved.
Local rank defects in either window are allowed. No half-power target
host estimate, full-rank premise or assumed small-kernel witness is used.
The only unproved argument in this route is the previously recorded BCN
property; the other three finite geometric properties are not invoked.
This does not prove BCN, Pila, or the separate Pila-only dependency route.

ActualOffsetNonalignment turns two exact units at distinct offset
points into the source positive reduced alignment, using the actual
offsets i-1 and the proved bounded-point geometry. Thus a nonaligned
pair has no exact offset line. Its disjoint-square-class variant only
needs nonvanishing of two-point even classes, not full-window injectivity.
CriticalTwoPointClasses proves that nonvanishing uniformly for ALL
critical dyadic windows, including defective ones, directly from the
already proved fixed-two-value Runge independence. Pairwise disjoint
effective spaces therefore also give the no-exact-line premise needed
for the pending primitive-triple assembly.

ActivePhysicalPrimeGroups now proves that every actual nonempty active
support has an injective block projection and contains two positions
in different blocks. ActivePhysicalGroupCountUnderBCN assigns each
actual large composite group to one such pair. For each ordered block
pair the indexed T8.1 little-o theorem applies to the TRUE divisors
and TRUE offsets. Full multiplicities are retained when different
ternary supports project to the same offset pair. There are at most
nine ordered block pairs. One threshold precedes the index TYPE, all
two- or three-block dyadic windows, every restriction M and every
cutoff H>=L+1. Thus #largeGroups(N^tau)<=epsilon*(L+1) uniformly.
Neither regularity nor a supplied prime pool is needed for this count.

DensePhysicalKernelWitnessUnderBCN combines this actual uniform count
with the checked finite erasure. If M has dimension>=eta*L, all block
projections inject, and NoDisjointRecovery has order d=1 or2 and t>=2,
every true center belongs to the ACTUAL small-kernel window set with
product cap N^(2*tau*supportBound(d,t,t-1)). All groups are computed on
the initial M; no recovery property is transported through the final
erasure. The source dependence of all thresholds is explicit.

TwoTargetEmptySource proves that the two-target kernel over W=0 has
EXACTLY the actual intersection dimension d_xy. The existing physical
regularization for s=0 gives order1 recovery exclusion, injective
projections and loss at most eta*L/4. It is performed separately for
each actual host, without enumerating chosen subspaces or deletions.
After t is fixed by eta, choose tau=epsilon/(16*(K+1)), where
K=supportBound(1,t,t-1). Both centers lie in the same literal set
SmallKernelWindowSets.twoWindows with product exponent2*tau*K.
Its proved two-small-kernel count, with margin epsilon/4, bounds the
pair family by N^(4*tau*K+epsilon/2)<=N^epsilon.
All pairs are counted as ordered pairs; no distinctness premise,
affine-compatibility assumption or homogeneous-to-actual substitution
is introduced. Nonalignment already excludes diagonal hosts.

T8.2 remains IN PROGRESS: its needed uniform group count and two-point
Runge geometry are now proved, but its primitive-triple host, homogeneous
mass and centered-activity assembly are not asserted at this checkpoint.
No new mathematical-improvement identifier, unproved input, global axiom
or Paper C port is introduced. Coverage is87/167 unconditional and41
conditional, with151 confirmed improvements. Original source bytes,
dependency pins, Ubuntu disk constraints and the later Palomar milestone
are preserved.

The JSON rows record the exact validation and proof commit.


## Correction of the local nonalignment scope

Companion T8.2 is complete CONDITIONALLY on the existing explicit
P1-GEO-BCN-PLANE-UNIFORM property, PlaneCurvePointCount.UniformBound c kappa
with c>0. Its single bundled theorem companion_T8_2 has one threshold
before every critical length and every actual triple family: for density
rho_rel>=eta*(L+1), #hosts<=N^epsilon and the actual heterogeneous rank
mass is <=N^(-2+epsilon); the total absolute centered activity of EVERY
primitive triple family is <=N^(-3/2+epsilon). The latter also holds for
the stronger sum of actual joint probability plus absolute centered
coefficient. No affine compatibility or positive-marginal restriction
is imposed. Zero marginals are retained using the proved exact zero
centered coefficient, not by substituting a nominal probability.
The host and dense-mass statements also hold under the weaker eta*L
density premise. The nominal homogeneous dense mass has the same power2.

InjectivePhysicalRelationRegularization chooses an actual linear section
of the SURJECTIVE physical-to-effective relation map. This removes local
window kernels without assuming full local rank. If effective projections
are injective, physical projections on the chosen section are injective.
Order2 disjoint-recovery regularization loses at most eta*L/4 dimensions.
One fixed t is chosen from eta before every index TYPE, three-block
configuration, true centers, critical length and arbitrary section.
The recovery exclusion, dimension and physical injectivity are proved
for the image subspace, using the checked injective-lift transport.

PrimitiveTrueWindowRelations identifies the effective kernel dimension
with the LITERAL runRelativeNullity of the actual finite center set.
Primitivity gives injective projections by the already checked minimal
relation-kernel theorem. Every pair in a primitive family of size>=3 is
proved disjoint by its strict proper-subfamily nullity, including windows
with local defects. The uniform two-value Runge result then gives the
no-exact-offset-line property for every pair, without full local rank.

DensePrimitiveTripleHostsUnderBCN applies the previous uniform actual
group count and kernel erasure with d=2. Every center of every actual
dense primitive triple lies in the SAME literal two-small-kernel set.
The recovery order is fixed first; tau=epsilon/(24*(K+1)) and the count
margin epsilon/6 are chosen afterwards, with K=supportBound(2,t,t-1).
A powersetCard cover retains the actual unordered triples. Its card is
at most #smallWindows^3, giving N^(6*tau*K+epsilon/2)<=N^epsilon.
No relation subspaces, deletion sets or auxiliary curves are enumerated.
This is the actual host count, not an abstract implication assuming it.

DensePrimitiveTripleRankMassUnderBCN uses the proved primitive bound
rho_rel<=L and the unconditional true marginal cap K_C/N. With the new
host bound, the exact heterogeneous weight prod(p_x)*2^rho has dense
mass N^(-2+epsilon). All constants are absorbed after the host count,
with one threshold. The literal nominal weight p^3*2^rho satisfies the
same bound, using the exact finite primitive cap and p^3*2^L=p^2.
The phrase homogeneous mass here is aligned with the actual effective
weight w(I) in main exact_setup.tex:93-100; nominal homogeneous mass is
also supplied, not silently substituted for the heterogeneous weight.

LowPrimitiveTripleRankMass is unconditional. For ANY fixed integer b>0,
rho_rel<L/b gives actual primitive mass at most
N^(-3/2+1/b+epsilon). This uses the already proved full primitive
independent mass and the actual critical binary root bound. Choosing b
after the final margin, and splitting the actual family at L/b, gives
PrimitiveTripleMassUnderBCN.uniform_rank_mass with power3/2. Dense
families use their stronger power2. The exact centered and joint bounds
then give the source activity, with all zero-marginal and incompatible
cases included.

The source alignment check also closes a scope mismatch in the preceding
T8.3 interface. Main confinement.tex:15-20 defines alignment IN THIS
SECTION by two exact units. The earlier theorem at proof commit019a203
only covered the smaller population outside the enlarged height-B^3
alignment. It was insufficient by itself for that local convention.
The proof is now generalized to the literal ActualOffsetNonalignment.NoExact
premise, and companion_T8_3_no_exact is the full source statement. The
older enlarged-nonalignment consequence and its declaration names remain
valid. Both use the same existing BCN input and allow defective windows.
This is a correction of the formalization's statement alignment, not a
new mathematical error in the original paper. It is recorded explicitly
here and in the T8.3 correspondence note; no manuscript improvement ID
is manufactured for that interface correction.

T8.2 moves from in_progress to conditional. T8.3 stays conditional with
its full local nonalignment scope now checked. Coverage is87/167
unconditional and42 conditional, with151 confirmed manuscript improvements.
No new unproved input, axiom, Paper C port, dependency download, original
manuscript-byte change or Palomar registration is introduced. The BCN
property and the other separately recorded geometric inputs remain
unproved; neither Pila nor BCN is claimed to be formalized. The near-
primitive and strong nonaligned triple profiles and optimal law upper
rate remain open.
