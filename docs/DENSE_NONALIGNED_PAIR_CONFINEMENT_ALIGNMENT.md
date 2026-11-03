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
