# Triple activity: qualitative structure and exact cancellation

Sources: main Theorem 11.2 (`p13:activity:incompatible`) and Proposition
11.3 (`p13:activity:kappa3`), `main_sections/triple_activities.tex`.
All three numbered results 11.1, 11.2 and 11.3 are **in progress**, not counted complete.
Coverage remains 72/167 (main 25/73, companion 47/94).

## Positivity holds at every finite order

`FamilyCenteredMass` defines the actual centered coefficient of arbitrary
finite binary affine events, centered at each event's exact uniform
probability. For a common affine witness, its exact value is the product
of those actual local probabilities times the cardinality of the full-
support effective relation set. The common witness makes every relation
character equal to one. Hence every compatible coefficient is nonnegative.
The result covers every finite order, repeated formal event coordinates,
zero-dimensional local spaces and empty families. It does not require
arithmetic, regularity, separation or a fixed-order asymptotic regime.

`CompatibleRunCentered` identifies the finite coefficient with the actual
original infinite-model centered run coefficient. Positive joint mass
supplies one actual common cylinder witness. The full-support relation
count is transported by the proved equivalence from row spaces to the
physical effective square-class spaces. Thus every compatible original
run family has the same exact nonnegative count formula with its actual
heterogeneous marginals, including irregular windows and repeated
formal centers. `coefficient_nonneg` gives the literal finite-set version.
This strengthens and simplifies the compatible-triple sign assertion
of main 11.3; it is recorded as P1-MATH-0071.

## Exact triple cancellation and connectedness

`TripleCentering` proves the complete heterogeneous three-site expansion
for arbitrary normalized joint data. When the triple joint mass is zero,
the centered coefficient is exactly minus the independent product minus
its three pair centered coefficients weighted by the remaining marginal.
`TripleCancellationBound` takes absolute values while retaining both signs
of each pair coefficient. `InfiniteTripleCancellation` identifies all
terms with actual original infinite-measure joint moments and marginal
probabilities. No compatibility or sign is silently discarded.

`SmallFinpartition` proves that a partition of at most three elements
without singleton parts is indiscrete. A full-support relation cannot
have a singleton part in a relation-direct partition. Consequently
`TripleActivityConnected` proves that an admissible nonzero triple
coefficient has one canonical direct component. A disconnected triple
therefore has coefficient zero. The admissibility premise is precisely
positivity of the three actual local marginals, as in the manuscript's
set I_N of possible starts.

## Exact finite activity comparison

`CompatibleActivitySplit` partitions an arbitrary finite population by
positive joint mass versus zero joint mass. Positivity gives the exact
identity

    absolute activity - compatible centered activity
      = incompatible absolute activity >= 0.

The absolute signed-sum error is bounded by the same incompatible
absolute activity. These statements hold at every finite order and for
mixed finite populations. At order three, disconnected coefficients
vanish, so `TripleActivityConnected.positive_eq_connected` identifies the
full compatible sum with the source connected compatible activity K3+.
Its `absolute_comparison` and `signed_comparison` are the corresponding
literal finite identities for the source triple populations.

## Actual independent incompatible-triple mass

`IncompatibleTripleSeed.families` is the actual finite population of
zero-joint-mass triples with nonzero centered coefficient. Removing the
zero coefficients preserves the incompatible absolute activity exactly.
The population is a subset of the actual connected triples. The complete
main 10.2 heterogeneous independent-mass bound then proves that the sum
of its independent products is at most N^(-3/2+epsilon), after a uniform
threshold before the length and admissible dyadic center set.

This is the first term in the main 11.2 proof. It is an independent
weight estimate, not the full incompatible activity estimate.

## Exact pair/target deficit and incidence reduction

`IndependentTargetDeficit.deficit` is the literal source D_(2,1), using
actual infinite pair coefficients, actual heterogeneous target marginals
and the physical effective square-class spaces. `pair_rank` identifies
the pair nullity with dim(S_x intersection S_y); `target_pair` identifies
the target condition with S_z intersection (S_x+S_y) nonzero.

`CenteredDependenceSupport` proves that at every finite order, a nonzero
admissible centered coefficient supplies a full-support effective relation.
Every coordinate lies in the span of the others, so every target meets
that span nontrivially. A nonempty nonzero coefficient also forces positive
effective relative nullity. No assumption on connectedness is needed for
these stronger support statements.

`TriplePairIncidence.erased_sum` proves, for arbitrary r and additive
commutative target, the exact sum identity between an (r+1)-element set
with a distinguished member and its r-element complement with that member.
Its restricted nonnegative form retains the actual dependence predicates.
`IncompatibleTripleReduction.pair_cost` consequently bounds all pair terms
of the actual active incompatible population by ONE copy of D_(2,1).
`finite_bound` gives incompatible absolute activity <= independent active
triple mass + D_(2,1). `reduced_bound` supplies the complete independent
N^(-3/2+epsilon) term with a threshold before L and the admissible dyadic set.
The improved finite constant and its incidence justification are recorded
as P1-MATH-0072.

## Actual third factorial cumulant and repeated indices

`SubsetPowerSums` proves the complete square and cube expansions with
all repeated indices over any commutative ring. `ThirdFactorialCumulant`
then proves the exact heterogeneous subset-data identity using the
erased-set incidence sum. These are algebraic identities, without sign
or independence assumptions. `FactorialCountMoments.factorialCountMoment_eq_subset`
identifies the actual infinite falling-factorial count moment with r! times
the unordered joint-mass sum. `ThirdRunFactorialCumulant.exact_formula`
therefore gives the literal original infinite-count third factorial cumulant:

    kappa3 = 6 sum_{|T|=3} c(T)
             -6 sum_{e={x,y}} (p_x+p_y)c(e) +2 sum_x p_x^3.

`RepeatedIndexCost.bound` proves the exact cost bound
12 p_* A2 +2 p_*^2 mu, retaining arbitrary heterogeneous p_x and both signs
of c(e). `ThirdRunActivityComparison.finite_bound` adds 6 times the actual
incompatible absolute activity to this cost. `RepeatedRunCost` uses the
proved actual critical-band marginal cap and finite dyadic mean bound to
obtain, uniformly before L and every dyadic subfamily,

    repeated cost <=12 K A2/N +2 K^3/N^2.

`ThirdCumulantReduction.cumulant_reduction` completes the actual comparison
assembly, with explicit remaining arithmetic quantities:

    |kappa3 -6 K3+| <= N^(-3/2+epsilon) +6 D_(2,1)
                       +12 K A2/N +2 K^3/N^2.

Its `absolute_reduction` gives the nonnegative difference A3-K3+ at most
N^(-3/2+epsilon)+D_(2,1). No bound for D_(2,1) or A2 is assumed. These
formulas isolate exactly the unproved arithmetic obligations, without
counting their conclusions as completed numbered results. This completes
the source cumulant/repeated-index assembly and adds no independent new
mathematical finding beyond the already recorded improvements.

## Uniform actual independent target mass

`WindowTargetHosts` lifts every actual target with a nontrivial effective
intersection into the one-block finite effective-relation population. The
source effective span is proved contained in the full span of its actual
raw window values. A finite source enumeration preserves the value union
exactly, including overlapping and internally defective source windows.
No short basis or prime witness is assumed.

`IndependentTargetMass.uniform_count` applies the complete half-count to
prove N^(1/2+epsilon) actual targets after every source family of a fixed
cardinality. `uniform_mass` combines this count with the actual
heterogeneous critical-band marginals, giving N^(-1/2+epsilon) independent
target mass. One threshold precedes the length, dyadic subfamily and
source centers; zero source cardinality is allowed. `deficit_bound`
consequently proves D_(2,1) <= A2 N^(-1/2+epsilon).

This verifies the fixed-source target step of the main 11.1 source proof.
It is not the claimed N^(-3/2+epsilon) full deficit estimate: the good
channels need their sharper two-block compression count, and the weak/
exceptional classes need their separate pair-activity estimates.

## Remaining obligations

The actual pair-activity/independent-target deficit D_(2,1) from main
11.1 still needs its arithmetic proof; the exact incidence summation is now proved.
It is necessary to bound the remaining terms in the incompatible triple
cancellation. The final N^(-3/2+epsilon) incompatible activity estimate
is therefore open. Main 11.3 now has the complete exact third factorial-cumulant/repeated-index
assembly. Its remaining quantitative correction uses the still open
A2 <= N^(-2/3+epsilon) pair profile of main 3.3.
Neither numbered result is marked proved. No deficit or target activity
estimate is introduced as an axiom or used to inflate coverage.
No new external theorem, Paper C source or Palomar submission is used.


## First vanishing numerical triple estimates

A first vanishing estimate for the actual absolute triple activity
and third factorial cumulant is proved under the existing single explicit
field-polynomial BCN input. Set

    g = 1/2 - (2/3)*log(2) > 0.

For every critical-band constantC and epsilon>0, one threshold precedes
allN,L and every actual G contained in the dyadic block. The connected
triple joint mass, full absolute triple activityA3 and absolute third
factorial cumulant are each at mostN^(-g+epsilon). Choosing epsilon=g/2
gives an explicit vanishing power. Zero-marginal sites are included in
the A3 and cumulant bounds; there is no regular-set substitution.

The arithmetic split is exact. For any fixed sourceX, actual aligned
targets have cardinality at most(4D+1)*(L+1)^10, by an injection of each
integer strip into[-R,R] and the actual bounded alignment codes. Thus
the all-pairwise-aligned triple population has cardinality at most
25*|G|*(L+1)^20, uniformly N^(1+epsilon) in the critical band. Its actual
joint mass is at mostN^(-1/2+epsilon) under BCN. Every other connected
triple contains a nonaligned pair. The retained stronger pair-rank
coefficient (2/3)*log2 gives its actual joint cap
N^(-2+(2/3)*log2+epsilon), without compatibility. The connected host
countN^(3/2+epsilon) yields the positive gapg. No dense-triple estimate
is assumed.

For every positive-joint family, the actual compatible-nullity bound
and exact joint formula give |c(I)|<=2^|I|*q(I). Nonzero compatible
triple activity is connected. Every centered coefficient containing
a zero-marginal site is proved zero, by a finite probability argument
that permits zero-weight samples; this gives an exact restriction of
every centered activity sum to the positive-marginal ground set.

The literal independent-target deficit has the coarse numerical bound
D_(2,1)<=N^(-1+epsilon) under BCN. On the positive-marginal ground set,
the actual incompatible triple activity is at mostN^(-1+epsilon),
including both signs. Both A3-K3+ and |kappa3-6K3+| have the same coarse
bound; the first difference is nonnegative. All repeated-index terms
are retained, and their absolute cost is separately at most
N^(-3/2+epsilon). These are consequences of the proved coarse A2
estimate and actual marginal caps, not target-bound hypotheses.

Every displayed estimate has the uniform source quantifier order.
The exponentg is substantially weaker than the source41/30 activity
exponent, and the exponent1 deficit/comparison rate is weaker than
the source3/2. Main11.1,11.2,11.3,14.1 and14.6 remain in progress;
14.1 also lacks its lower bound and optimality. Main13.8 remains
conditional on BCN itself. No numbered completion is added:
coverage77/167 (main28/73, companion49/94), findings87 unchanged.
The existing finding82 is extended only with the analytic probability
consequence of its retained stronger nonaligned rank coefficient.
No new external input, PaperC port, dependency download, manuscript-byte
change or Palomar registration is introduced.

Lean v4.36.0-rc2 full build passed (10731 jobs); actual axiom audit passed for all 6448 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 4165 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records remain intact. Ubuntu available space: 15.62 GiB. Under the existing single explicit BCN input, actual connected triple joint mass, full A3 and absolute third factorial cumulant are at most N^(-g+epsilon), g=1/2-(2/3)log2>0. All-aligned target counting is unconditional; the stronger nonaligned actual probability cap retains the strict rank gap. Zero-marginal centered coefficients vanish exactly, so the full A3 and cumulant include all actual dyadic starts. The literal deficit and positive-ground incompatible/comparison costs have coarse exponent1; repeated-index cost has exponent3/2. Source sharp exponents and optimality remain open; no numbered completion is added. Coverage77/167 (main28/73, companion49/94), confirmed findings87. Finding82 is extended only with its stronger probability consequence. No new external input, PaperC port, dependency download, manuscript-byte change or Palomar registration.


## Improved coarse exponent from actual fixed factorial moments

The actual absolute triple activity and actual third factorial cumulant
now satisfy the stronger coarse half-power estimates under explicit BCN:
for every eta>0, uniformly in every critical L and every G contained in
the dyadic block, eventually

    sum_(I subset G, |I|=3) |c(I)| <= N^(-1/2+eta),
    |kappa_3^factorial(Z_G)| <= N^(-1/2+eta).

These improve the earlier coarse exponent g=1/2-(2/3)*log(2)>0. The sharper
source exponents in main 14.1 and 14.6, and the sharp comparison remainder
in main 11.3, remain open. The new result does not replace those aligned
statements or count them complete.

The proof first uses the newly checked second and third factorial-moment
estimates for the full original count. With its actual mean mu,

    kappa_3 = (F_3-mu^3) - 3*mu*(F_2-mu^2),

and mu is uniformly bounded, so the full third cumulant has the half-power
bound. Next, deleting zero-marginal sites is proved to preserve all actual
joint-mass sums, every factorial moment and this cumulant exactly. A joint
family containing a zero-marginal site has actual mass zero; it is never
divided by a zero probability.

On the positive ground set, the existing actual incompatible-activity and
cumulant comparisons cost at most N^(-1+eta). These compare the full third
cumulant with six times the positive connected activity, and the latter
with the actual absolute triple activity. Exact zero-marginal restriction
recovers the activity on the full dyadic block. Since absolute activity
is a nonnegative sum, restriction to every G costs nothing. Finally the
exact third-cumulant identity, including its actual repeated-index cost
N^(-3/2+eta), gives the same half-power cumulant bound for every G.
All fixed orders and thresholds are assembled before N; heterogeneous
marginals, incompatible families and repeated indices remain explicit.

No new external input or axiom is introduced: BCN is the same ordinary
explicit plane-curve argument. Main 11.3, 14.1 and 14.6 remain in progress.
Coverage stays 77/167 (main 28/73, companion 49/94), confirmed improvements
stay 88. Original manuscript bytes, compiler/dependency pins and the later
Palomar milestone are preserved.

Verified Lean v4.36.0-rc2 full build (10813 jobs), actual Audit.lean kernel audit (6675 declarations; only propext, Classical.choice, Quot.sound), 4392 direct ledger/finding declaration checks, 138 source manifest entries and all 167 original statement hashes. Ubuntu root free space: 15.45 GiB. Exact deletion of zero-marginal sites preserves every actual factorial moment and the third cumulant. Under the existing ordinary explicit BCN premise, full absolute triple activity and the third factorial cumulant are uniformly at most N^(-1/2+eta) for every dyadic subground. All repeated and incompatible costs remain explicit. The sharp source exponents remain open; main 11.3,14.1,14.6 stay in progress. Coverage 77/167; improvements 88.


## All fixed orders: absolute values before summation

The actual absolute centered activity now has a uniform half-power bound
at every fixed positive order under the existing explicit BCN premise.
For every fixed r>=1 and eta>0, every critical L and every G contained in
the dyadic block, eventually

    sum_(I subset G, |I|=r) |c(I)| <= N^(-1/2+eta).

The connected subfamily satisfies the same bound. These are absolute sums
of the actual centered Bochner coefficients, not absolute values of signed
sums or a consequence of scalar factorial-moment cancellation. Zero
marginals and incompatible affine families are included. The order and
all finite lower-order assemblies are fixed before N.

The finite decomposition is unconditional. Nonempty direct families have
zero actual centered coefficient, including their zero-marginal cases.
Expanding the absolute heterogeneous centering transform and separating its
direct and dependent subfamilies gives, with mu=sum_x p_x,

    A_r <= 2^r * productDependentMass_r
           + sum_(s=0..r) jointDependentMass_s * mu^(r-s)/(r-s)!.

Both masses use actual geometric dependence rho>0. In the second mass,
q(A) is the actual joint probability, and the complementary marginals
are their actual heterogeneous products. Exact disjoint-subset incidence
and the previously proved cardinality convolution give this finite bound.
No absolute-activity estimate is a premise.

A new unconditional estimate proves, for every fixed r and eta>0,

    productDependentMass_r <= N^(-1+eta).

Every dependent family contains a primitive seed. A finite seed-cover
inequality preserves its entire nonnegative heterogeneous product weight:
for s-site seeds and total size s+k, completion costs at most
mu^k/k! times the actual seed product mass. Primitive host counts,
the actual local marginal cap, and the actual mean bound give the displayed
product estimate; no BCN or actual joint estimate is used here.

For the full absolute activity, the actual dependent joint masses at the
finitely many orders 0..r are at most N^(-1/2+eta) under BCN. The actual
mean is uniformly bounded, so the finite decomposition yields the claimed
half-power bound after absorbing fixed constants. BCN is the already
inventoried ordinary explicit plane-curve argument.

Companion T14.1 moves from not_started to in_progress. Its sharper connected
4/5 exponent and its separate N^(-1+eta) absolute contact bound are not
claimed. The proof makes no growing-order use of fixed-order estimates.
No numbered result or new mathematical finding is counted complete.
Coverage stays 77/167 (main 28/73, companion 49/94), improvements stay 89.
Original manuscript bytes, compiler/dependency pins and the later Palomar
milestone are preserved; no dependency download or axiom is introduced.
