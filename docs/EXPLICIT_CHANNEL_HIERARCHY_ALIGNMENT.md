# Explicit finite-height references: main1.4,18.1,18.3 and19.1

Original manuscript bytes are preserved. All four numbered rows remain in progress.

The literal finite-height channel coefficients are now defined with the
source reduced interior numerators b/2<a<b, gcd(a,b)=1, heights3<=b<=h,
and the exact rational weight2*(2a-b)/(ab). The index is(heightb,numeratora).
The finite signed polynomial S_{a,b}(L) is the already checked integer
source sum, including its empty-sum convention. Exact finite grouping
proves the literal source coefficient

    alphaHat_h=lambda^2/N*sum_{b=3..h} sum_a w_ab*S_ab(L).

For every fixedh>=3 and bandC, one threshold precedes allN,L. The actual
finite coefficient satisfies positive two-sided bounds

    d_C*L*N^(-2/3)<=alphaHat_h<=K_(C,h)*L*N^(-2/3),
    alphaHat_h<=N^(-2/3+epsilon) for everyepsilon>0.

Every summand is proved nonnegative in that range, and the included2:3
channel gives the positive lower bound. No pair-profile theorem,
cumulant comparison, BCN or count-law approximation is an input.
The threshold and upper constant may depend onh; no growing-height
uniformity is asserted. A uniform eventually-small statement is proved.

The nominal mean has its exact critical bounds
(2^C)^(-1)<=lambda<=2^C. The generic Charlier sufficient domain and the
actual independent-Poisson construction then prove, UNCONDITIONALLY,
for every fixedh>=3 and all sufficiently largeN in the critical band,

    0<alphaHat_h<lambda,
    Q(lambda,alphaHat_h) is an actual probability,
    H(lambda,alphaHat_h) is an actual probability.

These are the literal source parameters. No parameter positivity,
probability property, comparisonalphaHat_h~alpha or target estimate is
assumed. The height4 coefficient is proved exactly equal to
lambda^2/(3N)*(S_23+S_34). Its actual quadratic singleton masses have
exactly the displayed formula in main1.4, includingk=0,1. The mass
formula itself is a signed-measure identity for everyN>0; probability
status is the eventual statement, not a small-N assertion.

The moving-phase constant c_b(r) is also defined literally. Its finite
sum is strictly positive for everyb>=3, becausea=b-1 is a reduced
interior numerator and every summand is positive. The first constants
are checked exactly:

    c3(r)=(r+2)/(18*2^(r/3)), c4(r)=(r+3)/(24*2^(r/4)),
    c5(r)=17*(r+4)/(300*2^(r/5)), c6(r)=(r+5)/(45*2^(r/6)).

The generic height increment is proved. The height5 increment is the
sourceM5=lambda^2/N*((2/15)*S_35+(3/10)*S_45). ForL=5q+r, q>=1,r<5,
its exact displayed closed polynomial, with coefficients17,13,87,620,
113,127, is checked from the two signed integer channel identities.
No asymptotic equivalent for a distance is inferred from these finite
phase and polynomial identities.

Main1.4,18.1,18.3 are now in progress for their exact finite algebra
and probability-reference clauses. Their count-law and cumulant
remainder estimates, sharp distances, equivalents and optimality are
still open. Main19.1 gains unconditional probability status for every
literal fixed-height explicit Hermite reference; its distance rates
remain open. Finding87 is extended to record this second, entirely
finite route to reference admissibility, without comparison to the
actual cumulant. Coverage77/167 (main28/73, companion49/94), findings87.
No new external mathematical input, BCN argument, PaperC port,
dependency download, manuscript-byte change or Palomar registration.

Lean v4.36.0-rc2 full build passed (10691 jobs); actual axiom audit passed for all 6374 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 4091 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records remain intact. Ubuntu available space: 15.69 GiB. Every literal fixed-height coefficient has direct unconditional positive vanishing bounds, and its actual quadratic and Hermite references are probabilities without BCN, actual-cumulant comparison or count-law approximation. Exact height4 parameters and masses, c_b positivity, phases at heights3..6, generic height increments and the exact height5 polynomial are checked. Sharp count-law and cumulant remainders, distances, equivalents and optimality remain open; main1.4,18.1,18.3,19.1 stay in progress. Coverage77/167 (main28/73, companion49/94); confirmed findings87. Finding87 is extended to the direct explicit-parameter route. No new external input, BCN premise, PaperC port, dependency download, manuscript-byte change or Palomar registration.


## The finite omitted-height term has its full uniform leading equivalent

The literal finite height contribution now has its complete uniform
leading phase equivalent. For each fixed heightb>=3 and bandC, with
r=L modb andlambda=N*2^(-L), put

    heightMass_b=lambda^2/N*T_b(L),
    phaseMass_b=c_b(r)*lambda^(2-1/b)*L*N^(-1+1/b).

For everyepsilon>0, a threshold precedes allN,L in the critical band:
phaseMass_b>0 and

    |heightMass_b/phaseMass_b-1|<=epsilon,
    |heightMass_b-phaseMass_b|<=epsilon*phaseMass_b.

The moving residue and moving nominal mean are retained. No restriction
to a fixed phase subsequence is imposed. The heightb is fixed before
the threshold; no growing-height uniformity is asserted.

The original integer signed sum has an exact normalized Euclidean
formula atL=bq+r. Division byq*2^q leaves its positive leading
coefficient and only inverse-q and geometric terms. Their actual
limits prove each residue limit for the finite height sum. The actual
finite residue set is then assembled into one common threshold,
followed by Euclidean division for every sufficiently largeL. Critical
window geometry transports that common length threshold to the source
quantifier order beforeN,L.

The conversion to the source N,lambda expression is an exact real-power
identity, usingN/lambda=2^L. The positive nominal prefactor cancels;
it is not frozen or replaced by a constant. All fixed-residue limits,
finite sums, nonzero denominators, positivity and uniform assembly are
proved, not supplied as premises.

This proves the leading equivalent of the finite omitted-height term
appearing in the proof of main18.1, including the finite height5 and
height6 phases used in18.3. It does NOT prove the actual-cumulant
remainder, the count-law remainder, a total-variation equivalent or
optimality. The complete actual pair profile in3.3 remains open too.
All three numbered rows stay in progress. Coverage77/167
(main28/73, companion49/94), confirmed findings87 unchanged.
No new mathematical finding, external estimate, BCN input, PaperC
port, dependency download, source-byte change or Palomar registration.

Lean v4.36.0-rc2 full build passed (10697 jobs); actual axiom audit passed for all 6393 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 4110 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records remain intact. Ubuntu available space: 15.68 GiB. The literal finite height contribution has the full uniform source leading phase equivalent, with moving residue and nominal mean. Exact normalized integer identities, reciprocal/geometric limits, actual finite residue assembly and real-power transport are checked. No fixed-residue subsequence or frozen nominal mean is used in the final theorem. Actual pair-profile, cumulant and law remainders, distance equivalents and optimality remain open; main3.3,18.1,18.3 are in progress. Coverage77/167 (main28/73, companion49/94); confirmed findings87. No new mathematical finding, external estimate, BCN input, PaperC port, dependency download, manuscript-byte change or Palomar registration.


## The Hermite reference change is negligible on the omitted-height phase

The comparison of every literal fixed-height explicit Hermite reference
with its quadratic reference is now proved at the full source analytic
error scale, without any unformalized input. For each fixedh>=3, bandC
and everyepsilon>0, one threshold precedes allN,L and

    ||Q(lambda,alphaHat_h)-H(lambda,alphaHat_h)||_1<=N^(-4/3+epsilon).

The norm is the ordinary infinite sum of actual signed singleton
masses. The completed-algebra norm is only a proved majorant; it is
not substituted for the ordinary measure norm. Every coefficient and
both actual signed measures are identified exactly. The finite bound
4*alpha^2*exp(2*|alpha|), the proved literal coefficient rate and
uniform smallness give the displayed numerical rate. No comparison
with the exact cumulant, BCN or count-law error is assumed.

Actual total variation on the naturals now has checked triangle and
reference-stability inequalities. The signed-measure distance is
identified with exactly2*TV. Actual probability witnesses for the
literal Q andH references therefore satisfy, uniformly for EVERY
actual probability lawP on the naturals,

    |TV(P,Q)-TV(P,H)|<=N^(-4/3+epsilon)/2.

The witnesses and common threshold do not depend onP. In particular
this comparison is available for the actual run-count law, without
asserting either distance is already small.

The actual scalar phase of every omitted heightb>=3 also has a
positive uniform lower bound d_(C,b)*L*N^(-1+1/b), and hence d_(C,b)/N.
It follows that for everyepsilon>0 and fixedh>=3, eventually uniformly
in the critical band and for everyP,

    |TV(P,Q_h)-TV(P,H_h)|<=epsilon*phaseMass_(h+1).

The positive omitted-height phase retains the actual moving residue
and nominal mean. Its lower bound uses the included numeratorb-1,
the actual finite main terms and the previously proved uniform phase
equivalent. The final comparison proves negligibility on this scalar
phase without assuming a leading distance equivalent for either law.

These results complete the explicit-reference analytic comparison in
the proof of main19.1. Its original run-count approximation, the
quadratic hierarchy remainder and leading distance/optimality claims
remain open; the exact-parameter Hermite rate remains open too.
Main19.1 stays in progress, as do main18.1 and18.3. No numbered result
is added: coverage77/167 (main28/73, companion49/94), findings87.
No new mathematical finding, external estimate, BCN argument, PaperC
port, dependency download, manuscript-byte change or Palomar registration.

Lean v4.36.0-rc2 full build passed (10707 jobs); actual axiom audit passed for all 6406 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 4123 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records remain intact. Ubuntu available space: 15.66 GiB. Actual signed explicit quadratic/Hermite error is at mostN^(-4/3+epsilon), unconditionally for every fixed height. Actual probability witnesses have distance-to-P changes bounded by half that error for every probability lawP, with P after the common threshold. The change is negligible on the actual moving first-omitted-height scalar phase, whose positive lower bound is proved. Original-count approximation, distance equivalents and optimality remain open; main18.1,18.3,19.1 remain in progress. Coverage77/167 (main28/73, companion49/94); confirmed findings87. No new mathematical finding, external input, BCN premise, PaperC port, dependency download, manuscript-byte change or Palomar registration.


## Uniform mean-change negligibility at every fixed omitted height

The finite analytic mean-change step used in main1.4 and the fixed-height
hierarchy is now checked for actual signed measures. For nonnegative
meansmu,nu and arbitrary realalpha,beta,

    ||Pi_mu-Pi_nu||_1 <= 2*|mu-nu|,
    ||Q(mu,alpha)-Q(nu,beta)||_1
      <= 2*(1+2*|alpha|)*|mu-nu| + 2*|alpha-beta|.

The same bounds hold first in the completed convolution algebra and
are transported coefficient by coefficient to the ordinary infinite
sum of absolute singleton masses. The Poisson estimate uses its
actual nonnegative series, the explicit bound
||Pi_t-delta_0||<=2*(1-exp(-t))<=2t and the norm-one convolution
semigroup. It needs neither a mean cap nor an exponential loss.
No reference probability or infinite-tail estimate is assumed.

For each fixed coefficient boundA>=0 and epsilon>0, one threshold
precedes everyN,L in the critical band and every |alpha|<=A. Holding
alpha fixed, changing the actual original count mean toN*2^(-L)
costs at mostN^(-1+epsilon). This uses the already proved actual mean
bias estimate and is unconditional. At every sufficiently large scale
where the literal integer mean bias is nonzero, the same signed
reference distance is at leastc_C/N for everyalpha>=-1, with

    c_C = exp(-2*2^C)/(2*2^C) > 0.

Both signs of the mean bias are included. This is a scale-by-scale
conditional lower bound, not an assertion that nonzero biases occur
infinitely often. The coefficient is held fixed in this lower bound;
no lower bound for simultaneous arbitrary parameter changes is claimed.
The true count-law distance in main17.3 remains open.

For every fixed heightb>=3 and epsilon>0, the exact-to-nominal mean
change is at mostepsilon times the actual moving scalar phase at
heightb, uniformly for every boundedalpha. The proof uses the full
positive phase lower boundd*L*N^(-1+1/b) and chooses a mean-bias loss
strictly smaller than1/b. A weaker d/N phase lower bound would not
suffice for this step. Neither the residue nor the nominal mean is
frozen along a subsequence.

For each literal finite channel coefficientalphaHat_h, h>=3, both
Q(actualMean,alphaHat_h) and the corresponding actual Hermite law
are eventually probabilities without BCN or a pair-profile input.
Positive actual mean bounds and direct smallness/positivity of the
finite channel sum establish admissibility. There are actual
probability witnesses for Q(actualMean,alphaHat_h) and
Q(nominalMean,alphaHat_h) whose distances to EVERY probability lawP
differ by at mostepsilon times phaseMass_(h+1). The threshold and
witnesses precedeP, and both references retain the same literal
finite coefficient. No count-law approximation or leading distance
equivalent is assumed or established.

These results complete the analytic mean-replacement step of main1.4
and18.1. Their original count-law and cumulant remainders, leading
distance equivalents and optimality remain open. Main17.3 remains
in progress for its true-law conclusions. No numbered completion is
added: coverage77/167 (main28/73, companion49/94), findings87 unchanged.
Finding85 is extended with its explicit actual-reference quantum.
No new external input, BCN premise, PaperC port, dependency download,
manuscript-byte change or Palomar registration is introduced.
