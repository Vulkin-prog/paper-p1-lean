# Main19.1: actual independent Poisson jumps and Hermite comparison

Source: `p1:cor:compound`. Status: **in progress** for the arithmetic admissibility and count-law rates. Original source bytes are preserved.

The actual probabilistic and analytic reference step of main19.1
is now proved. General jump-Poisson exponentials exp(b*(delta_j-delta_0))
have absolutely convergent series of actual atomic masses. Their
singleton coefficients are proved to be the pushforward of the actual
Poisson masses by n->j*n, for every naturalj including0. They define
actual probability measures for b>=0 and have completion norm exactly1.
The ordinary Poisson exponential consequently has norm exactly1 too.

The general compound reference pi_a*jumpPoisson(j,b) is proved equal
to the actual law of U+jV, where U,V are the coordinate maps on the
actual product of Poisson measures of meansa,b. Both coordinate laws,
their independence, every actual product singleton and the full
pushforward count law are proved. All series products, coefficient
transport, normalization and infinite tails are justified; none is
supplied as an input.

For0<=alpha<=mu, the Hermite reference is the actual probability law
of U+2V with independent meansmu-alpha andalpha/2, including both zero
parameter endpoints. Its completed reference factors exactly as

    H(mu,alpha)=pi_mu*exp((alpha/2)*Delta^2).

The exact source quadratic reference is identified as an actual signed
measure, and absolute Taylor tails give the explicit bound

    ||H(mu,alpha)-Q(mu,alpha)||_1<=4alpha^2 exp(2alpha).

The completed algebra inequality also holds for any realalpha when
mu>=0, with exp(2|alpha|); the probability interpretation requires
the stated nonnegative Poisson means. No small-alpha or upper-mean
assumption is used in this finite comparison. For every actual
probability lawP, a proved finite transfer gives

    TV(P,H)<=||P-Q||_1/2+2alpha^2 exp(2alpha).

No bound for ||P-Q|| is assumed or counted as a count-law approximation.

Actual exponential sums and Bochner integrals are also proved. The
general compound law has mean a+j*b and exponential moment

    exp(a*(exp(t)-1)+b*(exp(j*t)-1))

for every realt. The Hermite law has actual meanmu and exponential
moment exp(mu*(exp(t)-1)+(alpha/2)*(exp(t)-1)^2). Integrability is
proved before using each actual Bochner integral. These properties
concern the constructed reference, not the original run count.

The actual/truncated parameter admissibility at largeN, the numerical
law approximation, and the fixed-height hierarchy rates and leading
equivalents in main19.1 remain open. No matching lower bound for the
exact-parameter Hermite error is asserted. The source row is in
progress and adds no proved numbered coverage. Coverage77/167
(main28/73, companion49/94); confirmed findings remain85.
No new mathematical finding, external input, BCN premise, Paper C
port, dependency download, manuscript-byte change or Palomar
registration is introduced.

## Validation

Lean v4.36.0-rc2 full build passed (10647 jobs); actual axiom audit passed for all 6238 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 3955 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records remain intact. Ubuntu available space: 15.78 GiB. Actual independent Poisson product coordinates, all natural jump sizes, absolutely convergent atomic series, exact coefficient pushforwards and norm-one probability exponentials are proved. The actual Hermite law has meanmu, every real exponential moment, factorization pi_mu*exp(alpha*Delta^2/2), explicit ordinary l1 error4alpha^2 exp(2alpha) and a finite TV transfer for any probability law. Integrability precedes all actual Bochner integrals. Eventual admissibility of model/truncated parameters and the source count-law rates remain open; main19.1 is in progress. Coverage77/167 (main28/73, companion49/94); confirmed findings85. No new finding, external input, BCN premise, Paper C port, dependency download, manuscript-byte change or Palomar registration.

Validated proof checkpoint: [78d568ce8f5c2a2e696d7b27570ed7ec587f6974](https://github.com/Vulkin-prog/paper-p1-lean/commit/78d568ce8f5c2a2e696d7b27570ed7ec587f6974).


## An eventual upper parameter gap under explicit BCN

The literal actual absolute pair mass A2 now has an unconditional finite
host reduction. The exact factor2 from unordered pairs to ordered tuples
is proved. Zero full pair loss forces zero covariance, including every
actual affine compatibility case. An injective tuple-to-host map gives

    2*A2(full)<=#full_loss_hosts*M+actual_host_independent_mass

wheneverM bounds actual joint masses of distinct pairs. The independent
term retains the actual heterogeneous products p_x*p_y. Every smaller
deterministic ground set has no greater absolute pair mass.

Under precisely the same explicit field-polynomial BCN argument already
used for main13.5,13.6,13.8, the checked actual host count N^(1+epsilon)
and actual pair cap N^(-3/2+epsilon) imply, uniformly before every
critical length and every deterministic dyadic subsetG,

    A2(G)<=N^(-1/2+epsilon),
    ||B2(G)-Q(actual_mean,actual_second_cumulant)||_1<=N^(-3/2+epsilon).

These are coarse rates. They do not supply the stronger manuscript
A2=O(N^(-2/3+epsilon)) or the optimal conversion exponent5/3, and they
do not compare the original count law with the retained reference.

The exact second factorial cumulant, including its negative diagonal
term, satisfies |alpha(G)|<=2*A2(G)+sum p_x^2. Its actual diagonal is
bounded byK^2/N using the proved critical marginal cap. The same BCN
argument therefore gives |alpha(G)|<=N^(-1/2+epsilon), and hence a
uniform eventually-small statement with the threshold beforeL andG.
No cumulant or activity bound is supplied as a premise of these rates.

Independently of BCN, the actual full count mean satisfies eventually

    (2^C)^(-1)/2<=mu<=2*2^C.

The lower bound uses the actual regular population, whose size is at
leastN/2, and its actual nominal marginal; the upper bound uses the
proved actual marginal cap. Under BCN this gives |alpha|<=mu/2 and
alpha<mu uniformly in the critical band. Nonnegativity ofalpha is NOT
proved here, so the remaining Hermite admissibility condition remains
open, as do the original and explicit-parameter approximation rates.

Main15.1 and19.1 remain in progress. Neither this weaker conversion nor
a partial parameter gap adds proved numbered coverage. Coverage77/167
(main28/73, companion49/94), confirmed findings86 unchanged. The only
unformalized input is the existing ordinary BCN argument, explicitly
passed at every dependent theorem. The finite host identities and the
mean bounds are unconditional. No new external estimate, PaperC port,
dependency download, manuscript-byte change or Palomar registration.

Lean v4.36.0-rc2 full build passed (10671 jobs); actual axiom audit passed for all 6305 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 4022 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records remain intact. Ubuntu available space: 15.73 GiB. The exact finite2A2 host reduction and unconditional actual two-sided mean bounds are proved. Under the same explicit unformalized BCN argument, actual pair activity and actual second cumulants are at mostN^(-1/2+epsilon), actual conversion is at mostN^(-3/2+epsilon), and the upper parameter gap |alpha|<=mu/2 holds uniformly. No target activity, covariance or cumulant rate is assumed. Positivity ofalpha and the sharper source rates remain open; main15.1 and19.1 are in progress. Coverage77/167 (main28/73, companion49/94); confirmed findings86. No new external input, PaperC port, dependency download, manuscript-byte change or Palomar registration.


## Actual exact-parameter admissibility is discharged

The actual second factorial cumulant is now proved eventually positive
without any unformalized analytic or geometric input. A finite identity
on actual distinct full-loss hosts shows that, for every selected
ordered host populationF,

    alpha>=sum_{(x,y) in F} actual_q_xy-actual_host_independent_mass-sum p_x^2.

The exact ordered/unordered multiplicity2 is proved for arbitrary
weights by a finite tuple/pair bijection. Zero full loss gives zero
actual covariance. Summation on all distinct hosts then gives the
selected-joint lower bound; no sign of a covariance is assumed.

Every private fixed-channel source is proved to be a distinct full-loss
host by its actual normalized-union rank and exact overlap cardinality.
Apply the finite bound to the actual ordered2:3 channel with cutoff6B.
Its already proved positive phase gives c_C*L*N^(-2/3). The actual host
independent mass is at mostN^(-5/6), and the actual marginal diagonal is
at mostK_C^2/N. These errors are absorbed uniformly. Thus, for a positive
constantd_C and one threshold before all critical lengths,

    alpha_N>=d_C*L*N^(-2/3)>0.

This lower bound and positivity are unconditional Lean theorems. They
do not use BCN, the complete pair profile, other channel estimates,
the count-law approximation or the asymptotic equivalent foralpha.
P1-MATH-0087 records this simpler positivity route and its input scope.
It supplies no new sharp exponent or leading equivalent.

The actual mean also has the explicit unconditional bias estimate

    |mu_N-N*2^(-L)|<=2^C*N^(-1+epsilon).

The previously proved actual mean interval m_C<=mu_N<=M_C has
m_C=(2^C)^(-1)/2 andM_C=2*2^C. Under the SAME explicit ordinary BCN
argument as before, the coarse actual cumulant upper bound gives
alpha_N<mu_N and uniform eventual smallness. The actual Hermite
reference with Poisson meansmu_N-alpha_N andalpha_N/2 is therefore
an actual probability law for all sufficiently largeN.

The quadratic reference is also proved to be an actual probability.
A generic sufficient domain derived from its exact integer Charlier
minimum is: if0<m<=mu<=M, alpha>=0 andalpha<=m^2/(M+1), then
Q(mu,alpha) is a probability. All these bounds are discharged for the
actual original-run parameters under the same explicit BCN argument.
No probability status or parameter admissibility is an assumption.

Main1.1 is now in progress for its exact mean-bias clause and its
conditional probability-reference clause. Main3.3 gains the
unconditional positive cumulant lower bound; its full pair profile
and asymptotic equivalents remain open. Main19.1 gains actual
exact-parameter admissibility; its count-law approximation, explicit
fixed-height parameters and optimal hierarchy rates remain open.
All three rows remain in progress. Coverage77/167 (main28/73,
companion49/94), confirmed findings87. No new external mathematical
input, PaperC port, dependency download, source-byte change or
Palomar registration.

Lean v4.36.0-rc2 full build passed (10681 jobs); actual axiom audit passed for all 6330 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 4047 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records remain intact. Ubuntu available space: 15.71 GiB. The actual second cumulant has the unconditional lower bound d_C*L*N^(-2/3)>0, from the actual selected-joint host identity and the private2:3 channel. No BCN, full pair profile, covariance sign or count-law approximation is assumed for this positivity theorem. The actual mean bias has explicit unconditional constant2^C. Actual quadratic and Hermite probability status is proved uniformly under the same existing explicit BCN input for the coarse upper bound. Sharp pair and law rates and explicit fixed-height parameters remain open; main1.1,3.3,19.1 are in progress. Coverage77/167 (main28/73, companion49/94); confirmed findings87. No new external input, PaperC port, dependency download, manuscript-byte change or Palomar registration.


## Every fixed-height explicit Hermite parameter is admissible unconditionally

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


## Explicit Hermite comparison at N^(-4/3+epsilon)

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


## Adjacent Hermite references have the same leading distance

The actual distances between adjacent explicit references now have
their exact coefficient and uniform moving-phase equivalents, without
BCN, an actual-cumulant comparison or any count-law error input.
For every nonnegative common meanmu and arbitrary realalpha,beta,

    ||Q(mu,alpha)-Q(mu,beta)||_1
      = |alpha-beta|/2 * ||Pi_mu*Delta^2||_1.

This is the ordinary sum of absolute singleton masses of actual signed
measures. When the two references are probabilities, their actual
total variation is exactly |alpha-beta|/4 times the same norm.
All coefficients, infinite sums and the factor2 between l1 andTV
are proved, including the zero-mean endpoint of the signed identity.

The exact coefficient increment from heighth to h+1 is the literal
heightMass_(h+1), with no asymptotic substitution. Therefore the
ordinary adjacent-reference distance is exactly

    |heightMass_(h+1)|/2 * ||Pi_lambda*Delta^2||_1.

For each fixedh>=3, define the positive moving leading term

    E_h = phaseMass_(h+1)/2 * ||Pi_lambda*Delta^2||_1.

For everyepsilon>0, one threshold precedes allN,L in the critical band
and |gap_h/E_h-1|<=epsilon. The phase includes the actual residue and
nominal mean, and the Poisson norm is evaluated at that same moving
mean. Its positivity follows from the proved lower bound
||Pi_lambda*Delta^2||_1>=2exp(-lambda). Actual probability witnesses
for the two adjacent quadratic references have TV gap_h/2, hence
the full equivalent E_h/2=phaseMass_(h+1)*norm/4.

Adjacent literal Hermite probabilities have the SAME uniform leading
total-variation equivalent E_h/2. A proved four-law metric stability
inequality bounds the change of the pair distance by the sum of the
two quadratic/Hermite comparison costs. Their checked error is
negligible on E_h: a positive lower bound d_C,h/N for E_h/2 follows
from the phase lower bound and the compact nominal-mean bound.
The comparison uses actual probability witnesses and ordinary signed
singleton errors, not formal generating functions as distributions.

These statements compare two constructed references. They do not
prove a leading distance from the original count to either reference,
a count-law remainder, an actual-cumulant remainder or optimality.
Those parts of main18.1,18.3,19.1 remain open and all three rows stay
in progress. No numbered completion is added: coverage77/167
(main28/73, companion49/94), findings87 unchanged. No new mathematical
finding, external input, BCN premise, PaperC port, dependency download,
manuscript-byte change or Palomar registration is introduced.
