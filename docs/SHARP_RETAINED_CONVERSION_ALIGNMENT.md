# Conditional completion of companion T17.4

Source: companion_sections/closure.tex:323, the ordinary l1 conversion with the actual regular covariance and nominal second factorial correction.

Companion Lemma T17.4 is now complete CONDITIONALLY under
the same three already recorded finite geometric properties:
chosen-source and ordinary surface covers, and uniform actual
normalized-curve counts. Its entire finite analytic inequality
remains unconditional. The only use of geometry in this
completion is the arithmetic upper bound for the ACTUAL
regular-set covariance parameter at the literal a_N scale.
No desired conversion error or covariance bound is an input.

SecondFactorialCorrection.value is exactly
a_N=E(Z_N)_2-(N*2^(-L))^2, for the full actual dyadic count.
The second factorial moment is the actual Bochner expectation,
not an independent approximation. gap_identity proves
a_N-kappa_2=(E Z_N)^2-lambda_N^2, with the full diagonal
correction retained. The previously proved actual mean-bias
estimate and actual mean caps give, unconditionally,
|a_N-kappa_2|<=N^(-1+epsilon).

SecondFactorialCorrectionLower.uniform_lower proves the
unconditional lower bound a_N>=c_C*L*N^(-2/3), c_C>0.
The actual positive2:3 channel gives a lower bound for beta;
the already proved one-sided full-cumulant comparison gives
2*beta-kappa_2<=N^(-1+epsilon). Together with the actual
mean-square gap this yields the claimed lower bound after
absorbing two N^(-11/12) errors. Thus positivity of the
literal a_N does not rely on the conditional upper profile.
This extends the already recorded unconditional positivity
argument of finding87 to the literal nominal correction.

SharpCovarianceScaleUnderInputs.uniform_absolute_scale
uses the existing actual pair-activity profile with fixed
margin1/15 and the unconditional principal beta upper phase.
The profile remainder N^(-4/5+1/15)=N^(-11/15) is smaller than
L*N^(-2/3). It proves the sharp bound
absolutePairMass(G,L)<=K_C*L*N^(-2/3) for EVERY actual
dyadic subset G, with NO epsilon in this power. The actual
regular covariance sum C_2 is bounded by this absolute mass.
Using the unconditional lower bound for a_N gives
|C_2|<=R_C*a_N. Both the signed covariance definition and
all possibly incompatible pairs remain exact.

SecondFactorialCorrection.regular_mean proves that the
actual regular-set count mean is n*p, n=card(G_N), p=2^(-L).
regular_cumulant proves its actual second factorial cumulant
equals2*C_2-n*p^2. The existing CountVariance identity
identifies that parameter exactly with variance minus mean.
There is no omitted marginal diagonal or change of mean.

SharpRetainedConversionUnderInputs.companion_T17_4 inserts
these actual parameters into the previously proved full
signed-measure conversion. It gives the literal ordinary l1
sum of absolute singleton errors over ALL k>=0:
  ||B_beta-Q(mu,alpha_G)||_1
    <=4*|beta_N-C_2|+K_C*(N^(-2)+a_N/N).
Here B_beta is the actual finite binomial pair reference
embedded as a signed measure, beta_N is the actual joint
mass of retained good edges, C_2 is the actual regular
covariance sum, mu is the actual regular mean, and alpha_G
is its actual variance-minus-mean parameter. Every real
private-prime threshold H is allowed; the beta discrepancy
is kept explicit, so no approximation beta_N=C_2 is assumed.
The exact coefficient4 is retained.

The geometric dimensions are chosen before their explicit
Hypotheses bundle, with chosen-source sizeCap(1/100).
After those supplied properties there is a constant K_C
and one threshold before every N,L and H. Those three
geometric translations themselves remain unformalized;
T17.4 moves from in_progress to conditional, not proved.
Unconditional coverage remains86/167; conditional results
rise from17 to18;131 confirmed improvements remain unchanged.
No new literature input, dependency download, PaperC port,
manuscript-byte edit or Palomar registration is introduced.

The JSON result row records complete validation and the exact proof commit.
