# Exact quadratic law lower inequality

Source: main_sections/quartic_lower.tex:121, main16.2, and main1.1. The full lower inequality is proved under the existing finite geometric inputs; the optimal upper bound is still open.

The lower inequality displayed in main Theorem16.2 and the optimal
quadratic lower clause of main1.1 are now proved for the actual full
original law and exact actual mean/second factorial cumulant:

  ||Law(Z_N)-Q(mu_N,alpha_N)||_1 >=c*N^(-4/3-epsilon), c>0.

This is the ordinary full singleton l1 distance of the actual original
probability measure and the literal quadratic Poisson signed measure.
No retained finite polynomial, formal coefficient norm, truncated law,
assumed norm comparison or positivity of the reference replaces it.
All original heterogeneous marginals and affine incompatibilities are
retained. One finite bundle of the SAME three geometric properties is
chosen before N and before all critical lengths. The already open optimal
triple activity and optimal upper law rate are NOT inputs to this lower
bound. Main16.2 moves from not_started to IN_PROGRESS: its lower inequality
is complete, but its concluding identification of the optimal power also
refers to the still open optimal upper bound. Main1.1 stays in progress.
Neither row is counted complete at this checkpoint.

PositiveQuarticObstructionUnderInputs uses completed main16.1 at the
FIXED margin1/12 and the unconditional actual alpha lower bound
alpha>=d*L*N^(-2/3). Its error is N^(-17/12), smaller than alpha^2 at
power4/3. After a common threshold, the actual coefficient satisfies

  kappa4+3alpha^2 >=2alpha^2 >=d'*L^2*N^(-4/3).

The compatible connected contribution is nonnegative. This inference
uses only the earlier coarse third activity through main16.1; the
still open41/30 triple estimate is unnecessary.

The fourth Charlier polynomial is literal:

  H4(k;mu)=(k)_4-4mu(k)_3+6mu^2(k)_2-4mu^3 k+mu^4.

Its uniform envelope |H4|<=(1+M)^4(1+k)^4 is proved whenever0<=mu<=M,
without a lower positive mean premise. OriginalLawPolynomialMoments
identifies EVERY actual singleton test sum with the finite observation
expectation and original infinite count integral. In particular the
exact H4 sum is kappa4+3alpha^2, including all repeated-index terms.
FourthCharlierReference proves its sum against Q(mu,alpha) is exactly0
for EVERY mu>=0 and real alpha, using genuine convergent factorial
moment sums, not a formal generating function assertion. General shifted
Poisson factorial sums and the quadratic factorial correction are
proved at every fixed order.

PoissonPolynomialMoments gives a positive summable envelope for the
absolute quadratic signed reference, uniformly over0<=mu<=M and|alpha|<=1.
It compares mass(mu,k) with exp(M)*mass(M,k) and controls both genuine
shifted sequences in the second difference. Every polynomially weighted
absolute series is summable and has a uniform finite bound. The actual
mean is uniformly bounded, and the already proved sharp pair bound
makes the actual |alpha|<=1. The earlier bounded fixed ordinary moments
supply the corresponding actual-law bound.

PolynomialTestTruncation proves a general signed-sequence estimate from
a FIXED higher moment, with all summability discharged. If|f(k)|<=K(1+k)^d,
r>=d and R>=1, then

  |sum a_k f(k)| <=K R^d sum|a_k|
                    +(K/R^(r-d))*sum|a_k|(1+k)^r.

Its proof splits the pointwise envelope at1+k=R, before taking the true
convergent infinite sums. It never applies a bounded-test inequality
directly to an unbounded polynomial. FourthCharlierLawDistance applies
this to the literal difference of the actual-law and quadratic-reference
singleton sequences. The unweighted sum is proved equal to the exact
SignedAtomicDistance.distance of those actual signed measures.

For a prescribed epsilon>0, set delta=epsilon/8 and
r=4+ceil((7/3)/delta). This integer is FIXED before N. At R=N^delta,
the weighted tail has power at least7/3 and is absorbed into half the
positive quartic coefficient. The low part costs R^4=N^(epsilon/2).
Dividing gives a positive constant times N^(-4/3-epsilon/2), hence the
stated lower bound with epsilon. The single moment bundle is used at
accuracy1/2, its pair and alpha bundles at sizeCap(1/100), and the quartic
bundle at1/12. All are finite and reduce to the same three explicit
geometric properties; no uniformly bounded growing-order moment is
assumed, and no target law lower bound occurs among the premises.

This checkpoint adds8 modules of actual polynomial sums, reference
moments, a general truncation inequality and the assembled optimal-power
lower inequality. It introduces no further mathematical improvement ID:
the needed removal of the optimal triple premise is already recorded in
P1-MATH-0150. No original source byte, dependency download, Paper C port,
new literature input, hidden axiom or Palomar registration is introduced.
Coverage remains87/167 unconditional and35 conditional, with150 confirmed
improvements. The optimal numerical upper rate and main15.14 final
numerical consequence remain open.

The main16.2 and main1.1 JSON rows record full validation and exact proof commits.
