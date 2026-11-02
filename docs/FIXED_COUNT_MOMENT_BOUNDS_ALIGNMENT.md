# Actual fixed-order dependent mass and bounded count moments

Sources: main 6.3, the bounded-moment clause of main 6.4, and moment transfer in main 3.1. The sharp expansion in main 6.4 is **in progress**.

Actual fixed-order dependent-family mass is now bounded under the existing
explicit BCN premise. For every fixed r and eta>0, uniformly for critical L
and every G contained in the dyadic block,

    sum_(I subset G, |I|=r, rho(I)>0) P(all starts in I active)
       <= N^(-1/2+eta)

for all sufficiently large N. The argument does not assume this bound.
Every dependent I contains a primitive seed D of size between 2 and r.
Canonical injective enumerations transport actual unordered families to the
already proved ordered-tuple propagation theorem, with an explicit r! position
factor. Their joint masses are exactly those of the original infinite measure.
The zero masses of incompatible seeds are retained; no regularity or positivity
restriction is imposed. A finite cover over all seed sizes is taken before N.

More generally, every actual family of size s+k containing a seed from a
finite s-site seed family F has joint mass at most

    (s+k)! * N^eta * sum_(D in F) P(all starts in D active).

This propagation statement is unconditional and keeps the full actual seed
mass. BCN is used only for the primitive two-site mass needed in the final
coarse dependent-family estimate.

An unconditional finite decomposition then proves, with the exact
heterogeneous mean mu=sum_x p_x,

    E(Z_G)_r <= mu^r + r! * dependentJointMass(G,L,r).

The direct families have exactly their actual product marginals, and the
nonnegative elementary-symmetric inequality bounds their total. Under BCN,
for every fixed r and eta>0 this gives

    E(Z_G)_r <= mu^r + N^(-1/2+eta).

The critical mean is uniformly bounded. Hence every fixed factorial moment
and every fixed ordinary moment of the original count is uniformly bounded.
The passage to ordinary moments uses the checked finite integer inequality

    n^r <= (2*r)^r + 2^r * n.descFactorial(r),

including r=0. No moment hypothesis, Poisson-law approximation, small coupling
error, or large-order estimate is used to deduce these bounded moments.
The already proved regular-count transfer now has its higher-moment premise
discharged under BCN, yielding, for every fixed j>=1,

    |E Z_N^j - E Z_regular^j| <= K * N^(-1+eta).

Main 6.4 moves from not_started to in_progress: its bounded-moment clause is
proved under explicit BCN, but its two-sided factorial/ordinary expansions,
quadratic correction, sharp 4/5 remainder and all higher factorial cumulants
are not asserted. Main 3.1 retains its previously proved aligned scope;
the new moment-transfer consequence is conditional only on BCN. Numbered
coverage remains 77/167 (main 28/73, companion 49/94), confirmed improvements
remain 88. No new external input, axiom, dependency download, source-byte
change, or Palomar registration is introduced.

Verified Lean v4.36.0-rc2 full build (10789 jobs), actual Audit.lean kernel audit (6636 declarations; only propext, Classical.choice, Quot.sound), 4353 direct ledger/finding declaration checks, 138 source manifest entries and all 167 original statement hashes. Ubuntu root free space: 15.49 GiB. Unordered actual seed propagation is unconditional; fixed dependent-mass and original moment bounds use only the existing ordinary explicit BCN premise. All moment orders and finite seed-size covers are fixed before N. Main 6.4 is in progress: bounded original moments are proved under BCN, but no full sharp moment expansion is claimed. Coverage 77/167 (main 28/73, companion 49/94); confirmed improvements 88.


## Unconditional lower branch and two-sided factorial convergence under BCN

Every fixed actual factorial moment now has a two-sided coarse estimate.
For the original full dyadic count, with its exact actual mean mu_N,
for every fixed r>=0 and eta>0, under the existing explicit BCN premise,

    |E(Z_N)_r - mu_N^r| <= N^(-1/2+eta)

eventually, uniformly for every critical length L in the fixed band. The
same estimate holds with the nominal mean lambda_N. These are actual
Bochner factorial moments of the original infinite prime-sign count.
No target moment expansion is assumed.

The new lower branch is unconditional. Exact deletion and insertion of a
marked coordinate give the finite identity

    sum_(distinct (r+1)-tuples) q(tuple)
      = sum_(distinct r-tuples t) sum_(z not in t) q(t union {z}).

For positive source mass, the inner sum is exactly that source mass times
its actual fresh conditional mean. Zero source masses are handled directly
by nonnegativity; no incompatible family is divided by its zero mass.
The previously checked negative conditional-deviation bound therefore gives

    E(Z_N)_r >= max(0,lambda_N-N^(-1/2+eta))^r

for every fixed r, without BCN. A bounded nonnegative power-difference
inequality yields lambda_N^r-E(Z_N)_r<=N^(-1/2+eta), still unconditionally.
All source cardinalities used in this induction are bounded by fixed r
before the final scale N is chosen.

The existing BCN-dependent upper bound uses the actual heterogeneous mean
and actual dependent-family mass. The exact mean bias estimate also gives,
unconditionally at every fixed r,

    |mu_N^r-lambda_N^r| <= N^(-1+eta).

Combining these checked branches proves the displayed two-sided estimates.
This is a first factorial-moment convergence result and is weaker than the
source quadratic expansion: the correction binom(r,2)*mu_N^(r-2)*alpha_N,
the source 4/5 error, ordinary-moment expansion and higher-cumulant estimate
remain open. It is not asserted to be an original-law total-variation or
Poisson approximation theorem. Main 6.4 remains in progress. Coverage stays
77/167 (main 28/73, companion 49/94), confirmed improvements stay 88.
The external BCN input is an ordinary explicit argument; no axiom, new
literature input, dependency download, source-byte change or Palomar
registration is introduced.

Verified Lean v4.36.0-rc2 full build (10799 jobs), actual Audit.lean kernel audit (6648 declarations; only propext, Classical.choice, Quot.sound), 4365 direct ledger/finding declaration checks, 138 source manifest entries and all 167 original statement hashes. Ubuntu root free space: 15.48 GiB. The actual fresh-tuple recurrence, lower factorial branch and power mean-bias estimate are unconditional. Two-sided actual and nominal fixed factorial-moment errors N^(-1/2+eta) use the existing ordinary explicit BCN premise. Orders and all bounded-order assemblies are fixed before N. No sharp quadratic expansion or original-law TV theorem is claimed. Main 6.4 remains in progress. Coverage 77/167; confirmed improvements 88.


## From finitely many fixed factorial moments to actual law convergence

The actual original count law now has a uniform qualitative Poisson
approximation, conditional on the existing explicit BCN plane-curve bound.
For every fixed critical-band width C and every tolerance epsilon>0 there
is one threshold N0 such that, for every N>=N0 and every critical length L,

    TV(Law(Z_N),Pois(mu_N)) <= epsilon,
    TV(Law(Z_N),Pois(lambda_N)) <= epsilon.

Here mu_N is the exact actual mean and lambda_N is the nominal mean. Both
Poisson references are actual normalized probability measures with singleton
masses exp(-mu)*mu^k/k!. Their parameters remain those of the current N,L;
no frozen limiting phase, fixed limiting mean, or convergence of the means
is assumed. Law(Z_N) is the actual pushforward law of the original infinite
prime-sign count, not a retained polynomial treated as a probability law.

The reconstruction argument is finite and unconditional before the arithmetic
moment estimates are inserted. For any finite Boolean family, write F_r for
its actual factorial moment and Delta=delta_1-delta_0. Its count law differs
from the finite polynomial sum_(r<k) F_r*Delta^r/r! in ordinary l1 by at most

    2^k * F_k / k!.

This follows from the already proved first-excluded-prefix expansion with
the hereditary cutoff |I|<k. Every boundary set has exactly k sites; its
suffix kernel stays positive and costs exactly its actual mass. Grouping
by cardinality identifies all coefficients with the actual factorial
moments. Comparing two such polynomials costs at most

    sum_(r<k) (2^r/r!) * |F_r-G_r|.

A new finite Banach-algebra estimate retains the factorial denominator:

    ||exp(x)-sum_(r<k) x^r/r!||
       <= ||x||^k * exp(||x||) / k!.

It is proved from the actual exponential series and the divisibility of
j!*k! into (j+k)!, not assumed as an interface. Applied in the completed
ordinary-l1 convolution algebra to x=mu*Delta, it bounds the Poisson
remainder by (2*mu)^k*exp(2*mu)/k!. Singleton coefficient comparison
transports the completed-norm bound to actual total variation. Universal
Poisson parameter stability TV(Pois(mu),Pois(nu))<=|mu-nu| is proved too.

For the actual original count, mu_N is uniformly bounded by M=2*2^C.
Choose the finite reconstruction order k AFTER epsilon, so that the
factorial tails for this fixed M are small. Only then assemble the
finitely many fixed-order moment estimates and choose N0. The original
moment of order k is bounded by mu_N^k+1, and the finite polynomial error
tends to zero by the checked fixed-order factorial estimates. The
convergent exponential series makes the reconstruction tails vanish.
No growing-order moment bound or target law approximation is a premise.

This proves leading Poisson approximation but not a quantitative TV rate,
the source optimal quadratic correction, its 4/3 remainder, or the exact
TV scale in main 1.2. Main 1.1 and 6.4 remain in progress; main 1.2 is not
counted complete. Numbered coverage remains 77/167 (main 28/73, companion
49/94); confirmed mathematical improvements remain 88. BCN is the same
ordinary explicit theorem argument already inventoried. No new external
input, axiom, dependency download, manuscript-byte change or Palomar
registration is introduced.


## Fourth actual factorial cumulant with every repeated-index term

The complete finite fourth-factorial-cumulant identity in the proof of
main 16.1 is now checked for the actual heterogeneous original count.
Writing C2=sum_(|e|=2)c(e), it is exactly

    kappa4 = 24*sum_(|I|=4)c(I) - 12*C2^2
             -24*sum_(|T|=3)c(T)*sum_(x in T)p_x
             +24*sum_(e={i,j})(p_i^2+p_i*p_j+p_j^2)*c(e)
             -6*sum_x p_x^4.

Every repeated-index term and every actual marginal is retained. The empty
ground set, zero marginals and incompatible families are included. Removing
all zero-marginal sites is proved to preserve this actual cumulant exactly.
No independent-indicator, regularity, positivity or arithmetic hypothesis is
needed for the finite identity, and no analytic logarithm is used.

The algebraic proof is stronger in scope: it works in any commutative ring
for coherent joint and centered data q,c with c(empty)=1, zero singleton
coefficients and the finite uncentering identity. An exact incidence
bijection between a set with a marked subset and two disjoint subsets gives
the full all-order cardinality convolution. Its order-2,3,4 specializations,
the two-site deletion formulas and the independent quartic identity supply
the displayed formula. For the actual model, the coherence hypothesis is
discharged by the already proved exact infinite uncentering expansion.
It is not an assumed cumulant formula or asymptotic bound.

This weaker algebraic setting is recorded as confirmed improvement
P1-MATH-0089. It applies to the finite displayed identity in the proof of
main 16.1, not to the source arithmetic estimates that follow it.
The original manuscript bytes are preserved for later integration.

A separate first vanishing bound under the existing explicit BCN premise
is proved for the actual full original count:

    |kappa4(Z_N)| <= N^(-1/2+eta)

at every fixed critical-band width and eta>0. With F_r the actual factorial
moments, mu the actual mean and d_r=F_r-mu^r, the checked decomposition is
kappa4=d_4-4*mu*d_3+6*mu^2*d_2-3*d_2^2. The fixed moment estimates and
bounded mean prove the bound, with a small fixed exponent selected before N.
This does not assume a fourth-cumulant estimate.

The source comparisons kappa4=24*K4+O(N^(-3/2+eta)),
K4=K4_positive+O(N^(-3/2+eta)), and their positive quartic consequence
remain open. Main 16.1 therefore moves from not_started to in_progress;
main 6.4 remains in progress. No numbered result is counted complete.
Coverage stays 77/167 (main 28/73, companion 49/94); confirmed improvements
increase from 88 to 89. No new external input, axiom, dependency download,
source-byte change or Palomar registration is introduced.


## A weaker bound needs no BCN

Every fixed nonnegative order now has an unconditional subpower bound
on the actual original model. For every fixed r>=0 and epsilon>0,

    sum_(I subset G, |I|=r)q(I) <= N^epsilon,
    E[(Z_G)_r] <= N^epsilon,
    E[Z_G^r] <= N^epsilon,

eventually uniformly over all critical lengths and every dyadic subground.
No BCN premise is used. The order, exponent and threshold are fixed before N.
For r>=1, every r-site family contains a singleton seed. The checked
unordered positive propagation bound and bounded exact actual mean give
the first estimate, with its factorial coefficient absorbed only afterward.
The exact factorial-moment subset formula gives the second. The elementary
pointwise comparison n^r<=(2r)^r+2^r*(n)_r gives the third. Order zero is
included explicitly. Irregular windows and zero marginals remain present.

These are weaker than uniform boundedness or convergence to the Poisson
factorial moments; the stronger existing boundedness/convergence theorems
remain conditional on their already explicit BCN premise. The new
unconditional subpower bounds can be used in fixed-order truncation and
contact estimates without assuming the source full fixed-moment asymptotic.
Main 6.4 remains in progress. Coverage stays 77/167 (main 28/73, companion
49/94), improvements stay 90. No new external input, axiom, dependency
download, source-byte change or Palomar registration is introduced.

Verified Lean v4.36.0-rc2 full build (10915 jobs), actual Audit.lean kernel audit (6841 declarations; only propext, Classical.choice, Quot.sound), 4558 direct ledger/finding declaration checks, 138 source manifest entries and all 167 original statement hashes. Ubuntu root free space: 15.28 GiB. Actual joint subset masses, factorial and ordinary moments are at most N^epsilon at every fixed nonnegative order, unconditionally and uniformly over all dyadic subgrounds. The proof uses positive singleton-seed propagation and the bounded actual mean, not BCN or assumed moment bounds. This does not claim uniform boundedness or the complete source asymptotic. Main 6.4 stays in progress; coverage 77/167, improvements 90.
