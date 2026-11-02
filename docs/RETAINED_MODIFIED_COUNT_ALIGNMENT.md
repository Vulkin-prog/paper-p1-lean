# Actual retained-configuration modified count

Sources: companionT15.2 andT19.3. Status: **in progress** for the arithmetic bad-event estimate and identification with the source seed-union event.

An actual modified count is now constructed by retaining exactly the
active configurations in the geometric first retained class and setting
the count to zero otherwise. Its bad event is the literal measurable
complement of that retained-active class. Write its actual probability
asdelta. No smallness or numerical estimate fordelta is an input.

The deterministic step is proved in the actual effective spaces.
For a compressed pair e inI, deleting either endpoint ofe leaves
relative nullity zero. Hence every retainedI has a direct subfamilyD
with |I|<=|D|+1. Applied to the actual active set, this gives

    modifiedCount <= R+1,

whereR is the previously constructed actual largest direct active
subfamily. Outside the bad event, the count is the original count.
ForN>=2, every active subfamily there has actual relative nullity
at mostL/3+1, by the checked good-pair bound and retained heredity.
This proves the finite geometric retained-class part ofT15.2.
It does not estimate the probability of the union of arithmetic
seed obstructions used in the source proof.

The modified variable and the bad event are realized exactly through
one explicit finite prime cylinder. Its natural observation law is
an actual probability measure, identified with the measurable
pushforward of the original infinite measure. Every real observable
is integrable, and its actual law integral agrees with the original
Bochner integral and finite probability sum. The original count law
is constructed and identified with its own actual pushforward too.
These are probability measures with proved normalization, rather than
signed expansions treated as probabilities.

The original and modified variables disagree exactly on the bad
event. The finite coupling is transported to their actual probability
laws, proving

    TV(Law(originalCount),Law(modifiedCount)) <= delta.

Withmu=sum of the actual local marginals, the modified count has,
for everyk>=1,r>=1 ands>=1,

    P(modifiedCount>=k) <= mu^(k-1)/(k-1)!,
    E(modifiedCount)_r <= mu^r+r*mu^(r-1),
    E s^modifiedCount <= s*product_(x inG)(1+(s-1)*p_x)
                       <= s*exp((s-1)*mu).

The original count satisfies the same tail bound with+delta.
All these are finite all-order statements on every actual finiteG,
including irregular and zero-marginal windows, and require onlyL>0.
Their proof uses actual pointwise domination, integrable Bochner
monotonicity and event inclusion; no target moment or probability
bound is assumed. On a regular ground set the exact binomial factor
s*(1+p*(s-1))^|G| andmu=|G|p are recovered. A single checked theorem
packages all five source inequalities with the literaldelta.

The still-open arithmetic core estimates must supply
delta=O(N^(-4/5+epsilon)) and the comparison with the source's specified
seed-union event. No such rate or identification is inferred from
this finite construction. ThusT15.2 moves to in_progress andT19.3
stays in_progress; neither is counted complete. Finding88 is extended
with the actual heterogeneous retained-modified construction.
Coverage77/167 (main28/73, companion49/94), findings88 unchanged.
No new external input, BCN premise, PaperC port, dependency download,
manuscript-byte change or Palomar registration is introduced.

Lean v4.36.0-rc2 full build passed (10771 jobs); actual axiom audit passed for all 6598 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 4315 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records remain intact. Ubuntu available space: 15.54 GiB. Deleting a compressed-pair endpoint gives a direct subfamily, proving actual retained-active count domination byR+1. Outside the literal measurable bad event, every active subfamily has nullity<=L/3+1 forN>=2. The zeroed retained-count law and the original law are actual probability pushforwards of the original infinite signs; every observable is integrable and all finite-cylinder and law integrals agree. Exact disagreement is the bad event, giving actual TV coupling<=delta. All-order heterogeneous modified factorial/tail/product-exponential bounds, the original tail with+delta and all five regular-setT19.3 inequalities are proved. The source arithmetic estimate fordelta and identification with its seed-union event remain open; T15.2,T19.3 are in progress. Finding88 is extended; coverage77/167 (main28/73, companion49/94), confirmed improvements88. No new external input, BCN premise, PaperC port, dependency download, manuscript-byte change or Palomar registration.


## Uniform vanishing of the literal error under BCN

The actual retained-modification error now converges uniformly to zero,
conditional on the existing explicit BCN plane-curve bound. For every fixed
critical-band width C and tolerance epsilon>0, there is a threshold N0 such that,
for every N>=N0, every critical L, every G contained in the dyadic block and
every real H,

    delta(H,N,L,G) <= epsilon,
    TV(Law(originalCount),Law(retainedModifiedCount)) <= epsilon.

Here delta is the literal probability that the actual active configuration is
not retained. No estimate for delta or convergence assertion is a premise.

The finite probabilistic step is unconditional: a nonretained active set has
positive relative nullity and hence contains an actual minimally dependent
subfamily of size at least two. For every finite cutoff K,

    delta <= actualMean/(K+1)
             + sum_(r=2..K) actualJointMass(primitiveFamilies of size r).

The expectation identity uses the exact finite cylinder of the original
infinite measure. The first term handles configurations with more than K
active starts; the remaining terms are actual joint probabilities, not
centered activities or formal weights. Empty ground sets and zero marginals
are included.

Under BCN, the two-site primitive joint mass is at most N^(-1/2+eta), using
the actual pair host count and actual joint-probability bound. Every fixed
order r>=3 has this same weaker bound from the unconditional primitive
estimate N^(1-r/2+eta). Only finitely many fixed orders are assembled.
The critical actual mean is uniformly bounded by M=2*2^C. Choose K after
epsilon so that M/(K+1)<=epsilon/2, then choose N0 to make the finitely many
primitive masses sum to at most epsilon/2. In particular K is fixed before
N, and no fixed-order constant is applied to an order growing with N.

This proves qualitative disappearance of the actual modification and its
coupling error. It does not prove the source rate N^(-4/5+eta), identify the
bad event with the specified source seed union, or establish a Poisson or
quadratic approximation for the original count. Companion T15.2 and T19.3
remain in progress. Numbered coverage stays 77/167 (main 28/73, companion
49/94), confirmed mathematical improvements stay 88. The BCN result remains
an ordinary explicit theorem argument; no new external input or axiom is
introduced. Original manuscript bytes and the Lean/Mathlib pins are preserved.

Verified Lean v4.36.0-rc2 full build (10777 jobs), actual Audit.lean kernel audit (6611 declarations; only propext, Classical.choice, Quot.sound), 4328 direct ledger/finding declaration checks, 138 source manifest entries and all 167 original statement hashes. Ubuntu root free space: 15.52 GiB. The literal retained bad-event probability and actual original-to-modified TV tend uniformly to zero under the ordinary explicit BCN premise. Finite cutoff K is fixed after the tolerance and before N. No source quantitative rate, Poisson approximation, new numbered completion or new mathematical finding is claimed. Coverage 77/167 (main 28/73, companion 49/94); confirmed improvements 88.


## Fixed original-to-modified moment transfer and actual Poisson convergence

The actual retained-modified count now agrees asymptotically with the
original count at every fixed ordinary moment, under explicit BCN.
For every fixed j>=0 and tolerance epsilon>0 there is a threshold N0,
uniform over every critical length L, every G contained in the dyadic
block and every real H, such that

    |E Z_G^j - E modified(H,N,L,G)^j| <= epsilon.

This is not inferred from small total variation alone. An unconditional
finite-cylinder theorem gives the actual quantitative truncation inequality
for every finite G, every j<=q and every R>0:

    |E Z_G^j - E modified^j|
       <= R^j * delta + E Z_G^q / R^(q-j).

Here delta is the literal probability of the actual bad event, and the
original count and modified variable are evaluated on the same finite
prime cylinder. The original and modified observables have their exact
Bochner integrals; every real original observable is proved integrable.
The finite modified count is pointwise bounded by the original count,
and their disagreement probability is exactly delta. No numerical estimate
for delta or moment bound is assumed in this finite theorem.

For convergence take the fixed higher order q=j+1. The previously proved
BCN-dependent uniform original moment bound gives E Z_G^(j+1)<=B.
Choose R=1+2B/epsilon before N, then apply the uniform actual bad-event
convergence with tolerance epsilon/(2R^j). The two truncation terms are
at most epsilon/2. The order, truncation level and bad-event tolerance
are all fixed before the final scale; no growing-order substitution occurs.

The actual modified law also converges uniformly, for every H, in total
variation to both actual Poisson references Pois(mu_N) and Pois(lambda_N)
on the full dyadic block. This follows from the checked original-law
Poisson theorem and the exact original-to-modified coupling by delta.
The references use the original actual and nominal means; no identity
between the modified mean and original mean is asserted at finite N.

The source numerical bad-event rate and identification with its specified
seed union remain open. Companion T15.2 and T19.3 remain in progress.
No new numbered completion, mathematical finding, external input, axiom,
dependency download, manuscript-byte change or Palomar registration occurs.
Coverage 77/167 (main 28/73, companion 49/94), improvements 88.

Verified Lean v4.36.0-rc2 full build (10817 jobs), actual Audit.lean kernel audit (6682 declarations; only propext, Classical.choice, Quot.sound), 4399 direct ledger/finding declaration checks, 138 source manifest entries and all 167 original statement hashes. Ubuntu root free space: 15.44 GiB. Finite original-to-modified moment truncation and original-observable integrability are unconditional. Every fixed original-to-modified moment difference and both modified-law Poisson TV distances converge uniformly under the existing ordinary explicit BCN premise. Higher order q=j+1, truncation level and bad-event tolerance are fixed before N. The sharp source error rate stays open. Coverage 77/167; confirmed improvements 88.
