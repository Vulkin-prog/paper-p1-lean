# Actual absolute centered activity at every fixed order

Source: companion T14.1. Status: **in progress** for its sharper connected exponent and contact assertion.

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

Verified Lean v4.36.0-rc2 full build (10835 jobs), actual Audit.lean kernel audit (6714 declarations; only propext, Classical.choice, Quot.sound), 4431 direct ledger/finding declaration checks, 138 source manifest entries and all 167 original statement hashes. Ubuntu root free space: 15.41 GiB. The finite absolute-activity decomposition and fixed-order dependent product mass N^(-1+eta) are unconditional. Full and connected actual absolute centered activity at every fixed positive order are at most N^(-1/2+eta) under the existing ordinary explicit BCN premise, uniformly over all dyadic subgrounds. Zero marginals and incompatible families are included; no fixed-order theorem is used at growing order. Companion T14.1 stays in progress for its sharper connected 4/5 exponent and contact bound. Coverage 77/167; improvements 89.


## Actual weak pairs, incompatible pairs and marked irregular rows

Two source-scale parts of companion T7.1 are now proved unconditionally
on the actual original model. Weak dependent pairs are defined literally by
rho(e)<=eta*L or q(e)=0. Their absolute activity is at most
N^(-1+eta+epsilon), for every fixed eta>=0 and epsilon>0. The finite
coefficient bound is 2*2^(eta*L)*prod_(x in e)p_x; the already checked
N^(-1+epsilon) product mass of dependent families supplies the total bound.
No common marginal, positive source mass or BCN premise is required.

Every covariance edge touching an irregular start has total absolute
activity at most N^(-1+epsilon). A finite marked-star cover bounds its mass
by the row sum over the marked sites. The unconditional actual row bound
and actual irregular marginal mass prove the estimate, including zero
marginals. An explicit disjoint three-part partition of the actual dependent
pairs separates the irregular class, the weak class after its removal, and
the remaining class. Their activity sums exactly to A2. Every remaining
pair is compatible, avoids irregular sites and has rho(e)>eta*L.
The remaining rational-channel/dense nonaligned analysis is not asserted.
T7.1 therefore moves from not_started to in_progress, not to proved.

All actual incompatible pair activity is also bounded unconditionally by
the dependent product mass, hence by N^(-1+epsilon). The exact pair sign
identity is A2-C2=2*A2_incompatible, with C2 the signed pair sum. The exact
heterogeneous second-cumulant formula consequently yields

    A2(G)-alpha(G)/2 = 2*A2_incompatible(G)+sum_(x in G)p_x^2/2.

The right side is nonnegative and eventually at most N^(-1+epsilon),
uniformly for all critical lengths and dyadic subgrounds. For the full
original dyadic count, the independently proved positive 2:3 channel lower
bound alpha>=d*L*N^(-2/3) gives the stronger quantitative equivalence

    alpha>0,
    0 <= 2*A2/alpha-1 <= N^(-1/3+epsilon).

These statements keep the actual moving mean, second cumulant, irregular
windows and all zero-marginal cases. They do not assume a full pair profile,
a sharp upper bound on A2 or the external BCN estimate. This new corollary
is recorded as improvement P1-MATH-0090 for later manuscript integration.
It does not prove the remaining full profile, the source A2 upper bound,
the good-channel partition or sharp triple/quartic errors. Main 3.3 remains
in progress. Coverage stays 77/167 (main 28/73, companion 49/94); confirmed
improvements increase to 90. No new external input, axiom, dependency
download, source-byte change or Palomar registration is introduced.

Verified Lean v4.36.0-rc2 full build (10905 jobs), actual Audit.lean kernel audit (6818 declarations; only propext, Classical.choice, Quot.sound), 4535 direct ledger/finding declaration checks, 138 source manifest entries and all 167 original statement hashes. Ubuntu root free space: 15.30 GiB. Weak dependent activity N^(-1+eta+epsilon), irregular-touching and incompatible pair activity N^(-1+epsilon), the exact initial disjoint partition, and the quantitative full-count equivalence 0<=2*A2/alpha-1<=N^(-1/3+epsilon) are unconditional. No BCN, complete signed profile or target A2 estimate is supplied as a premise. T7.1 and main 3.3 remain in progress; coverage 77/167, confirmed improvements 90.
