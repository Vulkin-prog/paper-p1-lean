# Exact actual fourth factorial cumulant

Source: main 16.1, its finite displayed identity and separate arithmetic remainder estimates. Status: **in progress** for the sharp arithmetic comparisons.

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

Verified Lean v4.36.0-rc2 full build (10827 jobs), actual Audit.lean kernel audit (6699 declarations; only propext, Classical.choice, Quot.sound), 4416 direct ledger/finding declaration checks, 138 source manifest entries and all 167 original statement hashes. Ubuntu root free space: 15.42 GiB. Exact disjoint-subset incidence, all-order centered cardinality convolution and the complete heterogeneous quartic identity hold over a commutative ring. The original infinite-model specialization and zero-marginal restriction are proved unconditionally. The separate half-power fourth-cumulant decay uses the existing ordinary explicit BCN premise. Source sharp connected-quartic comparisons remain open. Main 16.1 and 6.4 stay in progress. Confirmed improvement P1-MATH-0089 concerns only the generalized finite identity. Coverage 77/167; improvements 89.


## Two pair components and the complete repeated-index remainder

Two further parts of main 16.1 are now checked on the actual original
model: nonconnected quartic component factorization and the complete
repeated-index error at the source 3/2 scale under explicit BCN.

A finite four-element partition without singleton parts is either one
block or exactly two two-element parts. Applied to an actual full-support
relation, this classifies the canonical effective-space components.
Nonzero actual centered activity forces every local marginal to be positive;
this is proved from exact zero-marginal cancellation, not assumed.
Consequently every nonconnected actual four-site family I with c(I)!=0
has actual disjoint two-site subsets e,f such that

    e union f = I,
    rho(I) = rho(e)+rho(f),
    c(I) = c(e)*c(f).

The subsets are obtained from the canonical effective-space partition;
finite-part reindexing identifies their moments and nullities exactly.
The factorization and nullity additivity use the checked canonical direct
partition, actual infinite-model moment factorization and exact part
images. No arithmetic or BCN premise is needed for this finite geometry.
This existence result is not yet an identification of the sum over all
unordered direct edge pairs with the source D22 population.

Write C2 for the actual signed pair activity and C4 for the signed sum over
ALL four-element families. The exact heterogeneous identity gives

    kappa4 - 24*C4 + 12*C2^2 = repeatedRemainder.

For any nonnegative individual marginals p_x bounded by P, a checked finite
bound retains every term:

    |repeatedRemainder| <= 72*P*A3 + 72*P^2*A2 + 6*P^3*mu,

where A2,A3 are the full actual absolute centered activities and mu=sum p_x.
The triple sum, two-site quadratic weights and diagonal fourth powers are
bounded separately before taking their total absolute value. The finite
bound needs no asymptotic estimate.

For every critical length and every G contained in the dyadic block, the
proved marginal cap P<=K/N, bounded actual mean, BCN-dependent half-power
A3 and pair-activity bound yield

    |kappa4(G)-24*C4(G)+12*C2(G)^2| <= N^(-3/2+eta)

for every eta>0, eventually uniformly in G. The pair-weight contribution
actually costs N^(-5/2+eta), and the diagonal contribution costs N^-3.
The constants and thresholds are chosen before N. No target fourth-cumulant
comparison is assumed, and no incompatible family or repeated index is
silently removed.

This proves the complete repeated-index precision used in the source
argument, conditional only on its already inventoried ordinary explicit
BCN premise. The remaining work includes the exact unordered direct-pair
population decomposition, its comparison with C2^2/2, and the sharp
incompatible/connected quartic estimates. No claim kappa4=24*K4 with the
source error is made yet. Main 16.1 stays in progress; coverage remains
77/167 (main 28/73, companion 49/94), improvements remain 89.
No new external input, axiom, dependency download, source-byte change or
Palomar registration is introduced.

Verified Lean v4.36.0-rc2 full build (10847 jobs), actual Audit.lean kernel audit (6728 declarations; only propext, Classical.choice, Quot.sound), 4445 direct ledger/finding declaration checks, 138 source manifest entries and all 167 original statement hashes. Ubuntu root free space: 15.39 GiB. The exact nonconnected quartic pair factorization, nullity additivity and finite repeated-index bound are unconditional. Under the existing ordinary explicit BCN premise, the full repeated remainder relative to 24*C4-12*C2^2 is at most N^(-3/2+eta) uniformly over all dyadic subgrounds. The exact unordered direct-pair population and its sharp product/incompatible comparisons remain open; main 16.1 stays in progress. Coverage 77/167; confirmed improvements 89.
